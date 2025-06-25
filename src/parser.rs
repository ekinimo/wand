use pest::Parser;
use pest_derive::Parser;

use crate::{
    InternedString,
    expr::Pattern,
    intern_str,
    pools::{DeBruijnIndex, ExprId, PatternId, Pools, SpanId, TypeId, TypeVarId},
    types::{ConstructorType, TypeScheme},
};
use std::collections::HashMap;

#[derive(Parser)]
#[grammar = "lambda.pest"]
pub struct LambdaParser;

#[derive(Debug)]
struct ParseContext {
    name_stack: Vec<InternedString>,
}

impl ParseContext {
    const fn new() -> Self {
        Self {
            name_stack: Vec::new(),
        }
    }

    fn with_var<T>(&mut self, name: InternedString, f: impl FnOnce(&mut Self) -> T) -> T {
        self.name_stack.push(name);
        let result = f(self);
        self.name_stack.pop();
        result
    }

    fn lookup_var(&self, name: InternedString) -> Option<DeBruijnIndex> {
        self.name_stack
            .iter()
            .rev()
            .position(|&n| n == name)
            .map(DeBruijnIndex::new)
    }
}

impl ParseContext {
    fn clone(&self) -> Self {
        Self {
            name_stack: self.name_stack.clone(),
        }
    }
}

/// Context for tracking type variables during parsing
#[derive(Debug, Clone)]
struct TypeVarContext {
    /// Maps type variable names to their assigned IDs
    name_to_id: HashMap<InternedString, usize>,
}

impl TypeVarContext {
    fn new() -> Self {
        Self {
            name_to_id: HashMap::new(),
        }
    }

    /// Create a new context with additional type parameters
    fn with_params(
        &self,
        pools: &mut Pools,
        param_names: &[InternedString],
    ) -> (Self, Vec<TypeVarId>) {
        let mut new_context = self.clone();
        let mut param_ids = Vec::new();

        for &name in param_names {
            let var_id = pools.next_type_var;
            pools.next_type_var += 1;
            new_context.name_to_id.insert(name, var_id);
            param_ids.push(TypeVarId::new_named(var_id, name));
        }

        (new_context, param_ids)
    }

    /// Look up a type variable by name
    fn lookup(&self, name: InternedString) -> Option<usize> {
        self.name_to_id.get(&name).copied()
    }

}

fn parse_program(pairs: pest::iterators::Pairs<'_, Rule>, pools: &mut Pools) -> Vec<ExprId> {
    let mut ret = vec![];
    let program_pair = pairs.into_iter().next().unwrap();

    let program = program_pair.into_inner();

    let mut ctx = ParseContext::new();
    let type_ctx = TypeVarContext::new();

    for item in program {
        match item.as_rule() {
            Rule::declaration => {
                let decl_inner = item.into_inner().next().unwrap();
                match decl_inner.as_rule() {
                    Rule::data_def => {
                        parse_data_def(decl_inner, pools, &type_ctx);
                    }
                    Rule::function_def => {
                        parse_function_def(decl_inner, pools, &type_ctx);
                    }
                    _ => unreachable!("Unexpected declaration type"),
                }
            }
            Rule::expr => {
                let expr = parse_expr(
                    item.into_inner().next().unwrap(),
                    pools,
                    &mut ctx,
                    &type_ctx,
                );
                ret.push(expr);
            }
            Rule::EOI => break,
            _ty => {
                unreachable!()
            }
        }
    }

    ret
}

fn parse_data_def(
    data_def: pest::iterators::Pair<'_, Rule>,
    pools: &mut Pools,

    type_ctx: &TypeVarContext,
) {
    let mut inner = data_def.into_inner();

    let type_name = intern_str(inner.next().unwrap().as_str());

    let mut type_params = Vec::new();
    let mut constructor_defs = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::type_param => {
                type_params.push(intern_str(item.as_str()));
            }
            Rule::constructor_def => {
                constructor_defs.push(item);
            }
            _ => {}
        }
    }

    // Create extended type context with data type parameters
    let (extended_type_ctx, param_var_ids) = type_ctx.with_params(pools, &type_params);

    for constructor_def in constructor_defs {
        let mut cons_inner = constructor_def.into_inner();
        let constructor_name = intern_str(cons_inner.next().unwrap().as_str());

        let component_types: Vec<_> = cons_inner.collect();

        if component_types.is_empty() {
            // Nullary constructor
            let component_type = pools.type_unit();
            let param_types: Vec<TypeId> = param_var_ids
                .iter()
                .map(|&var_id| pools.type_var(var_id.id()))
                .collect();
            let result_type = pools.data_type(type_name, &param_types);

            let constructor_type = ConstructorType {
                outer_quantified_vars: param_var_ids.clone(),
                universal_vars: vec![],
                existential_vars: vec![],
                component_type,
                result_type,
            };

            pools.add_constructor(constructor_name, constructor_type);
        } else {
            // Constructor with components
            let mut all_universal_vars = Vec::new();
            let mut all_existential_vars = Vec::new();
            let mut parsed_types = Vec::new();

            for component_type_pair in component_types {
                let (ty, universal_vars, existential_vars) =
                    parse_component_type(component_type_pair, pools, &extended_type_ctx);
                parsed_types.push(ty);
                all_universal_vars.extend(universal_vars);
                all_existential_vars.extend(existential_vars);
            }

            let component_type = parsed_types[0];
            let param_types: Vec<TypeId> = param_var_ids
                .iter()
                .map(|&var_id| pools.type_var(var_id.0))
                .collect();
            let final_result = pools.data_type(type_name, &param_types);

            let result_type = parsed_types[1..]
                .iter()
                .rev()
                .fold(final_result, |acc, &ty| pools.type_arrow(ty, acc));

            let constructor_type = ConstructorType {
                outer_quantified_vars: param_var_ids.clone(),
                universal_vars: all_universal_vars,
                existential_vars: all_existential_vars,
                component_type,
                result_type,
            };

            pools.add_constructor(constructor_name, constructor_type);
        }
    }
}

fn parse_function_def(
    function_def: pest::iterators::Pair<'_, Rule>,
    pools: &mut Pools,
    type_ctx: &TypeVarContext,
) {
    let mut inner = function_def.into_inner();
    let function_name = intern_str(inner.next().unwrap().as_str());
    let mut params = Vec::new();
    let mut param_types = Vec::new();
    let mut has_annotations = false;

    let mut next_item = inner.next().unwrap();

    if next_item.as_rule() == Rule::param_list {
        for param_pair in next_item.into_inner() {
            if param_pair.as_rule() == Rule::param {
                let mut param_inner = param_pair.into_inner();
                let param_name = intern_str(param_inner.next().unwrap().as_str());
                params.push(param_name);

                if let Some(param_type_expr) = param_inner.next() {
                    let param_type = parse_type_expr(param_type_expr, pools, type_ctx);
                    param_types.push(Some(param_type));
                    has_annotations = true;
                } else {
                    param_types.push(None);
                }
            }
        }
        next_item = inner.next().unwrap();
    }

    let (return_type, body_expr_pair) = if next_item.as_rule() == Rule::type_expr {
        has_annotations = true;
        let ret_type = Some(parse_type_expr(next_item, pools, type_ctx));
        let body_pair = inner.next().unwrap();
        (ret_type, body_pair)
    } else {
        (None, next_item)
    };

    let mut ctx = ParseContext::new();
    for &param_name in &params {
        ctx.name_stack.push(param_name);
    }
    let body_expr = parse_expr(
        body_expr_pair.into_inner().next().unwrap(),
        pools,
        &mut ctx,
        type_ctx,
    );

    let mut lambda_expr = body_expr;
    for &param_name in params.iter().rev() {
        lambda_expr = pools.lambda(lambda_expr, param_name);
    }

    if has_annotations {
        let mut function_type = return_type.unwrap_or_else(|| pools.fresh_type_var());
        for param_type in param_types.iter().rev() {
            let param_t = param_type.unwrap_or_else(|| pools.fresh_type_var());
            function_type = pools.type_arrow(param_t, function_type);
        }

        let function_scheme = TypeScheme::new(Vec::new(), function_type);
        pools.bind_global_scheme(function_name, function_scheme);
    }

    pools.add_function_implementation(function_name, lambda_expr);
}

fn parse_component_type(
    component_type_pair: pest::iterators::Pair<'_, Rule>,
    pools: &mut Pools,
    type_ctx: &TypeVarContext,
) -> (TypeId, Vec<TypeVarId>, Vec<TypeVarId>) {
    let inner = component_type_pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::quantified_type => parse_quantified_type(inner, pools, type_ctx),
        Rule::type_param => {
            let var_name = intern_str(inner.as_str());
            type_ctx.lookup(var_name).map_or_else(
                || {
                    panic!("Unknown type variable: {var_name}");
                },
                |var_id| {
                    let ty = pools.type_var(var_id);
                    (ty, Vec::new(), Vec::new())
                },
            )
        }
        Rule::type_expr => {
            let ty = parse_type_expr(inner, pools, type_ctx);
            (ty, Vec::new(), Vec::new())
        }
        Rule::simple_type => {
            let ty = parse_type_atom(inner, pools, type_ctx);
            (ty, Vec::new(), Vec::new())
        }
        _ => unreachable!("Unexpected rule in component_type: {:?}", inner.as_rule()),
    }
}

fn parse_quantified_type(
    quantified_type_pair: pest::iterators::Pair<'_, Rule>,
    pools: &mut Pools,
    type_ctx: &TypeVarContext,
) -> (TypeId, Vec<TypeVarId>, Vec<TypeVarId>) {
    let original_text = quantified_type_pair.as_str();
    let inner = quantified_type_pair.into_inner().collect::<Vec<_>>();

    // Check if this actually contains quantification by looking for forall/exists
    if original_text.contains("forall")
        || original_text.contains("exists")
        || original_text.contains("∀")
        || original_text.contains("∃")
    {
        // Create completely fresh scope for quantified variables
        let (universal_vars, existential_vars, _var_names) =
            parse_quantifier_structure(original_text, pools);

        if !universal_vars.is_empty() || !existential_vars.is_empty() {
            // Extend existing context with the quantified variables
            let mut quantified_ctx = type_ctx.clone();
            for &var_id in universal_vars.iter().chain(existential_vars.iter()) {
                if let Some(name) = var_id.name() {
                    quantified_ctx.name_to_id.insert(name, var_id.id());
                }
            }

            // Find the body type expression (after the dot)
            let body_expr = inner.last().unwrap().clone();

            // Parse the body with isolated quantified context
            let ty = match body_expr.as_rule() {
                Rule::type_expr => parse_type_expr(body_expr, pools, &quantified_ctx),
                _ => parse_type_atom(body_expr, pools, &quantified_ctx),
            };

            return (ty, universal_vars, existential_vars);
        }
    }

    // Not actually quantified - just a regular type expression
    if inner.len() == 1 {
        let body_expr = inner[0].clone();
        let ty = match body_expr.as_rule() {
            Rule::type_expr => parse_type_expr(body_expr, pools, type_ctx),
            _ => parse_type_atom(body_expr, pools, type_ctx),
        };
        (ty, Vec::new(), Vec::new())
    } else {
        panic!("Unexpected quantified_type structure: {original_text}");
    }
}

fn parse_quantifier_structure(
    text: &str,
    pools: &mut Pools,
) -> (Vec<TypeVarId>, Vec<TypeVarId>, Vec<InternedString>) {
    let mut universal_vars = Vec::new();
    let mut existential_vars = Vec::new();
    let mut var_names = Vec::new();

    // Parse quantifier structure more carefully
    let mut remaining = text.trim();

    // Handle nested quantification: forall a. exists b. type OR exists a. forall b. type
    while !remaining.is_empty() {
        if remaining.starts_with("forall") || remaining.starts_with("∀") {
            let prefix_len = if remaining.starts_with("forall") {
                6
            } else {
                1
            };
            remaining = remaining[prefix_len..].trim();

            // Find the dot that ends this quantifier
            if let Some(dot_pos) = remaining.find('.') {
                let vars_part = remaining[..dot_pos].trim();
                remaining = remaining[dot_pos + 1..].trim();

                // Parse variable names
                for var_name_str in vars_part.split_whitespace() {
                    if !var_name_str.is_empty()
                        && var_name_str.chars().all(|c| c.is_alphabetic() || c == '_')
                    {
                        let var_name = intern_str(var_name_str);
                        let var_id = pools.next_type_var;
                        pools.next_type_var += 1;
                        universal_vars.push(TypeVarId::new_named(var_id, var_name));
                        var_names.push(var_name);
                    }
                }
            } else {
                break; // Malformed quantification
            }
        } else if remaining.starts_with("exists") || remaining.starts_with("∃") {
            let prefix_len = if remaining.starts_with("exists") {
                6
            } else {
                1
            };
            remaining = remaining[prefix_len..].trim();

            // Find the dot that ends this quantifier
            if let Some(dot_pos) = remaining.find('.') {
                let vars_part = remaining[..dot_pos].trim();
                remaining = remaining[dot_pos + 1..].trim();

                // Parse variable names
                for var_name_str in vars_part.split_whitespace() {
                    if !var_name_str.is_empty()
                        && var_name_str.chars().all(|c| c.is_alphabetic() || c == '_')
                    {
                        let var_name = intern_str(var_name_str);
                        let var_id = pools.next_type_var;
                        pools.next_type_var += 1;
                        existential_vars.push(TypeVarId::new_named(var_id, var_name));
                        var_names.push(var_name);
                    }
                }
            } else {
                break; // Malformed quantification
            }
        } else {
            break; // No more quantifiers
        }
    }

    (universal_vars, existential_vars, var_names)
}

fn parse_type_expr(
    type_expr_pair: pest::iterators::Pair<'_, Rule>,
    pools: &mut Pools,
    type_ctx: &TypeVarContext,
) -> TypeId {
    let inner = type_expr_pair.into_inner();
    let inner_items: Vec<_> = inner.collect();

    assert!(
        !inner_items.is_empty(),
        "parse_type_expr called with empty rule"
    );

    let type_atom = inner_items[0].clone();
    let atom_type = parse_type_atom(type_atom, pools, type_ctx);

    if inner_items.len() > 1 {
        let rest_type = parse_type_expr(inner_items[1].clone(), pools, type_ctx);
        pools.type_arrow(atom_type, rest_type)
    } else {
        atom_type
    }
}

fn parse_type_atom(
    type_atom_pair: pest::iterators::Pair<'_, Rule>,
    pools: &mut Pools,
    type_ctx: &TypeVarContext,
) -> TypeId {
    match type_atom_pair.as_rule() {
        Rule::type_param => {
            let var_name = intern_str(type_atom_pair.as_str());
            type_ctx.lookup(var_name).map_or_else(
                || {
                    panic!("Unknown type variable: {var_name}");
                },
                |var_id| pools.type_var(var_id),
            )
        }
        Rule::simple_type => {
            let mut inner = type_atom_pair.into_inner();
            let first = inner.next().unwrap();

            match first.as_rule() {
                Rule::type_param => {
                    let var_name = intern_str(first.as_str());
                    type_ctx.lookup(var_name).map_or_else(
                        || {
                            panic!("Unknown type variable: {var_name}");
                        },
                        |var_id| pools.type_var(var_id),
                    )
                }
                Rule::constructor => {
                    let type_name = intern_str(first.as_str());
                    let mut type_args = Vec::new();

                    for arg_pair in inner {
                        let arg_type = parse_type_atom(arg_pair, pools, type_ctx);
                        type_args.push(arg_type);
                    }

                    if type_name.as_str() == "Int" && type_args.is_empty() {
                        pools.type_int()
                    } else if type_name.as_str() == "String" && type_args.is_empty() {
                        pools.type_string()
                    } else {
                        pools.data_type(type_name, &type_args)
                    }
                }
                Rule::record_type => parse_record_type(first, pools, type_ctx),
                _ => unreachable!("Unexpected simple_type inner rule: {:?}", first.as_rule()),
            }
        }
        Rule::type_atom => {
            let mut inner = type_atom_pair.into_inner();
            let first = inner.next().unwrap();

            match first.as_rule() {
                Rule::type_param => {
                    let var_name = intern_str(first.as_str());

                    // Check if there are type arguments following this type parameter
                    let mut type_args = Vec::new();
                    for arg_pair in inner {
                        let arg_type = parse_type_atom(arg_pair, pools, type_ctx);
                        type_args.push(arg_type);
                    }

                    if type_args.is_empty() {
                        type_ctx.lookup(var_name).map_or_else(
                            || {
                                panic!("Unknown type variable: {var_name}");
                            },
                            |var_id| pools.type_var(var_id),
                        )
                    } else {
                        // This represents a higher-kinded type application like `m a`
                        if let Some(var_id) = type_ctx.lookup(var_name) {
                            pools.type_app(var_id, &type_args)
                        } else {
                            // If not a known type variable, treat as data type
                            pools.data_type(var_name, &type_args)
                        }
                    }
                }
                Rule::constructor => {
                    let type_name = intern_str(first.as_str());
                    let mut type_args = Vec::new();

                    for arg_pair in inner {
                        let arg_type = parse_type_atom(arg_pair, pools, type_ctx);
                        type_args.push(arg_type);
                    }

                    if type_name.as_str() == "Int" && type_args.is_empty() {
                        pools.type_int()
                    } else {
                        pools.data_type(type_name, &type_args)
                    }
                }
                Rule::record_type => parse_record_type(first, pools, type_ctx),
                _ => parse_type_expr(first, pools, type_ctx),
            }
        }
        Rule::constructor => {
            let type_name = intern_str(type_atom_pair.as_str());
            if type_name.as_str() == "Int" {
                pools.type_int()
            } else {
                pools.data_type(type_name, &[])
            }
        }
        Rule::record_type => parse_record_type(type_atom_pair, pools, type_ctx),
        _ => {
            let inner_type_expr = type_atom_pair.into_inner().next().unwrap();
            parse_type_expr(inner_type_expr, pools, type_ctx)
        }
    }
}

fn parse_record_type(
    record_type_pair: pest::iterators::Pair<'_, Rule>,
    pools: &mut Pools,
    type_ctx: &TypeVarContext,
) -> TypeId {
    use crate::types::RowField;

    let mut fields = Vec::new();
    let mut rest_type = None;

    for pair in record_type_pair.into_inner() {
        match pair.as_rule() {
            Rule::record_type_field => {
                let mut inner = pair.into_inner();
                let field_name = intern_str(inner.next().unwrap().as_str());
                let field_type_expr = inner.next().unwrap();
                let field_type = parse_type_expr(field_type_expr, pools, type_ctx);

                fields.push(RowField {
                    name: field_name,
                    field_type,
                });
            }
            Rule::type_param => {
                // This is the rest type variable: ...r
                let rest_var_name = intern_str(pair.as_str());
                if let Some(var_id) = type_ctx.lookup(rest_var_name) {
                    rest_type = Some(pools.type_var(var_id));
                } else {
                    panic!("Unknown row type variable: {rest_var_name}");
                }
            }
            _ => {}
        }
    }

    let rest = rest_type.unwrap_or_else(|| pools.type_empty_row());
    pools.type_row(&fields, rest)
}

fn parse_expr(
    expr: pest::iterators::Pair<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
) -> ExprId {
    let span = pools.span_from_pest(expr.as_span());
    match expr.as_rule() {
        Rule::ffi_expr => parse_ffi_expr(expr.into_inner(), pools, ctx, type_ctx, span),
        Rule::abstraction => parse_abstraction(expr.into_inner(), pools, ctx, type_ctx, span),
        Rule::application => parse_application(expr.into_inner(), pools, ctx, type_ctx, span),
        Rule::partial_application => {
            parse_partial_application(expr.into_inner(), pools, ctx, type_ctx, span)
        }
        Rule::let_expr => parse_let_expr(expr.into_inner(), pools, ctx, type_ctx, span),
        Rule::match_expr => parse_match_expr(expr.into_inner(), pools, ctx, type_ctx, span),
        Rule::cons_expr => parse_cons_expr(expr.into_inner(), pools, ctx, type_ctx, span),
        Rule::angle_apply_expr => {
            parse_angle_apply_expr(expr.into_inner(), pools, ctx, type_ctx, span)
        }
        Rule::pipe_expr => parse_pipe_expr(expr.into_inner(), pools, ctx, type_ctx, span),
        Rule::compose_expr => parse_compose_expr(expr.into_inner(), pools, ctx, type_ctx, span),
        Rule::apply_expr => parse_apply_expr(expr.into_inner(), pools, ctx, type_ctx, span),
        Rule::ternary_angle_expr => {
            parse_ternary_angle_expr(expr.into_inner(), pools, ctx, type_ctx, span)
        }
        Rule::pipe_angle_expr => {
            parse_pipe_angle_expr(expr.into_inner(), pools, ctx, type_ctx, span)
        }
        Rule::projection => parse_projection(expr.into_inner(), pools, ctx, type_ctx, span),
        Rule::atom => parse_atom(expr.into_inner().next().unwrap(), pools, ctx, type_ctx),
        Rule::expr => {
            // Handle recursive expr rule by parsing its inner content
            let inner_expr = expr.into_inner().next().unwrap();
            parse_expr(inner_expr, pools, ctx, type_ctx)
        }

        _rule => {
            unreachable!()
        }
    }
}

fn parse_application(
    into_inner: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,

    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    let pairs: Vec<_> = into_inner.collect();

    if let Some(first) = pairs.first() {
        if first.as_rule() == Rule::constructor {
            let constructor_name = intern_str(first.as_str());

            if pairs.len() == 1 {
                let unit_arg = pools.unit_span(span);
                return pools.construct_span(constructor_name, unit_arg, span);
            }
            let mut result = {
                let first_arg = parse_expr_or_projection(pairs[1].clone(), pools, ctx, type_ctx);
                pools.construct_span(constructor_name, first_arg, span)
            };

            for arg_pair in &pairs[2..] {
                let arg_expr = parse_expr_or_projection(arg_pair.clone(), pools, ctx, type_ctx);
                let arg_span = pools.span_from_pest(arg_pair.as_span());
                result = pools.call_span(result, arg_expr, arg_span);
            }

            return result;
        }
    }

    let atoms: Vec<ExprId> = pairs
        .into_iter()
        .map(|atom| parse_expr_or_projection(atom, pools, ctx, type_ctx))
        .collect();

    let mut ret = atoms[0];
    for &new in &atoms[1..] {
        ret = pools.call_span(ret, new, span);
    }
    ret
}

fn parse_let_expr(
    mut into_inner: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,

    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    let name_pair = into_inner.next().unwrap();
    let name = intern_str(name_pair.as_str());
    let value_expr = parse_expr(
        into_inner.next().unwrap().into_inner().next().unwrap(),
        pools,
        ctx,
        type_ctx,
    );

    let body_expr = ctx.with_var(name, |ctx| {
        parse_expr(
            into_inner.next().unwrap().into_inner().next().unwrap(),
            pools,
            ctx,
            type_ctx,
        )
    });

    pools.let_expr_span(value_expr, body_expr, name, span)
}

fn parse_match_expr(
    mut into_inner: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,

    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    let expr_pair = into_inner.next().unwrap();
    let scrutinee = parse_expr(expr_pair.into_inner().next().unwrap(), pools, ctx, type_ctx);

    // Collect all match cases first
    let mut cases = Vec::new();
    for case_pair in into_inner {
        if case_pair.as_rule() == Rule::match_case {
            let mut case_inner = case_pair.into_inner();
            let pattern_pair = case_inner.next().unwrap();
            let body_pair = case_inner.next().unwrap();
            cases.push((pattern_pair, body_pair));
        }
    }

    // Reserve slots in the pattern pool for this match
    let start_id = pools.patterns.len();
    let num_cases = cases.len();

    // Preallocate dummy patterns to reserve the slots
    let dummy_unit = pools.unit();
    for _ in 0..num_cases {
        pools.patterns.push(crate::expr::MatchCase {
            pattern: Pattern::Wildcard(span),
            body: dummy_unit,
        });
    }

    // Now process each case and fill in the actual patterns and bodies
    for (i, (pattern_pair, body_pair)) in cases.into_iter().enumerate() {
        let pattern = parse_pattern(pattern_pair, pools);

        let body = {
            let mut temp_ctx = ctx.clone();
            let mut pattern_vars = Vec::new();
            collect_pattern_variables(&pattern, pools, &mut pattern_vars);

            // Add all variables from the pattern to the context
            for var_name in pattern_vars {
                temp_ctx.name_stack.push(var_name);
            }

            parse_expr(
                body_pair.into_inner().next().unwrap(),
                pools,
                &mut temp_ctx,
                type_ctx,
            )
        };

        // Replace the dummy pattern with the actual one
        pools.patterns[start_id + i] = crate::expr::MatchCase { pattern, body };
    }

    pools.match_expr_span(scrutinee, PatternId(start_id), num_cases, span)
}

fn parse_cons_expr(
    mut into_inner: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    let head_pair = into_inner.next().unwrap();
    let tail_pair = into_inner.next().unwrap();

    let head_expr = parse_atom(head_pair, pools, ctx, type_ctx);
    let tail_expr = parse_expr(tail_pair, pools, ctx, type_ctx);

    // Transform a :: b into Cons a b
    let cons_name = intern_str("Cons");
    let cons_applied = pools.construct_span(cons_name, head_expr, span);
    pools.call_span(cons_applied, tail_expr, span)
}

fn parse_pipe_expr(
    into_inner: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    let parts: Vec<_> = into_inner.collect();

    assert!((parts.len() == 2), "Pipe expression should have exactly 2 parts");

    let left_value = parse_term(parts[0].clone(), pools, ctx, type_ctx);
    let right_part = &parts[1];

    if right_part.as_rule() == Rule::expr {
        let inner = right_part.clone().into_inner().next().unwrap();

        if inner.as_rule() == Rule::pipe_expr {
            let inner_parts: Vec<_> = inner.into_inner().collect();
            let first_func = parse_term(inner_parts[0].clone(), pools, ctx, type_ctx);
            let intermediate = pools.call_span(first_func, left_value, span);

            // Don't parse the rest as a separate expression - handle it as part of the chain
            // Check if inner_parts[1] is another pipe_expr or a simple expression
            let rest_part = &inner_parts[1];

            if rest_part.as_rule() == Rule::expr {
                let rest_inner = rest_part.clone().into_inner().next().unwrap();
                if rest_inner.as_rule() == Rule::pipe_expr {
                    // Another nested pipe - continue the chain manually
                    let rest_parts: Vec<_> = rest_inner.into_inner().collect();
                    let next_func = parse_term(rest_parts[0].clone(), pools, ctx, type_ctx);
                    let next_intermediate = pools.call_span(next_func, intermediate, span);
                    // Recursively handle the rest
                    let final_rest = parse_expr(rest_parts[1].clone(), pools, ctx, type_ctx);

                    pools.call_span(final_rest, next_intermediate, span)
                } else {
                    // Simple expression - apply to intermediate
                    let func = parse_expr(rest_part.clone(), pools, ctx, type_ctx);
                    pools.call_span(func, intermediate, span)
                }
            } else {
                // Direct term/expression
                let func = parse_expr(rest_part.clone(), pools, ctx, type_ctx);
                pools.call_span(func, intermediate, span)
            }
        } else {
            let func = parse_expr(right_part.clone(), pools, ctx, type_ctx);
            pools.call_span(func, left_value, span)
        }
    } else {
        let func = parse_expr(right_part.clone(), pools, ctx, type_ctx);
        pools.call_span(func, left_value, span)
    }
}

fn parse_compose_expr(
    into_inner: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    let parts: Vec<_> = into_inner.collect();

    assert!((parts.len() == 2), "Compose expression should have exactly 2 parts");

    // f <> g becomes λx. f (g x)
    let x_name = intern_str("_compose_x");

    // Build the body with the parameter in scope
    let body_expr = ctx.with_var(x_name, |new_ctx| {
        // Parse functions in the lambda context to get correct De Bruijn indices
        let left_func = parse_term(parts[0].clone(), pools, new_ctx, type_ctx);
        let right_func = parse_expr(parts[1].clone(), pools, new_ctx, type_ctx);

        let x_var = pools.expr_var_span(DeBruijnIndex::new(0), x_name, span);

        // g x
        let g_x = pools.call_span(right_func, x_var, span);

        // f (g x)
        pools.call_span(left_func, g_x, span)
    });

    // λx. f (g x)
    pools.lambda_span(body_expr, x_name, span)
}

fn parse_apply_expr(
    into_inner: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    let parts: Vec<_> = into_inner.collect();

    assert!((parts.len() == 2), "Apply expression should have exactly 2 parts");

    let func = parse_term(parts[0].clone(), pools, ctx, type_ctx);
    let arg = parse_expr(parts[1].clone(), pools, ctx, type_ctx);

    // f <$> x becomes f x (simple function application)
    pools.call_span(func, arg, span)
}

fn parse_ternary_angle_expr(
    into_inner: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    let parts: Vec<_> = into_inner.collect();

    assert!((parts.len() == 5), 
            "Ternary angle expression should have exactly 5 parts: term < optional_func | term | optional_func > expr"
        );

    // Pattern: a < f? | g | h? > (rest)
    // Desugars to: g (f a) (h b) where b comes from rest

    let left_value = parse_term(parts[0].clone(), pools, ctx, type_ctx);

    // Parse f? (optional_func)
    let f_opt = if parts[1].as_rule() == Rule::optional_func {
        let inner = parts[1].clone().into_inner().next();
        inner.map(|f_term| parse_expr(f_term, pools, ctx, type_ctx))
    } else {
        panic!("Expected optional_func at position 1");
    };

    // Parse g (term)
    let g = parse_term(parts[2].clone(), pools, ctx, type_ctx);

    // Parse h? (optional_func)
    let h_opt = if parts[3].as_rule() == Rule::optional_func {
        let inner = parts[3].clone().into_inner().next();
        inner.map(|h_term| parse_expr(h_term, pools, ctx, type_ctx))
    } else {
        panic!("Expected optional_func at position 3");
    };

    // Handle the right part which may be another ternary_angle chain
    let right_part = &parts[4];

    let right_value = if right_part.as_rule() == Rule::expr {
        let inner = right_part.clone().into_inner().next().unwrap();
        if inner.as_rule() == Rule::ternary_angle_expr {
            // Recursively parse nested ternary_angle
            parse_ternary_angle_expr(inner.into_inner(), pools, ctx, type_ctx, span)
        } else {
            parse_expr(right_part.clone(), pools, ctx, type_ctx)
        }
    } else {
        parse_expr(right_part.clone(), pools, ctx, type_ctx)
    };

    // Desugar: g (f a) (h b)
    // f a (or identity if f is None)
    let f_a = if let Some(f) = f_opt {
        pools.call_span(f, left_value, span)
    } else {
        left_value // identity
    };

    // h b (or identity if h is None)
    let h_b = if let Some(h) = h_opt {
        pools.call_span(h, right_value, span)
    } else {
        right_value // identity
    };

    // g (f a) (h b)
    let temp = pools.call_span(g, f_a, span);
    pools.call_span(temp, h_b, span)
}

fn parse_pipe_angle_expr(
    into_inner: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    let parts: Vec<_> = into_inner.collect();

    assert!((parts.len() == 5), 
            "Pipe angle expression should have exactly 5 parts: term | optional_func > term < optional_func | expr"
        );

    // Pattern: a | f? > g < h? | (rest)
    // Desugars to: g (f a b) (h a b) where b comes from rest
    // If f is missing: g a (h a b) (lefthand default = a)
    // If h is missing: g (f a b) b (righthand default = b)

    let left_value = parse_term(parts[0].clone(), pools, ctx, type_ctx);

    // Parse f? (optional_func)
    let f_opt = if parts[1].as_rule() == Rule::optional_func {
        let inner = parts[1].clone().into_inner().next();
        inner.map(|f_term| parse_expr(f_term, pools, ctx, type_ctx))
    } else {
        panic!("Expected optional_func at position 1");
    };

    // Parse g (term)
    let g = parse_term(parts[2].clone(), pools, ctx, type_ctx);

    // Parse h? (optional_func)
    let h_opt = if parts[3].as_rule() == Rule::optional_func {
        let inner = parts[3].clone().into_inner().next();
        inner.map(|h_term| parse_expr(h_term, pools, ctx, type_ctx))
    } else {
        panic!("Expected optional_func at position 3");
    };

    // Handle the right part which may be another pipe_angle chain
    let right_part = &parts[4];

    let right_value = if right_part.as_rule() == Rule::expr {
        let inner = right_part.clone().into_inner().next().unwrap();
        if inner.as_rule() == Rule::pipe_angle_expr {
            // Recursively parse nested pipe_angle
            parse_pipe_angle_expr(inner.into_inner(), pools, ctx, type_ctx, span)
        } else {
            parse_expr(right_part.clone(), pools, ctx, type_ctx)
        }
    } else {
        parse_expr(right_part.clone(), pools, ctx, type_ctx)
    };

    // Desugar: g (f a b) (h a b)
    // If f is missing: g a (h a b) - lefthand default is just a
    // If h is missing: g (f a b) b - righthand default is just b
    let left_arg = if let Some(f) = f_opt {
        let temp = pools.call_span(f, left_value, span);
        pools.call_span(temp, right_value, span) // f a b
    } else {
        left_value // lefthand default: just a
    };

    let right_arg = if let Some(h) = h_opt {
        let temp = pools.call_span(h, left_value, span);
        pools.call_span(temp, right_value, span) // h a b
    } else {
        right_value // righthand default: just b
    };

    // g (left_arg) (right_arg)
    let temp = pools.call_span(g, left_arg, span);
    pools.call_span(temp, right_arg, span)
}

fn parse_angle_apply_expr(
    into_inner: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    let parts: Vec<_> = into_inner.collect();

    assert!((parts.len() == 3), "Angle apply expression should have exactly 3 parts: term < term > expr");

    // For a <f> b <g> c <h> d becoming h d ( g c (f b a ) )
    // We need to collect all parts of the chain and process them correctly

    let left_value = parse_term(parts[0].clone(), pools, ctx, type_ctx);
    let first_func = parse_term(parts[1].clone(), pools, ctx, type_ctx);

    // Start with f(left_value, ...)
    let mut chain_functions = vec![first_func];
    let mut chain_args = vec![left_value];

    // Process the right part which may be another angle_apply chain
    let right_part = &parts[2];

    if right_part.as_rule() == Rule::expr {
        let inner = right_part.clone().into_inner().next().unwrap();
        if inner.as_rule() == Rule::angle_apply_expr {
            // Collect all functions and arguments from the nested chain
            collect_angle_functions(
                inner,
                &mut chain_functions,
                &mut chain_args,
                pools,
                ctx,
                type_ctx,
            );
        } else {
            // Simple case: just the final argument
            let final_arg = parse_expr(right_part.clone(), pools, ctx, type_ctx);
            chain_args.push(final_arg);
        }
    } else {
        let final_arg = parse_term(right_part.clone(), pools, ctx, type_ctx);
        chain_args.push(final_arg);
    }

    // Now build the result: for a <f> b <g> c <h> d
    // We want: h d ( g c (f b a ) )
    // chain_functions = [f, g, h], chain_args = [a, b, c, d]

    assert!((chain_functions.len() == chain_args.len() - 1), "Angle apply chain length mismatch");

    // Build left-associative: f a b, then g (...) c, etc.
    let mut result = {
        let func = chain_functions[0];
        let arg1 = chain_args[0]; // a
        let arg2 = chain_args[1]; // b
        // f a b
        let temp = pools.call_span(func, arg1, span);
        pools.call_span(temp, arg2, span)
    };

    // Apply remaining functions left-associatively: g (f a b) c, then h (...) d
    for i in 1..chain_functions.len() {
        let func = chain_functions[i];
        let arg = chain_args[i + 1];
        // func (previous_result) arg
        let temp = pools.call_span(func, result, span);
        result = pools.call_span(temp, arg, span);
    }

    result
}

fn collect_angle_functions(
    pair: pest::iterators::Pair<'_, Rule>,
    chain_functions: &mut Vec<ExprId>,
    chain_args: &mut Vec<ExprId>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
) {
    if pair.as_rule() != Rule::angle_apply_expr {
        // Base case: not an angle_apply, add as final argument
        let arg = parse_expr(pair, pools, ctx, type_ctx);
        chain_args.push(arg);
        return;
    }

    let parts: Vec<_> = pair.into_inner().collect();
    assert!((parts.len() == 3), "Angle apply expression should have exactly 3 parts");

    // Parse the function and first argument
    let arg = parse_term(parts[0].clone(), pools, ctx, type_ctx);
    let func = parse_term(parts[1].clone(), pools, ctx, type_ctx);

    chain_args.push(arg);
    chain_functions.push(func);

    // Recursively process the right part
    let right_part = &parts[2];
    if right_part.as_rule() == Rule::expr {
        let inner = right_part.clone().into_inner().next().unwrap();
        if inner.as_rule() == Rule::angle_apply_expr {
            collect_angle_functions(inner, chain_functions, chain_args, pools, ctx, type_ctx);
        } else {
            let final_arg = parse_expr(right_part.clone(), pools, ctx, type_ctx);
            chain_args.push(final_arg);
        }
    } else {
        let final_arg = parse_term(right_part.clone(), pools, ctx, type_ctx);
        chain_args.push(final_arg);
    }
}

fn parse_term(
    pair: pest::iterators::Pair<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
) -> ExprId {
    match pair.as_rule() {
        Rule::term => {
            // term contains one of: application, projection, or atom
            let inner = pair.into_inner().next().unwrap();
            parse_term(inner, pools, ctx, type_ctx)
        }
        Rule::application => {
            parse_application(pair.into_inner(), pools, ctx, type_ctx, pools.dummy_span())
        }
        Rule::projection => {
            parse_projection(pair.into_inner(), pools, ctx, type_ctx, pools.dummy_span())
        }
        Rule::atom => parse_atom(pair.into_inner().next().unwrap(), pools, ctx, type_ctx),
        Rule::expr => parse_expr(pair, pools, ctx, type_ctx),
        _ => unreachable!("Unexpected term rule: {:?}", pair.as_rule()),
    }
}

fn collect_pattern_variables(pattern: &Pattern, pools: &Pools, vars: &mut Vec<InternedString>) {
    match pattern {
        Pattern::Variable(_, var_name, _) => {
            vars.push(*var_name);
        }
        Pattern::Constructor(_, start_id, length, _) if *length > 0 => {
            let nested_patterns = pools.get_nested_patterns(start_id.0, *length);
            for nested_pattern in nested_patterns {
                collect_pattern_variables(nested_pattern, pools, vars);
            }
        }
        Pattern::Record(start, len, spread, _) => {
            let fields = pools.get_record_pattern_fields(start.0, *len);
            for field in fields {
                collect_pattern_variables(&field.pattern, pools, vars);
            }
            if let Some(spread_info) = spread {
                if let Some(spread_name) = spread_info.name {
                    vars.push(spread_name);
                }
            }
        }
        _ => {} // Int, String, Wildcard, Constructor with length 0
    }
}

fn parse_pattern(pattern_pair: pest::iterators::Pair<'_, Rule>, pools: &mut Pools) -> Pattern {
    let span = pools.span_from_pest(pattern_pair.as_span());
    match pattern_pair.as_rule() {
        Rule::pattern => parse_pattern(pattern_pair.into_inner().next().unwrap(), pools),
        Rule::constructor_pattern => {
            let mut inner = pattern_pair.into_inner();
            let constructor_pair = inner.next().unwrap();
            let constructor_name = intern_str(constructor_pair.as_str());

            let nested_patterns: Vec<Pattern> = inner
                .map(|pattern_pair| parse_pattern(pattern_pair, pools))
                .collect();

            if nested_patterns.is_empty() {
                Pattern::Constructor(constructor_name, PatternId(0), 0, span)
            } else {
                let (start_id, length) = pools.alloc_nested_patterns(&nested_patterns);
                Pattern::Constructor(constructor_name, start_id, length, span)
            }
        }
        Rule::var_pattern => {
            let var_name = intern_str(pattern_pair.as_str());
            let debruijn = DeBruijnIndex::new(0);
            Pattern::Variable(debruijn, var_name, span)
        }
        Rule::wildcard_pattern => Pattern::Wildcard(span),
        Rule::string_pattern => {
            let s = pattern_pair.as_str();
            // Remove the quotes
            let string_content = &s[1..s.len() - 1];
            Pattern::String(intern_str(string_content), span)
        }
        Rule::int_pattern => {
            let n = str::parse::<isize>(pattern_pair.as_str()).unwrap();
            Pattern::Int(n, span)
        }
        Rule::record_pattern => parse_record_pattern(pattern_pair.into_inner(), pools, span),
        Rule::cons_pattern => {
            let mut inner = pattern_pair.into_inner();
            let head_pattern_pair = inner.next().unwrap();
            let tail_pattern_pair = inner.next().unwrap();

            // Parse both patterns recursively
            let head_pattern = parse_pattern(head_pattern_pair, pools);
            let tail_pattern = parse_pattern(tail_pattern_pair, pools);

            // Create Cons constructor with nested patterns
            let cons_name = intern_str("Cons");
            let nested_patterns = vec![head_pattern, tail_pattern];
            let (start_id, length) = pools.alloc_nested_patterns(&nested_patterns);

            Pattern::Constructor(cons_name, start_id, length, span)
        }
        Rule::pattern_atom => {
            // Handle parenthesized patterns and other atomic patterns
            let inner = pattern_pair.into_inner().next().unwrap();
            parse_pattern(inner, pools)
        }
        Rule::pattern_arg => {
            // Handle pattern arguments (parenthesized patterns or pattern atoms)
            let inner = pattern_pair.into_inner().next().unwrap();
            parse_pattern(inner, pools)
        }
        _rule => {
            unreachable!("Unhandled pattern rule: {:?}", pattern_pair.as_rule())
        }
    }
}

fn parse_record_pattern(
    pairs: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    span: SpanId,
) -> Pattern {
    use crate::expr::{RecordPatternField, Spread};

    let mut fields = Vec::new();
    let mut spread = None;

    for pair in pairs {
        match pair.as_rule() {
            Rule::record_pattern_field => {
                let mut inner = pair.into_inner();
                let name_pair = inner.next().unwrap();
                let pattern_pair = inner.next().unwrap();

                let field_name = intern_str(name_pair.as_str());
                let pattern = parse_pattern(pattern_pair, pools);

                fields.push(RecordPatternField {
                    name: field_name,
                    pattern,
                });
            }
            Rule::spread => {
                let inner = pair.into_inner().next();
                let spread_name = inner.map(|name_pair| intern_str(name_pair.as_str()));
                spread = Some(Spread { name: spread_name });
            }
            _ => {}
        }
    }

    if fields.is_empty() {
        Pattern::Record(crate::types::FieldId(0), 0, spread, span)
    } else {
        let start_id = crate::types::FieldId(pools.record_pattern_fields.len());
        pools.record_pattern_fields.extend(fields.iter());
        Pattern::Record(start_id, fields.len(), spread, span)
    }
}

fn parse_abstraction(
    into_inner: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &ParseContext,

    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    let mut v: Vec<_> = into_inner.collect();
    let expr_pair = v.pop().unwrap().into_inner().next().unwrap();

    let param_names: Vec<InternedString> = v.iter().map(|p| intern_str(p.as_str())).collect();

    let mut temp_ctx = ctx.clone();
    for &param_name in &param_names {
        temp_ctx.name_stack.push(param_name);
    }
    let body_expr = parse_expr(expr_pair, pools, &mut temp_ctx, type_ctx);

    let mut result = body_expr;
    for &param_name in param_names.iter().rev() {
        result = pools.lambda_span(result, param_name, span);
    }

    result
}

fn parse_expr_or_projection(
    pair: pest::iterators::Pair<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
) -> ExprId {
    match pair.as_rule() {
        Rule::projection => {
            let span = pools.span_from_pest(pair.as_span());
            parse_projection(pair.into_inner(), pools, ctx, type_ctx, span)
        }
        _ => parse_atom(pair, pools, ctx, type_ctx),
    }
}

fn parse_atom(
    atom: pest::iterators::Pair<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,

    type_ctx: &TypeVarContext,
) -> ExprId {
    let span = pools.span_from_pest(atom.as_span());
    match atom.as_rule() {
        Rule::natural => pools.int_span(str::parse::<isize>(atom.as_str()).unwrap(), span),
        Rule::string => {
            let s = atom.as_str();
            // Remove the quotes
            let string_content = &s[1..s.len() - 1];
            pools.string_span(intern_str(string_content), span)
        }
        Rule::constructor => {
            let constructor_name = intern_str(atom.as_str());
            let unit_arg = pools.unit_span(span);
            pools.construct_span(constructor_name, unit_arg, span)
        }
        Rule::name => {
            let name = intern_str(atom.as_str());

            if pools.is_constructor(&name) {
                let unit_arg = pools.unit_span(span);
                pools.construct_span(name, unit_arg, span)
            } else if let Some(debruijn_index) = ctx.lookup_var(name) {
                pools.expr_var_span(debruijn_index, name, span)
            } else {
                let free_var_index = DeBruijnIndex::new(usize::MAX);
                pools.expr_var_span(free_var_index, name, span)
            }
        }
        Rule::expr => parse_expr(atom.into_inner().next().unwrap(), pools, ctx, type_ctx),
        Rule::atom => parse_atom(atom.into_inner().next().unwrap(), pools, ctx, type_ctx),
        Rule::ffi_expr => parse_ffi_expr(atom.into_inner(), pools, ctx, type_ctx, span),
        Rule::record_literal => parse_record_literal(atom.into_inner(), pools, ctx, type_ctx, span),
        Rule::record_extension => {
            parse_record_extension(atom.into_inner(), pools, ctx, type_ctx, span)
        }
        Rule::partial_application => {
            parse_partial_application(atom.into_inner(), pools, ctx, type_ctx, span)
        }
        _ty => {
            unreachable!()
        }
    }
}

fn parse_projection(
    mut pairs: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
    _span: SpanId,
) -> ExprId {
    let atom_pair = pairs.next().unwrap();
    let mut expr = parse_atom(atom_pair, pools, ctx, type_ctx);

    for field_pair in pairs {
        if field_pair.as_rule() == Rule::name {
            let field_name = intern_str(field_pair.as_str());
            let field_span = pools.span_from_pest(field_pair.as_span());
            expr = pools.project_expr_span(expr, field_name, field_span);
        }
    }

    expr
}

fn parse_record_literal(
    pairs: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    use crate::expr::RecordField;

    let mut fields = Vec::new();

    for pair in pairs {
        if pair.as_rule() == Rule::record_field {
            let mut inner = pair.into_inner();
            let name_pair = inner.next().unwrap();
            let expr_pair = inner.next().unwrap();

            let field_name = intern_str(name_pair.as_str());
            let field_expr =
                parse_expr(expr_pair.into_inner().next().unwrap(), pools, ctx, type_ctx);

            fields.push(RecordField {
                name: field_name,
                expr: field_expr,
            });
        }
    }

    pools.record_expr_span(&fields, span)
}

fn parse_record_extension(
    mut pairs: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    use crate::expr::RecordField;

    let record_expr = parse_expr(
        pairs.next().unwrap().into_inner().next().unwrap(),
        pools,
        ctx,
        type_ctx,
    );
    let mut fields = Vec::new();

    for pair in pairs {
        if pair.as_rule() == Rule::record_field {
            let mut inner = pair.into_inner();
            let name_pair = inner.next().unwrap();
            let expr_pair = inner.next().unwrap();

            let field_name = intern_str(name_pair.as_str());
            let field_expr =
                parse_expr(expr_pair.into_inner().next().unwrap(), pools, ctx, type_ctx);

            fields.push(RecordField {
                name: field_name,
                expr: field_expr,
            });
        }
    }

    pools.extend_expr_span(record_expr, &fields, span)
}

fn parse_ffi_expr(
    mut pairs: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    use crate::expr::Expr;

    let ffi_string_pair = pairs.next().unwrap();
    let js_code_str = ffi_string_pair.as_str();
    // Remove the angle brackets
    let js_code = &js_code_str[1..js_code_str.len() - 1];
    let js_code_interned = intern_str(js_code);

    let mut type_annotation = None;
    let mut arg_expr = None;

    for pair in pairs {
        match pair.as_rule() {
            Rule::type_expr => {
                type_annotation = Some(parse_type_expr(pair, pools, type_ctx));
            }
            Rule::expr => {
                arg_expr = Some(parse_expr(
                    pair.into_inner().next().unwrap(),
                    pools,
                    ctx,
                    type_ctx,
                ));
            }
            _ => {}
        }
    }

    pools.alloc_expr(Expr::Ffi(js_code_interned, type_annotation, arg_expr, span))
}

fn parse_partial_application(
    pairs: pest::iterators::Pairs<'_, Rule>,
    pools: &mut Pools,
    ctx: &mut ParseContext,
    type_ctx: &TypeVarContext,
    span: SpanId,
) -> ExprId {
    let pairs_vec: Vec<_> = pairs.collect();
    let function_name = intern_str(pairs_vec[0].as_str());

    // The new grammar guarantees we have placeholders, so extract arguments from partial_args_with_underscore
    let args_rule = &pairs_vec[1]; // This should be Rule::partial_args_with_underscore

    // First pass: collect argument pairs and count placeholders
    let mut arg_pairs = Vec::new();
    let mut placeholder_count = 0;

    for arg_pair in args_rule.clone().into_inner() {
        match arg_pair.as_rule() {
            Rule::expr => {
                arg_pairs.push(Some(arg_pair));
            }
            Rule::partial_arg => {
                if arg_pair.as_str() == "_" {
                    arg_pairs.push(None);
                    placeholder_count += 1;
                } else {
                    let arg_inner = arg_pair.into_inner().next().unwrap();
                    arg_pairs.push(Some(arg_inner));
                }
            }
            _ => {
                // Handle underscore directly if it appears as a separate token
                if arg_pair.as_str() == "_" {
                    arg_pairs.push(None);
                    placeholder_count += 1;
                }
            }
        }
    }

    // Generate lambda expressions for each placeholder
    // For p(_, x, _), generate: λd1 → λd2 → p(d1, x, d2)
    let mut lambda_vars = Vec::new();
    for i in 0..placeholder_count {
        let var_name = intern_str(format!("_placeholder_{i}"));
        lambda_vars.push(var_name);
    }

    // Build the lambda body with all placeholders in scope
    let body_expr = {
        let mut temp_ctx = ctx.clone();
        // Add all lambda parameters to context (in reverse order since we'll wrap right-to-left)
        for &var_name in lambda_vars.iter().rev() {
            temp_ctx.name_stack.push(var_name);
        }

        // Now parse expressions in the lambda context
        let mut placeholder_index = 0;
        let mut call_args = Vec::new();

        for arg_pair_opt in arg_pairs {
            if let Some(arg_pair) = arg_pair_opt {
                // Parse expression in lambda context to get correct De Bruijn indices
                let expr = parse_expr(arg_pair, pools, &mut temp_ctx, type_ctx);
                call_args.push(expr);
            } else {
                // Replace with the corresponding lambda variable
                let var_name = lambda_vars[placeholder_index];
                // De Bruijn index should be the position from the outside-in
                // For single placeholder: index 0
                // For multiple placeholders in f(_, x, _): first _ is index 1, second _ is index 0
                let debruijn_index =
                    DeBruijnIndex::new(placeholder_count - 1 - placeholder_index);
                let var_expr = pools.expr_var_span(debruijn_index, var_name, span);
                call_args.push(var_expr);
                placeholder_index += 1;
            }
        }

        // Build the function call: f(arg1, arg2, ...)
        let function_expr = if pools.is_constructor(&function_name) {
            let unit_arg = pools.unit_span(span);
            pools.construct_span(function_name, unit_arg, span)
        } else {
            // Parse function name in lambda context too
            let free_var_index = DeBruijnIndex::new(usize::MAX);
            pools.expr_var_span(free_var_index, function_name, span)
        };

        let mut result = function_expr;
        for arg in call_args {
            result = pools.call_span(result, arg, span);
        }
        result
    };

    // Wrap in lambda expressions for each placeholder (right to left)
    // This creates: λ_placeholder_0 -> (body with _placeholder_0)
    let mut result = body_expr;
    for var_name in lambda_vars.into_iter().rev() {
        result = pools.lambda_span(result, var_name, span);
    }

    result
}

impl LambdaParser {
    /// Parse a program string into expression IDs stored in pools
    ///
    /// # Errors
    ///
    /// Returns an error string if parsing fails
    pub fn parse_program_to_pool(
        input: impl AsRef<str>,
        pools: &mut Pools,
    ) -> Result<Vec<ExprId>, String> {
        let pairs = Self::parse(Rule::program, input.as_ref()).map_err(|err| err.to_string())?;
        let expr_ids = parse_program(pairs, pools);

        // Bind temporary schemes for functions without type annotations
        for name in pools.function_implementations.clone().keys() {
            if pools.get_global_scheme(name).is_none() {
                let temp_type = pools.fresh_type_var();
                let temp_scheme = TypeScheme::new(Vec::new(), temp_type);
                pools.bind_global_scheme(*name, temp_scheme);
            }
        }

        // Backpatch global variables so we can reference functions during type inference
        let undefined_vars = pools.backpatch_global_variables();
        if !undefined_vars.is_empty() {
            return Err(format!("Undefined variables: {undefined_vars:?}"));
        }

        Ok(expr_ids)
    }
}

