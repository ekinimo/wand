use crate::{
    InternedString,
    expr::Expr,
    pools::{DeBruijnIndex, ExprId, PatternId, Pools},
};
use std::{fmt, rc::Rc};

#[derive(Clone)]
pub struct HOASFunction {
    pub func: Rc<dyn Fn(PooledValue) -> PooledValue>,
    pub param: InternedString,
    pub body_id: ExprId,
    pub captured_env: Rc<[PooledValue]>,
    pub captured_globals: Rc<[(InternedString, PooledValue)]>,
}

#[derive(Clone)]
pub enum PooledValue {
    Int(isize),
    String(Rc<str>),
    Unit,
    Function(Rc<HOASFunction>),
    Constructor(InternedString, Rc<[PooledValue]>),
    Record(Rc<[(InternedString, PooledValue)]>),
}

impl PartialEq for PooledValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Int(l0), Self::Int(r0)) => l0 == r0,
            (Self::String(l0), Self::String(r0)) => l0 == r0,
            (Self::Unit, Self::Unit) => true,
            (Self::Constructor(name1, vals1), Self::Constructor(name2, vals2)) => {
                name1 == name2 && vals1 == vals2
            }
            (Self::Record(fields1), Self::Record(fields2)) => {
                if fields1.len() != fields2.len() {
                    return false;
                }

                // Sort both by field name and compare
                let mut sorted1: Vec<_> = fields1.iter().collect();
                let mut sorted2: Vec<_> = fields2.iter().collect();
                sorted1.sort_by_key(|(name, _)| *name);
                sorted2.sort_by_key(|(name, _)| *name);

                sorted1
                    .iter()
                    .zip(sorted2.iter())
                    .all(|((name1, val1), (name2, val2))| name1 == name2 && val1 == val2)
            }
            _ => false,
        }
    }
}

impl fmt::Debug for PooledValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(n) => write!(f, "Int({n})"),
            Self::String(s) => write!(f, "String(\"{s}\")"),
            Self::Unit => write!(f, "Unit"),
            Self::Function(hoas_func) => {
                write!(f, "Function(λ{}.{})", hoas_func.param, hoas_func.body_id.0)
            }
            Self::Constructor(name, vals) => {
                write!(f, "Constructor({name}, {vals:?})")
            }
            Self::Record(fields) => {
                write!(f, "Record({fields:?})")
            }
        }
    }
}

impl PooledValue {
    #[must_use]
    pub fn display_with_pool(&self, expr_pool: &Pools) -> String {
        match self {
            Self::Int(n) => n.to_string(),
            Self::String(s) => format!("\"{}\"", s.as_ref()),
            Self::Unit => "()".to_string(),
            Self::Function(hoas_func) => {
                let substituted_body = Self::substitute_in_expr(
                    expr_pool,
                    hoas_func.body_id,
                    &hoas_func.captured_env,
                    &hoas_func.captured_globals,
                );
                format!("λ{}.{}", hoas_func.param, substituted_body)
            }
            Self::Constructor(name, vals) => {
                if vals.is_empty() {
                    format!("{name} ()")
                } else {
                    let args = vals
                        .iter()
                        .map(|v| v.display_with_pool(expr_pool))
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!("{name} {args}")
                }
            }
            Self::Record(fields) => {
                if fields.is_empty() {
                    "{}".to_string()
                } else {
                    let field_strs: Vec<String> = fields
                        .iter()
                        .map(|(name, value)| {
                            format!("{}: {}", name.as_str(), value.display_with_pool(expr_pool))
                        })
                        .collect();
                    format!("{{{}}}", field_strs.join(", "))
                }
            }
        }
    }

    fn substitute_in_expr(
        expr_pool: &Pools,
        expr_id: ExprId,
        captured_env: &[Self],
        captured_globals: &[(InternedString, Self)],
    ) -> String {
        let expr = expr_pool[expr_id];
        match expr {
            Expr::Int(n, _) => n.to_string(),
            Expr::String(s, _) => format!("\"{}\"", s.as_str()),
            Expr::Unit(_) => "()".to_string(),
            Expr::Var(debruijn_index, name, _) => {
                let idx = debruijn_index.index();
                if idx == 0 {
                    name.to_string()
                } else if idx - 1 < captured_env.len() {
                    captured_env[captured_env.len() - idx].display_with_pool(expr_pool)
                } else {
                    name.to_string()
                }
            }

            Expr::GlobalVar(_, name, _) => {
                for (global_name, global_value) in captured_globals {
                    if *global_name == name {
                        return global_value.display_with_pool(expr_pool);
                    }
                }
                name.to_string()
            }
            Expr::Call(func_id, arg_id, _) => {
                let func_str =
                    Self::substitute_in_expr(expr_pool, func_id, captured_env, captured_globals);
                let arg_str =
                    Self::substitute_in_expr(expr_pool, arg_id, captured_env, captured_globals);
                format!("{func_str} {arg_str}")
            }
            Expr::Lambda(body_id, param_name, _) => {
                let body_str =
                    Self::substitute_in_expr(expr_pool, body_id, captured_env, captured_globals);
                format!("fn {param_name} => {body_str}")
            }
            Expr::Let(value_id, body_id, var_name, _) => {
                let value_str =
                    Self::substitute_in_expr(expr_pool, value_id, captured_env, captured_globals);
                let body_str =
                    Self::substitute_in_expr(expr_pool, body_id, captured_env, captured_globals);
                format!("let {var_name} = {value_str} in {body_str}")
            }
            Expr::Construct(constructor, arg_id, _) => {
                let arg_str =
                    Self::substitute_in_expr(expr_pool, arg_id, captured_env, captured_globals);
                format!("{constructor} {arg_str}")
            }
            Expr::Match(expr_id, _match_arms, _) => {
                let expr_str =
                    Self::substitute_in_expr(expr_pool, expr_id, captured_env, captured_globals);
                format!("match {expr_str} with ...")
            }
            Expr::Record(start, len, _) => {
                let fields = expr_pool.get_record_fields(start.0, len);
                let field_strs: Vec<String> = fields
                    .iter()
                    .map(|field| {
                        let expr_str = Self::substitute_in_expr(
                            expr_pool,
                            field.expr,
                            captured_env,
                            captured_globals,
                        );
                        format!("{}: {}", field.name.as_str(), expr_str)
                    })
                    .collect();
                format!("{{{}}}", field_strs.join(", "))
            }
            Expr::Project(record_id, field_name, _) => {
                let record_str =
                    Self::substitute_in_expr(expr_pool, record_id, captured_env, captured_globals);
                format!("{record_str}.{field_name}")
            }
            Expr::Extend(record_id, start, len, _) => {
                let record_str =
                    Self::substitute_in_expr(expr_pool, record_id, captured_env, captured_globals);
                let fields = expr_pool.get_record_fields(start.0, len);
                let field_strs: Vec<String> = fields
                    .iter()
                    .map(|field| {
                        let expr_str = Self::substitute_in_expr(
                            expr_pool,
                            field.expr,
                            captured_env,
                            captured_globals,
                        );
                        format!("{}: {}", field.name.as_str(), expr_str)
                    })
                    .collect();
                format!("{{{record_str} with {}}}", field_strs.join(", "))
            }
            Expr::Ffi(js_code, _, arg_expr, _) => {
                if let Some(arg_id) = arg_expr {
                    let arg_str =
                        Self::substitute_in_expr(expr_pool, arg_id, captured_env, captured_globals);
                    format!("ffi!(<{}>, {})", js_code.as_str(), arg_str)
                } else {
                    format!("ffi!(<{}>)", js_code.as_str())
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct PooledEnv {
    values: Vec<PooledValue>,
    pub globals: std::collections::HashMap<InternedString, PooledValue>,
}

impl Default for PooledEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl PooledEnv {
    #[must_use]
    pub fn new() -> Self {
        Self {
            values: Vec::new(),
            globals: std::collections::HashMap::new(),
        }
    }

    #[must_use]
    pub fn extend(&self, value: PooledValue) -> Self {
        let mut new_env = self.clone();
        new_env.values.push(value);
        new_env
    }

    #[must_use]
    pub fn lookup(&self, index: DeBruijnIndex) -> Option<PooledValue> {
        let idx = index.index();
        if idx < self.values.len() {
            Some(self.values[self.values.len() - 1 - idx].clone())
        } else {
            None
        }
    }

    #[must_use]
    pub fn lookup_global(&self, name: InternedString) -> Option<PooledValue> {
        self.globals.get(&name).cloned()
    }

    /// Create a new environment with built-in intrinsic functions
    ///
    /// # Panics
    ///
    /// May panic if intrinsic function arguments have incorrect types
    #[must_use]
    pub fn with_intrinsics() -> Self {
        let mut env = Self::new();

        let add_func = HOASFunction {
            func: Rc::new(|x: PooledValue| -> PooledValue {
                match x {
                    PooledValue::Int(x_val) => {
                        PooledValue::Function(Rc::new(HOASFunction {
                            func: Rc::new(move |y| match y {
                                PooledValue::Int(y_val) => PooledValue::Int(x_val + y_val),
                                _ => panic!("Second argument to add must be an integer"),
                            }),
                            param: "y".into(),
                            body_id: ExprId(0), // Placeholder body_id for intrinsic function
                            captured_env: vec![PooledValue::Int(x_val)].into(),
                            captured_globals: vec![].into(),
                        }))
                    }
                    _ => panic!("First argument to add must be an integer"),
                }
            }),
            param: "x".into(),
            body_id: ExprId(0), // Placeholder body_id for intrinsic function
            captured_env: vec![].into(),
            captured_globals: vec![].into(),
        };

        env.globals
            .insert("add".into(), PooledValue::Function(Rc::new(add_func)));
        env
    }
}

fn count_free_vars(expr_pool: &Pools, expr_id: ExprId, depth: usize) -> usize {
    let expr = expr_pool[expr_id];
    match expr {
        Expr::Var(debruijn_index, _, _) => {
            let idx = debruijn_index.index();
            if idx < depth {
                0 // Bound variable
            } else {
                idx - depth + 1 // Free variable
            }
        }
        Expr::GlobalVar(_, _, _) | Expr::Int(_, _) | Expr::String(_, _) | Expr::Unit(_) => 0,
        Expr::Call(func_id, arg_id, _) => {
            let func_free = count_free_vars(expr_pool, func_id, depth);
            let arg_free = count_free_vars(expr_pool, arg_id, depth);
            func_free.max(arg_free)
        }
        Expr::Lambda(body_id, _, _) => count_free_vars(expr_pool, body_id, depth + 1),
        Expr::Let(value_id, body_id, _, _) => {
            let value_free = count_free_vars(expr_pool, value_id, depth);
            let body_free = count_free_vars(expr_pool, body_id, depth + 1);
            value_free.max(body_free)
        }
        Expr::Construct(_, arg_id, _) => count_free_vars(expr_pool, arg_id, depth),
        Expr::Match(expr_id, _match_arms, _) => count_free_vars(expr_pool, expr_id, depth),
        Expr::Record(start, len, _) => {
            let fields = expr_pool.get_record_fields(start.0, len);
            fields
                .iter()
                .map(|field| count_free_vars(expr_pool, field.expr, depth))
                .max()
                .unwrap_or(0)
        }
        Expr::Project(record_id, _, _) => count_free_vars(expr_pool, record_id, depth),
        Expr::Extend(record_id, start, len, _) => {
            let record_free = count_free_vars(expr_pool, record_id, depth);
            let fields = expr_pool.get_record_fields(start.0, len);
            let field_free = fields
                .iter()
                .map(|field| count_free_vars(expr_pool, field.expr, depth))
                .max()
                .unwrap_or(0);
            record_free.max(field_free)
        }
        Expr::Ffi(_, _, arg_expr, _) => {
            if let Some(arg_id) = arg_expr {
                count_free_vars(expr_pool, arg_id, depth)
            } else {
                0
            }
        }
    }
}

#[must_use]
pub fn evaluate_pooled(expr_id: ExprId, expr_pool: &Pools, env: &PooledEnv) -> PooledValue {
    fn eval_hoas(
        expr_id: ExprId,
        expr_pool: &Pools,
        env: &[PooledValue],
        globals: &std::collections::HashMap<InternedString, PooledValue>,
    ) -> PooledValue {
        let expr = expr_pool[expr_id];
        match expr {
            Expr::Int(n, _) => PooledValue::Int(n),
            Expr::String(s, _) => PooledValue::String(s.as_str().into()),
            Expr::Unit(_) => PooledValue::Unit,

            Expr::Var(debruijn_index, name, _) => {
                let idx = debruijn_index.index();
                if idx < env.len() {
                    env[env.len() - 1 - idx].clone()
                } else {
                    panic!("Unbound variable: {name} (De Bruijn index: {idx})")
                }
            }

            Expr::GlobalVar(_, name, _) => globals
                .get(&name)
                .cloned()
                .unwrap_or_else(|| panic!("Unbound global variable: {name}")),

            Expr::Lambda(body_id, param_name, _) => {
                let free_vars = count_free_vars(expr_pool, body_id, 1);
                let needed_env: Rc<[PooledValue]> = if free_vars > 0 && env.len() >= free_vars {
                    env[env.len() - free_vars..].into()
                } else {
                    Rc::new([])
                };
                let globals_vec: Vec<(InternedString, PooledValue)> =
                    globals.iter().map(|(k, v)| (*k, v.clone())).collect();
                let globals_clone = globals.clone();
                let expr_pool_clone = expr_pool.clone();
                let needed_env_clone = needed_env.clone();

                PooledValue::Function(Rc::new(HOASFunction {
                    func: Rc::new(move |arg: PooledValue| -> PooledValue {
                        let mut new_env: Vec<_> = needed_env_clone.iter().cloned().collect();
                        new_env.push(arg);
                        eval_hoas(body_id, &expr_pool_clone, &new_env, &globals_clone)
                    }),
                    param: param_name,
                    body_id,
                    captured_env: needed_env,
                    captured_globals: globals_vec.into(),
                }))
            }

            Expr::Let(value_id, body_id, _var_name, _) => {
                let value_val = eval_hoas(value_id, expr_pool, env, globals);
                let free_vars = count_free_vars(expr_pool, body_id, 1);
                let needed_env = if free_vars > 0 && env.len() >= free_vars {
                    let mut new_env = env[env.len() - free_vars..].to_vec();
                    new_env.push(value_val);
                    new_env
                } else {
                    vec![value_val]
                };
                eval_hoas(body_id, expr_pool, &needed_env, globals)
            }

            Expr::Call(func_id, arg_id, _) => {
                let func_val = eval_hoas(func_id, expr_pool, env, globals);
                let arg_val = eval_hoas(arg_id, expr_pool, env, globals);

                match func_val {
                    PooledValue::Function(f) => (f.func)(arg_val),
                    PooledValue::Constructor(name, args) => {
                        let mut new_args = args.to_vec();
                        new_args.push(arg_val);
                        PooledValue::Constructor(name, Rc::from(new_args))
                    }
                    _ => panic!("Attempted to call a non-function value: {func_val:?}"),
                }
            }

            Expr::Construct(constructor, arg_id, _) => {
                let arg_val = eval_hoas(arg_id, expr_pool, env, globals);
                PooledValue::Constructor(constructor, Rc::new([arg_val]))
            }

            Expr::Match(expr_id, match_arms, _) => {
                let match_val = eval_hoas(expr_id, expr_pool, env, globals);

                for i in 0..match_arms.length {
                    let case = expr_pool[PatternId(match_arms.start_id.0 + i)];
                    if let Some(bindings) = try_match_pattern(case.pattern, &match_val) {
                        let mut new_env = env.to_vec();
                        for binding in bindings {
                            new_env.push(binding);
                        }
                        return eval_hoas(case.body, expr_pool, &new_env, globals);
                    }
                }

                panic!("Non-exhaustive pattern match")
            }

            Expr::Record(start, len, _) => {
                let record_fields = expr_pool.get_record_fields(start.0, len);
                let mut evaluated_fields = Vec::new();

                for field in record_fields {
                    let field_value = eval_hoas(field.expr, expr_pool, env, globals);
                    evaluated_fields.push((field.name, field_value));
                }

                PooledValue::Record(evaluated_fields.into())
            }

            Expr::Project(record_id, field_name, _) => {
                let record_value = eval_hoas(record_id, expr_pool, env, globals);

                match record_value {
                    PooledValue::Record(fields) => {
                        // Find the field by name
                        for (name, value) in fields.iter() {
                            if *name == field_name {
                                return value.clone();
                            }
                        }
                        panic!("Field '{}' not found in record", field_name.as_str());
                    }
                    _ => {
                        panic!("Attempted to project field from non-record value: {record_value:?}")
                    }
                }
            }

            Expr::Extend(record_id, start, len, _) => {
                let base_record = eval_hoas(record_id, expr_pool, env, globals);
                let extension_fields = expr_pool.get_record_fields(start.0, len);

                match base_record {
                    PooledValue::Record(base_fields) => {
                        let mut result_fields: Vec<(InternedString, PooledValue)> =
                            base_fields.to_vec();

                        // Add extension fields (they may override existing ones)
                        for field in extension_fields {
                            let field_value = eval_hoas(field.expr, expr_pool, env, globals);

                            // Check if field already exists and replace it, or add new field
                            if let Some(existing_pos) = result_fields
                                .iter()
                                .position(|(name, _)| *name == field.name)
                            {
                                result_fields[existing_pos] = (field.name, field_value);
                            } else {
                                result_fields.push((field.name, field_value));
                            }
                        }

                        PooledValue::Record(result_fields.into())
                    }
                    _ => panic!("Attempted to extend non-record value: {base_record:?}"),
                }
            }
            Expr::Ffi(_, _, _, _) => {
                // FFI expressions cannot be evaluated in the HOAS interpreter
                // They are only meaningful when transpiled to JavaScript
                panic!("FFI expressions cannot be evaluated in the interpreter")
            }
        }
    }

    eval_hoas(expr_id, expr_pool, &env.values, &env.globals)
}

fn try_match_pattern(
    pattern: crate::expr::Pattern,
    value: &PooledValue,
) -> Option<Vec<PooledValue>> {
    use crate::expr::Pattern;
    match pattern {
        Pattern::Constructor(constructor_name, _start_id, length, _) => match value {
            PooledValue::Constructor(value_constructor, arg_vals) => {
                if constructor_name == *value_constructor {
                    if length == 0 {
                        if arg_vals.len() == 1 {
                            match &arg_vals[0] {
                                PooledValue::Unit => Some(vec![]),
                                _ => None,
                            }
                        } else {
                            None
                        }
                    } else if arg_vals.len() == length {
                        Some(arg_vals.to_vec())
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        },
        Pattern::Variable(_debruijn, _var_name, _) => Some(vec![value.clone()]),
        Pattern::Wildcard(_) => Some(vec![]),
        Pattern::Int(pattern_int, _) => match value {
            PooledValue::Int(value_int) => {
                if pattern_int == *value_int {
                    Some(vec![]) // No bindings for literal patterns
                } else {
                    None // Pattern doesn't match
                }
            }
            _ => None, // Value is not an Int
        },
        Pattern::String(pattern_str, _) => match value {
            PooledValue::String(value_str) => {
                if pattern_str.as_str() == value_str.as_ref() {
                    Some(vec![]) // No bindings for literal patterns
                } else {
                    None // Pattern doesn't match
                }
            }
            _ => None, // Value is not a String
        },
        Pattern::Record(_, _, _, _) => {
            // Record patterns are not yet implemented
            panic!("Record pattern matching not yet implemented")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parser::LambdaParser, pools::Pools, type_inference::PooledTypingContext};

    fn eval_expr(input: &str, env: &PooledEnv) -> PooledValue {
        let mut pools = Pools::new();
        let typing_ctx = PooledTypingContext::new();

        // Set up intrinsics in pools to avoid undefined variable errors
        let int_type = pools.type_int();
        let arrow1 = pools.type_arrow(int_type, int_type);
        let arrow2 = pools.type_arrow(int_type, arrow1);
        let add_scheme = crate::types::TypeScheme::new(Vec::new(), arrow2);
        pools.bind_global_scheme(crate::intern_str("add"), add_scheme);

        match LambdaParser::parse_program_to_pool(input, &mut pools) {
            Ok(exprs) => evaluate_pooled(exprs[0], &pools, env),
            Err(e) => panic!("Parse error: {e:?}"),
        }
    }

    #[test]
    fn test_basic_integers() {
        let env = PooledEnv::new();
        assert_eq!(eval_expr("42", &env), PooledValue::Int(42));
        assert_eq!(eval_expr("-7", &env), PooledValue::Int(-7));
    }

    #[test]
    fn test_identity_function() {
        let env = PooledEnv::new();

        let identity = eval_expr("fn x => x", &env);

        match identity {
            PooledValue::Function(f) => {
                let result = (f.func)(PooledValue::Int(42));
                assert_eq!(result, PooledValue::Int(42));
            }
            _ => panic!("Expected a function"),
        }
    }

    #[test]
    fn test_application() {
        let env = PooledEnv::new();

        let result = eval_expr("(fn x => x) 42", &env);
        assert_eq!(result, PooledValue::Int(42));
    }

    #[test]
    fn test_higher_order_functions() {
        let env = PooledEnv::with_intrinsics();

        let result = eval_expr("((fn f => fn x => f x) (fn n => add n 1)) 5", &env);
        assert_eq!(result, PooledValue::Int(6));
    }

    #[test]
    fn test_lambda_display_with_captured_variables() {
        let env = PooledEnv::new();

        let result = eval_expr("let x = 42 in fn y => x", &env);
        match &result {
            PooledValue::Function(_f) => {
                let mut pools = Pools::new();
                let typing_ctx = PooledTypingContext::new();
                match LambdaParser::parse_program_to_pool("let x = 42 in fn y => x", &mut pools) {
                    Ok(_) => {
                        let _display = result.display_with_pool(&pools);
                    }
                    Err(_) => panic!("Parse failed"),
                }
            }
            _ => panic!("Expected a function"),
        }
    }

    #[test]
    fn test_partial_application_display() {
        let env = PooledEnv::new();

        let result = eval_expr("let id = fn x y => x in (id 2)", &env);
        match &result {
            PooledValue::Function(_f) => {
                let mut pools = Pools::new();
                let typing_ctx = PooledTypingContext::new();
                match LambdaParser::parse_program_to_pool(
                    "let id = fn x y => x in (id 2)",
                    &mut pools,
                ) {
                    Ok(_) => {
                        let _display = result.display_with_pool(&pools);
                    }
                    Err(_) => panic!("Parse failed"),
                }
            }
            _ => panic!("Expected a function"),
        }
    }

    #[test]
    fn test_simple_lambda_display() {
        let env = PooledEnv::new();

        let result = eval_expr("fn x => x", &env);
        match &result {
            PooledValue::Function(_f) => {
                let mut pools = Pools::new();
                let typing_ctx = PooledTypingContext::new();
                match LambdaParser::parse_program_to_pool("fn x => x", &mut pools) {
                    Ok(_) => {
                        let _display = result.display_with_pool(&pools);
                    }
                    Err(_) => panic!("Parse failed"),
                }
            }
            _ => panic!("Expected a function"),
        }
    }

    #[test]
    fn test_nested_functions() {
        let env = PooledEnv::new();

        let first = eval_expr("fn x y => x", &env);

        match first {
            PooledValue::Function(f) => {
                let partial = (f.func)(PooledValue::Int(10));

                match partial {
                    PooledValue::Function(g) => {
                        let result = (g.func)(PooledValue::Int(20));
                        assert_eq!(result, PooledValue::Int(10));
                    }
                    _ => panic!("Expected a function"),
                }
            }
            _ => panic!("Expected a function"),
        }

        let result = eval_expr("((fn x => fn y => x) 10) 20", &env);
        assert_eq!(result, PooledValue::Int(10));
    }

    #[test]
    fn test_variable_shadowing() {
        let env = PooledEnv::new();

        let result = eval_expr("((fn x => fn x => x) 10) 20", &env);
        assert_eq!(result, PooledValue::Int(20));
    }

    #[test]
    fn test_closure_preservation() {
        let env = PooledEnv::with_intrinsics();

        let add_z = eval_expr("let z = 10 in fn x => add z x", &env);

        match add_z {
            PooledValue::Function(f) => {
                let result = (f.func)(PooledValue::Int(5));
                assert_eq!(result, PooledValue::Int(15));
            }
            _ => panic!("Expected a function"),
        }
    }

    #[test]
    fn test_church_encoding() {
        let env = PooledEnv::with_intrinsics();

        let church_0 = "fn f => fn x => x";

        let church_1 = "fn f x => f x";

        let church_2 = "fn f x => f (f x)";

        let church_3 = "fn f x => f (f (f x))";

        let succ = "fn n f x => f (n f x)";

        let expr = format!("({succ}) ({church_2})");
        let _church_3_result = eval_expr(&expr, &env);

        let to_int = |church: &str| {
            let church_val = eval_expr(church, &env);

            match church_val {
                PooledValue::Function(n) => {
                    let inc = eval_expr("fn n => add n 1", &env);

                    let inc_n_times = (n.func)(inc);

                    match inc_n_times {
                        PooledValue::Function(inc_f) => {
                            let result = (inc_f.func)(PooledValue::Int(0));
                            match result {
                                PooledValue::Int(n) => n,
                                _ => panic!("Expected an integer"),
                            }
                        }
                        _ => panic!("Expected a function"),
                    }
                }
                _ => panic!("Expected a function"),
            }
        };

        assert_eq!(to_int(church_0), 0);
        assert_eq!(to_int(church_1), 1);
        assert_eq!(to_int(church_2), 2);
        assert_eq!(to_int(church_3), 3);

        let church_3_int = to_int(&format!("({succ}) ({church_2})"));
        assert_eq!(church_3_int, 3);
    }

    #[test]
    fn test_add_intrinsic() {
        let env = PooledEnv::with_intrinsics();

        let result = eval_expr("add 1 2", &env);
        assert_eq!(result, PooledValue::Int(3));

        let result = eval_expr("add 10 20", &env);
        assert_eq!(result, PooledValue::Int(30));

        let result = eval_expr("add 0 5", &env);
        assert_eq!(result, PooledValue::Int(5));

        let result = eval_expr("((add) 7) 8", &env);
        assert_eq!(result, PooledValue::Int(15));
    }
}
