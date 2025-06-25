use crate::{
    InternedString,
    dependency_analysis::analyze_pool_dependencies,
    expr::{Expr, Pattern},
    pools::{ExprId, PatternId, Pools},
    type_inference::PooledTypingContext,
};
use std::collections::HashMap;
use std::fmt::Write;

pub struct JavaScriptTranspiler {
    output: String,
    variable_mappings: HashMap<String, String>,
}

impl JavaScriptTranspiler {
    #[must_use]
    pub fn new() -> Self {
        Self {
            output: String::new(),
            variable_mappings: HashMap::new(),
        }
    }

    pub fn transpile_program(
        &mut self,
        input: &str,
        pools: &mut Pools,
        filename: &str,
    ) -> Result<String, String> {
        // Parse the program using the file parser (includes temp binding and backpatching)
        let expr_ids = crate::parser::LambdaParser::parse_program_to_pool(input, pools)?;

        // Perform dependency analysis and type checking
        let mut typing_ctx = PooledTypingContext::new();

        // Analyze dependencies and process in topological order
        let definition_groups = analyze_pool_dependencies(pools);
        if let Err(e) = typing_ctx.infer_definition_groups(pools, &definition_groups) {
            let error_msg = e.display_comprehensive(pools, &typing_ctx, input, filename);
            return Err(error_msg);
        }

        // Check if main function exists
        let main_name = crate::intern_str("main");
        if !pools.function_implementations.contains_key(&main_name) {
            return Err("No main function found. Program must have a 'main' function.".to_string());
        }

        // Type check remaining expressions
        for &expr_id in &expr_ids {
            if let Err(e) = typing_ctx.infer_type(pools, expr_id) {
                return Err(format!(
                    "Type error in expression: {}",
                    e.display_with_location(pools)
                ));
            }
        }

        // Add runtime library
        self.add_runtime_library();

        // Transpile data type constructors
        self.transpile_data_constructors(pools);

        // Transpile top-level functions
        self.transpile_functions(pools)?;

        // Print all expression types in main function
        for (name, main_impl_id) in &pools.function_implementations {
            writeln!(self.output, "// {name} function expression types:").unwrap();
            self.print_expression_types_recursive(*main_impl_id, pools, &typing_ctx, 0);
        }

        // Call main function
        writeln!(self.output, "// Execute main function").unwrap();
        writeln!(self.output, "const result = main();").unwrap();
        writeln!(self.output, "console.log('Result:', result);").unwrap();

        Ok(self.output.clone())
    }

    fn add_runtime_library(&mut self) {
        writeln!(self.output, "// Wand Runtime Library").unwrap();
        writeln!(self.output, "class WandValue {{").unwrap();
        writeln!(self.output, "  constructor(type, value) {{").unwrap();
        writeln!(self.output, "    this.type = type;").unwrap();
        writeln!(self.output, "    this.value = value;").unwrap();
        writeln!(self.output, "  }}").unwrap();
        writeln!(self.output, "}}").unwrap();
        writeln!(self.output).unwrap();

        // Constructor function
        writeln!(self.output, "function wandConstructor(name, ...args) {{").unwrap();
        writeln!(
            self.output,
            "  return new WandValue('constructor', {{ name, args }});"
        )
        .unwrap();
        writeln!(self.output, "}}").unwrap();
        writeln!(self.output).unwrap();

        // Record constructor
        writeln!(self.output, "function wandRecord(fields) {{").unwrap();
        writeln!(self.output, "  return new WandValue('record', fields);").unwrap();
        writeln!(self.output, "}}").unwrap();
        writeln!(self.output).unwrap();

        // Pattern matching helper
        writeln!(self.output, "function wandMatch(value, cases) {{").unwrap();
        writeln!(self.output, "  for (const [pattern, handler] of cases) {{").unwrap();
        writeln!(
            self.output,
            "    const bindings = wandMatchPattern(pattern, value);"
        )
        .unwrap();
        writeln!(self.output, "    if (bindings !== null) {{").unwrap();
        writeln!(self.output, "      return handler(...bindings);").unwrap();
        writeln!(self.output, "    }}").unwrap();
        writeln!(self.output, "  }}").unwrap();
        writeln!(
            self.output,
            "  throw new Error('Non-exhaustive pattern match');"
        )
        .unwrap();
        writeln!(self.output, "}}").unwrap();
        writeln!(self.output).unwrap();

        // Pattern matching implementation
        writeln!(self.output, "function wandMatchPattern(pattern, value) {{").unwrap();
        writeln!(self.output, "  if (pattern.type === 'wildcard') return [];").unwrap();
        writeln!(
            self.output,
            "  if (pattern.type === 'variable') return [value];"
        )
        .unwrap();
        writeln!(self.output, "  if (pattern.type === 'int') {{").unwrap();
        writeln!(
            self.output,
            "    return value === pattern.value ? [] : null;"
        )
        .unwrap();
        writeln!(self.output, "  }}").unwrap();
        writeln!(self.output, "  if (pattern.type === 'string') {{").unwrap();
        writeln!(
            self.output,
            "    return value === pattern.value ? [] : null;"
        )
        .unwrap();
        writeln!(self.output, "  }}").unwrap();
        writeln!(self.output, "  if (pattern.type === 'constructor') {{").unwrap();
        writeln!(self.output, "    if (value.type !== 'constructor' || value.value.name !== pattern.name) return null;").unwrap();
        writeln!(self.output, "    const bindings = [];").unwrap();
        writeln!(
            self.output,
            "    for (let i = 0; i < pattern.patterns.length; i++) {{"
        )
        .unwrap();
        writeln!(
            self.output,
            "      const subBindings = wandMatchPattern(pattern.patterns[i], value.value.args[i]);"
        )
        .unwrap();
        writeln!(self.output, "      if (subBindings === null) return null;").unwrap();
        writeln!(self.output, "      bindings.push(...subBindings);").unwrap();
        writeln!(self.output, "    }}").unwrap();
        writeln!(self.output, "    return bindings;").unwrap();
        writeln!(self.output, "  }}").unwrap();
        writeln!(self.output, "  return null;").unwrap();
        writeln!(self.output, "}}").unwrap();
        writeln!(self.output).unwrap();

        // Intrinsic functions
        writeln!(self.output, "const add = (x) => (y) => x + y;").unwrap();
        writeln!(self.output, "const sub = (x) => (y) => x - y;").unwrap();
        writeln!(self.output, "const mul = (x) => (y) => x * y;").unwrap();
        writeln!(self.output, "const div = (x) => (y) => x / y;").unwrap();
        writeln!(self.output).unwrap();
    }

    fn transpile_data_constructors(&mut self, pools: &Pools) {
        writeln!(self.output, "// Data constructors").unwrap();

        for (constructor_name, constructor_type) in &pools.constructors {
            // Determine arity by looking at both component and result types
            let arity = self.get_constructor_arity(constructor_type, pools);
            let js_name = self.js_identifier(constructor_name);

            if arity == 0 {
                // Nullary constructor - just the constructor value
                writeln!(
                    self.output,
                    "const {} = wandConstructor('{}');",
                    js_name,
                    constructor_name.as_str()
                )
                .unwrap();
            } else {
                // Curried constructor function
                let mut output = format!("const {js_name} = ");
                for i in 0..arity {
                    output.push_str(&format!("(arg{i}) => "));
                }
                output.push_str(&format!("wandConstructor('{}'", constructor_name.as_str()));
                for i in 0..arity {
                    output.push_str(&format!(", arg{i}"));
                }
                output.push_str(");");
                writeln!(self.output, "{output}").unwrap();
            }
        }
        writeln!(self.output).unwrap();
    }

    fn get_constructor_arity(
        &self,
        constructor_type: &crate::types::ConstructorType,
        pools: &Pools,
    ) -> usize {
        // For nullary constructors, component_type is Unit
        if matches!(
            &pools[constructor_type.component_type],
            crate::types::Type::Unit(_)
        ) {
            return 0;
        }

        // For non-nullary constructors, count: 1 (component_type) + arrows in result_type
        let mut count = 1; // The component_type itself
        let mut current_type = constructor_type.result_type;
        loop {
            let current_expr = &pools[current_type];
            match current_expr {
                crate::types::Type::Arrow(_, next_type, _) => {
                    count += 1;
                    current_type = *next_type;
                }
                _ => break,
            }
        }
        count
    }

    fn transpile_functions(&mut self, pools: &Pools) -> Result<(), String> {
        writeln!(self.output, "// Top-level functions").unwrap();

        // Sort functions to put main last
        let mut functions: Vec<_> = pools.function_implementations.iter().collect();
        let main_name = crate::intern_str("main");
        functions.sort_by_key(|(name, _)| if **name == main_name { 1 } else { 0 });

        for (function_name, &impl_id) in functions {
            // Print the function type to console and to JS file
            if let Some(type_scheme) = pools.globals.get(function_name) {
                let type_info =
                    format!("{}: {}", function_name.as_str(), type_scheme.display(pools));
                eprintln!("{type_info}");
                writeln!(self.output, "// {type_info}").unwrap();
            }

            write!(
                self.output,
                "const {} = ",
                self.js_identifier(function_name)
            )
            .unwrap();

            // Check if this is a zero-argument function by looking at the expression
            let expr = &pools[impl_id];
            if let Expr::Lambda(_param, _body, _) = expr {
                // This is a regular lambda function
                self.transpile_expression(impl_id, pools)?;
            } else {
                // This is a zero-argument function - wrap the body in a lambda
                write!(self.output, "() => ").unwrap();
                self.transpile_expression(impl_id, pools)?;
            }
            writeln!(self.output, ";").unwrap();
        }
        writeln!(self.output).unwrap();
        Ok(())
    }

    fn transpile_expression(&mut self, expr_id: ExprId, pools: &Pools) -> Result<(), String> {
        let expr = &pools[expr_id];
        match expr {
            Expr::Int(n, _) => {
                write!(self.output, "{n}").unwrap();
            }
            Expr::String(s, _) => {
                write!(self.output, "\"{}\"", s.as_str()).unwrap();
            }
            Expr::Unit(_) => {
                write!(self.output, "null").unwrap();
            }
            Expr::Var(_debruijn, name, _) => {
                let js_name = self.js_identifier(name);
                let final_name = self.variable_mappings.get(&js_name).unwrap_or(&js_name);
                write!(self.output, "{final_name}").unwrap();
            }
            Expr::GlobalVar(_, name, _) => {
                write!(self.output, "{}", self.js_identifier(name)).unwrap();
            }
            Expr::Lambda(body_id, param_name, _) => {
                // Check if this is a zero-argument function (parameter is unit)
                if param_name.as_str() == "()" {
                    write!(self.output, "(() => ").unwrap();
                    self.transpile_expression(*body_id, pools)?;
                    write!(self.output, ")").unwrap();
                } else {
                    write!(self.output, "(({}) => ", self.js_identifier(param_name)).unwrap();
                    self.transpile_expression(*body_id, pools)?;
                    write!(self.output, ")").unwrap();
                }
            }
            Expr::Call(func_id, arg_id, _) => {
                // Check if this is a constructor call with Unit argument
                let arg_expr = &pools[*arg_id];
                if matches!(arg_expr, Expr::Unit(_)) {
                    // This is a zero-argument function call
                    self.transpile_expression(*func_id, pools)?;
                    write!(self.output, "()").unwrap();
                } else {
                    write!(self.output, "(").unwrap();
                    self.transpile_expression(*func_id, pools)?;
                    write!(self.output, ")(").unwrap();
                    self.transpile_expression(*arg_id, pools)?;
                    write!(self.output, ")").unwrap();
                }
            }
            Expr::Let(value_id, body_id, var_name, _) => {
                write!(self.output, "((").unwrap();
                write!(self.output, "{} => ", self.js_identifier(var_name)).unwrap();
                self.transpile_expression(*body_id, pools)?;
                write!(self.output, ")(").unwrap();
                self.transpile_expression(*value_id, pools)?;
                write!(self.output, "))").unwrap();
            }
            Expr::Construct(constructor_name, arg_id, _) => {
                let arg_expr = &pools[*arg_id];
                if matches!(arg_expr, Expr::Unit(_)) {
                    // Nullary constructor - just reference the constructor
                    write!(self.output, "{}", self.js_identifier(constructor_name)).unwrap();
                } else {
                    // Call the curried constructor function
                    write!(self.output, "{}(", self.js_identifier(constructor_name)).unwrap();
                    self.transpile_expression(*arg_id, pools)?;
                    write!(self.output, ")").unwrap();
                }
            }
            Expr::Match(expr_id, match_arms, _) => {
                write!(self.output, "wandMatch(").unwrap();
                self.transpile_expression(*expr_id, pools)?;
                write!(self.output, ", [").unwrap();

                for i in 0..match_arms.length {
                    if i > 0 {
                        write!(self.output, ", ").unwrap();
                    }
                    let case = &pools[PatternId(match_arms.start_id.0 + i)];
                    write!(self.output, "[").unwrap();

                    // Generate pattern with variable names
                    let mut pattern_vars = Vec::new();
                    self.transpile_pattern_with_vars(case.pattern, pools, &mut pattern_vars);

                    write!(self.output, ", ").unwrap();
                    // Create a lambda for the case body with proper variable names
                    write!(self.output, "(").unwrap();
                    for (j, var_name) in pattern_vars.iter().enumerate() {
                        if j > 0 {
                            write!(self.output, ", ").unwrap();
                        }
                        write!(self.output, "{var_name}").unwrap();
                    }
                    write!(self.output, ") => ").unwrap();
                    self.transpile_expression(case.body, pools)?;
                    write!(self.output, "]").unwrap();
                }
                write!(self.output, "])").unwrap();
            }
            Expr::Record(start, len, _) => {
                let fields = pools.get_record_fields(start.0, *len);
                write!(self.output, "wandRecord({{").unwrap();
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(self.output, ", ").unwrap();
                    }
                    write!(self.output, "'{}': ", field.name.as_str()).unwrap();
                    self.transpile_expression(field.expr, pools)?;
                }
                write!(self.output, "}})").unwrap();
            }
            Expr::Project(record_id, field_name, _) => {
                write!(self.output, "(").unwrap();
                self.transpile_expression(*record_id, pools)?;
                write!(self.output, ".value['{}'])", field_name.as_str()).unwrap();
            }
            Expr::Extend(record_id, start, len, _) => {
                let fields = pools.get_record_fields(start.0, *len);
                write!(self.output, "wandRecord({{...").unwrap();
                self.transpile_expression(*record_id, pools)?;
                write!(self.output, ".value").unwrap();
                for field in fields {
                    write!(self.output, ", '{}': ", field.name.as_str()).unwrap();
                    self.transpile_expression(field.expr, pools)?;
                }
                write!(self.output, "}})").unwrap();
            }
            Expr::Ffi(js_code, _type_annotation, arg_expr, _) => {
                // For FFI, we directly embed the JavaScript code
                if let Some(arg_id) = arg_expr {
                    // If there's an argument, we treat the FFI as a function call
                    write!(self.output, "({})(", js_code.as_str()).unwrap();
                    self.transpile_expression(*arg_id, pools)?;
                    write!(self.output, ")").unwrap();
                } else {
                    // No argument, just embed the code directly
                    write!(self.output, "({})", js_code.as_str()).unwrap();
                }
            }
        }
        Ok(())
    }

    fn transpile_pattern_with_vars(
        &mut self,
        pattern: Pattern,
        pools: &Pools,
        vars: &mut Vec<String>,
    ) {
        match pattern {
            Pattern::Wildcard(_) => {
                write!(self.output, "{{ type: 'wildcard' }}").unwrap();
            }
            Pattern::Variable(_, var_name, _) => {
                let js_var_name = if var_name.as_str() == "_" {
                    format!("_wildcard{}", vars.len())
                } else {
                    self.js_identifier(&var_name)
                };
                vars.push(js_var_name.clone());
                write!(self.output, "{{ type: 'variable', name: '{js_var_name}' }}").unwrap();
            }
            Pattern::Int(n, _) => {
                write!(self.output, "{{ type: 'int', value: {n} }}").unwrap();
            }
            Pattern::String(s, _) => {
                write!(
                    self.output,
                    "{{ type: 'string', value: \"{}\" }}",
                    s.as_str()
                )
                .unwrap();
            }
            Pattern::Constructor(name, start_id, length, _) => {
                write!(
                    self.output,
                    "{{ type: 'constructor', name: '{}', patterns: [",
                    name.as_str()
                )
                .unwrap();

                if length > 0 {
                    let nested_patterns = pools.get_nested_patterns(start_id.0, length);
                    for (i, nested_pattern) in nested_patterns.iter().enumerate() {
                        if i > 0 {
                            write!(self.output, ", ").unwrap();
                        }

                        self.transpile_pattern_with_vars(*nested_pattern, pools, vars);
                    }
                }
                write!(self.output, "] }}").unwrap();
            }
            Pattern::Record(_, _, _, _) => {
                write!(self.output, "{{ type: 'record' }}").unwrap();
            }
        }
    }


    fn print_expression_types_recursive(
        &mut self,
        expr_id: ExprId,
        pools: &Pools,
        typing_ctx: &PooledTypingContext,
        depth: usize,
    ) {
        let indent = "  ".repeat(depth);

        // Print this expression's type if available
        if let Some(type_ids) = typing_ctx.expr_types.get(&expr_id) {
            if let Some(&type_id) = type_ids.last() {
                let type_info = format!(
                    "{}{}: {}",
                    indent,
                    pools.display_expr(expr_id),
                    pools.display_type(type_id)
                );
                eprintln!("{type_info}");
                writeln!(
                    self.output,
                    "{}// {} ~ {:?}",
                    indent, type_info, pools[type_id]
                )
                .unwrap();
            }
        }

        // Recursively print types for sub-expressions
        let expr = &pools[expr_id];
        match expr {
            Expr::Lambda(body_id, _param_name, _) => {
                self.print_expression_types_recursive(*body_id, pools, typing_ctx, depth + 1);
            }
            Expr::Call(func_id, arg_id, _) => {
                self.print_expression_types_recursive(*func_id, pools, typing_ctx, depth + 1);
                self.print_expression_types_recursive(*arg_id, pools, typing_ctx, depth + 1);
            }
            Expr::Let(value_id, body_id, _var_name, _) => {
                self.print_expression_types_recursive(*value_id, pools, typing_ctx, depth + 1);
                self.print_expression_types_recursive(*body_id, pools, typing_ctx, depth + 1);
            }
            Expr::Construct(_constructor_name, arg_id, _) => {
                self.print_expression_types_recursive(*arg_id, pools, typing_ctx, depth + 1);
            }
            Expr::Match(expr_id, match_arms, _) => {
                self.print_expression_types_recursive(*expr_id, pools, typing_ctx, depth + 1);
                for i in 0..match_arms.length {
                    let case = &pools[PatternId(match_arms.start_id.0 + i)];
                    self.print_expression_types_recursive(case.body, pools, typing_ctx, depth + 1);
                }
            }
            Expr::Record(start, len, _) => {
                let fields = pools.get_record_fields(start.0, *len);
                for field in fields {
                    self.print_expression_types_recursive(field.expr, pools, typing_ctx, depth + 1);
                }
            }
            Expr::Project(record_id, _field_name, _) => {
                self.print_expression_types_recursive(*record_id, pools, typing_ctx, depth + 1);
            }
            Expr::Extend(record_id, start, len, _) => {
                self.print_expression_types_recursive(*record_id, pools, typing_ctx, depth + 1);
                let fields = pools.get_record_fields(start.0, *len);
                for field in fields {
                    self.print_expression_types_recursive(field.expr, pools, typing_ctx, depth + 1);
                }
            }
            Expr::Ffi(_js_code, _type_annotation, arg_expr, _) => {
                if let Some(arg_id) = arg_expr {
                    self.print_expression_types_recursive(*arg_id, pools, typing_ctx, depth + 1);
                }
            }
            // Base cases - no sub-expressions
            Expr::Int(_, _)
            | Expr::String(_, _)
            | Expr::Unit(_)
            | Expr::Var(_, _, _)
            | Expr::GlobalVar(_, _, _) => {}
        }
    }

    fn js_identifier(&self, name: &InternedString) -> String {
        let name_str = name.as_str();
        // Convert Wand identifiers to valid JavaScript identifiers
        match name_str.as_ref() {
            "add" => "add".to_string(),
            "length" => "length".to_string(),
            _ => name_str.replace('-', "_"),
        }
    }
}

impl Default for JavaScriptTranspiler {
    fn default() -> Self {
        Self::new()
    }
}
