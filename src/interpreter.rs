use crate::{
    eval::hoas::{PooledEnv, evaluate_pooled},
    parser::LambdaParser,
    pools::Pools,
    type_inference::PooledTypingContext,
};

pub struct Interpreter {
    pub pools: Pools,
    pub typing_ctx: PooledTypingContext,
    pub env: PooledEnv,
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}

impl Interpreter {
    #[must_use]
    pub fn new() -> Self {
        Self {
            pools: Pools::new(),
            typing_ctx: PooledTypingContext::new(),
            env: PooledEnv::with_intrinsics(),
        }
    }

    /// Evaluate a recursive function by creating a closure that can reference itself
    fn evaluate_recursive_function(
        &mut self,
        impl_id: crate::pools::ExprId,
        name: crate::InternedString,
    ) -> crate::eval::hoas::PooledValue {
        use std::cell::RefCell;
        use std::rc::Rc;

        // Create a shared reference to the environment that will be updated
        let env_ref = Rc::new(RefCell::new(self.env.clone()));
        let env_ref_clone = env_ref.clone();
        let pools_clone = self.pools.clone();

        // Create the recursive function
        let recursive_func =
            crate::eval::hoas::PooledValue::Function(Rc::new(crate::eval::hoas::HOASFunction {
                func: Rc::new(
                    move |arg: crate::eval::hoas::PooledValue| -> crate::eval::hoas::PooledValue {
                        // Get the current environment which should have all functions available
                        let env = env_ref_clone.borrow();

                        // Evaluate the function implementation with the current environment
                        let func_value = evaluate_pooled(impl_id, &pools_clone, &env);

                        // Apply the function to the argument
                        match func_value {
                            crate::eval::hoas::PooledValue::Function(f) => (f.func)(arg),
                            _ => panic!("Expected function implementation to be a function"),
                        }
                    },
                ),
                param: "arg".into(),
                body_id: impl_id,
                captured_env: Rc::new([]),
                captured_globals: Rc::new([]),
            }));

        // Add this function to the environment reference so it's available for recursive calls
        env_ref
            .borrow_mut()
            .globals
            .insert(name, recursive_func.clone());

        // Update our main environment too
        self.env.globals.insert(name, recursive_func.clone());

        recursive_func
    }

    /// Interpret a program string and return the result
    ///
    /// # Errors
    ///
    /// Returns an error string if parsing, type checking, or evaluation fails
    pub fn interpret(&mut self, input: &str) -> Result<String, String> {
        let expr_ids = LambdaParser::parse_program_to_pool(input, &mut self.pools)?;

        if let Err(errors) = self.typing_ctx.verify_function_signatures(&mut self.pools) {
            return Err(format!("Function signature errors: {errors:?}"));
        }

        // Collect all function implementations
        let function_impls: Vec<(crate::InternedString, crate::pools::ExprId)> = self
            .pools
            .function_implementations
            .iter()
            .map(|(&name, &impl_id)| (name, impl_id))
            .collect();

        // Evaluate functions with recursive support
        for (name, impl_id) in function_impls {
            let func_value = self.evaluate_recursive_function(impl_id, name);
            self.env.globals.insert(name, func_value);
        }

        if expr_ids.is_empty() {
            return Ok("No expression to evaluate".to_string());
        }

        let expr_id = expr_ids[0];

        match self.typing_ctx.infer_type(&mut self.pools, expr_id) {
            Ok(ty) => {
                let scheme = self.typing_ctx.generalize_type(&self.pools, ty);
                let type_display = scheme.display(&self.pools).to_string();

                let result = evaluate_pooled(expr_id, &self.pools, &self.env);
                let value_display = result.display_with_pool(&self.pools);

                Ok(format!("Type: {type_display}, Value: {value_display}"))
            }
            Err(err) => Err(err.display_with_location(&self.pools)),
        }
    }

    /// Start a Read-Eval-Print Loop (REPL) for interactive use
    ///
    /// # Panics
    ///
    /// May panic if I/O operations fail
    pub fn repl(&mut self) {
        use std::io::{self, Write};

        println!("Lambda Calculus REPL with FCP");

        loop {
            print!("λ> ");
            io::stdout().flush().unwrap();

            let mut input = String::new();
            if let Err(error) = io::stdin().read_line(&mut input) {
                eprintln!("Error reading input: {error}");
                break;
            }

            if input.trim().is_empty() {
                continue;
            }

            match self.interpret(&input) {
                Ok(result) => println!("{result}"),
                Err(error) => println!("Error: {error}"),
            }
        }
    }
}
