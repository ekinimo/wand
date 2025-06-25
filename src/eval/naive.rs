use crate::{InternedString, expr::Expr};
use std::{collections::HashMap, rc::Rc};

#[derive(Debug, Clone, PartialEq)]
pub enum LSValue {
    Int(isize),
    Closure(InternedString, Rc<Expr>, Env),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Env {
    bindings: HashMap<InternedString, LSValue>,
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}

impl Env {
    pub fn new() -> Self {
        Env {
            bindings: HashMap::new(),
        }
    }

    pub fn extend(&self, name: InternedString, value: LSValue) -> Self {
        let mut new_env = self.clone();
        new_env.bindings.insert(name, value);
        new_env
    }

    pub fn lookup(&self, name: &InternedString) -> Option<LSValue> {
        self.bindings.get(name).cloned()
    }
}

pub fn evaluate(expr: &Expr, env: &Env) -> LSValue {
    match expr {
        Expr::Int(n) => LSValue::Int(*n),

        Expr::Var(name) => env.lookup(name).expect("why didn't you typecheck?"),

        Expr::Lambda(param, body) => LSValue::Closure(param.clone(), body.clone(), env.clone()),

        Expr::Let(name, value_body) => {
            let (value, body) = &**value_body;
            let value_val = evaluate(value, env);
            let new_env = env.extend(name.clone(), value_val);
            evaluate(body, &new_env)
        }
        Expr::Call(pair) => {
            let (func, arg) = &**pair;

            let func_val = evaluate(func, env);
            let arg_val = evaluate(arg, env);

            match func_val {
                LSValue::Closure(param, body, closure_env) => {
                    let new_env = closure_env.extend(param, arg_val);
                    evaluate(&body, &new_env)
                }
                _ => unreachable!("you must have forgotten to type check"),
            }
        }
    }
}
