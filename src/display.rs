use std::{fmt};

use crate::{
    InternedString,
    eval::hoas::{HOASValue, PooledValue},
    expr::Expr,
    types::{Type, TypeScheme},
};

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Var(id) => write!(f, "α{}", id),
            Type::Arrow(pair) => {
                let (from, to) = &**pair;
                // Add parentheses around arrow types in argument position
                match from {
                    Type::Arrow(_) => write!(f, "({}) → {}", from, to),
                    _ => write!(f, "{} → {}", from, to),
                }
            }
        }
    }
}

impl fmt::Display for TypeScheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_canonical_vars(f)
    }
}


impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Int(n) => write!(f, "{}", n),
            Expr::Var(name) => write!(f, "{}", name),
            Expr::Call(pair) => {
                let (func, arg) = &**pair;

                match (func, arg) {
                    (Expr::Call(_), _) => {
                        let mut current = func;
                        let mut args = vec![arg];
                        while let Expr::Call(inner_pair) = current {
                            let (inner_func, inner_arg) = &**inner_pair;
                            current = inner_func;
                            args.insert(0, inner_arg);
                        }
                        if let Expr::Var(name) = current {
                            write!(f, "{}", name)?;
                            for arg in args {
                                write!(f, " {}", format_arg(arg))?;
                            }
                            Ok(())
                        } else {
                            write!(f, "{} {}", format_func(func), format_arg(arg))
                        }
                    }
                    _ => write!(f, "{} {}", format_func(func), format_arg(arg)),
                }
            }
            Expr::Lambda(param, body) => {
                let mut params = vec![*param];
                let mut current_body = &**body;

                while let Expr::Lambda(next_param, next_body) = current_body {
                    params.push(*next_param);
                    current_body = &**next_body;
                }

                write!(
                    f,
                    "λ {} => {}",
                    params
                        .iter()
                        .map(|x| format!("{x}"))
                        .collect::<Vec<_>>()
                        .join(" "),
                    current_body
                )
            }
            Expr::Let(var, val_body) => {
                let (val, body) = &**val_body;
                write!(f, "let {var} = {val} in {body} ")
            }
        }
    }
}

fn format_func(expr: &Expr) -> String {
    match expr {
        Expr::Call(_) => format!("({})", expr),
        _ => format!("{}", expr),
    }
}

fn format_arg(expr: &Expr) -> String {
    match expr {
        Expr::Int(_) | Expr::Var(_) => format!("{}", expr),
        _ => format!("({})", expr),
    }
}

impl fmt::Display for HOASValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HOASValue::Int(n) => write!(f, "{}", n),
            HOASValue::Function(func) => {
                let substituted_body = substitute_vars(&func.body, &func.captured);
                write!(f, "λ{}.{}", func.param, substituted_body)
            }
        }
    }
}

fn substitute_vars(expr: &Expr, env: &[(InternedString, HOASValue)]) -> String {
    match expr {
        Expr::Int(n) => n.to_string(),
        Expr::Var(name) => {
            for (var_name, value) in env.iter().rev() {
                if var_name == name {
                    return format!("{}", value);
                }
            }
            name.to_string()
        }
        Expr::Lambda(param, body) => {
            let mut new_env = Vec::new();
            for (var_name, value) in env {
                if var_name != param {
                    new_env.push((var_name.clone(), value.clone()));
                }
            }
            format!("λ{}.{}", param, substitute_vars(body, &new_env))
        }
        Expr::Call(pair) => {
            let (fun, arg) = &**pair;
            format!(
                "({} {})",
                substitute_vars(fun, env),
                substitute_vars(arg, env)
            )
        }
        Expr::Let(var, val_body) => {
            let (val, body) = &**val_body;
            format!(
                "let {var} = {} in {}",
                substitute_vars(val, env),
                substitute_vars(body, env)
            )
        }
    }
}
