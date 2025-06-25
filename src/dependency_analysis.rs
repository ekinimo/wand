use crate::{
    InternedString,
    expr::Expr,
    pools::{ExprId, Pools},
};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct DefinitionGroup {
    pub definitions: Vec<InternedString>,
    pub is_recursive: bool,
}

#[derive(Debug, Clone)]
pub struct Declaration {
    pub name: InternedString,
    pub kind: DeclarationKind,
    pub dependencies: HashSet<InternedString>,
}

#[derive(Debug, Clone)]
pub enum DeclarationKind {
    Function(ExprId),
    DataType,
}

#[must_use] pub fn topological_sort_declarations(declarations: Vec<Declaration>) -> Vec<DefinitionGroup> {
    let mut name_to_index: HashMap<InternedString, usize> = HashMap::new();
    let mut adj_list: Vec<Vec<usize>> = vec![Vec::new(); declarations.len()];

    for (i, decl) in declarations.iter().enumerate() {
        name_to_index.insert(decl.name, i);
    }

    for (i, decl) in declarations.iter().enumerate() {
        for dep_name in &decl.dependencies {
            if let Some(&dep_index) = name_to_index.get(dep_name) {
                adj_list[dep_index].push(i);
            }
        }
    }

    let sccs = find_strongly_connected_components(&adj_list);

    let mut groups = Vec::new();
    let mut visited = vec![false; declarations.len()];

    for scc in sccs.into_iter().rev() {
        if scc.is_empty() {
            continue;
        }

        let mut group_names = Vec::new();
        let is_recursive = scc.len() > 1 || has_self_dependency(&declarations[scc[0]]);

        for &node_index in &scc {
            if !visited[node_index] {
                group_names.push(declarations[node_index].name);
                visited[node_index] = true;
            }
        }

        if !group_names.is_empty() {
            groups.push(DefinitionGroup {
                definitions: group_names,
                is_recursive,
            });
        }
    }

    groups
}

fn find_strongly_connected_components(adj_list: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut index = 0;
    let mut stack = Vec::new();
    let mut indices = vec![None; adj_list.len()];
    let mut lowlinks = vec![0; adj_list.len()];
    let mut on_stack = vec![false; adj_list.len()];
    let mut sccs = Vec::new();

    for v in 0..adj_list.len() {
        if indices[v].is_none() {
            strongconnect(
                v,
                &mut index,
                &mut stack,
                &mut indices,
                &mut lowlinks,
                &mut on_stack,
                &mut sccs,
                adj_list,
            );
        }
    }

    sccs
}

fn strongconnect(
    v: usize,
    index: &mut usize,
    stack: &mut Vec<usize>,
    indices: &mut [Option<usize>],
    lowlinks: &mut [usize],
    on_stack: &mut [bool],
    sccs: &mut Vec<Vec<usize>>,
    adj_list: &[Vec<usize>],
) {
    indices[v] = Some(*index);
    lowlinks[v] = *index;
    *index += 1;
    stack.push(v);
    on_stack[v] = true;

    for &w in &adj_list[v] {
        if indices[w].is_none() {
            strongconnect(w, index, stack, indices, lowlinks, on_stack, sccs, adj_list);
            lowlinks[v] = lowlinks[v].min(lowlinks[w]);
        } else if on_stack[w] {
            lowlinks[v] = lowlinks[v].min(indices[w].unwrap());
        }
    }

    if indices[v] == Some(lowlinks[v]) {
        let mut scc = Vec::new();
        loop {
            let w = stack.pop().unwrap();
            on_stack[w] = false;
            scc.push(w);
            if w == v {
                break;
            }
        }
        sccs.push(scc);
    }
}

fn has_self_dependency(decl: &Declaration) -> bool {
    decl.dependencies.contains(&decl.name)
}

#[must_use] pub fn analyze_pool_dependencies(pools: &Pools) -> Vec<DefinitionGroup> {
    let mut declarations = Vec::new();

    for (name, expr_id) in &pools.function_implementations {
        let dependencies = extract_dependencies(*expr_id, pools);
        declarations.push(Declaration {
            name: *name,
            kind: DeclarationKind::Function(*expr_id),
            dependencies,
        });
    }

    for name in pools.constructors.keys() {
        declarations.push(Declaration {
            name: *name,
            kind: DeclarationKind::DataType,
            dependencies: HashSet::new(),
        });
    }

    topological_sort_declarations(declarations)
}

#[must_use] pub fn extract_dependencies(expr_id: ExprId, pools: &Pools) -> HashSet<InternedString> {
    let mut dependencies = HashSet::new();
    extract_dependencies_recursive(expr_id, pools, &mut dependencies);
    dependencies
}

fn extract_dependencies_recursive(
    expr_id: ExprId,
    pools: &Pools,
    dependencies: &mut HashSet<InternedString>,
) {
    match &pools[expr_id] {
        Expr::Var(_, _, _) | Expr::Int(_, _) | Expr::String(_, _) | Expr::Unit(_) => {}
        Expr::GlobalVar(_, name, _) => {
            dependencies.insert(*name);
        }
        Expr::Call(func_id, arg_id, _) => {
            extract_dependencies_recursive(*func_id, pools, dependencies);
            extract_dependencies_recursive(*arg_id, pools, dependencies);
        }
        Expr::Lambda(body_id, _, _) => {
            extract_dependencies_recursive(*body_id, pools, dependencies);
        }
        Expr::Let(value_id, body_id, _, _) => {
            extract_dependencies_recursive(*value_id, pools, dependencies);
            extract_dependencies_recursive(*body_id, pools, dependencies);
        }
        Expr::Construct(constructor_name, arg_id, _) => {
            dependencies.insert(*constructor_name);
            extract_dependencies_recursive(*arg_id, pools, dependencies);
        }
        Expr::Match(expr_id, match_arms, _) => {
            extract_dependencies_recursive(*expr_id, pools, dependencies);
            for i in 0..match_arms.length {
                let case = &pools[crate::pools::PatternId(match_arms.start_id.0 + i)];
                extract_dependencies_recursive(case.body, pools, dependencies);
            }
        }
        Expr::Record(start, len, _) => {
            let fields = pools.get_record_fields(start.0, *len);
            for field in fields {
                extract_dependencies_recursive(field.expr, pools, dependencies);
            }
        }
        Expr::Project(record_id, _, _) => {
            extract_dependencies_recursive(*record_id, pools, dependencies);
        }
        Expr::Extend(record_id, start, len, _) => {
            extract_dependencies_recursive(*record_id, pools, dependencies);
            let fields = pools.get_record_fields(start.0, *len);
            for field in fields {
                extract_dependencies_recursive(field.expr, pools, dependencies);
            }
        }
        Expr::Ffi(_, _, arg_expr, _) => {
            if let Some(arg_id) = arg_expr {
                extract_dependencies_recursive(*arg_id, pools, dependencies);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern_str;

    #[test]
    fn test_simple_dependency_order() {
        let declarations = vec![
            Declaration {
                name: intern_str("main"),
                kind: DeclarationKind::Function(crate::pools::ExprId(0)),
                dependencies: [intern_str("helper")].into_iter().collect(),
            },
            Declaration {
                name: intern_str("helper"),
                kind: DeclarationKind::Function(crate::pools::ExprId(1)),
                dependencies: HashSet::new(),
            },
        ];

        let groups = topological_sort_declarations(declarations);

        assert_eq!(groups.len(), 2);
        assert_eq!(groups[0].definitions, vec![intern_str("helper")]);
        assert_eq!(groups[1].definitions, vec![intern_str("main")]);
        assert!(!groups[0].is_recursive);
        assert!(!groups[1].is_recursive);
    }

    #[test]
    fn test_mutual_recursion() {
        let declarations = vec![
            Declaration {
                name: intern_str("even"),
                kind: DeclarationKind::Function(crate::pools::ExprId(0)),
                dependencies: [intern_str("odd")].into_iter().collect(),
            },
            Declaration {
                name: intern_str("odd"),
                kind: DeclarationKind::Function(crate::pools::ExprId(1)),
                dependencies: [intern_str("even")].into_iter().collect(),
            },
        ];

        let groups = topological_sort_declarations(declarations);

        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].definitions.len(), 2);
        assert!(groups[0].is_recursive);
        assert!(groups[0].definitions.contains(&intern_str("even")));
        assert!(groups[0].definitions.contains(&intern_str("odd")));
    }

    #[test]
    fn test_self_recursion() {
        let mut factorial_deps = HashSet::new();
        factorial_deps.insert(intern_str("factorial"));

        let declarations = vec![Declaration {
            name: intern_str("factorial"),
            kind: DeclarationKind::Function(crate::pools::ExprId(0)),
            dependencies: factorial_deps,
        }];

        let groups = topological_sort_declarations(declarations);

        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].definitions, vec![intern_str("factorial")]);
        assert!(groups[0].is_recursive);
    }
}
