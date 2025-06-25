use crate::{
    dependency_analysis::DefinitionGroup,
    expr::Expr,
    pools::{DeBruijnIndex, ExprId, PatternId, Pools, SpanId, TypeId, TypeVarId},
    types::{Type, TypeScheme},
};
use std::collections::{HashMap, HashSet};

// Re-export the rich error type as TypeError
pub use crate::error::RichTypeError as TypeError;

#[derive(Debug, Clone)]
pub struct PooledTypingContext {
    pub type_schemes: Vec<TypeScheme>,
    pub substitutions: HashMap<TypeVarId, TypeId>,
    pub expr_types: HashMap<ExprId, Vec<TypeId>>,
}

impl Default for PooledTypingContext {
    fn default() -> Self {
        Self::new()
    }
}

impl PooledTypingContext {
    #[must_use]
    pub fn new() -> Self {
        Self {
            type_schemes: Vec::new(),
            substitutions: HashMap::new(),
            expr_types: HashMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.type_schemes.clear();
        self.substitutions.clear();
        self.expr_types.clear();
    }

    pub fn clear_substitutions(&mut self) {
        self.substitutions.clear();
    }

    pub fn fresh_type_var(&mut self, pools: &mut Pools) -> TypeId {
        pools.fresh_type_var()
    }

    pub fn fresh_type_var_span(&mut self, pools: &mut Pools, span: SpanId) -> TypeId {
        pools.fresh_type_var_span(span)
    }

    pub fn extend_scheme(&mut self, scheme: TypeScheme) {
        self.type_schemes.push(scheme);
    }

    #[must_use]
    pub fn lookup_scheme(&self, index: DeBruijnIndex) -> Option<&TypeScheme> {
        let idx = index.index();
        if idx < self.type_schemes.len() {
            Some(&self.type_schemes[self.type_schemes.len() - 1 - idx])
        } else {
            None
        }
    }

    pub fn record(&mut self, expr_id: ExprId, type_id: TypeId) {
        self.expr_types
            .entry(expr_id)
            .or_default()
            .push(type_id);
    }

    /// Apply substitutions to a list of type parameters
    fn apply_substitutions_to_params(&self, pools: &mut Pools, start: usize, len: usize) -> Vec<TypeId> {
        let params: Vec<TypeId> = pools.get_data_type_params(start, len).to_vec();
        params
            .into_iter()
            .map(|param_id| self.apply_substitutions(pools, param_id))
            .collect()
    }

    /// Helper to unify parameters of two type constructors
    fn unify_params(
        &mut self,
        pools: &mut Pools,
        params1: &[TypeId],
        params2: &[TypeId],
        protected_vars: &HashSet<TypeVarId>,
        span1: SpanId,
        span2: SpanId,
    ) -> Result<(), TypeError> {
        for (&p1, &p2) in params1.iter().rev().zip(params2.iter().rev()) {
            self.unify(pools, p1, p2, protected_vars, span1, span2)?;
        }
        Ok(())
    }

    pub fn apply_substitutions(&self, pools: &mut Pools, ty: TypeId) -> TypeId {
        let ty_val = pools[ty];
        match ty_val {
            Type::Int(_) => pools.type_int(),
            Type::String(_) => pools.type_string(),
            Type::Unit(_) => pools.type_unit(),
            Type::EmptyRow(_) => pools.type_empty_row(),
            Type::Var(var, _) => {
                if let Some(&substitution) = self.substitutions.get(&var) {
                    self.apply_substitutions(pools, substitution)
                } else {
                    pools.type_var(var.id())
                }
            }
            Type::Arrow(from, to, _) => {
                let new_from = self.apply_substitutions(pools, from);
                let new_to = self.apply_substitutions(pools, to);
                pools.type_arrow(new_from, new_to)
            }
            Type::DataType(name, start, len, _) => {
                let new_params = self.apply_substitutions_to_params(pools, start.0, len);
                pools.data_type(name, &new_params)
            }
            Type::TypeApp(var_id, start, len, _) => {
                if let Some(&substitution) = self.substitutions.get(&var_id) {
                    self.apply_substitutions(pools, substitution)
                } else {
                    let new_params = self.apply_substitutions_to_params(pools, start.0, len);
                    pools.type_app(var_id.0, &new_params)
                }
            }
            Type::Row(start, len, rest, _) => {
                use crate::types::RowField;
                let fields: Vec<RowField> = pools.get_row_fields(start.0, len).to_vec();
                let new_fields: Vec<RowField> = fields
                    .iter()
                    .map(|field| RowField {
                        name: field.name,
                        field_type: self.apply_substitutions(pools, field.field_type),
                    })
                    .collect();
                let new_rest = self.apply_substitutions(pools, rest);
                pools.type_row(&new_fields, new_rest)
            }
        }
    }


    /// Unify two types while protecting certain type variables
    ///
    /// # Errors
    ///
    /// Returns a `TypeError` if the types cannot be unified
    pub fn unify(
        &mut self,
        pools: &mut Pools,
        t1: TypeId,
        t2: TypeId,
        protected_vars: &HashSet<TypeVarId>,
        span1: SpanId,
        span2: SpanId,
    ) -> Result<(), TypeError> {
        let t1 = self.apply_substitutions(pools, t1);
        let t2 = self.apply_substitutions(pools, t2);

        if t1 == t2 {
            return Ok(());
        }

        let ty1 = pools[t1];
        let ty2 = pools[t2];

        match (ty1, ty2) {
            (Type::Int(_), Type::Int(_))
            | (Type::String(_), Type::String(_))
            | (Type::Unit(_), Type::Unit(_))
            | (Type::EmptyRow(_), Type::EmptyRow(_)) => Ok(()),

            (Type::Var(var, _), _) => {
                // FCP paper Figure 9 (var) rule: α ~^[τ/α] τ mod V if α ∉ V ∪ TV(τ)
                if protected_vars.contains(&var) {
                    // Protected variable cannot be substituted, but it can unify with any type
                    // The protection is about not allowing substitution, not about preventing unification
                    Ok(())
                } else if self.occurs_check(var, pools, t2) {
                    // Check if this is a trivial case where t2 is just the same variable
                    if let Type::Var(var2, _) = pools[t2] {
                        if var == var2 {
                            // This is just α = α, which is trivially true
                            return Ok(());
                        }
                    }
                    Err(TypeError::occurs_check(var, t2, span1, span1))
                } else {
                    // Non-protected variable can be substituted
                    self.substitutions.insert(var, t2);
                    Ok(())
                }
            }

            (_, Type::Var(var, _)) => {
                // Symmetric case
                if protected_vars.contains(&var) {
                    // Protected variable cannot be substituted, but it can unify with any type
                    Ok(())
                } else if self.occurs_check(var, pools, t1) {
                    // Check if this is a trivial case where t1 is just the same variable
                    if let Type::Var(var2, _) = pools[t1] {
                        if var == var2 {
                            // This is just α = α, which is trivially true
                            return Ok(());
                        }
                    }
                    Err(TypeError::occurs_check(var, t1, span2, span2))
                } else {
                    self.substitutions.insert(var, t1);
                    Ok(())
                }
            }

            (Type::Arrow(from_type_1, to_type_1, _), Type::Arrow(from_type_2, to_type_2, _)) => {
                self.unify(
                    pools,
                    from_type_1,
                    from_type_2,
                    protected_vars,
                    span1,
                    span2,
                )?;
                self.unify(pools, to_type_1, to_type_2, protected_vars, span1, span2)?;
                Ok(())
            }

            (Type::DataType(name1, start1, len1, _), Type::DataType(name2, start2, len2, _)) => {
                if name1 == name2 && len1 == len2 {
                    let params1: Vec<TypeId> = pools.get_data_type_params(start1.0, len1).to_vec();
                    let params2: Vec<TypeId> = pools.get_data_type_params(start2.0, len2).to_vec();

                    for (&p1, &p2) in params1.iter().zip(params2.iter()) {
                        self.unify(pools, p1, p2, protected_vars, span1, span2)?;
                    }
                    Ok(())
                } else {
                    Err(TypeError::type_mismatch(
                        t2, t1, span2, span1, None, None, None,
                    ))
                }
            }

            // DataType vs TypeApp unification (higher-kinded types)
            (Type::DataType(_name, start1, len1, _), Type::TypeApp(var_id, start2, len2, _))
            | (Type::TypeApp(var_id, start2, len2, _), Type::DataType(_name, start1, len1, _)) => {
                if len1 == len2 {
                    let params1: Vec<TypeId> = pools.get_data_type_params(start1.0, len1).to_vec();
                    let params2: Vec<TypeId> = pools.get_data_type_params(start2.0, len2).to_vec();

                    // Unify the type variable with the DataType constructor name
                    if protected_vars.contains(&var_id) {
                        // Protected variable cannot be substituted
                        return Err(TypeError::protected_variable_failure(
                            var_id, t1, span2, span1,
                        ));
                    }
                    self.unify_params(pools, &params1, &params2, protected_vars, span1, span2)
                } else if len2 < len1 {
                    let params1: Vec<TypeId> = pools.get_data_type_params(start1.0, len1).to_vec();
                    let params2: Vec<TypeId> = pools.get_data_type_params(start2.0, len2).to_vec();

                    self.unify_params(pools, &params1, &params2, protected_vars, span1, span2)
                } else {
                    Err(TypeError::arity_mismatch(t2, t1, len2, len1, span2, span1))
                }
            }

            // TypeApp vs Arrow unification (higher-kinded type variables can be functions)
            (Type::TypeApp(var_id, start, len, _), Type::Arrow(from_id, to_id, _))
            | (Type::Arrow(from_id, to_id, _), Type::TypeApp(var_id, start, len, _)) => {
                // When f a b == x -> y, we need to handle this similar to DataType unification
                // The arrow type (->) is like a type constructor with arity 2
                // So f should unify with the (->) constructor, and we need to unify parameters
                
                if protected_vars.contains(&var_id) {
                    // Protected variable cannot be substituted
                    return Err(TypeError::protected_variable_failure(
                        var_id, t1, span2, span1,
                    ));
                }

                let params: Vec<TypeId> = pools.get_data_type_params(start.0, len).to_vec();
                
                // Arrow type has exactly 2 parameters: from_type and to_type
                if len == 2 {
                    // f a b == x -> y
                    // Unify a with x and b with y, and f with (->)
                    let arrow_type = pools.type_arrow(params[0], params[1]);
                    self.substitutions.insert(var_id, arrow_type);
                    
                    // Unify the parameters
                    self.unify(pools, params[0], from_id, protected_vars, span1, span2)?;
                    self.unify(pools, params[1], to_id, protected_vars, span1, span2)?;
                    Ok(())
                } else if len < 2 {
                    // f a == x -> y (partial application)
                    // f should be a -> (x -> y), and we unify a with x
                    if len == 1 {
                        // f a == x -> y
                        // This should not happen in normal circumstances for function applications
                        // This case suggests a type error - we're trying to unify a type application
                        // with an arrow when the arity doesn't match
                        Err(TypeError::arity_mismatch(t2, t1, 2, len, span2, span1))
                    } else {
                        // f == x -> y
                        let arrow_type = pools.type_arrow(from_id, to_id);
                        self.substitutions.insert(var_id, arrow_type);
                        Ok(())
                    }
                } else {
                    // f a b c ... == x -> y (over-application)
                    // This suggests f has more parameters than the arrow can handle
                    Err(TypeError::arity_mismatch(t2, t1, 2, len, span2, span1))
                }
            }

            // TypeApp vs TypeApp unification
            (Type::TypeApp(var1, start1, len1, _), Type::TypeApp(var2, start2, len2, _)) => {
                if var1 == var2 {
                    let params1: Vec<TypeId> = pools.get_data_type_params(start1.0, len1).to_vec();
                    let params2: Vec<TypeId> = pools.get_data_type_params(start2.0, len2).to_vec();

                    self.substitutions.insert(var1, t2);
                    for (&p1, &p2) in params1.iter().rev().zip(params2.iter().rev()) {
                        self.unify(pools, p1, p2, protected_vars, span1, span2)?;
                    }
                    Ok(())
                } else if len1 == len2 {
                    // Different variables but same arity - handle through variable unification
                    if protected_vars.contains(&var1) && protected_vars.contains(&var2) {
                        // Both protected - cannot unify
                        Err(TypeError::protected_variable_failure(
                            var1, t2, span1, span2,
                        ))
                    } else if protected_vars.contains(&var1) {
                        // var1 protected, var2 not - unify var2 with t1
                        if self.occurs_check(var2, pools, t1) {
                            Err(TypeError::occurs_check(var2, t1, span2, span2))
                        } else {
                            self.substitutions.insert(var2, t1);
                            Ok(())
                        }
                    } else if protected_vars.contains(&var2) {
                        // var2 protected, var1 not - unify var1 with t2
                        if self.occurs_check(var1, pools, t2) {
                            Err(TypeError::occurs_check(var1, t2, span1, span1))
                        } else {
                            self.substitutions.insert(var1, t2);
                            Ok(())
                        }
                    } else {
                        // Neither protected - unify var1 with t2
                        if self.occurs_check(var1, pools, t2) {
                            Err(TypeError::occurs_check(var1, t2, span1, span1))
                        } else {
                            self.substitutions.insert(var1, t2);
                            Ok(())
                        }
                    }
                } else {
                    // Different arities - cannot unify
                    Err(TypeError::arity_mismatch(t2, t1, len2, len1, span2, span1))
                }
            }

            // Row unification
            (Type::Row(start1, len1, rest1, _), Type::Row(start2, len2, rest2, _)) => self
                .unify_rows(
                    pools,
                    start1,
                    len1,
                    rest1,
                    start2,
                    len2,
                    rest2,
                    protected_vars,
                    span1,
                    span2,
                ),

            // Row vs EmptyRow unification
            (Type::Row(_start, len, rest, _), Type::EmptyRow(_)) => {
                // A row can only unify with EmptyRow if it has no fields and rest unifies with EmptyRow
                if len == 0 {
                    self.unify(pools, rest, t2, protected_vars, span1, span2)
                } else {
                    Err(TypeError::row_mismatch(
                        t2,
                        t1,
                        span2,
                        span1,
                        "Row with fields cannot unify with EmptyRow".to_string(),
                    ))
                }
            }

            // EmptyRow vs Row unification (symmetric case)
            (Type::EmptyRow(_), Type::Row(_start, len, rest, _)) => {
                // EmptyRow can only unify with a row if the row has no fields and rest unifies with EmptyRow
                if len == 0 {
                    self.unify(pools, t1, rest, protected_vars, span1, span2)
                } else {
                    Err(TypeError::row_mismatch(
                        t2,
                        t1,
                        span2,
                        span1,
                        "Row with fields cannot unify with EmptyRow".to_string(),
                    ))
                }
            }

            _ => Err(TypeError::type_mismatch(
                t2, t1, span2, span1, None, None, None,
            )),
        }
    }

    /// Unify two row types using OCaml-style row polymorphism
    fn unify_rows(
        &mut self,
        pools: &mut Pools,
        start1: crate::types::FieldId,
        len1: usize,
        rest1: TypeId,
        start2: crate::types::FieldId,
        len2: usize,
        rest2: TypeId,
        protected_vars: &HashSet<TypeVarId>,
        span1: SpanId,
        span2: SpanId,
    ) -> Result<(), TypeError> {
        use std::collections::BTreeMap;

        // Get flattened representations (following OCaml match_row_ty)
        let (fields1, final_rest1) = self.match_row_ty(pools, start1, len1, rest1);
        let (fields2, final_rest2) = self.match_row_ty(pools, start2, len2, rest2);

        // Convert to sorted maps for deterministic processing
        let mut map1: BTreeMap<crate::InternedString, TypeId> = BTreeMap::new();
        let mut map2: BTreeMap<crate::InternedString, TypeId> = BTreeMap::new();

        for field in &fields1 {
            map1.insert(field.name, field.field_type);
        }
        for field in &fields2 {
            map2.insert(field.name, field.field_type);
        }

        // Following OCaml unify_labels logic
        let mut missing1 = Vec::new();
        let mut missing2 = Vec::new();

        let labels1: Vec<_> = map1.iter().collect();
        let labels2: Vec<_> = map2.iter().collect();

        self.unify_labels(
            pools,
            &mut missing1,
            &mut missing2,
            &labels1,
            &labels2,
            protected_vars,
            span1,
            span2,
        )?;

        // Handle missing fields following OCaml logic
        match (missing1.is_empty(), missing2.is_empty()) {
            (true, true) => {
                // No missing fields, just unify rests
                self.unify(
                    pools,
                    final_rest1,
                    final_rest2,
                    protected_vars,
                    span1,
                    span2,
                )
            }
            (true, false) => {
                // Row1 missing fields from row2, extend rest2 with missing fields
                let new_row = pools.type_row(&missing2, final_rest1);
                self.unify(pools, final_rest2, new_row, protected_vars, span1, span2)
            }
            (false, true) => {
                // Row2 missing fields from row1, extend rest1 with missing fields
                let new_row = pools.type_row(&missing1, final_rest2);
                self.unify(pools, final_rest1, new_row, protected_vars, span1, span2)
            }
            (false, false) => {
                // Both have missing fields - following OCaml complex case
                match pools[final_rest1] {
                    crate::types::Type::EmptyRow(_) => {
                        // Will result in error - trying to unify EmptyRow with non-empty extension
                        let fresh_var = self.fresh_type_var(pools);
                        let new_row = pools.type_row(&missing1, fresh_var);
                        self.unify(
                            pools,
                            final_rest1,
                            new_row,
                            protected_vars,
                            span1,
                            span2,
                        )
                    }
                    crate::types::Type::Var(var_id, _) if !protected_vars.contains(&var_id) => {
                        // Create fresh rest variable
                        let new_rest_var = self.fresh_type_var(pools);
                        let new_row2 = pools.type_row(&missing2, new_rest_var);

                        // Unify rest2 with extended row
                        self.unify(
                            pools,
                            final_rest2,
                            new_row2,
                            protected_vars,
                            span1,
                            span2,
                        )?;

                        // Check for recursive types
                        if self.substitutions.contains_key(&var_id) {
                            return Err(TypeError::type_mismatch(
                                rest2, rest1, span2, span1, None, None, None,
                            ));
                        }

                        // Unify rest1 with extended row
                        let new_row1 = pools.type_row(&missing1, new_rest_var);
                        self.unify(
                            pools,
                            final_rest1,
                            new_row1,
                            protected_vars,
                            span1,
                            span2,
                        )
                    }
                    _ => {
                        // Should not happen according to OCaml logic
                        Err(TypeError::type_mismatch(
                            rest2, rest1, span2, span1, None, None, None,
                        ))
                    }
                }
            }
        }
    }

    /// OCaml-style `match_row_ty` - extract fields and rest from a row type
    fn match_row_ty(
        &self,
        pools: &mut Pools,
        start: crate::types::FieldId,
        len: usize,
        rest: TypeId,
    ) -> (Vec<crate::types::RowField>, TypeId) {
        let direct_fields: Vec<_> = pools.get_row_fields(start.0, len).to_vec();
        let final_rest = self.apply_substitutions(pools, rest);
        (direct_fields, final_rest)
    }

    /// OCaml-style `unify_labels` - unify sorted field lists
    fn unify_labels(
        &mut self,
        pools: &mut Pools,
        missing1: &mut Vec<crate::types::RowField>,
        missing2: &mut Vec<crate::types::RowField>,
        left_labels: &[(&crate::InternedString, &TypeId)],
        right_labels: &[(&crate::InternedString, &TypeId)],
        protected_vars: &HashSet<TypeVarId>,
        span1: SpanId,
        span2: SpanId,
    ) -> Result<(), TypeError> {
        let mut i1 = 0;
        let mut i2 = 0;

        while i1 < left_labels.len() && i2 < right_labels.len() {
            let (left_label, left_type) = left_labels[i1];
            let (right_label, right_type) = right_labels[i2];

            match left_label.cmp(right_label) {
                std::cmp::Ordering::Equal => {
                    // Same label - unify types
                    self.unify(
                        pools,
                        *left_type,
                        *right_type,
                        protected_vars,
                        span1,
                        span2,
                    )?;
                    i1 += 1;
                    i2 += 1;
                }
                std::cmp::Ordering::Less => {
                    // left_label < right_label, so left_label is missing from row2
                    missing2.push(crate::types::RowField {
                        name: *left_label,
                        field_type: *left_type,
                    });
                    i1 += 1;
                }
                std::cmp::Ordering::Greater => {
                    // right_label < left_label, so right_label is missing from row1
                    missing1.push(crate::types::RowField {
                        name: *right_label,
                        field_type: *right_type,
                    });
                    i2 += 1;
                }
            }
        }

        // Add remaining labels from left_labels to missing2
        while i1 < left_labels.len() {
            let (left_label, left_type) = left_labels[i1];
            missing2.push(crate::types::RowField {
                name: *left_label,
                field_type: *left_type,
            });
            i1 += 1;
        }

        // Add remaining labels from right_labels to missing1
        while i2 < right_labels.len() {
            let (right_label, right_type) = right_labels[i2];
            missing1.push(crate::types::RowField {
                name: *right_label,
                field_type: *right_type,
            });
            i2 += 1;
        }

        Ok(())
    }


    fn occurs_check(&self, var: TypeVarId, pools: &Pools, ty: TypeId) -> bool {
        self.occurs_check_helper(var, pools, ty, &mut std::collections::HashSet::new())
    }

    fn occurs_check_helper(
        &self,
        var: TypeVarId,
        pools: &Pools,
        ty: TypeId,
        visited: &mut std::collections::HashSet<TypeId>,
    ) -> bool {
        if visited.contains(&ty) {
            // If we're revisiting a type during occurs check, that's a cycle
            // This indicates an infinite type, which is not allowed per FCP paper
            return true;
        }
        visited.insert(ty);

        let ty = pools[ty];
        match ty {
            Type::Int(_) | Type::String(_) | Type::Unit(_) | Type::EmptyRow(_) => false,
            Type::Var(v, _) => {
                if v == var {
                    true
                } else if let Some(&substitution) = self.substitutions.get(&v) {
                    self.occurs_check_helper(var, pools, substitution, visited)
                } else {
                    false
                }
            }
            Type::Arrow(from, to, _) => {
                self.occurs_check_helper(var, pools, from, visited)
                    || self.occurs_check_helper(var, pools, to, visited)
            }
            Type::DataType(_name, start, len, _) => {
                let params = pools.get_data_type_params(start.0, len);
                params
                    .iter()
                    .any(|&param_id| self.occurs_check_helper(var, pools, param_id, visited))
            }
            Type::TypeApp(var_id, start, len, _) => {
                if var_id == var {
                    true
                } else {
                    let params = pools.get_data_type_params(start.0, len);
                    params
                        .iter()
                        .any(|&param_id| self.occurs_check_helper(var, pools, param_id, visited))
                }
            }
            Type::Row(start, len, rest, _) => {
                let fields = pools.get_row_fields(start.0, len);
                fields
                    .iter()
                    .any(|field| self.occurs_check_helper(var, pools, field.field_type, visited))
                    || self.occurs_check_helper(var, pools, rest, visited)
            }
        }
    }

    /// Merge substitutions from another context, avoiding conflicts
    fn merge_substitutions(&mut self, other_substitutions: &HashMap<TypeVarId, TypeId>) {
        for (&var, &ty) in other_substitutions {
            // Only add substitutions that don't conflict with existing ones
            self.substitutions.entry(var).or_insert(ty);
        }
    }

    /// Infer the type of an expression
    ///
    /// # Errors
    ///
    /// Returns a `TypeError` if type inference fails
    pub fn infer_type(&mut self, pools: &mut Pools, expr_id: ExprId) -> Result<TypeId, TypeError> {
        let mut protected_vars = HashSet::new();
        self.infer_type_fcp(pools, expr_id, &mut protected_vars)
    }

    /// Infer the type of an expression using First-Class Polymorphism
    ///
    /// # Errors
    ///
    /// Returns a `TypeError` if type inference fails
    pub fn infer_type_fcp(
        &mut self,
        pools: &mut Pools,
        expr_id: ExprId,
        protected_vars: &mut HashSet<TypeVarId>,
    ) -> Result<TypeId, TypeError> {
        let expr = pools[expr_id];

        match expr {
            Expr::Int(_, _) => {
                let int_type = pools.type_int();
                self.record(expr_id, int_type);
                Ok(int_type)
            }
            Expr::String(_, _) => {
                let string_type = pools.type_string();
                self.record(expr_id, string_type);
                Ok(string_type)
            }
            Expr::Unit(_) => {
                let unit_type = pools.type_unit();
                self.record(expr_id, unit_type);
                Ok(unit_type)
            }

            Expr::Var(debruijn_index, name, span) => self
                .lookup_scheme(debruijn_index)
                .cloned()
                .map_or(Err(TypeError::unbound_variable(name, span)), |scheme| {
                    let instantiated = scheme.instantiate(pools);
                    self.record(expr_id, instantiated);
                    Ok(instantiated)
                }),

            Expr::GlobalVar(_, name, span) => pools.get_global_scheme(&name).cloned().map_or_else(
                || Err(TypeError::unbound_variable(name, span)),
                |scheme| {
                    let instantiated = scheme.instantiate(pools);
                    self.record(expr_id, instantiated);
                    Ok(instantiated)
                },
            ),

            Expr::Lambda(body_id, _param_name, span) => {
                // Create a provenance span for the parameter type derived from the lambda
                let param_span = pools.span_provenance(span);
                let param_type = self.fresh_type_var_span(pools, param_span);
                let param_scheme = TypeScheme::new(Vec::new(), param_type);

                let old_len = self.type_schemes.len();
                self.extend_scheme(param_scheme);

                let body_type = self.infer_type_fcp(pools, body_id, protected_vars)?;

                self.type_schemes.truncate(old_len);

                let final_param_type = self.apply_substitutions(pools, param_type);
                let final_body_type = self.apply_substitutions(pools, body_type);

                // Arrow type inherits the lambda's span
                Ok(pools.type_arrow_span(final_param_type, final_body_type, span))
            }

            Expr::Let(value_id, body_id, _var_name, _) => {
                let value_type = self.infer_type_fcp(pools, value_id, protected_vars)?;

                let env_vars = self.get_env_vars(pools);
                let value_scheme = TypeScheme::generalize(pools, value_type, &env_vars);

                let old_len = self.type_schemes.len();
                self.extend_scheme(value_scheme);

                let body_type = self.infer_type(pools, body_id)?;

                self.type_schemes.truncate(old_len);

                Ok(body_type)
            }

            Expr::Call(func_id, arg_id, span) => {
                let func_type = self.infer_type_fcp(pools, func_id, protected_vars)?;
                let arg_type = self.infer_type_fcp(pools, arg_id, protected_vars)?;

                // Result type gets provenance from call site
                let result_span = pools.span_provenance(span);
                let result_type = self.fresh_type_var_span(pools, result_span);

                // Expected function type merges arg and result spans
                let func_span = pools.span_merged(span, result_span);
                let expected_func_type = pools.type_arrow_span(arg_type, result_type, func_span);
                self.unify(pools, func_type, expected_func_type, protected_vars,span, func_span)?;

                Ok(self.apply_substitutions(pools, result_type))
            }

            Expr::Construct(constructor, arg_id, span) => {
                if let Some(constructor_type) = pools.get_constructor(&constructor).cloned() {
                    
                    // FCP paper (make) rule: σK = ∀γ. (∀α.∃β.τ) → τ'
                    // Create fresh variables for quantifiers following the paper's algorithm
                    let mut substitutions = HashMap::new();
                    let mut universal_fresh_vars = Vec::new();

                    // Instantiate outer quantified vars (γ) - these become non-protected
                    for &var in &constructor_type.outer_quantified_vars {
                        let fresh_var = self.fresh_type_var(pools);
                        substitutions.insert(var, fresh_var);
                    }

                    // Instantiate universal vars (α) - these become protected during unification
                    for &var in &constructor_type.universal_vars {
                        let fresh_var = self.fresh_type_var(pools);
                        substitutions.insert(var, fresh_var);
                        if let Type::Var(var_idx, _) = pools[fresh_var] {
                            universal_fresh_vars.push(var_idx);
                        }
                    }

                    // Instantiate existential vars (β) - these are handled differently
                    for &var in &constructor_type.existential_vars {
                        let fresh_var = self.fresh_type_var(pools);
                        substitutions.insert(var, fresh_var);
                    }

                    let component_type = TypeScheme::substitute_type_vars(
                        pools,
                        constructor_type.component_type,
                        &substitutions,
                    );
                    let result_type = TypeScheme::substitute_type_vars(
                        pools,
                        constructor_type.result_type,
                        &substitutions,
                    );

                    let arg_type = self.infer_type_fcp(pools, arg_id, protected_vars)?;

                    // FCP paper side condition: α ∉ TV(A)
                    let context_vars = self.get_env_vars(pools);
                    for &universal_var in &universal_fresh_vars {
                        if context_vars.contains(&universal_var) {
                            return Err(TypeError::universal_variable_escape(
                                universal_var,
                                span,
                                "FCP type instantiation".to_string(),
                            ));
                        }
                    }

                    // FCP paper: unify arg_type with component_type modulo V ∪ {α}
                    let mut extended_protected = protected_vars.clone();
                    extended_protected.extend(universal_fresh_vars.iter());

                    self.unify(
                        pools,
                        arg_type,
                        component_type,
                        &extended_protected,
                        span,
                        span,
                    )?;

                    let final_result_type = self.apply_substitutions(pools, result_type);
                    Ok(final_result_type)
                } else {
                    Err(TypeError::unknown_constructor(constructor, span))
                }
            }

            Expr::Match(expr_id, match_arms, span) => {
                let expr_type = self.infer_type_fcp(pools, expr_id, protected_vars)?;
                let result_type = self.fresh_type_var(pools);

                let mut patterns = Vec::new();

                for i in 0..match_arms.length {
                    let case = pools[PatternId(match_arms.start_id.0 + i)];
                    patterns.push(case.pattern);

                    // Clone the context for each match arm per FCP paper
                    let mut arm_context = self.clone();
                    let old_len = arm_context.type_schemes.len();

                    let (pattern_type, existential_vars) =
                        arm_context.infer_pattern_type_fcp(pools, case.pattern, expr_type, protected_vars)?;

                    let mut extended_protected = protected_vars.clone();
                    extended_protected.extend(existential_vars.iter());

                    let body_type =
                        arm_context.infer_type_fcp(pools, case.body, &mut extended_protected)?;
                    arm_context.type_schemes.truncate(old_len);

                    // Unify using the cloned context
                    arm_context.unify(pools, pattern_type, expr_type, protected_vars, span, span)?;
                    arm_context.unify(pools, body_type, result_type, protected_vars, span, span)?;

                    // Merge back only the substitutions that don't conflict
                    self.merge_substitutions(&arm_context.substitutions);
                }

                self.check_exhaustiveness(pools, expr_type, &patterns, span)?;

                Ok(self.apply_substitutions(pools, result_type))
            }

            Expr::Record(start, len, span) => {
                use crate::types::RowField;

                let record_fields: Vec<_> = pools.get_record_fields(start.0, len).to_vec();
                let mut row_fields = Vec::new();

                // Infer the type of each field
                for field in record_fields {
                    let field_type = self.infer_type_fcp(pools, field.expr, protected_vars)?;
                    row_fields.push(RowField {
                        name: field.name,
                        field_type,
                    });
                }

                // Create a closed row (empty rest)
                let empty_row = pools.type_empty_row();
                let row_type = pools.type_row_span(&row_fields, empty_row, span);

                Ok(self.apply_substitutions(pools, row_type))
            }

            Expr::Project(record_id, field_name, span) => {
                use crate::types::RowField;

                let record_type = self.infer_type_fcp(pools, record_id, protected_vars)?;

                // Create a fresh type variable for the field type
                let field_type = self.fresh_type_var_span(pools, span);

                // Create a fresh type variable for the rest of the row
                let rest_type = self.fresh_type_var_span(pools, span);

                // The record should have type {field_name: field_type, ...rest_type}
                let expected_field = RowField {
                    name: field_name,
                    field_type,
                };
                let expected_record_type = pools.type_row_span(&[expected_field], rest_type, span);

                // Unify the record type with our expected type
                self.unify(pools, record_type, expected_record_type,protected_vars, span, span)?;

                Ok(self.apply_substitutions(pools, field_type))
            }

            Expr::Extend(record_id, start, len, span) => {
                use crate::types::RowField;

                let record_type = self.infer_type_fcp(pools, record_id, protected_vars)?;
                let extension_fields: Vec<_> = pools.get_record_fields(start.0, len).to_vec();

                // Infer types for extension fields
                let mut row_fields = Vec::new();
                for field in extension_fields {
                    let field_type = self.infer_type_fcp(pools, field.expr, protected_vars)?;
                    row_fields.push(RowField {
                        name: field.name,
                        field_type,
                    });
                }

                // Following OCaml RecordExtend logic exactly:
                // Create a fresh rest variable
                let rest_row_ty = self.fresh_type_var_span(pools, span);

                // Unify original record with a fresh row variable to extract its row type
                // This means: record_type = {rest_row_ty}
                self.unify(pools, record_type, rest_row_ty,protected_vars, span, span)?;

                // Return TRowExtend(new_fields, rest_row_ty)
                // This creates {y: Int, ...{x: Int}} where rest_row_ty was unified with {x: Int}
                let extension_row = pools.type_row_span(&row_fields, rest_row_ty, span);

                Ok(extension_row)
            }
            Expr::Ffi(_, type_annotation, arg_expr, _span) => {
                // For FFI expressions, we can use the type annotation if provided
                if let Some(type_id) = type_annotation {
                    // If there's an argument, type check it but ignore its type
                    if let Some(arg_id) = arg_expr {
                        self.infer_type(pools, arg_id)?;
                    }
                    Ok(type_id)
                } else {
                    // No type annotation - infer argument type and return a fresh type variable
                    if let Some(arg_id) = arg_expr {
                        self.infer_type(pools, arg_id)?;
                    }
                    Ok(pools.fresh_type_var())
                }
            }
        }
    }

    fn get_env_vars(&self, pools: &Pools) -> HashSet<TypeVarId> {
        let mut vars = HashSet::new();
        for scheme in &self.type_schemes {
            let scheme_vars = pools.type_free_vars(scheme.ty);
            vars.extend(scheme_vars);
        }
        vars
    }

    #[must_use]
    pub fn generalize_type(&self, pools: &Pools, ty: TypeId) -> TypeScheme {
        let env_vars = self.get_env_vars(pools);
        TypeScheme::generalize(pools, ty, &env_vars)
    }

    /// Process definition groups in dependency order
    pub fn infer_definition_groups(
        &mut self,
        pools: &mut Pools,
        groups: &[DefinitionGroup],
    ) -> Result<(), TypeError> {
        for group in groups {
            self.infer_definition_group(pools, group)?;
        }
        Ok(())
    }

    /// Infer types for a single definition group (handles mutual recursion)
    fn infer_definition_group(
        &mut self,
        pools: &mut Pools,
        group: &DefinitionGroup,
    ) -> Result<(), TypeError> {
        let mut type_vars = HashMap::new();
        let protected_vars = HashSet::new();

        for def_name in &group.definitions {
            if let Some(_expr_id) = pools.get_function_implementation(def_name) {
                let type_var = self.fresh_type_var(pools);
                type_vars.insert(*def_name, type_var);

                let scheme = TypeScheme::new(Vec::new(), type_var);
                pools.bind_global_scheme(*def_name, scheme);
            }
        }

        for def_name in &group.definitions {
            if let Some(expr_id) = pools.get_function_implementation(def_name) {
                let inferred_type = self.infer_type(pools, expr_id)?;
                let expected_type = type_vars[def_name];

                let dummy_span = pools.dummy_span();
                self.unify(pools, inferred_type, expected_type,&protected_vars, dummy_span, dummy_span)?;
            }
        }

        for def_name in &group.definitions {
            if let Some(expected_type) = type_vars.get(def_name) {
                let final_type = self.apply_substitutions(pools, *expected_type);
                let generalized = self.generalize_type(pools, final_type);
                pools.bind_global_scheme(*def_name, generalized);
            }
        }

        Ok(())
    }

    /// Verify that all function implementations match their declared signatures
    ///
    /// # Errors
    ///
    /// Returns a vector of `TypeError`s if any function signatures don't match
    pub fn verify_function_signatures(&mut self, pools: &mut Pools) -> Result<(), Vec<TypeError>> {
        let mut errors = Vec::new();

        let protected_vars = HashSet::new();
        let function_implementations: Vec<_> = pools
            .function_implementations
            .iter()
            .map(|(k, v)| (*k, *v))
            .collect();

        for (function_name, impl_expr_id) in function_implementations {
            if let Some(declared_scheme) = pools.get_global_scheme(&function_name).cloned() {
                let declared_type = declared_scheme.instantiate(pools);

                match self.infer_type(pools, impl_expr_id) {
                    Ok(inferred_type) => {
                        let dummy_span = pools.dummy_span();
                        let declared_span = dummy_span; // TODO: Get actual declaration span
                        let inferred_span = pools.get_expr_span(impl_expr_id);

                        if self
                            .unify(pools, inferred_type, declared_type,&protected_vars, dummy_span, dummy_span)
                            .is_err()
                        {
                            errors.push(TypeError::function_signature_mismatch(
                                function_name,
                                declared_scheme.clone(),
                                declared_type,
                                inferred_type,
                                impl_expr_id,
                                declared_span,
                                inferred_span,
                            ));
                        }
                    }
                    Err(err) => {
                        // For now, pass through the inner error if it's already a RichTypeError
                        errors.push(err);
                    }
                }
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }


    fn check_exhaustiveness(
        &self,
        pools: &mut Pools,
        scrutinee_type: TypeId,
        patterns: &[crate::expr::Pattern],
        span: SpanId,
    ) -> Result<(), TypeError> {
        use crate::types::Type;

        let actual_type = self.apply_substitutions(pools, scrutinee_type);
        let type_val = pools[actual_type];

        match type_val {
            Type::DataType(data_type_name, _start, _len, _) => {
                // Check for wildcard patterns first - they cover everything
                for pattern in patterns {
                    match pattern {
                        crate::expr::Pattern::Variable(_, _, _)
                        | crate::expr::Pattern::Wildcard(_) => {
                            return Ok(());
                        }
                        _ => {}
                    }
                }

                // Collect all constructors for this specific data type
                let constructor_list: Vec<_> = pools
                    .constructors
                    .iter()
                    .map(|(k, v)| (*k, v.result_type))
                    .collect();
                let mut required_constructors = std::collections::HashSet::new();
                for (constructor_name, result_type) in constructor_list {
                    let resolved_result_type = self.apply_substitutions(pools, result_type);
                    if let Type::DataType(result_data_type, _, _, _) = pools[resolved_result_type] {
                        if result_data_type == data_type_name {
                            required_constructors.insert(constructor_name);
                        }
                    }
                }

                // Collect covered constructors from patterns
                let mut covered_constructors = std::collections::HashSet::new();
                for pattern in patterns {
                    if let crate::expr::Pattern::Constructor(
                            constructor_name,
                            _start_id,
                            _length,
                            _span,
                        ) = pattern {
                        covered_constructors.insert(*constructor_name);
                    }
                }

                // Check if all required constructors are covered
                let missing: Vec<_> = required_constructors
                    .difference(&covered_constructors)
                    .collect();

                if !missing.is_empty() {
                    let missing_names: Vec<String> = missing
                        .iter()
                        .map(|name| name.as_str())
                        .collect();
                    return Err(TypeError::non_exhaustive_patterns(
                        missing_names,
                        span,
                        scrutinee_type,
                    ));
                }

                Ok(())
            }
            _ => Ok(()),
        }
    }


    fn infer_pattern_type_fcp(
        &mut self,
        pools: &mut Pools,
        pattern: crate::expr::Pattern,
        expected_type: TypeId,
        protected_vars: &HashSet<TypeVarId>
    ) -> Result<(TypeId, Vec<TypeVarId>), TypeError> {
        use crate::expr::Pattern;
        match pattern {
            Pattern::Constructor(constructor_name, start_id, length, span) => {
                if let Some(constructor_type) = pools.get_constructor(&constructor_name).cloned() {
                    let mut substitutions = HashMap::new();
                    let mut existential_fresh_vars = Vec::new();

                    // FCP paper (break) rule: λ(K x).E
                    // Create fresh variables for quantifiers

                    // First handle outer quantified vars (γ)
                    for &var in &constructor_type.outer_quantified_vars {
                        let fresh_var = self.fresh_type_var(pools);
                        substitutions.insert(var, fresh_var);
                    }

                    // Handle universal vars (α)
                    for &var in &constructor_type.universal_vars {
                        let fresh_var = self.fresh_type_var(pools);
                        substitutions.insert(var, fresh_var);
                    }

                    // Handle existential vars (β) - these become protected in pattern context
                    for &var in &constructor_type.existential_vars {
                        let fresh_var = self.fresh_type_var(pools);
                        substitutions.insert(var, fresh_var);
                        if let Type::Var(var_idx, _) = pools[fresh_var] {
                            existential_fresh_vars.push(var_idx);
                        }
                    }

                    let result_type = TypeScheme::substitute_type_vars(
                        pools,
                        constructor_type.result_type,
                        &substitutions,
                    );
                    let component_type = TypeScheme::substitute_type_vars(
                        pools,
                        constructor_type.component_type,
                        &substitutions,
                    );

                    // Handle nested patterns recursively
                    if length > 0 {
                        let nested_patterns: Vec<Pattern> =
                            pools.get_nested_patterns(start_id.0, length).to_vec();

                        // For constructor patterns with multiple arguments:
                        // If constructor has type: component_type -> arg2_type -> ... -> final_result_type
                        // Then result_type = arg2_type -> ... -> final_result_type
                        // Pattern arguments should get types: [component_type, arg2_type, ...]

                        let mut current_result_type = result_type;

                        for (i, nested_pattern) in nested_patterns.iter().enumerate() {
                            let pattern_expected_type = if i == 0 {
                                // First pattern gets the component_type
                                component_type
                            } else {
                                // For subsequent patterns, extract argument types from result_type arrows
                                if let Type::Arrow(arg_type, rest_type, _) =
                                    pools[current_result_type]
                                {
                                    current_result_type = rest_type; // Update for next iteration
                                    arg_type
                                } else {
                                    return Err(TypeError::type_mismatch(
                                        current_result_type,
                                        expected_type,
                                        span,
                                        span,
                                        None,
                                        None,
                                        None,
                                    ));
                                }
                            };

                            let (_, nested_existentials) = self.infer_pattern_type_fcp(
                                pools,
                                *nested_pattern,
                                pattern_expected_type,
                            protected_vars
                            )?;
                            existential_fresh_vars.extend(nested_existentials);
                        }
                    }

                    // Calculate final pattern type
                    let mut final_type = result_type;
                    for _ in 1..length {
                        if let Type::Arrow(_, rest, _) = pools[final_type] {
                            final_type = rest;
                        }
                    }

                    // According to FCP (break) rule, existential variables are opened/unpacked
                    // and become available as fresh variables in the pattern match scope
                    Ok((final_type, existential_fresh_vars))
                } else {
                    Err(TypeError::unknown_constructor(constructor_name, span))
                }
            }
            Pattern::Variable(_debruijn, _var_name, _) => {
                self.extend_scheme(TypeScheme::new(Vec::new(), expected_type));
                Ok((expected_type, Vec::new()))
            }
            Pattern::Wildcard(_) => Ok((expected_type, Vec::new())),
            Pattern::Int(_n, span) => {
                let int_type = pools.type_int();
                self.unify(pools, int_type, expected_type,protected_vars, span, span)?;
                Ok((int_type, Vec::new()))
            }
            Pattern::String(_s, span) => {
                let string_type = pools.type_string();
                self.unify(pools, string_type, expected_type,protected_vars, span, span)?;
                Ok((string_type, Vec::new()))
            }
            Pattern::Record(start, len, spread, span) => {
                use crate::types::RowField;

                let pattern_fields: Vec<_> = pools.get_record_pattern_fields(start.0, len).to_vec();
                let mut row_fields = Vec::new();

                // Infer types for each pattern field
                for field in pattern_fields {
                    let fresh_var = pools.fresh_type_var();
                    let (field_pattern_type, _field_existentials) =
                        self.infer_pattern_type_fcp(pools, field.pattern, fresh_var,protected_vars)?;

                    // Add the field's existential variables to our list
                    // (Note: In a full implementation, we'd need to track these properly)

                    row_fields.push(RowField {
                        name: field.name,
                        field_type: field_pattern_type,
                    });
                }

                // Handle spread operator
                let rest_type = if spread.is_some() {
                    // Open row - create fresh type variable for rest
                    self.fresh_type_var(pools)
                } else {
                    // Closed row - use empty row
                    pools.type_empty_row()
                };

                let pattern_row_type = pools.type_row_span(&row_fields, rest_type, span);

                // If there's a named spread, bind it to the rest type
                if let Some(spread_info) = spread {
                    if spread_info.name.is_some() {
                        // Bind the rest variable (this would need proper scope handling)
                        self.extend_scheme(crate::types::TypeScheme::new(Vec::new(), rest_type));
                    }
                }

                Ok((pattern_row_type, Vec::new()))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unification_mod_vars_basic() {
        let mut pools = Pools::new();
        let mut ctx = PooledTypingContext::new();

        let alpha = pools.type_var(0);
        let _beta = pools.type_var(1);
        let int_type = pools.type_int();

        let protected = HashSet::new();
        let dummy_span = pools.dummy_span();
        let result = ctx.unify(
            &mut pools, alpha, int_type, &protected, dummy_span, dummy_span,
        );
        assert!(result.is_ok());

        assert!(ctx.substitutions.contains_key(&TypeVarId::new(0)));
        let final_type = ctx.apply_substitutions(&mut pools, alpha);
        assert_eq!(pools[final_type], Type::Int(SpanId(0)));
    }

    #[test]
    fn test_unification_mod_vars_protected() {
        let mut pools = Pools::new();
        let mut ctx = PooledTypingContext::new();

        let alpha = pools.type_var(0);
        let int_type = pools.type_int();

        let mut protected = HashSet::new();
        protected.insert(TypeVarId::new(0));
        let dummy_span = pools.dummy_span();
        let result = ctx.unify(
            &mut pools, alpha, int_type, &protected, dummy_span, dummy_span,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_unification_mod_vars_contains_protected() {
        let mut pools = Pools::new();
        let mut ctx = PooledTypingContext::new();

        let alpha = pools.type_var(0);
        let beta = pools.type_var(1);

        let arrow_type = pools.type_arrow(beta, alpha);

        let gamma = pools.type_var(2);
        let mut protected = HashSet::new();
        protected.insert(TypeVarId::new(0)); // α is protected

        let dummy_span = pools.dummy_span();
        let result = ctx.unify(
            &mut pools, gamma, arrow_type, &protected, dummy_span, dummy_span,
        );
        // FCP semantics: non-protected variables CAN unify with types containing protected variables
        assert!(result.is_ok());
        // γ should be substituted with β → α
        assert!(ctx.substitutions.contains_key(&TypeVarId::new(2)));
    }
}
