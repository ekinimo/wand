use crate::InternedString;
use crate::pools::{Kind, KindId, Pools, TypeId};
use crate::types::Type;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum KindError {
    KindMismatch {
        expected: KindId,
        actual: KindId,
    },
    UnboundTypeConstructor(InternedString),
    ArityMismatch {
        constructor: InternedString,
        expected: usize,
        actual: usize,
    },
    InfiniteKind,
    IllFormedType(TypeId),
}

impl std::fmt::Display for KindError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::KindMismatch { expected, actual } => {
                write!(
                    f,
                    "Kind mismatch: expected kind {expected:?}, got {actual:?}"
                )
            }
            Self::UnboundTypeConstructor(name) => {
                write!(f, "Unbound type constructor: {name:?}")
            }
            Self::ArityMismatch {
                constructor,
                expected,
                actual,
            } => {
                write!(
                    f,
                    "Type constructor {constructor:?} expects {expected} arguments, got {actual}"
                )
            }
            Self::InfiniteKind => {
                write!(f, "Infinite kind detected during unification")
            }
            Self::IllFormedType(type_id) => {
                write!(f, "Ill-formed type: {type_id:?}")
            }
        }
    }
}

impl std::error::Error for KindError {}

pub struct KindChecker<'a> {
    pools: &'a mut Pools,
    kind_substitution: HashMap<KindId, KindId>,
    _next_kind_var: usize,
}

impl<'a> KindChecker<'a> {
    pub fn new(pools: &'a mut Pools) -> Self {
        Self {
            pools,
            kind_substitution: HashMap::new(),
            _next_kind_var: 0,
        }
    }

    /// Infer the kind of a type expression
    ///
    /// # Errors
    ///
    /// Returns a `KindError` if kind inference fails
    pub fn infer_kind(&mut self, type_id: TypeId) -> Result<KindId, KindError> {
        let type_copy = self.pools.types[type_id.0];
        match type_copy {
            Type::Int(_) | Type::String(_) | Type::Unit(_) => Ok(self.pools.kind_star()),
            Type::Var(_, _) => {
                // Type variables have kind *
                Ok(self.pools.kind_star())
            }
            Type::Arrow(from, to, _) => {
                // τ₁ → τ₂ has kind * if both τ₁ and τ₂ have kind *
                let from_kind = self.infer_kind(from)?;
                let to_kind = self.infer_kind(to)?;
                let star = self.pools.kind_star();

                self.unify_kinds(from_kind, star)?;
                self.unify_kinds(to_kind, star)?;

                Ok(star)
            }
            Type::DataType(name, start, len, _) => {
                // Look up the kind of the type constructor
                let constructor_kind = self
                    .pools
                    .get_type_constructor_kind(&name)
                    .ok_or(KindError::UnboundTypeConstructor(name))?;

                // Get the parameter types
                let param_types: Vec<TypeId> =
                    self.pools.get_data_type_params(start.0, len).to_vec();

                // Apply the constructor to its arguments
                self.apply_constructor_kind(constructor_kind, &param_types, name)
            }
            Type::TypeApp(_var_id, start, len, _) => {
                // For type applications like `m a`, we need to infer the kind of
                // the type variable and apply it to the argument types

                // Get the parameter types
                let param_types: Vec<TypeId> =
                    self.pools.get_data_type_params(start.0, len).to_vec();

                // For now, assume the type variable has the appropriate kind
                // In a full implementation, we'd track type variable kinds
                let star = self.pools.kind_star();

                // All parameters should have kind *
                for &param_type in &param_types {
                    let param_kind = self.infer_kind(param_type)?;
                    self.unify_kinds(param_kind, star)?;
                }

                // Result has kind *
                Ok(star)
            }
            Type::EmptyRow(_) => {
                // Empty row has kind *
                Ok(self.pools.kind_star())
            }
            Type::Row(start, len, rest, _) => {
                // Row types have kind *
                let star = self.pools.kind_star();

                // Check that all field types have kind *
                let fields: Vec<_> = self.pools.get_row_fields(start.0, len).to_vec();
                for field in fields {
                    let field_kind = self.infer_kind(field.field_type)?;
                    self.unify_kinds(field_kind, star)?;
                }

                // Check that the rest type has kind *
                let rest_kind = self.infer_kind(rest)?;
                self.unify_kinds(rest_kind, star)?;

                Ok(star)
            }
        }
    }

    /// Apply a type constructor of given kind to a list of type arguments
    fn apply_constructor_kind(
        &mut self,
        mut constructor_kind: KindId,
        args: &[TypeId],
        constructor_name: InternedString,
    ) -> Result<KindId, KindError> {
        let expected_arity = self.count_kind_arrows(constructor_kind);
        if args.len() != expected_arity {
            return Err(KindError::ArityMismatch {
                constructor: constructor_name,
                expected: expected_arity,
                actual: args.len(),
            });
        }

        for arg in args {
            let arg_kind = self.infer_kind(*arg)?;
            let kind = self.pools.kinds[constructor_kind.0];
            match kind {
                Kind::Arrow(param_kind, result_kind) => {
                    self.unify_kinds(arg_kind, param_kind)?;
                    constructor_kind = result_kind;
                }
                Kind::Star => {
                    return Err(KindError::ArityMismatch {
                        constructor: constructor_name,
                        expected: 0,
                        actual: args.len(),
                    });
                }
            }
        }

        Ok(constructor_kind)
    }

    /// Count the number of arrows in a kind (i.e., the arity)
    fn count_kind_arrows(&self, kind: KindId) -> usize {
        match self.pools.kinds.get(kind.0).copied().unwrap_or(Kind::Star) {
            Kind::Star => 0,
            Kind::Arrow(_, result) => 1 + self.count_kind_arrows(result),
        }
    }

    /// Unify two kinds
    ///
    /// # Errors
    ///
    /// Returns a `KindError` if the kinds cannot be unified
    pub fn unify_kinds(&mut self, k1: KindId, k2: KindId) -> Result<(), KindError> {
        let k1 = self.deref_kind(k1);
        let k2 = self.deref_kind(k2);

        if k1 == k2 {
            return Ok(());
        }

        let k1_kind = self.pools.kinds[k1.0];
        let k2_kind = self.pools.kinds[k2.0];
        match (k1_kind, k2_kind) {
            (Kind::Star, Kind::Star) => Ok(()),
            (Kind::Arrow(from1, to1), Kind::Arrow(from2, to2)) => {
                self.unify_kinds(from1, from2)?;
                self.unify_kinds(to1, to2)
            }
            _ => Err(KindError::KindMismatch {
                expected: k1,
                actual: k2,
            }),
        }
    }

    /// Dereference a kind through the substitution
    fn deref_kind(&self, kind: KindId) -> KindId {
        self.kind_substitution.get(&kind).copied().unwrap_or(kind)
    }

    /// Check if a type is well-kinded
    ///
    /// # Errors
    ///
    /// Returns a `KindError` if the type is not well-kinded
    pub fn check_type_well_kinded(&mut self, type_id: TypeId) -> Result<(), KindError> {
        let kind = self.infer_kind(type_id)?;
        let star = self.pools.kind_star();
        self.unify_kinds(kind, star)?;
        Ok(())
    }

    /// Check if a data type definition is well-kinded
    ///
    /// # Errors
    ///
    /// Returns a `KindError` if the data type definition is not well-kinded
    pub fn check_data_type_definition(
        &mut self,
        type_name: InternedString,
        type_params: &[InternedString],
        constructors: &[(InternedString, Option<TypeId>)],
    ) -> Result<(), KindError> {
        // Compute and bind the kind for this type constructor
        let data_kind = self.pools.compute_data_type_kind(type_params);
        self.pools.bind_type_constructor_kind(type_name, data_kind);

        // Check each constructor's component type (if any)
        for (_, component_type) in constructors {
            if let Some(comp_type) = component_type {
                self.check_type_well_kinded(*comp_type)?;
            }
        }

        Ok(())
    }

    /// Validate that quantified types in constructor definitions are well-formed
    ///
    /// # Errors
    ///
    /// Returns a `KindError` if the quantified types are not well-formed
    pub fn check_constructor_quantified_types(
        &mut self,
        component_type: TypeId,
        _type_params: &[InternedString],
    ) -> Result<(), KindError> {
        // For quantified types like ∀α.∃β.τ, we need to ensure:
        // 1. All type variables in τ are properly bound
        // 2. The kinds work out correctly
        // 3. Higher-kinded variables (like m in m a) have appropriate kinds

        // This is a simplified check - in a full implementation, we'd need
        // to track the scope of quantified variables and their kinds
        self.check_type_well_kinded(component_type)
    }
}

/// Convenience function to check if a type is well-kinded
///
/// # Errors
///
/// Returns a `KindError` if the type is not well-kinded
pub fn check_type_kinds(pools: &mut Pools, type_id: TypeId) -> Result<(), KindError> {
    let mut checker = KindChecker::new(pools);
    checker.check_type_well_kinded(type_id)
}

/// Check a data type definition for kind correctness
///
/// # Errors
///
/// Returns a `KindError` if the data type definition is not well-kinded
pub fn check_data_definition_kinds(
    pools: &mut Pools,
    type_name: InternedString,
    type_params: &[InternedString],
    constructors: &[(InternedString, Option<TypeId>)],
) -> Result<(), KindError> {
    let mut checker = KindChecker::new(pools);
    checker.check_data_type_definition(type_name, type_params, constructors)
}
