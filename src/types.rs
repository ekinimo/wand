use crate::InternedString;
use crate::pools::{Pools, SpanId, TypeId, TypeVarId};
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FieldId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RowField {
    pub name: InternedString,
    pub field_type: TypeId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Int(SpanId),
    String(SpanId),
    Unit(SpanId),
    Var(TypeVarId, SpanId),
    Arrow(TypeId, TypeId, SpanId),
    DataType(crate::InternedString, TypeId, usize, SpanId), // T τ1 ... τn - name, start, len
    TypeApp(TypeVarId, TypeId, usize, SpanId), // α τ1 ... τn - higher-kinded type variable application
    // Row polymorphism types
    EmptyRow(SpanId),                    // Empty row type {}
    Row(FieldId, usize, TypeId, SpanId), // Row type {field1: τ1, ..., fieldn: τn, ...rest} - start, len, rest
}

#[derive(Debug, Clone)]
pub struct ConstructorType {
    pub outer_quantified_vars: Vec<TypeVarId>, // ∀γ (outer quantifiers from paper)
    pub universal_vars: Vec<TypeVarId>,        // ∀α
    pub existential_vars: Vec<TypeVarId>,      // ∃β
    pub component_type: TypeId,                // τ'
    pub result_type: TypeId,                   // τ
}

impl Pools {
    #[must_use]
    pub const fn display_type(&self, id: TypeId) -> TypeDisplay {
        TypeDisplay { pool: self, id }
    }

    #[must_use]
    pub fn free_vars(&self, id: TypeId) -> HashSet<TypeVarId> {
        let mut vars = HashSet::new();
        self.collect_free_vars(id, &mut vars);
        vars
    }

    fn collect_free_vars(&self, id: TypeId, vars: &mut HashSet<TypeVarId>) {
        let ty = self[id];
        match ty {
            Type::Int(_) | Type::String(_) | Type::Unit(_) | Type::EmptyRow(_) => {}
            Type::Var(var_id, _) => {
                vars.insert(var_id);
            }
            Type::Arrow(from_id, to_id, _) => {
                self.collect_free_vars(from_id, vars);
                self.collect_free_vars(to_id, vars);
            }
            Type::DataType(_name, start, len, _) => {
                let params = self.get_data_type_params(start.0, len);
                for &param_id in params {
                    self.collect_free_vars(param_id, vars);
                }
            }
            Type::TypeApp(_var_id, start, len, _) => {
                // Don't include TypeApp head variables in free vars for generalization
                // The head variable represents a type constructor that should be generalized
                let params = self.get_data_type_params(start.0, len);
                for &param_id in params {
                    self.collect_free_vars(param_id, vars);
                }
            }
            Type::Row(start, len, rest_id, _) => {
                let fields = self.get_row_fields(start.0, len);
                for field in fields {
                    self.collect_free_vars(field.field_type, vars);
                }
                self.collect_free_vars(rest_id, vars);
            }
        }
    }
}

pub struct TypeDisplay<'a> {
    pool: &'a Pools,
    id: TypeId,
}

impl fmt::Display for TypeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut mapping = HashMap::new();
        let mut next_var = 0;
        self.fmt_with_mapping(f, self.id, &mut mapping, &mut next_var)
    }
}

impl TypeDisplay<'_> {
    fn format_type_var(
        &self,
        f: &mut fmt::Formatter<'_>,
        var_id: TypeVarId,
        mapping: &mut HashMap<TypeVarId, usize>,
        next_var: &mut usize,
    ) -> fmt::Result {
        if let Some(name) = var_id.name() {
            write!(f, "{}", name.as_str())
        } else if let Some(&mapped_var) = mapping.get(&var_id) {
            write!(f, "α{mapped_var}")
        } else {
            mapping.insert(var_id, *next_var);
            write!(f, "α{}", *next_var)?;
            *next_var += 1;
            Ok(())
        }
    }

    fn fmt_with_mapping(
        &self,
        f: &mut fmt::Formatter<'_>,
        id: TypeId,
        mapping: &mut HashMap<TypeVarId, usize>,
        next_var: &mut usize,
    ) -> fmt::Result {
        let ty = self.pool[id];
        match ty {
            Type::Int(_) => write!(f, "Int"),
            Type::String(_) => write!(f, "String"),
            Type::Unit(_) => write!(f, "()"),
            Type::Var(var_id, _) => {
                self.format_type_var(f, var_id, mapping, next_var)
            }
            Type::Arrow(from_id, to_id, _) => {
                let from_ty = self.pool[from_id];
                let needs_parens = matches!(from_ty, Type::Arrow(..));

                if needs_parens {
                    write!(f, "(")?;
                    self.fmt_with_mapping(f, from_id, mapping, next_var)?;
                    write!(f, ") → ")?;
                } else {
                    self.fmt_with_mapping(f, from_id, mapping, next_var)?;
                    write!(f, " → ")?;
                }

                self.fmt_with_mapping(f, to_id, mapping, next_var)
            }
            Type::DataType(name, start, len, _) => {
                write!(f, "{name}")?;
                if len > 0 {
                    let params = self.pool.get_data_type_params(start.0, len);
                    for &param_id in params {
                        write!(f, " ")?;
                        let param_ty = self.pool[param_id];
                        let needs_parens = match param_ty {
                            Type::Arrow(..) => true,
                            Type::DataType(_, _, n, _) if n > 0 => true,
                            Type::TypeApp(_, _, n, _) if n > 0 => true,
                            _ => false,
                        };
                        if needs_parens {
                            write!(f, "(")?;
                            self.fmt_with_mapping(f, param_id, mapping, next_var)?;
                            write!(f, ")")?;
                        } else {
                            self.fmt_with_mapping(f, param_id, mapping, next_var)?;
                        }
                    }
                }
                Ok(())
            }
            Type::TypeApp(var_id, start, len, _) => {
                self.format_type_var(f, var_id, mapping, next_var)?;
                if len > 0 {
                    let params = self.pool.get_data_type_params(start.0, len);
                    for &param_id in params {
                        write!(f, " ")?;
                        let param_ty = self.pool[param_id];
                        let needs_parens = match param_ty {
                            Type::Arrow(..) => true,
                            Type::DataType(_, _, n, _) if n > 0 => true,
                            Type::TypeApp(_, _, n, _) if n > 0 => true,
                            _ => false,
                        };
                        if needs_parens {
                            write!(f, "(")?;
                            self.fmt_with_mapping(f, param_id, mapping, next_var)?;
                            write!(f, ")")?;
                        } else {
                            self.fmt_with_mapping(f, param_id, mapping, next_var)?;
                        }
                    }
                }
                Ok(())
            }
            Type::EmptyRow(_) => write!(f, "{{}}"),
            Type::Row(start, len, rest_id, _) => {
                write!(f, "{{")?;
                let fields = self.pool.get_row_fields(start.0, len);
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: ", field.name.as_str())?;
                    self.fmt_with_mapping(f, field.field_type, mapping, next_var)?;
                }

                // Check if rest is not empty
                let rest_ty = self.pool[rest_id];
                if !matches!(rest_ty, Type::EmptyRow(_)) {
                    if len > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "...")?;
                    self.fmt_with_mapping(f, rest_id, mapping, next_var)?;
                }
                write!(f, "}}")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeScheme {
    pub quantified: Vec<TypeVarId>,
    pub ty: TypeId,
}

impl TypeScheme {
    pub fn new(quantified: impl Into<Vec<TypeVarId>>, ty: TypeId) -> Self {
        Self {
            quantified: quantified.into(),
            ty,
        }
    }

    #[must_use]
    pub fn generalize(type_pool: &Pools, ty: TypeId, env_vars: &HashSet<TypeVarId>) -> Self {
        let free_in_type = type_pool.free_vars(ty);
        let mut quantified: Vec<_> = free_in_type
            .into_iter()
            .filter(|var| !env_vars.contains(var))
            .collect();

        quantified.sort_unstable();

        Self::new(quantified, ty)
    }

    pub fn instantiate(&self, type_pool: &mut Pools) -> TypeId {
        let mut substitutions = HashMap::new();

        for &var in &self.quantified {
            let fresh_var = type_pool.fresh_type_var();
            substitutions.insert(var, fresh_var);
        }

        Self::substitute_type_vars(type_pool, self.ty, &substitutions)
    }




    pub fn substitute_type_vars(
        pools: &mut Pools,
        ty: TypeId,
        substitutions: &HashMap<TypeVarId, TypeId>,
    ) -> TypeId {
 let ty_val = pools[ty];
        match ty_val {
            Type::Int(_) => pools.type_int(),
            Type::String(_) => pools.type_string(),
            Type::Unit(_) => pools.type_unit(),
            Type::EmptyRow(_) => pools.type_empty_row(),
            Type::Var(var_id, _) => {
                if let Some(&replacement) = substitutions.get(&var_id) {
                    replacement
                } else {
                    pools.type_var(var_id.id())
                }
            }
            Type::Arrow(from_id, to_id, _) => {
                let new_from = Self::substitute_type_vars(pools, from_id, substitutions);
                let new_to = Self::substitute_type_vars(pools, to_id, substitutions);
                pools.type_arrow(new_from, new_to)
            }
            Type::DataType(name, start, len, _) => {
                let params: Vec<TypeId> = pools.get_data_type_params(start.0, len).to_vec();
                let new_params: Vec<TypeId> = params
                    .iter()
                    .map(|&param_id| Self::substitute_type_vars(pools, param_id, substitutions))
                    .collect();
                pools.data_type(name, &new_params)
            }

            Type::TypeApp(var_id, start, len, _) => {
                let params: Vec<TypeId> = pools.get_data_type_params(start.0, len).to_vec();
                let new_params: Vec<TypeId> = params
                    .iter()
                    .map(|&param_id| Self::substitute_type_vars(pools, param_id, substitutions))
                    .collect();

                if let Some(&replacement) = substitutions.get(&var_id) {
                    // If the type variable has a replacement, we need to handle it carefully
                    match pools[replacement] {
                        Type::Var(new_var_id, _) => {
                            // If replacement is a variable, create TypeApp with new variable
                            pools.type_app(new_var_id.0, &new_params)
                        }
                        _ => {
                            // For other types (Arrow, primitives), just return the replacement
                            // This handles cases where a type variable is unified with a concrete type
                            replacement
                        }
                    }
                } else {
                    pools.type_app(var_id.0, &new_params)
                }
            }
            Type::Row(start, len, rest_id, _) => {
                use crate::types::RowField;
                let fields: Vec<RowField> = pools.get_row_fields(start.0, len).to_vec();
                let new_fields: Vec<RowField> = fields
                    .iter()
                    .map(|field| RowField {
                        name: field.name,
                        field_type: Self::substitute_type_vars(
                            pools,
                            field.field_type,
                            substitutions,
                        ),
                    })
                    .collect();
                let new_rest = Self::substitute_type_vars(pools, rest_id, substitutions);
                pools.type_row(&new_fields, new_rest)
            }
        }

    }

    #[must_use]
    pub const fn display<'a>(&'a self, type_pool: &'a Pools) -> TypeSchemeDisplay<'a> {
        TypeSchemeDisplay {
            scheme: self,
            type_pool,
        }
    }
}

pub struct TypeSchemeDisplay<'a> {
    scheme: &'a TypeScheme,
    type_pool: &'a Pools,
}

impl fmt::Display for TypeSchemeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut mapping = HashMap::new();
        let mut next_var = 0;

        if self.scheme.quantified.is_empty() {
            // Empty quantifiers case - no special handling needed
        } else {
            for &var in &self.scheme.quantified {
                mapping.insert(var, next_var);
                next_var += 1;
            }

            write!(f, "∀")?;
            for i in 0..self.scheme.quantified.len() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "α{i}")?;
            }
            write!(f, ". ")?;
        }

        let display = TypeDisplay {
            pool: self.type_pool,
            id: self.scheme.ty,
        };
        display.fmt_with_mapping(f, self.scheme.ty, &mut mapping, &mut next_var)
    }
}
