use crate::{
    InternedString,
    expr::{Expr, MatchCase, Pattern, PatternBinding, RecordField, RecordPatternField},
    types::{ConstructorType, FieldId, RowField, Type, TypeScheme},
};
use std::collections::HashMap;
use std::ops::Index;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PatternId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DeBruijnIndex(pub usize);

impl DeBruijnIndex {
    #[must_use]
    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    #[must_use]
    pub const fn index(&self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct GlobalVarIdx(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct KindId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct SpanId(pub usize);

#[derive(Debug, Clone, Copy)]
pub struct TypeVarId(pub usize, pub Option<InternedString>);

impl TypeVarId {
    #[must_use]
    pub const fn new(id: usize) -> Self {
        Self(id, None)
    }

    #[must_use]
    pub const fn new_named(id: usize, name: InternedString) -> Self {
        Self(id, Some(name))
    }

    #[must_use]
    pub const fn id(&self) -> usize {
        self.0
    }

    #[must_use]
    pub const fn name(&self) -> Option<InternedString> {
        self.1
    }
}

// Equality and hashing based only on the numeric ID
impl PartialEq for TypeVarId {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for TypeVarId {}

impl std::hash::Hash for TypeVarId {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl PartialOrd for TypeVarId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TypeVarId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl GlobalVarIdx {
    #[must_use]
    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    #[must_use]
    pub const fn index(&self) -> usize {
        self.0
    }
}

impl KindId {
    #[must_use]
    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    #[must_use]
    pub const fn index(&self) -> usize {
        self.0
    }
}

impl SpanId {
    #[must_use]
    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    #[must_use]
    pub const fn index(&self) -> usize {
        self.0
    }

    #[must_use]
    pub const fn dummy() -> Self {
        Self(0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Star,
    Arrow(KindId, KindId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Localization {
    Real { start: usize, end: usize },
    Provenance(SpanId),
    Merged(SpanId, SpanId),
    Dummy,
}

impl Localization {
    #[must_use]
    pub const fn new(start: usize, end: usize) -> Self {
        Self::Real { start, end }
    }

    #[must_use]
    pub const fn dummy() -> Self {
        Self::Dummy
    }

    #[must_use]
    pub fn from_pest_span(span: pest::Span<'_>) -> Self {
        Self::Real {
            start: span.start(),
            end: span.end(),
        }
    }

    #[must_use]
    pub const fn provenance(parent: SpanId) -> Self {
        Self::Provenance(parent)
    }

    #[must_use]
    pub const fn merged(left: SpanId, right: SpanId) -> Self {
        Self::Merged(left, right)
    }

    /// Resolve to actual start/end positions by following provenance chain
    #[must_use]
    pub fn resolve(&self, pools: &Pools) -> (usize, usize) {
        match self {
            Self::Real { start, end } => (*start, *end),
            Self::Provenance(parent) => pools[*parent].resolve(pools),
            Self::Merged(left, right) => {
                let (left_start, left_end) = pools[*left].resolve(pools);
                let (right_start, right_end) = pools[*right].resolve(pools);
                (
                    if left_start < right_start {
                        left_start
                    } else {
                        right_start
                    },
                    if left_end > right_end {
                        left_end
                    } else {
                        right_end
                    },
                )
            }
            Self::Dummy => (0, 0),
        }
    }

    #[must_use]
    pub fn len(&self, pools: &Pools) -> usize {
        let (start, end) = self.resolve(pools);
        end - start
    }

    #[must_use]
    pub fn is_empty(&self, pools: &Pools) -> bool {
        let (start, end) = self.resolve(pools);
        start >= end
    }
}

#[derive(Debug, Clone)]
pub struct Pools {
    pub exprs: Vec<Expr>,
    pub patterns: Vec<MatchCase>,
    pub pattern_bindings: Vec<PatternBinding>,
    pub nested_patterns: Vec<Pattern>, // Pool for nested patterns in constructors
    pub types: Vec<Type>,
    pub type_params: Vec<TypeId>,
    pub row_fields: Vec<RowField>,       // Row field storage
    pub record_fields: Vec<RecordField>, // Record expression field storage
    pub record_pattern_fields: Vec<RecordPatternField>, // Record pattern field storage
    pub kinds: Vec<Kind>,
    pub localizations: Vec<Localization>,
    pub globals: HashMap<InternedString, TypeScheme>,
    pub constructors: HashMap<InternedString, ConstructorType>,
    pub function_implementations: HashMap<InternedString, ExprId>,
    pub global_order: Vec<InternedString>,
    pub type_constructor_kinds: HashMap<InternedString, KindId>,
    pub next_type_var: usize,
    // Cached common types
    pub cached_int_type: TypeId,
    pub cached_unit_type: TypeId,
    pub cached_empty_row_type: TypeId,
}

impl Default for Pools {
    fn default() -> Self {
        Self::new()
    }
}

impl Pools {
    #[must_use]
    pub fn new() -> Self {
        let mut pools = Self {
            exprs: Vec::new(),
            patterns: Vec::new(),
            pattern_bindings: Vec::new(),
            nested_patterns: Vec::new(),
            types: Vec::new(),
            type_params: Vec::new(),
            row_fields: Vec::new(),
            record_fields: Vec::new(),
            record_pattern_fields: Vec::new(),
            kinds: Vec::new(),
            localizations: Vec::new(),
            globals: HashMap::new(),
            constructors: HashMap::new(),
            function_implementations: HashMap::new(),
            global_order: Vec::new(),
            type_constructor_kinds: HashMap::new(),
            next_type_var: 0,
            cached_int_type: TypeId(0),
            cached_unit_type: TypeId(1),
            cached_empty_row_type: TypeId(2),
        };
        pools.localizations.push(Localization::Dummy);

        pools.cached_int_type = pools.alloc_type(Type::Int(SpanId::dummy()));
        pools.cached_unit_type = pools.alloc_type(Type::Unit(SpanId::dummy()));
        pools.cached_empty_row_type = pools.alloc_type(Type::EmptyRow(SpanId::dummy()));

        // Initialize builtin constructors
        pools.init_builtin_constructors();

        pools
    }

    // Expression methods
    pub fn alloc_expr(&mut self, expr: Expr) -> ExprId {
        let id = ExprId(self.exprs.len());
        self.exprs.push(expr);
        id
    }

    #[must_use] pub fn get_expr_span(&self, expr_id: ExprId) -> SpanId {
        self.exprs[expr_id.0].span()
    }

    #[must_use] pub fn find_exprs_by_span(&self, target_span: SpanId) -> Vec<ExprId> {
        self.exprs.iter()
            .enumerate()
            .filter(|(_, expr)| expr.span() == target_span)
            .map(|(idx, _)| ExprId(idx))
            .collect()
    }

    // Type methods
    pub fn alloc_type(&mut self, ty: Type) -> TypeId {
        let id = TypeId(self.types.len());
        self.types.push(ty);
        id
    }

    pub fn alloc_kind(&mut self, kind: Kind) -> KindId {
        let id = KindId(self.kinds.len());
        self.kinds.push(kind);
        id
    }

    // Localization methods
    pub fn alloc_localization(&mut self, localization: Localization) -> SpanId {
        let id = SpanId(self.localizations.len());
        self.localizations.push(localization);
        id
    }

    pub fn localization(&mut self, start: usize, end: usize) -> SpanId {
        self.alloc_localization(Localization::new(start, end))
    }

    #[must_use]
    pub const fn dummy_span(&self) -> SpanId {
        SpanId::dummy()
    }

    pub fn span_from_pest(&mut self, span: pest::Span<'_>) -> SpanId {
        self.alloc_localization(Localization::from_pest_span(span))
    }

    pub fn span_provenance(&mut self, parent: SpanId) -> SpanId {
        self.alloc_localization(Localization::provenance(parent))
    }

    pub fn span_merged(&mut self, left: SpanId, right: SpanId) -> SpanId {
        self.alloc_localization(Localization::merged(left, right))
    }

    pub fn span_dummy(&mut self) -> SpanId {
        self.alloc_localization(Localization::Dummy)
    }

    #[must_use]
    pub fn resolve_span(&self, span_id: SpanId) -> (usize, usize) {
        self[span_id].resolve(self)
    }

    // Expression builder methods
    pub fn int(&mut self, value: isize) -> ExprId {
        self.alloc_expr(Expr::Int(value, SpanId::dummy()))
    }

    pub fn int_span(&mut self, value: isize, span: SpanId) -> ExprId {
        self.alloc_expr(Expr::Int(value, span))
    }

    pub fn string_span(&mut self, value: InternedString, span: SpanId) -> ExprId {
        self.alloc_expr(Expr::String(value, span))
    }

    pub fn unit(&mut self) -> ExprId {
        self.alloc_expr(Expr::Unit(SpanId::dummy()))
    }

    pub fn unit_span(&mut self, span: SpanId) -> ExprId {
        self.alloc_expr(Expr::Unit(span))
    }

    pub fn data_type(&mut self, name: InternedString, params: &[TypeId]) -> TypeId {
        let start = TypeId(self.type_params.len());
        self.type_params.extend(params);
        self.alloc_type(Type::DataType(name, start, params.len(), SpanId::dummy()))
    }

    pub fn data_type_span(
        &mut self,
        name: InternedString,
        params: &[TypeId],
        span: SpanId,
    ) -> TypeId {
        let start = TypeId(self.type_params.len());
        self.type_params.extend(params);
        self.alloc_type(Type::DataType(name, start, params.len(), span))
    }

    pub fn data_type_simple(&mut self, name: InternedString) -> TypeId {
        self.data_type(name, &[])
    }

    pub fn type_app(&mut self, var_id: usize, params: &[TypeId]) -> TypeId {
        let start = TypeId(self.type_params.len());
        self.type_params.extend(params);
        self.alloc_type(Type::TypeApp(
            TypeVarId::new(var_id),
            start,
            params.len(),
            SpanId::dummy(),
        ))
    }

    pub fn type_app_span(&mut self, var_id: usize, params: &[TypeId], span: SpanId) -> TypeId {
        let start = TypeId(self.type_params.len());
        self.type_params.extend(params);
        self.alloc_type(Type::TypeApp(
            TypeVarId::new(var_id),
            start,
            params.len(),
            span,
        ))
    }

    #[must_use]
    pub fn get_data_type_params(&self, start: usize, len: usize) -> &[TypeId] {
        &self.type_params[start..start + len]
    }

    #[must_use]
    pub fn get_row_fields(&self, start: usize, len: usize) -> &[RowField] {
        &self.row_fields[start..start + len]
    }

    #[must_use]
    pub fn get_record_fields(&self, start: usize, len: usize) -> &[RecordField] {
        &self.record_fields[start..start + len]
    }

    #[must_use]
    pub fn get_record_pattern_fields(&self, start: usize, len: usize) -> &[RecordPatternField] {
        &self.record_pattern_fields[start..start + len]
    }

    #[must_use]
    pub fn get_nested_patterns(&self, start: usize, len: usize) -> &[Pattern] {
        &self.nested_patterns[start..start + len]
    }

    pub fn type_int(&mut self) -> TypeId {
        self.alloc_type(Type::Int(SpanId::dummy()))
    }

    pub fn type_int_span(&mut self, span: SpanId) -> TypeId {
        self.alloc_type(Type::Int(span))
    }

    pub fn type_string(&mut self) -> TypeId {
        self.alloc_type(Type::String(SpanId::dummy()))
    }

    pub fn type_string_span(&mut self, span: SpanId) -> TypeId {
        self.alloc_type(Type::String(span))
    }

    pub fn type_unit(&mut self) -> TypeId {
        self.alloc_type(Type::Unit(SpanId::dummy()))
    }

    pub fn type_unit_span(&mut self, span: SpanId) -> TypeId {
        if span == SpanId::dummy() {
            self.cached_unit_type
        } else {
            self.alloc_type(Type::Unit(span))
        }
    }

    pub fn type_var(&mut self, index: usize) -> TypeId {
        self.alloc_type(Type::Var(TypeVarId::new(index), SpanId::dummy()))
    }

    pub fn type_var_span(&mut self, index: usize, span: SpanId) -> TypeId {
        self.alloc_type(Type::Var(TypeVarId::new(index), span))
    }

    pub fn fresh_type_var(&mut self) -> TypeId {
        let var = self.next_type_var;
        self.next_type_var += 1;
        self.alloc_type(Type::Var(TypeVarId::new(var), SpanId::dummy()))
    }

    pub fn fresh_type_var_span(&mut self, span: SpanId) -> TypeId {
        let var = self.next_type_var;
        self.next_type_var += 1;
        self.type_var_span(var, span)
    }

    pub fn type_arrow(&mut self, from: TypeId, to: TypeId) -> TypeId {
        self.alloc_type(Type::Arrow(from, to, SpanId::dummy()))
    }

    pub fn type_arrow_span(&mut self, from: TypeId, to: TypeId, span: SpanId) -> TypeId {
        self.alloc_type(Type::Arrow(from, to, span))
    }

    pub const fn type_empty_row(&mut self) -> TypeId {
        self.cached_empty_row_type
    }

    pub fn type_empty_row_span(&mut self, span: SpanId) -> TypeId {
        if span == SpanId::dummy() {
            self.cached_empty_row_type
        } else {
            self.alloc_type(Type::EmptyRow(span))
        }
    }

    pub fn type_row(&mut self, fields: &[RowField], rest: TypeId) -> TypeId {
        let start = FieldId(self.row_fields.len());
        self.row_fields.extend(fields);
        self.alloc_type(Type::Row(start, fields.len(), rest, SpanId::dummy()))
    }

    pub fn type_row_span(&mut self, fields: &[RowField], rest: TypeId, span: SpanId) -> TypeId {
        let start = FieldId(self.row_fields.len());
        self.row_fields.extend(fields);
        self.alloc_type(Type::Row(start, fields.len(), rest, span))
    }

    pub fn kind_star(&mut self) -> KindId {
        self.alloc_kind(Kind::Star)
    }

    pub fn kind_arrow(&mut self, from: KindId, to: KindId) -> KindId {
        self.alloc_kind(Kind::Arrow(from, to))
    }

    pub fn expr_var(&mut self, debruijn_index: DeBruijnIndex, name: InternedString) -> ExprId {
        self.alloc_expr(Expr::Var(debruijn_index, name, SpanId::dummy()))
    }

    pub fn expr_var_span(
        &mut self,
        debruijn_index: DeBruijnIndex,
        name: InternedString,
        span: SpanId,
    ) -> ExprId {
        self.alloc_expr(Expr::Var(debruijn_index, name, span))
    }

    pub fn global_var(&mut self, global_idx: GlobalVarIdx, name: InternedString) -> ExprId {
        self.alloc_expr(Expr::GlobalVar(global_idx, name, SpanId::dummy()))
    }

    pub fn global_var_span(
        &mut self,
        global_idx: GlobalVarIdx,
        name: InternedString,
        span: SpanId,
    ) -> ExprId {
        self.alloc_expr(Expr::GlobalVar(global_idx, name, span))
    }

    pub fn call(&mut self, fun: ExprId, arg: ExprId) -> ExprId {
        self.alloc_expr(Expr::Call(fun, arg, SpanId::dummy()))
    }

    pub fn call_span(&mut self, fun: ExprId, arg: ExprId, span: SpanId) -> ExprId {
        self.alloc_expr(Expr::Call(fun, arg, span))
    }

    pub fn lambda(&mut self, body: ExprId, param_name: InternedString) -> ExprId {
        self.alloc_expr(Expr::Lambda(body, param_name, SpanId::dummy()))
    }

    pub fn lambda_span(
        &mut self,
        body: ExprId,
        param_name: InternedString,
        span: SpanId,
    ) -> ExprId {
        self.alloc_expr(Expr::Lambda(body, param_name, span))
    }

    pub fn let_expr(&mut self, value: ExprId, body: ExprId, var_name: InternedString) -> ExprId {
        self.alloc_expr(Expr::Let(value, body, var_name, SpanId::dummy()))
    }

    pub fn let_expr_span(
        &mut self,
        value: ExprId,
        body: ExprId,
        var_name: InternedString,
        span: SpanId,
    ) -> ExprId {
        self.alloc_expr(Expr::Let(value, body, var_name, span))
    }

    pub fn construct(&mut self, constructor: InternedString, arg: ExprId) -> ExprId {
        self.alloc_expr(Expr::Construct(constructor, arg, SpanId::dummy()))
    }

    pub fn construct_span(
        &mut self,
        constructor: InternedString,
        arg: ExprId,
        span: SpanId,
    ) -> ExprId {
        self.alloc_expr(Expr::Construct(constructor, arg, span))
    }

    pub fn construct_nullary(&mut self, constructor: InternedString) -> ExprId {
        let unit_arg = self.unit();
        self.construct(constructor, unit_arg)
    }

    pub fn match_expr(&mut self, expr: ExprId, start_id: PatternId, length: usize) -> ExprId {
        self.alloc_expr(Expr::Match(
            expr,
            crate::expr::MatchArms { start_id, length },
            SpanId::dummy(),
        ))
    }

    pub fn match_expr_span(
        &mut self,
        expr: ExprId,
        start_id: PatternId,
        length: usize,
        span: SpanId,
    ) -> ExprId {
        self.alloc_expr(Expr::Match(
            expr,
            crate::expr::MatchArms { start_id, length },
            span,
        ))
    }

    pub fn record_expr(&mut self, fields: &[RecordField]) -> ExprId {
        let start = FieldId(self.record_fields.len());
        self.record_fields.extend(fields);
        self.alloc_expr(Expr::Record(start, fields.len(), SpanId::dummy()))
    }

    pub fn record_expr_span(&mut self, fields: &[RecordField], span: SpanId) -> ExprId {
        let start = FieldId(self.record_fields.len());
        self.record_fields.extend(fields);
        self.alloc_expr(Expr::Record(start, fields.len(), span))
    }

    pub fn project_expr(&mut self, record: ExprId, field: InternedString) -> ExprId {
        self.alloc_expr(Expr::Project(record, field, SpanId::dummy()))
    }

    pub fn project_expr_span(
        &mut self,
        record: ExprId,
        field: InternedString,
        span: SpanId,
    ) -> ExprId {
        self.alloc_expr(Expr::Project(record, field, span))
    }

    pub fn extend_expr(&mut self, record: ExprId, fields: &[RecordField]) -> ExprId {
        let start = FieldId(self.record_fields.len());
        self.record_fields.extend(fields);
        self.alloc_expr(Expr::Extend(record, start, fields.len(), SpanId::dummy()))
    }

    pub fn extend_expr_span(
        &mut self,
        record: ExprId,
        fields: &[RecordField],
        span: SpanId,
    ) -> ExprId {
        let start = FieldId(self.record_fields.len());
        self.record_fields.extend(fields);
        self.alloc_expr(Expr::Extend(record, start, fields.len(), span))
    }

    pub fn alloc_pattern(&mut self, pattern: Pattern, body: ExprId) -> PatternId {
        let id = PatternId(self.patterns.len());
        self.patterns.push(MatchCase { pattern, body });
        id
    }

    pub fn alloc_pattern_binding(&mut self, binding: PatternBinding) -> PatternId {
        let id = PatternId(self.pattern_bindings.len());
        self.pattern_bindings.push(binding);
        id
    }

    pub fn alloc_nested_pattern(&mut self, pattern: Pattern) -> PatternId {
        let id = PatternId(self.nested_patterns.len());
        self.nested_patterns.push(pattern);
        id
    }

    pub fn alloc_nested_patterns(&mut self, patterns: &[Pattern]) -> (PatternId, usize) {
        let start_id = PatternId(self.nested_patterns.len());
        self.nested_patterns.extend(patterns.iter().copied());
        (start_id, patterns.len())
    }

    #[must_use]
    pub fn get_pattern_bindings(&self, start_id: PatternId, length: usize) -> &[PatternBinding] {
        &self.pattern_bindings[start_id.0..start_id.0 + length]
    }

    pub fn bind_global_scheme(&mut self, name: InternedString, scheme: TypeScheme) {
        if !self.globals.contains_key(&name) {
            self.global_order.push(name);
        }
        self.globals.insert(name, scheme);
    }

    #[must_use]
    pub fn get_global_scheme(&self, name: &InternedString) -> Option<&TypeScheme> {
        self.globals.get(name)
    }

    pub fn add_constructor(&mut self, name: InternedString, constructor_type: ConstructorType) {
        self.constructors.insert(name, constructor_type);
    }

    #[must_use]
    pub fn is_constructor(&self, name: &InternedString) -> bool {
        self.constructors.contains_key(name)
    }

    #[must_use]
    pub fn get_constructor(&self, name: &InternedString) -> Option<&ConstructorType> {
        self.constructors.get(name)
    }

    pub fn add_function_implementation(&mut self, name: InternedString, expr_id: ExprId) {
        self.function_implementations.insert(name, expr_id);
    }

    #[must_use]
    pub fn get_function_implementation(&self, name: &InternedString) -> Option<ExprId> {
        self.function_implementations.get(name).copied()
    }

    pub fn get_global_index(&self, name: &InternedString) -> Option<GlobalVarIdx> {
        self.global_order
            .iter()
            .position(|n| n == name)
            .map(GlobalVarIdx::new)
    }

    #[must_use]
    pub fn get_global_name(&self, idx: GlobalVarIdx) -> Option<InternedString> {
        self.global_order.get(idx.index()).copied()
    }

    pub fn bind_type_constructor_kind(&mut self, name: InternedString, kind: KindId) {
        self.type_constructor_kinds.insert(name, kind);
    }

    #[must_use]
    pub fn get_type_constructor_kind(&self, name: &InternedString) -> Option<KindId> {
        self.type_constructor_kinds.get(name).copied()
    }

    pub fn compute_data_type_kind(&mut self, type_params: &[InternedString]) -> KindId {
        let star = self.kind_star();
        type_params
            .iter()
            .rev()
            .fold(star, |acc, _| self.kind_arrow(star, acc))
    }

    pub fn init_builtin_constructors(&mut self) {
        use crate::{intern_str, types::ConstructorType};

        // Create BuiltinList type constructor: BuiltinList : * -> *
        let list_name = intern_str("BuiltinList");
        let star_kind = self.kind_star();
        let list_kind = self.kind_arrow(star_kind, star_kind);
        self.bind_type_constructor_kind(list_name, list_kind);

        // We need to create constructor types that will be properly instantiated during type inference
        // The type variables here should be templates that get fresh instances during inference

        // Create a fresh type variable for 'a'
        let a_var_id = TypeVarId::new_named(self.next_type_var, intern_str("a"));
        self.next_type_var += 1;
        let a_type = self.alloc_type(Type::Var(a_var_id, SpanId::dummy()));

        // Create BuiltinList a type
        let list_a_type = self.data_type(list_name, &[a_type]);

        // Nil : ∀a. BuiltinList a
        let nil_name = intern_str("Nil");
        let nil_constructor_type = ConstructorType {
            outer_quantified_vars: vec![a_var_id],
            universal_vars: vec![],
            existential_vars: vec![],
            component_type: self.cached_unit_type, // Nil takes no arguments
            result_type: list_a_type,
        };
        self.add_constructor(nil_name, nil_constructor_type);

        // Cons : ∀a. a -> BuiltinList a -> BuiltinList a
        let cons_name = intern_str("Cons");
        // For Cons a (BuiltinList a), the component_type should be 'a' and result_type should be 'BuiltinList a -> BuiltinList a'
        let cons_component_type = a_type; // First argument: a
        let cons_result_type =
            self.alloc_type(Type::Arrow(list_a_type, list_a_type, SpanId::dummy())); // BuiltinList a -> BuiltinList a
        let cons_constructor_type = ConstructorType {
            outer_quantified_vars: vec![a_var_id],
            universal_vars: vec![],
            existential_vars: vec![],
            component_type: cons_component_type,
            result_type: cons_result_type,
        };
        self.add_constructor(cons_name, cons_constructor_type);
    }

    pub fn backpatch_global_variables(&mut self) -> Vec<InternedString> {
        let mut undefined_vars = Vec::new();
        let expr_count = self.exprs.len();
        for i in 0..expr_count {
            self.backpatch_expr(ExprId(i), &mut undefined_vars);
        }
        undefined_vars
    }

    fn backpatch_expr(&mut self, expr_id: ExprId, undefined_vars: &mut Vec<InternedString>) {
        let expr = self.exprs[expr_id.0];
        match expr {
            Expr::Var(debruijn_index, name, span) => {
                if debruijn_index.index() == usize::MAX {
                    if let Some(global_idx) = self.get_global_index(&name) {
                        self.exprs[expr_id.0] = Expr::GlobalVar(global_idx, name, span);
                    } else {
                        println!(
                            "DEBUG: Undefined variable found: {} (InternedString({:?}))",
                            name.as_str(),
                            name
                        );
                        undefined_vars.push(name);
                    }
                }
            }
            Expr::Lambda(body_id, _, _) => {
                self.backpatch_expr(body_id, undefined_vars);
            }
            Expr::Call(func_id, arg_id, _) => {
                self.backpatch_expr(func_id, undefined_vars);
                self.backpatch_expr(arg_id, undefined_vars);
            }
            Expr::Let(value_id, body_id, _, _) => {
                self.backpatch_expr(value_id, undefined_vars);
                self.backpatch_expr(body_id, undefined_vars);
            }
            Expr::Construct(_, arg_id, _) => {
                self.backpatch_expr(arg_id, undefined_vars);
            }
            Expr::Match(expr_id, match_arms, _) => {
                self.backpatch_expr(expr_id, undefined_vars);
                for i in 0..match_arms.length {
                    let case = self.patterns[match_arms.start_id.0 + i];
                    self.backpatch_expr(case.body, undefined_vars);
                }
            }
            Expr::Record(start, len, _) => {
                let fields = self.get_record_fields(start.0, len).to_vec();
                for field in fields {
                    self.backpatch_expr(field.expr, undefined_vars);
                }
            }
            Expr::Project(record_id, _, _) => {
                self.backpatch_expr(record_id, undefined_vars);
            }
            Expr::Extend(record_id, start, len, _) => {
                self.backpatch_expr(record_id, undefined_vars);
                let fields = self.get_record_fields(start.0, len).to_vec();
                for field in fields {
                    self.backpatch_expr(field.expr, undefined_vars);
                }
            }
            Expr::Ffi(_, _, arg_expr, _) => {
                if let Some(arg_id) = arg_expr {
                    self.backpatch_expr(arg_id, undefined_vars);
                }
            }
            Expr::Int(_, _) | Expr::String(_, _) | Expr::Unit(_) | Expr::GlobalVar(_, _, _) => {}
        }
    }

    #[must_use]
    pub fn type_free_vars(&self, ty: TypeId) -> Vec<TypeVarId> {
        use std::collections::HashSet;
        let mut vars = HashSet::new();
        self.type_collect_free_vars(ty, &mut vars);
        vars.into_iter().collect()
    }

    fn type_collect_free_vars(&self, ty: TypeId, vars: &mut std::collections::HashSet<TypeVarId>) {
        match self[ty] {
            Type::Int(_) | Type::String(_) | Type::Unit(_) | Type::EmptyRow(_) => {}
            Type::Var(var, _) => {
                vars.insert(var);
            }
            Type::Arrow(from, to, _) => {
                self.type_collect_free_vars(from, vars);
                self.type_collect_free_vars(to, vars);
            }
            Type::DataType(_, start, len, _) => {
                let params = self.get_data_type_params(start.0, len);
                for &param_id in params {
                    self.type_collect_free_vars(param_id, vars);
                }
            }
            Type::TypeApp(_var, start, len, _) => {
                // Don't include TypeApp head variables in free vars for generalization
                // The head variable represents a type constructor that should be generalized
                let params = self.get_data_type_params(start.0, len);
                for &param_id in params {
                    self.type_collect_free_vars(param_id, vars);
                }
            }
            Type::Row(start, len, rest, _) => {
                let fields = self.get_row_fields(start.0, len);
                for field in fields {
                    self.type_collect_free_vars(field.field_type, vars);
                }
                self.type_collect_free_vars(rest, vars);
            }
        }
    }
}

impl Index<ExprId> for Pools {
    type Output = Expr;

    fn index(&self, id: ExprId) -> &Self::Output {
        &self.exprs[id.0]
    }
}

impl Index<TypeId> for Pools {
    type Output = Type;

    fn index(&self, id: TypeId) -> &Self::Output {
        &self.types[id.0]
    }
}

impl Index<PatternId> for Pools {
    type Output = MatchCase;

    fn index(&self, id: PatternId) -> &Self::Output {
        &self.patterns[id.0]
    }
}

impl Index<KindId> for Pools {
    type Output = Kind;

    fn index(&self, id: KindId) -> &Self::Output {
        &self.kinds[id.0]
    }
}

impl Index<SpanId> for Pools {
    type Output = Localization;

    fn index(&self, id: SpanId) -> &Self::Output {
        &self.localizations[id.0]
    }
}
