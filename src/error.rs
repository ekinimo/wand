use crate::{
    InternedString,
    pools::{ExprId, Pools, SpanId, TypeId, TypeVarId},
    type_inference::PooledTypingContext,
    types::TypeScheme,
};

fn format_type_var_name(var: &TypeVarId) -> String {
    var.name().map_or_else(|| format!("α{}", var.id()), super::InternedString::as_str)
}

/// Rich error information with detailed context
#[derive(Debug, Clone)]
pub struct TypeMismatchInfo {
    pub expected_type: TypeId,
    pub found_type: TypeId,
    pub expected_expr: Option<ExprId>, // Expression that produced expected type
    pub found_expr: Option<ExprId>,    // Expression that produced found type
    pub expected_span: SpanId,
    pub found_span: SpanId,
    pub context: Option<MismatchContext>,
}

#[derive(Debug, Clone)]
pub enum MismatchContext {
    FunctionApplication {
        function_expr: ExprId,
        function_span: SpanId,
        arg_index: usize,
        arg_expr: ExprId,
        arg_span: SpanId,
    },
    FunctionReturn {
        function_name: Option<InternedString>,
        expected_return: TypeId,
        actual_return: TypeId,
    },
    VariableBinding {
        var_name: InternedString,
        var_span: SpanId,
    },
    PatternMatch {
        pattern_span: SpanId,
        scrutinee_expr: ExprId,
    },
    RecordField {
        record_expr: ExprId,
        field_name: InternedString,
        field_span: SpanId,
    },
}

#[derive(Debug, Clone)]
pub struct OccursCheckInfo {
    pub var: TypeVarId,
    pub in_type: TypeId,
    pub var_span: SpanId,
    pub type_span: SpanId,
    pub context_expr: Option<ExprId>,
}

#[derive(Debug, Clone)]
pub struct UnboundVariableInfo {
    pub name: InternedString,
    pub span: SpanId,
    pub suggestions: Vec<InternedString>, // Similar variable names
}

#[derive(Debug, Clone)]
pub struct NonExhaustiveInfo {
    pub missing_patterns: Vec<String>,
    pub match_span: SpanId,
    pub scrutinee_type: TypeId,
}

/// Enhanced type error with rich context
#[derive(Debug, Clone)]
pub enum RichTypeError {
    TypeMismatch(TypeMismatchInfo),
    OccursCheck(OccursCheckInfo),
    UnboundVariable(UnboundVariableInfo),
    NonExhaustivePatterns(NonExhaustiveInfo),
    InfiniteType {
        var: TypeVarId,
        type_id: TypeId,
        span: SpanId,
    },
    CannotInfer {
        expr: ExprId,
        span: SpanId,
        reason: String,
    },
    ProtectedVariableFailure {
        protected_var: TypeVarId,
        conflicting_type: TypeId,
        var_span: SpanId,
        type_span: SpanId,
    },
    ArityMismatch {
        expected_type: TypeId,
        found_type: TypeId,
        expected_arity: usize,
        found_arity: usize,
        expected_span: SpanId,
        found_span: SpanId,
    },
    UniversalVariableEscape {
        var: TypeVarId,
        span: SpanId,
        context: String,
    },
    UnknownConstructor {
        name: InternedString,
        span: SpanId,
        suggestions: Vec<InternedString>,
    },
    FunctionSignatureMismatch {
        function_name: InternedString,
        original_scheme: TypeScheme,
        instantiated_type: TypeId,
        inferred_type: TypeId,
        inferred_expr: ExprId,
        declared_span: SpanId,
        inferred_span: SpanId,
    },
    RowMismatch {
        expected_type: TypeId,
        found_type: TypeId,
        expected_span: SpanId,
        found_span: SpanId,
        context: String,
    },
}

impl RichTypeError {
    /// Create a type mismatch error
    #[must_use] pub const fn type_mismatch(
        expected_type: TypeId,
        found_type: TypeId,
        expected_span: SpanId,
        found_span: SpanId,
        expected_expr: Option<ExprId>,
        found_expr: Option<ExprId>,
        context: Option<MismatchContext>,
    ) -> Self {
        Self::TypeMismatch(TypeMismatchInfo {
            expected_type,
            found_type,
            expected_expr,
            found_expr,
            expected_span,
            found_span,
            context,
        })
    }

    /// Create an occurs check error
    #[must_use] pub const fn occurs_check(
        var: TypeVarId,
        in_type: TypeId,
        var_span: SpanId,
        type_span: SpanId,
    ) -> Self {
        Self::OccursCheck(OccursCheckInfo {
            var,
            in_type,
            var_span,
            type_span,
            context_expr: None, // Will be recovered during display from spans
        })
    }

    /// Create an unbound variable error
    #[must_use] pub const fn unbound_variable(name: InternedString, span: SpanId) -> Self {
        Self::UnboundVariable(UnboundVariableInfo {
            name,
            span,
            suggestions: Vec::new(),
        })
    }

    /// Create a generic type mismatch with message
    #[must_use] pub const fn type_error(message: String, span: SpanId) -> Self {
        Self::CannotInfer {
            expr: ExprId(0), // dummy
            span,
            reason: message,
        }
    }

    /// Create a non-exhaustive patterns error
    #[must_use] pub const fn non_exhaustive_patterns(
        missing_patterns: Vec<String>,
        match_span: SpanId,
        scrutinee_type: TypeId,
    ) -> Self {
        Self::NonExhaustivePatterns(NonExhaustiveInfo {
            missing_patterns,
            match_span,
            scrutinee_type,
        })
    }

    /// Create a protected variable failure error
    #[must_use] pub const fn protected_variable_failure(
        protected_var: TypeVarId,
        conflicting_type: TypeId,
        var_span: SpanId,
        type_span: SpanId,
    ) -> Self {
        Self::ProtectedVariableFailure {
            protected_var,
            conflicting_type,
            var_span,
            type_span,
        }
    }

    /// Create an arity mismatch error
    #[must_use] pub const fn arity_mismatch(
        expected_type: TypeId,
        found_type: TypeId,
        expected_arity: usize,
        found_arity: usize,
        expected_span: SpanId,
        found_span: SpanId,
    ) -> Self {
        Self::ArityMismatch {
            expected_type,
            found_type,
            expected_arity,
            found_arity,
            expected_span,
            found_span,
        }
    }

    /// Create a universal variable escape error
    #[must_use] pub const fn universal_variable_escape(var: TypeVarId, span: SpanId, context: String) -> Self {
        Self::UniversalVariableEscape { var, span, context }
    }

    /// Create an unknown constructor error
    #[must_use] pub const fn unknown_constructor(name: InternedString, span: SpanId) -> Self {
        Self::UnknownConstructor {
            name,
            span,
            suggestions: Vec::new(), // Could be populated with similar constructor names later
        }
    }

    /// Create a function signature mismatch error
    #[must_use] pub const fn function_signature_mismatch(
        function_name: InternedString,
        original_scheme: TypeScheme,
        instantiated_type: TypeId,
        inferred_type: TypeId,
        inferred_expr: ExprId,
        declared_span: SpanId,
        inferred_span: SpanId,
    ) -> Self {
        Self::FunctionSignatureMismatch {
            function_name,
            original_scheme,
            instantiated_type,
            inferred_type,
            inferred_expr,
            declared_span,
            inferred_span,
        }
    }

    /// Create a row type mismatch error
    #[must_use] pub const fn row_mismatch(
        expected_type: TypeId,
        found_type: TypeId,
        expected_span: SpanId,
        found_span: SpanId,
        context: String,
    ) -> Self {
        Self::RowMismatch {
            expected_type,
            found_type,
            expected_span,
            found_span,
            context,
        }
    }

    /// Display error with source location information  
    #[must_use]
    pub fn display_with_location(&self, pools: &Pools) -> String {
        let (start, end) = pools.resolve_span(self.primary_span());
        let location = if start == 0 && end == 0 {
            "unknown location".to_string()
        } else {
            format!("{start}:{end}")
        };

        match self {
            Self::TypeMismatch(info) => {
                format!(
                    "Type mismatch at {}: expected {}, found {}",
                    location,
                    pools.display_type(info.expected_type),
                    pools.display_type(info.found_type)
                )
            }
            Self::OccursCheck(info) => {
                format!(
                    "Occurs check failed at {}: variable α{} occurs in {}",
                    location,
                    info.var.id(),
                    pools.display_type(info.in_type)
                )
            }
            Self::UnboundVariable(info) => {
                format!("Unbound variable '{}' at {}", info.name.as_str(), location)
            }
            Self::CannotInfer { reason, .. } => {
                format!("{reason} at {location}")
            }
            Self::ProtectedVariableFailure {
                protected_var,
                conflicting_type,
                ..
            } => {
                let var_name = format_type_var_name(protected_var);
                format!(
                    "Protected variable '{}' cannot be unified with '{}' at {}",
                    var_name,
                    pools.display_type(*conflicting_type),
                    location
                )
            }
            Self::ArityMismatch {
                expected_type,
                found_type,
                expected_arity,
                found_arity,
                ..
            } => {
                format!(
                    "Arity mismatch: expected {} with {} parameters, found {} with {} parameters at {}",
                    pools.display_type(*expected_type),
                    expected_arity,
                    pools.display_type(*found_type),
                    found_arity,
                    location
                )
            }
            Self::UniversalVariableEscape { var, context, .. } => {
                let var_name = format_type_var_name(var);
                format!(
                    "Universal variable '{var_name}' escapes scope in {context} at {location}"
                )
            }
            Self::UnknownConstructor { name, .. } => {
                format!("Unknown constructor '{}' at {}", name.as_str(), location)
            }
            Self::FunctionSignatureMismatch {
                function_name,
                
                instantiated_type,
                inferred_type,
                ..
            } => {
                format!(
                    "Function '{}' signature mismatch at {}: expected instantiated type '{}', but function body inferred type '{}'",
                    function_name.as_str(),
                    location,
                    pools.display_type(*instantiated_type),
                    pools.display_type(*inferred_type)
                )
            }
            Self::RowMismatch {
                expected_type,
                found_type,
                context,
                ..
            } => {
                format!(
                    "Row type mismatch at {}: expected '{}', found '{}' ({})",
                    location,
                    pools.display_type(*expected_type),
                    pools.display_type(*found_type),
                    context
                )
            }
            Self::NonExhaustivePatterns(info) => {
                format!(
                    "NonExhaustivePatterns: Missing patterns {} at {}",
                    info.missing_patterns.join(", "),
                    location
                )
            }

            Self::InfiniteType { .. } =>
            /*TODO we should implement this*/
            {
                "todo".to_string()
            }
        }
    }
    /// Get the primary span for this error
    #[must_use] pub const fn primary_span(&self) -> SpanId {
        match self {
            Self::TypeMismatch(info) => info.found_span,
            Self::OccursCheck(info) => info.var_span,
            Self::UnboundVariable(info) => info.span,
            Self::NonExhaustivePatterns(info) => info.match_span,
            Self::InfiniteType { span, .. } | Self::CannotInfer { span, .. } | Self::UniversalVariableEscape { span, .. } | Self::UnknownConstructor { span, .. } => *span,
            Self::ProtectedVariableFailure { var_span, .. } => *var_span,
            Self::ArityMismatch { found_span, .. } | Self::RowMismatch { found_span, .. } => *found_span,
            Self::FunctionSignatureMismatch { inferred_span, .. } => *inferred_span,
        }
    }

    /// Display in emacs-compatible format with rich context
    #[must_use] pub fn display_emacs_format(
        &self,
        pools: &Pools,
        _typing_ctx: &PooledTypingContext,
        source_code: &str,
        filename: &str,
    ) -> String {
        let mut result = String::new();

        match self {
            Self::TypeMismatch(info) => {
                // Primary error location (emacs clickable)
                let primary_pos =
                    format_emacs_position(info.found_span, pools, source_code, filename);
                result.push_str(&format!(
                    "{}: Type mismatch: expected '{}' but found '{}'\n",
                    primary_pos,
                    pools.display_type(info.expected_type),
                    pools.display_type(info.found_type)
                ));

                // Expected type location (emacs clickable)
                if info.expected_span != info.found_span {
                    let expected_pos =
                        format_emacs_position(info.expected_span, pools, source_code, filename);
                    result.push_str(&format!(
                        "{}: Expected type '{}' comes from here\n",
                        expected_pos,
                        pools.display_type(info.expected_type)
                    ));
                }

                // Context-specific information
                if let Some(ctx) = &info.context {
                    match ctx {
                        MismatchContext::FunctionApplication {
                            function_expr,
                            arg_index,
                            arg_expr,
                            ..
                        } => {
                            result.push_str(&format!(
                                "  In function application: {} argument #{}\n",
                                pools.display_expr(*function_expr),
                                arg_index + 1
                            ));
                            result.push_str(&format!(
                                "  Argument expression: {}\n",
                                pools.display_expr(*arg_expr)
                            ));
                        }
                        MismatchContext::FunctionReturn { function_name, .. } => {
                            if let Some(name) = function_name {
                                result.push_str(&format!(
                                    "  In return type of function '{}'\n",
                                    name.as_str()
                                ));
                            }
                        }
                        MismatchContext::VariableBinding { var_name, .. } => {
                            result.push_str(&format!(
                                "  In binding of variable '{}'\n",
                                var_name.as_str()
                            ));
                        }
                        MismatchContext::PatternMatch { scrutinee_expr, .. } => {
                            result.push_str(&format!(
                                "  In pattern match on: {}\n",
                                pools.display_expr(*scrutinee_expr)
                            ));
                        }
                        MismatchContext::RecordField {
                            record_expr,
                            field_name,
                            ..
                        } => {
                            result.push_str(&format!(
                                "  In field '{}' of record: {}\n",
                                field_name.as_str(),
                                pools.display_expr(*record_expr)
                            ));
                        }
                    }
                }
            }

            Self::UnboundVariable(info) => {
                let pos = format_emacs_position(info.span, pools, source_code, filename);
                result.push_str(&format!(
                    "{}: Unbound variable '{}'\n",
                    pos,
                    info.name.as_str()
                ));

                if !info.suggestions.is_empty() {
                    result.push_str("  Did you mean one of: ");
                    let suggestions: Vec<String> = info
                        .suggestions
                        .iter()
                        .map(|s| format!("'{}'", s.as_str()))
                        .collect();
                    result.push_str(&suggestions.join(", "));
                    result.push('\n');
                }
            }

            Self::OccursCheck(info) => {
                let pos = format_emacs_position(info.var_span, pools, source_code, filename);
                let var_name = format_type_var_name(&info.var);
                result.push_str(&format!(
                    "{}: Infinite type: variable '{}' occurs in '{}'\n",
                    pos,
                    var_name,
                    pools.display_type(info.in_type)
                ));
            }

            Self::NonExhaustivePatterns(info) => {
                let pos = format_emacs_position(info.match_span, pools, source_code, filename);
                result.push_str(&format!("{pos}: Non-exhaustive pattern match\n"));
                result.push_str(&format!(
                    "  Missing patterns: {}\n",
                    info.missing_patterns.join(", ")
                ));
                result.push_str(&format!(
                    "  Scrutinee type: {}\n",
                    pools.display_type(info.scrutinee_type)
                ));
            }

            Self::InfiniteType { var, type_id, span } => {
                let pos = format_emacs_position(*span, pools, source_code, filename);
                let var_name = format_type_var_name(var);
                result.push_str(&format!(
                    "{}: Infinite type: '{}' = '{}'\n",
                    pos,
                    var_name,
                    pools.display_type(*type_id)
                ));
            }

            Self::CannotInfer { expr, span, reason } => {
                let pos = format_emacs_position(*span, pools, source_code, filename);
                result.push_str(&format!(
                    "{}: Cannot infer type for: {}\n",
                    pos,
                    pools.display_expr(*expr)
                ));
                result.push_str(&format!("  Reason: {reason}\n"));
            }

            Self::ProtectedVariableFailure {
                protected_var,
                conflicting_type,
                var_span,
                type_span,
            } => {
                let pos = format_emacs_position(*var_span, pools, source_code, filename);
                let var_name = format_type_var_name(protected_var);
                result.push_str(&format!(
                    "{}: Protected variable '{}' cannot be unified with '{}'\n",
                    pos,
                    var_name,
                    pools.display_type(*conflicting_type)
                ));

                if *var_span != *type_span {
                    let type_pos = format_emacs_position(*type_span, pools, source_code, filename);
                    result.push_str(&format!(
                        "{}: Conflicting type '{}' comes from here\n",
                        type_pos,
                        pools.display_type(*conflicting_type)
                    ));
                }
            }

            Self::ArityMismatch {
                expected_type,
                found_type,
                expected_arity,
                found_arity,
                expected_span,
                found_span,
            } => {
                let pos = format_emacs_position(*found_span, pools, source_code, filename);
                result.push_str(&format!("{}: Arity mismatch: expected {} with {} parameters, found {} with {} parameters\n",
                    pos, pools.display_type(*expected_type), expected_arity, 
                    pools.display_type(*found_type), found_arity
                ));

                if *expected_span != *found_span {
                    let expected_pos =
                        format_emacs_position(*expected_span, pools, source_code, filename);
                    result.push_str(&format!(
                        "{}: Expected type '{}' comes from here\n",
                        expected_pos,
                        pools.display_type(*expected_type)
                    ));
                }
            }

            Self::UniversalVariableEscape { var, span, context } => {
                let pos = format_emacs_position(*span, pools, source_code, filename);
                let var_name = format_type_var_name(var);
                result.push_str(&format!(
                    "{pos}: Universal variable '{var_name}' escapes its scope\n"
                ));
                result.push_str(&format!("  Context: {context}\n"));
                result.push_str("  This violates the constraint α ∉ TV(A)\n");
            }

            Self::UnknownConstructor {
                name,
                span,
                suggestions,
            } => {
                let pos = format_emacs_position(*span, pools, source_code, filename);
                result.push_str(&format!(
                    "{}: Unknown constructor '{}'\n",
                    pos,
                    name.as_str()
                ));

                if !suggestions.is_empty() {
                    result.push_str("  Did you mean one of: ");
                    let suggestion_strs: Vec<String> = suggestions
                        .iter()
                        .map(|s| format!("'{}'", s.as_str()))
                        .collect();
                    result.push_str(&suggestion_strs.join(", "));
                    result.push('\n');
                }
            }

            Self::FunctionSignatureMismatch {
                function_name,
                original_scheme,
                instantiated_type,
                inferred_type,
                inferred_expr,
                declared_span,
                inferred_span,
            } => {
                // Primary error location (emacs clickable)
                let primary_pos =
                    format_emacs_position(*inferred_span, pools, source_code, filename);
                result.push_str(&format!(
                    "{}: Function '{}' body type mismatch: expected '{}' but inferred '{}'\n",
                    primary_pos,
                    function_name.as_str(),
                    pools.display_type(*instantiated_type),
                    pools.display_type(*inferred_type)
                ));

                // Declaration location (emacs clickable)
                if *declared_span != *inferred_span {
                    let declared_pos =
                        format_emacs_position(*declared_span, pools, source_code, filename);
                    result.push_str(&format!(
                        "{}: Function '{}' declared here with scheme '{}'\n",
                        declared_pos,
                        function_name.as_str(),
                        original_scheme.display(pools)
                    ));
                }

                // Show the inferred expression
                result.push_str(&format!(
                    "  Function body expression: {}\n",
                    pools.display_expr(*inferred_expr)
                ));

                // Show scheme instantiation
                result.push_str(&format!(
                    "  Original scheme: {}\n",
                    original_scheme.display(pools)
                ));
                result.push_str(&format!(
                    "  Instantiated as: {}\n",
                    pools.display_type(*instantiated_type)
                ));
                result.push_str(&format!(
                    "  But body inferred: {}\n",
                    pools.display_type(*inferred_type)
                ));
            }

            Self::RowMismatch {
                expected_type,
                found_type,
                expected_span,
                found_span,
                context,
            } => {
                // Primary error location (emacs clickable)
                let primary_pos = format_emacs_position(*found_span, pools, source_code, filename);
                result.push_str(&format!(
                    "{}: Row type mismatch: expected '{}' but found '{}'\n",
                    primary_pos,
                    pools.display_type(*expected_type),
                    pools.display_type(*found_type)
                ));

                // Expected type location (emacs clickable)
                if *expected_span != *found_span {
                    let expected_pos =
                        format_emacs_position(*expected_span, pools, source_code, filename);
                    result.push_str(&format!(
                        "{}: Expected row type '{}' comes from here\n",
                        expected_pos,
                        pools.display_type(*expected_type)
                    ));
                }

                result.push_str(&format!("  Context: {context}\n"));
            }
        }

        result
    }

    /// Display with miette-style context and full typing information
    #[must_use] pub fn display_comprehensive(
        &self,
        pools: &Pools,
        typing_ctx: &PooledTypingContext,
        source_code: &str,
        filename: &str,
    ) -> String {
        let mut result = self.display_emacs_format(pools, typing_ctx, source_code, filename);

        // Add miette-style source context
        result.push('\n');
        result.push_str(&format_miette_context(
            self.primary_span(),
            pools,
            source_code,
        ));

        // Add typing context
        result.push('\n');
        result.push_str(&format_typing_context(
            typing_ctx,
            pools,
            source_code,
            filename,
        ));

        result
    }
}

/// Format position for emacs compatibility: filename:line:col
fn format_emacs_position(span: SpanId, pools: &Pools, source: &str, filename: &str) -> String {
    let (start, _) = pools.resolve_span(span);
    if start >= source.len() {
        return format!("{filename}:1:1");
    }

    let line_num = source[..start].chars().filter(|&c| c == '\n').count() + 1;
    let col_num = source[..start]
        .rfind('\n')
        .map_or(start + 1, |last_newline| start - last_newline);

    format!("{filename}:{line_num}:{col_num}")
}

/// Format miette-style context with line numbers and highlighting
fn format_miette_context(span: SpanId, pools: &Pools, source_code: &str) -> String {
    let (start, end) = pools.resolve_span(span);
    if start >= source_code.len() {
        return String::new();
    }

    let line_num = source_code[..start].chars().filter(|&c| c == '\n').count() + 1;
    let lines: Vec<&str> = source_code.lines().collect();

    if line_num == 0 || line_num > lines.len() {
        return String::new();
    }

    let mut result = String::new();
    let error_line_idx = line_num - 1;

    // Show context: 2 lines before and after
    let context_start = error_line_idx.saturating_sub(2);
    let context_end = std::cmp::min(lines.len(), error_line_idx + 3);

    for (idx, line) in lines[context_start..context_end].iter().enumerate() {
        let actual_line_num = context_start + idx + 1;
        let is_error_line = actual_line_num == line_num;

        if is_error_line {
            result.push_str(&format!("> {actual_line_num:3} | {line}\n"));

            // Add highlighting
            let line_start = source_code[..start].rfind('\n').map_or(0, |pos| pos + 1);
            let error_start_col = start - line_start;
            let error_end_col = if end > start {
                std::cmp::min(error_start_col + (end - start), line.len())
            } else {
                error_start_col + 1
            };

            result.push_str("     | ");
            for _ in 0..error_start_col {
                result.push(' ');
            }
            for _ in error_start_col..error_end_col {
                result.push('^');
            }
            result.push('\n');
        } else {
            result.push_str(&format!("  {actual_line_num:3} | {line}\n"));
        }
    }

    result
}

/// Format comprehensive typing context
fn format_typing_context(
    typing_ctx: &PooledTypingContext,
    pools: &Pools,
    source_code: &str,
    filename: &str,
) -> String {
    let mut result = String::new();
    result.push_str("Type inference context:\n");

    // Show local variables (type schemes stack)
    if !typing_ctx.type_schemes.is_empty() {
        result.push_str("Local variables (De Bruijn indexed):\n");
        for (i, scheme) in typing_ctx.type_schemes.iter().enumerate() {
            let quantified_vars: Vec<String> = scheme
                .quantified
                .iter()
                .map(format_type_var_name)
                .collect();

            if quantified_vars.is_empty() {
                result.push_str(&format!(
                    "  Var#{} : {}\n",
                    i,
                    pools.display_type(scheme.ty)
                ));
            } else {
                result.push_str(&format!(
                    "  Var#{} : ∀{}. {}\n",
                    i,
                    quantified_vars.join(" "),
                    pools.display_type(scheme.ty)
                ));
            }
        }
        result.push('\n');
    }

    // Show substitutions
    if !typing_ctx.substitutions.is_empty() {
        result.push_str("Unifications:\n");
        for (var, type_id) in &typing_ctx.substitutions {
            let var_name = format_type_var_name(var);
            result.push_str(&format!(
                "  {} = {}\n",
                var_name,
                pools.display_type(*type_id)
            ));
        }
        result.push('\n');
    }

    // Show expression types
    if !typing_ctx.expr_types.is_empty() {
        result.push_str("Expression types:\n");
        for (expr_id, type_ids) in &typing_ctx.expr_types {
            let expr_span = pools.get_expr_span(*expr_id);
            let pos = format_emacs_position(expr_span, pools, source_code, filename);
            result.push_str(&format!("  {}: {} : ", pos, pools.display_expr(*expr_id)));
            for (i, type_id) in type_ids.iter().enumerate() {
                if i > 0 {
                    result.push_str(", ");
                }
                result.push_str(&pools.display_type(*type_id).to_string());
            }
            result.push('\n');
        }
        result.push('\n');
    }

    // Show global functions
    result.push_str("Global functions:\n");
    for name in &pools.global_order {
        if let Some(scheme) = pools.get_global_scheme(name) {
            let quantified_vars: Vec<String> = scheme
                .quantified
                .iter()
                .map(format_type_var_name)
                .collect();

            if quantified_vars.is_empty() {
                result.push_str(&format!(
                    "  {} : {}\n",
                    name.as_str(),
                    pools.display_type(scheme.ty)
                ));
            } else {
                result.push_str(&format!(
                    "  {} : ∀{}. {}\n",
                    name.as_str(),
                    quantified_vars.join(" "),
                    pools.display_type(scheme.ty)
                ));
            }
        }
    }

    result
}
