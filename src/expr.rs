use crate::{
    InternedString,
    pools::{DeBruijnIndex, ExprId, GlobalVarIdx, PatternId, Pools, SpanId, TypeId},
    types::FieldId,
};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecordField {
    pub name: InternedString,
    pub expr: ExprId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Spread {
    pub name: Option<InternedString>, // Optional name for spread binding
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecordPatternField {
    pub name: InternedString,
    pub pattern: Pattern,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expr {
    Int(isize, SpanId),
    String(InternedString, SpanId),
    Unit(SpanId),
    Var(DeBruijnIndex, InternedString, SpanId),
    GlobalVar(GlobalVarIdx, InternedString, SpanId),
    Call(ExprId, ExprId, SpanId),
    Lambda(ExprId, InternedString, SpanId),
    Let(ExprId, ExprId, InternedString, SpanId),

    // FCP extensions for data constructors
    Construct(InternedString, ExprId, SpanId), // K E - constructor application
    Match(ExprId, MatchArms, SpanId),          // match expr with pattern arms

    // Row polymorphism - records
    Record(FieldId, usize, SpanId), // Record literal {field1: expr1, ..., fieldn: exprn} - start, len
    Project(ExprId, InternedString, SpanId), // Record field projection expr.field
    Extend(ExprId, FieldId, usize, SpanId), // Record extension {record with field1: expr1, ..., fieldn: exprn} - record, start, len

    // FFI - Foreign Function Interface
    Ffi(InternedString, Option<TypeId>, Option<ExprId>, SpanId), // ffi!(<js_code>, optional_type, optional_arg)
}

impl Expr {
    #[must_use]
    pub const fn span(&self) -> SpanId {
        match self {
            Self::Int(_, span) | Self::String(_, span) | Self::Var(_, _, span) | Self::GlobalVar(_, _, span) | Self::Call(_, _, span) | Self::Lambda(_, _, span) | Self::Let(_, _, _, span) | Self::Construct(_, _, span) | Self::Match(_, _, span) | Self::Record(_, _, span) | Self::Project(_, _, span) | Self::Extend(_, _, _, span) | Self::Ffi(_, _, _, span) => *span,
            Self::Unit(span) => *span,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MatchArms {
    pub start_id: PatternId,
    pub length: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pattern {
    Constructor(InternedString, PatternId, usize, SpanId), // K [patterns] - constructor with pattern pool start and length
    Variable(DeBruijnIndex, InternedString, SpanId), // x - variable pattern with index and name
    Wildcard(SpanId),                                // _ - wildcard pattern
    Int(isize, SpanId),                              // integer literal pattern
    String(InternedString, SpanId),                  // string literal pattern
    Record(FieldId, usize, Option<Spread>, SpanId), // Record pattern {field1: pat1, ..., fieldn: patn, ...spread} - start, len, spread
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PatternBinding {
    pub debruijn: DeBruijnIndex,
    pub name: InternedString,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MatchCase {
    pub pattern: Pattern,
    pub body: ExprId,
}

impl Pools {
    #[must_use]
    pub const fn display_expr(&self, id: ExprId) -> ExprDisplay {
        ExprDisplay { pool: self, id }
    }
}

pub struct ExprDisplay<'a> {
    pool: &'a Pools,
    id: ExprId,
}

impl fmt::Display for ExprDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_expr(f, self.id)
    }
}

impl ExprDisplay<'_> {
    fn fmt_expr(&self, f: &mut fmt::Formatter<'_>, id: ExprId) -> fmt::Result {
        let expr = self.pool[id];
        match expr {
            Expr::Int(n, _span) => write!(f, "{n}"),
            Expr::String(s, _span) => write!(f, "\"{}\"", s.as_str()),
            Expr::Unit(_span) => write!(f, "()"),
            Expr::Var(_debruijn, name, _span) => write!(f, "{name}"),
            Expr::GlobalVar(_, name, _span) => write!(f, "{name}"),
            Expr::Call(fun_id, arg_id, _span) => {
                let fun_expr = self.pool[fun_id];
                let needs_parens = matches!(fun_expr, Expr::Lambda(..) | Expr::Let(..));

                if needs_parens {
                    write!(f, "(")?;
                    self.fmt_expr(f, fun_id)?;
                    write!(f, ")")?;
                } else {
                    self.fmt_expr(f, fun_id)?;
                }

                write!(f, " ")?;

                let arg_expr = self.pool[arg_id];
                let arg_needs_parens =
                    matches!(arg_expr, Expr::Call(..) | Expr::Lambda(..) | Expr::Let(..));

                if arg_needs_parens {
                    write!(f, "(")?;
                    self.fmt_expr(f, arg_id)?;
                    write!(f, ")")?;
                } else {
                    self.fmt_expr(f, arg_id)?;
                }

                Ok(())
            }
            Expr::Lambda(body_id, param_name, _span) => {
                write!(f, "fn {param_name} => ")?;
                self.fmt_expr(f, body_id)
            }
            Expr::Let(value_id, body_id, var_name, _span) => {
                write!(f, "let {var_name} = ")?;
                self.fmt_expr(f, value_id)?;
                write!(f, " in ")?;
                self.fmt_expr(f, body_id)
            }
            Expr::Construct(constructor, arg_id, _span) => {
                write!(f, "{constructor} ")?;
                let arg_expr = self.pool[arg_id];
                let arg_needs_parens = matches!(
                    arg_expr,
                    Expr::Call(..) | Expr::Lambda(..) | Expr::Let(..) | Expr::Match(..)
                );

                if arg_needs_parens {
                    write!(f, "(")?;
                    self.fmt_expr(f, arg_id)?;
                    write!(f, ")")?;
                } else {
                    self.fmt_expr(f, arg_id)?;
                }

                Ok(())
            }
            Expr::Match(expr_id, match_arms, _span) => {
                write!(f, "match ")?;
                self.fmt_expr(f, expr_id)?;
                write!(f, " with")?;

                for i in 0..match_arms.length {
                    let case = self.pool[PatternId(match_arms.start_id.0 + i)];
                    write!(f, " | ")?;
                    Self::fmt_pattern(f, case.pattern, self.pool)?;
                    write!(f, " -> ")?;
                    self.fmt_expr(f, case.body)?;
                }

                Ok(())
            }
            Expr::Record(start, len, _span) => {
                write!(f, "{{")?;
                let fields = self.pool.get_record_fields(start.0, len);
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: ", field.name.as_str())?;
                    self.fmt_expr(f, field.expr)?;
                }
                write!(f, "}}")
            }
            Expr::Project(expr_id, field_name, _span) => {
                let expr = self.pool[expr_id];
                let needs_parens = matches!(
                    expr,
                    Expr::Call(..) | Expr::Lambda(..) | Expr::Let(..) | Expr::Match(..)
                );

                if needs_parens {
                    write!(f, "(")?;
                    self.fmt_expr(f, expr_id)?;
                    write!(f, ")")?;
                } else {
                    self.fmt_expr(f, expr_id)?;
                }
                write!(f, ".{}", field_name.as_str())
            }
            Expr::Extend(record_id, start, len, _span) => {
                write!(f, "{{")?;
                self.fmt_expr(f, record_id)?;
                write!(f, " with ")?;
                let fields = self.pool.get_record_fields(start.0, len);
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: ", field.name.as_str())?;
                    self.fmt_expr(f, field.expr)?;
                }
                write!(f, "}}")
            }
            Expr::Ffi(js_code, _type_annotation, arg, _span) => {
                write!(f, "ffi!(<{}>", js_code.as_str())?;
                if let Some(arg_id) = arg {
                    write!(f, ", ")?;
                    self.fmt_expr(f, arg_id)?;
                }
                write!(f, ")")
            }
        }
    }

    fn fmt_pattern(f: &mut fmt::Formatter<'_>, pattern: Pattern, pool: &Pools) -> fmt::Result {
        match pattern {
            Pattern::Constructor(constructor, start_id, length, _span) => {
                write!(f, "{constructor}")?;
                if length > 0 {
                    let nested_patterns = pool.get_nested_patterns(start_id.0, length);
                    for pattern in nested_patterns {
                        write!(f, " ")?;
                        Self::fmt_pattern(f, *pattern, pool)?;
                    }
                }
                Ok(())
            }
            Pattern::Variable(_debruijn, var_name, _span) => {
                write!(f, "{var_name}",)
            }
            Pattern::Wildcard(_span) => {
                write!(f, "_")
            }
            Pattern::Int(n, _span) => {
                write!(f, "{n}")
            }
            Pattern::String(s, _span) => {
                write!(f, "\"{}\"", s.as_str())
            }
            Pattern::Record(start, len, spread, _span) => {
                write!(f, "{{")?;
                let fields = pool.get_record_pattern_fields(start.0, len);
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: ", field.name.as_str())?;
                    Self::fmt_pattern(f, field.pattern, pool)?;
                }
                if let Some(spread) = spread {
                    if len > 0 {
                        write!(f, ", ")?;
                    }
                    if let Some(name) = spread.name {
                        write!(f, "...{name}")?;
                    } else {
                        write!(f, "...")?;
                    }
                }
                write!(f, "}}")
            }
        }
    }
}
