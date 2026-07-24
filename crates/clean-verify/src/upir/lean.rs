// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean translation for the Lean-compatible UPIR subset.

use super::syntax::{
    BinderStyle, UpirBinder, UpirExpr, UpirForeignExpr, UpirLevel, UpirLiteral, UpirName,
    UpirPattern, UpirProjection, UpirSort,
};
use super::UpirValidationError;
use std::collections::HashSet;

const PREC_TOP: u8 = 0;
const PREC_APP: u8 = 1;
const PREC_ATOM: u8 = 2;

/// Errors raised while translating UPIR into Lean syntax.
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum LeanTranslationError {
    #[error("UPIR validation failed: {0}")]
    Validation(UpirValidationError),
    #[error("unbound de Bruijn variable #{index} at render depth {depth}")]
    UnboundVar { index: u32, depth: usize },
    #[error("match motives are not currently rendered to Lean")]
    UnsupportedMatchMotive,
    #[error("holes are not renderable as Lean proofs: ?m.{0}")]
    Hole(u64),
    #[error("foreign sort `{0}` cannot be rendered to Lean")]
    ForeignSort(String),
    #[error("foreign construct `{0}` cannot be rendered to Lean")]
    ForeignExpr(String),
    #[error("name segment `{0}` cannot be escaped for Lean")]
    InvalidNameSegment(String),
    #[error("proof bundle is missing a statement")]
    MissingStatement,
    #[error("failed to parse rendered Lean source `{0}`: {1}")]
    Parse(String, String),
    #[error("failed to elaborate rendered Lean source `{0}`: {1}")]
    Elab(String, String),
}

#[derive(Debug, Default)]
struct RenderCtx {
    scope: Vec<String>,
    used_locals: HashSet<String>,
}

pub(crate) fn render_expr(expr: &UpirExpr) -> Result<String, LeanTranslationError> {
    let mut ctx = RenderCtx::default();
    render_expr_prec(expr, PREC_TOP, &mut ctx)
}

pub(crate) fn render_global_name(name: &UpirName) -> Result<String, LeanTranslationError> {
    name.segments()
        .iter()
        .map(|segment| render_name_segment(segment))
        .collect::<Result<Vec<_>, _>>()
        .map(|segments| segments.join("."))
}

fn render_expr_prec(
    expr: &UpirExpr,
    parent_prec: u8,
    ctx: &mut RenderCtx,
) -> Result<String, LeanTranslationError> {
    let rendered = match expr {
        UpirExpr::Var(index) => render_var(*index, ctx)?,
        UpirExpr::Sort(sort) => render_sort(sort)?,
        UpirExpr::Const {
            name, universes, ..
        } => render_const(name, universes)?,
        UpirExpr::App(_, _) => render_app(expr, ctx)?,
        UpirExpr::Lambda {
            binder,
            domain,
            body,
        } => render_lambda(binder, domain, body, ctx)?,
        UpirExpr::Pi {
            binder,
            domain,
            body,
        } => render_pi(binder, domain, body, ctx)?,
        UpirExpr::Let {
            binder,
            type_,
            value,
            body,
        } => render_let(binder, type_, value, body, ctx)?,
        UpirExpr::Match {
            scrutinee,
            motive,
            arms,
            ..
        } => render_match(scrutinee, motive.as_deref(), arms, ctx)?,
        UpirExpr::Proj { expr, projection } => {
            let base = render_expr_prec(expr, PREC_ATOM, ctx)?;
            let projection = match projection {
                UpirProjection::Index(index) => index.to_string(),
                UpirProjection::Field(field) => render_name_segment(field)?,
            };
            format!("{base}.{projection}")
        }
        UpirExpr::Annot { expr, type_ } => {
            let expr = render_expr_prec(expr, PREC_TOP, ctx)?;
            let type_ = render_expr_prec(type_, PREC_TOP, ctx)?;
            format!("({expr} : {type_})")
        }
        UpirExpr::Literal(literal) => render_literal(literal),
        UpirExpr::SourceLoc { expr, .. } => render_expr_prec(expr, parent_prec, ctx)?,
        UpirExpr::Hole { id, .. } => return Err(LeanTranslationError::Hole(*id)),
        UpirExpr::Foreign(foreign) => {
            return Err(LeanTranslationError::ForeignExpr(foreign_label(foreign)))
        }
    };

    let my_prec = expr_prec(expr);
    if my_prec < parent_prec {
        Ok(format!("({rendered})"))
    } else {
        Ok(rendered)
    }
}

fn expr_prec(expr: &UpirExpr) -> u8 {
    match expr {
        UpirExpr::Var(_)
        | UpirExpr::Sort(_)
        | UpirExpr::Const { .. }
        | UpirExpr::Proj { .. }
        | UpirExpr::Literal(_)
        | UpirExpr::Hole { .. }
        | UpirExpr::Foreign(_) => PREC_ATOM,
        UpirExpr::App(_, _) => PREC_APP,
        UpirExpr::SourceLoc { expr, .. } => expr_prec(expr),
        UpirExpr::Annot { .. }
        | UpirExpr::Lambda { .. }
        | UpirExpr::Pi { .. }
        | UpirExpr::Let { .. }
        | UpirExpr::Match { .. } => PREC_TOP,
    }
}

fn render_var(index: u32, ctx: &RenderCtx) -> Result<String, LeanTranslationError> {
    let depth = ctx.scope.len();
    let slot = usize::try_from(index).expect("u32 always fits in usize");
    if slot >= depth {
        return Err(LeanTranslationError::UnboundVar { index, depth });
    }
    Ok(ctx.scope[depth - 1 - slot].clone())
}

fn render_sort(sort: &UpirSort) -> Result<String, LeanTranslationError> {
    match sort {
        UpirSort::Prop => Ok("Prop".to_string()),
        UpirSort::Type(UpirLevel::Zero) => Ok("Type".to_string()),
        UpirSort::Type(level) => Ok(format!("Type {}", render_level(level)?)),
        UpirSort::Foreign { descriptor, .. } => {
            Err(LeanTranslationError::ForeignSort(descriptor.clone()))
        }
    }
}

fn render_const(name: &UpirName, universes: &[UpirLevel]) -> Result<String, LeanTranslationError> {
    let name = render_global_name(name)?;
    if universes.is_empty() {
        Ok(name)
    } else {
        let levels = universes
            .iter()
            .map(render_level)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!("{name}.{{{}}}", levels.join(", ")))
    }
}

fn render_app(expr: &UpirExpr, ctx: &mut RenderCtx) -> Result<String, LeanTranslationError> {
    let mut args = Vec::new();
    let mut head = expr;
    while let UpirExpr::App(func, arg) = head {
        args.push(arg.as_ref());
        head = func.as_ref();
    }
    args.reverse();

    let mut parts = Vec::with_capacity(args.len() + 1);
    parts.push(render_expr_prec(head, PREC_APP, ctx)?);
    for arg in args {
        parts.push(render_expr_prec(arg, PREC_ATOM, ctx)?);
    }
    Ok(parts.join(" "))
}

fn render_lambda(
    binder: &UpirBinder,
    domain: &UpirExpr,
    body: &UpirExpr,
    ctx: &mut RenderCtx,
) -> Result<String, LeanTranslationError> {
    let domain = render_expr_prec(domain, PREC_TOP, ctx)?;
    let local = ctx.fresh_local_name(binder.name.as_deref());
    ctx.scope.push(local.clone());
    let body = render_expr_prec(body, PREC_TOP, ctx)?;
    let _ = ctx.scope.pop();
    Ok(format!(
        "fun {} => {body}",
        render_binder(binder.style, &local, &domain)
    ))
}

fn render_pi(
    binder: &UpirBinder,
    domain: &UpirExpr,
    body: &UpirExpr,
    ctx: &mut RenderCtx,
) -> Result<String, LeanTranslationError> {
    let domain = render_expr_prec(domain, PREC_TOP, ctx)?;
    let local = ctx.fresh_local_name(binder.name.as_deref());
    ctx.scope.push(local.clone());
    let body = render_expr_prec(body, PREC_TOP, ctx)?;
    let _ = ctx.scope.pop();
    Ok(format!(
        "forall {}, {body}",
        render_binder(binder.style, &local, &domain)
    ))
}

fn render_let(
    binder: &UpirBinder,
    type_: &UpirExpr,
    value: &UpirExpr,
    body: &UpirExpr,
    ctx: &mut RenderCtx,
) -> Result<String, LeanTranslationError> {
    let name = ctx.fresh_local_name(binder.name.as_deref());
    let type_ = render_expr_prec(type_, PREC_TOP, ctx)?;
    let value = render_expr_prec(value, PREC_TOP, ctx)?;
    ctx.scope.push(name.clone());
    let body = render_expr_prec(body, PREC_TOP, ctx)?;
    let _ = ctx.scope.pop();
    Ok(format!("let {name} : {type_} := {value} in {body}"))
}

fn render_match(
    scrutinee: &UpirExpr,
    motive: Option<&UpirExpr>,
    arms: &[super::syntax::UpirMatchArm],
    ctx: &mut RenderCtx,
) -> Result<String, LeanTranslationError> {
    if motive.is_some() {
        return Err(LeanTranslationError::UnsupportedMatchMotive);
    }

    let scrutinee = render_expr_prec(scrutinee, PREC_TOP, ctx)?;
    let mut rendered_arms = Vec::with_capacity(arms.len());
    for arm in arms {
        rendered_arms.push(render_match_arm(arm, ctx)?);
    }
    Ok(format!(
        "match {scrutinee} with {}",
        rendered_arms.join(" ")
    ))
}

fn render_match_arm(
    arm: &super::syntax::UpirMatchArm,
    ctx: &mut RenderCtx,
) -> Result<String, LeanTranslationError> {
    let mut bindings = Vec::new();
    let pattern = render_pattern(&arm.pattern, ctx, &mut bindings)?;
    let previous_depth = ctx.scope.len();
    ctx.scope.extend(bindings.iter().cloned());
    let body = render_expr_prec(&arm.body, PREC_TOP, ctx)?;
    ctx.scope.truncate(previous_depth);
    Ok(format!("| {pattern} => {body}"))
}

fn render_pattern(
    pattern: &UpirPattern,
    ctx: &mut RenderCtx,
    bindings: &mut Vec<String>,
) -> Result<String, LeanTranslationError> {
    match pattern {
        UpirPattern::Wildcard => Ok("_".to_string()),
        UpirPattern::Var(name) => {
            let local = ctx.fresh_local_name(name.as_deref());
            bindings.push(local.clone());
            Ok(local)
        }
        UpirPattern::Literal(literal) => Ok(render_literal(literal)),
        UpirPattern::Ctor { name, args } => {
            let mut rendered = Vec::with_capacity(args.len() + 1);
            rendered.push(render_global_name(name)?);
            for arg in args {
                rendered.push(render_pattern(arg, ctx, bindings)?);
            }
            Ok(rendered.join(" "))
        }
    }
}

fn render_binder(style: BinderStyle, name: &str, domain: &str) -> String {
    match style {
        BinderStyle::Explicit => format!("({name} : {domain})"),
        BinderStyle::Implicit => format!("{{{name} : {domain}}}"),
        BinderStyle::StrictImplicit => format!("{{{{{name} : {domain}}}}}"),
        BinderStyle::InstanceImplicit => format!("[{name} : {domain}]"),
    }
}

fn render_level(level: &UpirLevel) -> Result<String, LeanTranslationError> {
    match level {
        UpirLevel::Zero => Ok("0".to_string()),
        UpirLevel::Succ(_) => {
            let (base, succs) = level_succ_chain(level);
            let base = render_level_atom(base)?;
            if base == "0" {
                Ok(succs.to_string())
            } else {
                Ok(format!("({base} + {succs})"))
            }
        }
        UpirLevel::Max(lhs, rhs) => Ok(format!(
            "(max {} {})",
            render_level(lhs)?,
            render_level(rhs)?
        )),
        UpirLevel::IMax(lhs, rhs) => Ok(format!(
            "(imax {} {})",
            render_level(lhs)?,
            render_level(rhs)?
        )),
        UpirLevel::Param(name) => render_name_segment(name),
    }
}

fn render_level_atom(level: &UpirLevel) -> Result<String, LeanTranslationError> {
    match level {
        UpirLevel::Zero | UpirLevel::Param(_) => render_level(level),
        _ => Ok(format!("({})", render_level(level)?)),
    }
}

fn level_succ_chain(mut level: &UpirLevel) -> (&UpirLevel, u32) {
    let mut succs = 0;
    while let UpirLevel::Succ(inner) = level {
        succs += 1;
        level = inner;
    }
    (level, succs)
}

fn render_literal(literal: &UpirLiteral) -> String {
    match literal {
        UpirLiteral::Nat(value) => value.to_string(),
        UpirLiteral::Bool(true) => "true".to_string(),
        UpirLiteral::Bool(false) => "false".to_string(),
        UpirLiteral::String(value) => format!("{value:?}"),
    }
}

fn render_name_segment(segment: &str) -> Result<String, LeanTranslationError> {
    if segment.is_empty() || segment.contains(['«', '»']) {
        return Err(LeanTranslationError::InvalidNameSegment(
            segment.to_string(),
        ));
    }
    if is_simple_ident(segment) && !is_reserved_keyword(segment) {
        return Ok(segment.to_string());
    }
    Ok(format!("«{segment}»"))
}

fn is_simple_ident(segment: &str) -> bool {
    let mut chars = segment.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first.is_ascii_alphabetic() || first == '_') {
        return false;
    }
    chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '\'')
}

fn is_reserved_keyword(segment: &str) -> bool {
    matches!(
        segment,
        "match"
            | "with"
            | "let"
            | "in"
            | "fun"
            | "forall"
            | "theorem"
            | "def"
            | "where"
            | "Prop"
            | "Type"
            | "Sort"
    )
}

fn foreign_label(foreign: &UpirForeignExpr) -> String {
    match foreign {
        UpirForeignExpr::CoqSet => "Coq Set".to_string(),
        UpirForeignExpr::CoqSProp => "Coq SProp".to_string(),
        UpirForeignExpr::AgdaInterval => "Agda interval".to_string(),
        UpirForeignExpr::HolType { repr } => format!("HOL type `{repr}`"),
        UpirForeignExpr::HolConst { name, .. } => format!("HOL constant `{name}`"),
        UpirForeignExpr::MetamathExpr { symbols } => {
            format!("Metamath expression `{}`", symbols.join(" "))
        }
        UpirForeignExpr::MizarTerm { repr } => format!("Mizar term `{repr}`"),
    }
}

impl RenderCtx {
    fn fresh_local_name(&mut self, preferred: Option<&str>) -> String {
        let base = sanitize_local_name(preferred.unwrap_or("x"));
        if self.used_locals.insert(base.clone()) {
            return base;
        }

        let mut counter = 1_u32;
        loop {
            let candidate = format!("{base}_{counter}");
            if self.used_locals.insert(candidate.clone()) {
                return candidate;
            }
            counter += 1;
        }
    }
}

fn sanitize_local_name(name: &str) -> String {
    let mut sanitized = String::with_capacity(name.len().max(1));
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' || ch == '\'' {
            sanitized.push(ch);
        } else {
            sanitized.push('_');
        }
    }
    if sanitized.is_empty() {
        sanitized.push('x');
    }
    let starts_ok = sanitized
        .chars()
        .next()
        .map(|ch| ch.is_ascii_alphabetic() || ch == '_')
        .unwrap_or(false);
    if !starts_ok {
        sanitized.insert_str(0, "x_");
    }
    if is_reserved_keyword(&sanitized) {
        sanitized.push('_');
    }
    sanitized
}
