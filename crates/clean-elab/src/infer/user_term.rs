// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Execution bridge for user-defined `elab "kw" e:term ... : term => <body>`
//! term elaborators (metaprogramming evaluator, phase 5).
//!
//! # Why terms are harder than tactics
//!
//! A tactic-category elaborator has a clean dispatch point: tactic invocations
//! parse to `SurfaceTactic::Named { name, args }`, so the keyword is already an
//! isolated head symbol the tactic evaluator can route on. The term category
//! has no such node — a user keyword in *term* position is just an ordinary
//! identifier, so `kw e` parses as the application `App(Ident("kw"), [e])` (and
//! a nullary `kw` parses as the bare `Ident("kw")`).
//!
//! The recognition path therefore works on the *post-macro-expansion* surface
//! shape: we register the keyword + its bound variable names, and when the
//! elaborator encounters an `App`/`Ident` whose head identifier is a registered
//! keyword, it binds the call-site arguments to the pattern variables,
//! substitutes them into the body surface AST, and re-elaborates the
//! substituted body through the normal pipeline.
//!
//! # Soundness
//!
//! The substituted body is elaborated by the *normal* `ElabCtx::elaborate`
//! pipeline and kernel-checked exactly like any other term. Substitution only
//! replaces a bound identifier with the call-site argument's already-parsed
//! surface expression; it never fabricates a kernel term or asserts
//! well-typedness. An ill-typed body (e.g. `elab "bad" : term => Nat.succ`
//! used where a `Nat` is expected) fails elaboration with the ordinary
//! type-mismatch error. No kernel bypass, no new axioms.
//!
//! # Deferred shapes
//!
//! Only the leading-keyword + flat bound-variable pattern is recognized (the
//! same tractable core the tactic path accepts). Bodies that need term-level
//! metaprogramming primitives at elaboration time (`do`-notation that calls
//! `elabTerm`/`mkApp`/`mkConst`, quotation-returning bodies, repetition or
//! optional patterns) are not registered here and fall through to the existing
//! handling.

use std::collections::HashMap;

use clean_parser::{DoElem, InterpolationPart, SurfaceArg, SurfaceExpr};

/// A registered user-defined term elaborator.
///
/// Keyed in [`ElabCtx`](crate::infer::ElabCtx) by its keyword. Stores the bound
/// variable names (in pattern order) and the body surface expression to
/// substitute into and elaborate.
#[derive(Debug, Clone)]
pub(super) struct UserTermElab {
    /// Bound pattern variable names, in left-to-right order (e.g. `["e"]` for
    /// `elab "mywrap" e:term : term => ...`). Empty for a nullary keyword.
    pub(super) bound_vars: Vec<String>,
    /// The body expression (right of `=>`) to substitute bindings into and
    /// elaborate.
    pub(super) body: SurfaceExpr,
    /// Whether the FINAL bound variable is optional (`x:term?`). When `true`,
    /// the keyword may be called with either all `bound_vars.len()` arguments
    /// (the optional one present) or one fewer (the optional one absent). In the
    /// absent case the trailing optional variable is left unsubstituted — it
    /// stays a free identifier, so a body that references it fails honestly
    /// (unknown identifier) while a body that does not reference it elaborates
    /// normally. No `Option`/`getD` plumbing is fabricated; the soundness
    /// boundary is identical to the mandatory path. `false` for the flat
    /// (all-mandatory) shape.
    pub(super) optional_trailing: bool,
}

/// A single substitution: a bound identifier mapped to the surface expression
/// that should replace it.
type Binding = (String, SurfaceExpr);

/// If `expanded` is a call to a registered user term keyword, return the keyword
/// and the positional call-site argument expressions.
///
/// Recognizes the two parser shapes a user keyword takes in term position:
/// - `App(Ident(kw), args)` for `kw a b ...`, and
/// - bare `Ident(kw)` for a nullary keyword `kw`.
///
/// Returns `None` (so normal elaboration proceeds) when the head is not a
/// registered keyword, when named arguments are present (the flat pattern is
/// positional only), or when the shape is anything else.
pub(super) fn match_user_term_call<'e>(
    expanded: &'e SurfaceExpr,
    registry: &HashMap<String, UserTermElab>,
) -> Option<(&'e str, Vec<SurfaceExpr>)> {
    match expanded {
        SurfaceExpr::Ident(_, name) if registry.contains_key(name) => Some((name.as_str(), vec![])),
        SurfaceExpr::App(_, func, args) => {
            let SurfaceExpr::Ident(_, name) = func.as_ref() else {
                return None;
            };
            if !registry.contains_key(name) {
                return None;
            }
            // The flat pattern binds positional arguments only. A named argument
            // (`f (x := e)`) does not correspond to a pattern slot, so defer.
            if args.iter().any(|a| a.name.is_some()) {
                return None;
            }
            let arg_exprs = args.iter().map(|a| a.expr.clone()).collect();
            Some((name.as_str(), arg_exprs))
        }
        _ => None,
    }
}

/// Build the substituted body for a recognized user term call.
///
/// Binds each pattern variable to the corresponding call-site argument and
/// substitutes those bindings into the body. Returns `None` when the call-site
/// arity does not match the declared bound-variable count, so a mis-applied
/// keyword falls through to the normal (error-reporting) elaboration path
/// instead of silently dropping or duplicating arguments.
///
/// # Optional trailing binder (`x:term?`)
///
/// When `entry.optional_trailing` is set, the FINAL bound variable is optional:
/// the call accepts either the full arity (optional present) or one fewer
/// (optional absent). In the absent case only the mandatory prefix is bound and
/// the trailing optional variable is intentionally left unsubstituted — it stays
/// a free identifier. A body that does not reference it elaborates normally; a
/// body that does reference it fails honestly through the normal pipeline
/// (unknown identifier). This never fabricates a binding, an `Option`, or a
/// default value, so the soundness boundary matches the mandatory path exactly.
pub(super) fn build_substituted_body(
    entry: &UserTermElab,
    args: &[SurfaceExpr],
) -> Option<SurfaceExpr> {
    let declared = entry.bound_vars.len();
    // The number of leading mandatory variables to bind. With an optional
    // trailing binder the call may legally supply one fewer argument.
    let bind_prefix = if entry.optional_trailing && declared > 0 && args.len() == declared - 1 {
        // Optional trailing binder absent: bind only the mandatory prefix.
        declared - 1
    } else if args.len() == declared {
        // Full arity: bind every declared variable (the optional one, if any,
        // is present and bound like the rest).
        declared
    } else {
        // Any other arity is a genuine mismatch; defer to the normal pipeline.
        return None;
    };
    let bindings: Vec<Binding> = entry.bound_vars[..bind_prefix]
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    Some(substitute_in_expr(&entry.body, &bindings))
}

/// Recursively substitute pattern bindings inside a surface expression.
///
/// Replaces every `SurfaceExpr::Ident(_, name)` whose `name` matches a bound
/// variable with the call-site argument expression, descending through the
/// common term shapes. Binder-introducing forms (`lambda`/`pi`/`let`) are left
/// to the elaborator: substitution here targets the argument-position uses of
/// the pattern variables, which is the tractable core the tactic path also
/// covers. A pattern variable that is itself shadowed by a body binder would
/// not be a sensible elaborator anyway.
fn substitute_in_expr(expr: &SurfaceExpr, bindings: &[Binding]) -> SurfaceExpr {
    match expr {
        SurfaceExpr::Ident(_, name) => bindings
            .iter()
            .find(|(bound, _)| bound == name)
            .map_or_else(|| expr.clone(), |(_, replacement)| replacement.clone()),
        SurfaceExpr::App(span, func, args) => SurfaceExpr::App(
            *span,
            Box::new(substitute_in_expr(func, bindings)),
            args.iter()
                .map(|a| SurfaceArg {
                    span: a.span,
                    expr: substitute_in_expr(&a.expr, bindings),
                    name: a.name.clone(),
                })
                .collect(),
        ),
        SurfaceExpr::Paren(span, inner) => {
            SurfaceExpr::Paren(*span, Box::new(substitute_in_expr(inner, bindings)))
        }
        SurfaceExpr::Ascription(span, inner, ty) => SurfaceExpr::Ascription(
            *span,
            Box::new(substitute_in_expr(inner, bindings)),
            Box::new(substitute_in_expr(ty, bindings)),
        ),
        SurfaceExpr::Explicit(span, inner) => {
            SurfaceExpr::Explicit(*span, Box::new(substitute_in_expr(inner, bindings)))
        }
        SurfaceExpr::Arrow(span, from, to) => SurfaceExpr::Arrow(
            *span,
            Box::new(substitute_in_expr(from, bindings)),
            Box::new(substitute_in_expr(to, bindings)),
        ),
        SurfaceExpr::If(span, cond, then_br, else_br) => SurfaceExpr::If(
            *span,
            Box::new(substitute_in_expr(cond, bindings)),
            Box::new(substitute_in_expr(then_br, bindings)),
            Box::new(substitute_in_expr(else_br, bindings)),
        ),
        SurfaceExpr::Proj(span, inner, proj) => SurfaceExpr::Proj(
            *span,
            Box::new(substitute_in_expr(inner, bindings)),
            proj.clone(),
        ),
        SurfaceExpr::NamedArg(span, name, value) => SurfaceExpr::NamedArg(
            *span,
            name.clone(),
            Box::new(substitute_in_expr(value, bindings)),
        ),
        // A `do`-block body (used by the metaprogram value channel, e.g.
        // `do let t := inferType e; t`) substitutes into each statement's
        // expression payloads. A `let`/bind binder shadows a same-named pattern
        // variable for the remainder of the block, matching lexical scoping, so
        // that binding is dropped before substituting the following statements.
        SurfaceExpr::Do(span, elems) => {
            SurfaceExpr::Do(*span, substitute_in_do_elems(elems, bindings))
        }
        // A string-interpolation (`s!"got {x}"`) substitutes into each embedded
        // `{expr}` hole so a pattern variable used inside an interpolated message
        // (e.g. a `throwError s!"got {x}"` body) is replaced by its call-site
        // argument before the message is rendered. Literal chunks are unchanged.
        SurfaceExpr::InterpolatedStr { span, kind, parts } => SurfaceExpr::InterpolatedStr {
            span: *span,
            kind: *kind,
            parts: parts
                .iter()
                .map(|part| match part {
                    InterpolationPart::Expr(expr) => {
                        InterpolationPart::Expr(substitute_in_expr(expr, bindings))
                    }
                    InterpolationPart::Literal(text) => InterpolationPart::Literal(text.clone()),
                    // A future variant is passed through unchanged (conservative:
                    // the elaborator resolves it, failing honestly if it cannot).
                    other => other.clone(),
                })
                .collect(),
        },
        // Leaf / binder-introducing / unsupported shapes are returned unchanged:
        // any bound variable nested inside them is left for the elaborator to
        // resolve, which fails honestly if it cannot, never fabricating success.
        other => other.clone(),
    }
}

/// Substitute pattern bindings into a `do`-block statement sequence, honoring
/// lexical scoping: a `let`/bind statement that introduces a binder shadows any
/// same-named pattern variable for the remaining statements (the binding is
/// dropped before recursing into them). Only the statement shapes the
/// metaprogram value channel uses (`let`, monadic bind, expression) substitute
/// into their payloads; other statement shapes are passed through unchanged (the
/// elaborator resolves them, failing honestly if it cannot).
fn substitute_in_do_elems(elems: &[DoElem], bindings: &[Binding]) -> Vec<DoElem> {
    // Bindings still in effect at the current statement (shrinks as inner `do`
    // binders shadow same-named pattern variables).
    let mut active: Vec<Binding> = bindings.to_vec();
    let mut out = Vec::with_capacity(elems.len());
    for elem in elems {
        match elem {
            DoElem::Let(span, binder, val) => {
                let new_val = Box::new(substitute_in_expr(val, &active));
                out.push(DoElem::Let(*span, binder.clone(), new_val));
                drop_binding(&mut active, &binder.name);
            }
            DoElem::Bind(span, binder, val) => {
                let new_val = Box::new(substitute_in_expr(val, &active));
                out.push(DoElem::Bind(*span, binder.clone(), new_val));
                drop_binding(&mut active, &binder.name);
            }
            DoElem::Expr(span, expr) => {
                out.push(DoElem::Expr(
                    *span,
                    Box::new(substitute_in_expr(expr, &active)),
                ));
            }
            // Other do-statement shapes (control flow, etc.) are passed through
            // unchanged: the value channel does not use them, and leaving them
            // intact keeps substitution conservative.
            other => out.push(other.clone()),
        }
    }
    out
}

/// Remove any binding for `name` (an inner `do` binder shadows the pattern
/// variable for the remainder of the block).
fn drop_binding(bindings: &mut Vec<Binding>, name: &str) {
    bindings.retain(|(bound, _)| bound != name);
}

#[cfg(test)]
#[path = "user_term_tests.rs"]
mod tests;
