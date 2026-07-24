// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minimal metaprogram value-constructor evaluator for term-elaborator bodies.
//!
//! # What this adds
//!
//! Phases 1–7 of the metaprogramming bridge made a term-elaborator body that is
//! written in *ordinary term syntax* work: `elab "myone" : term => Nat.succ
//! Nat.zero` substitutes its (possibly bound) call-site arguments into the body
//! and re-elaborates the body through the normal kernel-checked pipeline, so the
//! body `Nat.succ Nat.zero` elaborates to the kernel application
//! `Nat.succ Nat.zero` and is kernel-checked like any other term.
//!
//! What that path could *not* do is evaluate a body written in Lean's
//! `MetaM`/`TermElabM` *constructor* style, e.g.
//!
//! ```text
//! elab "myone" : term => mkApp (mkConst `Nat.succ) (mkConst `Nat.zero)
//! ```
//!
//! Here `mkConst`/`mkApp` are runtime `Expr`-builder functions that *compute*
//! the kernel `Expr` programmatically. Clean has no `MetaM` interpreter, so this
//! body previously failed with `UnknownIdent("mkConst")`.
//!
//! This module recognizes a small, fixed set of those `Expr`-builder builtins in
//! a term-elaborator body and rewrites each call into the equivalent *ordinary*
//! surface expression. The rewritten body is then elaborated by the normal
//! pipeline exactly as before.
//!
//! # Recognized builtins
//!
//! In Clean's transparent quotation model an `Expr` value is just the kernel
//! term it denotes, so each builtin maps to the surface form that elaborates to
//! the same term:
//!
//! | Builtin call                | Rewrites to        |
//! |-----------------------------|--------------------|
//! | `` mkConst `Foo ``          | `Foo`              |
//! | `` mkConst `Foo us ``       | `Foo`              |
//! | `mkApp f a`                 | `f a`              |
//! | `mkApp2 f a b`              | `f a b`            |
//! | `mkApp3 f a b c`            | `f a b c`          |
//! | `mkApp4 f a b c d`          | `f a b c d`        |
//! | `` Expr.const `Foo us ``    | `Foo`              |
//! | `Expr.app f a`              | `f a`              |
//! | `` mkLambda `x t b ``       | `fun x : t => b`   |
//! | `` Expr.lam `x t b bi ``    | `fun x : t => b`   |
//! | `` mkForall `x t b ``       | `(x : t) → b`      |
//! | `` Expr.forallE `x t b bi `` | `(x : t) → b`     |
//!
//! `mkConst` ignores the universe-level list (the elaborator infers levels from
//! the constant's signature); a constant that genuinely needs explicit levels is
//! written with the `Foo.{u}` surface form, which is preserved on rewrite.
//!
//! ## Binder builtins
//!
//! A binder constructor names its bound variable with a `` `x `` name literal,
//! followed by the binder type and the body (both ordinary sub-terms, rewritten
//! recursively). The optional `BinderInfo` argument is dropped — the surface
//! lambda/Pi always re-elaborates against the same kernel binder shape:
//!
//! - `Expr.lam`/`Expr.forallE` follow Lean's *constructor* signature
//!   `(name, type, body, binderInfo)`, so the `BinderInfo` (when present) is the
//!   trailing 4th argument and is dropped.
//! - `mkLambda`/`mkForall` follow Lean's *helper* signature
//!   `(name, binderInfo, type, body)`, so the `BinderInfo` (when present) is the
//!   2nd argument and is dropped.
//!
//! Both also accept the 3-argument `(name, type, body)` shape with no
//! `BinderInfo`. A binder whose name slot is not a `` `x `` literal, or whose
//! arity is neither 3 nor 4, defers (`None`) so a mis-shaped call falls through
//! and fails honestly.
//!
//! ## n-ary application
//!
//! Small-arity n-ary application is already covered by `mkApp2`/`mkApp3`/`mkApp4`
//! above. The general `mkAppN f #[a, b, …]` form is **not** rewritten: Clean's
//! parser drops the `#[…]` array literal entirely (and lowers the `[…]` list form
//! to a `List.cons`/`List.nil` chain), so there is no clean array of argument
//! sub-terms to recover. `mkAppN` therefore defers and fails honestly with
//! `UnknownIdent("mkAppN")` rather than guess at the arguments.
//!
//! Arguments are rewritten recursively, so nested calls
//! (`mkApp (mkConst `Nat.succ) (mkConst `Nat.zero)`) collapse to the plain
//! application `Nat.succ Nat.zero`.
//!
//! # Soundness
//!
//! This is a *syntactic* rewrite from one `SurfaceExpr` to another, followed by
//! the **normal** `ElabCtx::elaborate` pipeline. Nothing here fabricates a kernel
//! term or asserts well-typedness:
//!
//! - `` mkConst `Foo `` becomes the identifier `Foo`, which the elaborator
//!   resolves against the environment — an unknown name fails with
//!   `UnknownIdent`, never silently succeeds.
//! - `mkApp f a` becomes the application `f a`, which the elaborator
//!   type-checks — an ill-typed application (`mkApp Nat.succ Bool.true` used
//!   where a `Nat` is expected) fails with the ordinary type-mismatch error.
//!
//! The constructed term is kernel-checked by the same path as any other term.
//! There is no kernel bypass and no new axiom.

use clean_parser::{Projection, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr};

/// The fixed `Expr`-builder builtins recognized as `mkXxx` head identifiers,
/// paired with the number of *argument* positions they consume after the
/// (already-stripped) `Name` slot. `mkConst` is handled separately because its
/// leading argument is a name literal, not a sub-term.
///
/// For `mkApp`-family entries the value is the application arity (number of
/// arguments applied to the head function).
const MK_APP_BUILTINS: &[(&str, usize)] =
    &[("mkApp", 1), ("mkApp2", 2), ("mkApp3", 3), ("mkApp4", 4)];

/// Whether a binder builtin builds a lambda (`fun x : t => b`) or a dependent
/// arrow / `Pi` (`(x : t) → b`).
#[derive(Clone, Copy)]
enum BinderForm {
    /// `mkLambda` / `Expr.lam` — a `fun` binder.
    Lambda,
    /// `mkForall` / `Expr.forallE` — a dependent-arrow / `Pi` binder.
    Forall,
}

/// Where the optional `BinderInfo` argument sits in a 4-argument binder call.
///
/// Lean's `Expr.lam`/`Expr.forallE` *constructors* take `BinderInfo` last
/// (`name type body binderInfo`); the `mkLambda`/`mkForall` *helpers* take it
/// second (`name binderInfo type body`). Either way the `BinderInfo` is dropped:
/// the rewritten surface binder re-elaborates against the same kernel shape.
#[derive(Clone, Copy)]
enum BinderInfoSlot {
    /// `BinderInfo` is the trailing (4th) argument — `Expr.lam`/`Expr.forallE`.
    Last,
    /// `BinderInfo` is the 2nd argument — `mkLambda`/`mkForall`.
    Second,
}

/// The recognized binder builtins, paired with the binder they build and where
/// their optional `BinderInfo` argument sits when called with 4 arguments.
const BINDER_BUILTINS: &[(&str, BinderForm, BinderInfoSlot)] = &[
    ("mkLambda", BinderForm::Lambda, BinderInfoSlot::Second),
    ("mkForall", BinderForm::Forall, BinderInfoSlot::Second),
    ("Expr.lam", BinderForm::Lambda, BinderInfoSlot::Last),
    ("Expr.forallE", BinderForm::Forall, BinderInfoSlot::Last),
];

/// Rewrite recognized metaprogram constructor builtins inside `expr` into
/// ordinary surface expressions.
///
/// Returns `Some(rewritten)` if at least one builtin call was recognized and
/// rewritten anywhere in the tree, and `None` if the expression contains no
/// recognized builtin (so the caller can keep the original body unchanged and
/// avoid an allocation).
///
/// The walk is structural over the term shapes a constructor-style body uses:
/// applications, parentheses, ascriptions, and explicit markers. Other shapes
/// are returned unchanged — a builtin nested inside, say, a `match` arm is left
/// for the normal pipeline (and, since it is not rewritten, will fail honestly
/// with `UnknownIdent` rather than be silently accepted).
#[must_use]
pub(super) fn rewrite_meta_builtins(expr: &SurfaceExpr) -> Option<SurfaceExpr> {
    let mut changed = false;
    let rewritten = rewrite(expr, &mut changed);
    changed.then_some(rewritten)
}

/// Core recursive rewrite. Sets `*changed` to `true` whenever a builtin call is
/// recognized at this node or in a descendant.
fn rewrite(expr: &SurfaceExpr, changed: &mut bool) -> SurfaceExpr {
    // First, see whether *this* node is a recognized builtin call.
    if let Some(builtin) = match_builtin_call(expr) {
        *changed = true;
        return lower_builtin(builtin, changed);
    }

    // Otherwise descend into the term-construction shapes a body uses.
    match expr {
        SurfaceExpr::App(span, func, args) => SurfaceExpr::App(
            *span,
            Box::new(rewrite(func, changed)),
            args.iter()
                .map(|a| SurfaceArg {
                    span: a.span,
                    expr: rewrite(&a.expr, changed),
                    name: a.name.clone(),
                })
                .collect(),
        ),
        SurfaceExpr::Paren(span, inner) => {
            SurfaceExpr::Paren(*span, Box::new(rewrite(inner, changed)))
        }
        SurfaceExpr::Ascription(span, inner, ty) => SurfaceExpr::Ascription(
            *span,
            Box::new(rewrite(inner, changed)),
            // The ascription type is an ordinary type, not a constructor body,
            // so it is left as-is; only the value side is rewritten.
            ty.clone(),
        ),
        SurfaceExpr::Explicit(span, inner) => {
            SurfaceExpr::Explicit(*span, Box::new(rewrite(inner, changed)))
        }
        // Leaf / binder-introducing / unsupported shapes are returned unchanged.
        other => other.clone(),
    }
}

/// A recognized builtin call, normalized into the surface pieces needed to lower
/// it to an ordinary expression.
enum Builtin<'e> {
    /// `` mkConst `Name `` / `` Expr.const `Name us `` — yields the identifier
    /// `Name`. The span carried is the call's span for diagnostics.
    Const {
        span: clean_parser::Span,
        name: String,
    },
    /// `mkApp f a` / `mkApp2 f a b` / `Expr.app f a` — yields the application of
    /// the head to the argument sub-terms (each recursively rewritten by the
    /// caller).
    App {
        span: clean_parser::Span,
        func: &'e SurfaceExpr,
        args: Vec<&'e SurfaceExpr>,
    },
    /// `` mkLambda `x t b `` / `` Expr.forallE `x t b bi `` — yields the surface
    /// lambda or dependent-arrow binding `name : ty` over `body` (the `ty` and
    /// `body` sub-terms are recursively rewritten by the caller).
    Binder {
        span: clean_parser::Span,
        form: BinderForm,
        name: String,
        ty: &'e SurfaceExpr,
        body: &'e SurfaceExpr,
    },
}

/// If `expr` is a call to a recognized `Expr`-builder builtin, classify it.
///
/// Recognizes the head identifier (`mkApp`, `mkConst`, …) or the qualified
/// projection (`Expr.const`, `Expr.app`) and checks the argument arity. Returns
/// `None` for anything else, including a builtin head applied with the wrong
/// arity (which then falls through and fails honestly during elaboration).
fn match_builtin_call(expr: &SurfaceExpr) -> Option<Builtin<'_>> {
    let SurfaceExpr::App(span, func, args) = expr else {
        return None;
    };
    // Any named argument means this is not the flat positional builtin shape.
    if args.iter().any(|a| a.name.is_some()) {
        return None;
    }
    let head = builtin_head_name(func)?;

    match head.as_str() {
        // `mkConst `Name` (arity 1) or `mkConst `Name us` (arity 2, level list
        // dropped). The first argument must be a name literal (SyntaxQuote).
        "mkConst" if args.len() == 1 || args.len() == 2 => {
            let name = name_literal(&args[0].expr)?;
            Some(Builtin::Const { span: *span, name })
        }
        // `Expr.const `Name us` — Lean's constructor always takes the level
        // list, but we accept arity 1 or 2 and drop the levels either way.
        "Expr.const" if args.len() == 1 || args.len() == 2 => {
            let name = name_literal(&args[0].expr)?;
            Some(Builtin::Const { span: *span, name })
        }
        // `Expr.app f a` — exactly two sub-terms.
        "Expr.app" if args.len() == 2 => Some(Builtin::App {
            span: *span,
            func: &args[0].expr,
            args: vec![&args[1].expr],
        }),
        // Binder builtins (`mkLambda`/`mkForall`/`Expr.lam`/`Expr.forallE`)
        // before the `mkApp`-family fallthrough, since both are reached via the
        // catch-all `head` string.
        other if BINDER_BUILTINS.iter().any(|(name, _, _)| *name == other) => {
            match_binder_call(*span, other, args)
        }
        // `mkApp`-family: head function followed by `arity` argument sub-terms.
        other => MK_APP_BUILTINS
            .iter()
            .find(|(name, _)| *name == other)
            .filter(|(_, arity)| args.len() == arity + 1)
            .map(|_| Builtin::App {
                span: *span,
                func: &args[0].expr,
                args: args[1..].iter().map(|a| &a.expr).collect(),
            }),
    }
}

/// Classify a binder builtin call (`head` is known to be one of
/// [`BINDER_BUILTINS`]).
///
/// Accepts the 3-argument `(name, type, body)` shape and the 4-argument shape
/// with a dropped `BinderInfo` (trailing for `Expr.lam`/`Expr.forallE`, 2nd for
/// `mkLambda`/`mkForall`). The name slot must be a `` `x `` name literal; any
/// other arity or a non-literal name defers (`None`) so the mis-shaped call
/// falls through and fails honestly.
fn match_binder_call<'e>(
    span: clean_parser::Span,
    head: &str,
    args: &'e [SurfaceArg],
) -> Option<Builtin<'e>> {
    let &(_, form, info_slot) = BINDER_BUILTINS.iter().find(|(name, _, _)| *name == head)?;

    // Resolve the (name, type, body) positions for the supported arities. The
    // dropped `BinderInfo` position depends on the builtin family.
    let (name_arg, ty_arg, body_arg) = match (args.len(), info_slot) {
        // No `BinderInfo`: `(name, type, body)`.
        (3, _) => (&args[0], &args[1], &args[2]),
        // `Expr.lam`/`Expr.forallE`: `(name, type, body, binderInfo)` — drop the
        // trailing `BinderInfo`.
        (4, BinderInfoSlot::Last) => (&args[0], &args[1], &args[2]),
        // `mkLambda`/`mkForall`: `(name, binderInfo, type, body)` — drop the 2nd.
        (4, BinderInfoSlot::Second) => (&args[0], &args[2], &args[3]),
        _ => return None,
    };

    let name = name_literal(&name_arg.expr)?;
    Some(Builtin::Binder {
        span,
        form,
        name,
        ty: &ty_arg.expr,
        body: &body_arg.expr,
    })
}

/// Lower a classified builtin into the equivalent ordinary surface expression,
/// recursively rewriting its argument sub-terms (so nested builtins collapse).
fn lower_builtin(builtin: Builtin<'_>, changed: &mut bool) -> SurfaceExpr {
    match builtin {
        Builtin::Const { span, name } => SurfaceExpr::Ident(span, name),
        Builtin::App { span, func, args } => SurfaceExpr::App(
            span,
            Box::new(rewrite(func, changed)),
            args.into_iter()
                .map(|a| SurfaceArg::positional(rewrite(a, changed)))
                .collect(),
        ),
        Builtin::Binder {
            span,
            form,
            name,
            ty,
            body,
        } => {
            // The binder type and body are ordinary sub-terms: rewrite them so a
            // nested constructor builtin (e.g. `` mkConst `Nat ``) collapses.
            let binder = SurfaceBinder::new(
                name,
                Some(rewrite(ty, changed)),
                SurfaceBinderInfo::Explicit,
            );
            let body = Box::new(rewrite(body, changed));
            match form {
                BinderForm::Lambda => SurfaceExpr::Lambda(span, vec![binder], body),
                BinderForm::Forall => SurfaceExpr::Pi(span, vec![binder], body),
            }
        }
    }
}

/// Extract the head identifier of a builtin call: either a bare `Ident` (e.g.
/// `mkApp`) or a qualified `Expr.const`/`Expr.app` projection rendered as the
/// dotted string `"Expr.const"`.
fn builtin_head_name(func: &SurfaceExpr) -> Option<String> {
    match func {
        SurfaceExpr::Ident(_, name) => Some(name.clone()),
        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
            let SurfaceExpr::Ident(_, base_name) = base.as_ref() else {
                return None;
            };
            Some(format!("{base_name}.{field}"))
        }
        _ => None,
    }
}

/// Extract the name carried by a name-literal argument. `mkConst`/`Expr.const`
/// take a `` `Name `` syntax-quote literal; we accept that shape only, so a
/// non-literal first argument defers (returns `None`) rather than guessing.
fn name_literal(expr: &SurfaceExpr) -> Option<String> {
    match expr {
        SurfaceExpr::SyntaxQuote(_, name) => Some(name.clone()),
        SurfaceExpr::Paren(_, inner) => name_literal(inner),
        _ => None,
    }
}

#[cfg(test)]
#[path = "meta_builtin_tests.rs"]
mod tests;
