// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Course-of-values recursion via a pair-threading (accumulator) transform.
//!
//! Lean lowers a two-back recurrence such as
//!
//! ```text
//! def fib : Nat → Nat
//!   | 0     => 0
//!   | 1     => 1
//!   | n + 2 => fib (n + 1) + fib n
//! ```
//!
//! through `Nat.brecOn` / `Nat.below`, which memoizes *every* prior value.
//! Wiring `brecOn`/`below` into the equation compiler, IH resolution, and a new
//! `to_lcnf` lowering is deep. This module takes the tractable route instead: it
//! recognizes the two-prior (`n + 2`) shape *at the surface level* and rewrites
//! it into the textbook fast-`fib` pair-threading form that the **existing**
//! single-step `Nat.rec` lowering (#20) and `Prod` matchers (#21) already
//! handle:
//!
//! ```text
//! def fibAux : Nat → Nat × Nat            -- fibAux k = (fib k, fib (k+1))
//!   | 0     => (0, 1)
//!   | k + 1 => match fibAux k with | (a, b) => (b, a + b)
//! def fib (n : Nat) : Nat := Prod.fst (fibAux n)
//! ```
//!
//! `fibAux` recurses only on the *immediate* predecessor (a bare-`Ident`
//! decreasing self-call), so it elaborates through `elaborate_rec_arm`'s working
//! `k == 1` path and lowers through `lower_nat_rec`. No new kernel/IR machinery
//! and no `add_decl_unchecked` — both emitted declarations are ordinary `def`s
//! that the kernel re-checks.
//!
//! SCOPE: the named milestone — a single-argument `def f : Nat → R` whose arms
//! are exactly a `0` base case, a `1` base case, and one `n + 2` recursive arm
//! whose body uses the two immediate prior values `f (n + 1)` and `f n`. Any
//! other shape returns `None` and leaves every existing path byte-for-byte
//! unchanged (in particular the `n + k`, `k > 1` guard in `match_arms.rs` stays
//! as a defensive fail-closed for shapes this transform does not rewrite).

use clean_parser::{
    Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr, SurfaceLit, SurfaceMatchArm,
    SurfacePattern,
};

/// The two declarations the pair-threading transform produces from one
/// course-of-values `def`: the single-step pair-threading auxiliary and the
/// projecting wrapper that keeps the original surface name.
pub(super) struct PairThreaded {
    /// Auxiliary name (`<f>.cov` — a dotted name a user cannot collide with via
    /// a plain identifier, and which is namespaced under the function).
    pub aux_name: String,
    /// Auxiliary type: `Nat → R × R`.
    pub aux_ty: SurfaceExpr,
    /// Auxiliary value: the single-step pair-threading `PatternMatchLambda`.
    pub aux_val: SurfaceExpr,
    /// Wrapper return type `R` (the codomain of the original `Nat → R`).
    pub wrapper_ret_ty: SurfaceExpr,
    /// Wrapper value: `fun (n : Nat) => Prod.fst (<aux_name> n)`.
    pub wrapper_val: SurfaceExpr,
}

/// Recognize the two-prior course-of-values shape and, if matched, build the
/// pair-threading auxiliary + projecting wrapper. Returns `None` for every other
/// declaration shape, leaving the caller's existing path untouched.
///
/// `name` is the (unqualified) function name; `binders` must be empty (the
/// equation-def parser emits the single argument as the synthetic `_x` lambda
/// binder inside `val`, not as a declaration binder); `ty` must be `Nat → R`.
pub(super) fn try_pair_thread(
    name: &str,
    binders: &[SurfaceBinder],
    ty: Option<&SurfaceExpr>,
    val: &SurfaceExpr,
) -> Option<PairThreaded> {
    // Leading declaration binders would change the decreasing-argument position
    // and the wrapper signature; the milestone is the binder-free equation def.
    if !binders.is_empty() {
        return None;
    }

    // The codomain `R` of `Nat → R`. Only a non-dependent arrow whose domain is
    // `Nat` qualifies — a dependent `Pi` return type cannot be paired soundly
    // (the two prior values would inhabit different types).
    let ret_ty = match ty? {
        SurfaceExpr::Arrow(_, from, to) if is_nat_ident(from) => (**to).clone(),
        _ => return None,
    };

    // The equation def parses as `PatternMatchLambda([_x], Match(_x, arms))`.
    let SurfaceExpr::PatternMatchLambda(_, lam_binders, lam_body) = val else {
        return None;
    };
    let [lam_binder] = lam_binders.as_slice() else {
        return None;
    };
    if lam_binder.name != "_x" {
        return None;
    }
    let SurfaceExpr::Match(_, None, scrut, arms) = &**lam_body else {
        return None;
    };
    if !matches!(&**scrut, SurfaceExpr::Ident(_, s) if s == "_x") {
        return None;
    }

    // Exactly three arms: base `0`, base `1`, recursive `n + 2`.
    let [arm0, arm1, arm_rec] = arms.as_slice() else {
        return None;
    };
    let base0 = nat_lit_arm_body(arm0, 0)?;
    let base1 = nat_lit_arm_body(arm1, 1)?;

    // The recursive arm must be `n + 2 => <body>` binding a single variable `n`.
    let (pvar, rbody) = match &arm_rec.pattern {
        SurfacePattern::NumeralAdd(inner, 2) => match inner.as_ref() {
            SurfacePattern::Var(v) => (v.clone(), arm_rec.body.clone()),
            _ => return None,
        },
        _ => return None,
    };

    // The recursive body must genuinely recurse on `name`; otherwise this is not
    // a course-of-values def and the ordinary paths handle it.
    if !body_calls(&rbody, name) {
        return None;
    }

    // Rewrite the recursive body for the pair-threading minor. Inside
    // `fibAux (k+1) = match fibAux k with | (a, b) => (b, <rbody'>)` the binding
    // is `a = f k` (== `f n`) and `b = f (k+1)` (== `f (n+1)`), and the surface
    // variable `n` becomes the recursion variable `k`. We substitute, in `rbody`:
    //   * `f (n + 1)`  →  `b`
    //   * `f n`        →  `a`
    //   * bare `n`     →  `k`
    // Any *other* self-call shape (e.g. `f (n + 2)`, `f 0`) is outside the
    // two-prior envelope; `rewrite_rec_body` returns `None` so we bail rather
    // than emit a term that drops a recursive call.
    let a_name = "_cov_a";
    let b_name = "_cov_b";
    let k_name = "_cov_k";
    let rbody2 = rewrite_rec_body(&rbody, name, &pvar, a_name, b_name, k_name)?;

    // ---- Build `aux_ty = Nat → R × R` ----
    let prod_ret = prod_ty(ret_ty.clone(), ret_ty.clone());
    let aux_ty = SurfaceExpr::Arrow(
        Span::dummy(),
        Box::new(nat_ident()),
        Box::new(prod_ret.clone()),
    );

    // ---- Build `aux_val` as a `PatternMatchLambda([_x], Match(_x, [..]))` ----
    // Arm `0 => (base0, base1)`.
    let aux_arm0 = SurfaceMatchArm {
        span: Span::dummy(),
        pattern: SurfacePattern::Lit(SurfaceLit::Nat(0)),
        body: prod_mk(base0, base1),
    };
    // Arm `k + 1 => match <aux> k with | (a, b) => (b, rbody')`.
    let aux_self_call = app(
        SurfaceExpr::Ident(Span::dummy(), aux_name_of(name)),
        vec![SurfaceExpr::Ident(Span::dummy(), k_name.to_string())],
    );
    let pair_pattern = SurfacePattern::Ctor(
        "Prod.mk".to_string(),
        vec![
            SurfacePattern::Var(a_name.to_string()),
            SurfacePattern::Var(b_name.to_string()),
        ],
    );
    let next_pair = prod_mk(
        SurfaceExpr::Ident(Span::dummy(), b_name.to_string()),
        rbody2,
    );
    let inner_match = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(aux_self_call),
        vec![SurfaceMatchArm {
            span: Span::dummy(),
            pattern: pair_pattern,
            body: next_pair,
        }],
    );
    let aux_arm_succ = SurfaceMatchArm {
        span: Span::dummy(),
        pattern: SurfacePattern::NumeralAdd(Box::new(SurfacePattern::Var(k_name.to_string())), 1),
        body: inner_match,
    };
    let aux_match = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(Span::dummy(), "_x".to_string())),
        vec![aux_arm0, aux_arm_succ],
    );
    let aux_val = SurfaceExpr::PatternMatchLambda(
        Span::dummy(),
        vec![SurfaceBinder::new(
            "_x".to_string(),
            None,
            SurfaceBinderInfo::Explicit,
        )],
        Box::new(aux_match),
    );

    // ---- Build wrapper `fun (n : Nat) => Prod.fst (<aux> n)` ----
    let wrapper_param = "_cov_n";
    let wrapper_body = app(
        SurfaceExpr::Ident(Span::dummy(), "Prod.fst".to_string()),
        vec![app(
            SurfaceExpr::Ident(Span::dummy(), aux_name_of(name)),
            vec![SurfaceExpr::Ident(Span::dummy(), wrapper_param.to_string())],
        )],
    );
    let wrapper_val = SurfaceExpr::Lambda(
        Span::dummy(),
        vec![SurfaceBinder::new(
            wrapper_param.to_string(),
            Some(nat_ident()),
            SurfaceBinderInfo::Explicit,
        )],
        Box::new(wrapper_body),
    );

    Some(PairThreaded {
        aux_name: aux_name_of(name),
        aux_ty,
        aux_val,
        wrapper_ret_ty: ret_ty,
        wrapper_val,
    })
}

/// The auxiliary name for `f`: `f.cov`. Dotted so it never collides with a
/// user-written identifier and reads as "course-of-values helper of `f`".
fn aux_name_of(name: &str) -> String {
    format!("{name}.cov")
}

/// `Nat` as a surface identifier.
fn nat_ident() -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), "Nat".to_string())
}

/// Whether `e` is the bare `Nat` identifier (the only domain the transform
/// accepts).
fn is_nat_ident(e: &SurfaceExpr) -> bool {
    matches!(e, SurfaceExpr::Ident(_, s) if s == "Nat")
}

/// `A × B` as the parser renders it: `App(Ident "Prod", [A, B])`.
fn prod_ty(a: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
    app(
        SurfaceExpr::Ident(Span::dummy(), "Prod".to_string()),
        vec![a, b],
    )
}

/// `(a, b)` as the parser renders it: `App(Ident "Prod.mk", [a, b])`.
fn prod_mk(a: SurfaceExpr, b: SurfaceExpr) -> SurfaceExpr {
    app(
        SurfaceExpr::Ident(Span::dummy(), "Prod.mk".to_string()),
        vec![a, b],
    )
}

/// Build an application `head args...` with positional arguments.
fn app(head: SurfaceExpr, args: Vec<SurfaceExpr>) -> SurfaceExpr {
    SurfaceExpr::App(
        Span::dummy(),
        Box::new(head),
        args.into_iter().map(SurfaceArg::positional).collect(),
    )
}

/// If `arm`'s pattern is the numeral literal `lit` (or, for `0`, `Nat.zero`),
/// return a clone of its body; otherwise `None`.
fn nat_lit_arm_body(arm: &SurfaceMatchArm, lit: u64) -> Option<SurfaceExpr> {
    let matches_pat = match &arm.pattern {
        SurfacePattern::Lit(SurfaceLit::Nat(n)) => *n == lit,
        SurfacePattern::Ctor(name, sub) if lit == 0 && sub.is_empty() => {
            name == "Nat.zero" || name == "Nat.Zero"
        }
        _ => false,
    };
    matches_pat.then(|| arm.body.clone())
}

/// Whether `expr` contains an application whose head is the identifier `name`
/// (a self-call). Conservative structural walk over the surface forms the
/// recursive arm body can take.
pub(super) fn body_calls(expr: &SurfaceExpr, name: &str) -> bool {
    match expr {
        SurfaceExpr::App(_, head, args) => {
            let head_is_self = matches!(&**head, SurfaceExpr::Ident(_, s) if s == name);
            head_is_self || body_calls(head, name) || args.iter().any(|a| body_calls(&a.expr, name))
        }
        SurfaceExpr::Paren(_, inner) => body_calls(inner, name),
        SurfaceExpr::Ascription(_, e, t) => body_calls(e, name) || body_calls(t, name),
        SurfaceExpr::Lambda(_, _, b) | SurfaceExpr::PatternMatchLambda(_, _, b) => {
            body_calls(b, name)
        }
        SurfaceExpr::Let(_, _, v, b) => body_calls(v, name) || body_calls(b, name),
        SurfaceExpr::If(_, c, t, e) => {
            body_calls(c, name) || body_calls(t, name) || body_calls(e, name)
        }
        SurfaceExpr::Match(_, _, s, arms) => {
            body_calls(s, name) || arms.iter().any(|a| body_calls(&a.body, name))
        }
        _ => false,
    }
}

/// Rewrite the `n + 2` recursive arm body into the pair-threading minor body.
///
/// Substitutes, throughout `expr`:
///   * `f (pvar + 1)`  →  `Ident b`   (the second component = `f (k+1)`)
///   * `f pvar`        →  `Ident a`   (the first  component = `f k`)
///   * bare `Ident pvar` →  `Ident k` (the surface var becomes the rec var)
///
/// Returns `None` if a self-call to `f` appears at any *other* offset (anything
/// but the two immediate prior values), so we never silently drop or misroute a
/// recursive call.
fn rewrite_rec_body(
    expr: &SurfaceExpr,
    f: &str,
    pvar: &str,
    a: &str,
    b: &str,
    k: &str,
) -> Option<SurfaceExpr> {
    match expr {
        // A self-call `f <arg>`: only the two recognized offsets are allowed.
        SurfaceExpr::App(_, head, args) if matches!(&**head, SurfaceExpr::Ident(_, s) if s == f) => {
            let [arg] = args.as_slice() else {
                return None;
            };
            match classify_self_arg(&arg.expr, pvar)? {
                SelfArg::Pred => Some(SurfaceExpr::Ident(Span::dummy(), a.to_string())),
                SelfArg::PredPlusOne => Some(SurfaceExpr::Ident(Span::dummy(), b.to_string())),
            }
        }
        // A non-self application: recurse into head and args. Any nested self-call
        // is still validated by the recursive descent.
        SurfaceExpr::App(span, head, args) => {
            let new_head = rewrite_rec_body(head, f, pvar, a, b, k)?;
            let mut new_args = Vec::with_capacity(args.len());
            for arg in args {
                new_args.push(SurfaceArg {
                    span: arg.span,
                    expr: rewrite_rec_body(&arg.expr, f, pvar, a, b, k)?,
                    name: arg.name.clone(),
                });
            }
            Some(SurfaceExpr::App(*span, Box::new(new_head), new_args))
        }
        SurfaceExpr::Paren(span, inner) => Some(SurfaceExpr::Paren(
            *span,
            Box::new(rewrite_rec_body(inner, f, pvar, a, b, k)?),
        )),
        SurfaceExpr::Ascription(span, e, t) => Some(SurfaceExpr::Ascription(
            *span,
            Box::new(rewrite_rec_body(e, f, pvar, a, b, k)?),
            Box::new(rewrite_rec_body(t, f, pvar, a, b, k)?),
        )),
        // Bare reference to the surface recursion variable becomes `k`.
        SurfaceExpr::Ident(span, s) if s == pvar => Some(SurfaceExpr::Ident(*span, k.to_string())),
        // Leaves and other identifiers pass through unchanged. Conservatively, if
        // a self-call to `f` is buried inside a form we do not descend into,
        // `body_calls`-style detection would not catch it — but the recursive arm
        // body for the milestone is a plain arithmetic expression, so the App /
        // Paren / Ascription descent above covers it. Forms that could *hide* a
        // self-call (lambda, let, match, if) are rejected to stay sound.
        SurfaceExpr::Ident(..) | SurfaceExpr::Lit(..) | SurfaceExpr::Hole(_) => Some(expr.clone()),
        SurfaceExpr::Lambda(..)
        | SurfaceExpr::PatternMatchLambda(..)
        | SurfaceExpr::Let(..)
        | SurfaceExpr::LetRec(..)
        | SurfaceExpr::Match(..)
        | SurfaceExpr::If(..)
            if body_calls(expr, f) =>
        {
            // A self-call hidden inside a binder/control form is outside the
            // two-prior envelope this transform can faithfully rewrite.
            None
        }
        other => Some(other.clone()),
    }
}

/// Which prior value a self-call argument selects, relative to `pvar`.
enum SelfArg {
    /// `f pvar` — the value at `n` (== `k`).
    Pred,
    /// `f (pvar + 1)` — the value at `n + 1` (== `k + 1`).
    PredPlusOne,
}

/// Classify a self-call's single argument as one of the two recognized prior
/// offsets, or `None` for any other shape.
fn classify_self_arg(arg: &SurfaceExpr, pvar: &str) -> Option<SelfArg> {
    match arg {
        SurfaceExpr::Paren(_, inner) => classify_self_arg(inner, pvar),
        SurfaceExpr::Ident(_, s) if s == pvar => Some(SelfArg::Pred),
        // `pvar + 1` parses as `App(Ident "HAdd.hAdd", [pvar, 1])`.
        SurfaceExpr::App(_, head, args)
            if matches!(&**head, SurfaceExpr::Ident(_, s)
                if s == "HAdd.hAdd" || s == "Add.add" || s == "Nat.add") =>
        {
            let [lhs, rhs] = args.as_slice() else {
                return None;
            };
            let lhs_is_pvar = matches!(&lhs.expr, SurfaceExpr::Ident(_, s) if s == pvar);
            let rhs_is_one = matches!(&rhs.expr, SurfaceExpr::Lit(_, SurfaceLit::Nat(1)));
            (lhs_is_pvar && rhs_is_one).then_some(SelfArg::PredPlusOne)
        }
        _ => None,
    }
}
