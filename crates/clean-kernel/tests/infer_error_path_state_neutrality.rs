// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression: `infer_type` must be STATE-NEUTRAL on the error path.
//!
//! Each binder arm (Lam / Pi / Let) pushes an FVar onto the checker's local
//! context, infers the body, then pops. Until 2026-07-25 the `?` on the body
//! result fired BEFORE `ctx_pop()`, so any `Err` left the binder's FVar in
//! `self.ctx` permanently. Sites: `tc/infer.rs` Lam/Pi/Let (the release
//! `infer_type_fast_impl` path) and `tc/cert/infer_core.rs` +
//! `tc/cert/infer_modes.rs` (the debug certificate path) — i.e. BOTH build
//! profiles leaked, which is why this test is profile-agnostic.
//!
//! Why it matters beyond tidiness:
//!   * `can_cache` is `self.ctx.borrow().is_empty()`, so one leaked entry
//!     silently disables closed-term type caching;
//!   * the `infer_arc_memo` key contains `ctx_len()`, so a leak shifts every
//!     subsequent memo key;
//!   * `clean-elab`'s unifier holds a long-lived `TypeChecker`, swallows infer
//!     errors (`tc.infer_type(expr).ok()?`) and never calls
//!     `reset_local_context()`, so leaks accumulate there for its whole lifetime
//!     and its `push_binder_local` / `pop_binder_local` pairing then pops the
//!     leaked entry (LIFO) instead of its own binder.
//!   * a correspondence proof cannot treat `ctx` as a pure parameter while
//!     errors mutate it — which makes this a prerequisite for certifying the
//!     spine, not just a cleanliness fix.
//!
//! `reset_local_context`'s own doc comment describes this exact defect as its
//! reason to exist, and `clean-olean` calls it per declaration — a call-site
//! workaround. This test removes the need for the workaround at the source.

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};

/// `fun (x : Prop) => x x` — well-formed syntax, ill-typed body (`x` applied to
/// itself where `x : Prop` is not a function). Inference must fail INSIDE the
/// Lam body, i.e. after the binder FVar has been pushed.
fn ill_typed_lam() -> Expr {
    let prop = Expr::sort(Level::zero());
    let x = Expr::bvar(0);
    Expr::lam(BinderInfo::Default, prop, Expr::app(x.clone(), x))
}

/// `(x : Prop) -> x x` — same shape in a Pi binder.
fn ill_typed_pi() -> Expr {
    let prop = Expr::sort(Level::zero());
    let x = Expr::bvar(0);
    Expr::pi(BinderInfo::Default, prop, Expr::app(x.clone(), x))
}

/// `let x : Type := Prop; x x` — same shape in a Let binder.
fn ill_typed_let() -> Expr {
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let prop = Expr::sort(Level::zero());
    let x = Expr::bvar(0);
    Expr::let_named(Name::anon(), type0, prop, Expr::app(x.clone(), x), false)
}

fn assert_neutral(label: &str, term: Expr) {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert_eq!(
        tc.local_context_len(),
        0,
        "{label}: precondition — a fresh TypeChecker must start with an empty local context"
    );

    let result = tc.infer_type(&term);
    assert!(
        result.is_err(),
        "{label}: fixture must FAIL to type-check, otherwise this test proves nothing \
         (got {:?})",
        result.map(|t| format!("{t:?}"))
    );

    assert_eq!(
        tc.local_context_len(),
        0,
        "{label}: LEAK — inference errored inside the binder body and left {} entr(ies) in \
         the local context. The binder arm must `ctx_pop()` BEFORE the `?` on the body \
         result. This silently disables closed-term type caching (`can_cache` is \
         `ctx.is_empty()`) and shifts every `infer_arc_memo` key (which contains \
         `ctx_len()`).",
        tc.local_context_len()
    );
}

#[test]
fn lam_error_path_leaves_local_context_empty() {
    assert_neutral("Lam", ill_typed_lam());
}

#[test]
fn pi_error_path_leaves_local_context_empty() {
    assert_neutral("Pi", ill_typed_pi());
}

#[test]
fn let_error_path_leaves_local_context_empty() {
    assert_neutral("Let", ill_typed_let());
}

/// Nested binders leak one entry PER enclosing frame, so a single-frame test
/// could pass while deeper nesting still leaked.
#[test]
fn nested_binder_error_path_leaves_local_context_empty() {
    let prop = Expr::sort(Level::zero());
    let inner = ill_typed_lam();
    let nested = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::lam(BinderInfo::Default, prop, inner),
    );
    assert_neutral("nested Lam/Lam/Lam", nested);
}

/// The success path must also be neutral — guards against a "fix" that pops
/// twice, which would underflow the context or drop a caller's entry.
#[test]
fn success_path_leaves_local_context_empty() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // fun (x : Prop) => x   ⊢   Prop -> Prop
    let identity = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::bvar(0),
    );
    let _inferred = tc
        .infer_type(&identity)
        .expect("fun (x : Prop) => x must type-check");
    assert_eq!(
        tc.local_context_len(),
        0,
        "success path must also leave the local context empty"
    );
}
