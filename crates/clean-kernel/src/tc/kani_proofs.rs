// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kani bounded model checking harnesses for type checker module.
//!
//! Verify safety properties for all inputs up to a bound.
//!
//! Run with: cargo kani --features kani -p clean-kernel
//!
//! ## Design Note: Example-Based vs Symbolic Testing
//!
//! Some harnesses (verify_def_eq_reflexivity, verify_def_eq_symmetry, verify_whnf_idempotent)
//! use **example-based testing** rather than `kani::any()` for the `Expr` type. This is
//! intentional because:
//!
//! 1. **State explosion**: Expr is a deeply recursive enum with 12 variants. Full symbolic
//!    execution would require unbounded recursion or prohibitive unwind bounds.
//!
//! 2. **Arbitrary::arbitrary for Expr**: Implementing `kani::Arbitrary` for Expr would
//!    generate syntactically valid but semantically meaningless expressions (e.g., apps
//!    with wrong arity, lambdas with mismatched types).
//!
//! 3. **Environment dependencies**: Many Expr variants (Const, Proj) require a populated
//!    Environment to be meaningful. Symbolic testing would need to also generate valid
//!    environments.
//!
//! The example-based harnesses instead verify key properties on a representative sample:
//! - Sort/Type (base cases)
//! - BVar (de Bruijn indices)
//! - Lambda/Pi (binders)
//! - App (application/beta reduction)
//! - Let (let-bindings)
//!
//! For truly symbolic verification of Expr properties, consider using the lean4lean
//! formalization which proves these properties for all expressions via dependent types.
//!
//! See: level.rs and name.rs kani_proofs modules for examples of successful symbolic
//! testing on simpler types.

use super::*;
use crate::expr::BinderData;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Kani drop workaround for Arc<Name> unwinding
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// Expr, Name, and Level contain recursive Arc<Name> that cause CBMC
// to generate unbounded drop unwinding. Leak all values to prevent this.
// Sound for functional verification: we verify value semantics, not deallocation.

fn leak_expr(e: Expr) {
    std::mem::forget(e);
}
fn leak_name(n: Name) {
    std::mem::forget(n);
}

/// Verify push/pop are inverses for LocalContext.
#[kani::proof]
#[kani::unwind(4)]
fn verify_local_context_push_pop() {
    let mut ctx = LocalContext::new();

    // Initial state
    let initial_len = ctx.len();
    assert!(initial_len == 0, "New context should be empty");

    // Push a binding
    let name = Name::anon().num(1);
    let type_ = Expr::prop();
    let bi = BinderInfo::Default;

    let id = ctx.push(name.clone(), type_.clone(), bi);

    // After push, len should increase
    assert_eq!(ctx.len(), initial_len + 1, "Push should increase length");

    // Pop should return what we pushed
    let decl = ctx.pop().expect("Pop on non-empty context should succeed");
    assert_eq!(decl.id, id, "Popped id should match pushed id");
    assert_eq!(decl.name, name, "Popped name should match pushed name");
    assert_eq!(decl.type_, type_, "Popped type should match pushed type");

    // After pop, we should be back to initial length
    assert_eq!(ctx.len(), initial_len, "Pop should restore length");
    leak_name(decl.name);
    leak_expr(decl.type_);
    leak_name(name);
    leak_expr(type_);
    std::mem::forget(ctx);
}

/// Verify lookup finds pushed entries.
#[kani::proof]
fn verify_local_context_lookup() {
    let mut ctx = LocalContext::new();

    // Push a binding
    let name = Name::anon().num(2);
    let type_ = Expr::type_();
    let bi = BinderInfo::Implicit;

    let id = ctx.push(name.clone(), type_.clone(), bi);

    // Lookup should find it
    let decl = ctx.get(id).expect("Lookup should find pushed entry");
    assert_eq!(decl.id, id);
    assert_eq!(decl.name, name);
    assert_eq!(decl.type_, type_);
    assert_eq!(decl.bi, BinderData::from(bi));

    // Lookup with different ID should fail
    let other_id = FVarId(999);
    let not_found = ctx.get(other_id);
    assert!(
        not_found.is_none(),
        "Lookup of unknown id should return None"
    );
    leak_name(name);
    leak_expr(type_);
    std::mem::forget(ctx);
}

/// Verify is_def_eq reflexivity: is_def_eq(e, e) == true.
///
/// Note: Uses example-based testing with representative Expr variants rather than
/// `kani::any()`. See module doc for rationale (Expr state explosion).
#[kani::proof]
fn verify_def_eq_reflexivity() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let prop = Expr::prop();
    assert!(tc.is_def_eq(&prop, &prop), "def_eq(Prop, Prop)");

    let type_ = Expr::type_();
    assert!(tc.is_def_eq(&type_, &type_), "def_eq(Type, Type)");

    let bvar = Expr::from_kind(ExprKind::BVar(0));
    assert!(tc.is_def_eq(&bvar, &bvar), "def_eq(BVar, BVar)");

    let lam = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    assert!(tc.is_def_eq(&lam, &lam), "def_eq(lam, lam)");

    let pi = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());
    assert!(tc.is_def_eq(&pi, &pi), "def_eq(Pi, Pi)");

    let app = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
        Expr::prop(),
    );
    assert!(tc.is_def_eq(&app, &app), "def_eq(App, App)");
    leak_expr(prop);
    leak_expr(type_);
    leak_expr(lam);
    leak_expr(pi);
    leak_expr(app);
    std::mem::forget(tc);
    std::mem::forget(env);
}

/// Verify is_def_eq symmetry: is_def_eq(a, b) == is_def_eq(b, a).
///
/// Note: Uses example-based testing with representative Expr variants rather than
/// `kani::any()`. See module doc for rationale (Expr state explosion).
#[kani::proof]
fn verify_def_eq_symmetry() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let prop = Expr::prop();
    let type_ = Expr::type_();
    let ab = tc.is_def_eq(&prop, &type_);
    let ba = tc.is_def_eq(&type_, &prop);
    assert_eq!(ab, ba, "symmetry: def_eq(a,b) == def_eq(b,a)");

    let lam1 = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let lam2 = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let ab = tc.is_def_eq(&lam1, &lam2);
    let ba = tc.is_def_eq(&lam2, &lam1);
    assert_eq!(ab, ba, "symmetry for lambdas");
    leak_expr(prop);
    leak_expr(type_);
    leak_expr(lam1);
    leak_expr(lam2);
    std::mem::forget(tc);
    std::mem::forget(env);
}

/// Verify is_def_eq transitivity: is_def_eq(a, b) ∧ is_def_eq(b, c) ⟹ is_def_eq(a, c).
///
/// Note: Uses example-based testing with representative Expr variants rather than
/// `kani::any()`. See module doc for rationale (Expr state explosion).
///
/// Each test case uses expressions that are definitionally equal through different
/// reduction mechanisms, so transitivity is genuinely exercised:
/// - let-reduction: `let x := e in x` → e
/// - beta-reduction: `(λx:T . x) e` → e
/// - direct structural equality
#[kani::proof]
fn verify_def_eq_transitivity() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Case 1: a = let _ : Type := Prop in #0, b = Prop, c = (λ _ : Type . #0) Prop
    // a ≡ b via let-reduction, b ≡ c via beta-reduction
    let a = Expr::let_named(
        Name::anon(),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
        false,
    );
    let b = Expr::prop();
    let c = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
        Expr::prop(),
    );

    let ab = tc.is_def_eq(&a, &b);
    let bc = tc.is_def_eq(&b, &c);
    assert!(ab, "let _ := Prop in #0 should be def_eq to Prop");
    assert!(bc, "(λ _ : Type . #0) Prop should be def_eq to Prop");
    let ac = tc.is_def_eq(&a, &c);
    assert!(ac, "transitivity: let-reduced ≡ beta-reduced");

    // Case 2: a = let _ : Type := Type in #0, b = Type, c = Type
    // a ≡ b via let-reduction, b ≡ c structurally
    let a2 = Expr::let_named(
        Name::anon(),
        Expr::type_(),
        Expr::type_(),
        Expr::bvar(0),
        false,
    );
    let b2 = Expr::type_();
    let c2 = Expr::type_();

    let ab2 = tc.is_def_eq(&a2, &b2);
    let bc2 = tc.is_def_eq(&b2, &c2);
    assert!(ab2, "let _ := Type in #0 should be def_eq to Type");
    assert!(bc2, "Type ≡ Type structurally");
    let ac2 = tc.is_def_eq(&a2, &c2);
    assert!(ac2, "transitivity: let-reduced ≡ structural");

    // Case 3: reverse direction — a via beta, b direct, c via let
    let a3 = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
        Expr::prop(),
    );
    let b3 = Expr::prop();
    let c3 = Expr::let_named(
        Name::anon(),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
        false,
    );

    let ab3 = tc.is_def_eq(&a3, &b3);
    let bc3 = tc.is_def_eq(&b3, &c3);
    assert!(ab3, "(λ _ : Prop . #0) Prop should be def_eq to Prop");
    assert!(bc3, "Prop ≡ let _ := Prop in #0");
    let ac3 = tc.is_def_eq(&a3, &c3);
    assert!(ac3, "transitivity: beta-reduced ≡ let-reduced");

    // Leak all to prevent CBMC drop unwinding
    leak_expr(a);
    leak_expr(b);
    leak_expr(c);
    leak_expr(a2);
    leak_expr(b2);
    leak_expr(c2);
    leak_expr(a3);
    leak_expr(b3);
    leak_expr(c3);
    std::mem::forget(tc);
    std::mem::forget(env);
}

/// Verify WHNF idempotence: whnf(whnf(e)) == whnf(e).
///
/// Note: Uses example-based testing with representative Expr variants rather than
/// `kani::any()`. See module doc for rationale (Expr state explosion).
#[kani::proof]
fn verify_whnf_idempotent() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let prop = Expr::prop();
    let whnf1 = tc.whnf(&prop);
    let whnf2 = tc.whnf(&whnf1);
    assert_eq!(whnf1, whnf2, "WHNF idempotent for Prop");

    let type_ = Expr::type_();
    let whnf1 = tc.whnf(&type_);
    let whnf2 = tc.whnf(&whnf1);
    assert_eq!(whnf1, whnf2, "WHNF idempotent for Type");

    let lam = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let whnf1 = tc.whnf(&lam);
    let whnf2 = tc.whnf(&whnf1);
    assert_eq!(whnf1, whnf2, "WHNF idempotent for lambda");

    let beta = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
        Expr::prop(),
    );
    let whnf1 = tc.whnf(&beta);
    let whnf2 = tc.whnf(&whnf1);
    assert_eq!(whnf1, whnf2, "WHNF idempotent for beta redex");

    let let_expr = Expr::let_named(
        Name::anon(),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
        false,
    );
    let whnf1 = tc.whnf(&let_expr);
    let whnf2 = tc.whnf(&whnf1);
    assert_eq!(whnf1, whnf2, "WHNF idempotent for let");
    // Leak all to prevent CBMC drop unwinding
    leak_expr(prop);
    leak_expr(type_);
    leak_expr(lam);
    leak_expr(beta);
    leak_expr(let_expr);
    leak_expr(whnf1);
    leak_expr(whnf2);
    std::mem::forget(tc);
    std::mem::forget(env);
}
