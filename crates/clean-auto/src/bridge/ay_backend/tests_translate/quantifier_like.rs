// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Iff and Exists translation tests (Part of #2257).

use super::support::{build_exists_nat, build_iff_expr};
use super::*;
use clean_kernel::Expr;

/// Test that Iff(a, a) is provable (tautology: a ↔ a)
#[test]
fn test_iff_self_is_tautology() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let a_id = FVarId::new(100);
    backend.register_fvar_bool(a_id);
    let a = Expr::fvar(a_id);

    let goal = build_iff_expr(a.clone(), a);
    let result = backend
        .prove(&goal)
        .expect("Iff translation should succeed");
    assert!(result, "a ↔ a should be provable");
}

/// Test that Iff(True, False) is not provable
#[test]
fn test_iff_true_false_unprovable() {
    use clean_kernel::name::Name;
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let t = Expr::const_(Name::from_string("True"), vec![]);
    let f = Expr::const_(Name::from_string("False"), vec![]);

    let goal = build_iff_expr(t, f);
    let result = backend
        .prove(&goal)
        .expect("Iff translation should succeed");
    assert!(!result, "True ↔ False should not be provable");
}

/// Test that Iff decomposes correctly: (a ∧ b) ↔ (b ∧ a)
#[test]
fn test_iff_and_commutativity() {
    use clean_kernel::name::Name;
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let a_id = FVarId::new(100);
    let b_id = FVarId::new(200);
    backend.register_fvar_bool(a_id);
    backend.register_fvar_bool(b_id);
    let a = Expr::fvar(a_id);
    let b = Expr::fvar(b_id);

    let and_ab = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a.clone()),
        b.clone(),
    );
    let and_ba = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), b),
        a,
    );

    let goal = build_iff_expr(and_ab, and_ba);
    let result = backend
        .prove(&goal)
        .expect("Iff translation should succeed");
    assert!(result, "(a ∧ b) ↔ (b ∧ a) should be provable");
}

/// Test that ∃n. n = 5 translates and Skolemizes correctly.
///
/// Skolemization of `∃n. n = 5` produces `sk = 5`. When asserted as a
/// hypothesis (direct translation), this constrains sk to 5. We verify
/// by asserting the Skolemized form and checking that the conjunction
/// with `sk ≥ 0` is SAT.
///
/// Note: Skolemization is equisatisfiable, not equivalent under negation.
/// `prove()` would negate first, making `not(sk = 5)` trivially SAT.
/// The correct use is asserting existential hypotheses directly.
#[test]
fn test_exists_skolemization_satisfiable() {
    use clean_kernel::level::Level;
    use clean_kernel::name::Name;
    let mut backend = AyBackend::new(AyLogic::QfLia);

    // Body: BVar(0) = 5 (bound variable = 5)
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![Level::zero()]);
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::app(
        Expr::app(Expr::app(eq_const, nat_ty), Expr::bvar(0)),
        Expr::nat_lit(5),
    );
    let exists_expr = build_exists_nat(body);

    // Translate: Skolemizes to `sk_exists_N = 5`
    let term = backend
        .translate_expr(&exists_expr)
        .expect("Exists translation should succeed");

    // Assert the Skolemized hypothesis and check satisfiability
    backend.assert_term(term);
    assert_eq!(
        backend.check_sat(),
        AySolveResult::Sat,
        "∃n. n = 5 asserted as hypothesis should be SAT (sk = 5)"
    );
}

/// A real Lean constant named `sk_exists_0` in the body must fail closed
/// as an unsupported constant, not silently alias the synthesized witness.
/// Part of #2848.
#[test]
fn test_exists_body_constant_named_sk_exists_fails_closed() {
    use clean_kernel::level::Level;
    use clean_kernel::name::Name;
    let mut backend = AyBackend::new(AyLogic::QfLia);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![Level::zero()]);
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    // Body: Eq Nat BVar(0) (Const "sk_exists_0")
    // The body-side sk_exists_0 is a real Lean constant.
    let body = Expr::app(
        Expr::app(Expr::app(eq_const, nat_ty.clone()), Expr::bvar(0)),
        Expr::const_(Name::from_string("sk_exists_0"), vec![]),
    );
    let exists_expr = build_exists_nat(body);

    let result = backend.translate_expr(&exists_expr);
    assert!(
        result.is_err(),
        "body constant named sk_exists_0 must fail closed, not alias the witness"
    );
}

/// Test that ∃n. n = 5 ∧ n = 6 is not provable (contradictory)
#[test]
fn test_exists_skolemization_contradictory() {
    use clean_kernel::level::Level;
    use clean_kernel::name::Name;
    let mut backend = AyBackend::new(AyLogic::QfLia);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![Level::zero()]);
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

    // BVar(0) = 5
    let eq5 = Expr::app(
        Expr::app(Expr::app(eq_const.clone(), nat_ty.clone()), Expr::bvar(0)),
        Expr::nat_lit(5),
    );
    // BVar(0) = 6
    let eq6 = Expr::app(
        Expr::app(Expr::app(eq_const, nat_ty), Expr::bvar(0)),
        Expr::nat_lit(6),
    );
    // And(eq5, eq6)
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let body = Expr::app(Expr::app(and_const, eq5), eq6);

    let goal = build_exists_nat(body);

    let result = backend
        .prove(&goal)
        .expect("Exists translation should succeed");
    assert!(
        !result,
        "∃n. n = 5 ∧ n = 6 should not be provable (contradictory)"
    );
}

// -- Domain-mismatch rejection regressions (#2849) --

/// `Exists UInt8 ...` must be rejected before witness declaration (#2849 AC4).
#[test]
fn test_exists_uint8_binder_rejected() {
    use clean_kernel::level::Level;
    use clean_kernel::name::Name;

    let mut backend = AyBackend::new(AyLogic::QfLia);
    let uint8_ty = Expr::const_(Name::from_string("UInt8"), vec![Level::zero()]);
    let body = Expr::bvar(0); // trivial body — rejection is on the binder type
    let exists = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            uint8_ty.clone(),
        ),
        Expr::lam(clean_kernel::BinderInfo::Default, uint8_ty, body),
    );
    let result = backend.translate_expr(&exists);
    assert!(
        result.is_err(),
        "Exists UInt8 must be rejected, not widened to Int"
    );
}

/// `Exists Float ...` must be rejected before witness declaration (#2849 AC4).
#[test]
fn test_exists_float_binder_rejected() {
    use clean_kernel::level::Level;
    use clean_kernel::name::Name;

    let mut backend = AyBackend::new(AyLogic::QfLra);
    let float_ty = Expr::const_(Name::from_string("Float"), vec![Level::zero()]);
    let body = Expr::bvar(0);
    let exists = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            float_ty.clone(),
        ),
        Expr::lam(clean_kernel::BinderInfo::Default, float_ty, body),
    );
    let result = backend.translate_expr(&exists);
    assert!(
        result.is_err(),
        "Exists Float must be rejected, not widened to Real"
    );
}
