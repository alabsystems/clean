// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Iota reduction tests — extra args forwarding, insufficient args, and
//! recursive semantic preservation.
//!
//! Covers gaps in the iota test suite identified during #1406 RHS-approach audit:
//! - Extra arguments after the major premise are forwarded (inductive.h:113-117)
//! - Insufficient arguments cause `try_iota_reduction` to return `None`
//! - Semantic preservation (is_def_eq) holds for recursive Nat.succ case

use super::support::make_nat_env_and_ref;
use super::*;
use crate::inductive::RecursorArgOrder;

/// Extra arguments after the major premise must be forwarded to the result.
///
/// In Lean 4 (inductive.h:113-117), after applying the RHS to params+motives+
/// minors+fields, any remaining arguments after the major premise are appended.
/// This happens when a recursor is applied to more arguments than required —
/// e.g., `Nat.rec motive z s (succ n) extra₁ extra₂`.
///
/// The result should be: `(s n (Nat.rec motive z s n)) extra₁ extra₂`
///
/// Without the extras forwarding (lines 342-352 of reduction.rs), the extras
/// would be silently dropped, producing an ill-typed term.
#[test]
fn test_iota_reduction_extra_args_forwarded() {
    let (env, nat_ref) = make_nat_env_and_ref();
    let tc = TypeChecker::new(&env);

    // Build Nat.rec at level 1 (returning Nat → Nat)
    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    // motive: λ _:Nat. Nat → Nat  (returns a function type)
    let nat_to_nat = Expr::arrow(nat_ref.clone(), nat_ref.clone());
    let motive = Expr::lam(BinderInfo::Default, nat_ref.clone(), nat_to_nat);
    // zero case: λ x:Nat. x  (identity)
    let zero_case = Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::bvar(0));
    // succ case: λ n:Nat. λ ih:(Nat→Nat). ih
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::arrow(nat_ref.clone(), nat_ref.clone()),
            Expr::bvar(0), // return ih
        ),
    );

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let extra_arg = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Build: Nat.rec motive zero_case succ_case Nat.zero extra_arg
    // This has one extra arg beyond the major premise.
    // Expected: zero_case extra_arg = (λ x. x) extra_arg = extra_arg
    let app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(rec.clone(), motive.clone()), zero_case.clone()),
                succ_case.clone(),
            ),
            zero.clone(),
        ),
        extra_arg.clone(),
    );

    let result = tc.whnf(&app);
    // The extra arg should be forwarded. After iota reduction:
    //   Nat.rec motive zero_case succ_case zero extra_arg
    //   → zero_case extra_arg     (iota: select zero_case, then forward extra)
    //   → (λ x. x) extra_arg     (beta)
    //   → extra_arg               (beta)
    assert_eq!(
        result, extra_arg,
        "Extra arg after major premise must be forwarded: got {:?}",
        result
    );
}

/// Multiple extra args after the major premise are all forwarded in order.
#[test]
fn test_iota_reduction_multiple_extra_args() {
    let (env, nat_ref) = make_nat_env_and_ref();
    let tc = TypeChecker::new(&env);

    // Build Nat.rec at level 1 (returning Nat → Nat → Nat)
    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    // motive: λ _:Nat. Nat → Nat → Nat
    let nat_to_nat_to_nat = Expr::arrow(
        nat_ref.clone(),
        Expr::arrow(nat_ref.clone(), nat_ref.clone()),
    );
    let motive = Expr::lam(BinderInfo::Default, nat_ref.clone(), nat_to_nat_to_nat);
    // zero case: λ a:Nat. λ b:Nat. a  (select first extra arg)
    let zero_case = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::bvar(1)),
    );
    // succ case: λ _:Nat. λ _:(Nat→Nat→Nat). λ a:Nat. λ b:Nat. b (select second)
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::arrow(
                nat_ref.clone(),
                Expr::arrow(nat_ref.clone(), nat_ref.clone()),
            ),
            Expr::lam(
                BinderInfo::Default,
                nat_ref.clone(),
                Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::bvar(0)),
            ),
        ),
    );

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let extra1 = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let extra2 = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Nat.rec motive zero_case succ_case zero extra1 extra2
    // → zero_case extra1 extra2
    // → (λ a b. a) extra1 extra2
    // → extra1
    let app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(rec.clone(), motive.clone()), zero_case),
                    succ_case,
                ),
                zero,
            ),
            extra1.clone(),
        ),
        extra2,
    );

    let result = tc.whnf(&app);
    assert_eq!(
        result, extra1,
        "Multiple extra args must be forwarded in order: got {:?}",
        result
    );
}

/// Insufficient arguments: recursor with too few args returns None (no reduction).
///
/// Nat.rec requires 4 args (motive, zero_case, succ_case, major).
/// Providing only 3 should leave the expression unreduced.
#[test]
fn test_iota_reduction_insufficient_args_no_reduction() {
    let (env, nat_ref) = make_nat_env_and_ref();
    let tc = TypeChecker::new(&env);

    let rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::prop());
    let case_zero = Expr::type_();
    let case_succ = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(1)),
    );

    // Only 3 args (motive, case_zero, case_succ) — missing major premise
    let partial_app = Expr::app(
        Expr::app(Expr::app(rec.clone(), motive.clone()), case_zero),
        case_succ,
    );

    let result = tc.whnf(&partial_app);
    // Should be stuck — no reduction without the major premise
    assert_eq!(
        partial_app, result,
        "Nat.rec with insufficient args must not reduce"
    );
}

/// Even fewer args: just the recursor and motive (2 args, needs 4).
#[test]
fn test_iota_reduction_minimal_args_no_reduction() {
    let (env, nat_ref) = make_nat_env_and_ref();
    let tc = TypeChecker::new(&env);

    let rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::prop());

    // Only 1 arg (motive) — far too few
    let partial_app = Expr::app(rec, motive);
    let result = tc.whnf(&partial_app);
    assert_eq!(
        partial_app, result,
        "Nat.rec with only motive must not reduce"
    );
}

/// Bare recursor constant (0 args) must not reduce.
#[test]
fn test_iota_reduction_bare_recursor_no_reduction() {
    let (env, _nat_ref) = make_nat_env_and_ref();
    let tc = TypeChecker::new(&env);

    let rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let result = tc.whnf(&rec);
    assert_eq!(rec, result, "Bare Nat.rec constant must not reduce");
}

/// Semantic preservation for recursive Nat.succ case.
///
/// Nat.rec motive z s (succ n) should satisfy:
///   is_def_eq(Nat.rec motive z s (succ n), s n (Nat.rec motive z s n))
///
/// This tests the RHS-based reduction for the recursive case where the IH
/// (induction hypothesis) is generated. Existing semantic preservation tests
/// only cover the non-recursive zero case.
#[test]
fn test_iota_semantic_preservation_nat_rec_succ() {
    let (env, nat_ref) = make_nat_env_and_ref();
    let tc = TypeChecker::new(&env);

    let rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::prop());
    let case_zero = Expr::type_();
    // succ_case: λ n:Nat. λ ih:Prop. ih  (identity on IH)
    let case_succ = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
    );
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // Build: Nat.rec motive case_zero case_succ (succ zero)
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec.clone(), motive.clone()), case_zero.clone()),
            case_succ.clone(),
        ),
        one,
    );

    let result = tc.whnf(&app);

    // The result should not be the original (it should reduce)
    assert_ne!(app, result, "Nat.rec (succ zero) should reduce");

    // Semantic preservation: app ≡ result
    assert!(
        tc.is_def_eq(&app, &result),
        "Iota reduction semantic preservation must hold for recursive Nat.succ: \
         Nat.rec motive z s (succ zero) ≡ {:?}",
        result
    );
}

/// Semantic preservation for doubly-recursive Nat case (succ(succ(zero))).
///
/// Tests that the IH chain works correctly: the RHS-based approach generates
/// `s 1 (Nat.rec motive z s 1)` which itself reduces further.
#[test]
fn test_iota_semantic_preservation_nat_rec_succ_succ() {
    let (env, nat_ref) = make_nat_env_and_ref();
    let tc = TypeChecker::new(&env);

    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    // motive: λ _:Nat. Nat
    let motive = Expr::lam(BinderInfo::Default, nat_ref.clone(), nat_ref.clone());
    // zero case: Nat.zero
    let case_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    // succ case: λ n:Nat. λ ih:Nat. succ(ih)  — computes successor of IH
    let case_succ = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::bvar(0),
            ),
        ),
    );

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let two = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            zero.clone(),
        ),
    );

    // Build: Nat.rec motive zero_case succ_case (succ(succ(zero)))
    // This should reduce to succ(succ(zero)) — the identity function on Nat
    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), case_zero), case_succ),
        two.clone(),
    );

    let result = tc.whnf(&app);
    assert_ne!(app, result, "Nat.rec (succ(succ(zero))) should reduce");

    // Semantic preservation
    assert!(
        tc.is_def_eq(&app, &result),
        "Iota reduction semantic preservation must hold for doubly-recursive case: \
         Nat.rec motive z s (succ(succ(zero))) ≡ {:?}",
        result
    );
}

/// Semantic preservation for MajorAfterMotive (recOn) argument order.
///
/// The RHS-based reduction must correctly handle recOn's different arg layout:
///   recOn motive major minors  (vs rec motive minors major)
/// This test verifies is_def_eq holds through the MajorAfterMotive path
/// (reduction.rs:309-319), which was untested for semantic preservation.
#[test]
fn test_iota_semantic_preservation_rec_on_succ() {
    let (env, nat_ref) = make_nat_env_and_ref();

    // Verify recOn uses MajorAfterMotive
    let rec_on_val = env
        .get_recursor(&Name::from_string("Nat.recOn"))
        .expect("Nat.recOn should exist");
    assert_eq!(rec_on_val.arg_order, RecursorArgOrder::MajorAfterMotive);

    let tc = TypeChecker::new(&env);

    let rec_on = Expr::const_(Name::from_string("Nat.recOn"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::prop());
    let zero_case = Expr::type_();
    // succ_case: λ n:Nat. λ ih:Prop. ih  (return IH)
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
    );

    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // recOn arg order: motive, major, zero_case, succ_case
    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec_on, motive), one), zero_case),
        succ_case,
    );

    let result = tc.whnf(&app);
    assert_ne!(app, result, "Nat.recOn (succ zero) should reduce");

    // Semantic preservation through MajorAfterMotive path
    assert!(
        tc.is_def_eq(&app, &result),
        "MajorAfterMotive semantic preservation: Nat.recOn motive (succ 0) z s ≡ {:?}",
        result
    );
}

/// Extra args forwarding for MajorAfterMotive (recOn) argument order.
///
/// Verifies that extras_start is computed correctly for recOn layout:
///   extras_start = args_before_major + 1 + num_minors  (reduction.rs:345-347)
/// vs the standard rec layout:
///   extras_start = args_before_major + 1               (reduction.rs:344)
#[test]
fn test_iota_reduction_rec_on_extra_args_forwarded() {
    let (env, nat_ref) = make_nat_env_and_ref();
    let tc = TypeChecker::new(&env);

    // Nat.recOn at level 1 (returning Nat → Nat)
    let rec_on = Expr::const_(
        Name::from_string("Nat.recOn"),
        vec![Level::succ(Level::zero())],
    );
    // motive: λ _:Nat. Nat → Nat  (returns function type)
    let motive = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::arrow(nat_ref.clone(), nat_ref.clone()),
    );
    // zero_case: λ x:Nat. x  (identity)
    let zero_case = Expr::lam(BinderInfo::Default, nat_ref.clone(), Expr::bvar(0));
    // succ_case: λ n:Nat. λ ih:(Nat→Nat). ih
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::arrow(nat_ref.clone(), nat_ref.clone()),
            Expr::bvar(0),
        ),
    );

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let extra_arg = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // recOn arg order: motive, major(=zero), zero_case, succ_case, extra_arg
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::app(rec_on, motive), zero), zero_case),
            succ_case,
        ),
        extra_arg.clone(),
    );

    let result = tc.whnf(&app);
    assert_eq!(
        result, extra_arg,
        "recOn extra arg must be forwarded through MajorAfterMotive path: got {:?}",
        result
    );
}
