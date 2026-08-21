// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;

fn count_lams(expr: &Expr) -> usize {
    match expr.kind() {
        ExprKind::App(f, a) => count_lams(f) + count_lams(a),
        ExprKind::Lam(_, ty, body) => 1 + count_lams(ty) + count_lams(body),
        ExprKind::Pi(_, ty, body) => count_lams(ty) + count_lams(body),
        ExprKind::Let(_, ty, val, body, _) => count_lams(ty) + count_lams(val) + count_lams(body),
        _ => 0,
    }
}

fn count_named_const(expr: &Expr, target: &str) -> usize {
    match expr.kind() {
        ExprKind::Const(name, _) if name.to_string() == target => 1,
        ExprKind::App(f, a) => count_named_const(f, target) + count_named_const(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            count_named_const(ty, target) + count_named_const(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            count_named_const(ty, target)
                + count_named_const(val, target)
                + count_named_const(body, target)
        }
        _ => 0,
    }
}

// make_eq is now a shared helper in tests/mod.rs

fn make_decidable_eq_goal(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        make_eq(ty, lhs, rhs),
    )
}

fn list_nat_ty() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    )
}

fn list_nat_nil() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    )
}

fn list_nat_cons(head: u64, tail: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
            Expr::nat_lit(head),
        ),
        tail,
    )
}

#[test]
fn test_decide_eq_generic_enum_cross_constructor_uses_noconfusion() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    env.init_ordering().unwrap();
    env.init_decidable().unwrap();

    let ordering_ty = Expr::const_(Name::from_string("Ordering"), vec![]);
    let gt = Expr::const_(Name::from_string("Ordering.gt"), vec![]);
    let lt = Expr::const_(Name::from_string("Ordering.lt"), vec![]);
    let mut state = ProofState::new(env, make_decidable_eq_goal(ordering_ty, gt, lt));

    decide_eq(&mut state).expect("different Ordering constructors should be decidably unequal");
    assert!(state.is_complete());
    assert_eq!(state.trusted_axiom_count(), 0);
    let proof = state
        .proof_term()
        .expect("completed state should have a proof");
    assert_eq!(count_named_const(&proof, "Ordering.noConfusion"), 1);
}

#[test]
fn test_decide_eq_nat_inequality_proof_uses_recursive_noconfusion_shape() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    env.init_nat().unwrap();
    env.init_decidable().unwrap();

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let five = Expr::nat_lit(5);
    let six = Expr::nat_lit(6);
    let eq_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty,
            ),
            five,
        ),
        six,
    );
    let decidable_goal = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        eq_expr,
    );
    let mut state = ProofState::new(env, decidable_goal);

    decide_eq(&mut state).expect("decide_eq should solve Decidable (5 = 6)");
    assert!(
        state.is_complete(),
        "goal should be closed after decide_eq builds the noConfusion proof",
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "5 ≠ 6 should stay entirely on the kernel noConfusion path",
    );

    let proof = state
        .proof_term()
        .expect("completed state should have proof term");
    let args = proof.get_app_args();
    assert_eq!(
        args.len(),
        2,
        "Decidable.isFalse proof should keep both the proposition and proof arguments",
    );

    let ne_proof = args[1];
    assert_eq!(
        count_named_const(ne_proof, "Nat.noConfusion"),
        6,
        "5 ≠ 6 should recurse through six Nat.noConfusion applications",
    );
    assert_eq!(
        count_lams(ne_proof),
        6,
        "5 ≠ 6 should build one equality lambda per recursive predecessor step",
    );
}

#[test]
fn test_build_noconfusion_ne_proof_typechecks_for_list_head_mismatch() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let list_nat_ty = list_nat_ty();
    let lhs = list_nat_cons(1, list_nat_nil());
    let rhs = list_nat_cons(2, list_nat_nil());
    let eq_level = Level::succ(Level::zero());

    let proof = decide_eq_noconfusion::build_noconfusion_ne_proof(
        &env,
        &list_nat_ty,
        &lhs,
        &rhs,
        &eq_level,
    )
    .expect("List head mismatch should produce a noConfusion proof");
    let inferred = tc
        .infer_type(&proof)
        .expect("List head mismatch proof should typecheck");
    let expected = Expr::pi(
        BinderInfo::Default,
        decide_eq_noconfusion::mk_eq_expr(&list_nat_ty, &lhs, &rhs, &eq_level),
        Expr::const_(Name::from_string("False"), vec![]),
    );

    assert!(
        tc.is_def_eq(&inferred, &expected),
        "type mismatch:\n  inferred: {inferred:?}\n  expected: {expected:?}"
    );

    let consts = collect_consts(&proof);
    assert!(
        consts.contains(&Name::from_string("List.noConfusion")),
        "proof should contain List.noConfusion, got consts: {consts:?}"
    );
    assert!(
        consts.contains(&Name::from_string("Nat.noConfusion")),
        "proof should recurse to Nat.noConfusion, got consts: {consts:?}"
    );
}

#[test]
fn test_decide_eq_string_inequality_no_trusted_axioms_with_prelude() {
    let env = Environment::with_prelude();
    let string_ty = Expr::const_(Name::from_string("String"), vec![]);
    let goal = make_decidable_eq_goal(string_ty, Expr::str_lit("ab"), Expr::str_lit("ac"));
    let mut state = ProofState::new(env, goal);

    let result = decide_eq(&mut state);
    assert!(
        result.is_ok(),
        "decide_eq should solve Decidable (\"ab\" = \"ac\")"
    );
    assert!(
        state.is_complete(),
        "string inequality goal should be closed"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "REGRESSION: decide_eq used {} trusted axioms for string inequality (expected 0)",
        state.trusted_axiom_count()
    );

    let proof = state
        .proof_term()
        .expect("completed state should retain the proof term");
    let consts = collect_consts(&proof);
    // Char leaves discriminate via `congrArg Char.toNat` (the genuine 2-field
    // v4.30 Char has no 1-field noConfusion diagonal — carrier-parity P2), so
    // `Char.noConfusion` is no longer in the proof; the String→List→Nat
    // structural chain still is.
    for name in ["String.noConfusion", "List.noConfusion", "Nat.noConfusion"] {
        assert!(
            consts.contains(&Name::from_string(name)),
            "proof should contain {name}, got consts: {consts:?}"
        );
    }
}

/// Same-constructor recursive path: cons/cons with matching heads and different tails.
///
/// `[1,2] ≠ [1,3]` exercises the BVar(0) tail-equality branch (line 401 of
/// decide_eq_noconfusion.rs). If the de Bruijn index is wrong, the proof term
/// will fail kernel typechecking because the lambda binder order is
/// `fun (h_head : 1=1) (h_tail : [2]=[3]) => tail_proof(h_tail)`.
#[test]
fn test_build_noconfusion_ne_proof_typechecks_for_list_tail_recursion() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let list_nat_ty = list_nat_ty();
    // [1,2]
    let lhs = list_nat_cons(1, list_nat_cons(2, list_nat_nil()));
    // [1,3]
    let rhs = list_nat_cons(1, list_nat_cons(3, list_nat_nil()));
    let eq_level = Level::succ(Level::zero());

    let proof = decide_eq_noconfusion::build_noconfusion_ne_proof(
        &env,
        &list_nat_ty,
        &lhs,
        &rhs,
        &eq_level,
    )
    .expect("[1,2] ≠ [1,3] should produce a noConfusion proof via tail recursion");

    let inferred = tc
        .infer_type(&proof)
        .expect("List tail-recursion proof should typecheck");
    let expected = Expr::pi(
        BinderInfo::Default,
        decide_eq_noconfusion::mk_eq_expr(&list_nat_ty, &lhs, &rhs, &eq_level),
        Expr::const_(Name::from_string("False"), vec![]),
    );
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "tail recursion proof type mismatch:\n  inferred: {inferred:?}\n  expected: {expected:?}"
    );

    let consts = collect_consts(&proof);
    assert!(
        consts.contains(&Name::from_string("List.noConfusion")),
        "tail recursion proof should contain List.noConfusion, got: {consts:?}"
    );
    assert!(
        consts.contains(&Name::from_string("Nat.noConfusion")),
        "tail recursion proof should recurse to Nat.noConfusion for inner head mismatch, got: {consts:?}"
    );

    // The outer List.noConfusion + inner List.noConfusion (head [2] vs [3])
    // plus Nat.noConfusion for the actual 2≠3 discrimination.
    assert!(
        count_named_const(&proof, "List.noConfusion") >= 2,
        "expected ≥2 List.noConfusion (outer cons + inner tail cons), got {}",
        count_named_const(&proof, "List.noConfusion")
    );
}

/// Nil/cons discrimination: `[] ≠ [1]` is the different-constructor base case
/// for List.noConfusion.
#[test]
fn test_build_noconfusion_ne_proof_typechecks_for_list_nil_cons() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let list_nat_ty = list_nat_ty();
    let lhs = list_nat_nil();
    let rhs = list_nat_cons(1, list_nat_nil());
    let eq_level = Level::succ(Level::zero());

    let proof = decide_eq_noconfusion::build_noconfusion_ne_proof(
        &env,
        &list_nat_ty,
        &lhs,
        &rhs,
        &eq_level,
    )
    .expect("[] ≠ [1] should produce a noConfusion proof");

    let inferred = tc
        .infer_type(&proof)
        .expect("nil/cons discrimination proof should typecheck");
    let expected = Expr::pi(
        BinderInfo::Default,
        decide_eq_noconfusion::mk_eq_expr(&list_nat_ty, &lhs, &rhs, &eq_level),
        Expr::const_(Name::from_string("False"), vec![]),
    );
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "nil/cons proof type mismatch:\n  inferred: {inferred:?}\n  expected: {expected:?}"
    );

    let consts = collect_consts(&proof);
    assert!(
        consts.contains(&Name::from_string("List.noConfusion")),
        "nil/cons proof should contain List.noConfusion, got: {consts:?}"
    );
    // Different constructors: no recursive descent needed
    assert!(
        !consts.contains(&Name::from_string("Nat.noConfusion")),
        "nil/cons should NOT recurse to Nat.noConfusion (different constructors), got: {consts:?}"
    );
}

/// Deep list recursion: `[1,2,3] ≠ [1,2,4]` requires two layers of cons/cons
/// same-constructor recursion before finding the 3≠4 base case.
#[test]
fn test_build_noconfusion_ne_proof_typechecks_for_list_deep_tail_recursion() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let list_nat_ty = list_nat_ty();
    // [1,2,3]
    let lhs = list_nat_cons(1, list_nat_cons(2, list_nat_cons(3, list_nat_nil())));
    // [1,2,4]
    let rhs = list_nat_cons(1, list_nat_cons(2, list_nat_cons(4, list_nat_nil())));
    let eq_level = Level::succ(Level::zero());

    let proof = decide_eq_noconfusion::build_noconfusion_ne_proof(
        &env,
        &list_nat_ty,
        &lhs,
        &rhs,
        &eq_level,
    )
    .expect("[1,2,3] ≠ [1,2,4] should produce a noConfusion proof");

    let inferred = tc
        .infer_type(&proof)
        .expect("deep list recursion proof should typecheck");
    let expected = Expr::pi(
        BinderInfo::Default,
        decide_eq_noconfusion::mk_eq_expr(&list_nat_ty, &lhs, &rhs, &eq_level),
        Expr::const_(Name::from_string("False"), vec![]),
    );
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "deep recursion proof type mismatch:\n  inferred: {inferred:?}\n  expected: {expected:?}"
    );

    // Should recurse through at least 3 List.noConfusion (one per cons layer)
    assert!(
        count_named_const(&proof, "List.noConfusion") >= 3,
        "expected ≥3 List.noConfusion for [1,2,3]≠[1,2,4], got {}",
        count_named_const(&proof, "List.noConfusion")
    );
}

/// String same-prefix recursive descent: `"abc" ≠ "abd"` requires matching
/// 'a' and 'b' before finding the 'c' ≠ 'd' base case. This exercises the
/// String → List Char → Char → Nat recursion chain at depth.
#[test]
fn test_decide_eq_string_same_prefix_deeper_recursion() {
    let env = Environment::with_prelude();
    let string_ty = Expr::const_(Name::from_string("String"), vec![]);
    let goal = make_decidable_eq_goal(string_ty, Expr::str_lit("abc"), Expr::str_lit("abd"));
    let mut state = ProofState::new(env, goal);

    let result = decide_eq(&mut state);
    assert!(
        result.is_ok(),
        "decide_eq should solve Decidable (\"abc\" = \"abd\")"
    );
    assert!(
        state.is_complete(),
        "string same-prefix inequality goal should be closed"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "\"abc\" ≠ \"abd\" should use 0 trusted axioms (got {})",
        state.trusted_axiom_count()
    );

    let proof = state
        .proof_term()
        .expect("completed state should retain the proof term");
    let consts = collect_consts(&proof);

    // All four noConfusion constants needed for the String→List Char→Char→Nat chain
    // Char leaves discriminate via `congrArg Char.toNat` (the genuine 2-field
    // v4.30 Char has no 1-field noConfusion diagonal — carrier-parity P2), so
    // `Char.noConfusion` is no longer in the proof; the String→List→Nat
    // structural chain still is.
    for name in ["String.noConfusion", "List.noConfusion", "Nat.noConfusion"] {
        assert!(
            consts.contains(&Name::from_string(name)),
            "\"abc\"≠\"abd\" proof should contain {name}, got: {consts:?}"
        );
    }

    // Deeper string requires more List.noConfusion applications (one per char position)
    // "abc" vs "abd": 3 char positions → at least 3 List.noConfusion
    assert!(
        count_named_const(&proof, "List.noConfusion") >= 3,
        "expected ≥3 List.noConfusion for 3-char same-prefix string, got {}",
        count_named_const(&proof, "List.noConfusion")
    );
}

/// Constructor field ordering: under Lean v4.30's heterogeneous convention
/// (designs/2026-07-03-noconfusion-ctoridx-convention.md §3),
/// `List.noConfusionType P (cons a1 t1) (cons a2 t2)` reduces to
/// `((a1 ≍ a2 → t1 ≍ t2 → P) → P)` — both cons fields mention the param α,
/// so the diagonal hypotheses are HEq.
///
/// The proof term must use BVar(1) for the head hypothesis and BVar(0) for
/// the tail hypothesis (converted back to Eq via eq_of_heq before feeding
/// the recursive sub-proofs). This test verifies the ordering by checking
/// that tail-different lists ([1,2] vs [1,3]) produce a proof where the
/// tail-inequality sub-proof references the inner (BVar 0) binder.
///
/// This is a structural check — the typechecker confirms correctness, but
/// this test also verifies the *specific* Lean 4 field ordering so that
/// proof terms are compatible with Lean 4's expected noConfusionType shape.
#[test]
fn test_noconfusion_field_ordering_head_before_tail() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let list_nat_ty = list_nat_ty();
    // Tail-different: heads match, so tail path (BVar 0) should be used
    let lhs = list_nat_cons(1, list_nat_cons(2, list_nat_nil()));
    let rhs = list_nat_cons(1, list_nat_cons(3, list_nat_nil()));
    let eq_level = Level::succ(Level::zero());

    let proof = decide_eq_noconfusion::build_noconfusion_ne_proof(
        &env,
        &list_nat_ty,
        &lhs,
        &rhs,
        &eq_level,
    )
    .expect("tail-different list should produce a noConfusion proof");

    // Kernel typechecking is the ground truth for field ordering correctness:
    // if BVar indices don't match the lambda binder types produced by
    // noConfusionType, infer_type will fail.
    let inferred = tc
        .infer_type(&proof)
        .expect("field ordering must be correct for proof to typecheck");
    let expected = Expr::pi(
        BinderInfo::Default,
        decide_eq_noconfusion::mk_eq_expr(&list_nat_ty, &lhs, &rhs, &eq_level),
        Expr::const_(Name::from_string("False"), vec![]),
    );
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "field-ordering proof type mismatch"
    );

    // Also verify head-different: heads differ, so head path (BVar 1) should be used
    let lhs_hd = list_nat_cons(1, list_nat_cons(2, list_nat_nil()));
    let rhs_hd = list_nat_cons(5, list_nat_cons(2, list_nat_nil()));
    let proof_hd = decide_eq_noconfusion::build_noconfusion_ne_proof(
        &env,
        &list_nat_ty,
        &lhs_hd,
        &rhs_hd,
        &eq_level,
    )
    .expect("head-different list should produce a noConfusion proof");
    let inferred_hd = tc
        .infer_type(&proof_hd)
        .expect("head-different proof field ordering must be correct");
    let expected_hd = Expr::pi(
        BinderInfo::Default,
        decide_eq_noconfusion::mk_eq_expr(&list_nat_ty, &lhs_hd, &rhs_hd, &eq_level),
        Expr::const_(Name::from_string("False"), vec![]),
    );
    assert!(
        tc.is_def_eq(&inferred_hd, &expected_hd),
        "head-different proof type mismatch"
    );
}
