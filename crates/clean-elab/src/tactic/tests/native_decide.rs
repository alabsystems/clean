// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::tactic::native_decide_eval::{
    clear_native_decide_cache_for_tests, execute_native_decide, native_decide_cache_len_for_tests,
    native_eval_bool, NativeDecideExecOutcome, NativeRunner,
};
use serial_test::serial;

#[test]
fn test_native_decide_true_goal_with_prelude_closes_without_trust() {
    let env = Environment::with_prelude();
    let target = Expr::const_(Name::from_string("True"), vec![]);
    let mut state = ProofState::new(env, target);

    native_decide(&mut state).expect("native_decide should close True via Decidable.isTrue");

    assert!(state.is_complete(), "True goal should be closed");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "native_decide on True should not use trusted fallbacks"
    );

    let proof = state.proof_term().expect("closed goal should retain proof");
    assert!(
        matches!(proof.kind(), ExprKind::Const(name, _) if name == &Name::from_string("True.intro")),
        "expected True.intro proof, got {proof:?}"
    );
}

#[test]
fn test_native_decide_false_goal_fails() {
    let env = Environment::with_prelude();
    let target = Expr::const_(Name::from_string("False"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = native_decide(&mut state);
    assert!(
        result.is_err(),
        "False should not be provable by native_decide"
    );
    assert!(
        !state.is_complete(),
        "refuted False goal should remain open after failure"
    );
}

#[test]
#[serial]
fn test_native_runner_compiles_nat_equality_and_hits_cache() {
    clear_native_decide_cache_for_tests();
    let target = make_eq(
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::apps(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            [Expr::nat_lit(2), Expr::nat_lit(2)],
        ),
        Expr::nat_lit(4),
    );

    let compiled = NativeRunner
        .compile(&target)
        .expect("native runner should compile ground Nat equality");
    assert!(
        !compiled.bytecode.is_empty(),
        "compiled native_decide bytecode should not be empty"
    );
    assert!(
        compiled.rust_source.contains("nat_add"),
        "generated native_decide program should lower Nat.add"
    );
    assert!(
        native_eval_bool(&compiled).expect("compiled native_decide program should execute"),
        "2 + 2 = 4 should evaluate to true via the native runner"
    );
    let first_len = native_decide_cache_len_for_tests();
    assert!(
        first_len >= 1,
        "first compile should populate the cache (got {first_len})"
    );

    let cached = NativeRunner
        .compile(&target)
        .expect("second compile should hit the cache");
    assert_eq!(
        compiled.bytecode, cached.bytecode,
        "cached compile result should reuse the same bytecode"
    );
    assert_eq!(
        native_decide_cache_len_for_tests(),
        first_len,
        "cache hit should not create a new entry"
    );
}

#[test]
fn test_native_decide_nat_equality_goal_uses_computational_path() {
    let env = Environment::with_prelude();
    let lhs = Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [Expr::nat_lit(2), Expr::nat_lit(2)],
    );
    let target = make_eq(
        Expr::const_(Name::from_string("Nat"), vec![]),
        lhs,
        Expr::nat_lit(4),
    );
    let mut state = ProofState::new(env, target);
    let goal = state.current_goal().expect("goal should exist").clone();

    // Wave 95 — Gap 19 CLOSED. `Nat.decEq` is registered as a native
    // reducer in the prelude; `synthesize_decidable_expr` now accepts
    // native-reducer-only hooks (not just full declarations).
    match execute_native_decide(&state, &goal) {
        Ok(NativeDecideExecOutcome::Proved(proof)) => {
            let proof_head = proof.get_app_fn();
            assert!(
                matches!(proof_head.kind(), ExprKind::Const(name, _) if name == &Name::from_string("Eq.refl")),
                "expected native_decide to extract an Eq.refl proof, got {proof:?}"
            );
        }
        Ok(NativeDecideExecOutcome::Refuted) => {
            panic!("2 + 2 = 4 should evaluate to true");
        }
        Err(err) => {
            panic!("native_decide computational path must close Nat 2+2=4: {err:?}");
        }
    }

    native_decide(&mut state).expect("native_decide should close Nat arithmetic equality");

    assert!(state.is_complete(), "Nat equality goal should be closed");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "native_decide on Nat equality should not use trusted fallbacks"
    );

    let proof = state.proof_term().expect("closed goal should retain proof");
    let proof_head = proof.get_app_fn();
    assert!(
        matches!(proof_head.kind(), ExprKind::Const(name, _) if name == &Name::from_string("Eq.refl")),
        "expected Eq.refl-headed proof, got {proof:?}"
    );
}

#[test]
fn test_native_decide_false_nat_equality_is_refuted_by_kernel_path() {
    let env = Environment::with_prelude();
    let lhs = Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [Expr::nat_lit(2), Expr::nat_lit(2)],
    );
    let target = make_eq(
        Expr::const_(Name::from_string("Nat"), vec![]),
        lhs,
        Expr::nat_lit(5),
    );
    let mut state = ProofState::new(env, target);
    let goal = state.current_goal().expect("goal should exist").clone();

    // Wave 95 — Gap 19 CLOSED. Refutation path now reaches the kernel
    // reducer for `Nat.decEq` (a native reducer suffices to enter the
    // path), and `2+2 = 5` reduces to `Decidable.isFalse`.
    let outcome = execute_native_decide(&state, &goal);
    match outcome {
        Ok(NativeDecideExecOutcome::Refuted) => {}
        Ok(NativeDecideExecOutcome::Proved(_)) => {
            panic!("2 + 2 = 5 should not prove")
        }
        Err(err) => {
            panic!("native_decide must reach refutation path for 2+2=5: {err:?}");
        }
    }

    let result = native_decide(&mut state);
    assert!(
        matches!(result, Err(TacticError::InvalidTarget { .. })),
        "refuted native_decide result should fail without falling back to decide, got: {result:?}"
    );
    assert!(
        !state.is_complete(),
        "refuted equality should leave the goal open"
    );
}

#[test]
fn test_native_decide_bool_equality_lowers_natively_and_stays_kernel_checked() {
    let env = Environment::with_prelude();
    let target = make_eq(
        Expr::const_(Name::from_string("Bool"), vec![]),
        Expr::const_(Name::from_string("Bool.true"), vec![]),
        Expr::const_(Name::from_string("Bool.true"), vec![]),
    );
    let mut state = ProofState::new(env, target.clone());
    let goal = state.current_goal().expect("goal should exist").clone();

    // native-decide-beyond-nat: Bool equality now lowers natively. The
    // lowering is only a fast oracle; on `Ok(true)` the trusted proof is
    // still re-derived by reducing `Bool.decEq` in the kernel.
    let compiled = NativeRunner
        .compile(&target)
        .expect("Bool equality should lower to a native program");
    assert!(
        compiled.rust_source.contains("bool_eq"),
        "generated native_decide program should lower Bool equality, got {}",
        compiled.rust_source
    );
    assert!(
        native_eval_bool(&compiled).expect("compiled Bool program should run"),
        "Bool.true = Bool.true should evaluate to true natively"
    );

    match execute_native_decide(&state, &goal) {
        Ok(NativeDecideExecOutcome::Proved(proof)) => {
            let proof_head = proof.get_app_fn();
            assert!(
                matches!(proof_head.kind(), ExprKind::Const(name, _) if name == &Name::from_string("Eq.refl")),
                "expected a kernel-checked Eq.refl proof, got {proof:?}"
            );
        }
        Ok(NativeDecideExecOutcome::Refuted) => panic!("true Bool equality should not be refuted"),
        Err(err) => {
            panic!("native_decide must close Bool.true=Bool.true: {err:?}");
        }
    }

    native_decide(&mut state).expect("native_decide should close Bool equality");
    assert!(
        state.is_complete(),
        "native_decide should close Bool equality"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "native_decide on Bool equality should not use trusted fallbacks"
    );
}

#[test]
fn test_native_decide_rejects_equality_on_type_with_no_dec_eq_hook() {
    // Wave 95 — Gap 19 negative test. Even with the native-reducer
    // hook acceptance, `synthesize_decidable_expr` must STILL refuse
    // equalities on types whose `<Ty>.decEq` is absent both as a
    // declaration AND as a native reducer. This guards the new path:
    // we relaxed the gate from "has declaration" to "has declaration
    // OR has native reducer" but it must still close on neither.
    let env = Environment::with_prelude();
    let unknown_ty = Expr::const_(Name::from_string("__NoSuchType_For_Wave95"), vec![]);
    let lhs = Expr::const_(Name::from_string("__NoSuchType_lhs"), vec![]);
    let rhs = Expr::const_(Name::from_string("__NoSuchType_rhs"), vec![]);
    let target = make_eq(unknown_ty, lhs, rhs);
    let state = ProofState::new(env, target);
    let goal = state.current_goal().expect("goal should exist").clone();

    let err = execute_native_decide(&state, &goal)
        .expect_err("synthesize_decidable_expr must reject unknown types");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("no DecidableEq synthesis hook") || msg.contains("__NoSuchType_For_Wave95"),
        "expected 'no DecidableEq synthesis hook' error, got: {msg}"
    );
}

#[test]
fn test_native_decide_falls_back_to_decide_when_native_and_kernel_paths_are_unsupported() {
    let env = Environment::with_prelude();
    let target = Expr::apps(
        Expr::const_(Name::from_string("Or"), vec![]),
        [
            Expr::const_(Name::from_string("True"), vec![]),
            Expr::const_(Name::from_string("False"), vec![]),
        ],
    );
    let mut state = ProofState::new(env, target);
    let goal = state.current_goal().expect("goal should exist").clone();

    assert!(
        execute_native_decide(&state, &goal).is_err(),
        "native and kernel paths should reject unsupported non-equality goals so decide can run"
    );

    native_decide(&mut state).expect("native_decide should fall back to decide on Or True False");
    assert!(
        state.is_complete(),
        "fallback decide should close Or True False"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "native_decide fallback should still avoid trusted fallbacks"
    );
}

/// Build the Lean `Int.ofNat n` representation of a non-negative integer.
fn int_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

#[test]
#[serial]
fn test_native_decide_bool_true_decide_closes() {
    clear_native_decide_cache_for_tests();
    let env = Environment::with_prelude();
    let target = make_eq(
        Expr::const_(Name::from_string("Bool"), vec![]),
        Expr::const_(Name::from_string("Bool.true"), vec![]),
        Expr::const_(Name::from_string("Bool.true"), vec![]),
    );
    let mut state = ProofState::new(env, target);

    native_decide(&mut state).expect("native_decide should close Bool true = true");
    assert!(state.is_complete(), "Bool true=true goal should be closed");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "Bool native_decide should not use trusted fallbacks"
    );
}

#[test]
#[serial]
fn test_native_decide_int_equality_lowers_natively_and_closes() {
    clear_native_decide_cache_for_tests();
    let env = Environment::with_prelude();
    // 2 + 2 = 4 over Int via Int.add on Int.ofNat constructors.
    let lhs = Expr::apps(
        Expr::const_(Name::from_string("Int.add"), vec![]),
        [int_of_nat(2), int_of_nat(2)],
    );
    let target = make_eq(
        Expr::const_(Name::from_string("Int"), vec![]),
        lhs,
        int_of_nat(4),
    );
    let mut state = ProofState::new(env, target.clone());

    let compiled = NativeRunner
        .compile(&target)
        .expect("Int equality should lower to a native program");
    assert!(
        compiled.rust_source.contains("int_eq"),
        "generated native_decide program should lower Int equality, got {}",
        compiled.rust_source
    );
    assert!(
        native_eval_bool(&compiled).expect("compiled Int program should run"),
        "Int 2 + 2 = 4 should evaluate to true natively"
    );

    native_decide(&mut state).expect("native_decide should close Int equality");
    assert!(state.is_complete(), "Int equality goal should be closed");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "native_decide on Int equality should not use trusted fallbacks"
    );
    let proof = state.proof_term().expect("closed goal should retain proof");
    assert!(
        matches!(proof.get_app_fn().kind(), ExprKind::Const(name, _) if name == &Name::from_string("Eq.refl")),
        "expected Eq.refl-headed proof, got {proof:?}"
    );
}

#[test]
#[serial]
fn test_native_decide_int_negative_equality_lowers_faithfully() {
    clear_native_decide_cache_for_tests();
    // negSucc 0 denotes -1; -1 = -1 must lower and run as `true`.
    let neg_one = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(0),
    );
    let target = make_eq(
        Expr::const_(Name::from_string("Int"), vec![]),
        neg_one.clone(),
        neg_one,
    );
    let compiled = NativeRunner
        .compile(&target)
        .expect("negative Int equality should lower to a native program");
    assert!(
        compiled.rust_source.contains("-1i64"),
        "Int.negSucc 0 should lower to -1i64, got {}",
        compiled.rust_source
    );
    assert!(
        native_eval_bool(&compiled).expect("compiled negative Int program should run"),
        "-1 = -1 should evaluate to true natively"
    );
}

#[test]
#[serial]
fn test_native_decide_string_equality_true_closes() {
    clear_native_decide_cache_for_tests();
    let env = Environment::with_prelude();
    let target = make_eq(
        Expr::const_(Name::from_string("String"), vec![]),
        Expr::str_lit("clean"),
        Expr::str_lit("clean"),
    );
    let mut state = ProofState::new(env, target.clone());

    let compiled = NativeRunner
        .compile(&target)
        .expect("String equality should lower to a native program");
    assert!(
        compiled.rust_source.contains("string_eq"),
        "generated native_decide program should lower String equality, got {}",
        compiled.rust_source
    );
    assert!(
        native_eval_bool(&compiled).expect("compiled String program should run"),
        "\"clean\" = \"clean\" should evaluate to true natively"
    );

    native_decide(&mut state).expect("native_decide should close equal String literals");
    assert!(state.is_complete(), "String equality goal should be closed");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "native_decide on String equality should not use trusted fallbacks"
    );
}

#[test]
#[serial]
fn test_native_decide_string_equality_false_is_refuted() {
    clear_native_decide_cache_for_tests();
    let env = Environment::with_prelude();
    let target = make_eq(
        Expr::const_(Name::from_string("String"), vec![]),
        Expr::str_lit("clean"),
        Expr::str_lit("lean"),
    );
    let compiled = NativeRunner
        .compile(&target)
        .expect("unequal String equality should still lower to a native program");
    assert!(
        !native_eval_bool(&compiled).expect("compiled String program should run"),
        "\"clean\" = \"lean\" should evaluate to false natively"
    );

    let mut state = ProofState::new(env, target);
    let goal = state.current_goal().expect("goal should exist").clone();
    match execute_native_decide(&state, &goal) {
        Ok(NativeDecideExecOutcome::Refuted) => {}
        other => panic!("unequal String literals should be refuted, got {other:?}"),
    }

    let result = native_decide(&mut state);
    assert!(
        result.is_err(),
        "refuted String inequality should fail native_decide, got {result:?}"
    );
    assert!(
        !state.is_complete(),
        "refuted String inequality should leave the goal open"
    );
}

#[test]
fn test_native_decide_unsupported_type_lowering_errors_honestly() {
    // SOUNDNESS: Float `==` is NaN-unfaithful, so it is NOT lowered. The
    // native lowering must reject it (and any unmodelled type) with an
    // honest Unsupported error rather than emitting a native decision.
    let target = make_eq(
        Expr::const_(Name::from_string("Float"), vec![]),
        Expr::const_(Name::from_string("Float.zero"), vec![]),
        Expr::const_(Name::from_string("Float.zero"), vec![]),
    );
    let err = NativeRunner
        .compile(&target)
        .expect_err("Float equality must not lower natively");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("only supports Nat/Bool/Int/String equality"),
        "expected honest unsupported-type error, got: {msg}"
    );
}
