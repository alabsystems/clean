// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end ay-smt integration tests.
//!
//! These tests verify that the ay solver handles diverse goal types in-process.
//! All tests are gated behind `#[cfg(feature = "ay-smt")]` — they test the
//! actual ay solver path, not the native SMT fallback.
//!
//! Part of #1598: In-process ay tactic via ay-lean-bridge.

#![cfg(feature = "ay-smt")]

use super::*;
use crate::tactic::smt::{ay_bv, ay_decide, ay_omega, ay_smt, AyConfig};
use crate::tactic::tc_app::{nat_le_tc, nat_lt_tc};
use clean_kernel::env::Declaration;
use clean_kernel::sorry::{
    local_ay_reconstruction_success_count, reset_local_ay_reconstruction_success_counter,
};

// =========================================================================
// Setup helpers
// =========================================================================

/// Environment with Eq, And, Not, Nat, trustedAy + propositions P, Q, R.
///
/// Uses targeted init (not with_prelude) to avoid List.cons type-check
/// regression from in-progress W1 add_inductive changes (#2156).
fn setup_ay_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_and().unwrap();
    env.init_classical().unwrap();
    env.init_nat().unwrap();
    env.init_true_false().unwrap();
    env.init_trusted_ay().unwrap();
    env.init_trusted_arith().unwrap();
    env.init_le().unwrap();
    env.init_lt().unwrap();

    let prop = Expr::prop();
    // Propositions P, Q, R
    for name in ["P", "Q", "R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }
    env
}

/// Make: @Eq α lhs rhs
fn ay_make_eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs,
        ),
        rhs,
    )
}

/// Make: @And a b
fn ay_make_and(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a),
        b,
    )
}

/// Make: @Or a b
fn ay_make_or(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a),
        b,
    )
}

/// Make: @Not a
fn ay_make_not(a: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), a)
}

/// Make: @LE.le Nat instLENat lhs rhs
fn ay_make_nat_le(lhs: Expr, rhs: Expr) -> Expr {
    nat_le_tc(lhs, rhs)
}

/// Make: @LT.lt Nat instLTNat lhs rhs
fn ay_make_nat_lt(lhs: Expr, rhs: Expr) -> Expr {
    nat_lt_tc(lhs, rhs)
}

/// Make: @HAdd.hAdd Nat Nat Nat instHAddNat lhs rhs
fn ay_make_nat_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), lhs),
        rhs,
    )
}

fn prop_local_decl(id: u64, name: &str) -> (Expr, LocalDecl) {
    let fvar = FVarId::new(id);
    (
        Expr::fvar(fvar),
        LocalDecl {
            fvar,
            name: name.to_string(),
            ty: Expr::prop(),
            value: None,
        },
    )
}

// =========================================================================
// Propositional logic (ay_decide)
// =========================================================================

/// 1. P ∨ ¬P (law of excluded middle)
#[test]
fn test_ay_prop_excluded_middle() {
    let env = setup_ay_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let target = ay_make_or(p.clone(), ay_make_not(p));

    let mut state = ProofState::new(env, target);
    ay_decide(&mut state, AyConfig::default()).expect("ay should prove P ∨ ¬P");
    assert!(state.is_complete());
}

/// 2. h: P ∧ Q ⊢ P (conjunction elimination via hypothesis)
#[test]
fn test_ay_prop_and_elim_left() {
    let env = setup_ay_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let h_fvar = FVarId::new(1);

    let mut state = ProofState::with_context(
        env,
        p.clone(),
        vec![LocalDecl {
            fvar: h_fvar,
            name: "h".to_string(),
            ty: ay_make_and(p, q),
            value: None,
        }],
    );
    ay_decide(&mut state, AyConfig::default()).expect("ay should prove P from P ∧ Q");
    assert!(state.is_complete());
}

/// 3. h: P ⊢ P ∨ Q (disjunction introduction via hypothesis)
#[test]
fn test_ay_prop_or_intro_left() {
    let env = setup_ay_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let h_fvar = FVarId::new(1);

    let mut state = ProofState::with_context(
        env,
        ay_make_or(p.clone(), q),
        vec![LocalDecl {
            fvar: h_fvar,
            name: "h".to_string(),
            ty: p,
            value: None,
        }],
    );
    ay_decide(&mut state, AyConfig::default()).expect("ay should prove P ∨ Q from P");
    assert!(state.is_complete());
}

/// 5. h: ¬Q ⊢ ¬Q (direct hypothesis forwarding)
#[test]
fn test_ay_prop_not_from_hypothesis() {
    let env = setup_ay_env();
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let h_fvar = FVarId::new(1);

    let mut state = ProofState::with_context(
        env,
        ay_make_not(q.clone()),
        vec![LocalDecl {
            fvar: h_fvar,
            name: "h".to_string(),
            ty: ay_make_not(q),
            value: None,
        }],
    );
    ay_decide(&mut state, AyConfig::default()).expect("ay should prove ¬Q from ¬Q");
    assert!(state.is_complete());
}

/// 6. h1: P, h2: ¬P ⊢ False (contradiction from hypotheses)
#[test]
fn test_ay_prop_contradiction_from_hyps() {
    let env = setup_ay_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let h1_fvar = FVarId::new(1);
    let h2_fvar = FVarId::new(2);
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);

    let mut state = ProofState::with_context(
        env,
        false_ty,
        vec![
            LocalDecl {
                fvar: h1_fvar,
                name: "h1".to_string(),
                ty: p.clone(),
                value: None,
            },
            LocalDecl {
                fvar: h2_fvar,
                name: "h2".to_string(),
                ty: ay_make_not(p),
                value: None,
            },
        ],
    );
    ay_decide(&mut state, AyConfig::default()).expect("ay should derive False from P and ¬P");
    assert!(state.is_complete());
}

/// 8. h1: P ∨ Q, h2: ¬P ⊢ Q (disjunctive syllogism)
#[test]
fn test_ay_prop_disjunctive_syllogism() {
    let env = setup_ay_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let h1_fvar = FVarId::new(1);
    let h2_fvar = FVarId::new(2);

    let mut state = ProofState::with_context(
        env,
        q.clone(),
        vec![
            LocalDecl {
                fvar: h1_fvar,
                name: "h1".to_string(),
                ty: ay_make_or(p.clone(), q),
                value: None,
            },
            LocalDecl {
                fvar: h2_fvar,
                name: "h2".to_string(),
                ty: ay_make_not(p),
                value: None,
            },
        ],
    );
    ay_decide(&mut state, AyConfig::default()).expect("ay should prove disjunctive syllogism");
    assert!(state.is_complete());
}

// =========================================================================
// Integer arithmetic (ay_omega)
// =========================================================================

/// 9. 0 ≤ 5 (concrete inequality)
#[test]
fn test_ay_arith_concrete_le() {
    let env = setup_ay_env();
    let target = ay_make_nat_le(Expr::nat_lit(0), Expr::nat_lit(5));

    let mut state = ProofState::new(env, target);
    ay_omega(&mut state, AyConfig::default()).expect("ay should prove 0 ≤ 5");
    assert!(state.is_complete());
}

/// 10. 2 + 3 = 5 (concrete addition)
#[test]
fn test_ay_arith_concrete_add() {
    let env = setup_ay_env();
    let lhs = ay_make_nat_add(Expr::nat_lit(2), Expr::nat_lit(3));
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = ay_make_eq(nat_ty, lhs, Expr::nat_lit(5));

    let mut state = ProofState::new(env, target);
    ay_omega(&mut state, AyConfig::default()).expect("ay should prove 2 + 3 = 5");
    assert!(state.is_complete());
}

/// 11. 3 < 7 (concrete strict inequality)
#[test]
fn test_ay_arith_concrete_lt() {
    let env = setup_ay_env();
    let target = ay_make_nat_lt(Expr::nat_lit(3), Expr::nat_lit(7));

    let mut state = ProofState::new(env, target);
    ay_omega(&mut state, AyConfig::default()).expect("ay should prove 3 < 7");
    assert!(state.is_complete());
}

/// 12. h: a ≤ b ⊢ a ≤ b (hypothesis forwarding)
#[test]
fn test_ay_arith_hypothesis_le() {
    let env = setup_ay_env();
    let fvar_a = FVarId::new(1);
    let fvar_b = FVarId::new(2);
    let fvar_h = FVarId::new(3);
    let a = Expr::fvar(fvar_a);
    let b = Expr::fvar(fvar_b);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let le_ty = ay_make_nat_le(a.clone(), b.clone());

    let state = ProofState::with_context(
        env,
        le_ty.clone(),
        vec![
            LocalDecl {
                fvar: fvar_a,
                name: "a".to_string(),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: fvar_b,
                name: "b".to_string(),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                fvar: fvar_h,
                name: "h".to_string(),
                ty: le_ty.clone(),
                value: None,
            },
        ],
    );

    let mut state = state;
    ay_omega(&mut state, AyConfig::default()).expect("ay should forward hypothesis a ≤ b");
    assert!(state.is_complete());
}

/// 13. h1: a ≤ b, h2: b ≤ c ⊢ a ≤ c (transitivity via ay)
#[test]
fn test_ay_arith_transitivity() {
    let env = setup_ay_env();
    let fvar_a = FVarId::new(1);
    let fvar_b = FVarId::new(2);
    let fvar_c = FVarId::new(3);
    let fvar_h1 = FVarId::new(4);
    let fvar_h2 = FVarId::new(5);
    let a = Expr::fvar(fvar_a);
    let b = Expr::fvar(fvar_b);
    let c = Expr::fvar(fvar_c);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let h1_ty = ay_make_nat_le(a.clone(), b.clone());
    let h2_ty = ay_make_nat_le(b.clone(), c.clone());
    let target = ay_make_nat_le(a, c);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: fvar_a,
                name: "a".to_string(),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: fvar_b,
                name: "b".to_string(),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: fvar_c,
                name: "c".to_string(),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                fvar: fvar_h1,
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: fvar_h2,
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    ay_omega(&mut state, AyConfig::default())
        .expect("ay should prove transitivity a ≤ b, b ≤ c ⊢ a ≤ c");
    assert!(state.is_complete());
}

/// 14. h: a < b ⊢ a ≤ b (strict to weak inequality)
#[test]
fn test_ay_arith_lt_implies_le() {
    let env = setup_ay_env();
    let fvar_a = FVarId::new(1);
    let fvar_b = FVarId::new(2);
    let fvar_h = FVarId::new(3);
    let a = Expr::fvar(fvar_a);
    let b = Expr::fvar(fvar_b);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let h_ty = ay_make_nat_lt(a.clone(), b.clone());
    let target = ay_make_nat_le(a, b);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: fvar_a,
                name: "a".to_string(),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: fvar_b,
                name: "b".to_string(),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                fvar: fvar_h,
                name: "h".to_string(),
                ty: h_ty,
                value: None,
            },
        ],
    );

    ay_omega(&mut state, AyConfig::default()).expect("ay should prove a < b → a ≤ b");
    assert!(state.is_complete());
}

// =========================================================================
// General SMT (ay_smt)
// =========================================================================

/// 15. a = b → b = a (symmetry via SMT)
#[test]
fn test_ay_smt_eq_symmetry() {
    let env = setup_ay_env();
    let fvar_a = FVarId::new(1);
    let fvar_b = FVarId::new(2);
    let fvar_h = FVarId::new(3);
    let a = Expr::fvar(fvar_a);
    let b = Expr::fvar(fvar_b);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let h_ty = ay_make_eq(nat_ty.clone(), a.clone(), b.clone());
    let target = ay_make_eq(nat_ty.clone(), b, a);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: fvar_a,
                name: "a".to_string(),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: fvar_b,
                name: "b".to_string(),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                fvar: fvar_h,
                name: "h".to_string(),
                ty: h_ty,
                value: None,
            },
        ],
    );

    ay_smt(&mut state, AyConfig::default()).expect("ay should prove eq symmetry");
    assert!(state.is_complete());
}

/// 16. a = b, b = c ⊢ a = c (equality transitivity)
#[test]
fn test_ay_smt_eq_transitivity() {
    let env = setup_ay_env();
    let fvar_a = FVarId::new(1);
    let fvar_b = FVarId::new(2);
    let fvar_c = FVarId::new(3);
    let fvar_h1 = FVarId::new(4);
    let fvar_h2 = FVarId::new(5);
    let a = Expr::fvar(fvar_a);
    let b = Expr::fvar(fvar_b);
    let c = Expr::fvar(fvar_c);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let h1_ty = ay_make_eq(nat_ty.clone(), a.clone(), b.clone());
    let h2_ty = ay_make_eq(nat_ty.clone(), b.clone(), c.clone());
    let target = ay_make_eq(nat_ty.clone(), a, c);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: fvar_a,
                name: "a".to_string(),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: fvar_b,
                name: "b".to_string(),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: fvar_c,
                name: "c".to_string(),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                fvar: fvar_h1,
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: fvar_h2,
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    ay_smt(&mut state, AyConfig::default()).expect("ay should prove eq transitivity");
    assert!(state.is_complete());
}

/// 17. a = a (reflexivity via ay_smt with explicit QF_UF logic)
#[test]
fn test_ay_smt_qf_uf_reflexivity() {
    let env = setup_ay_env();
    let fvar_a = FVarId::new(1);
    let a = Expr::fvar(fvar_a);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = ay_make_eq(nat_ty.clone(), a.clone(), a);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: fvar_a,
            name: "a".to_string(),
            ty: nat_ty,
            value: None,
        }],
    );

    let config = AyConfig::default().with_logic(clean_auto::bridge::ay_contract::AyLogic::QfUf);
    ay_smt(&mut state, config).expect("ay QF_UF should prove reflexivity");
    assert!(state.is_complete());
}

// =========================================================================
// Timeout support
// =========================================================================

/// 18. Timeout configuration is respected (doesn't hang)
#[test]
fn test_ay_omega_with_timeout() {
    let env = setup_ay_env();
    let target = ay_make_nat_le(Expr::nat_lit(0), Expr::nat_lit(1));

    let mut state = ProofState::new(env, target);

    let config = AyConfig::default().with_timeout_ms(1000);
    ay_omega(&mut state, config).expect("ay with timeout should prove 0 ≤ 1");
    assert!(state.is_complete());
}

// =========================================================================
// Mixed theory (ay_smt with hypotheses)
// =========================================================================

/// 20. h: a ≤ 5, goal: a ≤ 10 (arithmetic weakening)
#[test]
fn test_ay_arith_weakening() {
    let env = setup_ay_env();
    let fvar_a = FVarId::new(1);
    let fvar_h = FVarId::new(2);
    let a = Expr::fvar(fvar_a);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let h_ty = ay_make_nat_le(a.clone(), Expr::nat_lit(5));
    let target = ay_make_nat_le(a, Expr::nat_lit(10));

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: fvar_a,
                name: "a".to_string(),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                fvar: fvar_h,
                name: "h".to_string(),
                ty: h_ty,
                value: None,
            },
        ],
    );

    ay_omega(&mut state, AyConfig::default()).expect("ay should prove a ≤ 5 → a ≤ 10");
    assert!(state.is_complete());
}

/// 21. h1: a ≤ b, h2: b < c ⊢ a < c (mixed inequality transitivity)
#[test]
fn test_ay_arith_mixed_inequality_transitivity() {
    let env = setup_ay_env();
    let fvar_a = FVarId::new(1);
    let fvar_b = FVarId::new(2);
    let fvar_c = FVarId::new(3);
    let fvar_h1 = FVarId::new(4);
    let fvar_h2 = FVarId::new(5);
    let a = Expr::fvar(fvar_a);
    let b = Expr::fvar(fvar_b);
    let c = Expr::fvar(fvar_c);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let h1_ty = ay_make_nat_le(a.clone(), b.clone());
    let h2_ty = ay_make_nat_lt(b.clone(), c.clone());
    let target = ay_make_nat_lt(a, c);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: fvar_a,
                name: "a".to_string(),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: fvar_b,
                name: "b".to_string(),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: fvar_c,
                name: "c".to_string(),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                fvar: fvar_h1,
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: fvar_h2,
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    ay_omega(&mut state, AyConfig::default()).expect("ay should prove a ≤ b, b < c → a < c");
    assert!(state.is_complete());
}

/// 22. 0 + 0 = 0 (addition identity)
#[test]
fn test_ay_arith_add_identity() {
    let env = setup_ay_env();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let sum = ay_make_nat_add(Expr::nat_lit(0), Expr::nat_lit(0));
    let target = ay_make_eq(nat_ty, sum, Expr::nat_lit(0));

    let mut state = ProofState::new(env, target);
    ay_omega(&mut state, AyConfig::default()).expect("ay should prove 0 + 0 = 0");
    assert!(state.is_complete());
}

/// 23. ay_bv with simple equality (bitvector path)
#[test]
fn test_ay_bv_simple_eq() {
    let env = setup_ay_env();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = ay_make_eq(nat_ty, Expr::nat_lit(42), Expr::nat_lit(42));

    let mut state = ProofState::new(env, target);
    ay_bv(&mut state, AyConfig::default()).expect("ay_bv should prove 42 = 42");
    assert!(state.is_complete());
}

/// 24. ¬(5 < 3) (negated false inequality)
#[test]
fn test_ay_arith_negated_false_lt() {
    let env = setup_ay_env();
    let target = ay_make_not(ay_make_nat_lt(Expr::nat_lit(5), Expr::nat_lit(3)));

    let mut state = ProofState::new(env, target);
    ay_omega(&mut state, AyConfig::default()).expect("ay should prove ¬(5 < 3)");
    assert!(state.is_complete());
}

// =========================================================================
// Verifiable path: kernel proof reconstruction (Part of #302)
// =========================================================================

use crate::tactic::smt::SmtVerifyPolicy;

/// 26. Verifiable path: ay_decide closes goal via ExtractOnly policy
///
/// Full tactic-level test verifying ay_decide works through the Verifiable
/// solver path (ExtractOnly) without falling back to trusted axioms for a
/// propositional tautology. Part of #302, #2442.
#[test]
fn test_ay_decide_verifiable_path_closes_goal() {
    let env = setup_ay_env();
    let (p, p_decl) = prop_local_decl(91, "p");
    let target = ay_make_or(p.clone(), ay_make_not(p));

    reset_local_ay_reconstruction_success_counter();
    let mut state = ProofState::with_context(env, target, vec![p_decl]);
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    ay_decide(&mut state, config).expect("ay ExtractOnly should prove P ∨ ¬P");
    assert!(state.is_complete(), "goal should be closed");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "ay ExtractOnly tautology path should stay trust-free"
    );
    let recon_count = local_ay_reconstruction_success_count();
    assert!(
        recon_count >= 1,
        "supported Prop-FVar tautology should stay on the ay/bridge path; got {recon_count}"
    );
}

/// 29. ExtractOnly reconstruction effectiveness: h:P, h:¬P ⊢ False
///
/// Measures whether the Alethe proof reconstruction pipeline (Path A) or
/// the native SmtBridge (Path B) produces a kernel proof, avoiding trustedAy.
/// We use a supported Prop FVar tautology so the tactic must stay on the
/// proof-producing ay/bridge lane instead of falling back through the
/// unsupported bare-constant path.
///
/// Uses the goal-local trust ledger plus the thread-local reconstruction-success
/// counter so the assertion stays stable under the broader parallel `-- smt`
/// suite while still proving this tactic-level case stayed on the checked
/// post-gate path.
#[test]
fn test_ay_decide_extract_only_tautology_reconstruction() {
    let env = setup_ay_env();
    let (p, p_decl) = prop_local_decl(94, "p");
    let target = ay_make_or(p.clone(), ay_make_not(p));

    reset_local_ay_reconstruction_success_counter();
    let mut state = ProofState::with_context(env, target, vec![p_decl]);

    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    ay_decide(&mut state, config).expect("ay ExtractOnly should prove P ∨ ¬P");
    assert!(state.is_complete(), "goal should be closed");

    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "supported Prop-FVar tautology should close without trustedAy"
    );
    let recon_count = local_ay_reconstruction_success_count();
    assert!(
        recon_count >= 1,
        "supported Prop-FVar tautology should increment the local ay reconstruction counter; got {recon_count}"
    );
}
