// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::cdcl::{Lit, Var};
use crate::smt::TermId;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, ExprKind, FVarId, Level};
use std::collections::HashMap;

/// Build a minimal environment where `A : Type` is declared.
/// Allows `infer_sort(A)` to succeed in proof builder tests.
fn env_with_type_a() -> Environment {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add_decl A should succeed");
    env
}

#[test]
fn test_proof_step_refl() {
    let step = ProofStep::refl(TermId(0));
    assert!(matches!(step, ProofStep::Refl(TermId(0))));
}

#[test]
fn test_proof_step_symm_optimization() {
    // symm(refl) = refl
    let refl = ProofStep::refl(TermId(0));
    let symm = ProofStep::symm(refl);
    assert!(matches!(symm, ProofStep::Refl(_)));

    // symm(symm(p)) = p
    let hyp = ProofStep::hypothesis(FVarId::new(0));
    let s1 = ProofStep::symm(hyp.clone());
    let s2 = ProofStep::symm(s1);
    assert!(matches!(s2, ProofStep::Hypothesis(_)));
}

#[test]
fn test_proof_step_trans_optimization() {
    let hyp = ProofStep::hypothesis(FVarId::new(0));
    let refl = ProofStep::refl(TermId(0));

    // trans(refl, p) = p
    let t1 = ProofStep::trans(refl.clone(), hyp.clone());
    assert!(matches!(t1, ProofStep::Hypothesis(_)));

    // trans(p, refl) = p
    let t2 = ProofStep::trans(hyp.clone(), refl);
    assert!(matches!(t2, ProofStep::Hypothesis(_)));
}

#[test]
fn test_proof_trace_record() {
    let mut trace = ProofTrace::new();

    let idx = trace.record_union(
        0,
        1,
        UnionReason::Asserted {
            hypothesis: Some(FVarId::new(0)),
            lhs: TermId(0),
            rhs: TermId(1),
        },
    );

    assert_eq!(idx, 0);
    assert_eq!(trace.get_proof_index(0, 1), Some(0));
    assert_eq!(trace.get_proof_index(1, 0), Some(0)); // Both directions indexed
}

#[test]
fn test_proof_trace_build_direct() {
    let mut trace = ProofTrace::new();

    trace.record_union(
        0,
        1,
        UnionReason::Asserted {
            hypothesis: Some(FVarId::new(42)),
            lhs: TermId(0),
            rhs: TermId(1),
        },
    );

    let proof = trace.build_proof(0, 1);
    assert!(
        matches!(proof, Some(ProofStep::Hypothesis(fvar)) if fvar.as_u64() == 42),
        "expected Some(Hypothesis(FVarId(42))), got: {:?}",
        proof
    );
}

#[test]
fn test_proof_trace_build_flipped() {
    let mut trace = ProofTrace::new();

    trace.record_union(
        0,
        1,
        UnionReason::Asserted {
            hypothesis: Some(FVarId::new(42)),
            lhs: TermId(0),
            rhs: TermId(1),
        },
    );

    // Request proof in opposite direction
    let proof = trace.build_proof(1, 0);
    assert!(
        matches!(proof, Some(ProofStep::Symm(_))),
        "expected Some(Symm(_)), got: {:?}",
        proof
    );
}

#[test]
fn test_proof_trace_build_transitive() {
    let mut trace = ProofTrace::new();

    // 0 = 1
    trace.record_union(
        0,
        1,
        UnionReason::Asserted {
            hypothesis: Some(FVarId::new(0)),
            lhs: TermId(0),
            rhs: TermId(1),
        },
    );

    // 1 = 2
    trace.record_union(
        1,
        2,
        UnionReason::Asserted {
            hypothesis: Some(FVarId::new(1)),
            lhs: TermId(1),
            rhs: TermId(2),
        },
    );

    // Should be able to prove 0 = 2 via transitivity
    let proof = trace.build_proof(0, 2);
    assert!(
        matches!(proof, Some(ProofStep::Trans(_, _))),
        "expected Some(Trans(_, _)), got: {:?}",
        proof
    );
}

#[test]
fn test_proof_trace_truncate_removes_tail_indices_and_preserves_prefix() {
    let mut trace = ProofTrace::new();

    trace.record_union(
        0,
        1,
        UnionReason::Asserted {
            hypothesis: Some(FVarId::new(0)),
            lhs: TermId(0),
            rhs: TermId(1),
        },
    );
    let checkpoint = trace.len();

    trace.record_union(
        1,
        2,
        UnionReason::Asserted {
            hypothesis: Some(FVarId::new(1)),
            lhs: TermId(1),
            rhs: TermId(2),
        },
    );

    trace.truncate(checkpoint);

    assert_eq!(trace.len(), checkpoint);
    assert_eq!(trace.get_proof_index(0, 1), Some(0));
    assert_eq!(trace.get_proof_index(1, 0), Some(0));
    assert_eq!(trace.get_proof_index(1, 2), None);
    assert_eq!(trace.get_proof_index(2, 1), None);
    assert!(
        matches!(trace.get_reason(0), Some(UnionReason::Asserted { hypothesis: Some(fvar), .. }) if fvar.as_u64() == 0),
        "expected the surviving prefix edge to keep its original reason"
    );
    assert!(trace.get_reason(1).is_none());
    assert!(
        matches!(trace.build_proof(0, 1), Some(ProofStep::Hypothesis(fvar)) if fvar.as_u64() == 0),
        "expected the truncated prefix edge to remain reconstructable"
    );
    assert!(
        trace.build_proof(1, 2).is_none(),
        "expected the truncated suffix edge to be removed from proof lookup"
    );
}

#[test]
fn test_proof_builder_refl() {
    let mut term_to_expr = HashMap::new();
    let mut term_to_type = HashMap::new();

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let ty_a = Expr::const_(Name::from_string("A"), vec![]);

    term_to_expr.insert(TermId(0), a.clone());
    term_to_type.insert(TermId(0), ty_a);

    let env = env_with_type_a();
    let builder = ProofBuilder::with_env(&term_to_expr, &term_to_type, &env);
    let step = ProofStep::refl(TermId(0));

    let proof = builder
        .build(&step)
        .expect("ProofBuilder should produce proof for Refl step");
    match proof.kind() {
        ExprKind::App(_f, arg) => {
            // Should be (Eq.refl A) applied to a
            assert!(matches!(arg.kind(), ExprKind::Const(n, _) if n.to_string() == "a"));
        }
        _ => panic!("Expected App, got {proof:?}"),
    }
}

#[test]
fn test_proof_builder_hypothesis() {
    let term_to_expr = HashMap::new();
    let term_to_type = HashMap::new();

    let builder = ProofBuilder::new(&term_to_expr, &term_to_type);
    let step = ProofStep::hypothesis(FVarId::new(42));

    let proof = builder.build(&step);
    assert!(
        proof
            .as_ref()
            .ok()
            .map(|e| matches!(e.kind(), ExprKind::FVar(fvar) if fvar.as_u64() == 42))
            .unwrap_or(false),
        "expected Ok(FVar(42)), got: {:?}",
        proof
    );
}

// Tests for #210 and #211 fixes

#[test]
fn test_asserted_without_hypothesis_returns_none() {
    // Issue #210: Assertions without hypothesis should fail proof reconstruction
    // rather than generating unverified Axiom placeholders
    let mut trace = ProofTrace::new();

    // Record assertion with NO hypothesis and different lhs/rhs
    trace.record_union(
        0,
        1,
        UnionReason::Asserted {
            hypothesis: None,
            lhs: TermId(0),
            rhs: TermId(1), // Different from lhs
        },
    );

    // Proof reconstruction should return None (not an Axiom)
    let proof = trace.build_proof(0, 1);
    assert!(
        proof.is_none(),
        "Assertions without hypothesis must not produce proof"
    );
}

#[test]
fn test_asserted_reflexive_without_hypothesis_succeeds() {
    // Reflexive assertions (lhs == rhs) should still work even without hypothesis
    let mut trace = ProofTrace::new();

    trace.record_union(
        0,
        1,
        UnionReason::Asserted {
            hypothesis: None,
            lhs: TermId(0),
            rhs: TermId(0), // Same as lhs - reflexive
        },
    );

    let proof = trace.build_proof(0, 1);
    assert!(
        matches!(proof, Some(ProofStep::Refl(_))),
        "expected Some(Refl(_)), got: {:?}",
        proof
    );
}

#[test]
fn test_congruence_with_missing_arg_proofs_returns_none() {
    // Issue #210: Congruence with expected args but missing proofs should fail
    let mut trace = ProofTrace::new();

    // Record congruence with arg_reasons pointing to non-existent steps
    trace.record_union(
        0,
        1,
        UnionReason::Congruence {
            func: "test_func".to_string(),
            app1: 0,
            app2: 1,
            arg_reasons: vec![999], // Non-existent step index
        },
    );

    let proof = trace.build_proof(0, 1);
    assert!(
        proof.is_none(),
        "Congruence with missing arg proofs must not produce proof"
    );
}

#[test]
fn test_congruence_with_nullary_function_succeeds() {
    // Nullary functions (empty arg_reasons) should still work
    let mut trace = ProofTrace::new();

    trace.record_union(
        0,
        1,
        UnionReason::Congruence {
            func: "nullary_const".to_string(),
            app1: 0,
            app2: 1,
            arg_reasons: vec![], // No args for nullary function
        },
    );

    let proof = trace.build_proof(0, 1);
    assert!(
        matches!(&proof, Some(ProofStep::Congr(_, args)) if args.is_empty()),
        "expected Some(Congr(_, [])), got: {:?}",
        proof
    );
}

/// Build an env with Nat + Nat.add for congruence proof tests (#2305).
fn setup_nat_add_env() -> (Environment, Expr) {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add Nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_add_ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.add"),
        level_params: vec![],
        type_: nat_add_ty,
    })
    .expect("add Nat.add");
    (env, nat)
}

#[test]
fn test_multi_arg_congruence_proof_structure() {
    // Issue #211: Multi-argument congruence should use congr, not just congrArg
    // Requires env with Nat and Nat.add for universe level inference (#2305).
    let (env, nat) = setup_nat_add_env();

    let mut term_to_expr = HashMap::new();
    let mut term_to_type = HashMap::new();

    // Set up terms
    let a1 = Expr::const_(Name::from_string("a1"), vec![]);
    let a2 = Expr::const_(Name::from_string("a2"), vec![]);
    let b1 = Expr::const_(Name::from_string("b1"), vec![]);
    let b2 = Expr::const_(Name::from_string("b2"), vec![]);

    term_to_expr.insert(TermId(0), a1);
    term_to_expr.insert(TermId(1), a2);
    term_to_expr.insert(TermId(2), b1);
    term_to_expr.insert(TermId(3), b2);
    term_to_type.insert(TermId(0), nat.clone());
    term_to_type.insert(TermId(1), nat.clone());
    term_to_type.insert(TermId(2), nat.clone());
    term_to_type.insert(TermId(3), nat);

    // Register hypothesis canonical directions so step_span can recover
    // a₁, a₂ from ProofStep::Hypothesis (needed for implicit args in #2103).
    let mut eq_hypotheses = HashMap::new();
    eq_hypotheses.insert((TermId(0), TermId(1)), FVarId::new(0)); // h_a : a1 = a2
    eq_hypotheses.insert((TermId(2), TermId(3)), FVarId::new(1)); // h_b : b1 = b2
    let builder = ProofBuilder::with_hypotheses(&term_to_expr, &term_to_type, &env, &eq_hypotheses);

    // Build a 2-arg congruence proof: f a1 b1 = f a2 b2
    // with proofs h_a : a1 = a2, h_b : b1 = b2
    let h_a = ProofStep::hypothesis(FVarId::new(0));
    let h_b = ProofStep::hypothesis(FVarId::new(1));
    let nat_add_expr = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let step = ProofStep::congr(nat_add_expr, vec![h_a, h_b]);

    let proof = builder.build(&step);
    assert!(proof.is_ok(), "Multi-arg congruence should produce proof");

    // Structure: @congr.{u,v} α β f₁ f₂ a₁ a₂ (congrArg ...) h_b
    // Outer head is congr with all implicit + explicit args (#2103).
    let proof_expr = proof.unwrap();
    let (name, levels) = head_const_info(&proof_expr);
    assert_eq!(name, "congr");
    assert_eq!(levels, 2, "congr should have 2 universe levels");

    // The congrArg proof is the second-to-last arg (hf in @congr ... hf ha)
    if let ExprKind::App(outer_fn, _ha) = proof_expr.kind() {
        if let ExprKind::App(_, hf) = outer_fn.kind() {
            let (inner_name, inner_levels) = head_const_info(hf);
            assert_eq!(inner_name, "congrArg");
            assert_eq!(inner_levels, 2, "congrArg should have 2 universe levels");
        } else {
            panic!("Expected nested App for hf");
        }
    } else {
        panic!("Expected App, got {proof_expr:?}");
    }
}

#[test]
fn test_proof_reconstruction_error_display() {
    // Test that error messages are useful
    let err1 = ProofReconstructionError::MissingHypothesis {
        lhs: TermId(1),
        rhs: TermId(2),
    };
    // TermId Display produces "tN" format
    assert!(err1.to_string().contains("t1"));
    assert!(err1.to_string().contains("t2"));

    let err2 = ProofReconstructionError::EmptyCongruenceArgs {
        func: "test".to_string(),
    };
    assert!(err2.to_string().contains("test"));

    let err3 = ProofReconstructionError::NoProofPath { ec1: 5, ec2: 10 };
    assert!(err3.to_string().contains("5"));
    assert!(err3.to_string().contains("10"));
}

#[test]
fn test_proof_builder_nullary_congr_without_env_returns_err() {
    // Without an environment, nullary congruence cannot determine the
    // function's type. It correctly returns Err (fail-safe) rather than
    // producing an ill-typed proof with Expr::type_() as the type parameter.
    let term_to_expr = HashMap::new();
    let term_to_type = HashMap::new();

    let builder = ProofBuilder::new(&term_to_expr, &term_to_type);

    // Build a nullary congruence: const_f = const_f
    let step = ProofStep::congr(Expr::const_(Name::from_string("const_f"), vec![]), vec![]);

    let proof = builder.build(&step);
    assert!(
        proof.is_err(),
        "Nullary congruence without env should return Err (fail-safe)"
    );
}

#[test]
fn test_proof_builder_nullary_congr_with_env_produces_eq_refl() {
    // With an environment containing the constant, nullary congruence
    // correctly produces Eq.refl with the constant's actual type.
    use clean_kernel::Declaration;

    let mut env = Environment::new();

    // Declare Nat : Type first so const_f's type is valid
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add_decl Nat should succeed");

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    // Declare const_f : Nat in the environment
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("const_f"),
        level_params: vec![],
        type_: nat_ty.clone(),
    })
    .expect("add_decl const_f should succeed");

    let term_to_expr = HashMap::new();
    let term_to_type = HashMap::new();

    let builder = ProofBuilder::with_env(&term_to_expr, &term_to_type, &env);

    // Build a nullary congruence: const_f = const_f
    let step = ProofStep::congr(Expr::const_(Name::from_string("const_f"), vec![]), vec![]);

    let proof = builder.build(&step);
    assert!(
        proof.is_ok(),
        "Nullary congruence with env should produce Eq.refl proof"
    );

    // The proof should be @Eq.refl.{u} Nat const_f
    // Structure: App(App(Eq.refl_u, Nat), const_f)
    let proof_expr = proof.unwrap();
    match proof_expr.kind() {
        ExprKind::App(func, arg) => {
            // arg should be const_f
            match arg.kind() {
                ExprKind::Const(name, _) => {
                    assert_eq!(name.to_string(), "const_f");
                }
                _ => panic!("Expected const_f in Eq.refl application"),
            }
            // func should be App(Eq.refl_u, Nat) — verify type is Nat, not Type
            match func.kind() {
                ExprKind::App(eq_refl, ty_arg) => {
                    match eq_refl.kind() {
                        ExprKind::Const(name, _) => {
                            assert_eq!(name.to_string(), "Eq.refl");
                        }
                        _ => panic!("Expected Eq.refl const, got {eq_refl:?}"),
                    }
                    match ty_arg.kind() {
                        ExprKind::Const(name, _) => {
                            assert_eq!(
                                name.to_string(),
                                "Nat",
                                "Type parameter should be Nat from env, not Type"
                            );
                        }
                        _ => panic!("Expected Nat type parameter, got {ty_arg:?}"),
                    }
                }
                _ => panic!("Expected App(Eq.refl, Nat), got {func:?}"),
            }
        }
        _ => panic!("Expected App for Eq.refl, got {proof_expr:?}"),
    }
}

/// Extract the head constant name and universe level count from a proof expr.
/// Walks through App nodes to find the innermost Const.
fn head_const_info(expr: &Expr) -> (String, usize) {
    let mut current = expr;
    while let ExprKind::App(func, _) = current.kind() {
        current = func;
    }
    match current.kind() {
        ExprKind::Const(name, levels) => (name.to_string(), levels.len()),
        _ => panic!("Expected Const at head, got {current:?}"),
    }
}

/// Issue #211 verification: check universe levels in multi-arg congruence proofs.
///
/// Verifies mk_congr_multi uses correct universe levels.
/// Both congrArg and congr require two universe parameters (u, v).
#[test]
fn test_multi_arg_congruence_universe_levels() {
    let (env, nat) = setup_nat_add_env();
    let mut term_to_expr = HashMap::new();
    let mut term_to_type = HashMap::new();
    // Term expressions needed for implicit args (#2103)
    term_to_expr.insert(TermId(0), Expr::const_(Name::from_string("a1"), vec![]));
    term_to_expr.insert(TermId(1), Expr::const_(Name::from_string("a2"), vec![]));
    term_to_expr.insert(TermId(2), Expr::const_(Name::from_string("b1"), vec![]));
    term_to_expr.insert(TermId(3), Expr::const_(Name::from_string("b2"), vec![]));
    term_to_type.insert(TermId(0), nat.clone());
    term_to_type.insert(TermId(1), nat.clone());
    term_to_type.insert(TermId(2), nat.clone());
    term_to_type.insert(TermId(3), nat.clone());
    let mut eq_hypotheses = HashMap::new();
    eq_hypotheses.insert((TermId(0), TermId(1)), FVarId::new(0));
    eq_hypotheses.insert((TermId(2), TermId(3)), FVarId::new(1));
    let builder = ProofBuilder::with_hypotheses(&term_to_expr, &term_to_type, &env, &eq_hypotheses);

    let h_a = ProofStep::hypothesis(FVarId::new(0));
    let h_b = ProofStep::hypothesis(FVarId::new(1));
    let nat_add_expr = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let step = ProofStep::congr(nat_add_expr, vec![h_a, h_b]);
    let proof_expr = builder.build(&step).expect("congr proof should build");

    // Structure: @congr.{u,v} α β f₁ f₂ a₁ a₂ (congrArg ...) h_b (#2103)
    let (outer_name, outer_levels) = head_const_info(&proof_expr);
    assert_eq!(outer_name, "congr");
    assert_eq!(outer_levels, 2, "congr should receive 2 universe levels");

    // congrArg proof is second-to-last arg (hf in @congr ... hf ha)
    if let ExprKind::App(outer_fn, _ha) = proof_expr.kind() {
        if let ExprKind::App(_, hf) = outer_fn.kind() {
            let (inner_name, inner_levels) = head_const_info(hf);
            assert_eq!(inner_name, "congrArg");
            assert_eq!(inner_levels, 2, "congrArg should receive 2 universe levels");
        } else {
            panic!("Expected nested App");
        }
    } else {
        panic!("Expected App");
    }
}

/// Count the number of arguments applied to a proof term's head constant.
/// e.g., App(App(App(Eq.trans, α), a), b) → 3 args applied to Eq.trans.
fn count_app_args(expr: &Expr) -> usize {
    let mut count = 0;
    let mut current = expr;
    while let ExprKind::App(func, _arg) = current.kind() {
        count += 1;
        current = func;
    }
    count
}

/// Helper to set up ProofBuilder with hypothesis tracking for arity tests.
fn setup_builder_with_hyps() -> (
    HashMap<TermId, Expr>,
    HashMap<TermId, Expr>,
    HashMap<(TermId, TermId), FVarId>,
) {
    let mut term_to_expr = HashMap::new();
    let mut term_to_type = HashMap::new();
    let mut eq_hyps = HashMap::new();

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    term_to_expr.insert(TermId(0), a);
    term_to_expr.insert(TermId(1), b);
    term_to_expr.insert(TermId(2), c);
    term_to_type.insert(TermId(0), ty_a.clone());
    term_to_type.insert(TermId(1), ty_a.clone());
    term_to_type.insert(TermId(2), ty_a);

    // h1 : a = b, h2 : b = c
    eq_hyps.insert((TermId(0), TermId(1)), FVarId::new(10));
    eq_hyps.insert((TermId(1), TermId(2)), FVarId::new(11));

    (term_to_expr, term_to_type, eq_hyps)
}

/// Verify ProofStep::Congr preserves universe levels in function Expr.
/// AC #4 for #2401: at least one test with a universe-polymorphic function.
#[test]
fn test_congr_preserves_universe_levels() {
    // Construct a function Expr with non-empty universe levels, e.g., List.cons.{u}
    let u = Level::param(Name::from_string("u"));
    let func_expr = Expr::const_(Name::from_string("List.cons"), vec![u.clone()]);

    // Create a Congr step carrying the universe-polymorphic function
    let h = ProofStep::hypothesis(FVarId::new(99));
    let step = ProofStep::congr(func_expr.clone(), vec![h]);

    // Verify the Congr variant preserves the function Expr with levels
    match &step {
        ProofStep::Congr(expr, args) => {
            // The function Expr must carry the universe level
            match expr.kind() {
                ExprKind::Const(name, levels) => {
                    assert_eq!(name.to_string(), "List.cons");
                    assert_eq!(levels.len(), 1, "List.cons should have 1 universe level");
                    assert_eq!(levels[0], u, "Universe level should be param 'u'");
                }
                _ => panic!("Congr func_expr should be Const, got {expr:?}"),
            }
            assert_eq!(args.len(), 1);
        }
        _ => panic!("Expected Congr, got {step:?}"),
    }

    // Also verify Axiom carries universe levels
    let ax = ProofStep::Axiom(
        "Eq.rec".to_string(),
        vec![
            Level::param(Name::from_string("u_1")),
            Level::param(Name::from_string("u_2")),
        ],
    );
    match &ax {
        ProofStep::Axiom(name, levels) => {
            assert_eq!(name, "Eq.rec");
            assert_eq!(levels.len(), 2, "Eq.rec should have 2 universe params");
        }
        _ => panic!("Expected Axiom, got {ax:?}"),
    }
}

/// Verify @Eq.symm.{u} α a b h produces exactly 4 arguments.
#[test]
fn test_proof_builder_symm_arity() {
    let (term_to_expr, term_to_type, eq_hyps) = setup_builder_with_hyps();
    let env = env_with_type_a();
    let builder = ProofBuilder {
        term_to_expr: &term_to_expr,
        term_to_type: &term_to_type,
        env: Some(&env),
        hyp_terms: eq_hyps
            .iter()
            .map(|(&(t1, t2), &fvar)| (fvar, (t1, t2)))
            .collect(),
    };

    // Symm(Hypothesis(h1)) where h1 : a = b → should produce b = a
    let step = ProofStep::Symm(Box::new(ProofStep::Hypothesis(FVarId::new(10))));
    let proof = builder
        .build(&step)
        .expect("Should produce proof for Symm(Hypothesis)");

    // @Eq.symm.{u} α a b h — 4 arguments applied
    let arity = count_app_args(&proof);
    assert_eq!(
        arity, 4,
        "Eq.symm must have 4 args (@Eq.symm.{{u}} α a b h), got {arity}"
    );

    // Head should be Eq.symm
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string() == "Eq.symm"),
        "Head should be Eq.symm, got {head:?}"
    );
}

/// Verify @Eq.trans.{u} α a b c h₁ h₂ produces exactly 6 arguments.
#[test]
fn test_proof_builder_trans_arity() {
    let (term_to_expr, term_to_type, eq_hyps) = setup_builder_with_hyps();
    let env = env_with_type_a();
    let builder = ProofBuilder {
        term_to_expr: &term_to_expr,
        term_to_type: &term_to_type,
        env: Some(&env),
        hyp_terms: eq_hyps
            .iter()
            .map(|(&(t1, t2), &fvar)| (fvar, (t1, t2)))
            .collect(),
    };

    // Trans(Hypothesis(h1), Hypothesis(h2)) where h1 : a = b, h2 : b = c
    let step = ProofStep::Trans(
        Box::new(ProofStep::Hypothesis(FVarId::new(10))),
        Box::new(ProofStep::Hypothesis(FVarId::new(11))),
    );
    let proof = builder
        .build(&step)
        .expect("Should produce proof for Trans(Hypothesis, Hypothesis)");

    // @Eq.trans.{u} α a b c h₁ h₂ — 6 arguments applied
    let arity = count_app_args(&proof);
    assert_eq!(
        arity, 6,
        "Eq.trans must have 6 args (@Eq.trans.{{u}} α a b c h₁ h₂), got {arity}"
    );

    // Head should be Eq.trans
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string() == "Eq.trans"),
        "Head should be Eq.trans, got {head:?}"
    );
}

/// Verify nested Trans(Trans(h1, h2), h3) also produces correct arity at each level.
#[test]
fn test_proof_builder_nested_trans_arity() {
    let mut term_to_expr = HashMap::new();
    let mut term_to_type = HashMap::new();
    let mut eq_hyps: HashMap<(TermId, TermId), FVarId> = HashMap::new();

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);

    term_to_expr.insert(TermId(0), a);
    term_to_expr.insert(TermId(1), b);
    term_to_expr.insert(TermId(2), c);
    term_to_expr.insert(TermId(3), d);
    for i in 0..4 {
        term_to_type.insert(TermId(i), ty_a.clone());
    }

    // h1 : a = b, h2 : b = c, h3 : c = d
    eq_hyps.insert((TermId(0), TermId(1)), FVarId::new(10));
    eq_hyps.insert((TermId(1), TermId(2)), FVarId::new(11));
    eq_hyps.insert((TermId(2), TermId(3)), FVarId::new(12));

    let env = env_with_type_a();
    let builder = ProofBuilder {
        term_to_expr: &term_to_expr,
        term_to_type: &term_to_type,
        env: Some(&env),
        hyp_terms: eq_hyps
            .iter()
            .map(|(&(t1, t2), &fvar)| (fvar, (t1, t2)))
            .collect(),
    };

    // Trans(Trans(h1, h2), h3): (a = b, b = c) → a = c, then (a = c, c = d) → a = d
    let step = ProofStep::Trans(
        Box::new(ProofStep::Trans(
            Box::new(ProofStep::Hypothesis(FVarId::new(10))),
            Box::new(ProofStep::Hypothesis(FVarId::new(11))),
        )),
        Box::new(ProofStep::Hypothesis(FVarId::new(12))),
    );

    let proof = builder
        .build(&step)
        .expect("Should produce proof for nested Trans");

    // Outer: @Eq.trans.{u} α a c d (inner_proof) h₃ — 6 args
    let arity = count_app_args(&proof);
    assert_eq!(arity, 6, "Outer Eq.trans must have 6 args, got {arity}");

    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string() == "Eq.trans"),
        "Outer head should be Eq.trans, got {head:?}"
    );
}

/// Verify Eq.refl produces exactly 2 arguments.
#[test]
fn test_proof_builder_refl_arity() {
    let mut term_to_expr = HashMap::new();
    let mut term_to_type = HashMap::new();

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    term_to_expr.insert(TermId(0), a);
    term_to_type.insert(TermId(0), ty_a);

    let env = env_with_type_a();
    let builder = ProofBuilder::with_env(&term_to_expr, &term_to_type, &env);
    let step = ProofStep::refl(TermId(0));
    let proof = builder.build(&step).expect("Should produce Eq.refl proof");

    // @Eq.refl.{u} α a — 2 arguments
    let arity = count_app_args(&proof);
    assert_eq!(
        arity, 2,
        "Eq.refl must have 2 args (@Eq.refl.{{u}} α a), got {arity}"
    );
}

/// Verify ProofBuilder returns Err for Trans/Symm when hyp_terms is empty
/// (rather than producing incorrect arity).
#[test]
fn test_proof_builder_trans_without_hyp_terms_returns_err() {
    let mut term_to_expr = HashMap::new();
    let mut term_to_type = HashMap::new();

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    term_to_expr.insert(TermId(0), a);
    term_to_type.insert(TermId(0), ty_a);

    // No hyp_terms — step_span will return None for Hypothesis
    let builder = ProofBuilder::new(&term_to_expr, &term_to_type);

    let step = ProofStep::Trans(
        Box::new(ProofStep::Hypothesis(FVarId::new(10))),
        Box::new(ProofStep::Hypothesis(FVarId::new(11))),
    );

    let proof = builder.build(&step);
    assert!(
        proof.is_err(),
        "Trans without hyp_terms should return Err (not wrong-arity term)"
    );
}

// =========================================================================
// proof_coverage: ProofTrace::get_reason, build_proof no-path (#982)
// =========================================================================

#[test]
fn test_proof_trace_get_reason() {
    let mut trace = ProofTrace::new();

    let reason = UnionReason::Asserted {
        hypothesis: Some(FVarId::new(42)),
        lhs: TermId(0),
        rhs: TermId(1),
    };
    let idx = trace.record_union(10, 20, reason.clone());

    // Valid index returns the reason
    let got = trace.get_reason(idx);
    assert!(got.is_some(), "valid index should return reason");
    match got.unwrap() {
        UnionReason::Asserted {
            hypothesis,
            lhs,
            rhs,
        } => {
            assert_eq!(*hypothesis, Some(FVarId::new(42)));
            assert_eq!(*lhs, TermId(0));
            assert_eq!(*rhs, TermId(1));
        }
        other => panic!("Expected Asserted, got {other:?}"),
    }

    // Out of bounds returns None
    assert!(
        trace.get_reason(999).is_none(),
        "out-of-bounds clause id 999 should return None"
    );
}

#[test]
fn test_proof_trace_get_reason_congruence() {
    let mut trace = ProofTrace::new();

    let reason = UnionReason::Congruence {
        func: "f".to_string(),
        app1: 5,
        app2: 6,
        arg_reasons: vec![0],
    };
    let idx = trace.record_union(30, 40, reason);

    match trace.get_reason(idx) {
        Some(UnionReason::Congruence {
            func,
            app1,
            app2,
            arg_reasons,
        }) => {
            assert_eq!(func.as_str(), "f");
            assert_eq!(*app1, 5);
            assert_eq!(*app2, 6);
            assert_eq!(arg_reasons, &[0]);
        }
        other => panic!("Expected Congruence, got {other:?}"),
    }
}

#[test]
fn test_congruence_partial_arg_failure_returns_none() {
    // Algorithm audit: when N arg_reasons exist but only M<N succeed,
    // the congruence proof has wrong argument count. This must return None.
    // Bug: filter_map drops failed arg proofs silently, and only the
    // all-failed case is caught (line 651). Partial failure produces a
    // Congr with mismatched arg count → ill-typed kernel term.
    let mut trace = ProofTrace::new();

    // Step 0: valid arg proof (a = b via hypothesis)
    trace.record_union(
        10,
        11,
        UnionReason::Asserted {
            hypothesis: Some(FVarId::new(0)),
            lhs: TermId(10),
            rhs: TermId(11),
        },
    );

    // Step 1: unprovable arg (assertion without hypothesis, lhs != rhs)
    // step_to_proof returns None for this case
    trace.record_union(
        20,
        21,
        UnionReason::Asserted {
            hypothesis: None,
            lhs: TermId(20),
            rhs: TermId(21), // Different from lhs, no hypothesis → None
        },
    );

    // Step 2: congruence f(a,c) = f(b,d) with arg_reasons [0, 1]
    // Arg 0 succeeds (has hypothesis), arg 1 fails (no hypothesis, lhs != rhs)
    trace.record_union(
        0,
        1,
        UnionReason::Congruence {
            func: "f".to_string(),
            app1: 0,
            app2: 1,
            arg_reasons: vec![0, 1], // Step 0 succeeds, step 1 fails
        },
    );

    let proof = trace.build_proof(0, 1);
    // With the bug (filter_map + is_empty check), this returns
    // Some(Congr("f", [Hypothesis(0)])) with 1 arg proof for a 2-arg function.
    // Correct behavior: return None because arg proof count doesn't match.
    //
    // NOTE: This test documents the bug. If it fails with Some(Congr(...))
    // containing fewer args than arg_reasons, the fix is at proof.rs:651:
    //   change `arg_proofs.is_empty() && !arg_reasons.is_empty()`
    //   to     `arg_proofs.len() != arg_reasons.len()`
    assert!(
        proof.is_none(),
        "Partial arg proof failure must return None, got: {:?}",
        proof
    );
}

#[test]
fn test_proof_trace_build_proof_no_path() {
    let trace = ProofTrace::new();
    // No edges at all — should return None
    assert!(
        trace.build_proof(0, 1).is_none(),
        "empty trace should return None for any pair"
    );
}

#[test]
fn test_proof_trace_build_proof_disconnected_components() {
    let mut trace = ProofTrace::new();
    // Two disconnected edges: (0,1) and (2,3)
    trace.record_union(
        0,
        1,
        UnionReason::Asserted {
            hypothesis: Some(FVarId::new(0)),
            lhs: TermId(0),
            rhs: TermId(1),
        },
    );
    trace.record_union(
        2,
        3,
        UnionReason::Asserted {
            hypothesis: Some(FVarId::new(1)),
            lhs: TermId(2),
            rhs: TermId(3),
        },
    );

    // Path within a component should work
    let proof_01 = trace
        .build_proof(0, 1)
        .expect("path 0→1 should exist within component");
    assert!(
        !matches!(proof_01, ProofStep::Refl(_)),
        "proof 0→1 should be non-trivial (not reflexivity)"
    );
    let proof_23 = trace
        .build_proof(2, 3)
        .expect("path 2→3 should exist within component");
    assert!(
        !matches!(proof_23, ProofStep::Refl(_)),
        "proof 2→3 should be non-trivial (not reflexivity)"
    );

    // Path across components should fail
    assert!(
        trace.build_proof(0, 2).is_none(),
        "no path between disconnected components"
    );
    assert!(
        trace.build_proof(1, 3).is_none(),
        "no path between disconnected components"
    );
}

// === ProofForest tests ===

#[test]
fn test_proof_forest_direct_equality() {
    let mut forest = ProofForest::new();
    let a = TermId(0);
    let b = TermId(1);
    let lit = Lit::pos(Var::new(0));

    forest.record_merge(a, b, ForestReason::Asserted(lit), 0);

    let lits = forest
        .explain(a, b)
        .expect("connected terms should have explanation");
    assert_eq!(lits.len(), 1, "direct equality should have exactly one lit");
    assert_eq!(lits[0], lit);
}

#[test]
fn test_proof_forest_transitive_explanation() {
    // a = b, b = c → explain(a, c) should include both lits
    let mut forest = ProofForest::new();
    let a = TermId(0);
    let b = TermId(1);
    let c = TermId(2);
    let lit_ab = Lit::pos(Var::new(0));
    let lit_bc = Lit::pos(Var::new(1));

    forest.record_merge(a, b, ForestReason::Asserted(lit_ab), 0);
    forest.record_merge(b, c, ForestReason::Asserted(lit_bc), 0);

    let lits = forest
        .explain(a, c)
        .expect("transitive path a→b→c should have explanation");
    assert_eq!(
        lits.len(),
        2,
        "transitive equality needs both assertion lits"
    );
    assert!(lits.contains(&lit_ab));
    assert!(lits.contains(&lit_bc));
}

#[test]
fn test_proof_forest_reflexive() {
    let forest = ProofForest::new();
    let a = TermId(0);

    let lits = forest
        .explain(a, a)
        .expect("reflexive equality should always succeed");
    assert!(lits.is_empty(), "reflexive equality needs no lits");
}

#[test]
fn test_proof_forest_disconnected() {
    let mut forest = ProofForest::new();
    let a = TermId(0);
    let b = TermId(1);
    let c = TermId(2);
    let lit = Lit::pos(Var::new(0));

    forest.record_merge(a, b, ForestReason::Asserted(lit), 0);

    let explanation = forest.explain(a, c);
    assert!(
        matches!(explanation, Err(ExplainFailure::DisconnectedTerms)),
        "disconnected terms should return DisconnectedTerms, got: {:?}",
        explanation
    );
}

#[test]
fn test_proof_forest_backtrack() {
    let mut forest = ProofForest::new();
    let a = TermId(0);
    let b = TermId(1);
    let c = TermId(2);
    let lit_ab = Lit::pos(Var::new(0));
    let lit_bc = Lit::pos(Var::new(1));

    // Level 0: a = b
    forest.record_merge(a, b, ForestReason::Asserted(lit_ab), 0);
    let lits_ab = forest
        .explain(a, b)
        .expect("a=b should be connected at level 0");
    assert_eq!(lits_ab, vec![lit_ab]);

    // Level 1: b = c
    forest.record_merge(b, c, ForestReason::Asserted(lit_bc), 1);
    let lits_ac = forest
        .explain(a, c)
        .expect("a=c should be connected via a=b, b=c");
    assert!(lits_ac.contains(&lit_ab));
    assert!(lits_ac.contains(&lit_bc));

    // Backtrack to level 0
    forest.backtrack(0);

    // a = b still connected (level 0)
    let lits_ab_after = forest
        .explain(a, b)
        .expect("a=b should survive backtrack to level 0");
    assert_eq!(lits_ab_after, vec![lit_ab]);
    // a = c no longer connected (level 1 removed)
    assert!(
        matches!(forest.explain(a, c), Err(ExplainFailure::DisconnectedTerms)),
        "backtracked merge should be undone"
    );
}

#[test]
fn test_proof_forest_congruence_reason() {
    // f(a) = f(b) by congruence where a = b
    let mut forest = ProofForest::new();
    let a = TermId(0);
    let b = TermId(1);
    let fa = TermId(2);
    let fb = TermId(3);
    let lit_ab = Lit::pos(Var::new(0));

    // a = b directly
    forest.record_merge(a, b, ForestReason::Asserted(lit_ab), 0);
    // f(a) = f(b) by congruence on arg pair (a, b)
    forest.record_merge(fa, fb, ForestReason::Congruence(vec![(a, b)]), 0);

    let lits = forest
        .explain(fa, fb)
        .expect("congruence-connected terms should have explanation");
    // Congruence recursively explains arg pair (a, b) → lit_ab
    assert_eq!(lits.len(), 1);
    assert_eq!(lits[0], lit_ab);
}

#[test]
fn test_proof_forest_already_merged_noop() {
    let mut forest = ProofForest::new();
    let a = TermId(0);
    let b = TermId(1);
    let lit1 = Lit::pos(Var::new(0));
    let lit2 = Lit::pos(Var::new(1));

    forest.record_merge(a, b, ForestReason::Asserted(lit1), 0);
    // Second merge between a and b should be a no-op (same root)
    forest.record_merge(a, b, ForestReason::Asserted(lit2), 0);

    let lits = forest
        .explain(a, b)
        .expect("merged terms should have explanation");
    // Only the first merge's lit should appear
    assert_eq!(lits.len(), 1);
    assert_eq!(lits[0], lit1);
}

#[test]
fn test_proof_forest_congruence_with_disconnected_arg_returns_reason() {
    // Self-audit (#2352): if a congruence edge references arg pairs where
    // one pair is disconnected, explain must return a typed failure
    // (not partial lits).
    // Before the fix, collect_reasons_to_ancestor silently skipped
    // unexplainable arg pairs, producing incomplete (unsound) explanations.
    let mut forest = ProofForest::new();
    let a = TermId(0);
    let b = TermId(1);
    let c = TermId(2); // disconnected
    let d = TermId(3); // disconnected
    let fa = TermId(4);
    let fb = TermId(5);
    let lit_ab = Lit::pos(Var::new(0));

    // a = b connected
    forest.record_merge(a, b, ForestReason::Asserted(lit_ab), 0);
    // f(a,c) = f(b,d) by congruence on arg pairs [(a,b), (c,d)]
    // BUT c and d are NOT connected — this is a malformed congruence
    // (shouldn't happen in practice, but defense-in-depth matters)
    forest.record_merge(fa, fb, ForestReason::Congruence(vec![(a, b), (c, d)]), 0);

    let explanation = forest.explain(fa, fb);
    assert!(
        matches!(explanation, Err(ExplainFailure::CongruenceArgumentUnexplained)),
        "congruence with disconnected arg pair must return CongruenceArgumentUnexplained, got: {:?}",
        explanation
    );
}
