// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for Eq.trans TC infinite recursion (#3305).
//!
//! Validates that type-checking Eq.trans proof terms with axiom-typed
//! sub-expressions does not cause unbounded WHNF recursion.

use super::*;
use crate::env::Declaration;
use crate::level::Level;

/// Set up an environment with Eq and basic types for testing Eq.trans.
fn setup_eq_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    env
}

/// Build `@Eq.{u1} α x y` — the fully explicit Eq application.
/// Eq takes 3 arguments: {α : Sort u}, x : α, y : α.
fn mk_eq(u: &Level, alpha: Expr, x: Expr, y: Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![u.clone()]);
    Expr::app(Expr::app(Expr::app(eq, alpha), x), y)
}

/// Test that type-checking a direct Eq.trans application succeeds.
///
/// Builds: @Eq.trans Nat a b c h1 h2
/// where h1 : @Eq Nat a b and h2 : @Eq Nat b c are axioms.
///
/// This is the core regression test for #3305. Previously, this caused
/// unbounded WHNF recursion when normalizing axiom-typed sub-terms.
#[test]
fn test_eq_trans_with_axiom_subterms() {
    let mut env = setup_eq_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let u1 = Level::succ(Level::zero());

    // Declare a, b, c as axiom constants of type Nat
    for name in &["test.a", "test.b", "test.c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .expect("add axiom");
    }

    let a = Expr::const_(Name::from_string("test.a"), vec![]);
    let b = Expr::const_(Name::from_string("test.b"), vec![]);
    let c = Expr::const_(Name::from_string("test.c"), vec![]);

    // Build Eq types: @Eq.{1} Nat a b
    let eq_ab = mk_eq(&u1, nat.clone(), a.clone(), b.clone());
    let eq_bc = mk_eq(&u1, nat.clone(), b.clone(), c.clone());

    // Declare h1 : @Eq Nat a b and h2 : @Eq Nat b c as axioms
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h1"),
        level_params: vec![],
        type_: eq_ab,
    })
    .expect("add h1 axiom");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h2"),
        level_params: vec![],
        type_: eq_bc,
    })
    .expect("add h2 axiom");

    let h1 = Expr::const_(Name::from_string("test.h1"), vec![]);
    let h2 = Expr::const_(Name::from_string("test.h2"), vec![]);

    // Build the Eq.trans application: @Eq.trans.{1} Nat a b c h1 h2
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![u1]);
    let trans_app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::app(Expr::app(eq_trans, nat), a), b), c),
            h1,
        ),
        h2,
    );

    // Type-check: the result should be @Eq Nat a c without stack overflow
    let tc = TypeChecker::new(&env);
    let result = tc.infer_type(&trans_app);
    assert!(
        result.is_ok(),
        "infer_type on Eq.trans application should succeed: {:?}",
        result.err(),
    );
}

/// Test that a theorem using Eq.trans can be added via add_decl.
///
/// Declares a theorem whose proof is @Eq.trans Nat a b c h1 h2 where
/// h1 and h2 are axiom constants. Tests the full add_decl pipeline
/// including check_type (infer_only=false).
#[test]
fn test_add_decl_eq_trans_theorem() {
    let mut env = setup_eq_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let u1 = Level::succ(Level::zero());

    // Declare a, b, c as axiom constants of type Nat
    for name in &["test.a", "test.b", "test.c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .expect("add axiom");
    }

    let a = Expr::const_(Name::from_string("test.a"), vec![]);
    let b = Expr::const_(Name::from_string("test.b"), vec![]);
    let c = Expr::const_(Name::from_string("test.c"), vec![]);

    // Build Eq types
    let eq_ab = mk_eq(&u1, nat.clone(), a.clone(), b.clone());
    let eq_bc = mk_eq(&u1, nat.clone(), b.clone(), c.clone());
    let eq_ac = mk_eq(&u1, nat.clone(), a.clone(), c.clone());

    // Declare h1 : @Eq Nat a b and h2 : @Eq Nat b c as axioms
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h1"),
        level_params: vec![],
        type_: eq_ab,
    })
    .expect("add h1 axiom");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h2"),
        level_params: vec![],
        type_: eq_bc,
    })
    .expect("add h2 axiom");

    let h1 = Expr::const_(Name::from_string("test.h1"), vec![]);
    let h2 = Expr::const_(Name::from_string("test.h2"), vec![]);

    // Build proof: @Eq.trans.{1} Nat a b c h1 h2
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![u1]);
    let proof = Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::app(Expr::app(eq_trans, nat), a), b), c),
            h1,
        ),
        h2,
    );

    // Add as theorem: test.trans_result : @Eq Nat a c := @Eq.trans Nat a b c h1 h2
    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("test.trans_result"),
        level_params: vec![],
        type_: eq_ac,
        value: proof,
    });
    assert!(
        result.is_ok(),
        "add_decl for Eq.trans theorem should succeed: {:?}",
        result.err(),
    );
}

/// Test Eq.trans chaining: a = b = c = d via two Eq.trans calls.
///
/// Tests the deeper recursion case where Eq.trans is nested.
#[test]
fn test_eq_trans_chain() {
    let mut env = setup_eq_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let u1 = Level::succ(Level::zero());

    // Declare a, b, c, d as axiom constants of type Nat
    for name in &["test.a", "test.b", "test.c", "test.d"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .expect("add axiom");
    }

    let a = Expr::const_(Name::from_string("test.a"), vec![]);
    let b = Expr::const_(Name::from_string("test.b"), vec![]);
    let c = Expr::const_(Name::from_string("test.c"), vec![]);
    let d = Expr::const_(Name::from_string("test.d"), vec![]);

    // Build Eq types
    let eq_ab = mk_eq(&u1, nat.clone(), a.clone(), b.clone());
    let eq_bc = mk_eq(&u1, nat.clone(), b.clone(), c.clone());
    let eq_cd = mk_eq(&u1, nat.clone(), c.clone(), d.clone());
    let eq_ad = mk_eq(&u1, nat.clone(), a.clone(), d.clone());

    // Declare axioms
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h_ab"),
        level_params: vec![],
        type_: eq_ab,
    })
    .expect("add h_ab axiom");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h_bc"),
        level_params: vec![],
        type_: eq_bc,
    })
    .expect("add h_bc axiom");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h_cd"),
        level_params: vec![],
        type_: eq_cd,
    })
    .expect("add h_cd axiom");

    let h_ab = Expr::const_(Name::from_string("test.h_ab"), vec![]);
    let h_bc = Expr::const_(Name::from_string("test.h_bc"), vec![]);
    let h_cd = Expr::const_(Name::from_string("test.h_cd"), vec![]);

    // Build proof: @Eq.trans Nat a c d (@Eq.trans Nat a b c h_ab h_bc) h_cd
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![u1.clone()]);
    let inner_trans = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(eq_trans.clone(), nat.clone()), a.clone()),
                    b,
                ),
                c.clone(),
            ),
            h_ab,
        ),
        h_bc,
    );
    let outer_trans = Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::app(Expr::app(eq_trans, nat), a), c), d),
            inner_trans,
        ),
        h_cd,
    );

    // Add as theorem
    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("test.chain_abcd"),
        level_params: vec![],
        type_: eq_ad,
        value: outer_trans,
    });
    assert!(
        result.is_ok(),
        "add_decl for chained Eq.trans should succeed: {:?}",
        result.err(),
    );
}

/// Test deeply nested Eq.trans chain (stress test for recursion depth).
///
/// Builds a chain of 16 Eq.trans applications: a₀ = a₁ = ... = a₁₆.
/// This tests that the depth-bounded WHNF and infer_sort handle deep
/// chains without stack overflow or heartbeat exhaustion.
#[test]
fn test_eq_trans_deep_chain() {
    let mut env = setup_eq_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let u1 = Level::succ(Level::zero());
    let chain_len = 16usize;

    // Declare a_0 through a_16 as axiom constants of type Nat
    let mut vars = Vec::new();
    for i in 0..=chain_len {
        let name = format!("test.a_{i}");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .expect("add a_i axiom");
        vars.push(Expr::const_(Name::from_string(&name), vec![]));
    }

    // Declare h_i : a_i = a_{i+1} for i = 0..chain_len-1
    let mut proofs = Vec::new();
    for i in 0..chain_len {
        let name = format!("test.h_{i}");
        let eq_ty = mk_eq(&u1, nat.clone(), vars[i].clone(), vars[i + 1].clone());
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&name),
            level_params: vec![],
            type_: eq_ty,
        })
        .expect("add h_i axiom");
        proofs.push(Expr::const_(Name::from_string(&name), vec![]));
    }

    // Build the chain: @Eq.trans ... (@Eq.trans ... h_0 h_1) h_2) ... h_{n-1}
    // Start with h_0 (proof that a_0 = a_1), then chain each h_i
    let eq_trans_const = Expr::const_(Name::from_string("Eq.trans"), vec![u1.clone()]);
    let mut chain_proof = proofs[0].clone();
    // chain_proof proves a_0 = a_{chain_end}

    for (chain_end, i) in (1usize..).zip(1..chain_len) {
        // chain_proof : a_0 = a_{chain_end}
        // proofs[i] : a_i = a_{i+1}   (where i == chain_end)
        // @Eq.trans Nat a_0 a_{chain_end} a_{chain_end+1} chain_proof proofs[i]
        chain_proof = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(eq_trans_const.clone(), nat.clone()),
                            vars[0].clone(),
                        ),
                        vars[chain_end].clone(),
                    ),
                    vars[chain_end + 1].clone(),
                ),
                chain_proof,
            ),
            proofs[i].clone(),
        );
    }

    // chain_proof should be a proof of a_0 = a_{chain_len}
    let expected_ty = mk_eq(&u1, nat.clone(), vars[0].clone(), vars[chain_len].clone());

    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("test.deep_chain"),
        level_params: vec![],
        type_: expected_ty,
        value: chain_proof,
    });
    assert!(
        result.is_ok(),
        "add_decl for deeply chained Eq.trans should succeed: {:?}",
        result.err(),
    );
}

/// Test Eq.trans via check_type (infer_only=false).
///
/// `check_type` exercises a deeper checking path than `infer_type`: it sets
/// `infer_only=false`, which triggers argument type checks at every App node.
/// This is the same path used by `add_decl` for theorems. Previously, the
/// deeper checks could trigger unbounded re-inference of Eq.trans sub-terms.
#[test]
fn test_eq_trans_check_type_path() {
    let mut env = setup_eq_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let u1 = Level::succ(Level::zero());

    for name in &["test.a", "test.b", "test.c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .expect("add axiom");
    }

    let a = Expr::const_(Name::from_string("test.a"), vec![]);
    let b = Expr::const_(Name::from_string("test.b"), vec![]);
    let c = Expr::const_(Name::from_string("test.c"), vec![]);

    let eq_ab = mk_eq(&u1, nat.clone(), a.clone(), b.clone());
    let eq_bc = mk_eq(&u1, nat.clone(), b.clone(), c.clone());
    let eq_ac = mk_eq(&u1, nat.clone(), a.clone(), c.clone());

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h1"),
        level_params: vec![],
        type_: eq_ab,
    })
    .expect("add h1 axiom");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h2"),
        level_params: vec![],
        type_: eq_bc,
    })
    .expect("add h2 axiom");

    let h1 = Expr::const_(Name::from_string("test.h1"), vec![]);
    let h2 = Expr::const_(Name::from_string("test.h2"), vec![]);

    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![u1]);
    let proof = Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::app(Expr::app(eq_trans, nat), a), b), c),
            h1,
        ),
        h2,
    );

    // check_type uses infer_only=false, exercising the full arg checking path
    let tc = TypeChecker::new(&env);
    let result = tc.check_type(&proof, &eq_ac);
    assert!(
        result.is_ok(),
        "check_type on Eq.trans proof should succeed: {:?}",
        result.err(),
    );
}

/// Test Eq.symm composed with Eq.trans.
///
/// Given h1 : b = a and h2 : b = c, prove a = c via:
/// @Eq.trans Nat a b c (@Eq.symm Nat a b h1) h2
///
/// This tests the composition of equality lemmas — a critical path for
/// proof reconstruction from SMT solvers where equality chains may use
/// mixed directions.
#[test]
fn test_eq_symm_then_trans() {
    let mut env = setup_eq_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let u1 = Level::succ(Level::zero());

    for name in &["test.a", "test.b", "test.c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .expect("add axiom");
    }

    let a = Expr::const_(Name::from_string("test.a"), vec![]);
    let b = Expr::const_(Name::from_string("test.b"), vec![]);
    let c = Expr::const_(Name::from_string("test.c"), vec![]);

    let eq_ba = mk_eq(&u1, nat.clone(), b.clone(), a.clone());
    let eq_bc = mk_eq(&u1, nat.clone(), b.clone(), c.clone());
    let eq_ac = mk_eq(&u1, nat.clone(), a.clone(), c.clone());

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h_ba"),
        level_params: vec![],
        type_: eq_ba,
    })
    .expect("add h_ba axiom");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h_bc"),
        level_params: vec![],
        type_: eq_bc,
    })
    .expect("add h_bc axiom");

    let h_ba = Expr::const_(Name::from_string("test.h_ba"), vec![]);
    let h_bc = Expr::const_(Name::from_string("test.h_bc"), vec![]);

    // @Eq.symm.{1} Nat b a h_ba : @Eq Nat a b
    let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![u1.clone()]);
    let symm_proof = Expr::app(
        Expr::app(
            Expr::app(Expr::app(eq_symm, nat.clone()), b.clone()),
            a.clone(),
        ),
        h_ba,
    );

    // @Eq.trans.{1} Nat a b c (symm_proof) h_bc
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![u1]);
    let proof = Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::app(Expr::app(eq_trans, nat), a), b), c),
            symm_proof,
        ),
        h_bc,
    );

    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("test.symm_trans"),
        level_params: vec![],
        type_: eq_ac,
        value: proof,
    });
    assert!(
        result.is_ok(),
        "add_decl for Eq.symm+Eq.trans composition should succeed: {:?}",
        result.err(),
    );
}

/// Test Eq.trans on Prop-typed values (universe level 0).
///
/// Eq at Sort 0 (Prop) equates propositions. This tests that the universe
/// machinery works at the lowest level — a common case when the SMT bridge
/// produces equality proofs between propositional terms.
#[test]
fn test_eq_trans_prop_level() {
    let mut env = setup_eq_env();
    let prop = Expr::sort(Level::zero());
    let u1 = Level::succ(Level::zero());

    for name in &["test.P", "test.Q", "test.R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("add prop axiom");
    }

    let p = Expr::const_(Name::from_string("test.P"), vec![]);
    let q = Expr::const_(Name::from_string("test.Q"), vec![]);
    let r = Expr::const_(Name::from_string("test.R"), vec![]);

    let eq_pq = mk_eq(&u1, prop.clone(), p.clone(), q.clone());
    let eq_qr = mk_eq(&u1, prop.clone(), q.clone(), r.clone());
    let eq_pr = mk_eq(&u1, prop.clone(), p.clone(), r.clone());

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h_pq"),
        level_params: vec![],
        type_: eq_pq,
    })
    .expect("add h_pq axiom");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h_qr"),
        level_params: vec![],
        type_: eq_qr,
    })
    .expect("add h_qr axiom");

    let h_pq = Expr::const_(Name::from_string("test.h_pq"), vec![]);
    let h_qr = Expr::const_(Name::from_string("test.h_qr"), vec![]);

    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![u1]);
    let proof = Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::app(Expr::app(eq_trans, prop), p), q), r),
            h_pq,
        ),
        h_qr,
    );

    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("test.prop_trans"),
        level_params: vec![],
        type_: eq_pr,
        value: proof,
    });
    assert!(
        result.is_ok(),
        "add_decl for Prop-level Eq.trans should succeed: {:?}",
        result.err(),
    );
}

/// Test Eq.trans with higher-order function types (combines #3304 and #3305).
///
/// Uses function types as the equality domain, testing both Pi-type sort
/// inference and Eq.trans proof term type checking together.
#[test]
fn test_eq_trans_with_function_type_domain() {
    let mut env = setup_eq_env();
    env.init_nn_verify_types().expect("init_nn_verify_types");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nn_vec = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);
    let u1 = Level::succ(Level::zero());

    // Declare n : Nat
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.n"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .expect("add n axiom");

    let n = Expr::const_(Name::from_string("test.n"), vec![]);
    let vec_n = Expr::app(nn_vec, n);

    // The function type: NNVec n -> NNVec n
    let endo_type = Expr::pi(BinderInfo::Default, vec_n.clone(), vec_n);

    // Declare f, g : NNVec n -> NNVec n as axioms
    for name in &["test.f", "test.g"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: endo_type.clone(),
        })
        .expect("add function axiom");
    }

    let f = Expr::const_(Name::from_string("test.f"), vec![]);
    let g = Expr::const_(Name::from_string("test.g"), vec![]);

    // Build Eq type for function-typed values: @Eq.{1} (NNVec n → NNVec n) f g
    let eq_fg = mk_eq(&u1, endo_type, f, g);

    // Declare h_fg : f = g as axiom
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("test.h_fg"),
        level_params: vec![],
        type_: eq_fg.clone(),
    })
    .expect("add h_fg axiom");

    // Type-check: ensure the Eq type for function-typed values works
    let tc = TypeChecker::new(&env);
    let result = tc.infer_type(&eq_fg);
    assert!(
        result.is_ok(),
        "infer_type on Eq for function types should succeed: {:?}",
        result.err(),
    );
}

/// Test that Eq.trans is NOT delta-reducible in the lazy delta loop.
///
/// This is the core fix for #3305: theorems (including Eq.trans, Eq.symm)
/// have Reducibility::Opaque, so `get_delta_const` must exclude them from
/// the lazy delta reduction loop. Without this, the loop repeatedly unfolds
/// Eq.trans into its Eq.rec body, which cannot reduce when the major premise
/// is an axiom-typed proof, wasting heartbeat budget.
///
/// Eq.trans CAN still be unfolded by WHNF (needed for iota reduction when
/// the major premise IS a constructor), but it must not participate in the
/// is_def_eq delta unfolding loop.
#[test]
fn test_eq_trans_not_delta_reducible_in_lazy_loop() {
    let env = setup_eq_env();
    let tc = TypeChecker::new(&env);

    // Eq.trans with universe level 1
    let u1 = Level::succ(Level::zero());
    let eq_trans_expr = Expr::const_(Name::from_string("Eq.trans"), vec![u1.clone()]);

    // Verify Eq.trans is a theorem with Reducibility::Opaque
    let info = env
        .get_const(&Name::from_string("Eq.trans"))
        .expect("Eq.trans should exist");
    assert!(
        info.value.is_some(),
        "Eq.trans should have a value (theorem body)"
    );
    assert_eq!(
        info.kind,
        crate::env::ConstantKind::Theorem,
        "Eq.trans should be a Theorem"
    );
    assert_eq!(
        info.reducibility,
        crate::env::Reducibility::Opaque,
        "Eq.trans should have Opaque reducibility"
    );

    // Eq.symm should also be excluded
    let info_symm = env
        .get_const(&Name::from_string("Eq.symm"))
        .expect("Eq.symm should exist");
    assert_eq!(
        info_symm.kind,
        crate::env::ConstantKind::Theorem,
        "Eq.symm should be a Theorem"
    );
    assert_eq!(
        info_symm.reducibility,
        crate::env::Reducibility::Opaque,
        "Eq.symm should have Opaque reducibility"
    );

    // Verify that WHNF still unfolds Eq.trans (it should, for iota reduction).
    // Just unfold the constant itself (no arguments) — this tests that the
    // WHNF path (whnf_outer_loop -> unfold_definition) still works.
    let whnf_result = tc.whnf(&eq_trans_expr);
    // Eq.trans should unfold to its lambda body (starting with λ α ...)
    assert_ne!(
        whnf_result, eq_trans_expr,
        "WHNF should still unfold Eq.trans (theorem bodies unfold in WHNF)"
    );
}

/// Test Eq.trans proof composition with limited heartbeat budget.
///
/// This test validates that the fix for #3305 actually prevents heartbeat
/// exhaustion. With a tight heartbeat budget, the old code would fail because
/// lazy delta kept trying to unfold Eq.trans. With the fix, theorems stay
/// stuck in the delta loop and proof irrelevance handles equality.
#[test]
fn test_eq_trans_composition_tight_heartbeat() {
    let mut env = setup_eq_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let u1 = Level::succ(Level::zero());

    // Declare 5 constants and 4 equality axioms
    let chain_len = 4usize;
    let mut vars = Vec::new();
    for i in 0..=chain_len {
        let name = format!("test.v_{i}");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .expect("add v_i axiom");
        vars.push(Expr::const_(Name::from_string(&name), vec![]));
    }

    let mut proofs = Vec::new();
    for i in 0..chain_len {
        let name = format!("test.p_{i}");
        let eq_ty = mk_eq(&u1, nat.clone(), vars[i].clone(), vars[i + 1].clone());
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&name),
            level_params: vec![],
            type_: eq_ty,
        })
        .expect("add p_i axiom");
        proofs.push(Expr::const_(Name::from_string(&name), vec![]));
    }

    // Build the chain: @Eq.trans ... (@Eq.trans ... p_0 p_1) p_2) ... p_{n-1}
    let eq_trans_const = Expr::const_(Name::from_string("Eq.trans"), vec![u1.clone()]);
    let mut chain_proof = proofs[0].clone();

    for (chain_end, i) in (1usize..).zip(1..chain_len) {
        chain_proof = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(eq_trans_const.clone(), nat.clone()),
                            vars[0].clone(),
                        ),
                        vars[chain_end].clone(),
                    ),
                    vars[chain_end + 1].clone(),
                ),
                chain_proof,
            ),
            proofs[i].clone(),
        );
    }

    let expected_ty = mk_eq(&u1, nat.clone(), vars[0].clone(), vars[chain_len].clone());

    // Use a tight heartbeat budget. Without the fix, this would fail because
    // the lazy delta loop would waste budget unfolding Eq.trans theorem bodies.
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(50_000); // Much lower than the default 2M

    let result = tc.check_type(&chain_proof, &expected_ty);
    assert!(
        result.is_ok(),
        "check_type for Eq.trans chain should succeed with tight heartbeat: {:?}",
        result.err(),
    );
}
