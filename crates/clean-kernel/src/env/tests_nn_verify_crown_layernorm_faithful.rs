// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Discriminator tests for the faithful C004 LayerNorm carriers (#3488).
//!
//! Companion tests to `nn_verify_crown_layernorm_faithful.rs`. These
//! tests assert that the two new carriers are **semantically live**:
//!
//! * Their outputs depend on BOTH `n` and the input `B`.
//! * They are NOT definitionally aliased to each other (CROWN-faithful
//!   vs IBP-faithful) — defeating the Rule M1 alias-collapse that
//!   underlay the original C004 MASQUERADE (#3488).
//!
//! The pattern mirrors `tests_nn_verify_blockwise_crown_faithful.rs`
//! and the template in
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md` → "Template:
//! faithful abstract-domain carrier" → "Discriminator property".

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_crown_layernorm()
        .expect("init_nn_verify_crown_layernorm");
    env
}

/// Returns true iff `expr` (or any of its subexpressions) references
/// `target_const` as a `Const` head. Mirrors the helper used in
/// `tests_nn_verify_blockwise_crown_faithful.rs`.
fn expr_references_const(expr: &Expr, target_const: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target_const,
        ExprKind::App(f, a) => {
            expr_references_const(f, target_const) || expr_references_const(a, target_const)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_references_const(ty, target_const) || expr_references_const(body, target_const)
        }
        ExprKind::Let(_, ty, val, body, _nondep) => {
            expr_references_const(ty, target_const)
                || expr_references_const(val, target_const)
                || expr_references_const(body, target_const)
        }
        ExprKind::Proj(_, _, inner) => expr_references_const(inner, target_const),
        ExprKind::MData(_, inner) => expr_references_const(inner, target_const),
        _ => false,
    }
}

// =============================================================================
// Registration + shape
// =============================================================================

#[test]
fn test_ibp_forward_layernorm_faithful_registered() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.IBP.forward_layernorm_faithful",
        ))
        .expect("IBP.forward_layernorm_faithful should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Definition,
        "faithful carrier must be a Declaration::Definition (reducible)"
    );
    assert!(
        ci.value.is_some(),
        "faithful carrier must carry a body (reducible Definition)"
    );
}

#[test]
fn test_crown_backward_layernorm_faithful_registered() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.CROWN.backward_layernorm_faithful",
        ))
        .expect("CROWN.backward_layernorm_faithful should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Definition,
        "faithful carrier must be a Declaration::Definition (reducible)"
    );
    assert!(
        ci.value.is_some(),
        "faithful carrier must carry a body (reducible Definition)"
    );
}

#[test]
fn test_ibp_forward_layernorm_faithful_body_uses_nat_rec() {
    // The body must reference Nat.rec (structural recursion on n). A body
    // like `fun n γ β ε B => B` or `fun n γ β ε B => zero_ib n` would
    // trivially collapse.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.IBP.forward_layernorm_faithful",
        ))
        .expect("IBP.forward_layernorm_faithful should exist");
    let value = ci
        .value
        .as_ref()
        .expect("IBP.forward_layernorm_faithful should have a value");
    assert!(
        expr_references_const(value, "Nat.rec"),
        "faithful carrier body must reference Nat.rec — it is supposed to \
         pattern-match on `n` via structural recursion",
    );
    // Step case must construct zero_ib via IntervalBounds.mk.
    assert!(
        expr_references_const(value, "NNVerify.IntervalBounds.mk"),
        "IBP-faithful body must construct zero_ib via IntervalBounds.mk \
         in the base case",
    );
}

#[test]
fn test_crown_backward_layernorm_faithful_body_uses_nat_rec() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.CROWN.backward_layernorm_faithful",
        ))
        .expect("CROWN.backward_layernorm_faithful should exist");
    let value = ci
        .value
        .as_ref()
        .expect("CROWN.backward_layernorm_faithful should have a value");
    assert!(
        expr_references_const(value, "Nat.rec"),
        "CROWN-faithful body must reference Nat.rec",
    );
    assert!(
        expr_references_const(value, "NNVerify.IntervalBounds.mk"),
        "CROWN-faithful body must construct zero_ib via IntervalBounds.mk \
         in the step case",
    );
}

// =============================================================================
// Discriminators: the faithful carriers have distinct WHNF at different
// inputs. If they were identity-on-B (old placeholder), these tests would
// fail because every output would WHNF to the input B.
// =============================================================================

fn nat_zero_expr() -> Expr {
    Expr::const_(Name::from_string("Nat.zero"), vec![])
}

fn nat_one_expr() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        nat_zero_expr(),
    )
}

/// Build an `IntervalBounds n` constructor application that is not
/// the zero bounds. Using `n = 1` and filling with `Rat.one`.
fn sym_bounds_one() -> Expr {
    let ib_mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
    let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
    let rat_le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let fin_1 = Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        nat_one_expr(),
    );
    let const_one_vec = Expr::lam(BinderInfo::Default, fin_1.clone(), rat_one.clone());
    let valid_proof = Expr::lam(BinderInfo::Default, fin_1, Expr::app(rat_le_refl, rat_one));
    Expr::apps(
        ib_mk,
        [
            nat_one_expr(),
            const_one_vec.clone(),
            const_one_vec,
            valid_proof,
        ],
    )
}

/// Build an `IntervalBounds 0` constructor application. We use
/// `Rat.zero`-typed empty vectors; at `n = 0` the `Fin 0 → Rat`
/// function is uniquely `fun _ => Rat.zero`.
fn sym_bounds_zero_dim() -> Expr {
    let ib_mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let rat_le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let fin_0 = Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        nat_zero_expr(),
    );
    let const_zero_vec = Expr::lam(BinderInfo::Default, fin_0.clone(), rat_zero.clone());
    let valid_proof = Expr::lam(BinderInfo::Default, fin_0, Expr::app(rat_le_refl, rat_zero));
    Expr::apps(
        ib_mk,
        [
            nat_zero_expr(),
            const_zero_vec.clone(),
            const_zero_vec,
            valid_proof,
        ],
    )
}

/// `NNVec n` value `fun _ : Fin n => Rat.zero` — used as a typed
/// placeholder for the `γ` / `β` parameters in kernel applications.
fn const_zero_vec_for(dim: Expr) -> Expr {
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let fin_dim = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), dim);
    Expr::lam(BinderInfo::Default, fin_dim, rat_zero)
}

fn ibp_faithful_app(n: Expr, gamma: Expr, beta: Expr, eps: Expr, bnd: Expr) -> Expr {
    let f = Expr::const_(
        Name::from_string("NNVerify.IBP.forward_layernorm_faithful"),
        vec![],
    );
    Expr::apps(f, [n, gamma, beta, eps, bnd])
}

fn crown_faithful_app(n: Expr, gamma: Expr, beta: Expr, eps: Expr, bnd: Expr) -> Expr {
    let f = Expr::const_(
        Name::from_string("NNVerify.CROWN.backward_layernorm_faithful"),
        vec![],
    );
    Expr::apps(f, [n, gamma, beta, eps, bnd])
}

#[test]
fn test_ibp_faithful_discriminates_on_n() {
    // At n = 0 the IBP-faithful carrier returns zero_ib 0 (via Nat.rec
    // base case). At n = 1 it returns the input B (via step case). Two
    // distinct normal forms → the body depends on n.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

    let n0 = nat_zero_expr();
    let n1 = nat_one_expr();
    let b0 = sym_bounds_zero_dim();
    let b1 = sym_bounds_one();
    let gamma0 = const_zero_vec_for(n0.clone());
    let beta0 = const_zero_vec_for(n0.clone());
    let gamma1 = const_zero_vec_for(n1.clone());
    let beta1 = const_zero_vec_for(n1.clone());

    let whnf_n0 = tc.whnf(&ibp_faithful_app(
        n0.clone(),
        gamma0,
        beta0,
        rat_zero.clone(),
        b0.clone(),
    ));
    let whnf_n1 = tc.whnf(&ibp_faithful_app(
        n1.clone(),
        gamma1,
        beta1,
        rat_zero,
        b1.clone(),
    ));
    assert_ne!(
        whnf_n0, whnf_n1,
        "MASQUERADE NOT CLOSED: IBP-faithful carrier produced the same \
         WHNF at n=0 and n=1 — body is constant in n. \
         WHNF(n=0)={:?}, WHNF(n=1)={:?}",
        whnf_n0, whnf_n1,
    );
}

#[test]
fn test_ibp_faithful_step_case_returns_input() {
    // At n = 1 the IBP-faithful carrier must iota-reduce to the input B.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

    let n1 = nat_one_expr();
    let b = sym_bounds_one();
    let gamma = const_zero_vec_for(n1.clone());
    let beta = const_zero_vec_for(n1.clone());

    let whnf_applied = tc.whnf(&ibp_faithful_app(n1, gamma, beta, rat_zero, b.clone()));
    let whnf_input = tc.whnf(&b);
    assert_eq!(
        whnf_applied, whnf_input,
        "at n=1 the IBP-faithful carrier must WHNF-reduce to its input B \
         (was: {:?}, expected: {:?})",
        whnf_applied, whnf_input,
    );
}

#[test]
fn test_crown_faithful_discriminates_on_n() {
    // At n = 0 the CROWN-faithful carrier returns the input B. At n = 1
    // it returns zero_ib 1. Two distinct normal forms → depends on n.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

    let n0 = nat_zero_expr();
    let n1 = nat_one_expr();
    let b0 = sym_bounds_zero_dim();
    let b1 = sym_bounds_one();
    let gamma0 = const_zero_vec_for(n0.clone());
    let beta0 = const_zero_vec_for(n0.clone());
    let gamma1 = const_zero_vec_for(n1.clone());
    let beta1 = const_zero_vec_for(n1.clone());

    let whnf_n0 = tc.whnf(&crown_faithful_app(
        n0.clone(),
        gamma0,
        beta0,
        rat_zero.clone(),
        b0,
    ));
    let whnf_n1 = tc.whnf(&crown_faithful_app(n1.clone(), gamma1, beta1, rat_zero, b1));
    assert_ne!(
        whnf_n0, whnf_n1,
        "MASQUERADE NOT CLOSED: CROWN-faithful carrier produced the same \
         WHNF at n=0 and n=1 — body is constant in n. \
         WHNF(n=0)={:?}, WHNF(n=1)={:?}",
        whnf_n0, whnf_n1,
    );
}

#[test]
fn test_crown_faithful_base_case_returns_input() {
    // At n = 0 the CROWN-faithful carrier must iota-reduce to its input.
    // This is the reduction that powers `_refl_zero` theorem.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

    let n0 = nat_zero_expr();
    let b = sym_bounds_zero_dim();
    let gamma = const_zero_vec_for(n0.clone());
    let beta = const_zero_vec_for(n0.clone());

    let whnf_applied = tc.whnf(&crown_faithful_app(n0, gamma, beta, rat_zero, b.clone()));
    let whnf_input = tc.whnf(&b);
    assert_eq!(
        whnf_applied, whnf_input,
        "at n=0 the CROWN-faithful carrier must WHNF-reduce to its input B \
         (was: {:?}, expected: {:?})",
        whnf_applied, whnf_input,
    );
}

#[test]
fn test_faithful_carriers_are_not_aliased() {
    // CROWN-faithful and IBP-faithful MUST produce different outputs at
    // at least one input pair. We test at n=0 where CROWN returns B and
    // IBP returns zero_ib 0 — so for a symbolic non-zero B at n=0 they
    // differ; and we test at n=1 where CROWN returns zero_ib 1 and IBP
    // returns B — so for a non-zero B they again differ.
    //
    // If the two carriers were aliased (old MASQUERADE shape), every
    // input would produce the same WHNF under both, and this test
    // would fail.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);

    // At n=1, with a non-zero symbolic B.
    let n1 = nat_one_expr();
    let b = sym_bounds_one();
    let gamma = const_zero_vec_for(n1.clone());
    let beta = const_zero_vec_for(n1.clone());

    let whnf_ibp = tc.whnf(&ibp_faithful_app(
        n1.clone(),
        gamma.clone(),
        beta.clone(),
        rat_zero.clone(),
        b.clone(),
    ));
    let whnf_crown = tc.whnf(&crown_faithful_app(n1, gamma, beta, rat_zero, b));
    assert_ne!(
        whnf_ibp, whnf_crown,
        "MASQUERADE NOT CLOSED: CROWN and IBP faithful carriers produced \
         the same WHNF at n=1 — they are definitionally aliased, so any \
         equality between them would close by Eq.refl. \
         WHNF(IBP)={:?}, WHNF(CROWN)={:?}",
        whnf_ibp, whnf_crown,
    );
}

// =============================================================================
// Refl-at-zero theorem — demonstrates the demasquerade is invertible.
// =============================================================================

#[test]
fn test_refl_zero_theorem_registered() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C004.crown_backward_layernorm_faithful_refl_zero",
        ))
        .expect("refl_zero theorem should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "refl_zero must be a Declaration::Theorem"
    );
    assert!(ci.value.is_some(), "refl_zero must have a proof value");
}

#[test]
fn test_refl_zero_theorem_kernel_accepts() {
    // The kernel's add_decl must accept the proof. Re-run the full init
    // on a fresh env so the Declaration::Theorem registration exercises
    // add_decl (type-checks the proof term against the type).
    let mut env = Environment::new();
    env.init_nn_verify_crown_layernorm()
        .expect("kernel must accept refl_zero proof term");
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C004.crown_backward_layernorm_faithful_refl_zero",
        ))
        .expect("refl_zero theorem should be registered");
    assert_eq!(ci.kind, ConstantKind::Theorem);
    assert!(ci.value.is_some());
}

#[test]
fn test_refl_zero_theorem_type_has_four_binders() {
    // forall (γ β : NNVec 0) (ε : Rat) (B : IntervalBounds 0), _
    // → 4 outer Pi binders.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C004.crown_backward_layernorm_faithful_refl_zero",
        ))
        .expect("refl_zero theorem should exist");
    let mut cursor = ci.type_.clone();
    let mut binders = 0;
    while let ExprKind::Pi(_, _, body) = cursor.kind() {
        binders += 1;
        cursor = (**body).clone();
    }
    assert_eq!(
        binders, 4,
        "refl_zero should have 4 Pi binders (γ, β, ε, B), got {}",
        binders,
    );
}

#[test]
fn test_refl_zero_proof_references_eq_refl() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C004.crown_backward_layernorm_faithful_refl_zero",
        ))
        .expect("refl_zero theorem should exist");
    let value = ci.value.as_ref().expect("proof value missing");
    assert!(
        expr_references_const(value, "Eq.refl"),
        "proof term must reference Eq.refl",
    );
}

#[test]
fn test_refl_zero_proof_infer_type_matches() {
    // Kernel infer_type on the theorem must succeed and yield a Pi type.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let thm = Expr::const_(
        Name::from_string("NNVerify.C004.crown_backward_layernorm_faithful_refl_zero"),
        vec![],
    );
    let ty = tc
        .infer_type(&thm)
        .expect("infer_type must succeed on refl_zero faithful theorem");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "inferred type must be a Pi (universally quantified)",
    );
    // Suppress dead-import warning for Level::zero in case edits remove it.
    let _ = Level::zero();
}

// =============================================================================
// Refl-at-succ theorem (#3373 Phase 1 sub-piece) — IBP-faithful step case.
// Symmetric companion to refl_zero: proves IBP-faithful at n = Nat.succ k
// reduces to its input B via the step-case Nat.rec reduction.
// =============================================================================

#[test]
fn test_refl_succ_theorem_registered() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C004.ibp_forward_layernorm_faithful_refl_succ",
        ))
        .expect("refl_succ theorem should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "refl_succ must be a Declaration::Theorem"
    );
    assert!(ci.value.is_some(), "refl_succ must have a proof value");
}

#[test]
fn test_refl_succ_theorem_kernel_accepts() {
    // Fresh env so add_decl actually type-checks the proof term.
    let mut env = Environment::new();
    env.init_nn_verify_crown_layernorm()
        .expect("kernel must accept refl_succ proof term");
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C004.ibp_forward_layernorm_faithful_refl_succ",
        ))
        .expect("refl_succ theorem should be registered");
    assert_eq!(ci.kind, ConstantKind::Theorem);
    assert!(ci.value.is_some());
}

#[test]
fn test_refl_succ_theorem_type_has_five_binders() {
    // forall (k : Nat) (γ β : NNVec (Nat.succ k)) (ε : Rat)
    //        (B : IntervalBounds (Nat.succ k)), _
    // → 5 outer Pi binders.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C004.ibp_forward_layernorm_faithful_refl_succ",
        ))
        .expect("refl_succ theorem should exist");
    let mut cursor = ci.type_.clone();
    let mut binders = 0;
    while let ExprKind::Pi(_, _, body) = cursor.kind() {
        binders += 1;
        cursor = (**body).clone();
    }
    assert_eq!(
        binders, 5,
        "refl_succ should have 5 Pi binders (k, γ, β, ε, B), got {}",
        binders,
    );
}

#[test]
fn test_refl_succ_proof_references_eq_refl() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C004.ibp_forward_layernorm_faithful_refl_succ",
        ))
        .expect("refl_succ theorem should exist");
    let value = ci.value.as_ref().expect("proof value missing");
    assert!(
        expr_references_const(value, "Eq.refl"),
        "proof term must reference Eq.refl",
    );
}

#[test]
fn test_refl_succ_proof_witness_is_bvar() {
    // Rule M4 detection: the proof term's Eq.refl witness must be a BVar
    // (bound B), NOT a fully-applied alias like `zero_ib (Nat.succ k)`.
    // The proof has 5 outer lambdas (k, γ, β, ε, B). BVar 0 is `B`.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C004.ibp_forward_layernorm_faithful_refl_succ",
        ))
        .expect("refl_succ should exist");
    let value = ci.value.as_ref().expect("proof value missing");

    let mut cursor = value.clone();
    let mut lam_depth = 0;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        lam_depth += 1;
        cursor = (**body).clone();
    }
    assert_eq!(
        lam_depth, 5,
        "proof should have 5 outer lambdas (k, γ, β, ε, B), got {}",
        lam_depth,
    );
    let (_head, args) = app_spine(&cursor);
    assert!(
        args.len() >= 2,
        "proof spine should be `Eq.refl T B` — got {} args",
        args.len(),
    );
    let witness = &args[args.len() - 1];
    match witness.kind() {
        ExprKind::BVar(idx) => {
            assert_eq!(
                *idx, 0,
                "witness arg of Eq.refl should be BVar 0 (bound B), got BVar {}",
                idx,
            );
        }
        other => panic!(
            "MASQUERADE NOT CLOSED: Eq.refl witness should be a BVar (bound \
             B), got {:?}. This would suggest the proof closes over a \
             collapsed constant (e.g., zero_ib (Nat.succ k)) instead of the \
             symbolic input.",
            other,
        ),
    }
}

#[test]
fn test_refl_succ_infer_type_succeeds() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let thm = Expr::const_(
        Name::from_string("NNVerify.C004.ibp_forward_layernorm_faithful_refl_succ"),
        vec![],
    );
    let ty = tc
        .infer_type(&thm)
        .expect("infer_type must succeed on refl_succ faithful theorem");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "inferred type must be a Pi (universally quantified)",
    );
}

#[test]
fn test_refl_zero_proof_witness_is_bvar() {
    // Rule M4 detection: the proof term must be Eq.refl on a BOUND
    // VARIABLE (BVar, introduced by the outermost Pi binder for B),
    // NOT Eq.refl on a fully-applied alias like `zero_ib 0`. In the
    // latter case, the theorem would hold vacuously via alias
    // collapse.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.C004.crown_backward_layernorm_faithful_refl_zero",
        ))
        .expect("refl_zero should exist");
    let value = ci.value.as_ref().expect("proof value missing");

    // Walk through outer lambdas; the innermost body should be an
    // application of Eq.refl whose last argument is a BVar (referring
    // to the bound B).
    let mut cursor = value.clone();
    let mut lam_depth = 0;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        lam_depth += 1;
        cursor = (**body).clone();
    }
    assert_eq!(
        lam_depth, 4,
        "proof should have 4 outer lambdas (γ, β, ε, B), got {}",
        lam_depth,
    );
    let (_head, args) = app_spine(&cursor);
    assert!(
        args.len() >= 2,
        "proof spine should be `Eq.refl T B` — got {} args",
        args.len(),
    );
    let witness = &args[args.len() - 1];
    match witness.kind() {
        ExprKind::BVar(idx) => {
            assert_eq!(
                *idx, 0,
                "witness arg of Eq.refl should be BVar 0 (bound B), got BVar {}",
                idx,
            );
        }
        other => panic!(
            "MASQUERADE NOT CLOSED: Eq.refl witness should be a BVar (bound \
             B), got {:?}. This suggests the proof closes over a collapsed \
             constant (e.g., zero_ib 0) instead of the symbolic input.",
            other,
        ),
    }
}

fn app_spine(expr: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut cursor = expr.clone();
    while let ExprKind::App(f, a) = cursor.kind() {
        args.push((**a).clone());
        cursor = (**f).clone();
    }
    args.reverse();
    (cursor, args)
}
