// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Discriminator tests for the Phase-3 `compose_faithful_succ_unfold`
//! promotion (#3533).
//!
//! The generic successor-unfold lemma `compose_faithful_succ_unfold`
//! promotes the degenerate `k = 0` `compose_faithful_zero_eq_input`
//! scaffolding to a statement that covers every `Nat.succ m` index.
//! Proof term is
//! `@Eq.refl.{1} (IB d) (cb m (compose_faithful d m cb B))` — the witness
//! is the CONSTRUCTED RHS, not a bound variable, so this cannot be the
//! degenerate `Eq.refl B` pattern. The kernel closes the equation by one
//! iota step on `Nat.rec` at the `Nat.succ` branch.
//!
//! These tests assert: (a) registration as `Declaration::Theorem`,
//! (b) kernel accepts the proof term on a fresh env, (c) transitive axiom
//! closure is a subset of `FOUNDATIONAL_AXIOMS` (zero domain-specific
//! axioms — genuinely constructive), (d) the proof's Eq.refl witness is
//! NOT a bound variable alone (catches regression to the k=0 BVar
//! pattern).
//!
//! Lives in its own file to keep
//! `tests_nn_verify_blockwise_crown_faithful.rs` under the 1000-line cap.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

const THEOREM_NAME: &str = "NNVerify.Block.compose_faithful_succ_unfold";

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("init_nn_verify_blockwise_crown_ext");
    env
}

/// Returns true iff `expr` (or any subexpression) references `target_const`
/// as a `Const` head.
fn expr_references_const(expr: &Expr, target_const: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target_const,
        ExprKind::App(f, a) => {
            expr_references_const(f, target_const) || expr_references_const(a, target_const)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_references_const(ty, target_const) || expr_references_const(body, target_const)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_references_const(ty, target_const)
                || expr_references_const(val, target_const)
                || expr_references_const(body, target_const)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            expr_references_const(inner, target_const)
        }
        _ => false,
    }
}

/// Peel an application spine into (head, args).
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

/// Peel outer lambdas, returning (innermost body, lambda depth).
fn peel_outer_lams(expr: &Expr) -> (Expr, usize) {
    let mut cursor = expr.clone();
    let mut depth = 0;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        depth += 1;
        cursor = (**body).clone();
    }
    (cursor, depth)
}

/// Fetch the registered theorem value or fail with a descriptive message.
fn get_theorem_value(env: &Environment) -> Expr {
    let ci = env
        .get_const(&Name::from_string(THEOREM_NAME))
        .expect("compose_faithful_succ_unfold should exist");
    ci.value
        .as_ref()
        .expect("compose_faithful_succ_unfold proof value missing")
        .clone()
}

// =============================================================================
// Registration + shape
// =============================================================================

#[test]
fn test_compose_faithful_succ_unfold_registered() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(THEOREM_NAME))
        .expect("compose_faithful_succ_unfold should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "compose_faithful_succ_unfold must be Declaration::Theorem (NOT an \
         axiom wrapper — Phase 3 promotion demands genuine Theorem)",
    );
    assert!(ci.value.is_some(), "theorem must carry a proof value");
}

#[test]
fn test_compose_faithful_succ_unfold_kernel_accepts() {
    // Fresh env re-runs `add_decl`, which type-checks the proof term
    // against the statement. The kernel must reduce the LHS
    // `compose_faithful d (Nat.succ m) cb B` to the RHS
    // `cb m (compose_faithful d m cb B)` via one iota step on Nat.rec
    // at the succ branch — if that iota were blocked, add_decl would
    // refuse the Eq.refl witness.
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("kernel must accept compose_faithful_succ_unfold proof term");
    let ci = env
        .get_const(&Name::from_string(THEOREM_NAME))
        .expect("compose_faithful_succ_unfold should be registered");
    assert_eq!(ci.kind, ConstantKind::Theorem);
}

#[test]
fn test_compose_faithful_succ_unfold_type_has_four_binders() {
    // Statement: forall (d m : Nat) (cb : Nat -> IB d -> IB d) (B : IB d),
    //   compose_faithful d (succ m) cb B = cb m (compose_faithful d m cb B)
    // — four outer Pi binders.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(THEOREM_NAME))
        .expect("compose_faithful_succ_unfold should exist");
    let mut cursor = ci.type_.clone();
    let mut binders = 0;
    while let ExprKind::Pi(_, _, body) = cursor.kind() {
        binders += 1;
        cursor = (**body).clone();
    }
    assert_eq!(
        binders, 4,
        "compose_faithful_succ_unfold should have 4 Pi binders (d, m, cb, B), \
         got {}",
        binders,
    );
}

#[test]
fn test_compose_faithful_succ_unfold_proof_references_compose_faithful() {
    // The proof's RHS witness is `cb m (compose_faithful d m cb B)`, so
    // the proof term MUST reference `compose_faithful` as a Const in its
    // VALUE (not just its type).
    let env = make_env();
    let value = get_theorem_value(&env);
    assert!(
        expr_references_const(&value, "NNVerify.Block.compose_faithful"),
        "proof term must reference compose_faithful (as the recursive \
         call in the RHS witness) — otherwise the \
         `cb m (compose_faithful ...)` spine collapsed to a constant",
    );
    assert!(
        expr_references_const(&value, "Eq.refl"),
        "proof term must reference Eq.refl",
    );
}

#[test]
fn test_compose_faithful_succ_unfold_infer_type_matches() {
    // Kernel infer_type on the theorem must succeed and yield the Pi type.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let thm = Expr::const_(Name::from_string(THEOREM_NAME), vec![]);
    let ty = tc
        .infer_type(&thm)
        .expect("infer_type must succeed on compose_faithful_succ_unfold");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "inferred type must be a Pi (universally quantified)",
    );
    // Suppress Level/BinderInfo-unused warnings in case imports change.
    let _ = Level::zero();
    let _ = BinderInfo::Default;
}

// =============================================================================
// Phase 3 witness check — the proof is NOT a bare BVar (no `k=0` regression).
// =============================================================================

/// Peel the outer lambdas of the proof term. Returns the innermost body.
/// Asserts there are exactly 4 lambdas (d, m, cb, B).
fn peel_proof_body(value: &Expr) -> Expr {
    let (body, depth) = peel_outer_lams(value);
    assert_eq!(
        depth, 4,
        "proof should have 4 outer lambdas (d, m, cb, B), got {}",
        depth,
    );
    body
}

/// Assert the head of the Eq.refl application is `Const(Eq.refl)`.
fn assert_head_is_eq_refl(head: &Expr) {
    match head.kind() {
        ExprKind::Const(name, _levels) => {
            assert_eq!(
                name.to_string(),
                "Eq.refl",
                "proof head must be Eq.refl, got {}",
                name,
            );
        }
        other => panic!("proof head must be Const(Eq.refl), got {:?}", other),
    }
}

/// Given the spine `Eq.refl T witness`, return the witness (last arg).
fn witness_of_eq_refl(args: &[Expr]) -> &Expr {
    assert!(
        args.len() >= 2,
        "proof spine should be `Eq.refl T witness` — got {} args",
        args.len(),
    );
    &args[args.len() - 1]
}

/// Assert the witness of Eq.refl is an App whose head is the bound `cb`
/// variable (BVar 1 under the d,m,cb,B lambda stack). Panics with a
/// Phase-3 regression message if the witness is a BVar directly.
fn assert_witness_is_cb_application(witness: &Expr) {
    match witness.kind() {
        ExprKind::App(_, _) => {
            let (w_head, _w_args) = app_spine(witness);
            match w_head.kind() {
                ExprKind::BVar(idx) => assert_eq!(
                    *idx, 1,
                    "witness head should be cb (BVar 1 under d,m,cb,B), \
                     got BVar {}",
                    idx,
                ),
                other => panic!(
                    "witness head should be the bound cb variable (BVar 1), \
                     got {:?}. If this is a collapsed constant the proof has \
                     regressed.",
                    other,
                ),
            }
        }
        ExprKind::BVar(idx) => panic!(
            "PHASE 3 REGRESSION: Eq.refl witness is a bare BVar({}), not \
             a constructed application. The theorem has collapsed back to \
             the `k = 0` identity pattern that \
             `compose_faithful_zero_eq_input` already covers — #3533 \
             Phase 3 promotion is NOT closed.",
            idx,
        ),
        other => panic!(
            "Eq.refl witness must be an App spine \
             `cb m (compose_faithful d m cb B)`, got {:?}",
            other,
        ),
    }
}

#[test]
fn test_compose_faithful_succ_unfold_proof_witness_is_constructed_term() {
    // Rule M4+ detection (stronger than the k=0 case): the proof term must
    // be `@Eq.refl.{1} (IB d) <RHS>` where <RHS> is the application
    // `cb m (compose_faithful d m cb B)` — i.e. an `App`/`App`/... spine,
    // NOT a bare `BVar`.
    let env = make_env();
    let value = get_theorem_value(&env);
    let body = peel_proof_body(&value);
    let (head, args) = app_spine(&body);
    assert_head_is_eq_refl(&head);
    let witness = witness_of_eq_refl(&args);
    assert_witness_is_cb_application(witness);
}

// =============================================================================
// Axiom-profile gate — the #3533 soundness acceptance criterion.
// =============================================================================

#[test]
fn test_compose_faithful_succ_unfold_axiom_deps_are_foundational() {
    // Phase 3 soundness gate: the transitive axiom closure of the new
    // theorem must be a subset of FOUNDATIONAL_AXIOMS. `axiom_deps()`
    // returns only NON-foundational (domain-specific) axioms — so an
    // empty set means the proof is genuinely constructive
    // (ProofQuality::Constructive, qualifies for the
    // clean-native.mathverse shard).
    //
    // If this assertion fails, the commit message MUST use "formalize" /
    // "register" instead of "prove" per design doc Proof Soundness Rules.
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(THEOREM_NAME))
        .expect("axiom_deps must resolve");
    assert!(
        deps.is_empty(),
        "compose_faithful_succ_unfold has domain-specific axiom \
         dependencies: {:?}. Phase 3 promotion requires ZERO domain \
         axioms — the proof term closes by a single iota step on Nat.rec \
         at the succ branch, using only FOUNDATIONAL_AXIOMS.",
        deps.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
    );
    let quality = env
        .proof_quality(&Name::from_string(THEOREM_NAME))
        .expect("proof_quality must resolve");
    assert!(
        matches!(quality, crate::env::ProofQuality::Constructive),
        "compose_faithful_succ_unfold must classify as \
         ProofQuality::Constructive for the clean-native shard to accept \
         it, got {:?}",
        quality,
    );
}

// =============================================================================
// Empirical iota — the LHS actually reduces to the RHS the proof builds.
// =============================================================================

/// Construct `@Block.compose_faithful d k cb B` as a kernel Expr.
fn cf_app(d: Expr, k: Expr, cb: Expr, b: Expr) -> Expr {
    let cf = Expr::const_(Name::from_string("NNVerify.Block.compose_faithful"), vec![]);
    Expr::apps(cf, [d, k, cb, b])
}

/// Build `zero_bounds_one` — a two-vector-of-zero IntervalBounds at dim 1.
/// The validity proof is schematic; only the constructor head matters for
/// WHNF comparison.
fn zero_bounds_one() -> Expr {
    let ib_mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
    let nat_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let rat_le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let fin_1 = Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        nat_one.clone(),
    );
    let const_zero_vec = Expr::lam(BinderInfo::Default, fin_1.clone(), rat_zero.clone());
    let valid_proof = Expr::lam(BinderInfo::Default, fin_1, Expr::app(rat_le_refl, rat_zero));
    Expr::apps(
        ib_mk,
        [nat_one, const_zero_vec.clone(), const_zero_vec, valid_proof],
    )
}

/// Symbolic `IntervalBounds 1` with 1-vectors — distinct from zero bounds.
fn sym_bounds_one() -> Expr {
    let ib_mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
    let nat_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
    let rat_le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let fin_1 = Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        nat_one.clone(),
    );
    let const_one_vec = Expr::lam(BinderInfo::Default, fin_1.clone(), rat_one.clone());
    let valid_proof = Expr::lam(BinderInfo::Default, fin_1, Expr::app(rat_le_refl, rat_one));
    Expr::apps(
        ib_mk,
        [nat_one, const_one_vec.clone(), const_one_vec, valid_proof],
    )
}

/// `cb := fun (_m : Nat) (b : IB 1) => b` — identity step that uses `ih`.
fn cb_identity_step() -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let ib1 = Expr::app(
        Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ),
    );
    let inner = Expr::lam(BinderInfo::Default, ib1, Expr::bvar(0));
    Expr::lam(BinderInfo::Default, nat_ty, inner)
}

#[test]
fn test_compose_faithful_succ_unfold_whnf_matches_iota() {
    // Empirical sanity: applied at a concrete `succ m` index with the
    // identity cb, the LHS must WHNF-reduce to
    // `cb m (compose_faithful d m cb B)` — the same RHS the proof term
    // constructs.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nat_one_dim = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let k_succ = Expr::app(nat_succ, nat_zero.clone());
    let cb = cb_identity_step();
    let b_sym = sym_bounds_one();

    let lhs_app = cf_app(nat_one_dim.clone(), k_succ, cb.clone(), b_sym.clone());
    let lhs_whnf = tc.whnf(&lhs_app);
    let rec_call = cf_app(nat_one_dim, nat_zero.clone(), cb.clone(), b_sym);
    let rhs_app = Expr::app(Expr::app(cb, nat_zero), rec_call);
    let rhs_whnf = tc.whnf(&rhs_app);
    assert_eq!(
        lhs_whnf, rhs_whnf,
        "compose_faithful at succ m did NOT WHNF-reduce to \
         `cb m (compose_faithful d m cb B)` — the iota step on Nat.rec \
         at the succ branch is not firing. WHNF(LHS)={:?}, WHNF(RHS)={:?}",
        lhs_whnf, rhs_whnf,
    );
    // Suppress zero_bounds_one-unused warning if it gets GC'd in future edits.
    let _ = zero_bounds_one();
}
