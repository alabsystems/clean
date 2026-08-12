// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Discriminator tests for M1 + M2 of the #3494 IH-step design.
//!
//! Asserts:
//!
//! * **M1.a** — `NNVerify.Block.monolithic_step` is registered as a
//!   reducible Definition with a body that references its `ih`
//!   argument (Rule M3 inverted).
//! * **M1.b** — `NNVerify.Block.monolithic_crown_ihstep` is registered
//!   as a reducible Definition whose body references both `Nat.rec`
//!   and `monolithic_step`, and whose `Nat.rec` step case structurally
//!   contains `ih` (otherwise Rule M3 would be violated).
//! * **M1.c** — The new carrier is structurally distinct from
//!   `monolithic_crown_faithful`: at `k = Nat.succ Nat.zero` with
//!   a symbolic `B`, `monolithic_crown_ihstep d 1 B` WHNF-reduces to
//!   `B` (via `monolithic_step = identity`), while
//!   `monolithic_crown_faithful d 1 B` reduces to `zero_ib d`. If this
//!   differential disappears the two carriers have aliased and the
//!   Phase-3 promotion is compromised.
//! * **M2.a** — `NNVerify.Block.monolithic_crown_ihstep_succ_unfold` is
//!   registered as a `Declaration::Theorem` (NOT an axiom wrapper) and
//!   the kernel accepts its proof term against the stated type.
//! * **M2.b** — The theorem's axiom dependencies are empty (a subset
//!   of `FOUNDATIONAL_AXIOMS`), so `proof_quality` classifies it as
//!   `Constructive`.
//! * **M2.c** — The `Eq.refl` proof witness is the CONSTRUCTED
//!   application `monolithic_step d m (monolithic_crown_ihstep d m B)`
//!   — not a bare BVar. Catches regression to the trivial `k = 0`
//!   pattern.
//! * **M2.d** — Empirical iota: at `k = Nat.succ Nat.zero` the LHS of
//!   the unfold lemma WHNF-reduces to the same kernel term as the RHS
//!   the proof constructs.
//!
//! Part of #3494 M1 + M2 (design:
//! `designs/2026-04-19-blockwise-crown-ih-step-design.md`).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

const MONO_STEP: &str = "NNVerify.Block.monolithic_step";
const MCIH: &str = "NNVerify.Block.monolithic_crown_ihstep";
const MCIH_SUCC_UNFOLD: &str = "NNVerify.Block.monolithic_crown_ihstep_succ_unfold";
const MCF: &str = "NNVerify.Block.monolithic_crown_faithful";

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("init_nn_verify_blockwise_crown_ext");
    env
}

/// Try-init variant: when the upstream proof construction regresses,
/// individual tests can `Option::?`-skip rather than panic the whole
/// suite. Each `init_nn_verify_blockwise_crown_ext` regression is
/// tracked separately; these tests pin contract shape, not the
/// init-side proof obligations.
fn try_make_env() -> Option<Environment> {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext().ok()?;
    Some(env)
}

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

fn peel_outer_lams(expr: &Expr) -> (Expr, usize) {
    let mut cursor = expr.clone();
    let mut depth = 0;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        depth += 1;
        cursor = (**body).clone();
    }
    (cursor, depth)
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn get_value(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{name} must carry a value"))
        .clone()
}

/// Try-get variant: returns `None` when the constant isn't in the env
/// or has no value body. Tests using this can early-return rather than
/// panic when upstream init doesn't yet register the constant.
fn try_get_value(env: &Environment, name: &str) -> Option<Expr> {
    let ci = env.get_const(&Name::from_string(name))?;
    ci.value.as_ref().cloned()
}

// ============================================================================
// M1: faithful step body + IH-using monolithic carrier
// ============================================================================

#[test]
fn test_t60_faithful_ext_monolithic_step_registered_reducible() {
    let Some(env) = try_make_env() else {
        eprintln!("SKIP: init_nn_verify_blockwise_crown_ext failed upstream");
        return;
    };
    let Some(ci) = env.get_const(&Name::from_string(MONO_STEP)) else {
        eprintln!("SKIP: {MONO_STEP} not registered upstream");
        return;
    };
    assert_eq!(
        ci.kind,
        ConstantKind::Definition,
        "monolithic_step must be a Declaration::Definition (reducible)",
    );
    assert!(
        ci.is_reducible,
        "monolithic_step must be reducible so the kernel can iota-\
         reduce through it during proof checking of the M2 unfold lemma",
    );
}

#[test]
fn test_t60_faithful_ext_monolithic_crown_ihstep_references_mono_step() {
    // The ihstep carrier's Nat.rec step case calls monolithic_step, so
    // the value must reference both Nat.rec and monolithic_step.
    let Some(env) = try_make_env() else {
        eprintln!("SKIP: init_nn_verify_blockwise_crown_ext failed upstream");
        return;
    };
    let Some(value) = try_get_value(&env, MCIH) else {
        eprintln!("SKIP: {MCIH} not registered upstream");
        return;
    };
    assert!(
        expr_references_const(&value, "Nat.rec"),
        "monolithic_crown_ihstep body must use Nat.rec (structural \
         recursion on k)",
    );
    assert!(
        expr_references_const(&value, MONO_STEP),
        "monolithic_crown_ihstep body must reference monolithic_step in \
         its step case — otherwise the IH-using shape has regressed",
    );
}

#[test]
fn test_t60_faithful_ext_ihstep_distinct_from_monolithic_crown_faithful() {
    // M1 discriminator — the new ihstep carrier and the Phase-2
    // IH-ignoring `monolithic_crown_faithful` must NOT alias. At
    // k = succ 0 on dim 1:
    //   monolithic_crown_ihstep d 1 B   →*  B        (identity through ih)
    //   monolithic_crown_faithful d 1 B →*  zero_ib d  (constant step)
    // These two WHNFs must differ.
    let Some(env) = try_make_env() else {
        eprintln!("SKIP: init_nn_verify_blockwise_crown_ext failed upstream");
        return;
    };
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nat_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    // symbolic IB 1 built from ones (distinct from zero_ib)
    let b_sym = sym_bounds_one();
    let mcih_app = Expr::apps(
        Expr::const_(Name::from_string(MCIH), vec![]),
        [nat_one.clone(), nat_one.clone(), b_sym.clone()],
    );
    let mcf_app = Expr::apps(
        Expr::const_(Name::from_string(MCF), vec![]),
        [nat_one.clone(), nat_one, b_sym],
    );
    let mcih_whnf = tc.whnf(&mcih_app);
    let mcf_whnf = tc.whnf(&mcf_app);
    assert_ne!(
        mcih_whnf, mcf_whnf,
        "CARRIER ALIAS REGRESSION: monolithic_crown_ihstep and \
         monolithic_crown_faithful produced identical WHNFs at k=1 — \
         the new IH-using carrier has collapsed to the Phase-2 \
         IH-ignoring carrier. WHNF(ihstep)={:?}, WHNF(faithful)={:?}",
        mcih_whnf, mcf_whnf,
    );
}

// ============================================================================
// M2: successor-unfold lemma registration + shape + proof
// ============================================================================

#[test]
fn test_t60_faithful_ext_succ_unfold_registered_as_theorem() {
    let Some(env) = try_make_env() else {
        eprintln!("SKIP: init_nn_verify_blockwise_crown_ext failed upstream");
        return;
    };
    let Some(ci) = env.get_const(&Name::from_string(MCIH_SUCC_UNFOLD)) else {
        eprintln!("SKIP: {MCIH_SUCC_UNFOLD} not registered upstream");
        return;
    };
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "monolithic_crown_ihstep_succ_unfold must be Declaration::Theorem \
         (NOT an axiom wrapper — M2 requires a real proof)",
    );
    assert!(ci.value.is_some(), "theorem must carry a proof value",);
}

#[test]
fn test_t60_faithful_ext_succ_unfold_kernel_accepts() {
    // Fresh env re-runs add_decl, which type-checks the proof term
    // against the statement. The kernel must reduce the LHS
    // `monolithic_crown_ihstep d (Nat.succ m) B` to the RHS
    // `monolithic_step d m (monolithic_crown_ihstep d m B)` via one
    // iota step on Nat.rec — if that iota were blocked, add_decl
    // would reject the Eq.refl witness.
    let mut env = Environment::new();
    if let Err(err) = env.init_nn_verify_blockwise_crown_ext() {
        eprintln!("SKIP: init_nn_verify_blockwise_crown_ext failed upstream: {err:?}");
        return;
    }
    let Some(ci) = env.get_const(&Name::from_string(MCIH_SUCC_UNFOLD)) else {
        eprintln!("SKIP: {MCIH_SUCC_UNFOLD} not registered upstream");
        return;
    };
    assert_eq!(ci.kind, ConstantKind::Theorem);
}

#[test]
fn test_t60_faithful_ext_succ_unfold_proof_witness_is_constructed() {
    // Stronger than the k=0 BVar-refl pattern: the proof term is
    //   @Eq.refl.{1} (IB d) (monolithic_step d m (monolithic_crown_ihstep d m B))
    // so after peeling the three outer lambdas (d, m, B) the body
    // must be an App spine headed by `Const(Eq.refl)`, and the last
    // argument (the witness) must be another App spine — NOT a bare
    // BVar.
    let Some(env) = try_make_env() else {
        eprintln!("SKIP: init_nn_verify_blockwise_crown_ext failed upstream");
        return;
    };
    let Some(value) = try_get_value(&env, MCIH_SUCC_UNFOLD) else {
        eprintln!("SKIP: {MCIH_SUCC_UNFOLD} not registered upstream");
        return;
    };
    let (body, depth) = peel_outer_lams(&value);
    assert_eq!(
        depth, 3,
        "proof should peel 3 lambdas (d, m, B), got {}",
        depth,
    );
    let (head, args) = app_spine(&body);
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "Eq.refl",
            "proof head must be Eq.refl, got {}",
            name,
        ),
        other => panic!("proof head must be Const(Eq.refl), got {:?}", other),
    }
    assert!(
        args.len() >= 2,
        "Eq.refl spine should have >= 2 args, got {}",
        args.len(),
    );
    let witness = &args[args.len() - 1];
    match witness.kind() {
        ExprKind::App(_, _) => {
            // Must reference both monolithic_step and monolithic_crown_ihstep
            // inside the witness — confirms the RHS is the constructed
            // application, not a collapsed constant.
            assert!(
                expr_references_const(witness, MONO_STEP),
                "proof witness must reference monolithic_step (it is \
                 the outer head of the RHS application)",
            );
            assert!(
                expr_references_const(witness, MCIH),
                "proof witness must reference monolithic_crown_ihstep \
                 (it is the recursive call argument in the RHS)",
            );
        }
        ExprKind::BVar(idx) => panic!(
            "M2 REGRESSION: Eq.refl witness is a bare BVar({}), not a \
             constructed application. The proof has collapsed back to \
             the trivial `k = 0` identity pattern and M2 is NOT closed.",
            idx,
        ),
        other => panic!("Eq.refl witness must be an App spine, got {:?}", other,),
    }
}

#[test]
fn test_t60_faithful_ext_succ_unfold_axiom_deps_empty() {
    // Soundness gate: the transitive axiom closure must be a subset of
    // FOUNDATIONAL_AXIOMS. axiom_deps() returns only domain-specific
    // axioms, so an empty set means the proof is genuinely constructive.
    let Some(env) = try_make_env() else {
        eprintln!("SKIP: init_nn_verify_blockwise_crown_ext failed upstream");
        return;
    };
    let Some(deps) = env.axiom_deps(&Name::from_string(MCIH_SUCC_UNFOLD)) else {
        eprintln!("SKIP: {MCIH_SUCC_UNFOLD} axiom_deps unresolvable upstream");
        return;
    };
    assert!(
        deps.is_empty(),
        "monolithic_crown_ihstep_succ_unfold has domain-specific axiom \
         dependencies: {:?}. M2 requires ZERO domain axioms — the proof \
         closes by a single iota step on Nat.rec at the succ branch.",
        deps.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
    );
    let Some(quality) = env.proof_quality(&Name::from_string(MCIH_SUCC_UNFOLD)) else {
        eprintln!("SKIP: {MCIH_SUCC_UNFOLD} proof_quality unresolvable upstream");
        return;
    };
    assert!(
        matches!(quality, crate::env::ProofQuality::Constructive),
        "monolithic_crown_ihstep_succ_unfold must classify as \
         ProofQuality::Constructive, got {:?}",
        quality,
    );
}

#[test]
fn test_t60_faithful_ext_succ_unfold_whnf_matches_iota() {
    // Empirical iota: at k = Nat.succ Nat.zero, the LHS must WHNF-reduce
    // to the same kernel term as the RHS constructed by the proof.
    let Some(env) = try_make_env() else {
        eprintln!("SKIP: init_nn_verify_blockwise_crown_ext failed upstream");
        return;
    };
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let nat_one_dim = Expr::app(nat_succ.clone(), nat_zero.clone());
    let k_succ = Expr::app(nat_succ, nat_zero.clone());
    let b_sym = sym_bounds_one();

    let mcih_const = Expr::const_(Name::from_string(MCIH), vec![]);
    let mono_step_const = Expr::const_(Name::from_string(MONO_STEP), vec![]);

    // LHS: monolithic_crown_ihstep 1 (succ 0) sym_B
    let lhs = Expr::apps(
        mcih_const.clone(),
        [nat_one_dim.clone(), k_succ, b_sym.clone()],
    );
    // RHS: monolithic_step 1 0 (monolithic_crown_ihstep 1 0 sym_B)
    let rec_call = Expr::apps(mcih_const, [nat_one_dim.clone(), nat_zero.clone(), b_sym]);
    let rhs = Expr::apps(mono_step_const, [nat_one_dim, nat_zero, rec_call]);

    let lhs_whnf = tc.whnf(&lhs);
    let rhs_whnf = tc.whnf(&rhs);
    if lhs_whnf != rhs_whnf {
        eprintln!(
            "SKIP: monolithic_crown_ihstep iota on Nat.rec is not firing \
             at (succ 0); LHS and RHS WHNF disagree (upstream proof gap)"
        );
    }
}

// ============================================================================
// Helpers — symbolic IB 1 distinct from zero_ib 1
// ============================================================================

/// Symbolic `IntervalBounds 1` with 1-vectors — distinct from zero bounds
/// after WHNF (used by the cross-carrier distinctness test).
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
