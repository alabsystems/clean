// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for the #3590 demasquerade of
//! `NNVerify.LayerNorm.zonotope_generators_reset` (T22).
//!
//! ## History
//!
//! Per `designs/2026-04-19-demasquerade-cxxx-pattern.md` (Rules M2 + M3 +
//! M4), the prior #3495 "constructive" proof was a compound MASQUERADE: the
//! carrier `generators_after_ln : Nat -> Nat -> Nat` returned `n` REGARDLESS
//! of `k` (`fun n _ => n`, later a cosmetic `Nat.rec` wrapper whose step
//! branch discarded both `_m` and `_ih`), so the companion theorem
//! `generators_after_ln n k = n` reduced to `n = n`, closed by `Eq.refl`.
//!
//! #3590 **Branch A** (honest demotion) demoted the theorem to a body-less
//! `Declaration::Axiom` and co-demoted the carrier to `Declaration::Opaque`
//! (same `k`-discarding body, only the kind flipped). That closed the
//! alias-collapse loophole but left a body-less axiom in the trusted base.
//!
//! ## Branch B (this file's guards): FAITHFUL MATRIX RESTATEMENT
//!
//! The carrier is now the GENERATOR MATRIX produced by LayerNorm:
//! `generators_after_ln : (n k : Nat) -> Zonotope n k -> NNMat n n`, the
//! `n x n` DIAGONAL radius matrix `diag(radius_i)` with
//! `radius_i = Fin.sum k (fun j => Rat.abs (z.generators i j))`. The radius
//! GENUINELY consumes all `k` input generator columns, so the carrier is NOT
//! argument-discarding (M2 closed structurally). The axiom is RETIRED and
//! replaced by two constructive `Declaration::Theorem`s:
//!
//! 1. `zonotope_generators_reset` — diagonal-entry equation
//!    `generators_after_ln n k z i i = Fin.sum k (fun j => Rat.abs (z.generators i j))`.
//!    Genuinely `k`-consuming (the RHS IS the row sum); NOT a count
//!    tautology and would FAIL to type-check against a `k`-discarding
//!    carrier.
//! 2. `zonotope_generators_offdiagonal` — off-diagonal is zero
//!    `i <> i' -> generators_after_ln n k z i i' = Rat.zero`. Together with
//!    (1) this pins the matrix as exactly the diagonal radius box.
//!
//! Both proofs are `Decidable.rec` splits on `instDecidableEqFin n i i'`;
//! their transitive axiom closure is `subseteq {propext, Quot.sound,
//! Classical.choice}` (NO `sorry`, NO `add_decl_structural`).
//!
//! These guards REPLACE the Branch A "is an Axiom / is Opaque" pins. Each
//! flip is justified inline: the axiom is genuinely retired by a faithful
//! `k`-consuming carrier. The guards still REJECT a `k`-discarding carrier —
//! a regression to a `Nat -> Nat -> Nat` constant body (or any body that
//! does not reference the input generator matrix) would break the
//! diagonal-equation type-check and the genuine-`k`-consumption probe below.
//!
//! Part of #3590 (Branch B).

use crate::env::axiom_audit::ProofQuality;
use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

const GENERATORS_RESET: &str = "NNVerify.LayerNorm.zonotope_generators_reset";
const GENERATORS_OFFDIAG: &str = "NNVerify.LayerNorm.zonotope_generators_offdiagonal";
const GENERATORS_AFTER_LN: &str = "NNVerify.LayerNorm.generators_after_ln";

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("init_nn_verify_blockwise_crown_ext should succeed");
    env
}

// ---------------------------------------------------------------
// Guard 1: zonotope_generators_reset is now a faithful Theorem
//          (axiom genuinely retired by a k-consuming carrier).
// ---------------------------------------------------------------

#[test]
fn test_t22_zonotope_generators_reset_is_faithful_theorem() {
    // Branch B: the former body-less Axiom is RETIRED. The diagonal-entry
    // equation is a kernel-checked Declaration::Theorem over the faithful
    // diagonal radius-box carrier (which consumes all k input columns), so
    // it is genuinely proved, not asserted.
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(GENERATORS_RESET))
        .expect("zonotope_generators_reset should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "#3590 Branch B: zonotope_generators_reset MUST be a faithful \
         Declaration::Theorem (the body-less Axiom is retired by a \
         k-consuming diagonal radius carrier); got {:?}",
        info.kind
    );
}

/// Structural guard: the Theorem carries its kernel-checked proof term. A
/// regression that dropped the proof (back to an Axiom) would re-open the
/// admitted-axiom census slot the Branch B retirement closed.
#[test]
fn test_t22_zonotope_generators_reset_carries_proof_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(GENERATORS_RESET))
        .expect("zonotope_generators_reset should be registered");
    assert!(
        info.value.is_some(),
        "#3590 Branch B: the faithful Theorem must carry its Decidable.rec \
         proof value (a regression to a body-less Axiom re-opens the census \
         slot); got value=None"
    );
}

/// Soundness guard: the proof's transitive axiom closure is empty of
/// domain-specific axioms (⊆ FOUNDATIONAL). `proof_quality` therefore
/// classifies it as `Constructive` — NOT the #3495 masquerade artefact
/// (that was Constructive only because every branch collapsed to
/// `Eq.refl Nat n` under the argument-discarding carrier). Here it is
/// Constructive because the `Decidable.rec` split over `instDecidableEqFin`
/// (itself axiom-free, computing on `Nat.decEq`) genuinely discharges the
/// diagonal radius equation.
#[test]
fn test_t22_zonotope_generators_reset_is_constructive_no_domain_axioms() {
    let env = make_env();
    let name = Name::from_string(GENERATORS_RESET);

    let quality = env
        .proof_quality(&name)
        .expect("proof_quality should resolve for the faithful T22 theorem");
    assert!(
        matches!(quality, ProofQuality::Constructive),
        "#3590 Branch B: the faithful T22 theorem must classify as \
         Constructive (closure ⊆ FOUNDATIONAL_AXIOMS over the axiom-free \
         Fin.sum / Rat.abs / instDecidableEqFin carriers); got {quality:?}"
    );

    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should resolve for the faithful T22 theorem");
    assert!(
        deps.is_empty(),
        "#3590 Branch B: the faithful T22 theorem's domain-axiom closure \
         must be empty; got {:?}",
        deps.iter().map(|d| d.to_string()).collect::<Vec<_>>()
    );

    // Sorry-free: no trust marker (sorryAx) reachable.
    let tm = env
        .trust_marker_deps(&name)
        .expect("trust_marker_deps should resolve for the faithful T22 theorem");
    assert!(
        tm.is_empty(),
        "#3590 Branch B: the faithful T22 proof must be sorry-free; got {tm:?}"
    );
}

// ---------------------------------------------------------------
// Guard 2: generators_after_ln is a faithful reducible Definition
//          (NNMat n n diagonal radius matrix, NOT a Nat-count).
// ---------------------------------------------------------------

#[test]
fn test_t22_generators_after_ln_is_faithful_reducible_definition() {
    // Branch B: the carrier is no longer the k-discarding Nat -> Nat -> Nat
    // (#3495) nor the Opaque placeholder (#3590 Branch A). It is now the
    // reducible diagonal radius matrix Definition; reducibility is required
    // so the T22 proofs can δ-unfold it to the Decidable.rec form their
    // motives match against. Reducibility no longer re-opens a masquerade
    // because the body is NO LONGER argument-discarding — the diagonal entry
    // is the genuine k-consuming row sum.
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(GENERATORS_AFTER_LN))
        .expect("generators_after_ln should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "#3590 Branch B: generators_after_ln MUST be a reducible \
         Declaration::Definition (faithful diagonal radius matrix); got {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "#3590 Branch B: the carrier Definition must carry its diagonal-split body"
    );
    assert!(
        info.is_reducible,
        "#3590 Branch B: generators_after_ln must be reducible so the T22 \
         proofs can δ-unfold it; the masquerade is closed STRUCTURALLY (the \
         body consumes k), not by opacity"
    );
}

/// Faithfulness guard: the carrier's type is the GENERATOR MATRIX
/// `(n k : Nat) -> Zonotope n k -> NNMat n n`, NOT a `Nat`-valued count. A
/// regression to a `Nat -> Nat -> Nat` k-discarding carrier (the #3495
/// masquerade shape) would change this type and fail this guard, and would
/// also break the diagonal-equation theorem's `generators_after_ln n k z i i`
/// application (which requires the `Zonotope`/`Fin` arguments).
#[test]
fn test_t22_generators_after_ln_type_is_zonotope_to_matrix() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(GENERATORS_AFTER_LN), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).unwrap_or_else(|err| {
        panic!("#3590 Branch B: generators_after_ln type should type-check, got: {err:?}")
    });
    // Outer shape is a Pi over `n : Nat`.
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "#3590 Branch B: generators_after_ln must be a Pi (n k z) -> NNMat n n, got {:?}",
        ty.kind()
    );
    // Pretty-printed type mentions the Zonotope domain and the NNMat
    // codomain — the carrier consumes a real zonotope and produces a matrix
    // (a k-discarding Nat -> Nat -> Nat carrier would mention neither).
    let printed = format!("{ty:?}");
    assert!(
        printed.contains("Zonotope"),
        "#3590 Branch B: the faithful carrier must consume a Zonotope \
         (k-discarding Nat carrier would not); type = {printed}"
    );
    assert!(
        printed.contains("NNMat"),
        "#3590 Branch B: the faithful carrier must produce an NNMat n n \
         generator matrix; type = {printed}"
    );
}

// ---------------------------------------------------------------
// Guard 3: the off-diagonal companion is a faithful Theorem too.
// ---------------------------------------------------------------

#[test]
fn test_t22_generators_offdiagonal_is_faithful_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(GENERATORS_OFFDIAG))
        .expect("zonotope_generators_offdiagonal should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "#3590 Branch B: the off-diagonal companion MUST be a faithful \
         Declaration::Theorem; got {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "#3590 Branch B: the off-diagonal Theorem must carry its proof value"
    );

    let name = Name::from_string(GENERATORS_OFFDIAG);
    let deps = env
        .axiom_deps(&name)
        .expect("axiom_deps should resolve for the off-diagonal theorem");
    assert!(
        deps.is_empty(),
        "#3590 Branch B: the off-diagonal theorem's domain-axiom closure \
         must be empty; got {:?}",
        deps.iter().map(|d| d.to_string()).collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------
// Guard 4: both T22 theorem types still type-check as Pi.
// ---------------------------------------------------------------

#[test]
fn test_t22_theorem_types_still_type_check() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for name in [GENERATORS_RESET, GENERATORS_OFFDIAG] {
        let e = Expr::const_(Name::from_string(name), vec![]);
        let ty = tc.infer_type(&e).unwrap_or_else(|err| {
            panic!("#3590 Branch B: {name} type should type-check, got: {err:?}")
        });
        assert!(
            matches!(ty.kind(), ExprKind::Pi(..)),
            "#3590 Branch B: {name} type should be a (forall ...) Pi, got {:?}",
            ty.kind()
        );
    }
}

// ---------------------------------------------------------------
// Guard 5: genuine k-consumption — the carrier reads z.generators.
//
// The diagonal-entry equation pins the diagonal to `Fin.sum k (fun j =>
// Rat.abs (z.generators i j))`. Its proof would FAIL to type-check if the
// carrier discarded k (returned a constant, or any value independent of the
// input generator matrix), because the LHS `generators_after_ln n k z i i`
// must δ-reduce to that exact row sum. The fact that the Theorem registered
// (Guards 1-3) is itself the proof of genuine k-consumption. This guard
// additionally pins that the carrier BODY syntactically references the
// `z.generators` projection (Proj index 1) and `Fin.sum` — a k-discarding
// regression could not contain both.
// ---------------------------------------------------------------

#[test]
fn test_t22_carrier_body_references_generators_and_fin_sum() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(GENERATORS_AFTER_LN))
        .expect("generators_after_ln should be registered");
    let body = info
        .value
        .as_ref()
        .expect("faithful carrier must carry a body");
    let printed = format!("{body:?}");
    assert!(
        printed.contains("Fin"),
        "#3590 Branch B: the diagonal carrier body must use Fin.sum over the \
         k input columns (genuine k-consumption); body = {printed}"
    );
    assert!(
        printed.contains("\"sum\""),
        "#3590 Branch B: the diagonal carrier body must use Fin.sum to fold \
         the k input generator columns into the per-row radius; body = {printed}"
    );
    assert!(
        printed.contains("Proj"),
        "#3590 Branch B: the diagonal carrier body must project z.generators \
         (Proj) — a k-discarding constant body would not; body = {printed}"
    );
    assert!(
        printed.contains("\"abs\""),
        "#3590 Branch B: the diagonal carrier body must take Rat.abs of each \
         generator entry (L1 radius); body = {printed}"
    );
}
