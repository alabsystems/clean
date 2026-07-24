// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for the #3492 Branch A demasquerade of
//! `NNVerify.C006.blockwise_nat_induction`.
//!
//! Per `designs/2026-04-19-demasquerade-cxxx-pattern.md` (Rules M1 + M2 +
//! M3 + M4), the prior #3375 "constructive" proof was a compound
//! MASQUERADE:
//!
//! - **M1** (alias-collapse via reducible Definition): `Block.compose` and
//!   `Block.monolithic_crown` were reducible `Declaration::Definition`
//!   entries whose bodies both reduce to `zero_ib (block_dim k)`. Under
//!   δ-reduction, `compose k ... = monolithic_crown k ...` collapsed to
//!   `zero_ib (block_dim k) = zero_ib (block_dim k)`.
//! - **M2** (argument-discarding carrier): both carriers take six
//!   arguments and ignore five of them — the result depends only on `k`
//!   (via `block_dim k`), not on the `crown_block`/`ln_gamma`/`ln_beta`/
//!   `ln_eps`/`B` configuration. The carriers are constant-in-configuration.
//! - **M3** (cosmetic `Nat.rec` wrapper): `blockwise_nat_induction`'s
//!   former proof term was `Nat.rec blockwise_base blockwise_step k` —
//!   but both base and step closed by `Eq.refl` because the carriers
//!   collapsed under δ. The induction hypothesis was never used.
//! - **M4** (`Eq.refl` root): the base case closed with `Eq.refl` on
//!   `zero_ib`, and the step case returned another `Eq.refl` after
//!   lambda-binding-and-discarding the induction hypothesis.
//!
//! Branch A remediation (this file's guards):
//! 1. `blockwise_nat_induction` is now a hypothesis-wrapped
//!    `Declaration::Theorem` requiring explicit local induction evidence.
//! 2. `blockwise_step` is now also a local-evidence
//!    `Declaration::Theorem`; `blockwise_base` is a Phase-3 zero-input
//!    hypothesis-wrapped theorem.
//! 3. `blockwise_equals_monolithic` is now a Phase-2 hypothesis-wrapped
//!    `Declaration::Theorem` whose proof uses Nat.rec, the pointwise
//!    `crown_block = mono_step` hypothesis, and the induction hypothesis.
//! 4. `Block.compose` and `Block.monolithic_crown` are now reducible
//!    indexed Nat.rec carriers with distinct step bodies (#3638), closing
//!    the old shared `zero_ib = zero_ib` alias-collapse path structurally.
//! 5. The `blockwise_nat_induction` type still type-checks through the
//!    kernel `TypeChecker` (as a Pi) to ensure the demotion did not
//!    regress well-formedness.
//!
//! Mirrors the sibling demasquerade guard files for #3578 (C010
//! `certified_implies_lipschitz_local`), #3579 (C012 `single_lp_form`),
//! #3583 (C004 `interval_hull_eq_ibp_forward`), #3586 (C001
//! `compress_tightness_helper`), #3590 (T22 LayerNorm
//! `zonotope_generators_reset`), #3591 (C003 `zonotope_to_ibp`), and
//! #3592 (cert trust composition).
//!
//! Part of #3492.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown()
        .expect("init_nn_verify_blockwise_crown should succeed");
    env
}

// ---------------------------------------------------------------
// Guard 1: blockwise_nat_induction is an honest hypothesis-wrapped Theorem
// ---------------------------------------------------------------

#[test]
fn test_c006_blockwise_nat_induction_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_nat_induction"))
        .expect("blockwise_nat_induction should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "blockwise_nat_induction is retired as a hypothesis-wrapped \
         Declaration::Theorem; got {:?}",
        info.kind
    );
}

/// Structural guard: the theorem carries the local-evidence proof term.
#[test]
fn test_c006_blockwise_nat_induction_has_proof_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C006.blockwise_nat_induction"))
        .expect("blockwise_nat_induction should be registered");
    assert!(
        info.value.is_some(),
        "hypothesis-wrapped theorem must carry a proof value; got value={:?}",
        info.value
    );
}

// ---------------------------------------------------------------
// Guard 2: Block.compose is a reducible Definition with a FAITHFUL
// indexed Nat.rec body (Phase-1 successor guard to the #3492 Branch A
// Opaque invariant; see #3638 and
// `designs/2026-04-20-c006-block-compose-faithful-carriers.md`).
// ---------------------------------------------------------------
//
// Pre-#3638 this test asserted that `Block.compose` was a non-reducible
// Opaque — the only thing blocking the `compose = monolithic_crown =
// zero_ib` δ-collapse. Phase 1 replaces that guard with a *structural*
// one in the body itself: the compose step case is `cb i ih` while the
// monolithic step case is `mono_step … i ih`. These are syntactically
// distinct head symbols, so δ-reduction cannot alias them regardless of
// reducibility. Reducibility is restored because downstream proof terms
// (Phase 2) need iota-unfolding at `Nat.succ m` to make progress.

#[test]
fn test_c006_block_compose_is_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Block.compose"))
        .expect("Block.compose should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "#3638 Phase 1: Block.compose MUST be a reducible \
         Declaration::Definition with its new indexed Nat.rec body \
         (fun k bd cb lg lb eps B => @Nat.rec (fun i => IB (bd i)) B \
         (fun i ih => cb i ih) k); got {:?}",
        info.kind
    );
}

#[test]
fn test_c006_block_compose_is_reducible_with_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Block.compose"))
        .expect("Block.compose should be registered");
    assert!(
        info.value.is_some(),
        "#3638 Phase 1: Block.compose should carry its indexed Nat.rec \
         body; got value=None"
    );
    assert!(
        info.is_reducible,
        "#3638 Phase 1: Block.compose must be reducible — its step body \
         `cb i ih` is syntactically distinct from Block.monolithic_crown's \
         step body `mono_step … i ih`, so δ-collapse to a shared \
         placeholder is structurally blocked without needing Opacity."
    );
}

// ---------------------------------------------------------------
// Guard 3: Block.monolithic_crown is a reducible Definition with a
// FAITHFUL indexed Nat.rec body (Phase-1 successor guard)
// ---------------------------------------------------------------

#[test]
fn test_c006_block_monolithic_crown_is_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Block.monolithic_crown"))
        .expect("Block.monolithic_crown should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "#3638 Phase 1: Block.monolithic_crown MUST be a reducible \
         Declaration::Definition with its new indexed Nat.rec body \
         (step case `mono_step bd lg lb eps i ih` — syntactically \
         distinct from Block.compose's `cb i ih`); got {:?}",
        info.kind
    );
}

#[test]
fn test_c006_block_monolithic_crown_is_reducible_with_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Block.monolithic_crown"))
        .expect("Block.monolithic_crown should be registered");
    assert!(
        info.value.is_some(),
        "#3638 Phase 1: Block.monolithic_crown should carry its indexed \
         Nat.rec body; got value=None"
    );
    assert!(
        info.is_reducible,
        "#3638 Phase 1: Block.monolithic_crown must be reducible — its \
         step body `mono_step bd lg lb eps i ih` differs structurally \
         from Block.compose's `cb i ih`, so δ-collapse is blocked in \
         the body itself, not via Opacity."
    );
}

// ---------------------------------------------------------------
// Guard 4: blockwise_nat_induction type still type-checks as Pi
// ---------------------------------------------------------------

#[test]
fn test_c006_blockwise_nat_induction_type_still_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.C006.blockwise_nat_induction"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).unwrap_or_else(|err| {
        panic!(
            "blockwise_nat_induction theorem type should still \
             type-check, got: {err:?}"
        )
    });
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "#3492: blockwise_nat_induction type should be Pi (forall k bd cb \
         lg lb eps B, compose ... = monolithic_crown ...), got {:?}",
        ty.kind()
    );
}
