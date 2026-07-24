// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for the #3648 Branch B FAITHFUL RETIREMENT of
//! `NNVerify.Block.blockwise_complexity` (T61).
//!
//! ## History
//!
//! Per `designs/2026-04-19-demasquerade-cxxx-pattern.md`, the original
//! "constructive" T61 proof was a compound MASQUERADE (Rules M1 + M2 + M4):
//! `crown_cost` / `total_dim` were reducible Definitions with
//! argument-discarding bodies `fun (_ : Nat) (_ : Nat -> Nat) => Nat.zero`,
//! and the proof reduced to the vacuous `Nat.zero <= Nat.zero`
//! (`Nat.le_refl Nat.zero`). Branch A (the prior state of this file) demoted
//! T61 to an `Axiom` and froze the carriers to `Opaque` to block the
//! δ-reduction.
//!
//! ## Branch B (this file's guards) — #3648 faithful carrier path (#3646
//! triage Site 4)
//!
//! The placeholders are replaced with FAITHFUL reducible `Declaration::
//! Definition` carriers whose `Nat.rec` folds genuinely consume `k`, `bd`,
//! and the IH accumulator:
//! ```text
//! crown_cost k bd = Nat.rec 0 (fun m ih => ih + bd m * bd m) k
//! total_dim  k bd = Nat.rec 0 (fun m ih => ih + bd m) k
//! ```
//! Over these carriers T61 becomes the GENUINE combinatorial fact
//! `Σ_{m<k} bd(m)² ≤ (Σ_{m<k} bd(m))²`, discharged by a real `Nat.rec`
//! induction (constructive `Declaration::Theorem`, no `sorry`, no
//! `add_decl_structural`). The new carriers are NOT a masquerade: the proof
//! consumes the cross-term structure and would fail to type-check against
//! the arg-discarding placeholders. See
//! `nn_verify_blockwise_crown_ext_t61_proof.rs`.
//!
//! These guards pin the Branch B reality and would catch any regression to
//! the arg-discarding placeholder / vacuous-proof masquerade.
//!
//! Part of #3648.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("init_nn_verify_blockwise_crown_ext should succeed");
    env
}

// ---------------------------------------------------------------
// Guard 1: blockwise_complexity is a faithful constructive Theorem
// ---------------------------------------------------------------

/// T61 must be a `Declaration::Theorem` after the #3648 Branch B faithful
/// retirement (was an `Axiom` under Branch A; a vacuous `Nat.le_refl`
/// Theorem before that).
#[test]
fn test_blockwise_complexity_is_faithful_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Block.blockwise_complexity"))
        .expect("T61 blockwise_complexity should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "#3648 Branch B: T61 blockwise_complexity MUST be a constructive \
         Declaration::Theorem over the faithful crown_cost/total_dim \
         carriers (Σ bd² ≤ (Σ bd)²); got {:?}",
        info.kind
    );
}

/// Structural guard: the Theorem carries a real proof term, and that term is
/// sorry-free (`trust_marker_deps` empty). A regression to the vacuous
/// `Nat.le_refl Nat.zero` masquerade would only type-check against
/// arg-discarding carriers, which this env no longer has.
#[test]
fn test_blockwise_complexity_carries_sorry_free_proof() {
    let env = make_env();
    let name = Name::from_string("NNVerify.Block.blockwise_complexity");
    let info = env
        .get_const(&name)
        .expect("T61 blockwise_complexity should be registered");

    assert!(
        info.value.is_some(),
        "#3648 Branch B: T61 Theorem must carry a proof value (the \
         constructive Nat.rec induction term); got value = None"
    );

    let tm = env
        .trust_marker_deps(&name)
        .expect("trust_marker_deps should resolve for a registered T61");
    assert!(
        tm.is_empty(),
        "#3648 Branch B: T61 proof must be sorry-free; got trust markers {tm:?}"
    );
}

// ---------------------------------------------------------------
// Guard 2: T61 type still type-checks as Pi (kernel well-formedness)
// ---------------------------------------------------------------

/// The Theorem's type must still round-trip through the kernel `TypeChecker`
/// as a Pi — the faithful-carrier retirement must not regress declaration
/// well-formedness, and downstream consumers can still instantiate the
/// universal-quantified statement.
#[test]
fn test_blockwise_complexity_type_still_type_checks_as_pi() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.Block.blockwise_complexity"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("kernel must infer T61 Theorem type from the environment");

    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "#3648: T61 type must be a Pi (forall k block_dim, \
         crown_cost k bd <= total_dim k bd * total_dim k bd); got {:?}",
        ty.kind()
    );

    // The type binds exactly 2 Pi binders (k : Nat, bd : Nat -> Nat).
    let mut binder_count = 0;
    let mut cursor = ty.clone();
    while let ExprKind::Pi(_, _, body) = cursor.kind() {
        binder_count += 1;
        cursor = (**body).clone();
    }
    assert_eq!(
        binder_count, 2,
        "#3648: T61 type should have exactly 2 Pi binders \
         (k : Nat, block_dim : Nat -> Nat); got {} binders",
        binder_count,
    );
}

// ---------------------------------------------------------------
// Guard 3: crown_cost is a faithful reducible Definition
// ---------------------------------------------------------------

#[test]
fn test_crown_cost_is_faithful_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Block.crown_cost"))
        .expect("NNVerify.Block.crown_cost should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "#3648 Branch B: crown_cost MUST be a reducible Declaration::\
         Definition with the faithful Nat.rec fold body (was an \
         arg-discarding Opaque placeholder under Branch A); got {:?}",
        info.kind
    );
    assert!(
        info.is_reducible,
        "#3648 Branch B: crown_cost must be reducible so the T61 proof can \
         ι-reduce the carrier at each constructor."
    );
    assert!(
        info.value.is_some(),
        "#3648 Branch B: crown_cost Definition must carry its Nat.rec body."
    );
}

/// Faithfulness guard: the body must mention `Nat.rec` AND reference the
/// block-dimension argument (`bd m`) — i.e. it genuinely consumes its
/// arguments rather than returning a constant `Nat.zero`.
#[test]
fn test_crown_cost_body_is_not_arg_discarding() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Block.crown_cost"))
        .expect("crown_cost should be registered");
    let value = info.value.as_ref().expect("crown_cost carries a value");

    assert!(
        mentions_const(value, "Nat.rec"),
        "#3648 Branch B: crown_cost body must be a Nat.rec fold (genuine \
         combinatorial cost), not an arg-discarding `fun _ _ => Nat.zero`."
    );
    assert!(
        mentions_const(value, "Nat.mul"),
        "#3648 Branch B: crown_cost step branch must square `bd m` \
         (Nat.mul), i.e. consume the block-dimension function."
    );
}

// ---------------------------------------------------------------
// Guard 4: total_dim is a faithful reducible Definition
// ---------------------------------------------------------------

#[test]
fn test_total_dim_is_faithful_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Block.total_dim"))
        .expect("NNVerify.Block.total_dim should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "#3648 Branch B: total_dim MUST be a reducible Declaration::\
         Definition with the faithful Nat.rec fold body; got {:?}",
        info.kind
    );
    assert!(
        info.is_reducible,
        "#3648 Branch B: total_dim must be reducible for the T61 proof's \
         ι-reduction at each constructor."
    );
    assert!(
        info.value.is_some(),
        "#3648 Branch B: total_dim Definition must carry its Nat.rec body."
    );
}

#[test]
fn test_total_dim_body_is_not_arg_discarding() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.Block.total_dim"))
        .expect("total_dim should be registered");
    let value = info.value.as_ref().expect("total_dim carries a value");

    assert!(
        mentions_const(value, "Nat.rec"),
        "#3648 Branch B: total_dim body must be a Nat.rec fold (genuine \
         dimension accumulator), not an arg-discarding `fun _ _ => Nat.zero`."
    );
    assert!(
        mentions_const(value, "Nat.add"),
        "#3648 Branch B: total_dim step branch must accumulate `bd m` \
         (Nat.add), i.e. consume the block-dimension function."
    );
}

// ---------------------------------------------------------------
// Guard 5: kernel round-trip on a fresh Environment
// ---------------------------------------------------------------

/// A fresh Environment must register T61 (constructive Theorem) + crown_cost
/// / total_dim (faithful reducible Definitions) without error. Exercises the
/// `add_decl` path, which re-checks the T61 proof body against its type.
#[test]
fn test_kernel_round_trip_on_fresh_env_after_3648_branch_b() {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext().expect(
        "fresh init should succeed — T61 Theorem + crown_cost/total_dim \
         faithful Definitions must pass kernel add_decl (incl. re-checking \
         the T61 proof term)",
    );

    let t61 = env
        .get_const(&Name::from_string("NNVerify.Block.blockwise_complexity"))
        .expect("T61 should be registered after init on a fresh env");
    assert_eq!(
        t61.kind,
        ConstantKind::Theorem,
        "#3648 Branch B: T61 must be a Declaration::Theorem after \
         kernel-checked registration on a fresh env; got {:?}",
        t61.kind,
    );

    for carrier in &["NNVerify.Block.crown_cost", "NNVerify.Block.total_dim"] {
        let info = env
            .get_const(&Name::from_string(carrier))
            .unwrap_or_else(|| panic!("{} should be registered", carrier));
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "#3648 Branch B: {} must be a faithful Declaration::Definition \
             after fresh init; got {:?}",
            carrier,
            info.kind,
        );
    }
}

// ---------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------

/// Whether `e` references a `Const` named `name` anywhere in its tree.
fn mentions_const(e: &Expr, name: &str) -> bool {
    let target = Name::from_string(name);
    match e.kind() {
        ExprKind::Const(n, _) => *n == target,
        ExprKind::App(f, a) => mentions_const(f, name) || mentions_const(a, name),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            mentions_const(ty, name) || mentions_const(body, name)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            mentions_const(ty, name) || mentions_const(val, name) || mentions_const(body, name)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            mentions_const(inner, name)
        }
        _ => false,
    }
}
