// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sorry/trusted proof term constructors.

use std::sync::LazyLock;

use crate::tc::TypeChecker;
use crate::{Environment, Expr, Level, Name};

use super::accounting::{deny_sorry_enabled, record_ay_creation, record_sorry_creation};
use super::kind::SorryKind;
use super::locations::{record_ay_location, record_sorry_location};

/// Pre-interned sorry-related names (avoids repeated allocation on every sorry
/// creation). Matches the `LazyLock<Name>` pattern used in `tc/infer.rs`.
static NAME_SORRY_AX: LazyLock<Name> = LazyLock::new(|| Name::from_string("sorryAx"));
static NAME_SORRY: LazyLock<Name> = LazyLock::new(|| Name::from_string("sorry"));
static NAME_BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
static NAME_BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
static NAME_SMT_PROOF: LazyLock<Name> = LazyLock::new(|| Name::from_string("SMT_PROOF"));
static NAME_TRUSTED_AY: LazyLock<Name> = LazyLock::new(|| Name::from_string("trustedAy"));

/// Infer the universe level u such that `goal_ty : Sort u`.
///
/// Uses a temporary TypeChecker to infer the sort level. Falls back to
/// `Level::zero()` (correct for Prop goals) when inference fails — e.g.,
/// when goal_ty contains free variables not in the TypeChecker's context.
fn infer_sorry_level(env: &Environment, goal_ty: &Expr) -> Level {
    let tc = TypeChecker::new(env);
    tc.infer_sort(goal_ty).unwrap_or(Level::zero())
}

fn bool_flag_expr(kind: SorryKind) -> Expr {
    let name = match kind {
        SorryKind::Explicit => NAME_BOOL_FALSE.clone(),
        SorryKind::Synthetic => NAME_BOOL_TRUE.clone(),
    };
    Expr::const_(name, vec![])
}

fn build_legacy_sorry(level: Level, goal_ty: &Expr) -> Expr {
    let sorry_const = Expr::const_(NAME_SORRY.clone(), vec![level]);
    Expr::app(sorry_const, goal_ty.clone())
}

fn build_sorry_ax(level: Level, goal_ty: &Expr, kind: SorryKind) -> Expr {
    let sorry_ax = Expr::const_(NAME_SORRY_AX.clone(), vec![level]);
    Expr::apps(sorry_ax, [goal_ty.clone(), bool_flag_expr(kind)])
}

#[track_caller]
pub fn create_sorry_term_with_kind_at_level(
    env: &Environment,
    goal_ty: &Expr,
    kind: SorryKind,
    level: Level,
) -> Expr {
    let caller = std::panic::Location::caller();
    assert!(
        !deny_sorry_enabled(),
        "DENY_SORRY mode enabled: sorry term creation at {}:{} is not allowed. \
         Goal type: {:?}",
        caller.file(),
        caller.line(),
        goal_ty
    );

    record_sorry_creation(kind);
    record_sorry_location();

    if env.get_const(&NAME_SORRY_AX).is_some() {
        return build_sorry_ax(level, goal_ty, kind);
    }
    if env.get_const(&NAME_SORRY).is_some() {
        return build_legacy_sorry(level, goal_ty);
    }

    // If no sorry exists, create a typed stub expression matching the sorry pattern.
    // This is used for propositions that SMT can prove but we can't
    // yet reconstruct proofs for (e.g., transitive chains, congruence).
    // Apply goal_ty so the term has the correct type structure: @SMT_PROOF.{u} goal_ty
    Expr::app(
        Expr::const_(NAME_SMT_PROOF.clone(), vec![level]),
        goal_ty.clone(),
    )
}

/// Create a sorry term with explicit provenance.
///
/// The constructor prefers Lean 4-style `sorryAx α synthetic` whenever the
/// environment has registered it, and falls back to the legacy bootstrap `sorry`
/// axiom when only the bootstrap surface exists.
#[track_caller]
pub fn create_sorry_term_with_kind(env: &Environment, goal_ty: &Expr, kind: SorryKind) -> Expr {
    let level = infer_sorry_level(env, goal_ty);
    create_sorry_term_with_kind_at_level(env, goal_ty, kind, level)
}

/// Create a synthetic/internal sorry term.
///
/// This preserves the historical `create_sorry_term` entrypoint while routing
/// callers through the new provenance-aware constructor.
#[track_caller]
pub fn create_sorry_term(env: &Environment, goal_ty: &Expr) -> Expr {
    create_sorry_term_with_kind(env, goal_ty, SorryKind::Synthetic)
}

/// Create a trustedAy term for SMT-proved goals.
///
/// Constructs `@trustedAy.{u} goal_ty` with universe level inferred from `goal_ty`.
/// Falls back to synthetic `create_sorry_term` if `trustedAy` axiom is not registered.
/// Increments `AY_PROOF_COUNTER` (not `SORRY_COUNTER`).
#[track_caller]
pub fn create_trusted_ay_term(env: &Environment, goal_ty: &Expr) -> Expr {
    if env.get_const(&NAME_TRUSTED_AY).is_some() {
        record_ay_location();
        record_ay_creation();
        let u = infer_sorry_level(env, goal_ty);
        return Expr::app(
            Expr::const_(NAME_TRUSTED_AY.clone(), vec![u]),
            goal_ty.clone(),
        );
    }

    // trustedAy axiom not registered — fall back to synthetic sorry
    create_sorry_term(env, goal_ty)
}
