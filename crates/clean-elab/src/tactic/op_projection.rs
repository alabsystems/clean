// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared heterogeneous-operator typeclass-projection peeling.
//!
//! A surface expression `a ⊕ b` desugars to
//! `@H⊕.h⊕ {u v w} α β γ inst a b`, where `H⊕.h⊕` is a *reducible* projection
//! that unfolds (through the instance) to the underlying operation `op` (e.g.
//! `Nat.mul`). Library/builtin rewrite lemmas, by contrast, are stated over the
//! bare op head (`Nat.mul ?n 0`). To make a bare-head lemma match a
//! projection-headed goal subterm, both `rw` (see `equality/rewrite.rs`) and
//! `simp` (its discrimination-tree key paths and its matcher) need to peel
//! *exactly* the projection layer to expose the bare op head — WITHOUT running a
//! full `whnf` that would δ-unfold the op const itself and ι-reduce the operands
//! (`Nat.mul n 0 → Nat.zero`), erasing the very `Nat.mul` head the lemma is
//! keyed on. This module is the single shared implementation of that peel,
//! consumed by both surfaces so the lemma LHS and the goal subterm land on the
//! same head key.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::{Goal, ProofState};

/// Names of the heterogeneous binary-operator typeclass *projection* functions
/// (`HAdd.hAdd`, `HMul.hMul`, …). A goal written `a ⊕ b` desugars to
/// `@H⊕.h⊕ {…} {α β γ} inst a b`, where the projection is a reducible
/// definition unfolding to `α.proj0 inst`. Each of these takes its two operands
/// as the *trailing* two arguments after the implicit type/instance arguments,
/// which lets [`reduce_op_projection_head`] peel exactly the projection layer
/// without touching the operands.
///
/// Kept in sync with the hetero-op flavors in
/// `clean-kernel/src/env/algebra_hetero.rs`. All are binary (2 operands).
pub(crate) const HETERO_OP_PROJECTIONS: &[&str] = &[
    "HAdd.hAdd",
    "HSub.hSub",
    "HMul.hMul",
    "HDiv.hDiv",
    "HMod.hMod",
    "HPow.hPow",
    "HAnd.hAnd",
    "HOr.hOr",
    "HXor.hXor",
    "HShiftLeft.hShiftLeft",
    "HShiftRight.hShiftRight",
    "HAppend.hAppend",
];

/// Whether `name` is one of the heterogeneous binary-op projection functions
/// (see [`HETERO_OP_PROJECTIONS`]).
pub(crate) fn is_hetero_op_projection(name: &Name) -> bool {
    let s = name.to_string();
    HETERO_OP_PROJECTIONS.iter().any(|p| *p == s)
}

/// Given a hetero-op projection name (`HAdd.hAdd`), return the owning class name
/// (`HAdd`) so the constructor `HAdd.mk` can be checked. Returns `None` for a
/// non-projection name.
pub(crate) fn hetero_class_of_projection(name: &Name) -> Option<String> {
    let s = name.to_string();
    HETERO_OP_PROJECTIONS
        .iter()
        .find(|p| **p == s)
        .and_then(|p| p.split_once('.').map(|(class, _)| class.to_string()))
}

/// Reduce exactly the typeclass-projection layer of an op-headed subterm,
/// exposing the underlying operation head WITHOUT reducing the operands.
///
/// Given `haystack = @H⊕.h⊕ {u v w} α β γ inst a b` (head a registered hetero-op
/// projection per [`is_hetero_op_projection`]), this:
///   1. splits off the two trailing operand arguments `a`, `b`;
///   2. extracts the *underlying operation* `op` (`Nat.add`) from the instance
///      argument — the field-0 payload of the `H⊕.mk … op` constructor. The
///      instance is WHNF-reduced ONLY far enough to expose that constructor
///      (so an instance written as the reducible alias `instHAddNat` unfolds to
///      `HAdd.mk … Nat.add`); the stored op field is never *applied*, so this
///      can never trigger the `Nat.add _ 0 → _` ι base-case that full WHNF of
///      the whole subterm would;
///   3. re-applies `a b` to `op`, yielding `op a b` (`Nat.add a b`).
///
/// Crucially this does NOT call `state.whnf` on the whole head application:
/// that δ-unfolds the *reducible* op const itself (`Nat.mul` → its `Nat.rec`
/// body lambda) and ι-reduces the operands (`Nat.mul n 0 → Nat.zero`), losing
/// the `Nat.mul`/`Nat.add` head the pattern/key is keyed on. Pulling the op
/// straight out of the instance constructor keeps the surface op const intact.
///
/// Returns `None` when the head is not an applied hetero-op projection, when it
/// has fewer than two operand arguments, or when the instance does not reduce to
/// a structure constructor whose field-0 payload is the op (e.g. an instance
/// metavariable). The result is the surface `op a b` form to key/match against;
/// any downstream rewrite proof remains kernel-checked, so this only affects
/// *which* form is selected, never soundness.
pub(crate) fn reduce_op_projection_head(
    state: &ProofState,
    goal: &Goal,
    haystack: &Expr,
) -> Option<Expr> {
    let hay_fn = haystack.get_app_fn();
    let ExprKind::Const(hay_name, _) = hay_fn.kind() else {
        return None;
    };
    if !is_hetero_op_projection(hay_name) {
        return None;
    }
    let args: Vec<Expr> = haystack.get_app_args().into_iter().cloned().collect();
    // Binary op: the last two args are the operands; everything before is the
    // implicit type/level/instance prefix that carries the projection.
    if args.len() < 2 {
        return None;
    }
    let split = args.len() - 2;
    let (prefix_args, operands) = args.split_at(split);

    // The instance argument is the LAST prefix arg (`H⊕.hH⊕ {…} α β γ inst`).
    let inst = prefix_args.last()?;

    // Reduce the instance ONLY enough to expose its `H⊕.mk …` constructor.
    // WHNF-ing the *instance term itself* (not the projection application) is
    // safe: the op is a stored field, not applied, so no operator ι-redex fires.
    let inst_whnf = state.whnf(goal, inst);
    let inst_fn = inst_whnf.get_app_fn();
    let ExprKind::Const(inst_ctor, _) = inst_fn.kind() else {
        return None;
    };
    // The constructor must be the matching `H⊕.mk`. Its field-0 payload (the op)
    // is its LAST argument: `H⊕.mk {L} α β γ op`.
    let expected_ctor = format!("{}.mk", hetero_class_of_projection(hay_name)?);
    if inst_ctor.to_string() != expected_ctor {
        return None;
    }
    let inst_args = inst_whnf.get_app_args();
    let op: Expr = (*inst_args.last()?).clone();

    // Re-apply the operands to the op: `op a b`.
    let mut result = op;
    for operand in operands {
        result = Expr::app(result, operand.clone());
    }
    Some(result)
}
