// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FUSION (design 2026-06-20-fusion-obligation-as-clean-expr): the per-kind
//! `Expr` encoder for the **IndexInBounds** obligation (the
//! `ProofAnnotation::InBounds` marker): an indexed array access is in bounds
//! iff `index < len`.
//!
//! This is the in-bounds sibling of [`crate::clean_expr_lowering::overflow_goal`]
//! / `overflow_obligation`. It takes an indexed-access node's OWN fields (the
//! array length `len` read off the place's `Ty::Array { len, .. }`, the array
//! and index `ValueId`s, and the concrete index value as a `Nat` fact) and
//! returns the obligation as a `clean_kernel::Expr`, so the goal is born from
//! the same field bindings that construct the access. Program-change =>
//! Expr-change is structural, not a test discipline.
//!
//! ## The goal shape (mirrors the overflow `Eq Bool _ Bool.true` shape)
//!
//! `index < len` is encoded as `index + 1 <= len`:
//!
//! ```text
//! @Eq Bool (Nat.ble (Nat.add index 1) len) Bool.true
//! ```
//!
//! `Nat.ble` (not `Nat.blt`) is used because the prelude reduces `Nat.ble`
//! natively — the SAME primitive `overflow_goal` relies on — so discharge is a
//! kernel reduction with no extra lemmas. The hand proof term
//! `@Eq.refl Bool Bool.true` is accepted by the kernel iff `index + 1 <= len`
//! genuinely reduces to `Bool.true`; an out-of-bounds index reduces it to
//! `Bool.false` and the kernel REFUSES — the de Bruijn criterion, no external
//! `.lean`.
//!
//! Fail-closed: a zero-length array has no valid index, so the encoder returns
//! `Err(ZeroLengthArray)` rather than minting an unsatisfiable / vacuous goal.
//!
//! The whole module is gated on `clean-expr` (via the parent module in lib.rs)
//! so the default zero-dependency trust-ir format build never references
//! clean-kernel.

use crate::proof::ExprObligation;
use crate::value::ValueId;
use clean_kernel::{Expr, Level, Name};

/// Errors the IndexInBounds encoder can fail-closed with rather than minting a
/// vacuous goal for an unsupported shape.
///
/// Manual `Display`/`Error` impls (not `thiserror`): `trust-ir` keeps zero
/// required external dependencies; the `clean-expr` feature adds only
/// `clean-kernel`. Kept as a distinct type, mirroring the sibling per-kind
/// encoders' self-contained error enums.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IndexInBoundsError {
    /// A zero-length array has NO valid index, so `index < 0` is unsatisfiable:
    /// fail closed rather than mint an always-false (or vacuous) goal. A node
    /// edit that drops the array to length 0 must re-shape, not reuse a goal.
    ZeroLengthArray,
}

impl core::fmt::Display for IndexInBoundsError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            IndexInBoundsError::ZeroLengthArray => {
                write!(f, "index-in-bounds obligation: array has length 0")
            }
        }
    }
}

impl std::error::Error for IndexInBoundsError {}

/// `@Eq Bool b Bool.true`: the kernel-checkable "this Bool is true" goal.
///
/// Mirrors `clean_expr_lowering::not_overflow_goal`, but asserts `Bool.true`
/// (the bound HOLDS) rather than `Bool.false`. Discharged by `@Eq.refl Bool
/// Bool.true` exactly when `b` reduces to `Bool.true` — the kernel does the
/// `Nat.ble` reduction itself, so a true bound proves and a false one is
/// refused (fail closed).
fn bool_is_true_goal(b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_str("Bool"), b, Expr::const_str("Bool.true")],
    )
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.add"), [a, b])
}

fn nat_ble(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.ble"), [a, b])
}

/// Build the index-in-bounds goal `Expr` for an indexed array access from the
/// node's OWN fields. The bound `len` is the array length (from the place's
/// `Ty::Array { len, .. }`); `index` is the concrete index the node implies.
///
/// `index < len` is encoded as `index + 1 <= len`, i.e.
/// `@Eq Bool (Nat.ble (Nat.add index 1) len) Bool.true`. `Nat.ble` is used (not
/// `Nat.blt`) because the prelude reduces `Nat.ble` natively — the SAME
/// primitive `overflow_goal` relies on — so discharge is a kernel reduction with
/// no extra lemmas. Fails closed on a zero-length array (no valid index).
pub fn indexinbounds_goal(len: u64, index: u64) -> Result<Expr, IndexInBoundsError> {
    if len == 0 {
        return Err(IndexInBoundsError::ZeroLengthArray);
    }
    // index + 1 <= len  <=>  index < len
    let lhs = nat_add(Expr::nat_lit(index), Expr::nat_lit(1));
    let bound = nat_ble(lhs, Expr::nat_lit(len));
    Ok(bool_is_true_goal(bound))
}

/// Build the full [`ExprObligation`] (goal + node-sourced operand hypotheses)
/// for an indexed access, ready to stamp as `ProofAnnotation::Goal` in the same
/// lowering chain that stamps the `InBounds` marker.
///
/// Hypotheses are the node's own facts: the array value and the index value are
/// `Nat`s in the kernel context, sourced from the node, not an external model.
/// (In the bridge, `array`/`index_val` are the `ValueId`s on the indexed access.)
pub fn indexinbounds_obligation(
    len: u64,
    array: ValueId,
    index_val: ValueId,
    index: u64,
) -> Result<ExprObligation, IndexInBoundsError> {
    let goal = indexinbounds_goal(len, index)?;
    Ok(ExprObligation::new(goal)
        .with_hypothesis(format!("%{}", array.index()), Expr::const_str("Nat"))
        .with_hypothesis(format!("%{}", index_val.index()), Expr::const_str("Nat")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, LocalContext, TypeChecker};

    /// The hand-supplied proof term `@Eq.refl Bool Bool.true`. Proves the
    /// in-bounds goal exactly when the goal's `Nat.ble (index+1) len` reduces to
    /// `Bool.true` — the kernel does the reduction itself.
    fn refl_true() -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [Expr::const_str("Bool"), Expr::const_str("Bool.true")],
        )
    }

    /// Kernel-discharge the obligation's goal: local context from the
    /// node-sourced hypotheses, then `check_type(term, &goal)` under
    /// `Environment::with_prelude()` ONLY — the same gate trust-certify uses.
    fn discharge(ob: &ExprObligation, proof_term: &Expr) -> bool {
        let env = Environment::with_prelude();
        let mut ctx = LocalContext::new();
        for (name, ty) in &ob.hypotheses {
            ctx.push(
                Name::from_string(name),
                ty.clone(),
                clean_kernel::BinderInfo::Default,
            );
        }
        let tc = TypeChecker::with_context(&env, ctx);
        tc.check_type(proof_term, &ob.goal).is_ok()
    }

    #[test]
    fn test_goal_shape_is_function_of_fields() {
        // Array len 8, index 3: goal = @Eq Bool (Nat.ble (Nat.add 3 1) 8) Bool.true.
        let goal = indexinbounds_goal(8, 3).expect("len>0 has a representable goal");
        let eq_args = goal.get_app_args();
        assert_eq!(eq_args.len(), 3, "@Eq takes (Bool, bound, Bool.true)");
        assert_eq!(
            eq_args[2],
            &Expr::const_str("Bool.true"),
            "InBounds is a positive in-range claim => Bool.true on the safe side"
        );
        let ble_args = eq_args[1].get_app_args();
        assert_eq!(ble_args.len(), 2, "Nat.ble takes (index+1, len)");
        assert_eq!(
            ble_args[1],
            &Expr::nat_lit(8),
            "the bound arg is the array len, read off the node"
        );
    }

    #[test]
    fn test_in_bounds_is_proven() {
        let ob = indexinbounds_obligation(8, ValueId::new(0), ValueId::new(1), 3)
            .expect("len 8 index 3 has a representable obligation");
        assert!(
            discharge(&ob, &refl_true()),
            "index 3 < len 8: the kernel must discharge the in-bounds goal"
        );
    }

    #[test]
    fn test_out_of_bounds_is_unverified_fail_closed() {
        // index 8 == len 8 is out of bounds (valid indices are 0..=7).
        let ob = indexinbounds_obligation(8, ValueId::new(0), ValueId::new(1), 8)
            .expect("out-of-bounds index still has a representable (false) goal");
        assert!(
            !discharge(&ob, &refl_true()),
            "index 8 >= len 8: the kernel must REFUSE the in-bounds goal (fail closed)"
        );
    }

    #[test]
    fn test_change_coupling_len_flips_verdict_and_goal() {
        // CHANGE-COUPLING on the array `len` field. FIXED index 5. len 8 (in
        // bounds) vs len 4 (out of bounds): BOTH the goal Expr's len arg AND the
        // kernel verdict move.
        let ob_in =
            indexinbounds_obligation(8, ValueId::new(0), ValueId::new(1), 5).expect("in-bounds");
        let ob_out = indexinbounds_obligation(4, ValueId::new(0), ValueId::new(1), 5)
            .expect("representable out-of-bounds goal");
        assert_ne!(
            ob_in.goal, ob_out.goal,
            "the goal Expr is change-coupled: changing the array len changed the goal"
        );
        assert!(discharge(&ob_in, &refl_true()), "index 5 < len 8 => PROVEN");
        assert!(
            !discharge(&ob_out, &refl_true()),
            "index 5 >= len 4 => UNVERIFIED: verdict flipped with the len edit"
        );
    }

    #[test]
    fn test_zero_length_array_fails_closed() {
        assert_eq!(
            indexinbounds_goal(0, 0),
            Err(IndexInBoundsError::ZeroLengthArray),
            "a zero-length array has no valid index => fail closed, no vacuous goal"
        );
    }
}
