// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Contradiction closing for linarith proofs
//!
//! Evaluates concrete Nat/Int/Real expressions and derives `False` from
//! contradictory inequalities (lhs > rhs as concrete values).
//! Real endpoints are downcast to Int via `Real.ofInt_le_to_Int` (#302).
//!
//! Extracted from `arith_linarith_proof.rs` (#302 file-size split).

use clean_kernel::expr::{ExprKind, Literal};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::nat_expr_eval::eval_nat_expr;
use clean_auto::arith_proof::{mk_int_concrete_false, ArithSort, CmpOp};

/// Derive `False` from a contradictory `@Nat.le lhs rhs` proof where
/// `lhs_val > rhs_val` as concrete Nat values.
///
/// 1. Apply `Nat.le_of_succ_le_succ` `rhs_val` times -> `p' : @Nat.le diff 0`
/// 2. diff = 1: `Nat.lt_irrefl 0 p'` (unfolds to `@Nat.le 1 0 -> False`)
/// 3. diff >= 2: `Nat.not_succ_lt_zero (diff-2) p'` (unfolds to `@Nat.le diff 0 -> False`)
///
/// REQUIRES: `proof` has type `@Nat.le lhs_val rhs_val`
/// REQUIRES: `lhs_val > rhs_val` (otherwise returns `None`)
/// ENSURES: On `Some(e)`, `e` has type `False`
pub(crate) fn derive_false_from_contradictory_le(
    proof: Expr,
    lhs_val: u64,
    rhs_val: u64,
) -> Option<Expr> {
    if lhs_val <= rhs_val {
        return None;
    }

    let le_of_succ = Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]);

    // Strip successors from both sides rhs_val times.
    let mut current_proof = proof;
    let mut current_lhs = lhs_val;
    let mut current_rhs = rhs_val;

    while current_rhs > 0 {
        let n = Expr::nat_lit(current_lhs - 1);
        let m = Expr::nat_lit(current_rhs - 1);
        current_proof = Expr::app(
            Expr::app(Expr::app(le_of_succ.clone(), n), m),
            current_proof,
        );
        current_lhs -= 1;
        current_rhs -= 1;
    }

    // current_proof : @Nat.le diff 0 where diff = lhs_val - rhs_val >= 1
    let diff = current_lhs;

    let false_proof = if diff == 1 {
        let lt_irrefl = Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]);
        Expr::app(Expr::app(lt_irrefl, Expr::nat_lit(0)), current_proof)
    } else {
        let not_succ_lt = Expr::const_(Name::from_string("Nat.not_succ_lt_zero"), vec![]);
        Expr::app(
            Expr::app(not_succ_lt, Expr::nat_lit(diff - 2)),
            current_proof,
        )
    };

    Some(false_proof)
}

/// Wrap a proof of `False` with `@False.elim.{0} goal_type false_proof`.
///
/// REQUIRES: `false_proof` has type `False`
/// REQUIRES: `goal_type` is a well-typed Lean expression
/// ENSURES: Result has type `goal_type` (via `False.elim` at universe 0)
pub(crate) fn wrap_false_elim(false_proof: Expr, goal_type: &Expr) -> Expr {
    // Universe zero correct: linarith goals target Prop (arithmetic inequalities)
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
    Expr::app(Expr::app(false_elim, goal_type.clone()), false_proof)
}

/// Try to derive `False` from a contradictory Nat inequality and close the goal.
///
/// Two routes:
/// 1. Concrete: both endpoints evaluate to literals with `lhs_val > rhs_val`.
/// 2. Symbolic cancellation (#ineq_gap sub-fix 2): endpoints share an additive
///    core, `lhs = core + c1`, `rhs = core + c2`, with `c1 > c2`. Then
///    `core + c1` is not `≤ core + c2`, so the hypothesis is contradictory.
///
/// REQUIRES: `combined_proof` has type `Nat.le lhs rhs` (up to def-eq)
/// ENSURES: On `Some(proof)`, `proof` has type `goal_target`
/// ENSURES: On `None`, neither route applies
fn try_close_contradictory_le(
    combined_proof: Expr,
    lhs: &Expr,
    rhs: &Expr,
    goal_target: &Expr,
) -> Option<Expr> {
    // Route 1: concrete endpoints.
    if let (Some(lhs_val), Some(rhs_val)) = (eval_nat_expr(lhs), eval_nat_expr(rhs)) {
        if lhs_val <= rhs_val {
            return None;
        }
        let false_proof = derive_false_from_contradictory_le(combined_proof, lhs_val, rhs_val)?;
        return Some(wrap_false_elim(false_proof, goal_target));
    }
    // Route 2: symbolic cancellation.
    try_close_contradictory_nat_le_symbolic(&combined_proof, lhs, rhs, goal_target)
}

/// Derive `False` from `h : Nat.le (core + c1) (core + c2)` with `c1 > c2`.
///
/// Construction (mirrors `order_nat_le_antisymm_proof.rs`):
/// - `step : Nat.le (Nat.succ rhs) lhs` built from `Nat.le.refl`/`Nat.le.step`
///   (valid since `c1 >= c2 + 1`, i.e. `succ rhs` has offset `c2 + 1 <= c1`).
/// - `Nat.le_trans (Nat.succ rhs) lhs rhs step h : Nat.le (Nat.succ rhs) rhs`
///   which is `Nat.lt rhs rhs`.
/// - `Nat.lt_irrefl rhs (...) : False`.
///
/// All three constants (`Nat.le.refl`/`Nat.le.step`, `Nat.le_trans`,
/// `Nat.lt_irrefl`) are constructive prelude theorems / inductive constructors,
/// so the resulting `False` term carries no domain axioms. `close_goal` still
/// re-checks it.
fn try_close_contradictory_nat_le_symbolic(
    proof: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    goal_target: &Expr,
) -> Option<Expr> {
    use crate::tactic::arith_linarith_nat_direct::{nat_le_via_steps, nat_split_core_offset};

    let (lhs_core, lhs_off) = nat_split_core_offset(lhs)?;
    let (rhs_core, rhs_off) = nat_split_core_offset(rhs)?;
    if lhs_core != rhs_core || lhs_off <= rhs_off {
        return None;
    }

    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_rhs = Expr::app(succ, rhs.clone());

    // step : Nat.le (succ rhs) lhs.  succ rhs has offset rhs_off + 1 <= lhs_off,
    // so we weaken from `Nat.le.refl (succ rhs)` by `lhs_off - (rhs_off + 1)`.
    let steps = lhs_off - rhs_off - 1;
    let step = nat_le_via_steps(&succ_rhs, steps);

    // Nat.le_trans (succ rhs) lhs rhs step proof : Nat.le (succ rhs) rhs ≡ Nat.lt rhs rhs
    let le_trans = Expr::const_(Name::from_string("Nat.le_trans"), vec![]);
    let lt_proof = Expr::apps(
        le_trans,
        [succ_rhs, lhs.clone(), rhs.clone(), step, proof.clone()],
    );

    // Nat.lt_irrefl rhs lt_proof : False
    let lt_irrefl = Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]);
    let false_proof = Expr::apps(lt_irrefl, [rhs.clone(), lt_proof]);

    Some(wrap_false_elim(false_proof, goal_target))
}

/// Evaluate an Int expression to a concrete i64 value.
///
/// Handles `Int.ofNat(n)`, `Int.negSucc(n)`, `Int.add(a, b)`, `Int.mul(a, b)`.
///
/// REQUIRES: `expr` is a well-formed kernel expression
/// ENSURES: On `Some(n)`, `expr` evaluates to `n` as i64
/// ENSURES: On `None`, `expr` contains free variables or unrecognized constructors
fn eval_int_expr(expr: &Expr) -> Option<i64> {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(n)) => {
            use clean_kernel::expr::BigNat;
            match n {
                BigNat::Small(v) => i64::try_from(*v).ok(),
                BigNat::Big(_) => None,
            }
        }
        ExprKind::App(f, arg) => {
            // Binary: Int.add a b, Int.mul a b, Int.sub a b
            if let ExprKind::App(f2, arg1) = f.kind() {
                if let ExprKind::Const(name, _) = f2.kind() {
                    let s = name.to_string();
                    match s.as_str() {
                        "Int.add" => {
                            return eval_int_expr(arg1)?.checked_add(eval_int_expr(arg)?);
                        }
                        "Int.mul" => {
                            return eval_int_expr(arg1)?.checked_mul(eval_int_expr(arg)?);
                        }
                        "Int.sub" => {
                            return eval_int_expr(arg1)?.checked_sub(eval_int_expr(arg)?);
                        }
                        _ => {}
                    }
                }
            }
            // Unary: Int.ofNat n, Int.negSucc n
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                match s.as_str() {
                    "Int.ofNat" => {
                        let n = eval_nat_expr(arg)?;
                        return i64::try_from(n).ok();
                    }
                    "Int.negSucc" => {
                        let n = eval_nat_expr(arg)?;
                        let pos = i64::try_from(n).ok()?;
                        return pos.checked_add(1).and_then(|v| v.checked_neg());
                    }
                    _ => {}
                }
            }
            None
        }
        _ => None,
    }
}

/// Extract children from `Int.add(a, b)`.
fn extract_int_add_children(expr: &Expr) -> Option<(Expr, Expr)> {
    if let ExprKind::App(f, b) = expr.kind() {
        if let ExprKind::App(f2, a) = f.kind() {
            if let ExprKind::Const(name, _) = f2.kind() {
                if name.to_string() == "Int.add" {
                    return Some(((**a).clone(), (**b).clone()));
                }
            }
        }
    }
    None
}

/// Cancel identical additive context from both sides of an Int inequality.
///
/// If `lhs = Int.add(a, b)` and `rhs = Int.add(a, c)` (identical left addend),
/// applies `Int.le_of_add_le_add_left a b c h` to produce `Int.le b c`.
///
/// If `lhs = Int.add(b, a)` and `rhs = Int.add(c, a)` (identical right addend),
/// applies `Int.le_of_add_le_add_right a b c h` to produce `Int.le b c`.
fn cancel_int_add_context(proof: &Expr, lhs: &Expr, rhs: &Expr) -> Option<(Expr, Expr, Expr)> {
    let (lhs_a, lhs_b) = extract_int_add_children(lhs)?;
    let (rhs_a, rhs_b) = extract_int_add_children(rhs)?;

    if lhs_a == rhs_a {
        // Int.le_of_add_le_add_left : ∀ a b c, Int.le (Int.add a b) (Int.add a c) → Int.le b c
        let result = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Int.le_of_add_le_add_left"), vec![]),
                        lhs_a,
                    ),
                    lhs_b.clone(),
                ),
                rhs_b.clone(),
            ),
            proof.clone(),
        );
        return Some((lhs_b, rhs_b, result));
    }

    if lhs_b == rhs_b {
        // Int.le_of_add_le_add_right : ∀ a b c, Int.le (Int.add a b) (Int.add c b) → Int.le a c
        let result = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Int.le_of_add_le_add_right"), vec![]),
                        lhs_a.clone(),
                    ),
                    lhs_b,
                ),
                rhs_a.clone(),
            ),
            proof.clone(),
        );
        return Some((lhs_a, rhs_a, result));
    }

    None
}

/// Try to derive `False` from a contradictory Int inequality and close the goal.
///
/// First tries direct concrete evaluation. If the endpoints are symbolic
/// (contain shared additive context), cancels identical addends via
/// `Int.le_of_add_le_add_left/right` before retrying (#2621).
///
/// REQUIRES: `combined_proof` has type `Int.le lhs rhs` (via NonNeg)
/// ENSURES: On `Some(proof)`, `proof` has type `goal_target`
/// ENSURES: On `None`, not concrete Int values or not contradictory
fn try_close_contradictory_int_le(
    combined_proof: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    goal_target: &Expr,
) -> Option<Expr> {
    // Direct concrete evaluation
    if let (Some(lhs_val), Some(rhs_val)) = (eval_int_expr(lhs), eval_int_expr(rhs)) {
        if lhs_val > rhs_val {
            let false_proof = mk_int_concrete_false(CmpOp::Le, lhs, rhs, combined_proof);
            return Some(wrap_false_elim(false_proof, goal_target));
        }
        return None;
    }

    // Additive cancellation then retry
    let (reduced_lhs, reduced_rhs, reduced_proof) =
        cancel_int_add_context(combined_proof, lhs, rhs)?;
    try_close_contradictory_int_le(&reduced_proof, &reduced_lhs, &reduced_rhs, goal_target)
}

/// Try to close a contradictory `Real.le lhs rhs` by downcasting to Int.
///
/// For endpoints that are `Real.ofNat(n)`, `Real.ofInt(e)`, or additive trees
/// built from these (`Real.add`), normalizes to `Real.ofInt` form, downcasts
/// via `Real.ofInt_le_to_Int`, then delegates to `try_close_contradictory_int_le`.
///
/// The Int closer supports additive cancellation (#2621), so symbolic
/// integer-valued additive contradictions like `Int.add m 5 <= Int.add m 3`
/// are handled after downcast.
///
/// Returns `None` for non-integer-valued Real endpoints.
fn try_close_contradictory_real_le(
    combined_proof: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    goal_target: &Expr,
) -> Option<Expr> {
    let (int_lhs, int_rhs, int_proof) =
        super::arith_linarith_real_downcast::downcast_integer_valued_real_le_proof_to_int(
            combined_proof,
            lhs,
            rhs,
        )?;
    try_close_contradictory_int_le(&int_proof, &int_lhs, &int_rhs, goal_target)
}

/// Sort-dispatched contradiction closing: tries Nat, Int, or Real evaluation.
///
/// ENSURES: On `Some(proof)`, `proof` has type `goal_target`
pub(crate) fn try_close_contradictory_le_generic(
    sort: ArithSort,
    combined_proof: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    goal_target: &Expr,
) -> Option<Expr> {
    match sort {
        ArithSort::Nat => try_close_contradictory_le(combined_proof.clone(), lhs, rhs, goal_target),
        ArithSort::Int => try_close_contradictory_int_le(combined_proof, lhs, rhs, goal_target),
        ArithSort::Real => try_close_contradictory_real_le(combined_proof, lhs, rhs, goal_target),
        // Rat integer-valued endpoints downcast via Int.cast_le_prop (#3367).
        ArithSort::Rat => try_close_contradictory_rat_le(combined_proof, lhs, rhs, goal_target),
    }
}

/// Try to close a contradictory `Rat.le lhs rhs` (or def-eq
/// `LE.le Rat instLERat lhs rhs`) by downcasting integer-valued endpoints
/// (`Rat.ofInt(int_expr)`) to `Int.le` via `Int.cast_le_prop` and delegating
/// to the Int concrete-contradiction closer (#3367).
///
/// REQUIRES: `combined_proof` has a type kernel-def-eq to `Rat.le lhs rhs`
/// REQUIRES: `Int.cast_le_prop` is registered (via `init_cast_simp_lemmas`)
/// ENSURES: On `Some(proof)`, `proof` has type `goal_target`
/// ENSURES: On `None`, endpoints are not concrete integer-valued Rat
fn try_close_contradictory_rat_le(
    combined_proof: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    goal_target: &Expr,
) -> Option<Expr> {
    let (int_lhs, int_rhs, int_proof) =
        super::arith_linarith_rat_downcast::downcast_integer_valued_rat_le_proof_to_int(
            combined_proof,
            lhs,
            rhs,
        )?;
    try_close_contradictory_int_le(&int_proof, &int_lhs, &int_rhs, goal_target)
}
