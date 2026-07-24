// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared arithmetic chain proof builders.
//!
//! Cross-crate contract for sort-generic comparison chain construction
//! (Nat/Int/Real transitivity, irreflexivity, antisymmetry). Used by both the
//! SMT bridge (`clean-auto`) and the linarith tactic (`clean-elab`).
//!
//! Part of #2905 (shared builder consolidation) and #2442 Phase 2D.

use clean_kernel::expr::{BigNat, Literal};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

/// Arithmetic sort for comparison chain construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithSort {
    Nat,
    Int,
    Real,
    /// Rat maps to SMT Real (dense ordered field) but uses its own kernel lemmas.
    Rat,
}

/// Comparison operator kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CmpOp {
    Le,
    Lt,
}

/// Detect the arithmetic sort from a type expression (the `α` in `@LE.le α inst a b`).
pub fn detect_sort(alpha: &Expr) -> Option<ArithSort> {
    if let ExprKind::Const(name, _) = alpha.kind() {
        match name.to_string().as_str() {
            "Nat" => Some(ArithSort::Nat),
            "Int" => Some(ArithSort::Int),
            "Real" => Some(ArithSort::Real),
            "Rat" => Some(ArithSort::Rat),
            _ => None,
        }
    } else {
        None
    }
}

/// Determine the result comparison op when chaining two ops.
///
/// Returns `CmpOp::Le` iff both inputs are `Le`; `CmpOp::Lt` if either is `Lt`.
pub fn combine_ops(left: CmpOp, right: CmpOp) -> CmpOp {
    match (left, right) {
        (CmpOp::Le, CmpOp::Le) => CmpOp::Le,
        _ => CmpOp::Lt,
    }
}

fn mk_apply(lemma: &str, args: &[&Expr]) -> Expr {
    let mut expr = Expr::const_(Name::from_string(lemma), vec![]);
    for arg in args {
        expr = Expr::app(expr, (*arg).clone());
    }
    expr
}

fn eval_small_nat(expr: &Expr) -> Option<u64> {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(n)) => match n {
            BigNat::Small(v) => Some(*v),
            BigNat::Big(_) => None,
        },
        ExprKind::Const(name, _) if name.to_string() == "Nat.zero" => Some(0),
        ExprKind::App(fun, rhs) => match fun.kind() {
            ExprKind::App(head, lhs) => match head.kind() {
                ExprKind::Const(name, _) if name.to_string() == "Nat.add" => {
                    eval_small_nat(lhs)?.checked_add(eval_small_nat(rhs)?)
                }
                // `Nat.mul` mirrors the `Nat.add` ground-reduction lane: recurse
                // into both operands (so nested `add`/`mul` on numerals fold) and
                // fail closed on overflow via `checked_mul` — bounded to small
                // numerals exactly as the `add` case is (no panic, no wraparound).
                ExprKind::Const(name, _) if name.to_string() == "Nat.mul" => {
                    eval_small_nat(lhs)?.checked_mul(eval_small_nat(rhs)?)
                }
                _ => None,
            },
            ExprKind::Const(name, _) if name.to_string() == "Nat.succ" => {
                eval_small_nat(rhs).and_then(|n| n.checked_add(1))
            }
            _ => None,
        },
        _ => None,
    }
}

fn mk_nat_le_constructor_chain(start: u64, end: u64) -> Option<Expr> {
    if start > end {
        return None;
    }

    let le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
    let le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);

    let mut proof = Expr::app(le_refl, Expr::nat_lit(start));
    for current_rhs in start..end {
        proof = Expr::app(
            Expr::app(
                Expr::app(le_step.clone(), Expr::nat_lit(start)),
                Expr::nat_lit(current_rhs),
            ),
            proof,
        );
    }
    Some(proof)
}

fn mk_nat_ground_le_from_values(lhs_val: u64, rhs_val: u64) -> Option<Expr> {
    mk_nat_le_constructor_chain(lhs_val, rhs_val)
}

fn mk_nat_ground_lt_from_values(lhs_val: u64, rhs_val: u64) -> Option<Expr> {
    let succ_lhs = lhs_val.checked_add(1)?;
    mk_nat_le_constructor_chain(succ_lhs, rhs_val)
}

/// Build a sort-dispatched le_trans / lt_trans / mixed chain step proof.
///
/// All chain-step lemmas take 5 args: `@Lemma a b c h1 h2`.
pub fn mk_chain_step(
    sort: ArithSort,
    a: &Expr,
    b: &Expr,
    c: &Expr,
    left_op: CmpOp,
    right_op: CmpOp,
    h1: &Expr,
    h2: &Expr,
) -> Expr {
    let lemma = match (sort, left_op, right_op) {
        (ArithSort::Nat, CmpOp::Le, CmpOp::Le) => "Nat.le_trans",
        (ArithSort::Nat, CmpOp::Le, CmpOp::Lt) => "Nat.lt_of_le_of_lt",
        (ArithSort::Nat, CmpOp::Lt, CmpOp::Le) => "Nat.lt_of_lt_of_le",
        (ArithSort::Nat, CmpOp::Lt, CmpOp::Lt) => "Nat.lt_trans",
        (ArithSort::Int, CmpOp::Le, CmpOp::Le) => "Int.le_trans",
        (ArithSort::Int, CmpOp::Le, CmpOp::Lt) => "Int.lt_of_le_of_lt",
        (ArithSort::Int, CmpOp::Lt, CmpOp::Le) => "Int.lt_of_lt_of_le",
        (ArithSort::Int, CmpOp::Lt, CmpOp::Lt) => "Int.lt_trans",
        (ArithSort::Real, CmpOp::Le, CmpOp::Le) => "Real.le_trans",
        (ArithSort::Real, CmpOp::Le, CmpOp::Lt) => "Real.lt_of_le_of_lt",
        (ArithSort::Real, CmpOp::Lt, CmpOp::Le) => "Real.lt_of_lt_of_le",
        (ArithSort::Real, CmpOp::Lt, CmpOp::Lt) => "Real.lt_trans",
        // Rat uses its own kernel lemmas (registered by algebra_field.rs)
        (ArithSort::Rat, CmpOp::Le, CmpOp::Le) => "Rat.le_trans",
        (ArithSort::Rat, CmpOp::Le, CmpOp::Lt) => "Rat.lt_of_le_of_lt",
        (ArithSort::Rat, CmpOp::Lt, CmpOp::Le) => "Rat.lt_of_lt_of_le",
        (ArithSort::Rat, CmpOp::Lt, CmpOp::Lt) => "Rat.lt_trans",
    };
    mk_apply(lemma, &[a, b, c, h1, h2])
}

/// Build `@{Sort}.le_refl a`.
pub(crate) fn mk_le_refl(sort: ArithSort, a: &Expr) -> Expr {
    let lemma = match sort {
        ArithSort::Nat => "Nat.le_refl",
        ArithSort::Int => "Int.le_refl",
        ArithSort::Real => "Real.le_refl",
        ArithSort::Rat => "Rat.le_refl",
    };
    mk_apply(lemma, &[a])
}

/// Build `@{Sort}.le_of_lt a b proof`. Returns `None` for Real and Rat.
pub(crate) fn mk_le_of_lt(sort: ArithSort, a: &Expr, b: &Expr, proof: &Expr) -> Option<Expr> {
    let lemma = match sort {
        ArithSort::Nat => "Nat.le_of_lt",
        ArithSort::Int => "Int.le_of_lt",
        ArithSort::Real | ArithSort::Rat => return None,
    };
    Some(mk_apply(lemma, &[a, b, proof]))
}

/// Build `False` from a cyclic strict chain `a < a` using `{Sort}.lt_irrefl`.
pub fn mk_lt_irrefl_false(sort: ArithSort, a: &Expr, proof: &Expr) -> Expr {
    let lemma = match sort {
        ArithSort::Nat => "Nat.lt_irrefl",
        ArithSort::Int => "Int.lt_irrefl",
        ArithSort::Real => "Real.lt_irrefl",
        ArithSort::Rat => "Rat.lt_irrefl",
    };
    mk_apply(lemma, &[a, proof])
}

/// Build `False` from a contradictory concrete Int bound.
pub fn mk_int_concrete_false(op: CmpOp, start: &Expr, end_: &Expr, chain_proof: &Expr) -> Expr {
    let int_sub = Expr::const_(Name::from_string("Int.sub"), vec![]);
    let nonneg_index = match op {
        CmpOp::Le => Expr::app(Expr::app(int_sub, end_.clone()), start.clone()),
        CmpOp::Lt => {
            let one = Expr::app(
                Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                Expr::app(
                    Expr::const_(Name::from_string("Nat.succ"), vec![]),
                    Expr::const_(Name::from_string("Nat.zero"), vec![]),
                ),
            );
            let start_plus_one = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Int.add"), vec![]),
                    start.clone(),
                ),
                one,
            );
            Expr::app(Expr::app(int_sub, end_.clone()), start_plus_one)
        }
    };
    mk_nonneg_caseson_false(&nonneg_index, chain_proof)
}

fn mk_nonneg_caseson_false(nonneg_index: &Expr, chain_proof: &Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let int_cases_motive = Expr::lam(BinderInfo::Default, int_ty.clone(), prop);
    let ofnat_branch = Expr::lam(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::const_(Name::from_string("True"), vec![]),
    );
    let negsucc_branch = Expr::lam(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::const_(Name::from_string("False"), vec![]),
    );
    let int_caseson = Expr::const_(
        Name::from_string("Int.casesOn"),
        vec![Level::succ(Level::zero())],
    );
    // Lean-faithful casesOn order: motive, major, then minors.
    let motive_body = Expr::app(
        Expr::app(
            Expr::app(Expr::app(int_caseson, int_cases_motive), Expr::bvar(1)),
            ofnat_branch,
        ),
        negsucc_branch,
    );

    let nonneg_of_x = Expr::app(
        Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
        Expr::bvar(0),
    );
    let motive = Expr::lam(
        BinderInfo::Default,
        int_ty,
        Expr::lam(BinderInfo::Default, nonneg_of_x, motive_body),
    );
    let mk_branch = Expr::lam(
        BinderInfo::Default,
        nat_ty,
        Expr::const_(Name::from_string("True.intro"), vec![]),
    );
    // `Int.NonNeg` is a Prop-valued inductive with ZERO level params, so the
    // kernel's Prop-only elimination gives its `casesOn` ZERO level arguments.
    // Emitting `.{0}` makes the kernel reject the refutation with
    // `LevelCountMismatch { Int.NonNeg.casesOn, expected: 0, got: 1 }`.
    let nonneg_caseson = Expr::const_(Name::from_string("Int.NonNeg.casesOn"), vec![]);
    // Lean-faithful casesOn order: motive, index, major, then minors.
    Expr::app(
        Expr::app(
            Expr::app(Expr::app(nonneg_caseson, motive), nonneg_index.clone()),
            chain_proof.clone(),
        ),
        mk_branch,
    )
}

/// Build `@{Sort}.le_antisymm a b hab hba`.
pub(crate) fn mk_le_antisymm(sort: ArithSort, a: &Expr, b: &Expr, hab: &Expr, hba: &Expr) -> Expr {
    let lemma = match sort {
        ArithSort::Nat => "Nat.le_antisymm",
        ArithSort::Int => "Int.le_antisymm",
        ArithSort::Real => "Real.le_antisymm",
        ArithSort::Rat => "Rat.le_antisymm",
    };
    mk_apply(lemma, &[a, b, hab, hba])
}

/// Build a ground Nat `≤` proof from literal expressions.
pub(crate) fn mk_nat_ground_le(lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    let lhs_val = eval_small_nat(lhs)?;
    let rhs_val = eval_small_nat(rhs)?;
    mk_nat_ground_le_from_values(lhs_val, rhs_val)
}

/// Build a ground Nat `<` proof from literal expressions.
pub(crate) fn mk_nat_ground_lt(lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    let lhs_val = eval_small_nat(lhs)?;
    let rhs_val = eval_small_nat(rhs)?;
    mk_nat_ground_lt_from_values(lhs_val, rhs_val)
}

#[cfg(test)]
mod tests {
    use super::{
        combine_ops, detect_sort, eval_small_nat, mk_le_of_lt, mk_le_refl, mk_lt_irrefl_false,
        mk_nat_ground_le, mk_nat_ground_lt, ArithSort, CmpOp,
    };
    use clean_kernel::name::Name;
    use clean_kernel::{Expr, ExprKind};

    fn assert_head_const_name(expr: &Expr, expected: &str) {
        let head = expr.get_app_fn();
        assert!(
            matches!(head.kind(), ExprKind::Const(name, _) if name.to_string() == expected),
            "expected proof term head {expected}, got {head:?}"
        );
    }

    #[test]
    fn test_mk_nat_ground_le_zero_le_shape() {
        let proof = mk_nat_ground_le(&Expr::nat_lit(0), &Expr::nat_lit(1))
            .expect("0 <= 1 should produce a Nat ground proof");
        assert_head_const_name(&proof, "Nat.le.step");
    }

    #[test]
    fn test_mk_nat_ground_lt_recursive_shape() {
        let proof = mk_nat_ground_lt(&Expr::nat_lit(3), &Expr::nat_lit(7))
            .expect("3 < 7 should produce a Nat ground proof");
        assert_head_const_name(&proof, "Nat.le.step");
    }

    #[test]
    fn test_mk_nat_ground_le_rejects_false_goal() {
        assert!(
            mk_nat_ground_le(&Expr::nat_lit(2), &Expr::nat_lit(1)).is_none(),
            "2 <= 1 should not produce a Nat ground proof"
        );
    }

    #[test]
    fn test_mk_nat_ground_lt_rejects_false_goal() {
        let lhs = Expr::const_(Name::from_string("a"), vec![]);
        assert!(
            mk_nat_ground_lt(&lhs, &Expr::nat_lit(1)).is_none(),
            "non-literal Nat < goals should stay unsupported in the ground builder"
        );
    }

    #[test]
    fn test_mk_nat_ground_le_supports_nat_add_literals() {
        let lhs = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.add"), vec![]),
                Expr::nat_lit(2),
            ),
            Expr::nat_lit(3),
        );
        let proof = mk_nat_ground_le(&lhs, &Expr::nat_lit(5))
            .expect("2 + 3 <= 5 should reduce to a ground Nat proof");
        assert_head_const_name(&proof, "Nat.le.refl");
    }

    #[test]
    fn test_mk_nat_ground_lt_supports_nat_add_literals() {
        let lhs = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.add"), vec![]),
                Expr::nat_lit(2),
            ),
            Expr::nat_lit(2),
        );
        let proof = mk_nat_ground_lt(&lhs, &Expr::nat_lit(5))
            .expect("2 + 2 < 5 should reduce to a ground Nat proof");
        assert_head_const_name(&proof, "Nat.le.refl");
    }

    #[test]
    fn test_eval_small_nat_nat_add_overflow_returns_none() {
        let overflow_sum = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.add"), vec![]),
                Expr::nat_lit(u64::MAX),
            ),
            Expr::nat_lit(1),
        );
        assert!(
            eval_small_nat(&overflow_sum).is_none(),
            "overflowing Nat.add should fail closed instead of panicking"
        );
    }

    #[test]
    fn test_mk_nat_ground_le_supports_nat_mul_literals() {
        // 2 * 3 = 6, so the equality lane's `2*3 <= 6` sub-goal must reduce.
        let lhs = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.mul"), vec![]),
                Expr::nat_lit(2),
            ),
            Expr::nat_lit(3),
        );
        let proof = mk_nat_ground_le(&lhs, &Expr::nat_lit(6))
            .expect("2 * 3 <= 6 should reduce to a ground Nat proof");
        assert_head_const_name(&proof, "Nat.le.refl");
    }

    #[test]
    fn test_mk_nat_ground_le_supports_nested_add_mul_literals() {
        // (2 + 3) * 2 = 10 — nested add-under-mul must fold recursively.
        let inner_add = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.add"), vec![]),
                Expr::nat_lit(2),
            ),
            Expr::nat_lit(3),
        );
        let lhs = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.mul"), vec![]),
                inner_add,
            ),
            Expr::nat_lit(2),
        );
        let proof = mk_nat_ground_le(&lhs, &Expr::nat_lit(10))
            .expect("(2 + 3) * 2 <= 10 should reduce to a ground Nat proof");
        assert_head_const_name(&proof, "Nat.le.refl");
    }

    #[test]
    fn test_eval_small_nat_nat_mul_overflow_returns_none() {
        let overflow_prod = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.mul"), vec![]),
                Expr::nat_lit(u64::MAX),
            ),
            Expr::nat_lit(2),
        );
        assert!(
            eval_small_nat(&overflow_prod).is_none(),
            "overflowing Nat.mul should fail closed instead of panicking"
        );
    }

    #[test]
    fn test_detect_sort_nat() {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        assert_eq!(detect_sort(&nat), Some(ArithSort::Nat));
    }

    #[test]
    fn test_detect_sort_int() {
        let int = Expr::const_(Name::from_string("Int"), vec![]);
        assert_eq!(detect_sort(&int), Some(ArithSort::Int));
    }

    #[test]
    fn test_detect_sort_real() {
        let real = Expr::const_(Name::from_string("Real"), vec![]);
        assert_eq!(detect_sort(&real), Some(ArithSort::Real));
    }

    #[test]
    fn test_detect_sort_rat() {
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        assert_eq!(detect_sort(&rat), Some(ArithSort::Rat));
    }

    #[test]
    fn test_detect_sort_unknown_returns_none() {
        let unknown = Expr::const_(Name::from_string("Complex"), vec![]);
        assert_eq!(detect_sort(&unknown), None);
    }

    #[test]
    fn test_detect_sort_non_const_returns_none() {
        assert_eq!(detect_sort(&Expr::bvar(0)), None);
    }

    #[test]
    fn test_combine_ops_le_le_is_le() {
        assert_eq!(combine_ops(CmpOp::Le, CmpOp::Le), CmpOp::Le);
    }

    #[test]
    fn test_combine_ops_le_lt_is_lt() {
        assert_eq!(combine_ops(CmpOp::Le, CmpOp::Lt), CmpOp::Lt);
    }

    #[test]
    fn test_combine_ops_lt_le_is_lt() {
        assert_eq!(combine_ops(CmpOp::Lt, CmpOp::Le), CmpOp::Lt);
    }

    #[test]
    fn test_combine_ops_lt_lt_is_lt() {
        assert_eq!(combine_ops(CmpOp::Lt, CmpOp::Lt), CmpOp::Lt);
    }

    #[test]
    fn test_mk_le_of_lt_nat_produces_proof() {
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let b = Expr::const_(Name::from_string("b"), vec![]);
        let h = Expr::const_(Name::from_string("h"), vec![]);

        let result = mk_le_of_lt(ArithSort::Nat, &a, &b, &h);
        assert!(result.is_some(), "Nat le_of_lt should produce a proof");
        assert_head_const_name(&result.unwrap(), "Nat.le_of_lt");
    }

    #[test]
    fn test_mk_le_of_lt_int_produces_proof() {
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let b = Expr::const_(Name::from_string("b"), vec![]);
        let h = Expr::const_(Name::from_string("h"), vec![]);

        let result = mk_le_of_lt(ArithSort::Int, &a, &b, &h);
        assert!(result.is_some(), "Int le_of_lt should produce a proof");
        assert_head_const_name(&result.unwrap(), "Int.le_of_lt");
    }

    #[test]
    fn test_mk_le_of_lt_real_returns_none() {
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let b = Expr::const_(Name::from_string("b"), vec![]);
        let h = Expr::const_(Name::from_string("h"), vec![]);

        let result = mk_le_of_lt(ArithSort::Real, &a, &b, &h);
        assert!(
            result.is_none(),
            "Real le_of_lt must return None (not supported)"
        );
    }

    #[test]
    fn test_mk_le_refl_int() {
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let proof = mk_le_refl(ArithSort::Int, &a);
        assert_head_const_name(&proof, "Int.le_refl");
    }

    #[test]
    fn test_mk_le_refl_real() {
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let proof = mk_le_refl(ArithSort::Real, &a);
        assert_head_const_name(&proof, "Real.le_refl");
    }

    #[test]
    fn test_mk_lt_irrefl_false_int() {
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let h = Expr::const_(Name::from_string("h"), vec![]);
        let proof = mk_lt_irrefl_false(ArithSort::Int, &a, &h);
        assert_head_const_name(&proof, "Int.lt_irrefl");
    }

    #[test]
    fn test_mk_lt_irrefl_false_real() {
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let h = Expr::const_(Name::from_string("h"), vec![]);
        let proof = mk_lt_irrefl_false(ArithSort::Real, &a, &h);
        assert_head_const_name(&proof, "Real.lt_irrefl");
    }
}
