// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sort-generic inequality scaling accumulators for linarith proof reconstruction.
//!
//! Extracted from `arith_linarith_proof.rs` to stay under the 500-line limit (#2630).

use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

use super::arith_linarith_chain;
use super::arith_linarith_proof::{extract_le_args, find_hyp_type};
use super::arith_linarith_real_downcast;
use super::Goal;
use clean_auto::arith_proof::ArithSort;

/// Sort-generic inequality proof accumulator: tracks `(sort, lhs, rhs, proof)` through
/// sort-appropriate addition combination steps (#2493, #302).
///
/// - Nat: `Nat.add_le_add` (single-step binary combination)
/// - Int: `Int.add_le_add_right` + `Int.add_le_add_left` + `Int.le_trans` (3-step)
/// - Real: `Real.add_le_add_right` + `Real.add_le_add_left` + `Real.le_trans` (3-step)
pub(crate) struct SortLeAcc {
    pub(crate) sort: ArithSort,
    pub(crate) lhs: Expr,
    pub(crate) rhs: Expr,
    pub(crate) proof: Expr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RealAccumulationMode {
    PreserveReal,
    DowncastToInt,
}

impl SortLeAcc {
    /// Construct a Nat accumulator directly from `(lhs, rhs, proof)` where
    /// `proof` has a type kernel-def-eq to `Nat.le lhs rhs` (e.g. a `Nat.lt`
    /// proof reused as `Nat.le (succ ·) ·`). Used by the Farkas-with-goal
    /// builder to inject the negated-goal inequality; the kernel re-checks the
    /// assembled term, so a def-eq mismatch fails closed.
    pub(crate) fn nat_from_parts(lhs: Expr, rhs: Expr, proof: Expr) -> Option<Self> {
        Some(SortLeAcc {
            sort: ArithSort::Nat,
            lhs,
            rhs,
            proof,
        })
    }

    /// From `fvar : a ≤ b` to `(sort, a, b, fvar)`, optionally downcasting
    /// concrete-all-Real slices to Int.
    pub(crate) fn from_hypothesis(
        fvar: FVarId,
        goal: &Goal,
        real_mode: RealAccumulationMode,
    ) -> Option<Self> {
        let h_ty = find_hyp_type(goal, fvar)?;
        let (alpha, lhs, rhs) = extract_le_args(&h_ty)?;
        let sort = arith_linarith_chain::detect_sort(&alpha)?;
        if sort == ArithSort::Real && real_mode == RealAccumulationMode::DowncastToInt {
            if let Some(acc) = Self::from_real_downcast(fvar, &lhs, &rhs) {
                return Some(acc);
            }
        }
        Some(SortLeAcc {
            sort,
            lhs,
            rhs,
            proof: Expr::fvar(fvar),
        })
    }

    /// Downcast a Real hypothesis to Int for proof reconstruction.
    fn from_real_downcast(fvar: FVarId, lhs: &Expr, rhs: &Expr) -> Option<Self> {
        let (int_lhs, int_rhs, h_int) =
            arith_linarith_real_downcast::downcast_real_le_to_int(fvar, lhs, rhs)?;
        Some(SortLeAcc {
            sort: ArithSort::Int,
            lhs: int_lhs,
            rhs: int_rhs,
            proof: h_int,
        })
    }

    /// From a scaled hypothesis (coeff > 1).
    ///
    /// - Nat: single-step via `Nat.mul_le_mul_left a b c h` → `c*a ≤ c*b`
    /// - Int (including downcasted Real→Int): compact multiplication via
    ///   `Int.mul_le_mul_of_nonneg_left` with `Int.ofNat coeff` (#2630)
    /// - Real (preserved): repeated self-addition via `add_le_add`
    pub(crate) fn from_scaled(
        fvar: FVarId,
        coeff: i128,
        goal: &Goal,
        real_mode: RealAccumulationMode,
    ) -> Option<Self> {
        let h_ty = find_hyp_type(goal, fvar)?;
        let (alpha, a, b) = extract_le_args(&h_ty)?;
        let sort = arith_linarith_chain::detect_sort(&alpha)?;

        if sort == ArithSort::Nat {
            let coeff_u64 = u64::try_from(coeff).ok()?;
            let coeff_expr = Expr::nat_lit(coeff_u64);
            let mul_le = Expr::const_(Name::from_string("Nat.mul_le_mul_left"), vec![]);
            let proof = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(mul_le, a.clone()), b.clone()),
                    coeff_expr.clone(),
                ),
                Expr::fvar(fvar),
            );
            let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
            let lhs = Expr::app(Expr::app(nat_mul.clone(), coeff_expr.clone()), a);
            let rhs = Expr::app(Expr::app(nat_mul, coeff_expr), b);
            Some(SortLeAcc {
                sort,
                lhs,
                rhs,
                proof,
            })
        } else if sort == ArithSort::Int
            || (sort == ArithSort::Real && real_mode == RealAccumulationMode::DowncastToInt)
        {
            let acc = Self::from_hypothesis(fvar, goal, real_mode)?;
            build_compact_int_scaled_acc(acc, coeff)
        } else {
            // Preserved Real: repeated self-addition via existing combine infrastructure.
            let coeff_i64 = match i64::try_from(coeff) {
                Ok(value) => value,
                Err(_) => {
                    tracing::debug!(
                        coeff = %coeff,
                        "build_linarith_proof: preserved-Real scaling coefficient exceeds repeated-add support"
                    );
                    return None;
                }
            };
            let mut acc = Self::from_hypothesis(fvar, goal, real_mode)?;
            for _ in 1..coeff_i64 {
                let next = Self::from_hypothesis(fvar, goal, real_mode)?;
                acc = acc.combine(next)?;
            }
            Some(acc)
        }
    }

    /// Combine: `(lhs1, rhs1) + (lhs2, rhs2)` → `(lhs1+lhs2, rhs1+rhs2)`.
    pub(crate) fn combine(self, next: SortLeAcc) -> Option<SortLeAcc> {
        if self.sort != next.sort {
            return None;
        }
        Some(match self.sort {
            ArithSort::Nat => self.combine_nat(next),
            ArithSort::Int => self.combine_int_or_real(next, "Int"),
            ArithSort::Real => self.combine_int_or_real(next, "Real"),
            ArithSort::Rat => self.combine_int_or_real(next, "Rat"),
        })
    }

    fn combine_nat(self, next: SortLeAcc) -> SortLeAcc {
        let add_le_add = Expr::const_(Name::from_string("Nat.add_le_add"), vec![]);
        let proof = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(add_le_add, self.lhs.clone()), self.rhs.clone()),
                        next.lhs.clone(),
                    ),
                    next.rhs.clone(),
                ),
                self.proof,
            ),
            next.proof,
        );
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let lhs = Expr::app(Expr::app(nat_add.clone(), self.lhs), next.lhs);
        let rhs = Expr::app(Expr::app(nat_add, self.rhs), next.rhs);
        SortLeAcc {
            sort: ArithSort::Nat,
            lhs,
            rhs,
            proof,
        }
    }

    fn combine_int_or_real(self, next: SortLeAcc, sort_prefix: &str) -> SortLeAcc {
        let sort_add = Expr::const_(Name::from_string(&format!("{sort_prefix}.add")), vec![]);
        let add_right = Expr::const_(
            Name::from_string(&format!("{sort_prefix}.add_le_add_right")),
            vec![],
        );
        let step1 = Expr::app(
            Expr::app(
                Expr::app(Expr::app(add_right, self.lhs.clone()), self.rhs.clone()),
                self.proof,
            ),
            next.lhs.clone(),
        );
        let add_left = Expr::const_(
            Name::from_string(&format!("{sort_prefix}.add_le_add_left")),
            vec![],
        );
        let step2 = Expr::app(
            Expr::app(
                Expr::app(Expr::app(add_left, next.lhs.clone()), next.rhs.clone()),
                next.proof,
            ),
            self.rhs.clone(),
        );
        let new_lhs = Expr::app(Expr::app(sort_add.clone(), self.lhs), next.lhs.clone());
        let mid = Expr::app(Expr::app(sort_add.clone(), self.rhs.clone()), next.lhs);
        let new_rhs = Expr::app(Expr::app(sort_add, self.rhs), next.rhs);
        let le_trans = Expr::const_(
            Name::from_string(&format!("{sort_prefix}.le_trans")),
            vec![],
        );
        let proof = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(le_trans, new_lhs.clone()), mid),
                    new_rhs.clone(),
                ),
                step1,
            ),
            step2,
        );
        SortLeAcc {
            sort: self.sort,
            lhs: new_lhs,
            rhs: new_rhs,
            proof,
        }
    }
}

/// Build a compact Int-scaled accumulator using `Int.mul_le_mul_of_nonneg_left` (#2630).
fn build_compact_int_scaled_acc(acc: SortLeAcc, coeff: i128) -> Option<SortLeAcc> {
    if acc.sort != ArithSort::Int || coeff <= 0 {
        return None;
    }
    let coeff_u64 = u64::try_from(coeff).ok().or_else(|| {
        tracing::debug!(
            coeff = %coeff,
            "build_compact_int_scaled_acc: coefficient exceeds u64 numeral ceiling"
        );
        None
    })?;

    let coeff_nat = Expr::nat_lit(coeff_u64);
    let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
    let coeff_int = Expr::app(int_of_nat, coeff_nat.clone());

    let ofnat_zero_le = Expr::const_(Name::from_string("Int.ofNat_zero_le"), vec![]);
    let nonneg_proof = Expr::app(ofnat_zero_le, coeff_nat);

    let mul_le_nonneg = Expr::const_(Name::from_string("Int.mul_le_mul_of_nonneg_left"), vec![]);
    let proof = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(mul_le_nonneg, acc.lhs.clone()), acc.rhs.clone()),
                coeff_int.clone(),
            ),
            acc.proof,
        ),
        nonneg_proof,
    );

    let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
    let lhs = Expr::app(Expr::app(int_mul.clone(), coeff_int.clone()), acc.lhs);
    let rhs = Expr::app(Expr::app(int_mul, coeff_int), acc.rhs);

    Some(SortLeAcc {
        sort: ArithSort::Int,
        lhs,
        rhs,
        proof,
    })
}

pub(crate) fn choose_real_accumulation_mode(
    active: &[(usize, i128)],
    hypothesis_fvars: &[FVarId],
    goal: &Goal,
) -> Option<RealAccumulationMode> {
    let mut saw_real = false;
    for &(idx, _) in active {
        let fvar = *hypothesis_fvars.get(idx)?;
        let h_ty = find_hyp_type(goal, fvar)?;
        let (alpha, lhs, rhs) = extract_le_args(&h_ty)?;
        let sort = arith_linarith_chain::detect_sort(&alpha)?;
        if sort != ArithSort::Real {
            return Some(RealAccumulationMode::PreserveReal);
        }
        saw_real = true;
        if arith_linarith_real_downcast::downcast_real_le_to_int(fvar, &lhs, &rhs).is_none() {
            return Some(RealAccumulationMode::PreserveReal);
        }
    }
    Some(if saw_real {
        RealAccumulationMode::DowncastToInt
    } else {
        RealAccumulationMode::PreserveReal
    })
}
