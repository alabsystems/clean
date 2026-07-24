// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Hard-equality elimination via the balanced-modulo (`bmod`) trick.
//!
//! Mirrors Lean 4 mathverse's `dealWithHardEquality` (`Core.lean:340–356`).
//! Given an equality `c·v + r = 0` whose smallest absolute coefficient
//! is `m_min ≥ 2`, the algorithm introduces a fresh integer variable
//! `y` and adds a new equality
//!
//! ```text
//!   bmod(c, m) · v + m · y + bmod(r, m) = 0    where  m = m_min + 1
//! ```
//!
//! Here `bmod(x, m) := (x mod m, normalised to (-m/2, m/2])`. The
//! lemma `bmod_sat` (`Constraint.lean:383`) guarantees: for every
//! integer assignment `v` of `c·v + r = 0`, setting
//! `y = (bmod(c·v + r, m) - bmod(c, m)·v - bmod(r, m)) / m` (which is
//! integer-valued by `dvd_bmod_dot_sub_dot_bmod`) makes the new
//! equality hold. Combined with the fact that `bmod(c, m)` has every
//! entry in `(-m/2, m/2]` and at least one entry strictly smaller in
//! magnitude than the original `m_min`, the lex measure
//! `(minNatAbs, maxNatAbs)` of the equality set strictly decreases —
//! so iterating bmod terminates and eventually produces an easy
//! equality (some coefficient `±1`).
//!
//! Important: the new equality is **added** to the constraint set; the
//! original hard equality is **not removed** (Lean 4's algorithm does
//! the same — `Core.lean:352` calls `addConstraint`, not "replace").
//! The recursive `solve_easy_equality` step that follows will then use
//! the *smaller* new equality to substitute variables out of the
//! *original* hard equality, transforming it into a constraint with
//! smaller minNatAbs. Repeat until no hard equalities remain.

use crate::tactic::arithmetic::{LinearConstraint, LinearExpr};

/// `Int.bmod x m` — balanced modulo, result in `(-m/2, m/2]`.
/// Definition from `Init/Data/Int/DivMod/Basic.lean:315`.
///
/// `m` must be positive. For `m = 0` we return `x` unchanged (caller
/// is expected to avoid m = 0).
pub(crate) fn int_bmod(x: i64, m: i64) -> i64 {
    if m == 0 {
        return x;
    }
    let m_abs = m.unsigned_abs();
    // `rem_euclid` yields the unique residue in `[0, m_abs)`.
    let r = x.rem_euclid(m_abs as i64);
    let half_up = (m_abs as i64 + 1) / 2;
    if r < half_up {
        r
    } else {
        r - m_abs as i64
    }
}

/// Outcome of a single bmod step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BmodStepResult {
    /// A new (smaller) equality was appended and `next_var_index` advanced.
    /// Caller should re-run `solve_easy_equalities` to attempt substitution.
    Progressed { fresh_var: usize },
    /// No hard equality remains (every equality either has a ±1
    /// coefficient or no variables) — caller should fall through to FM.
    NoHardEqualities,
    /// A bmod computation overflowed or hit a budget cap; caller treats
    /// this as `Unknown` (sound: fall through to existing pipeline).
    Overflow,
}

/// Apply one bmod-reduction step to the first hard equality found in
/// `constraints`. The fresh atom index is allocated as `*next_var_index`
/// (which is then incremented). On success, a new equality is appended;
/// the original hard equality is left in place per the Lean algorithm.
pub(crate) fn bmod_reduce_hard_equality(
    constraints: &mut Vec<LinearConstraint>,
    next_var_index: &mut usize,
) -> BmodStepResult {
    let Some(hard_index) = find_hard_equality(constraints) else {
        return BmodStepResult::NoHardEqualities;
    };

    let pivot = match &constraints[hard_index] {
        LinearConstraint::Eq(e) => e.clone(),
        _ => return BmodStepResult::NoHardEqualities,
    };

    let Some(min_abs) = pivot.coeffs.iter().map(|&(_, c)| c.unsigned_abs()).min() else {
        return BmodStepResult::NoHardEqualities;
    };

    // `m = m_min + 1`. The new coeffs lie in `(-m/2, m/2]` and the new
    // y-coefficient is `m`. The lex measure decreases because the
    // original minNatAbs was `m - 1 < m/2` only when m - 1 < m/2, i.e.
    // when m_min ≤ 1 — but we're in the hard case where m_min ≥ 2, so
    // bmod actually changes some coefficients. (See Lean's discussion.)
    let m = min_abs.checked_add(1).and_then(|m| i64::try_from(m).ok());
    let Some(m) = m else {
        return BmodStepResult::Overflow;
    };
    if m <= 1 {
        // m_min was 0, which means a column entry was 0 — shouldn't be
        // in `coeffs` per LinearExpr invariants. Conservative fallthrough.
        return BmodStepResult::NoHardEqualities;
    }

    let fresh_var = *next_var_index;
    *next_var_index += 1;

    let mut new_coeffs: Vec<(usize, i64)> = Vec::with_capacity(pivot.coeffs.len() + 1);
    for &(var, coef) in &pivot.coeffs {
        let b = int_bmod(coef, m);
        if b != 0 {
            new_coeffs.push((var, b));
        }
    }
    // Insert the fresh variable's coefficient = m, preserving sort order.
    let insert_pos = new_coeffs
        .binary_search_by_key(&fresh_var, |&(v, _)| v)
        .unwrap_or_else(|p| p);
    new_coeffs.insert(insert_pos, (fresh_var, m));

    let new_constant = int_bmod(pivot.constant, m);

    constraints.push(LinearConstraint::Eq(LinearExpr {
        constant: new_constant,
        coeffs: new_coeffs,
    }));
    BmodStepResult::Progressed { fresh_var }
}

/// Find the index of the first `Eq` whose minimum absolute coefficient
/// is ≥ 2 (i.e. all coefficients are non-unit). Returns `None` when no
/// such equality exists (every equality is easy or there are no
/// equalities at all).
fn find_hard_equality(constraints: &[LinearConstraint]) -> Option<usize> {
    for (i, c) in constraints.iter().enumerate() {
        let LinearConstraint::Eq(e) = c else {
            continue;
        };
        if e.coeffs.is_empty() {
            continue; // ground; handled elsewhere
        }
        let min_abs = e
            .coeffs
            .iter()
            .map(|&(_, c)| c.unsigned_abs())
            .min()
            .expect("invariant: e.coeffs non-empty (checked above)");
        if min_abs >= 2 {
            return Some(i);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Reference values from `Init/Data/Int/DivMod/Basic.lean:307-313`.
    #[test]
    fn int_bmod_matches_lean_examples() {
        // (12 : Int).bmod 9 = 3
        assert_eq!(int_bmod(12, 9), 3);
        // (-12 : Int).bmod 6 = 0
        assert_eq!(int_bmod(-12, 6), 0);
        // (-12 : Int).bmod 7 = 2
        assert_eq!(int_bmod(-12, 7), 2);
        // (-12 : Int).bmod 8 = -4
        assert_eq!(int_bmod(-12, 8), -4);
        // (-12 : Int).bmod 9 = -3
        assert_eq!(int_bmod(-12, 9), -3);
    }

    /// `bmod(x, m)` is in `(-m/2, m/2]` for positive `m`.
    #[test]
    fn int_bmod_range() {
        for m in 1..20i64 {
            for x in -50..=50i64 {
                let r = int_bmod(x, m);
                assert!(r <= m / 2, "bmod({x}, {m}) = {r}, expected ≤ {}", m / 2);
                assert!(r > -m, "bmod({x}, {m}) = {r}, expected > -{m}");
                // Equivalence: r ≡ x (mod m).
                assert_eq!(
                    r.rem_euclid(m),
                    x.rem_euclid(m),
                    "bmod({x}, {m}) = {r} not ≡ {x} mod {m}"
                );
            }
        }
    }

    fn eq(constant: i64, coeffs: &[(usize, i64)]) -> LinearConstraint {
        LinearConstraint::Eq(LinearExpr {
            constant,
            coeffs: coeffs.to_vec(),
        })
    }

    /// `4x - 3y - 6 = 0`. min |c| = 3, m = 4.
    /// bmod(4, 4) = 0, bmod(-3, 4) = 1, bmod(-6, 4) = -2 (since -6 mod 4 = 2,
    /// and 2 ≥ (4+1)/2 = 2, so the result wraps to 2 - 4 = -2).
    /// New eq: 1·y + 4·z + (-2) = 0  ⇔  y = 2 - 4z.
    /// (The `4·x` term drops out because bmod(4, 4) = 0.)
    #[test]
    fn reduces_hard_equality_to_easy() {
        let mut cs = vec![eq(-6, &[(0, 4), (1, -3)])];
        let mut next_var = 2;
        let result = bmod_reduce_hard_equality(&mut cs, &mut next_var);
        match result {
            BmodStepResult::Progressed { fresh_var } => assert_eq!(fresh_var, 2),
            other => panic!("expected Progressed, got {:?}", other),
        }
        assert_eq!(next_var, 3);
        // Original equality still present + new equality appended.
        assert_eq!(cs.len(), 2);
        let LinearConstraint::Eq(new) = &cs[1] else {
            panic!("expected new Eq");
        };
        assert_eq!(new.constant, -2);
        assert_eq!(new.coeffs, vec![(1, 1), (2, 4)]);
    }

    /// Equality with a ±1 coefficient should be skipped (not "hard").
    #[test]
    fn skips_easy_equality() {
        let mut cs = vec![eq(-5, &[(0, 1), (1, 3)])]; // x + 3y - 5 = 0; min |c| = 1
        let mut next_var = 2;
        assert_eq!(
            bmod_reduce_hard_equality(&mut cs, &mut next_var),
            BmodStepResult::NoHardEqualities
        );
        assert_eq!(cs.len(), 1);
        assert_eq!(next_var, 2);
    }

    /// No equalities at all → NoHardEqualities.
    #[test]
    fn no_equalities() {
        let mut cs = vec![LinearConstraint::Le(LinearExpr {
            constant: 0,
            coeffs: vec![(0, 1)],
        })];
        let mut next_var = 1;
        assert_eq!(
            bmod_reduce_hard_equality(&mut cs, &mut next_var),
            BmodStepResult::NoHardEqualities
        );
    }
}
