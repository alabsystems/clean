// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integer-tight refutation by GCD normalization.
//!
//! Soundly detects `ℤ`-unsatisfiable single-constraint cases that the
//! existing rational Fourier-Motzkin pipeline accepts as ℚ-satisfiable.
//! The canonical example: `2x = 1` has no integer solution (2 ∤ 1), but
//! FM sees `x = 1/2` and reports `Sat`.
//!
//! The math: a linear combination `a₁·x₁ + ... + aₙ·xₙ + c = 0` has an
//! integer solution iff `gcd(a₁, ..., aₙ)` divides `c`. The same divides-
//! constant condition lifts to modular constraints:
//! `a₁·x₁ + ... + aₙ·xₙ + c ≡ r (mod m)` has an integer solution iff
//! `gcd(a₁, ..., aₙ, m)` divides `c - r`.
//!
//! See `docs/DESIGN_MATHVERSE_COMPLETION.md` §3.2 step 3 ("GCD normalisation").

use crate::tactic::arithmetic::{LinearConstraint, LinearExpr};

/// Outcome of the per-constraint GCD divisibility check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GcdResult {
    /// The constraint is `ℤ`-infeasible on its own.
    Infeasible,
    /// The constraint passes the GCD check (or doesn't apply to it).
    Feasible,
}

/// Tighten a `Le` constraint to its integer-strict form, if possible.
///
/// Given `Σ aᵢxᵢ + c ≤ 0` over `ℤ`, let `g = gcd(a₁, ..., aₙ)`. If
/// `g > 1`, the constraint is equivalent over the integers to
/// `Σ (aᵢ/g)xᵢ + ⌈c/g⌉ ≤ 0` because the integer linear combination on
/// the left is a multiple of `g`, so the bound on it can be rounded up
/// to the next multiple of `g` without changing the integer feasibility
/// set. Example: `2x + 1 ≤ 0` over ℤ becomes `x + 1 ≤ 0` (i.e.
/// `x ≤ -1`), not just `x ≤ -1/2`.
///
/// Returns `None` when no tightening applies (constraint has no
/// variables, or `gcd = 1`). Sound: integer solutions of the original
/// and the tightened constraint are identical; rational-only solutions
/// may be excluded (the desired effect for ℤ-decision).
///
/// Note: we deliberately do not tighten `Lt` here. The existing
/// `pugh.rs`-era lifting (now in the design doc as §3.2 step 2) is
/// `Lt(e) ⇔ Le(e + 1)` over ℤ. Callers should perform the lift before
/// invoking this if they want strict-inequality tightening.
pub(crate) fn integer_tighten_le(c: &LinearConstraint) -> Option<LinearConstraint> {
    let LinearConstraint::Le(e) = c else {
        return None;
    };
    if e.coeffs.is_empty() {
        return None;
    }
    let g = coeff_gcd(&e.coeffs);
    if g <= 1 {
        return None;
    }
    let tight_coeffs: Vec<(usize, i64)> = e.coeffs.iter().map(|&(v, a)| (v, a / g)).collect();
    let tight_constant = div_ceil_i64(e.constant, g);
    Some(LinearConstraint::Le(LinearExpr {
        constant: tight_constant,
        coeffs: tight_coeffs,
    }))
}

/// `⌈a / b⌉` for `b > 0`, expressed without floats.
fn div_ceil_i64(a: i64, b: i64) -> i64 {
    debug_assert!(b > 0);
    if a >= 0 {
        // a + b - 1 stays within i64 because `a` came from a (possibly
        // negated) i64 constant; both gcd and the worst-case shift fit.
        a.saturating_add(b).saturating_sub(1) / b
    } else {
        -((-a) / b)
    }
}

/// Divide every coefficient (and the constant) of an `Eq` by their common
/// `gcd > 1`, producing an equivalent equality with strictly smaller
/// coefficients. Returns `None` when no reduction applies (no variables,
/// gcd = 1, or `gcd ∤ constant`, the latter handled earlier as the
/// infeasibility-detection path).
///
/// Sound: `Σ aᵢxᵢ + c = 0` over ℤ ⇔ `Σ (aᵢ/g)xᵢ + c/g = 0` whenever
/// `g | gcd(a₁..aₙ)` and `g | c`. Exposes ±1 coefficients to the easy-
/// equality substitution path that the original would have missed.
pub(crate) fn integer_normalize_eq(c: &LinearConstraint) -> Option<LinearConstraint> {
    let LinearConstraint::Eq(e) = c else {
        return None;
    };
    if e.coeffs.is_empty() {
        return None;
    }
    let g = coeff_gcd(&e.coeffs);
    if g <= 1 {
        return None;
    }
    if e.constant.unsigned_abs() % g.unsigned_abs() != 0 {
        // Caller will pick this up via `first_integer_infeasible`.
        return None;
    }
    let coeffs: Vec<(usize, i64)> = e.coeffs.iter().map(|&(v, a)| (v, a / g)).collect();
    let constant = e.constant / g;
    Some(LinearConstraint::Eq(LinearExpr { constant, coeffs }))
}

/// Examine a single linear constraint for an integer-tight contradiction.
///
/// - `Eq(expr)`: infeasible if `gcd(expr.coeffs) ∤ expr.constant`.
///   Variables on the left, constant on the right of `expr = 0` means
///   `a·x = -constant`, so the divisibility check is on `-constant`,
///   which has the same divisors as `constant`.
/// - `Mod { expr, modulus }`: infeasible if
///   `gcd(expr.coeffs, modulus) ∤ expr.constant`.
/// - `Le` / `Lt` / `Ne` / `NotMod`: never declared infeasible by this
///   check alone — they admit too much slack.
pub(crate) fn gcd_check_constraint(c: &LinearConstraint) -> GcdResult {
    match c {
        LinearConstraint::Eq(e) => check_eq(e),
        LinearConstraint::Mod { expr, modulus } => check_mod(expr, *modulus),
        LinearConstraint::Le(_)
        | LinearConstraint::Lt(_)
        | LinearConstraint::Ne(_)
        | LinearConstraint::NotMod { .. } => GcdResult::Feasible,
    }
}

/// Scan a constraint set; return the index of the first `ℤ`-infeasible
/// constraint, or `None` if every constraint passes the GCD check.
pub(crate) fn first_integer_infeasible(constraints: &[LinearConstraint]) -> Option<usize> {
    constraints
        .iter()
        .position(|c| matches!(gcd_check_constraint(c), GcdResult::Infeasible))
}

fn check_eq(expr: &LinearExpr) -> GcdResult {
    // If there are no variables, the constraint is `constant = 0`. Feasibility
    // is just constant == 0; non-zero constant is caught downstream as a
    // ground contradiction by Fourier-Motzkin. Don't flag it here so callers
    // don't double-report it.
    if expr.coeffs.is_empty() {
        return GcdResult::Feasible;
    }
    let g = coeff_gcd(&expr.coeffs);
    if g == 0 {
        return GcdResult::Feasible;
    }
    if expr
        .constant
        .unsigned_abs()
        .is_multiple_of(g.unsigned_abs())
    {
        GcdResult::Feasible
    } else {
        GcdResult::Infeasible
    }
}

fn check_mod(expr: &LinearExpr, modulus: i64) -> GcdResult {
    if modulus == 0 {
        return GcdResult::Feasible;
    }
    // The modular constraint `expr ≡ 0 (mod m)` (after the caller has
    // baked the remainder into `expr.constant`) has an integer solution
    // iff `gcd(coeffs ∪ {m})` divides `expr.constant`.
    if expr.coeffs.is_empty() {
        // Ground: `constant ≡ 0 (mod m)`. Feasible iff m | constant.
        return if expr
            .constant
            .unsigned_abs()
            .is_multiple_of(modulus.unsigned_abs())
        {
            GcdResult::Feasible
        } else {
            GcdResult::Infeasible
        };
    }
    let mut g = coeff_gcd(&expr.coeffs);
    g = gcd_i64(g, modulus);
    if g == 0 {
        return GcdResult::Feasible;
    }
    if expr
        .constant
        .unsigned_abs()
        .is_multiple_of(g.unsigned_abs())
    {
        GcdResult::Feasible
    } else {
        GcdResult::Infeasible
    }
}

fn coeff_gcd(coeffs: &[(usize, i64)]) -> i64 {
    coeffs.iter().fold(0_i64, |acc, &(_, c)| gcd_i64(acc, c))
}

/// Non-negative i64 gcd.
fn gcd_i64(a: i64, b: i64) -> i64 {
    let mut a = a.unsigned_abs();
    let mut b = b.unsigned_abs();
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    // a fits back into i64 because we only abs'd individual i64 values
    // and the gcd doesn't exceed the larger absolute value.
    i64::try_from(a).unwrap_or(i64::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eq(constant: i64, coeffs: &[(usize, i64)]) -> LinearConstraint {
        LinearConstraint::Eq(LinearExpr {
            constant,
            coeffs: coeffs.to_vec(),
        })
    }

    fn mod_(constant: i64, coeffs: &[(usize, i64)], modulus: i64) -> LinearConstraint {
        LinearConstraint::Mod {
            expr: LinearExpr {
                constant,
                coeffs: coeffs.to_vec(),
            },
            modulus,
        }
    }

    /// `2x = 1` is the canonical ℤ-infeasible Eq the FM pipeline misses.
    #[test]
    fn detects_2x_equals_1() {
        // Stored as Eq(2x - 1 = 0), so constant = -1, coeff = 2.
        let c = eq(-1, &[(0, 2)]);
        assert_eq!(gcd_check_constraint(&c), GcdResult::Infeasible);
    }

    /// `3x + 6y = 5` has gcd 3; 3 ∤ 5 ⇒ infeasible.
    #[test]
    fn detects_three_x_plus_six_y_equals_five() {
        let c = eq(-5, &[(0, 3), (1, 6)]);
        assert_eq!(gcd_check_constraint(&c), GcdResult::Infeasible);
    }

    /// `3x + 6y = 9` has gcd 3 and 3 | 9 ⇒ feasible (x=3, y=0 works).
    #[test]
    fn passes_three_x_plus_six_y_equals_nine() {
        let c = eq(-9, &[(0, 3), (1, 6)]);
        assert_eq!(gcd_check_constraint(&c), GcdResult::Feasible);
    }

    /// `2x = 4` is feasible (x = 2).
    #[test]
    fn passes_2x_equals_4() {
        let c = eq(-4, &[(0, 2)]);
        assert_eq!(gcd_check_constraint(&c), GcdResult::Feasible);
    }

    /// `x = 5` is feasible. (Coeff is 1, divides anything.)
    #[test]
    fn passes_unit_coefficient() {
        let c = eq(-5, &[(0, 1)]);
        assert_eq!(gcd_check_constraint(&c), GcdResult::Feasible);
    }

    /// Negative coefficient and negative constant: `-2x = -3` ⇔ `2x = 3`,
    /// still infeasible.
    #[test]
    fn detects_negative_signs() {
        let c = eq(3, &[(0, -2)]);
        assert_eq!(gcd_check_constraint(&c), GcdResult::Infeasible);
    }

    /// Le constraints never flagged by this check.
    #[test]
    fn ignores_le() {
        let c = LinearConstraint::Le(LinearExpr {
            constant: -1,
            coeffs: vec![(0, 2)],
        });
        assert_eq!(gcd_check_constraint(&c), GcdResult::Feasible);
    }

    /// Modular: `2x ≡ 1 (mod 4)`. After folding remainder into constant
    /// the constraint is `(2x - 1) ≡ 0 (mod 4)`. gcd(2, 4) = 2; 2 ∤ -1.
    /// Infeasible.
    #[test]
    fn detects_2x_mod_4_eq_1() {
        let c = mod_(-1, &[(0, 2)], 4);
        assert_eq!(gcd_check_constraint(&c), GcdResult::Infeasible);
    }

    /// Modular: `2x ≡ 0 (mod 4)`. gcd(2, 4) = 2; 2 | 0 ⇒ feasible.
    #[test]
    fn passes_2x_mod_4_eq_0() {
        let c = mod_(0, &[(0, 2)], 4);
        assert_eq!(gcd_check_constraint(&c), GcdResult::Feasible);
    }

    /// Ground Eq with empty coeffs: deferred to FM (not flagged here).
    /// This avoids double-reporting; FM treats it as a ground contradiction
    /// when constant != 0.
    #[test]
    fn defers_ground_eq() {
        let c = eq(1, &[]);
        assert_eq!(gcd_check_constraint(&c), GcdResult::Feasible);
    }

    /// `first_integer_infeasible` returns the earliest infeasible index.
    #[test]
    fn first_index_lookup() {
        let cs = vec![
            LinearConstraint::Le(LinearExpr {
                constant: 0,
                coeffs: vec![(0, 1)],
            }),
            eq(-5, &[(0, 3), (1, 6)]), // index 1: infeasible
            eq(-1, &[(0, 2)]),         // index 2: also infeasible, not reported
        ];
        assert_eq!(first_integer_infeasible(&cs), Some(1));
    }

    fn le(constant: i64, coeffs: &[(usize, i64)]) -> LinearConstraint {
        LinearConstraint::Le(LinearExpr {
            constant,
            coeffs: coeffs.to_vec(),
        })
    }

    /// `2x + 1 ≤ 0` over ℤ ⇔ `x + 1 ≤ 0` (i.e. `x ≤ -1`).
    #[test]
    fn tightens_2x_plus_1_le_0() {
        let c = le(1, &[(0, 2)]);
        let tightened = integer_tighten_le(&c).expect("should tighten");
        assert_eq!(tightened, le(1, &[(0, 1)]));
    }

    /// `2x - 5 ≤ 0` ⇔ `x - 2 ≤ 0`. ⌈-5/2⌉ = -2.
    #[test]
    fn tightens_2x_minus_5_le_0() {
        let c = le(-5, &[(0, 2)]);
        let tightened = integer_tighten_le(&c).expect("should tighten");
        assert_eq!(tightened, le(-2, &[(0, 1)]));
    }

    /// `6x + 4y + 5 ≤ 0`, gcd(6,4)=2, ⌈5/2⌉=3. Becomes `3x + 2y + 3 ≤ 0`.
    #[test]
    fn tightens_two_var_with_gcd_2() {
        let c = le(5, &[(0, 6), (1, 4)]);
        let tightened = integer_tighten_le(&c).expect("should tighten");
        assert_eq!(tightened, le(3, &[(0, 3), (1, 2)]));
    }

    /// gcd = 1 → no tightening.
    #[test]
    fn no_tightening_when_gcd_is_one() {
        let c = le(5, &[(0, 3), (1, 2)]);
        assert!(integer_tighten_le(&c).is_none());
    }

    /// Empty coeffs (ground) → defer to FM.
    #[test]
    fn no_tightening_when_ground() {
        let c = le(5, &[]);
        assert!(integer_tighten_le(&c).is_none());
    }

    /// Non-Le constraints not handled.
    #[test]
    fn no_tightening_for_eq_or_mod() {
        let c = eq(-1, &[(0, 2)]);
        assert!(integer_tighten_le(&c).is_none());
    }

    /// Sanity on `div_ceil_i64`.
    #[test]
    fn div_ceil_basics() {
        assert_eq!(div_ceil_i64(5, 2), 3);
        assert_eq!(div_ceil_i64(4, 2), 2);
        assert_eq!(div_ceil_i64(0, 2), 0);
        assert_eq!(div_ceil_i64(-5, 2), -2);
        assert_eq!(div_ceil_i64(-4, 2), -2);
        assert_eq!(div_ceil_i64(-1, 2), 0);
        assert_eq!(div_ceil_i64(1, 1), 1);
    }

    /// gcd helper sanity.
    #[test]
    fn gcd_basics() {
        assert_eq!(gcd_i64(0, 0), 0);
        assert_eq!(gcd_i64(0, 5), 5);
        assert_eq!(gcd_i64(5, 0), 5);
        assert_eq!(gcd_i64(12, 18), 6);
        assert_eq!(gcd_i64(-12, 18), 6);
        assert_eq!(gcd_i64(7, 13), 1);
    }
}
