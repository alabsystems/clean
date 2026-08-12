// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Equality substitution for the mathverse tactic.
//!
//! Implements **easy-equality elimination** (Lean 4 `solveEasyEquality`,
//! `Core.lean:316–331`): when an equality has a coefficient `±1` on some
//! variable, that variable is exactly determined by the rest of the
//! equality and can be substituted out of every other constraint.
//!
//! ```text
//!   given:   c·v + k = 0  where c_j = ±1
//!   solve:   v_j = -sign(c_j) · (Σ_{i≠j} c_i·v_i + k)
//!   for every other constraint g·v + g0 ≤ 0 (or = 0, or ≡ 0 (mod m)):
//!     replace by (g + (-sign(c_j) · g_j) · c)·v + (g0 + (-sign(c_j) · g_j) · k)
//!     — the v_j coefficient becomes exactly 0, the rest is back-substituted.
//! ```
//!
//! Soundness: every integer assignment satisfying the original system also
//! satisfies the rewritten system (because `c·v + k = 0` means the combo
//! we add is zero). Conversely, given a sat assignment of the rewritten
//! system over the variables ≠ j, recover `v_j` from the equality; the
//! integer-ness is preserved because `c_j = ±1` makes the division exact.
//!
//! Hard-equality elimination (the bmod trick at `Core.lean:340–356`) is
//! handled in a follow-up.

use super::bmod_elim::{bmod_reduce_hard_equality, BmodStepResult};
use super::gcd_normalize::integer_normalize_eq;
use crate::tactic::arithmetic::{LinearConstraint, LinearExpr};

/// Outcome of a single pass of easy-equality elimination.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EqualityStepResult {
    /// At least one easy equality was substituted out; caller should re-run.
    Progressed,
    /// No easy equalities remain — every equality has all non-unit coefficients.
    NoEasyEqualities,
    /// During substitution a downstream ground contradiction emerged (e.g.
    /// `1 = 0` from substitution-induced inconsistency). The system is
    /// `ℤ`-unsatisfiable.
    Unsat,
}

/// Maximum number of bmod reductions before giving up. Each bmod step
/// strictly decreases the lex measure `(minNatAbs, maxNatAbs)` of some
/// equality, so the loop terminates in practice, but soundness demands
/// a hard cap in case of pathological inputs (and to keep the certified
/// path predictable). `Unknown` falls through to FM.
const MAX_BMOD_STEPS: usize = 50;

/// Full Lean-4-style equality solver: alternate easy substitution and
/// bmod-reduction of hard equalities until either no equalities remain
/// or a ground contradiction emerges. Re-normalises Eq coefficients by
/// gcd inside the loop so reductions exposed by substitution flow into
/// the next easy step.
///
/// `next_var_index` is the index used for fresh atoms introduced by
/// bmod-reduction; pass the count of original variables on entry.
pub(crate) fn solve_all_equalities(
    constraints: &mut Vec<LinearConstraint>,
    next_var_index: &mut usize,
) -> EqualityStepResult {
    let mut bmod_steps = 0usize;
    let mut any_progress = false;
    loop {
        // Renormalise any equality whose coefficients share a common gcd
        // — this can expose ±1 entries the easy pass would otherwise miss.
        for c in constraints.iter_mut() {
            if let Some(normalised) = integer_normalize_eq(c) {
                *c = normalised;
            }
        }

        match solve_easy_equalities(constraints) {
            EqualityStepResult::Unsat => return EqualityStepResult::Unsat,
            EqualityStepResult::Progressed => {
                any_progress = true;
                continue;
            }
            EqualityStepResult::NoEasyEqualities => {}
        }

        if bmod_steps >= MAX_BMOD_STEPS {
            // Budget exhausted; whatever's left falls through to FM.
            return if any_progress {
                EqualityStepResult::Progressed
            } else {
                EqualityStepResult::NoEasyEqualities
            };
        }

        match bmod_reduce_hard_equality(constraints, next_var_index) {
            BmodStepResult::Progressed { .. } => {
                bmod_steps += 1;
                any_progress = true;
                continue;
            }
            BmodStepResult::NoHardEqualities | BmodStepResult::Overflow => {
                return if any_progress {
                    EqualityStepResult::Progressed
                } else {
                    EqualityStepResult::NoEasyEqualities
                };
            }
        }
    }
}

/// Run easy-equality elimination as a fixed-point: repeatedly find an
/// equality with a `±1` coefficient and substitute that variable out of
/// every other constraint. Returns once no easy equality remains or once
/// a ground contradiction surfaces.
///
/// `Mod` and `NotMod` constraints participate in substitution: replacing
/// `v_j` with its definition is sound over integers because the
/// definition is an integer linear combination.
pub(crate) fn solve_easy_equalities(constraints: &mut Vec<LinearConstraint>) -> EqualityStepResult {
    let mut progressed = false;
    loop {
        let Some(easy) = find_easy_equality(constraints) else {
            return if progressed {
                EqualityStepResult::Progressed
            } else {
                EqualityStepResult::NoEasyEqualities
            };
        };
        match substitute_easy_equality(constraints, easy.eq_index, easy.var_index, easy.coef_sign) {
            SubstitutionResult::Done => progressed = true,
            SubstitutionResult::Unsat => return EqualityStepResult::Unsat,
            SubstitutionResult::Overflow => {
                // Stop substitution — leave the original system intact for
                // the downstream FM pipeline. Whatever progress we already
                // made is committed via prior iterations.
                return if progressed {
                    EqualityStepResult::Progressed
                } else {
                    EqualityStepResult::NoEasyEqualities
                };
            }
        }
    }
}

/// Location of a usable easy equality.
#[derive(Debug, Clone, Copy)]
struct EasyEquality {
    /// Index into the `constraints` vector pointing at the `Eq(expr)`.
    eq_index: usize,
    /// Variable to eliminate via this equality. Its coefficient in
    /// `constraints[eq_index]` is `±1`.
    var_index: usize,
    /// Sign of the coefficient on `var_index` in the equality (`+1` or `-1`).
    /// Pre-computed so the caller doesn't redo the lookup.
    coef_sign: i64,
}

/// Find the first equality with a `±1` coefficient on some variable.
/// Returns the equality / variable / sign triple, or `None` when every
/// equality has only non-unit coefficients (i.e. only hard equalities
/// remain).
fn find_easy_equality(constraints: &[LinearConstraint]) -> Option<EasyEquality> {
    for (eq_index, c) in constraints.iter().enumerate() {
        let LinearConstraint::Eq(expr) = c else {
            continue;
        };
        for &(var_index, coef) in &expr.coeffs {
            if coef == 1 {
                return Some(EasyEquality {
                    eq_index,
                    var_index,
                    coef_sign: 1,
                });
            }
            if coef == -1 {
                return Some(EasyEquality {
                    eq_index,
                    var_index,
                    coef_sign: -1,
                });
            }
        }
    }
    None
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SubstitutionResult {
    /// Substitution completed; constraints have been rewritten in place.
    Done,
    /// During substitution a constraint became a ground contradiction
    /// (e.g. `1 ≤ 0` or `1 = 0`).
    Unsat,
    /// A coefficient combination overflowed i64. The substitution is
    /// aborted *without* rewriting the constraint set so the original
    /// system survives intact for downstream FM. Treated as "no progress"
    /// upstream.
    Overflow,
}

/// Eliminate `var_index` from every constraint other than `constraints[eq_index]`
/// using the equality at `eq_index`, then remove the consumed equality.
///
/// Soundness: see module docs. The combination factor `k` is chosen so
/// the resulting constraint has zero coefficient on `var_index`; integer
/// solutions of the original satisfy the new constraint by linearity.
fn substitute_easy_equality(
    constraints: &mut Vec<LinearConstraint>,
    eq_index: usize,
    var_index: usize,
    coef_sign: i64,
) -> SubstitutionResult {
    let pivot_expr = match &constraints[eq_index] {
        LinearConstraint::Eq(e) => e.clone(),
        _ => return SubstitutionResult::Done, // unreachable: caller guaranteed Eq
    };
    debug_assert_eq!(pivot_expr.get_coeff(var_index), coef_sign);

    // First pass: compute all rewrites without mutating the input. If any
    // rewrite would overflow, abort wholesale so the caller falls back to
    // the un-substituted system. This preserves completeness of the
    // downstream FM pipeline — silently replacing a constraint with a
    // vacuous `0 ≤ 0` would lose infeasibility evidence.
    let mut rewrites: Vec<(usize, LinearConstraint)> = Vec::with_capacity(constraints.len());
    let mut unsat_witness: Option<(usize, LinearConstraint)> = None;
    for (i, c) in constraints.iter().enumerate() {
        if i == eq_index {
            continue;
        }
        let g = c.clone();
        let Some(rewritten) = rewrite_constraint(g, &pivot_expr, var_index, coef_sign) else {
            return SubstitutionResult::Overflow;
        };
        if let Some(unsat) = ground_contradiction(&rewritten) {
            unsat_witness = Some((i, unsat));
            break;
        }
        rewrites.push((i, rewritten));
    }

    if let Some((idx, unsat)) = unsat_witness {
        constraints[idx] = unsat;
        return SubstitutionResult::Unsat;
    }

    // Second pass: commit. The eq is removed first; indices into the
    // returned rewrites are valid because we never wrote to `eq_index`.
    for (idx, c) in rewrites {
        constraints[idx] = c;
    }
    constraints.remove(eq_index);
    SubstitutionResult::Done
}

/// Compute `k · pivot + g` and rebuild the constraint of the same shape
/// as `g`, where `k = -coef_sign · g_j` so the resulting expression has
/// a zero coefficient on `var_index`.
///
/// The arithmetic runs in [`BigInt`] internally so intermediate
/// products of bmod-chain coefficients can't overflow i64. After
/// computing the combined expression, we **tidy by GCD** — divide
/// every coefficient and the constant by their common gcd — which
/// frequently narrows results back into i64 range even when the
/// pre-tidy values do not. If the tidied result still doesn't fit
/// `i64`, the rewrite is reported as overflow and the caller aborts
/// substitution (so the original system survives intact for FM).
fn rewrite_constraint(
    g: LinearConstraint,
    pivot: &LinearExpr,
    var_index: usize,
    coef_sign: i64,
) -> Option<LinearConstraint> {
    let g_j = g.expr().get_coeff(var_index);
    if g_j == 0 {
        return Some(g);
    }
    let k = num_bigint::BigInt::from(-coef_sign) * num_bigint::BigInt::from(g_j);
    let new_expr = bigint_scale_add_tidy(pivot, &k, g.expr())?;
    Some(match g {
        LinearConstraint::Le(_) => LinearConstraint::Le(new_expr),
        LinearConstraint::Lt(_) => LinearConstraint::Lt(new_expr),
        LinearConstraint::Eq(_) => LinearConstraint::Eq(new_expr),
        LinearConstraint::Ne(_) => LinearConstraint::Ne(new_expr),
        LinearConstraint::Mod { modulus, .. } => LinearConstraint::Mod {
            expr: new_expr,
            modulus,
        },
        LinearConstraint::NotMod { modulus, .. } => LinearConstraint::NotMod {
            expr: new_expr,
            modulus,
        },
    })
}

/// Compute `k · a + b` in `BigInt`, tidy by gcd, narrow to `i64`.
/// Returns `None` only if the tidied result has at least one coefficient
/// or constant that exceeds `i64::MIN..=i64::MAX` — at which point the
/// constraint genuinely cannot be represented in our existing `i64`
/// pipeline and the caller falls back to leaving the system intact.
///
/// The gcd-tidy step is what makes this practically lossless: the
/// substitution chain in bmod / easy-equality elimination *typically*
/// produces post-tidy coefficients well below i64::MAX even when
/// pre-tidy products exceed it.
///
/// **Important**: for `Eq` rewrites we tidy aggressively; for other
/// constraint kinds (`Le`/`Lt`/`Mod`) we still tidy because the gcd
/// transformation is sound (the constraint shape is preserved, just
/// expressed with smaller numerals).
fn bigint_scale_add_tidy(
    a: &LinearExpr,
    k: &num_bigint::BigInt,
    b: &LinearExpr,
) -> Option<LinearExpr> {
    use num_bigint::BigInt;
    use num_traits::{Signed, ToPrimitive, Zero};
    use std::collections::BTreeMap;

    let mut coeffs: BTreeMap<usize, BigInt> = BTreeMap::new();
    for &(v, c) in &a.coeffs {
        coeffs.insert(v, k * BigInt::from(c));
    }
    for &(v, c) in &b.coeffs {
        let entry = coeffs.entry(v).or_insert_with(BigInt::zero);
        *entry += BigInt::from(c);
    }
    let mut constant = k * BigInt::from(a.constant) + BigInt::from(b.constant);

    // Drop zero coefficients.
    coeffs.retain(|_, c| !c.is_zero());

    // Tidy by gcd of all non-zero coefficients and the constant.
    // Skips when there's nothing to tidy (single value).
    let mut g: BigInt = constant.abs();
    for c in coeffs.values() {
        g = bigint_gcd(g, c.abs());
        if g == BigInt::from(1) {
            break;
        }
    }
    if g > BigInt::from(1) {
        for c in coeffs.values_mut() {
            *c /= &g;
        }
        constant /= &g;
    }

    // Narrow to i64. Any out-of-range value bails the entire combination.
    let constant_i64 = constant.to_i64()?;
    let mut out: Vec<(usize, i64)> = Vec::with_capacity(coeffs.len());
    for (v, c) in coeffs {
        out.push((v, c.to_i64()?));
    }
    Some(LinearExpr {
        constant: constant_i64,
        coeffs: out,
    })
}

/// Non-negative `BigInt` gcd via Euclid.
fn bigint_gcd(a: num_bigint::BigInt, b: num_bigint::BigInt) -> num_bigint::BigInt {
    use num_traits::Zero;
    let mut a = a;
    let mut b = b;
    while !b.is_zero() {
        let t = b.clone();
        b = a % &b;
        a = t;
    }
    a
}

/// (Kept for any external callers; equality_solver no longer uses i64
/// linear_add internally — the BigInt path supersedes it.)
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
fn linear_add(a: &LinearExpr, b: &LinearExpr) -> Option<LinearExpr> {
    let constant = a.constant.checked_add(b.constant)?;
    let mut coeffs: Vec<(usize, i64)> = Vec::with_capacity(a.coeffs.len() + b.coeffs.len());
    let mut ai = 0;
    let mut bi = 0;
    while ai < a.coeffs.len() || bi < b.coeffs.len() {
        match (a.coeffs.get(ai), b.coeffs.get(bi)) {
            (Some(&(av, ac)), Some(&(bv, bc))) if av == bv => {
                let sum = ac.checked_add(bc)?;
                if sum != 0 {
                    coeffs.push((av, sum));
                }
                ai += 1;
                bi += 1;
            }
            (Some(&(av, ac)), Some(&(bv, _))) if av < bv => {
                coeffs.push((av, ac));
                ai += 1;
            }
            (Some(_), Some(&(bv, bc))) => {
                coeffs.push((bv, bc));
                bi += 1;
            }
            (Some(&(av, ac)), None) => {
                coeffs.push((av, ac));
                ai += 1;
            }
            (None, Some(&(bv, bc))) => {
                coeffs.push((bv, bc));
                bi += 1;
            }
            (None, None) => break,
        }
    }
    Some(LinearExpr { constant, coeffs })
}

/// Detect ground-only constraints that are false on their face. Used to
/// short-circuit when substitution turns a constraint into `c ≤ 0` (or
/// `= 0`, `≠ 0`, `mod 0`) with no variables and an inconsistent constant.
fn ground_contradiction(c: &LinearConstraint) -> Option<LinearConstraint> {
    if !c.expr().coeffs.is_empty() {
        return None;
    }
    let constant = c.expr().constant;
    let inconsistent = match c {
        LinearConstraint::Le(_) => constant > 0, // c ≤ 0 false iff c > 0
        LinearConstraint::Lt(_) => constant >= 0, // c < 0 false iff c ≥ 0
        LinearConstraint::Eq(_) => constant != 0, // c = 0 false iff c ≠ 0
        LinearConstraint::Ne(_) => constant == 0, // c ≠ 0 false iff c = 0
        LinearConstraint::Mod { modulus, .. } => *modulus != 0 && (constant % *modulus != 0),
        LinearConstraint::NotMod { modulus, .. } => *modulus != 0 && (constant % *modulus == 0),
    };
    if inconsistent {
        Some(c.clone())
    } else {
        None
    }
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

    fn le(constant: i64, coeffs: &[(usize, i64)]) -> LinearConstraint {
        LinearConstraint::Le(LinearExpr {
            constant,
            coeffs: coeffs.to_vec(),
        })
    }

    /// `x = 5`: easy substitution into `x + y ≤ 0` gives `y + 5 ≤ 0`.
    #[test]
    fn easy_substitutes_var_into_le() {
        // Eq(x - 5 = 0) and Le(x + y ≤ 0)
        let mut cs = vec![eq(-5, &[(0, 1)]), le(0, &[(0, 1), (1, 1)])];
        let result = solve_easy_equalities(&mut cs);
        assert_eq!(result, EqualityStepResult::Progressed);
        assert_eq!(cs.len(), 1);
        // x = 5, so x + y ≤ 0 becomes y + 5 ≤ 0
        assert_eq!(cs[0], le(5, &[(1, 1)]));
    }

    /// `x = y + 1 ∧ x = y - 1` collapses to `1 = -1`, contradiction.
    #[test]
    fn contradicting_equalities_detected() {
        // Eq(x - y - 1 = 0): x = y + 1
        // Eq(x - y + 1 = 0): x = y - 1
        // Substituting first: second becomes (y + 1) - y + 1 = 2, so Eq(2 = 0) → Unsat.
        let mut cs = vec![eq(-1, &[(0, 1), (1, -1)]), eq(1, &[(0, 1), (1, -1)])];
        let result = solve_easy_equalities(&mut cs);
        assert_eq!(result, EqualityStepResult::Unsat);
    }

    /// `-x = 5`: pivot has `-1` coefficient. `x = -5`. Substitute into `Le(x ≤ 3)`
    /// (`x - 3 ≤ 0`) gives `-5 - 3 ≤ 0 → -8 ≤ 0`. SAT (trivially true).
    #[test]
    fn negative_pivot_substitution() {
        let mut cs = vec![
            eq(5, &[(0, -1)]), // -x + 5 = 0 → x = 5
            le(-3, &[(0, 1)]), // x - 3 ≤ 0 → x ≤ 3
        ];
        let result = solve_easy_equalities(&mut cs);
        // After substitution Le becomes 5 - 3 = 2 ≤ 0 — FALSE. Unsat.
        assert_eq!(result, EqualityStepResult::Unsat);
    }

    /// Only a hard equality remains (coefficients `±2`) — solver reports
    /// no easy progress.
    #[test]
    fn no_easy_when_all_hard() {
        let mut cs = vec![eq(-3, &[(0, 2)])]; // 2x = 3
        let result = solve_easy_equalities(&mut cs);
        assert_eq!(result, EqualityStepResult::NoEasyEqualities);
    }

    /// Two-step chain: first substitution exposes a fresh easy equality.
    #[test]
    fn two_step_substitution_chain() {
        // Eq(x - y - 1 = 0):  x = y + 1
        // Eq(2*y - z = 0):    not easy yet (coeff on y is 2, on z is -1 → -1 is easy)
        // Le(x + z ≤ 0)
        // After first substitution (x = y + 1): Le(y + 1 + z ≤ 0), Eq(2y - z = 0)
        // Now z = 2y is easy, substitutes into Le: y + 1 + 2y = 3y + 1 ≤ 0
        let mut cs = vec![
            eq(-1, &[(0, 1), (1, -1)]),
            eq(0, &[(1, 2), (2, -1)]),
            le(0, &[(0, 1), (2, 1)]),
        ];
        let result = solve_easy_equalities(&mut cs);
        assert_eq!(result, EqualityStepResult::Progressed);
        // Both equalities consumed
        let eq_count = cs
            .iter()
            .filter(|c| matches!(c, LinearConstraint::Eq(_)))
            .count();
        assert_eq!(eq_count, 0);
        // One Le remains, in y only
        assert_eq!(cs.len(), 1);
        let LinearConstraint::Le(remaining) = &cs[0] else {
            panic!("expected Le");
        };
        // 3y + 1 ≤ 0
        assert_eq!(remaining.constant, 1);
        assert_eq!(remaining.coeffs, vec![(1, 3)]);
    }

    /// Substituting into Mod is sound. `x = 5 ∧ x ≡ 0 (mod 2)` → `5 ≡ 0 (mod 2)`
    /// which is FALSE. Unsat.
    #[test]
    fn substitution_into_mod_detects_contradiction() {
        let mut cs = vec![
            eq(-5, &[(0, 1)]),
            LinearConstraint::Mod {
                expr: LinearExpr {
                    constant: 0,
                    coeffs: vec![(0, 1)],
                },
                modulus: 2,
            },
        ];
        let result = solve_easy_equalities(&mut cs);
        assert_eq!(result, EqualityStepResult::Unsat);
    }

    /// End-to-end smoke test: hard equality `-6x0 - 7x1 - 8 = 0` plus a
    /// simple Le constraint. The bmod chain should reduce the equality to
    /// an easy form, substitute out original variables, and leave only Le
    /// constraints over the bmod-introduced fresh variable.
    #[test]
    fn combined_solver_handles_hard_equality_with_substitution() {
        let mut cs = vec![eq(-8, &[(0, -6), (1, -7)]), le(-1, &[(1, -1)])];
        let mut next_var = 2;
        let result = solve_all_equalities(&mut cs, &mut next_var);
        // Something must have happened given the hard equality is present.
        assert_ne!(result, EqualityStepResult::NoEasyEqualities);
    }

    /// Reproduces the fuzzer's I1 case exactly: hard equality plus four
    /// Le constraints that, after substitution, force `z ≥ 1 ∧ z ≤ 0`
    /// in the fresh bmod variable — Unsat via FM real shadow.
    #[test]
    fn fuzz_i1_full_substitution_chain() {
        // (1)  Le: -x1 - 1                     ≤ 0     (x1 ≥ -1)
        // (2)  Le:  2x0 - 3x1 - 7              ≤ 0     (lifted from <)
        // (3)  Le:  x0 - x1                    ≤ 0
        // (4)  Eq: -6x0 - 7x1 - 8              = 0
        // (5)  Le:  2x0 + 7x1 + 2              ≤ 0
        let mut cs = vec![
            le(-1, &[(1, -1)]),
            le(-7, &[(0, 2), (1, -3)]),
            le(0, &[(0, 1), (1, -1)]),
            eq(-8, &[(0, -6), (1, -7)]),
            le(2, &[(0, 2), (1, 7)]),
        ];
        let mut next_var = 2;
        let result = solve_all_equalities(&mut cs, &mut next_var);
        eprintln!("I1 result: {:?}", result);
        for c in &cs {
            eprintln!("  remaining: {:?}", c);
        }
        // Result should be Progressed (substitution chain ran). Final
        // system contains only Le constraints in z; FM detects the
        // z ≥ 1 ∧ z ≤ 0 contradiction. Solver itself doesn't claim Unsat
        // unless a ground contradiction surfaced mid-substitution.
        assert_ne!(result, EqualityStepResult::NoEasyEqualities);
    }

    /// `3x = 4` (i.e. `3x - 4 = 0`) is ℤ-infeasible. The combined solver
    /// runs bmod → easy → derives a tighter equality. Final detection of
    /// ℤ-infeasibility flows through the downstream GCD check in
    /// certified.rs; here we just verify the solver makes forward progress.
    #[test]
    fn combined_solver_makes_progress_on_3x_equals_4() {
        let mut cs = vec![eq(-4, &[(0, 3)])];
        let mut next_var = 1;
        let result = solve_all_equalities(&mut cs, &mut next_var);
        assert!(matches!(
            result,
            EqualityStepResult::Progressed | EqualityStepResult::Unsat
        ));
    }

    /// Empty input is the no-progress base case.
    #[test]
    fn empty_returns_no_easy() {
        let mut cs: Vec<LinearConstraint> = vec![];
        let result = solve_easy_equalities(&mut cs);
        assert_eq!(result, EqualityStepResult::NoEasyEqualities);
    }
}
