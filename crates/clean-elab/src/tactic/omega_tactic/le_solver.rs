// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Iterative Fourier-Motzkin with integer-tightening between rounds.
//!
//! After `solve_all_equalities` consumes every equality, the system is a
//! bag of `Le` constraints (and possibly `Mod`/`Ne` which we route
//! separately). The textbook FM real-shadow eliminates all variables in
//! one shot and checks for a ground contradiction at the end.
//!
//! That's not enough for ℤ completeness because the *combinations* FM
//! produces typically have non-unit coefficients on a remaining
//! variable, e.g. `7y - 3 ≤ 0 ∧ 7y - 4 ≤ 0` reduces only to itself
//! over ℚ but the integer-tightening of `7y - 3 ≤ 0` is `y ≤ 0`, which
//! combined with a separate `7y ≥ 1` would surface the contradiction.
//!
//! This module's loop:
//! ```text
//!   1. tighten every Le (`integer_tighten_le`)
//!   2. detect ground contradiction → Unsat
//!   3. if no variables left → return Unknown (caller falls through)
//!   4. pick a variable and eliminate it (one-shot FM real shadow)
//!   5. drop tautological / duplicated constraints
//!   6. goto 1
//! ```
//!
//! Soundness: every step is a sound rewriting. Tightening is exact for
//! ℤ. FM elimination yields a real-shadow projection — sound for
//! refutation: if any combined Le is integer-infeasible, the original
//! is infeasible. We never claim Sat from this loop.

use std::collections::BTreeSet;

use super::gcd_normalize::integer_tighten_le;
use crate::tactic::arithmetic::{LinearConstraint, LinearExpr};

/// Result of the iterative FM loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LeSolverResult {
    /// A ground contradiction was produced during the loop. The original
    /// system is `ℤ`-unsatisfiable.
    Unsat,
    /// During the loop, opposing `Le` constraints (whose expressions sum
    /// to zero) were detected and converted into `Eq` constraints. The
    /// caller should re-run the equality solver to propagate the new
    /// equality through the rest of the system.
    NewEqualitiesEmitted,
    /// Either no Le-only contradiction was found (system may be sat) or
    /// some elimination step overflowed and we bailed. Caller treats
    /// this as "no further progress" and falls through to the existing
    /// pipeline (which may still find contradictions in `Mod`/`Ne`).
    Unknown,
}

/// Detect pairs of `Le`/`Lt` constraints whose expressions sum to zero —
/// i.e. one says `expr ≤ 0` and another says `-expr ≤ 0`. Together they
/// imply `expr = 0`. Converts each detected pair into an `Eq` constraint
/// and removes the originating Le's. Returns `true` if any conversion
/// happened.
fn promote_opposing_les_to_eq(constraints: &mut Vec<LinearConstraint>) -> bool {
    let mut emitted = false;
    let mut to_remove: BTreeSet<usize> = BTreeSet::new();
    let mut new_eqs: Vec<LinearExpr> = Vec::new();

    // Inner loop uses `j > i`, so an iterator-based rewrite of the outer
    // loop alone would not silence the lint and only obscures the offset.
    #[allow(clippy::needless_range_loop)]
    for i in 0..constraints.len() {
        if to_remove.contains(&i) {
            continue;
        }
        let LinearConstraint::Le(e_i) = &constraints[i] else {
            continue;
        };
        // Negation of e_i: same coeffs flipped, opposite constant.
        for j in (i + 1)..constraints.len() {
            if to_remove.contains(&j) {
                continue;
            }
            let LinearConstraint::Le(e_j) = &constraints[j] else {
                continue;
            };
            if exprs_sum_to_zero(e_i, e_j) {
                new_eqs.push(e_i.clone());
                to_remove.insert(i);
                to_remove.insert(j);
                emitted = true;
                break;
            }
        }
    }

    if emitted {
        let mut new_constraints: Vec<LinearConstraint> =
            Vec::with_capacity(constraints.len() - to_remove.len() + new_eqs.len());
        for (idx, c) in constraints.drain(..).enumerate() {
            if !to_remove.contains(&idx) {
                new_constraints.push(c);
            }
        }
        for e in new_eqs {
            new_constraints.push(LinearConstraint::Eq(e));
        }
        *constraints = new_constraints;
    }

    emitted
}

/// True iff `a.coeffs == -b.coeffs` and `a.constant == -b.constant`.
fn exprs_sum_to_zero(a: &LinearExpr, b: &LinearExpr) -> bool {
    if a.constant != -b.constant {
        return false;
    }
    if a.coeffs.len() != b.coeffs.len() {
        return false;
    }
    a.coeffs
        .iter()
        .zip(b.coeffs.iter())
        .all(|(&(av, ac), &(bv, bc))| av == bv && ac == -bc)
}

/// Maximum elimination rounds before bailing — bounds worst-case
/// behaviour. Each FM step eliminates one variable, so the loop
/// terminates after at most `vars` iterations under normal inputs.
const MAX_ROUNDS: usize = 200;

/// Maximum Le constraints kept after a single FM round; prevents the
/// algorithm from running away on adversarial inputs.
const MAX_CONSTRAINTS: usize = 2000;

/// Run iterative tighten-and-eliminate on the `Le`/`Lt` subset of
/// `constraints`. Mutates `constraints` to reflect eliminated state.
/// `Ne` and `Mod` constraints are passed through unchanged.
pub(crate) fn solve_le_iteratively(constraints: &mut Vec<LinearConstraint>) -> LeSolverResult {
    // Up-front: lift every `Lt(e)` to `Le(e + 1)`. Over ℤ this is exact
    // (`e < 0` ⇔ `e ≤ -1` ⇔ `e + 1 ≤ 0`). Lets `integer_tighten_le`
    // see the result and tighten further. Saturating add to avoid
    // overflow on already-extreme constants.
    for c in constraints.iter_mut() {
        if let LinearConstraint::Lt(e) = c {
            let new = LinearExpr {
                constant: e.constant.saturating_add(1),
                coeffs: e.coeffs.clone(),
            };
            *c = LinearConstraint::Le(new);
        }
    }

    for _round in 0..MAX_ROUNDS {
        // 1. Tighten every Le.
        for c in constraints.iter_mut() {
            if let Some(t) = integer_tighten_le(c) {
                *c = t;
            }
        }

        // 1.5. Detect implicit equalities from opposing Le's
        // (e.g. `x ≤ 4 ∧ x ≥ 4` ⇒ `x = 4`). When found, promote to
        // `Eq` and ask the caller to re-run the equality solver.
        if promote_opposing_les_to_eq(constraints) {
            return LeSolverResult::NewEqualitiesEmitted;
        }

        // 2. Detect ground contradiction.
        for c in constraints.iter() {
            if let LinearConstraint::Le(e) | LinearConstraint::Lt(e) = c {
                if e.coeffs.is_empty() {
                    let ground = e.constant;
                    let bad = match c {
                        LinearConstraint::Le(_) => ground > 0,
                        LinearConstraint::Lt(_) => ground >= 0,
                        _ => false,
                    };
                    if bad {
                        return LeSolverResult::Unsat;
                    }
                }
            }
        }

        // 3. Collect Le/Lt variables.
        let vars: BTreeSet<usize> = constraints
            .iter()
            .filter(|c| matches!(c, LinearConstraint::Le(_) | LinearConstraint::Lt(_)))
            .flat_map(|c| c.expr().coeffs.iter().map(|&(v, _)| v))
            .collect();
        if vars.is_empty() {
            return LeSolverResult::Unknown;
        }

        // 4. Pick a variable. Heuristic: smallest fanout (fewest
        //    constraints mention it), tie-broken by smallest index.
        let var = *vars
            .iter()
            .min_by_key(|&&v| {
                constraints
                    .iter()
                    .filter(|c| matches!(c, LinearConstraint::Le(_) | LinearConstraint::Lt(_)))
                    .filter(|c| c.expr().get_coeff(v) != 0)
                    .count()
            })
            .expect("invariant: vars non-empty (checked above)");

        // 5. FM-combine on `var` and APPEND derived constraints. The
        //    originals are kept so any equality the next tighten-round
        //    derives via opposing Le's substitutes through everything.
        if fm_combine_appending(constraints, var).is_none() {
            return LeSolverResult::Unknown;
        }
        if constraints.len() > MAX_CONSTRAINTS {
            return LeSolverResult::Unknown;
        }
    }
    LeSolverResult::Unknown
}

/// **Append** FM-style combinations of (lower, upper) bound pairs on
/// `var`. The originals are kept so any equality later derived from
/// opposing tightened Le's can substitute back through all of them.
/// Returns `None` if any combination overflows i64.
fn fm_combine_appending(constraints: &mut Vec<LinearConstraint>, var: usize) -> Option<()> {
    let mut lower_bounds: Vec<LinearConstraint> = Vec::new();
    let mut upper_bounds: Vec<LinearConstraint> = Vec::new();

    for c in constraints.iter() {
        match c {
            LinearConstraint::Le(e) | LinearConstraint::Lt(e) => {
                let coef = e.get_coeff(var);
                if coef > 0 {
                    upper_bounds.push(c.clone());
                } else if coef < 0 {
                    lower_bounds.push(c.clone());
                }
            }
            _ => {}
        }
    }

    for lower in &lower_bounds {
        for upper in &upper_bounds {
            let combined = combine_le_pair(lower, upper, var)?;
            if !is_tautology(&combined) && !constraints.iter().any(|c| same_le(c, &combined)) {
                constraints.push(combined);
            }
        }
    }
    Some(())
}

/// Equality on Le/Lt with identical expressions; used to dedupe newly
/// combined constraints against existing ones.
fn same_le(a: &LinearConstraint, b: &LinearConstraint) -> bool {
    match (a, b) {
        (LinearConstraint::Le(ea), LinearConstraint::Le(eb))
        | (LinearConstraint::Lt(ea), LinearConstraint::Lt(eb)) => {
            ea.constant == eb.constant && ea.coeffs == eb.coeffs
        }
        _ => false,
    }
}

/// Combine a lower bound `(b·x ≥ U_l, encoded as -b·x + U_l ≤ 0)` with
/// an upper bound `(a·x ≤ -U_u, encoded as a·x + U_u ≤ 0)` to eliminate
/// `x`. The combination is `a · lower + b · upper`, where `a` and `b`
/// are the *positive* coefficients. The `x`-term cancels exactly:
/// `a · (-b) + b · a = 0`. Result is `Le` unless either input is `Lt`,
/// in which case the strict-ness propagates.
fn combine_le_pair(
    lower: &LinearConstraint,
    upper: &LinearConstraint,
    var: usize,
) -> Option<LinearConstraint> {
    let lower_expr = lower.expr();
    let upper_expr = upper.expr();
    let a = upper_expr.get_coeff(var); // > 0
    let b = -lower_expr.get_coeff(var); // > 0 (negated since stored as -b)
    if a <= 0 || b <= 0 {
        return None;
    }
    let scaled_lower = lower_expr.try_scale(a)?;
    let scaled_upper = upper_expr.try_scale(b)?;
    let combined_expr = linear_add(&scaled_lower, &scaled_upper)?;
    let strict =
        matches!(lower, LinearConstraint::Lt(_)) || matches!(upper, LinearConstraint::Lt(_));
    Some(if strict {
        LinearConstraint::Lt(combined_expr)
    } else {
        LinearConstraint::Le(combined_expr)
    })
}

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

fn is_tautology(c: &LinearConstraint) -> bool {
    match c {
        LinearConstraint::Le(e) => e.coeffs.is_empty() && e.constant <= 0,
        LinearConstraint::Lt(e) => e.coeffs.is_empty() && e.constant < 0,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn le(constant: i64, coeffs: &[(usize, i64)]) -> LinearConstraint {
        LinearConstraint::Le(LinearExpr {
            constant,
            coeffs: coeffs.to_vec(),
        })
    }

    /// `x ≤ 3 ∧ x ≥ 5` — ground after one elimination round: `2 ≤ 0` → Unsat.
    #[test]
    fn simple_pair_contradiction() {
        let mut cs = vec![le(-3, &[(0, 1)]), le(5, &[(0, -1)])];
        assert_eq!(solve_le_iteratively(&mut cs), LeSolverResult::Unsat);
    }

    /// `7y - 3 ≤ 0 ∧ 7y ≥ 4` — rationally `y ∈ [4/7, 3/7]` is empty, FM
    /// alone catches it: real shadow `7·(-3) + 7·4 = 7 ≤ 0` → impossible.
    /// Actually let me redo: 7y ≤ 3, 7y ≥ 4 → real shadow: 7·4 ≤ 7·3, 28 ≤ 21,
    /// false. → unsat via FM alone. Verify the loop reaches it.
    #[test]
    fn rational_unsat_caught() {
        // 7y - 3 ≤ 0  and  -7y + 4 ≤ 0  (i.e. 7y ≥ 4)
        let mut cs = vec![le(-3, &[(0, 7)]), le(4, &[(0, -7)])];
        assert_eq!(solve_le_iteratively(&mut cs), LeSolverResult::Unsat);
    }

    /// `7y - 4 ≤ 0 ∧ 7y - 3 ≥ 0` — rationally y ∈ [3/7, 4/7] non-empty.
    /// Integrally empty (no integer in (0, 1)). After tightening:
    /// `y ≤ 0` from `7y - 4 ≤ 0` (⌈-4/7⌉ = 0), and `-y + 1 ≤ 0` from
    /// `-7y + 3 ≤ 0` (⌈3/7⌉ = 1, giving `-y + 1 ≤ 0` → y ≥ 1). Together
    /// y ≥ 1 ∧ y ≤ 0 → Unsat after elimination.
    #[test]
    fn integer_only_unsat_via_tighten() {
        let mut cs = vec![le(-4, &[(0, 7)]), le(3, &[(0, -7)])];
        assert_eq!(solve_le_iteratively(&mut cs), LeSolverResult::Unsat);
    }

    /// Truly satisfiable system: x ∈ [0, 5]. Should return Unknown
    /// (no contradiction found).
    #[test]
    fn satisfiable_returns_unknown() {
        let mut cs = vec![le(-5, &[(0, 1)]), le(0, &[(0, -1)])];
        assert_eq!(solve_le_iteratively(&mut cs), LeSolverResult::Unknown);
    }

    /// Empty input — degenerate Unknown.
    #[test]
    fn empty_returns_unknown() {
        let mut cs: Vec<LinearConstraint> = vec![];
        assert_eq!(solve_le_iteratively(&mut cs), LeSolverResult::Unknown);
    }
}
