// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Normalization and simplification for pseudo-Boolean constraints.
//!
//! Operations:
//! - **Normalize**: merge duplicate literals, handle negated literals
//!   (x_i = 1 - ~x_i), ensure non-negative coefficients.
//! - **Saturate**: cap each coefficient at the degree.
//! - **Tautology/contradiction detection**: static analysis without assignment.
//! - **Formula simplification**: normalize all constraints, remove tautologies.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use std::collections::{HashMap, HashSet};

use super::types::{PbConstraint, PbFormula};

/// Normalize a PB constraint into canonical form.
///
/// Steps:
/// 1. Merge duplicate literals (sum coefficients for same literal).
/// 2. Handle negated pairs: if both `x` and `~x` appear, substitute
///    `~x = 1 - x` to consolidate into a single literal per variable.
/// 3. Flip negative coefficients: `-a * l` becomes `a * ~l`, degree += a.
/// 4. Remove zero-coefficient terms.
/// 5. Sort terms by variable index for canonical ordering.
#[must_use]
pub(crate) fn normalize(c: &PbConstraint) -> PbConstraint {
    // Step 1: merge duplicate literals.
    let mut lit_map: HashMap<i32, i64> = HashMap::new();
    for &(coeff, lit) in &c.terms {
        *lit_map.entry(lit).or_insert(0) += coeff;
    }

    // Step 2: consolidate pos/neg pairs per variable.
    // For variable v with positive-literal coefficient `a` and negative-literal
    // coefficient `b`:
    //   a * x + b * ~x = a * x + b * (1 - x) = (a - b) * x + b
    // Move constant b to RHS: net coefficient = a - b, degree -= b.
    let mut degree = c.degree;
    let mut terms: Vec<(i64, i32)> = Vec::new();
    let mut processed_vars: HashSet<u32> = HashSet::new();
    let lits: Vec<i32> = lit_map.keys().copied().collect();

    for lit in &lits {
        let var = lit.unsigned_abs();
        if !processed_vars.insert(var) {
            continue;
        }
        let pos = lit_map.get(&(var as i32)).copied().unwrap_or(0);
        let neg = lit_map.get(&-(var as i32)).copied().unwrap_or(0);

        if pos != 0 && neg != 0 {
            // a * x + b * ~x = (a - b) * x + b; degree -= b
            let net = pos - neg;
            degree -= neg;
            if net > 0 {
                terms.push((net, var as i32));
            } else if net < 0 {
                // net * x where net < 0: flip to |net| * ~x, degree += |net|.
                terms.push((-net, -(var as i32)));
                degree -= net; // net is negative, so this adds |net|
            }
            // net == 0: variable eliminated entirely.
        } else if pos != 0 {
            terms.push((pos, var as i32));
        } else if neg != 0 {
            terms.push((neg, -(var as i32)));
        }
    }

    // Step 3: flip any remaining negative coefficients.
    // This handles the case where a single literal had a negative coefficient
    // (without a complementary literal to consolidate with).
    let mut final_terms = Vec::with_capacity(terms.len());
    for (coeff, lit) in terms {
        if coeff == 0 {
            continue;
        }
        if coeff < 0 {
            // -a * l becomes a * ~l, degree += a
            final_terms.push((-coeff, -lit));
            degree -= coeff; // coeff is negative, so degree += |coeff|
        } else {
            final_terms.push((coeff, lit));
        }
    }

    // Step 5: sort by variable index for canonical ordering.
    final_terms.sort_by_key(|&(_, lit)| (lit.unsigned_abs(), lit < 0));

    PbConstraint {
        terms: final_terms,
        degree,
    }
}

/// Saturate a PB constraint: cap each positive coefficient at the degree.
///
/// For 0/1 variables, if `a_i > d` and `x_i = 1`, the term contributes `a_i`
/// but we only need `d` total. Capping at `d` preserves all satisfying
/// assignments. Soundness: `min(a_i, d) * x_i <= a_i * x_i` when `x_i = 1`,
/// so any assignment satisfying the original also satisfies the saturated form.
#[must_use]
pub(crate) fn saturate(c: &PbConstraint) -> PbConstraint {
    if c.degree <= 0 {
        return c.clone();
    }

    PbConstraint {
        terms: c
            .terms
            .iter()
            .map(|&(coeff, lit)| {
                if coeff > 0 {
                    (coeff.min(c.degree), lit)
                } else {
                    (coeff, lit)
                }
            })
            .collect(),
        degree: c.degree,
    }
}

/// Check if a PB constraint is a tautology.
///
/// A constraint is a tautology if it is satisfied by every 0/1 assignment.
/// For non-negative coefficients, the minimum LHS value is 0 (all literals
/// false), so degree <= 0 is required. For the general case, the minimum LHS
/// is the sum of all negative coefficients.
#[must_use]
pub(crate) fn is_tautology(c: &PbConstraint) -> bool {
    if c.degree <= 0 {
        return true;
    }

    // The minimum value of sum(a_i * l_i) for l_i in {0,1} is
    // the sum of negative coefficients (each contributes its value when l_i=1).
    let min_lhs: i64 = c.terms.iter().map(|&(coeff, _)| coeff.min(0)).sum();
    min_lhs >= c.degree
}

/// Simplify a PB formula: normalize all constraints and remove tautologies.
///
/// Preserves the variable count and objective. Constraint indices will shift
/// since tautologies are removed.
#[must_use]
pub(crate) fn simplify_formula(f: &PbFormula) -> PbFormula {
    let mut result = PbFormula::new(f.num_vars);
    result.objective = f.objective.clone();

    for constraint in &f.constraints {
        let normalized = normalize(constraint);
        if !is_tautology(&normalized) {
            result.add_constraint(normalized);
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normalize_merge_duplicate_literals() {
        // 1*x1 + 2*x1 + 3*x2 >= 4 -> 3*x1 + 3*x2 >= 4
        let c = PbConstraint::new(vec![(1, 1), (2, 1), (3, 2)], 4);
        let n = normalize(&c);
        let coeff_map: HashMap<i32, i64> = n.terms.iter().map(|&(c, l)| (l, c)).collect();
        assert_eq!(coeff_map.get(&1), Some(&3));
        assert_eq!(coeff_map.get(&2), Some(&3));
        assert_eq!(n.degree, 4);
    }

    #[test]
    fn test_normalize_negation_handling() {
        // 3*x1 + 2*~x1 >= 4
        // Substitute ~x1 = 1 - x1: 3*x1 + 2*(1 - x1) = x1 + 2 >= 4
        // So: x1 >= 2, degree = 4 - 2 = 2, coefficient = 1
        let c = PbConstraint::new(vec![(3, 1), (2, -1)], 4);
        let n = normalize(&c);
        let coeff_map: HashMap<i32, i64> = n.terms.iter().map(|&(c, l)| (l, c)).collect();
        assert_eq!(coeff_map.get(&1), Some(&1));
        assert!(!coeff_map.contains_key(&-1));
        assert_eq!(n.degree, 2);
    }

    #[test]
    fn test_normalize_negative_coefficient_flip() {
        // -2*x1 >= 1 -> 2*~x1 >= 3
        let c = PbConstraint::new(vec![(-2, 1)], 1);
        let n = normalize(&c);
        assert_eq!(n.terms.len(), 1);
        assert_eq!(n.terms[0].0, 2);
        assert_eq!(n.terms[0].1, -1);
        assert_eq!(n.degree, 3);
    }

    #[test]
    fn test_normalize_removes_zero_coefficients() {
        // 1*x1 + (-1)*x1 + 3*x2 >= 2
        // Both terms have literal 1 (positive): coeff sums to 0. Variable eliminated.
        let c = PbConstraint::new(vec![(1, 1), (-1, 1), (3, 2)], 2);
        let n = normalize(&c);
        let coeff_map: HashMap<i32, i64> = n.terms.iter().map(|&(c, l)| (l, c)).collect();
        assert!(!coeff_map.contains_key(&1));
        assert_eq!(coeff_map.get(&2), Some(&3));
    }

    #[test]
    fn test_normalize_sorted_output() {
        let c = PbConstraint::new(vec![(1, 3), (2, 1), (3, 2)], 4);
        let n = normalize(&c);
        assert_eq!(n.terms[0].1, 1);
        assert_eq!(n.terms[1].1, 2);
        assert_eq!(n.terms[2].1, 3);
    }

    #[test]
    fn test_saturate_caps_at_degree() {
        // 10*x1 + 5*x2 + 1*x3 >= 3
        let c = PbConstraint::new(vec![(10, 1), (5, 2), (1, 3)], 3);
        let s = saturate(&c);
        assert_eq!(s.terms[0], (3, 1));
        assert_eq!(s.terms[1], (3, 2));
        assert_eq!(s.terms[2], (1, 3));
        assert_eq!(s.degree, 3);
    }

    #[test]
    fn test_saturate_noop_when_coefficients_within_degree() {
        let c = PbConstraint::new(vec![(1, 1), (2, 2)], 3);
        let s = saturate(&c);
        assert_eq!(s, c);
    }

    #[test]
    fn test_saturate_noop_when_degree_nonpositive() {
        let c = PbConstraint::new(vec![(10, 1)], 0);
        let s = saturate(&c);
        assert_eq!(s, c);
    }

    #[test]
    fn test_is_tautology_true_for_trivial() {
        assert!(is_tautology(&PbConstraint::new(vec![], -1)));
        assert!(is_tautology(&PbConstraint::new(vec![], 0)));
    }

    #[test]
    fn test_is_tautology_false_for_nontrivial() {
        assert!(!is_tautology(&PbConstraint::new(vec![(1, 1)], 1)));
    }

    #[test]
    fn test_is_tautology_false_for_contradiction() {
        assert!(!is_tautology(&PbConstraint::new(vec![], 1)));
    }

    #[test]
    fn test_simplify_formula_removes_tautologies() {
        let mut f = PbFormula::new(2);
        f.add_constraint(PbConstraint::new(vec![(1, 1), (1, 2)], 1));
        f.add_constraint(PbConstraint::new(vec![(1, 1)], 0));
        f.add_constraint(PbConstraint::new(vec![(2, 1)], 2));

        let simplified = simplify_formula(&f);
        assert_eq!(simplified.constraints.len(), 2);
        assert_eq!(simplified.num_vars, 2);
    }

    #[test]
    fn test_simplify_formula_preserves_objective() {
        use super::super::types::PbObjective;

        let mut f = PbFormula::new(2);
        f.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
        f.set_objective(PbObjective::minimize(vec![(1, 1), (2, 2)]));

        let simplified = simplify_formula(&f);
        assert!(simplified.objective.is_some());
    }

    #[test]
    fn test_normalize_idempotent() {
        let c = PbConstraint::new(vec![(3, 1), (2, -1), (5, 2)], 4);
        let n1 = normalize(&c);
        let n2 = normalize(&n1);
        assert_eq!(n1, n2);
    }

    #[test]
    fn test_normalize_then_saturate() {
        // 10*x1 + 5*~x1 + 3*x2 >= 7
        // Normalize: net for x1 = 10 - 5 = 5, degree = 7 - 5 = 2
        // Result: 5*x1 + 3*x2 >= 2
        // Saturate: min(5, 2) = 2, min(3, 2) = 2
        // Result: 2*x1 + 2*x2 >= 2
        let c = PbConstraint::new(vec![(10, 1), (5, -1), (3, 2)], 7);
        let n = normalize(&c);
        assert_eq!(n.degree, 2);
        let coeff_map: HashMap<i32, i64> = n.terms.iter().map(|&(c, l)| (l, c)).collect();
        assert_eq!(coeff_map.get(&1), Some(&5));
        assert_eq!(coeff_map.get(&2), Some(&3));

        let s = saturate(&n);
        assert_eq!(s.degree, 2);
        let coeff_map: HashMap<i32, i64> = s.terms.iter().map(|&(c, l)| (l, c)).collect();
        assert_eq!(coeff_map.get(&1), Some(&2));
        assert_eq!(coeff_map.get(&2), Some(&2));
    }
}
