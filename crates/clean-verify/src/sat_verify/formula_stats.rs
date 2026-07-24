// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Formula analysis for proof-system routing.
//!
//! Computes structural statistics on a [`CnfFormula`] that guide the
//! selection of an appropriate proof system. For example, formulas with
//! high Horn clause ratio are amenable to resolution, while formulas
//! with many XOR patterns benefit from polynomial calculus.
//!
//! ## References
//!
//! - Ansotegui et al. (2012): Structure features for SAT instances.
//! - Mull et al. (2016): On the width of regular-resolution proofs.

use std::collections::HashMap;

use super::cnf_core::{CnfFormula, CnfLiteral};

/// Structural statistics of a CNF formula for proof-system routing.
#[derive(Debug, Clone)]
pub struct FormulaStats {
    /// Number of variables.
    pub num_vars: u32,
    /// Number of active clauses.
    pub num_clauses: usize,
    /// Distribution of clause lengths: length -> count.
    pub clause_length_distribution: HashMap<usize, usize>,
    /// Per-variable occurrence count (0-indexed).
    /// `variable_frequency[v]` = number of clauses containing variable v.
    pub variable_frequency: Vec<usize>,
    /// Fraction of clauses that are Horn (at most one positive literal).
    pub horn_clause_ratio: f64,
    /// Number of clause pairs that form XOR patterns.
    ///
    /// Two clauses form an XOR pattern over variables {v1, ..., vk} if they
    /// cover all 2^(k-1) parity-consistent assignments. We detect the
    /// simpler case: pairs of binary clauses {x, y} and {~x, ~y} or
    /// {x, ~y} and {~x, y}.
    pub xor_clause_count: usize,
    /// Upper bound on treewidth estimated via min-degree heuristic.
    ///
    /// `None` if the formula is empty or the estimate is not meaningful.
    pub estimated_treewidth: Option<usize>,
    /// Average clause length.
    pub avg_clause_length: f64,
    /// Maximum clause length.
    pub max_clause_length: usize,
    /// Variable-clause ratio (num_vars / num_clauses).
    pub var_clause_ratio: f64,
    /// Number of unit clauses.
    pub unit_clauses: usize,
    /// Number of binary clauses.
    pub binary_clauses: usize,
    /// Number of pure literals (appearing in only one polarity).
    pub pure_literals: usize,
}

/// Analyze a [`CnfFormula`] and compute structural statistics.
#[must_use]
pub fn analyze_formula(formula: &CnfFormula) -> FormulaStats {
    let num_vars = formula.num_vars;
    let num_clauses = formula.num_clauses();

    let mut clause_length_distribution: HashMap<usize, usize> = HashMap::new();
    let mut variable_frequency = vec![0usize; num_vars as usize];
    let mut positive_count = vec![0usize; num_vars as usize];
    let mut negative_count = vec![0usize; num_vars as usize];
    let mut horn_count = 0usize;
    let mut total_length = 0usize;
    let mut max_clause_length = 0usize;
    let mut unit_clauses = 0usize;
    let mut binary_clauses = 0usize;

    // Collect binary clauses for XOR detection.
    let mut binary_clause_set: Vec<(CnfLiteral, CnfLiteral)> = Vec::new();

    for (_cid, lits) in formula.db.iter_active() {
        let len = lits.len();
        *clause_length_distribution.entry(len).or_insert(0) += 1;
        total_length += len;
        if len > max_clause_length {
            max_clause_length = len;
        }
        if len == 1 {
            unit_clauses += 1;
        }
        if len == 2 {
            binary_clauses += 1;
            binary_clause_set.push((lits[0], lits[1]));
        }

        // Track variable frequency and polarity counts.
        let mut positive_in_clause = 0usize;
        let mut seen_vars = Vec::new();
        for &lit in lits {
            let v = lit.var() as usize;
            if v < num_vars as usize && !seen_vars.contains(&v) {
                variable_frequency[v] += 1;
                seen_vars.push(v);
            }
            if v < num_vars as usize {
                if lit.is_positive() {
                    positive_count[v] += 1;
                    positive_in_clause += 1;
                } else {
                    negative_count[v] += 1;
                }
            }
        }

        // Horn clause: at most one positive literal.
        if positive_in_clause <= 1 {
            horn_count += 1;
        }
    }

    let horn_clause_ratio = if num_clauses > 0 {
        horn_count as f64 / num_clauses as f64
    } else {
        0.0
    };

    let avg_clause_length = if num_clauses > 0 {
        total_length as f64 / num_clauses as f64
    } else {
        0.0
    };

    let var_clause_ratio = if num_clauses > 0 {
        num_vars as f64 / num_clauses as f64
    } else {
        0.0
    };

    // XOR detection: count binary clause pairs {a, b} and {~a, ~b}.
    let xor_clause_count = count_xor_patterns(&binary_clause_set);

    // Pure literals: variables appearing in only one polarity.
    let pure_literals = (0..num_vars as usize)
        .filter(|&v| {
            let has_pos = positive_count[v] > 0;
            let has_neg = negative_count[v] > 0;
            (has_pos && !has_neg) || (!has_pos && has_neg)
        })
        .count();

    // Treewidth upper bound via min-degree heuristic on primal graph.
    let estimated_treewidth = estimate_treewidth(formula);

    FormulaStats {
        num_vars,
        num_clauses,
        clause_length_distribution,
        variable_frequency,
        horn_clause_ratio,
        xor_clause_count,
        estimated_treewidth,
        avg_clause_length,
        max_clause_length,
        var_clause_ratio,
        unit_clauses,
        binary_clauses,
        pure_literals,
    }
}

/// Count XOR patterns among binary clauses.
///
/// A pair {a, b} and {~a, ~b} (or equivalently {a, ~b} and {~a, b}) encodes
/// an XOR constraint a XOR b = 0 (or 1).
fn count_xor_patterns(binary_clauses: &[(CnfLiteral, CnfLiteral)]) -> usize {
    use std::collections::HashSet;
    let mut clause_set: HashSet<(u32, u32)> = HashSet::new();
    for &(a, b) in binary_clauses {
        // Normalize: smaller code first.
        let (x, y) = if a.code() <= b.code() {
            (a.code(), b.code())
        } else {
            (b.code(), a.code())
        };
        clause_set.insert((x, y));
    }

    let mut count = 0usize;
    for &(a, b) in binary_clauses {
        // Check if the complementary pair exists.
        let neg_a = a.negate();
        let neg_b = b.negate();
        let (x, y) = if neg_a.code() <= neg_b.code() {
            (neg_a.code(), neg_b.code())
        } else {
            (neg_b.code(), neg_a.code())
        };
        if clause_set.contains(&(x, y)) {
            count += 1;
        }
    }
    // Each pair is counted twice (once from each clause).
    count / 2
}

/// Estimate treewidth upper bound using the min-degree elimination heuristic
/// on the primal graph (variables are nodes, edges connect variables sharing
/// a clause).
fn estimate_treewidth(formula: &CnfFormula) -> Option<usize> {
    let n = formula.num_vars as usize;
    if n == 0 {
        return None;
    }

    // Build adjacency list from clause co-occurrence.
    let mut adj: Vec<Vec<bool>> = vec![vec![false; n]; n];
    for (_cid, lits) in formula.db.iter_active() {
        let vars: Vec<usize> = lits.iter().map(|l| l.var() as usize).collect();
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                if vars[i] < n && vars[j] < n {
                    adj[vars[i]][vars[j]] = true;
                    adj[vars[j]][vars[i]] = true;
                }
            }
        }
    }

    // Min-degree elimination.
    let mut eliminated = vec![false; n];
    let mut max_degree = 0usize;

    for _ in 0..n {
        // Find the non-eliminated vertex with minimum degree.
        let mut min_deg = usize::MAX;
        let mut min_v = 0;
        for v in 0..n {
            if eliminated[v] {
                continue;
            }
            let deg = (0..n)
                .filter(|&u| !eliminated[u] && u != v && adj[v][u])
                .count();
            if deg < min_deg {
                min_deg = deg;
                min_v = v;
            }
        }
        if min_deg == usize::MAX {
            break;
        }
        if min_deg > max_degree {
            max_degree = min_deg;
        }

        // Add fill edges among neighbors of min_v.
        let neighbors: Vec<usize> = (0..n)
            .filter(|&u| !eliminated[u] && u != min_v && adj[min_v][u])
            .collect();
        for i in 0..neighbors.len() {
            for j in (i + 1)..neighbors.len() {
                adj[neighbors[i]][neighbors[j]] = true;
                adj[neighbors[j]][neighbors[i]] = true;
            }
        }

        eliminated[min_v] = true;
    }

    Some(max_degree)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_verify::cnf_core::{parse_dimacs, CnfFormula, CnfLiteral};

    #[test]
    fn test_analyze_empty_formula() {
        let formula = CnfFormula::new(0);
        let stats = analyze_formula(&formula);
        assert_eq!(stats.num_vars, 0);
        assert_eq!(stats.num_clauses, 0);
        assert_eq!(stats.horn_clause_ratio, 0.0);
        assert_eq!(stats.avg_clause_length, 0.0);
        assert!(stats.estimated_treewidth.is_none());
    }

    #[test]
    fn test_analyze_unit_clauses() {
        let mut formula = CnfFormula::new(3);
        formula.add_clause(&[CnfLiteral::positive(0)]);
        formula.add_clause(&[CnfLiteral::negative(1)]);
        formula.add_clause(&[CnfLiteral::positive(2)]);

        let stats = analyze_formula(&formula);
        assert_eq!(stats.num_vars, 3);
        assert_eq!(stats.num_clauses, 3);
        assert_eq!(stats.unit_clauses, 3);
        assert_eq!(stats.max_clause_length, 1);
        assert!((stats.avg_clause_length - 1.0).abs() < f64::EPSILON);
        // All unit clauses are Horn (0 or 1 positive literal).
        assert!((stats.horn_clause_ratio - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analyze_horn_clause_ratio() {
        let mut formula = CnfFormula::new(3);
        // Horn: at most 1 positive literal
        formula.add_clause(&[CnfLiteral::positive(0), CnfLiteral::negative(1)]);
        // Non-horn: 2 positive literals
        formula.add_clause(&[CnfLiteral::positive(0), CnfLiteral::positive(1)]);

        let stats = analyze_formula(&formula);
        assert!((stats.horn_clause_ratio - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analyze_clause_length_distribution() {
        let mut formula = CnfFormula::new(4);
        formula.add_clause(&[CnfLiteral::positive(0)]); // len 1
        formula.add_clause(&[CnfLiteral::positive(1), CnfLiteral::negative(2)]); // len 2
        formula.add_clause(&[
            CnfLiteral::positive(0),
            CnfLiteral::positive(1),
            CnfLiteral::positive(2),
        ]); // len 3

        let stats = analyze_formula(&formula);
        assert_eq!(stats.clause_length_distribution[&1], 1);
        assert_eq!(stats.clause_length_distribution[&2], 1);
        assert_eq!(stats.clause_length_distribution[&3], 1);
    }

    #[test]
    fn test_analyze_variable_frequency() {
        let mut formula = CnfFormula::new(3);
        formula.add_clause(&[CnfLiteral::positive(0), CnfLiteral::negative(1)]);
        formula.add_clause(&[CnfLiteral::positive(0), CnfLiteral::positive(2)]);
        formula.add_clause(&[CnfLiteral::negative(1), CnfLiteral::positive(2)]);

        let stats = analyze_formula(&formula);
        assert_eq!(stats.variable_frequency[0], 2); // var 0 in 2 clauses
        assert_eq!(stats.variable_frequency[1], 2); // var 1 in 2 clauses
        assert_eq!(stats.variable_frequency[2], 2); // var 2 in 2 clauses
    }

    #[test]
    fn test_analyze_xor_detection() {
        let mut formula = CnfFormula::new(2);
        // XOR(x0, x1) encodes as: {x0, x1} and {~x0, ~x1}
        formula.add_clause(&[CnfLiteral::positive(0), CnfLiteral::positive(1)]);
        formula.add_clause(&[CnfLiteral::negative(0), CnfLiteral::negative(1)]);

        let stats = analyze_formula(&formula);
        assert_eq!(stats.xor_clause_count, 1);
    }

    #[test]
    fn test_analyze_no_xor() {
        let mut formula = CnfFormula::new(2);
        formula.add_clause(&[CnfLiteral::positive(0), CnfLiteral::positive(1)]);
        formula.add_clause(&[CnfLiteral::positive(0), CnfLiteral::negative(1)]);

        let stats = analyze_formula(&formula);
        assert_eq!(stats.xor_clause_count, 0);
    }

    #[test]
    fn test_analyze_pure_literals() {
        let mut formula = CnfFormula::new(3);
        // var 0 appears only positive -> pure
        formula.add_clause(&[CnfLiteral::positive(0), CnfLiteral::positive(1)]);
        formula.add_clause(&[CnfLiteral::positive(0), CnfLiteral::negative(1)]);
        // var 1 appears both ways -> not pure
        // var 2 never appears -> not counted as pure (zero occurrences)

        let stats = analyze_formula(&formula);
        assert_eq!(stats.pure_literals, 1); // only var 0
    }

    #[test]
    fn test_analyze_treewidth_path() {
        // Three clauses forming a path: {0,1}, {1,2}, {2,3}
        let mut formula = CnfFormula::new(4);
        formula.add_clause(&[CnfLiteral::positive(0), CnfLiteral::positive(1)]);
        formula.add_clause(&[CnfLiteral::positive(1), CnfLiteral::positive(2)]);
        formula.add_clause(&[CnfLiteral::positive(2), CnfLiteral::positive(3)]);

        let stats = analyze_formula(&formula);
        // Path graph has treewidth 1.
        assert_eq!(stats.estimated_treewidth, Some(1));
    }

    #[test]
    fn test_analyze_treewidth_clique() {
        // One clause with all 3 variables -> complete graph K3
        let mut formula = CnfFormula::new(3);
        formula.add_clause(&[
            CnfLiteral::positive(0),
            CnfLiteral::positive(1),
            CnfLiteral::positive(2),
        ]);

        let stats = analyze_formula(&formula);
        // K3 has treewidth 2.
        assert_eq!(stats.estimated_treewidth, Some(2));
    }

    #[test]
    fn test_analyze_dimacs_pigeonhole_php21() {
        // PHP(2,1): 2 pigeons, 1 hole.
        // Pigeon 1 must go to hole 1: p_{1,1}
        // Pigeon 2 must go to hole 1: p_{2,1}
        // At most one pigeon per hole: ~p_{1,1} v ~p_{2,1}
        let input = "\
p cnf 2 3
1 0
2 0
-1 -2 0
";
        let formula = parse_dimacs(input).expect("parse");
        let stats = analyze_formula(&formula);
        assert_eq!(stats.num_vars, 2);
        assert_eq!(stats.num_clauses, 3);
        assert_eq!(stats.unit_clauses, 2);
        // The third clause (-1 -2) has 2 literals, so it is binary.
        assert_eq!(stats.binary_clauses, 1);
    }

    #[test]
    fn test_var_clause_ratio() {
        let mut formula = CnfFormula::new(10);
        for i in 0..5 {
            formula.add_clause(&[CnfLiteral::positive(i)]);
        }
        let stats = analyze_formula(&formula);
        assert!((stats.var_clause_ratio - 2.0).abs() < f64::EPSILON);
    }
}
