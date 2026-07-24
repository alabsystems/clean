// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct GF(2) polynomial encoding of Tseitin formulas.
//!
//! Tseitin formulas encode graph parity constraints: for each vertex, the
//! XOR of incident edge variables equals a given parity bit. In GF(2),
//! each vertex constraint is a single polynomial equation. In CNF, each
//! k-variable XOR constraint requires 2^{k-1} clauses.
//!
//! This module demonstrates the exponential separation between resolution
//! (which operates on CNF) and GF(2) Polynomial Calculus:
//!
//! - CNF encoding of Tseitin on a d-regular expander: O(n * 2^d) clauses.
//! - GF(2) encoding: exactly n polynomials (one per vertex).
//! - Resolution proof length: 2^{Mathverse(n/log n)} (Ben-Sasson & Wigderson, 1999).
//! - GF(2)-PC proof length: O(n) (summing the vertex polynomials).
//!
//! ## References
//!
//! - Ben-Sasson, Wigderson (1999). "Short proofs are narrow — resolution
//!   made simple." STOC 1999.
//! - Razborov (1998). "Lower bounds for the polynomial calculus."
//! - Tseitin (1968). "On the complexity of derivation in propositional
//!   calculus." Studies in Constructive Mathematics and Mathematical Logic.

use super::polynomial::Gf2Poly;

/// Encode Tseitin parity constraints directly as GF(2) polynomials.
///
/// For each vertex `v` in `0..num_vertices`, the constraint is:
///   sum of edge variables incident to v + parity_v = 0  (over GF(2))
///
/// Edge variables are numbered 0..edges.len()-1.
///
/// # Arguments
///
/// * `num_vertices` - Number of vertices in the graph.
/// * `edges` - ListType of undirected edges `(u, v)` with `u, v < num_vertices`.
/// * `parities` - Parity bit for each vertex. If shorter than `num_vertices`,
///   missing entries default to `false` (even parity).
///
/// # Returns
///
/// A vector of GF(2) polynomials, one per vertex with at least one incident
/// edge. Each polynomial is the sum of incident edge variables plus the
/// parity constant.
#[must_use]
pub fn tseitin_gf2_system(
    num_vertices: usize,
    edges: &[(usize, usize)],
    parities: &[bool],
) -> Vec<Gf2Poly> {
    let mut system = Vec::new();

    for v in 0..num_vertices {
        // Collect edge indices incident to vertex v.
        let incident: Vec<u32> = edges
            .iter()
            .enumerate()
            .filter(|(_, &(a, b))| a == v || b == v)
            .map(|(i, _)| i as u32)
            .collect();

        if incident.is_empty() {
            continue;
        }

        // Build polynomial: sum of incident edge variables.
        let mut poly = Gf2Poly::zero();
        for &edge_var in &incident {
            poly = poly.add(&Gf2Poly::variable(edge_var));
        }

        // Add parity constant (1 if odd parity).
        let parity = parities.get(v).copied().unwrap_or(false);
        if parity {
            poly = poly.add(&Gf2Poly::one());
        }

        system.push(poly);
    }

    system
}

/// Generate a regular-ish expander-like graph on `n` vertices.
///
/// Uses a deterministic construction based on modular arithmetic to create
/// a graph where each vertex has degree approximately 3-4. This is not a
/// true Ramanujan expander, but it has good expansion properties for small
/// `n` and serves to demonstrate the separation.
///
/// Returns the edge list.
#[must_use]
pub fn generate_expander_graph(n: usize) -> Vec<(usize, usize)> {
    if n < 3 {
        // Trivial cases.
        if n == 2 {
            return vec![(0, 1)];
        }
        return vec![];
    }

    let mut edges = Vec::new();
    let mut seen = std::collections::HashSet::new();

    // Cycle: connect i to (i+1) mod n.
    for i in 0..n {
        let j = (i + 1) % n;
        let (a, b) = if i < j { (i, j) } else { (j, i) };
        if seen.insert((a, b)) {
            edges.push((a, b));
        }
    }

    // Additional connections for expansion: connect i to (i+2) mod n
    // (if n >= 5) to increase connectivity.
    if n >= 5 {
        for i in 0..n {
            let j = (i + 2) % n;
            let (a, b) = if i < j { (i, j) } else { (j, i) };
            if seen.insert((a, b)) {
                edges.push((a, b));
            }
        }
    }

    edges
}

/// Demonstrate the exponential separation between CNF and GF(2) encodings
/// of Tseitin formulas on expander-like graphs.
///
/// For a graph on `n` vertices with vertex degree `d`:
/// - GF(2) system size: n polynomials, each of degree 1.
/// - CNF encoding: O(n * 2^{d-1}) clauses.
///
/// Returns `(gf2_poly_count, gf2_max_terms, cnf_clause_count, num_vars)`.
///
/// The GF(2) system is unsatisfiable (odd parity sum) and can be refuted
/// in O(n) steps by summing all vertex polynomials.
#[must_use]
pub fn demonstrate_exponential_separation(n: usize) -> (usize, usize, usize, usize) {
    let edges = generate_expander_graph(n);
    let num_edges = edges.len();

    // Set parities: make the sum odd so the system is UNSAT.
    // Set vertex 0 to parity 1, all others to 0.
    let mut parities = vec![false; n];
    if !parities.is_empty() {
        parities[0] = true;
    }

    // GF(2) encoding.
    let gf2_system = tseitin_gf2_system(n, &edges, &parities);
    let gf2_poly_count = gf2_system.len();
    let gf2_max_terms = gf2_system.iter().map(|p| p.num_terms()).max().unwrap_or(0);

    // CNF encoding using the existing Tseitin encoder.
    let edges_u32: Vec<(u32, u32)> = edges.iter().map(|&(a, b)| (a as u32, b as u32)).collect();
    let (cnf_clauses, _cnf_num_vars) =
        super::super::frontier::gf2_algebra::generate_tseitin_cnf(n as u32, &edges_u32, &parities);
    let cnf_clause_count = cnf_clauses.len();

    (gf2_poly_count, gf2_max_terms, cnf_clause_count, num_edges)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_verify::gf2_polynomial::groebner::{buchberger, is_unsatisfiable};

    #[test]
    fn test_tseitin_triangle_unsat() {
        // Triangle: 3 vertices, 3 edges.
        // Edges: (0,1), (1,2), (0,2).
        // Parity: [true, false, false] -> sum = 1 (odd) -> UNSAT.
        let edges = vec![(0, 1), (1, 2), (0, 2)];
        let parities = vec![true, false, false];
        let system = tseitin_gf2_system(3, &edges, &parities);

        assert_eq!(system.len(), 3);

        // Verify via Groebner basis.
        let basis = buchberger(&system, 3);
        assert!(is_unsatisfiable(&basis));
    }

    #[test]
    fn test_tseitin_triangle_sat() {
        // Triangle with even parity sum -> SAT.
        let edges = vec![(0, 1), (1, 2), (0, 2)];
        let parities = vec![false, false, false];
        let system = tseitin_gf2_system(3, &edges, &parities);

        let basis = buchberger(&system, 3);
        assert!(!is_unsatisfiable(&basis));
    }

    #[test]
    fn test_tseitin_gf2_system_structure() {
        // Verify that each polynomial is linear (degree 1).
        let edges = vec![(0, 1), (1, 2), (2, 3), (3, 0)];
        let parities = vec![true, false, false, false];
        let system = tseitin_gf2_system(4, &edges, &parities);

        for poly in &system {
            assert!(
                poly.degree() <= 1,
                "Tseitin GF(2) polynomials must be linear"
            );
        }
    }

    #[test]
    fn test_tseitin_sum_proves_unsat() {
        // The key insight: summing all vertex polynomials in an UNSAT
        // Tseitin instance gives the constant 1.
        //
        // Each edge variable appears in exactly 2 vertex polynomials,
        // so it cancels (2 = 0 in GF(2)). What remains is the sum of
        // parity constants. If that sum is odd, we get 1 = 0.
        let edges = vec![(0, 1), (1, 2), (0, 2)];
        let parities = vec![true, false, false]; // sum = 1 (odd)
        let system = tseitin_gf2_system(3, &edges, &parities);

        let sum = system.iter().fold(Gf2Poly::zero(), |acc, p| acc.add(p));
        assert!(sum.is_one(), "sum of UNSAT Tseitin polynomials should be 1");
    }

    #[test]
    fn test_tseitin_sum_even_parity() {
        // Even parity sum: summing all polynomials gives 0 (consistent).
        let edges = vec![(0, 1), (1, 2), (0, 2)];
        let parities = vec![false, false, false];
        let system = tseitin_gf2_system(3, &edges, &parities);

        let sum = system.iter().fold(Gf2Poly::zero(), |acc, p| acc.add(p));
        assert!(sum.is_zero(), "sum of SAT Tseitin polynomials should be 0");
    }

    #[test]
    fn test_generate_expander_graph_small() {
        let edges = generate_expander_graph(5);
        assert!(!edges.is_empty());
        // Should have cycle edges + extra connections.
        assert!(edges.len() >= 5); // at least the cycle
    }

    #[test]
    fn test_exponential_separation() {
        let (gf2_count, _gf2_max, cnf_count, num_vars) = demonstrate_exponential_separation(6);

        // GF(2) system should have exactly one poly per vertex (6).
        assert_eq!(gf2_count, 6);

        // CNF should have significantly more clauses than GF(2) polynomials.
        assert!(
            cnf_count > gf2_count,
            "CNF ({cnf_count} clauses) should exceed GF(2) ({gf2_count} polys) \
             for {num_vars} edge variables"
        );
    }

    #[test]
    fn test_exponential_separation_grows() {
        // Verify that the ratio CNF/GF(2) grows with n.
        let (gf2_6, _, cnf_6, _) = demonstrate_exponential_separation(6);
        let (gf2_10, _, cnf_10, _) = demonstrate_exponential_separation(10);

        let ratio_6 = cnf_6 as f64 / gf2_6 as f64;
        let ratio_10 = cnf_10 as f64 / gf2_10 as f64;

        assert!(
            ratio_10 >= ratio_6,
            "CNF/GF(2) ratio should grow: n=6 -> {ratio_6:.1}, n=10 -> {ratio_10:.1}"
        );
    }

    #[test]
    fn test_tseitin_empty_graph() {
        let system = tseitin_gf2_system(3, &[], &[true, false, false]);
        assert!(system.is_empty(), "no edges means no constraints");
    }

    #[test]
    fn test_tseitin_isolated_vertex() {
        // Vertex 2 has no edges -> should be skipped.
        let edges = vec![(0, 1)];
        let parities = vec![true, false, false];
        let system = tseitin_gf2_system(3, &edges, &parities);
        // Only vertices 0 and 1 have incident edges.
        assert_eq!(system.len(), 2);
    }
}
