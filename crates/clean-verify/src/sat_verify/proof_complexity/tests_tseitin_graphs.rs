// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tseitin graph formula generation and analysis.

use super::tseitin_graphs::*;

// ---------------------------------------------------------------------------
// Cycle graph tests
// ---------------------------------------------------------------------------

#[test]
fn test_cycle_graph_3_vertices() {
    let g = cycle_graph(3);
    assert_eq!(g.num_vertices, 3);
    assert_eq!(g.edges.len(), 3);
}

#[test]
fn test_cycle_graph_4_vertices() {
    let g = cycle_graph(4);
    assert_eq!(g.num_vertices, 4);
    assert_eq!(g.edges.len(), 4);
    // Verify wrap-around edge exists
    assert!(g.edges.contains(&(3, 0)));
}

#[test]
fn test_cycle_graph_10_vertices() {
    let g = cycle_graph(10);
    assert_eq!(g.num_vertices, 10);
    assert_eq!(g.edges.len(), 10);
}

#[test]
fn test_cycle_graph_degenerate_below_3() {
    let g = cycle_graph(2);
    assert_eq!(g.num_vertices, 2);
    assert!(g.edges.is_empty(), "no valid cycle with < 3 vertices");

    let g0 = cycle_graph(0);
    assert_eq!(g0.num_vertices, 0);
    assert!(g0.edges.is_empty());
}

#[test]
fn test_cycle_graph_all_degree_2() {
    let g = cycle_graph(7);
    let mut degree = vec![0usize; g.num_vertices];
    for &(u, v) in &g.edges {
        degree[u] += 1;
        degree[v] += 1;
    }
    for (v, d) in degree.iter().enumerate() {
        assert_eq!(*d, 2, "vertex {v} should have degree 2");
    }
}

// ---------------------------------------------------------------------------
// Grid graph tests
// ---------------------------------------------------------------------------

#[test]
fn test_grid_graph_2x2() {
    let g = grid_graph(2, 2);
    assert_eq!(g.num_vertices, 4);
    // 2x2 grid: 2 horizontal + 2 vertical = 4 edges
    assert_eq!(g.edges.len(), 4);
}

#[test]
fn test_grid_graph_3x3() {
    let g = grid_graph(3, 3);
    assert_eq!(g.num_vertices, 9);
    // 3x3 grid: 3*2 horizontal + 2*3 vertical = 6 + 6 = 12 edges
    assert_eq!(g.edges.len(), 12);
}

#[test]
fn test_grid_graph_1xn_is_path() {
    let g = grid_graph(1, 5);
    assert_eq!(g.num_vertices, 5);
    assert_eq!(g.edges.len(), 4, "1x5 grid is a path with 4 edges");
}

#[test]
fn test_grid_graph_empty() {
    let g = grid_graph(0, 5);
    assert_eq!(g.num_vertices, 0);
    assert!(g.edges.is_empty());
}

// ---------------------------------------------------------------------------
// Complete graph tests
// ---------------------------------------------------------------------------

#[test]
fn test_complete_graph_3() {
    let g = complete_graph(3);
    assert_eq!(g.num_vertices, 3);
    assert_eq!(g.edges.len(), 3); // C(3,2) = 3
}

#[test]
fn test_complete_graph_4() {
    let g = complete_graph(4);
    assert_eq!(g.num_vertices, 4);
    assert_eq!(g.edges.len(), 6); // C(4,2) = 6
}

#[test]
fn test_complete_graph_edge_count_formula() {
    for n in 0..=8 {
        let g = complete_graph(n);
        let expected = n * n.saturating_sub(1) / 2;
        assert_eq!(g.edges.len(), expected, "K_{n} edge count");
    }
}

#[test]
fn test_complete_graph_all_pairs_present() {
    let g = complete_graph(5);
    for i in 0..5 {
        for j in (i + 1)..5 {
            assert!(g.edges.contains(&(i, j)), "edge ({i},{j}) missing from K_5");
        }
    }
}

// ---------------------------------------------------------------------------
// Expander graph tests
// ---------------------------------------------------------------------------

#[test]
fn test_expander_graph_basic() {
    let g = expander_graph(10, 3);
    assert_eq!(g.num_vertices, 10);
    assert!(!g.edges.is_empty(), "expander should have edges");
}

#[test]
fn test_expander_graph_degree_bound() {
    let n = 12;
    let degree = 4;
    let g = expander_graph(n, degree);
    // Each vertex has at most `degree` distinct neighbors
    let mut adj_count = vec![0usize; n];
    for &(u, v) in &g.edges {
        adj_count[u] += 1;
        adj_count[v] += 1;
    }
    for (v, &d) in adj_count.iter().enumerate() {
        assert!(d <= 2 * degree, "vertex {v} degree {d} exceeds 2*{degree}");
    }
}

#[test]
fn test_expander_graph_no_self_loops() {
    let g = expander_graph(15, 3);
    for &(u, v) in &g.edges {
        assert_ne!(u, v, "self-loop found");
    }
}

#[test]
fn test_expander_graph_degenerate() {
    let g = expander_graph(1, 3);
    assert!(g.edges.is_empty());
    let g0 = expander_graph(0, 3);
    assert!(g0.edges.is_empty());
}

// ---------------------------------------------------------------------------
// Tseitin formula tests
// ---------------------------------------------------------------------------

#[test]
fn test_tseitin_on_cycle_even_parity_satisfiable() {
    // Cycle of 4, all-false parity => even total => satisfiable
    let g = cycle_graph(4);
    let parity = vec![false; 4];
    let clauses = tseitin_on_graph(&g, &parity);
    assert!(!clauses.is_empty());
    // Even parity should be satisfiable
    assert!(verify_tseitin_parity(&g, &parity));
}

#[test]
fn test_tseitin_on_cycle_odd_parity_unsatisfiable() {
    // Cycle of 4, one vertex has parity true => odd total => unsat
    let g = cycle_graph(4);
    let parity = vec![true, false, false, false];
    let clauses = tseitin_on_graph(&g, &parity);
    assert!(!clauses.is_empty());
    assert!(!verify_tseitin_parity(&g, &parity));
}

#[test]
fn test_tseitin_on_grid_even_parity() {
    let g = grid_graph(2, 2);
    let parity = vec![false; 4];
    assert!(verify_tseitin_parity(&g, &parity));
    let clauses = tseitin_on_graph(&g, &parity);
    assert!(!clauses.is_empty());
}

#[test]
fn test_tseitin_on_grid_odd_parity() {
    let g = grid_graph(2, 2);
    // Three false + one true = odd total => unsat
    let parity = vec![true, false, false, false];
    assert!(!verify_tseitin_parity(&g, &parity));
}

#[test]
fn test_tseitin_on_complete_graph() {
    let g = complete_graph(4);
    // Even number of trues => even parity => sat
    let parity = vec![true, true, false, false];
    assert!(verify_tseitin_parity(&g, &parity));
    let clauses = tseitin_on_graph(&g, &parity);
    assert!(!clauses.is_empty());
}

#[test]
fn test_tseitin_formula_clause_count() {
    // For a cycle of n, each vertex has degree 2 => 2^(2-1) = 2 clauses per vertex
    // Total: n * 2 = 2n clauses
    let g = cycle_graph(5);
    let parity = vec![false; 5];
    let clauses = tseitin_on_graph(&g, &parity);
    assert_eq!(clauses.len(), 10, "cycle(5) should produce 2*5=10 clauses");
}

// ---------------------------------------------------------------------------
// Parity verification tests
// ---------------------------------------------------------------------------

#[test]
fn test_parity_even_is_satisfiable() {
    let g = cycle_graph(6);
    // Even number of true parities => sat
    let parity = vec![true, true, false, false, false, false];
    assert!(verify_tseitin_parity(&g, &parity));
}

#[test]
fn test_parity_odd_is_unsatisfiable() {
    let g = cycle_graph(6);
    // Odd number of true parities => unsat
    let parity = vec![true, true, true, false, false, false];
    assert!(!verify_tseitin_parity(&g, &parity));
}

#[test]
fn test_parity_all_false_is_satisfiable() {
    let g = complete_graph(5);
    let parity = vec![false; 5];
    assert!(verify_tseitin_parity(&g, &parity));
}

#[test]
fn test_parity_all_true_even_count() {
    // 4 true values => even => sat
    let g = grid_graph(2, 2);
    let parity = vec![true; 4];
    assert!(verify_tseitin_parity(&g, &parity));
}

#[test]
fn test_parity_all_true_odd_count() {
    // 3 true values => odd => unsat
    let g = cycle_graph(3);
    let parity = vec![true; 3];
    assert!(!verify_tseitin_parity(&g, &parity));
}

#[test]
fn test_parity_short_defaults_to_false() {
    let g = cycle_graph(4);
    // Only 2 parities given, rest default to false
    let parity = vec![true, true];
    // total = true ^ true ^ false ^ false = false => sat
    assert!(verify_tseitin_parity(&g, &parity));
}

// ---------------------------------------------------------------------------
// Expansion tests
// ---------------------------------------------------------------------------

#[test]
fn test_expansion_cycle() {
    let g = cycle_graph(6);
    let h = graph_expansion(&g);
    // Cycle expansion: cutting one vertex removes 2 edges => h(C_n) = 2/1 = 2
    // for single vertex. But the minimum over all subsets: for S of size n/2,
    // we get 2 cut edges / (n/2) = 4/n. The minimum is at the largest subset.
    assert!(h > 0.0, "cycle expansion should be positive");
    assert!(h <= 2.0, "cycle expansion should be at most 2.0");
}

#[test]
fn test_expansion_complete() {
    let g = complete_graph(4);
    let h = graph_expansion(&g);
    // K_4: single vertex cut = 3 edges / 1 = 3.0
    // Two vertices cut = 4 edges / 2 = 2.0
    // Minimum expansion is 2.0
    assert!(
        (h - 2.0).abs() < 1e-9,
        "K_4 expansion should be 2.0, got {h}"
    );
}

#[test]
fn test_expansion_grid() {
    let g = grid_graph(3, 3);
    let h = graph_expansion(&g);
    assert!(h > 0.0, "grid expansion should be positive");
    // Grid expansion is relatively low (O(1/sqrt(n)))
    assert!(h < 3.0, "grid expansion should be moderate");
}

#[test]
fn test_expansion_empty_graph() {
    let g = Graph {
        num_vertices: 5,
        edges: Vec::new(),
    };
    assert_eq!(graph_expansion(&g), 0.0);
}

#[test]
fn test_expansion_single_vertex() {
    let g = Graph {
        num_vertices: 1,
        edges: Vec::new(),
    };
    assert_eq!(graph_expansion(&g), 0.0);
}

// ---------------------------------------------------------------------------
// Variable count tests
// ---------------------------------------------------------------------------

#[test]
fn test_variable_count_cycle() {
    let g = cycle_graph(5);
    assert_eq!(formula_variable_count(&g), 5);
}

#[test]
fn test_variable_count_complete() {
    let g = complete_graph(4);
    assert_eq!(formula_variable_count(&g), 6);
}

#[test]
fn test_variable_count_grid() {
    let g = grid_graph(3, 3);
    assert_eq!(formula_variable_count(&g), 12);
}

#[test]
fn test_variable_count_empty() {
    let g = Graph {
        num_vertices: 3,
        edges: Vec::new(),
    };
    assert_eq!(formula_variable_count(&g), 0);
}

// ---------------------------------------------------------------------------
// Edge case tests
// ---------------------------------------------------------------------------

#[test]
fn test_tseitin_empty_graph() {
    let g = Graph {
        num_vertices: 0,
        edges: Vec::new(),
    };
    let clauses = tseitin_on_graph(&g, &[]);
    assert!(clauses.is_empty());
}

#[test]
fn test_tseitin_isolated_vertex_with_parity() {
    // Isolated vertex with parity true => unsatisfiable (empty clause)
    let g = Graph {
        num_vertices: 1,
        edges: Vec::new(),
    };
    let parity = vec![true];
    let clauses = tseitin_on_graph(&g, &parity);
    // Should contain an empty clause (contradiction)
    assert!(
        clauses.iter().any(|c| c.is_empty()),
        "should have empty clause"
    );
}

#[test]
fn test_tseitin_clause_variables_in_range() {
    let g = cycle_graph(5);
    let parity = vec![false; 5];
    let clauses = tseitin_on_graph(&g, &parity);
    let num_vars = formula_variable_count(&g) as i32;
    for clause in &clauses {
        for &lit in clause {
            let var = lit.unsigned_abs() as i32;
            assert!(
                var >= 1 && var <= num_vars,
                "variable {var} out of range [1, {num_vars}]"
            );
        }
    }
}
