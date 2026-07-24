// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tseitin Formula Generation over Explicit Graph Structures
//!
//! Constructs Tseitin formulas (parity constraints) on graphs, following
//! the proof complexity tradition of Ben-Sasson & Wigderson (1999).
//!
//! Each edge of a graph becomes a Boolean variable. Each vertex imposes
//! a parity constraint: the XOR of incident edge variables must equal
//! the vertex's assigned parity bit. The resulting CNF is unsatisfiable
//! exactly when the total parity (XOR of all vertex parities) is odd.
//!
//! Graph families provided:
//! - **Cycle**: hard for tree-resolution
//! - **Grid**: moderate expansion, standard benchmark
//! - **Complete**: maximum expansion, easiest Tseitin instances
//! - **Expander**: deterministic Margulis-like construction for
//!   exponential resolution lower bounds

/// An undirected graph represented by vertex count and edge list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Graph {
    pub num_vertices: usize,
    pub edges: Vec<(usize, usize)>,
}

/// Construct a cycle graph on `n` vertices (C_n).
///
/// Vertices 0..n, edges: (0,1), (1,2), ..., (n-2,n-1), (n-1,0).
/// Returns an empty graph for n < 3 (no valid cycle).
#[must_use]
pub fn cycle_graph(n: usize) -> Graph {
    if n < 3 {
        return Graph {
            num_vertices: n,
            edges: Vec::new(),
        };
    }
    let edges = (0..n).map(|i| (i, (i + 1) % n)).collect();
    Graph {
        num_vertices: n,
        edges,
    }
}

/// Construct a grid graph with `rows` x `cols` vertices.
///
/// Vertex (r, c) is indexed as r * cols + c.
/// Horizontal edges connect (r,c)-(r,c+1), vertical edges connect (r,c)-(r+1,c).
#[must_use]
pub fn grid_graph(rows: usize, cols: usize) -> Graph {
    let num_vertices = rows * cols;
    let mut edges = Vec::new();
    let idx = |r: usize, c: usize| r * cols + c;
    for r in 0..rows {
        for c in 0..cols {
            if c + 1 < cols {
                edges.push((idx(r, c), idx(r, c + 1)));
            }
            if r + 1 < rows {
                edges.push((idx(r, c), idx(r + 1, c)));
            }
        }
    }
    Graph {
        num_vertices,
        edges,
    }
}

/// Construct the complete graph K_n on `n` vertices.
///
/// Every pair of distinct vertices is connected. n*(n-1)/2 edges total.
#[must_use]
pub fn complete_graph(n: usize) -> Graph {
    let mut edges = Vec::new();
    for i in 0..n {
        for j in (i + 1)..n {
            edges.push((i, j));
        }
    }
    Graph {
        num_vertices: n,
        edges,
    }
}

/// Construct a deterministic expander-like graph (Margulis approximation).
///
/// Uses a Cayley-graph-inspired construction on Z_n x Z_n with
/// algebraic neighbor generators, projected down to `n` vertices.
/// Each vertex v connects to `degree` neighbors via:
///   neighbor_k(v) = (v + k * (v + 1)) mod n, for k in 1..=degree
/// with self-loops and duplicate edges removed.
///
/// This is a deterministic approximation; true Ramanujan expanders
/// require more sophisticated algebraic constructions.
#[must_use]
pub fn expander_graph(n: usize, degree: usize) -> Graph {
    if n < 2 {
        return Graph {
            num_vertices: n,
            edges: Vec::new(),
        };
    }
    let mut edge_set = std::collections::BTreeSet::new();
    for v in 0..n {
        for k in 1..=degree {
            let neighbor = (v + k * (v + 1)) % n;
            if neighbor != v {
                let e = if v < neighbor {
                    (v, neighbor)
                } else {
                    (neighbor, v)
                };
                edge_set.insert(e);
            }
        }
    }
    Graph {
        num_vertices: n,
        edges: edge_set.into_iter().collect(),
    }
}

/// Generate a Tseitin CNF formula from a graph and vertex parity assignment.
///
/// One Boolean variable per edge (1-indexed). For each vertex, the XOR of
/// its incident edge variables must equal the vertex's parity bit.
///
/// The XOR constraint for degree-d vertex with parity p is encoded as
/// 2^(d-1) clauses, each of width d, covering all odd/even sign combinations.
///
/// Returns DIMACS-style clause vectors (positive/negative i32 literals).
/// If `parity` is shorter than `num_vertices`, missing entries default to `false`.
#[must_use]
pub fn tseitin_on_graph(graph: &Graph, parity: &[bool]) -> Vec<Vec<i32>> {
    let incident = build_incidence(graph);
    let mut clauses = Vec::new();
    for (v, edges) in incident.iter().enumerate() {
        let p = parity.get(v).copied().unwrap_or(false);
        encode_xor_constraint(edges, p, &mut clauses);
    }
    clauses
}

/// Check if a Tseitin parity assignment is satisfiable.
///
/// A Tseitin formula is satisfiable iff the XOR of all vertex parities is
/// `false` (even total parity). This is because each edge variable appears
/// in exactly two vertex constraints, so summing all constraints mod 2
/// cancels all variables, leaving just the XOR of parities.
#[must_use]
pub fn verify_tseitin_parity(graph: &Graph, parity: &[bool]) -> bool {
    let n = graph.num_vertices;
    let total = (0..n)
        .map(|v| parity.get(v).copied().unwrap_or(false))
        .fold(false, |acc, p| acc ^ p);
    !total
}

/// Count the number of edge variables in a Tseitin encoding over this graph.
#[must_use]
pub fn formula_variable_count(graph: &Graph) -> usize {
    graph.edges.len()
}

/// Estimate the edge expansion of a graph.
///
/// Edge expansion h(G) = min over non-empty S with |S| <= n/2 of
/// |E(S, V\S)| / |S|.
///
/// This uses an exhaustive search for small graphs (n <= 16) and a
/// sampling heuristic for larger graphs. The exhaustive search considers
/// all non-empty subsets of size <= n/2.
#[must_use]
pub fn graph_expansion(graph: &Graph) -> f64 {
    let n = graph.num_vertices;
    if n <= 1 || graph.edges.is_empty() {
        return 0.0;
    }
    if n <= 16 {
        expansion_exhaustive(graph)
    } else {
        expansion_sampled(graph)
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Build incidence lists: for each vertex, the 1-indexed edge variable IDs.
fn build_incidence(graph: &Graph) -> Vec<Vec<i32>> {
    let mut incident: Vec<Vec<i32>> = vec![Vec::new(); graph.num_vertices];
    for (idx, &(u, v)) in graph.edges.iter().enumerate() {
        let var = (idx + 1) as i32; // 1-indexed DIMACS variable
        if u < graph.num_vertices {
            incident[u].push(var);
        }
        if v < graph.num_vertices {
            incident[v].push(var);
        }
    }
    incident
}

/// Encode XOR constraint: XOR of `vars` = `target_parity`.
///
/// Generates 2^(d-1) clauses for d variables. Each clause has
/// all d variables with signs chosen so an odd/even number are negated.
fn encode_xor_constraint(vars: &[i32], target_parity: bool, clauses: &mut Vec<Vec<i32>>) {
    let d = vars.len();
    if d == 0 {
        // Zero-degree vertex with parity true = unsatisfiable constraint.
        if target_parity {
            clauses.push(Vec::new()); // empty clause = contradiction
        }
        return;
    }
    // We enumerate all 2^d sign patterns and keep those whose negation
    // count parity matches the target.
    // XOR(x1,...,xd) = target_parity is satisfied when the number of
    // true variables has parity = target_parity.
    // Each clause blocks one "bad" assignment: one where the number of
    // true variables has the wrong parity.
    let total = 1u32 << d;
    for mask in 0..total {
        let neg_count = mask.count_ones() as usize;
        // This mask represents: for each bit i, if set then variable i is negated.
        // The clause is satisfied unless all literals are false, i.e. unless
        // variable i is true when negated, false when positive.
        // That means variable i is true iff bit i is set, so #true = neg_count.
        // We want to block assignments where #true has wrong parity.
        let assignment_parity = (neg_count % 2) == 1;
        if assignment_parity != target_parity {
            continue;
        }
        // Block this assignment: clause has literal positive if bit=1
        // (negating the assignment), negative if bit=0.
        let clause: Vec<i32> = (0..d)
            .map(|i| {
                if (mask >> i) & 1 == 1 {
                    -vars[i]
                } else {
                    vars[i]
                }
            })
            .collect();
        clauses.push(clause);
    }
}

/// Exhaustive expansion computation for small graphs.
fn expansion_exhaustive(graph: &Graph) -> f64 {
    let n = graph.num_vertices;
    let half = n / 2;
    let mut min_expansion = f64::INFINITY;

    // Enumerate all non-empty subsets of size 1..=half
    for size in 1..=half {
        for_each_subset(n, size, |subset| {
            let cut = count_cut_edges(graph, subset);
            let exp = cut as f64 / size as f64;
            if exp < min_expansion {
                min_expansion = exp;
            }
        });
    }
    if min_expansion.is_infinite() {
        0.0
    } else {
        min_expansion
    }
}

/// Iterate over all subsets of `{0..n}` with exactly `size` elements.
fn for_each_subset(n: usize, size: usize, mut f: impl FnMut(&[bool])) {
    let mut in_set = vec![false; n];
    enumerate_subsets(&mut in_set, 0, size, &mut f);
}

fn enumerate_subsets(
    in_set: &mut [bool],
    start: usize,
    remaining: usize,
    f: &mut impl FnMut(&[bool]),
) {
    if remaining == 0 {
        f(in_set);
        return;
    }
    let n = in_set.len();
    if start + remaining > n {
        return;
    }
    // Include start
    in_set[start] = true;
    enumerate_subsets(in_set, start + 1, remaining - 1, f);
    in_set[start] = false;
    // Exclude start
    enumerate_subsets(in_set, start + 1, remaining, f);
}

/// Count edges crossing the cut defined by `in_set`.
fn count_cut_edges(graph: &Graph, in_set: &[bool]) -> usize {
    graph
        .edges
        .iter()
        .filter(|&&(u, v)| {
            let u_in = in_set.get(u).copied().unwrap_or(false);
            let v_in = in_set.get(v).copied().unwrap_or(false);
            u_in != v_in
        })
        .count()
}

/// Sampling-based expansion estimate for larger graphs.
///
/// Tests single-vertex subsets and small random-ish subsets to get a
/// reasonable lower bound on expansion without exponential enumeration.
fn expansion_sampled(graph: &Graph) -> f64 {
    let n = graph.num_vertices;
    let mut min_expansion = f64::INFINITY;

    // Degree-based: check each single vertex
    let mut degree = vec![0usize; n];
    for &(u, v) in &graph.edges {
        if u < n {
            degree[u] += 1;
        }
        if v < n {
            degree[v] += 1;
        }
    }
    for d in &degree {
        let exp = *d as f64;
        if exp < min_expansion {
            min_expansion = exp;
        }
    }

    // Check pairs of adjacent vertices
    for &(u, v) in &graph.edges {
        let mut in_set = vec![false; n];
        in_set[u] = true;
        in_set[v] = true;
        let cut = count_cut_edges(graph, &in_set);
        let exp = cut as f64 / 2.0;
        if exp < min_expansion {
            min_expansion = exp;
        }
    }

    if min_expansion.is_infinite() {
        0.0
    } else {
        min_expansion
    }
}
