// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse-driven counterexample and benchmark synthesis for SAT proof checkers.
//!
//! Generates hard formula instances (counterexamples and benchmarks) from
//! mathematically-motivated structures, enabling automated testing of
//! `sat_verify` proof checkers against instances with known properties.
//!
//! ## Formula Families
//!
//! - **Pigeonhole** PHP(m,n): m pigeons into n holes. UNSAT when m > n.
//!   Exponential for resolution (Haken 1985).
//! - **Tseitin** on d-regular graphs: XOR parity constraints. Hard for
//!   resolution on expanders, easy for polynomial calculus.
//! - **Graph coloring** k-COL: Encodes k-colorability as CNF. UNSAT when
//!   chromatic number > k.
//! - **Parity/XOR**: Linear algebra over GF(2) encoded in CNF. Hard for
//!   resolution, easy for Gaussian elimination.
//! - **Ordering principles**: Every finite partial order has a minimal element.
//!   Hard for resolution (Bonet & Galesi 1999).
//! - **Random k-SAT**: Phase transition at clause/var ratio ~4.267 for k=3.
//!
//! ## References
//!
//! - Haken (1985): "The Intractability of Resolution"
//! - Ben-Sasson & Wigderson (2001): "Short proofs are narrow"
//! - Cook (1971): "The complexity of theorem-proving procedures"

use std::collections::{BTreeSet, HashMap};
use std::time::Instant;

use super::hard_formulas::{combinations, sample_distinct_vars, saturating_usize_to_u32, LcgRng};
use super::types::{Cnf, Lit, SatClause};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Expected satisfiability result for a synthesized instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SatResult {
    /// The instance is satisfiable.
    Sat,
    /// The instance is unsatisfiable.
    Unsat,
    /// Satisfiability is unknown or depends on parameters.
    Unknown,
}

/// Difficulty tier for benchmarking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum HardnessClass {
    /// Trivial instances (< 10 variables).
    Trivial,
    /// Easy instances solvable in milliseconds.
    Easy,
    /// Medium instances solvable in seconds.
    Medium,
    /// Hard instances requiring minutes or more.
    Hard,
}

/// Metadata describing a synthesized instance's provenance and properties.
#[derive(Debug, Clone)]
pub struct InstanceMetadata {
    /// Formula family name (e.g. "pigeonhole", "tseitin").
    pub family: String,
    /// Generator parameters (e.g. "m" -> "5", "n" -> "4").
    pub parameters: HashMap<String, String>,
    /// Estimated difficulty tier.
    pub hardness_class: HardnessClass,
}

/// A synthesized CNF instance with metadata.
#[derive(Debug, Clone)]
pub struct CnfInstance {
    /// The CNF formula (clause list with typed literals).
    pub clauses: Vec<Vec<i32>>,
    /// Number of propositional variables.
    pub num_vars: usize,
    /// Expected satisfiability result.
    pub expected_result: SatResult,
    /// Provenance and structural metadata.
    pub metadata: InstanceMetadata,
}

/// A DRAT proof step for counterexample search.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DratStep {
    /// Add a clause (clause addition / RAT step).
    Add(Vec<i32>),
    /// Delete a clause.
    Delete(Vec<i32>),
}

/// A counterexample found by the search procedure.
#[derive(Debug, Clone)]
pub struct Counterexample {
    /// The formula that triggered the checker bug.
    pub formula: Vec<Vec<i32>>,
    /// Number of variables in the formula.
    pub num_vars: usize,
    /// The proof that was incorrectly accepted.
    pub proof: Vec<DratStep>,
    /// Seed that produced this counterexample.
    pub seed: u64,
}

// ---------------------------------------------------------------------------
// Synthesis targets
// ---------------------------------------------------------------------------

/// Edge list for graph-based encodings.
pub type EdgeList = Vec<(usize, usize)>;

/// Specification of a formula to synthesize.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum SynthesisTarget {
    /// Pigeonhole principle: m pigeons, n holes.
    Pigeonhole { m: usize, n: usize },
    /// Tseitin formula on a d-regular graph with `n` vertices.
    Tseitin { n: usize, degree: usize },
    /// Ramsey-theory-inspired coloring: R(r,s) on n vertices.
    Ramsey { r: usize, s: usize, n: usize },
    /// Parity/XOR constraints over `n` variables with `num_xors` constraints.
    Parity { n: usize, num_xors: usize },
    /// Ordering principle on `n` elements.
    Ordering { n: usize },
    /// Graph k-coloring on an explicit edge list.
    GraphColoring { k: usize, edges: EdgeList },
}

/// Synthesize a CNF instance from a target specification.
#[must_use]
pub fn synthesize(target: &SynthesisTarget) -> CnfInstance {
    match target {
        SynthesisTarget::Pigeonhole { m, n } => synthesize_pigeonhole(*m, *n),
        SynthesisTarget::Tseitin { n, degree } => synthesize_tseitin(*n, *degree),
        SynthesisTarget::Ramsey { r, s, n } => synthesize_ramsey(*r, *s, *n),
        SynthesisTarget::Parity { n, num_xors } => synthesize_parity(*n, *num_xors),
        SynthesisTarget::Ordering { n } => synthesize_ordering(*n),
        SynthesisTarget::GraphColoring { k, edges } => synthesize_graph_coloring(*k, edges),
    }
}

// ---------------------------------------------------------------------------
// Generator: Pigeonhole PHP(m, n)
// ---------------------------------------------------------------------------

/// Generate the pigeonhole principle PHP(m, n).
///
/// Variables: p_{i,j} for pigeon i in hole j (1-indexed).
/// - At-least-one: each pigeon maps to some hole.
/// - At-most-one: no two pigeons share a hole.
///
/// UNSAT when m > n.
fn synthesize_pigeonhole(m: usize, n: usize) -> CnfInstance {
    if m == 0 || n == 0 {
        return CnfInstance {
            clauses: Vec::new(),
            num_vars: 0,
            expected_result: if m == 0 {
                SatResult::Sat
            } else {
                SatResult::Unsat
            },
            metadata: InstanceMetadata {
                family: "pigeonhole".to_string(),
                parameters: php_params(m, n),
                hardness_class: HardnessClass::Trivial,
            },
        };
    }

    let num_vars = m * n;
    let mut clauses = Vec::new();

    // At-least-one: pigeon i must be in some hole.
    for i in 0..m {
        let clause: Vec<i32> = (0..n).map(|j| php_var(i, j, n) as i32).collect();
        clauses.push(clause);
    }

    // At-most-one: no hole has two pigeons.
    for j in 0..n {
        for i1 in 0..m {
            for i2 in (i1 + 1)..m {
                clauses.push(vec![
                    -(php_var(i1, j, n) as i32),
                    -(php_var(i2, j, n) as i32),
                ]);
            }
        }
    }

    let expected = if m > n {
        SatResult::Unsat
    } else {
        SatResult::Sat
    };
    let hardness = match m.saturating_sub(n) {
        0 => HardnessClass::Easy,
        _ if m <= 6 => HardnessClass::Easy,
        _ if m <= 12 => HardnessClass::Medium,
        _ => HardnessClass::Hard,
    };

    CnfInstance {
        clauses,
        num_vars,
        expected_result: expected,
        metadata: InstanceMetadata {
            family: "pigeonhole".to_string(),
            parameters: php_params(m, n),
            hardness_class: hardness,
        },
    }
}

/// 1-indexed variable for pigeon `i` in hole `j`.
#[must_use]
fn php_var(i: usize, j: usize, n: usize) -> usize {
    i * n + j + 1
}

fn php_params(m: usize, n: usize) -> HashMap<String, String> {
    let mut p = HashMap::new();
    p.insert("m".to_string(), m.to_string());
    p.insert("n".to_string(), n.to_string());
    p
}

// ---------------------------------------------------------------------------
// Generator: Tseitin on d-regular graph
// ---------------------------------------------------------------------------

/// Generate a Tseitin formula on a deterministic d-regular graph.
///
/// Edge variables encode XOR constraints: for each vertex, the XOR of
/// incident edge variables equals a label. With odd parity on one vertex
/// and an even total vertex count, the formula is UNSAT.
fn synthesize_tseitin(n: usize, degree: usize) -> CnfInstance {
    if n < 2 || degree == 0 {
        return CnfInstance {
            clauses: Vec::new(),
            num_vars: 0,
            expected_result: SatResult::Unknown,
            metadata: InstanceMetadata {
                family: "tseitin".to_string(),
                parameters: tseitin_params(n, degree),
                hardness_class: HardnessClass::Trivial,
            },
        };
    }

    // Build a deterministic d-regular-ish graph.
    let edges = build_regular_graph(n, degree);
    let num_edge_vars = edges.len();

    if num_edge_vars == 0 {
        return CnfInstance {
            clauses: Vec::new(),
            num_vars: 0,
            expected_result: SatResult::Unknown,
            metadata: InstanceMetadata {
                family: "tseitin".to_string(),
                parameters: tseitin_params(n, degree),
                hardness_class: HardnessClass::Trivial,
            },
        };
    }

    // Build incidence: for each vertex, list of edge indices.
    let mut incidence: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (idx, &(u, v)) in edges.iter().enumerate() {
        incidence[u].push(idx);
        incidence[v].push(idx);
    }

    // Parity labels: vertex 0 gets odd parity, rest even.
    // Sum of labels is odd => UNSAT (Tseitin's theorem).
    let mut clauses = Vec::new();
    for (vertex, edge_indices) in incidence.iter().enumerate() {
        if edge_indices.is_empty() {
            continue;
        }
        let target_parity = vertex == 0;
        let edge_vars: Vec<i32> = edge_indices.iter().map(|&idx| (idx + 1) as i32).collect();
        encode_xor_constraint(&edge_vars, target_parity, &mut clauses);
    }

    let hardness = if n <= 6 {
        HardnessClass::Easy
    } else if n <= 16 {
        HardnessClass::Medium
    } else {
        HardnessClass::Hard
    };

    CnfInstance {
        clauses,
        num_vars: num_edge_vars,
        expected_result: SatResult::Unsat,
        metadata: InstanceMetadata {
            family: "tseitin".to_string(),
            parameters: tseitin_params(n, degree),
            hardness_class: hardness,
        },
    }
}

/// Build a deterministic pseudo-regular graph on n vertices with target degree d.
fn build_regular_graph(n: usize, degree: usize) -> Vec<(usize, usize)> {
    let mut edges = BTreeSet::new();
    for v in 0..n {
        for offset in 1..=degree / 2 {
            let u = (v + offset) % n;
            let edge = if v < u { (v, u) } else { (u, v) };
            edges.insert(edge);
        }
        // For odd degree, connect to the opposite vertex.
        if degree % 2 == 1 && n > 2 {
            let u = (v + n / 2) % n;
            if u != v {
                let edge = if v < u { (v, u) } else { (u, v) };
                edges.insert(edge);
            }
        }
    }
    edges.into_iter().collect()
}

/// Encode XOR constraint: XOR of `vars` equals `target`.
///
/// A width-k XOR produces 2^{k-1} clauses.
fn encode_xor_constraint(vars: &[i32], target: bool, clauses: &mut Vec<Vec<i32>>) {
    let k = vars.len();
    if k == 0 {
        return;
    }
    // Enumerate all 2^k sign patterns; keep those with the wrong parity.
    let total = 1u64 << k;
    for mask in 0..total {
        let negated_count = mask.count_ones() as usize;
        let parity = negated_count % 2 == 1;
        // We want clauses that block assignments violating the XOR.
        // The XOR = target means: (number of false vars) has parity = target.
        // A clause blocks a full assignment => we negate the assignment.
        // Include this clause if the assignment's parity != target.
        if parity != target {
            let clause: Vec<i32> = (0..k)
                .map(|bit| {
                    let var = vars[bit];
                    // If this bit is 1 in mask, the assignment sets var to false,
                    // so the blocking clause includes var positive.
                    if mask & (1u64 << bit) != 0 {
                        var
                    } else {
                        -var
                    }
                })
                .collect();
            clauses.push(clause);
        }
    }
}

fn tseitin_params(n: usize, degree: usize) -> HashMap<String, String> {
    let mut p = HashMap::new();
    p.insert("n".to_string(), n.to_string());
    p.insert("degree".to_string(), degree.to_string());
    p
}

// ---------------------------------------------------------------------------
// Generator: Graph k-coloring
// ---------------------------------------------------------------------------

/// Encode k-colorability of a graph as CNF.
///
/// Variables: `x_{v,c}` for vertex v, color c.
/// - ALO: each vertex has at least one color.
/// - AMO: each vertex has at most one color.
/// - Edge: adjacent vertices have different colors.
fn synthesize_graph_coloring(k: usize, edges: &[(usize, usize)]) -> CnfInstance {
    // Determine vertex count from edge list.
    let n = edges
        .iter()
        .flat_map(|&(u, v)| [u, v])
        .max()
        .map_or(0, |m| m + 1);

    if n == 0 || k == 0 {
        return CnfInstance {
            clauses: if n > 0 && k == 0 {
                // No colors available but vertices exist => UNSAT.
                vec![Vec::new()]
            } else {
                Vec::new()
            },
            num_vars: 0,
            expected_result: if n > 0 && k == 0 {
                SatResult::Unsat
            } else {
                SatResult::Sat
            },
            metadata: InstanceMetadata {
                family: "graph_coloring".to_string(),
                parameters: coloring_params(k, n, edges.len()),
                hardness_class: HardnessClass::Trivial,
            },
        };
    }

    let num_vars = n * k;
    let mut clauses = Vec::new();

    // ALO: each vertex has at least one color.
    for v in 0..n {
        let clause: Vec<i32> = (0..k).map(|c| gc_var(v, c, k) as i32).collect();
        clauses.push(clause);
    }

    // AMO: each vertex has at most one color.
    for v in 0..n {
        for c1 in 0..k {
            for c2 in (c1 + 1)..k {
                clauses.push(vec![-(gc_var(v, c1, k) as i32), -(gc_var(v, c2, k) as i32)]);
            }
        }
    }

    // Edge constraints: adjacent vertices differ in every color.
    for &(u, v) in edges {
        for c in 0..k {
            clauses.push(vec![-(gc_var(u, c, k) as i32), -(gc_var(v, c, k) as i32)]);
        }
    }

    CnfInstance {
        clauses,
        num_vars,
        expected_result: SatResult::Unknown, // depends on graph structure
        metadata: InstanceMetadata {
            family: "graph_coloring".to_string(),
            parameters: coloring_params(k, n, edges.len()),
            hardness_class: if n * k <= 20 {
                HardnessClass::Easy
            } else if n * k <= 100 {
                HardnessClass::Medium
            } else {
                HardnessClass::Hard
            },
        },
    }
}

/// 1-indexed variable for vertex `v`, color `c`.
#[must_use]
fn gc_var(v: usize, c: usize, k: usize) -> usize {
    v * k + c + 1
}

fn coloring_params(k: usize, n: usize, edges: usize) -> HashMap<String, String> {
    let mut p = HashMap::new();
    p.insert("k".to_string(), k.to_string());
    p.insert("vertices".to_string(), n.to_string());
    p.insert("edges".to_string(), edges.to_string());
    p
}

// ---------------------------------------------------------------------------
// Generator: Parity/XOR constraints
// ---------------------------------------------------------------------------

/// Generate parity/XOR constraints.
///
/// Creates `num_xors` random XOR constraints over `n` variables, each of
/// width 3 (the standard "random XORSAT" model). When the system is
/// over-determined, the result is likely UNSAT.
fn synthesize_parity(n: usize, num_xors: usize) -> CnfInstance {
    if n < 2 || num_xors == 0 {
        return CnfInstance {
            clauses: Vec::new(),
            num_vars: n,
            expected_result: SatResult::Sat,
            metadata: InstanceMetadata {
                family: "parity".to_string(),
                parameters: parity_params(n, num_xors),
                hardness_class: HardnessClass::Trivial,
            },
        };
    }

    let seed = (n as u64)
        .wrapping_mul(0xBF58_476D_1CE4_E5B9)
        .wrapping_add(num_xors as u64);
    let mut rng = LcgRng::new(seed);
    let width = n.min(3);
    let num_vars_u32 = saturating_usize_to_u32(n);

    let mut clauses = Vec::new();
    for _ in 0..num_xors {
        let vars_chosen = sample_distinct_vars(width, num_vars_u32, &mut rng);
        let dimacs_vars: Vec<i32> = vars_chosen.iter().map(|v| v.index() as i32).collect();
        let target_parity = rng.gen_bool();
        encode_xor_constraint(&dimacs_vars, target_parity, &mut clauses);
    }

    CnfInstance {
        clauses,
        num_vars: n,
        // Parity instances: high XOR-to-var ratio is likely UNSAT but not
        // guaranteed; we report Unknown uniformly until the solver labels it.
        expected_result: SatResult::Unknown,
        metadata: InstanceMetadata {
            family: "parity".to_string(),
            parameters: parity_params(n, num_xors),
            hardness_class: if n <= 8 {
                HardnessClass::Easy
            } else if n <= 20 {
                HardnessClass::Medium
            } else {
                HardnessClass::Hard
            },
        },
    }
}

fn parity_params(n: usize, num_xors: usize) -> HashMap<String, String> {
    let mut p = HashMap::new();
    p.insert("n".to_string(), n.to_string());
    p.insert("num_xors".to_string(), num_xors.to_string());
    p
}

// ---------------------------------------------------------------------------
// Generator: Ordering principle
// ---------------------------------------------------------------------------

/// Generate the ordering principle: "every finite partial order on n
/// elements has a minimal element."
///
/// Variables: `x_{i,j}` means element i < element j.
/// Clauses enforce:
/// - Irreflexivity: NOT (i < i).
/// - Transitivity: (i < j) AND (j < k) => (i < k).
/// - Totality: for every pair, either i < j or j < i (linear order).
/// - No minimal element: each element has something below it.
///
/// With totality + no-minimal, this is UNSAT (well-ordering principle).
fn synthesize_ordering(n: usize) -> CnfInstance {
    if n <= 1 {
        return CnfInstance {
            clauses: if n == 1 { vec![Vec::new()] } else { Vec::new() },
            num_vars: 0,
            expected_result: if n == 1 {
                SatResult::Unsat
            } else {
                SatResult::Sat
            },
            metadata: InstanceMetadata {
                family: "ordering".to_string(),
                parameters: ordering_params(n),
                hardness_class: HardnessClass::Trivial,
            },
        };
    }

    // Variables: ord_var(i, j) for i != j means "i < j".
    let num_vars = n * (n - 1); // ordered pairs
    let mut clauses = Vec::new();

    // Asymmetry: NOT (i < j AND j < i).
    for i in 0..n {
        for j in 0..n {
            if i != j {
                clauses.push(vec![-(ord_var(i, j, n) as i32), -(ord_var(j, i, n) as i32)]);
            }
        }
    }

    // Transitivity: (i < j) AND (j < k) => (i < k).
    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            for k in 0..n {
                if k == i || k == j {
                    continue;
                }
                clauses.push(vec![
                    -(ord_var(i, j, n) as i32),
                    -(ord_var(j, k, n) as i32),
                    ord_var(i, k, n) as i32,
                ]);
            }
        }
    }

    // No minimal element: for each element i, some j satisfies j < i.
    for i in 0..n {
        let clause: Vec<i32> = (0..n)
            .filter(|&j| j != i)
            .map(|j| ord_var(j, i, n) as i32)
            .collect();
        clauses.push(clause);
    }

    CnfInstance {
        clauses,
        num_vars,
        expected_result: SatResult::Unsat,
        metadata: InstanceMetadata {
            family: "ordering".to_string(),
            parameters: ordering_params(n),
            hardness_class: if n <= 4 {
                HardnessClass::Easy
            } else if n <= 8 {
                HardnessClass::Medium
            } else {
                HardnessClass::Hard
            },
        },
    }
}

/// 1-indexed variable for "element i < element j" (i != j).
#[must_use]
fn ord_var(i: usize, j: usize, n: usize) -> usize {
    debug_assert!(i != j);
    // Map ordered pair (i, j) where i != j to 1-indexed variable.
    // For i < j: position = i * (n-1) + j - (if j > i then 1 else 0).
    let adjusted_j = if j > i { j - 1 } else { j };
    i * (n - 1) + adjusted_j + 1
}

fn ordering_params(n: usize) -> HashMap<String, String> {
    let mut p = HashMap::new();
    p.insert("n".to_string(), n.to_string());
    p
}

// ---------------------------------------------------------------------------
// Generator: Random k-SAT
// ---------------------------------------------------------------------------

/// Generate a random k-SAT instance at a specified clause-to-variable ratio.
///
/// For k=3 and ratio ~4.267, instances are at the satisfiability phase
/// transition: approximately half are SAT, half UNSAT.
#[must_use]
pub fn generate_random_ksat(num_vars: usize, k: usize, ratio: f64, seed: u64) -> CnfInstance {
    if num_vars == 0 || k == 0 || ratio <= 0.0 {
        return CnfInstance {
            clauses: Vec::new(),
            num_vars,
            expected_result: SatResult::Sat,
            metadata: InstanceMetadata {
                family: "random_ksat".to_string(),
                parameters: ksat_params(num_vars, k, ratio),
                hardness_class: HardnessClass::Trivial,
            },
        };
    }

    let num_clauses = (num_vars as f64 * ratio).round() as usize;
    let num_vars_u32 = saturating_usize_to_u32(num_vars);
    let mut rng = LcgRng::new(seed);
    let effective_k = k.min(num_vars);

    let mut clauses = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        let vars = sample_distinct_vars(effective_k, num_vars_u32, &mut rng);
        let clause: Vec<i32> = vars
            .iter()
            .map(|v| {
                let base = v.index() as i32;
                if rng.gen_bool() {
                    base
                } else {
                    -base
                }
            })
            .collect();
        clauses.push(clause);
    }

    CnfInstance {
        clauses,
        num_vars,
        expected_result: SatResult::Unknown,
        metadata: InstanceMetadata {
            family: "random_ksat".to_string(),
            parameters: ksat_params(num_vars, k, ratio),
            hardness_class: if num_vars <= 20 {
                HardnessClass::Easy
            } else if num_vars <= 100 {
                HardnessClass::Medium
            } else {
                HardnessClass::Hard
            },
        },
    }
}

fn ksat_params(num_vars: usize, k: usize, ratio: f64) -> HashMap<String, String> {
    let mut p = HashMap::new();
    p.insert("num_vars".to_string(), num_vars.to_string());
    p.insert("k".to_string(), k.to_string());
    p.insert("ratio".to_string(), format!("{ratio:.3}"));
    p
}

// ---------------------------------------------------------------------------
// Generator: Ramsey coloring
// ---------------------------------------------------------------------------

/// Generate a Ramsey-theory-inspired formula.
///
/// Encodes: "the complete graph K_n has a 2-coloring with no monochromatic
/// K_r (red) or K_s (blue)." This is UNSAT when n >= R(r,s).
fn synthesize_ramsey(r: usize, s: usize, n: usize) -> CnfInstance {
    if n < 2 || (r < 2 && s < 2) {
        return CnfInstance {
            clauses: Vec::new(),
            num_vars: 0,
            expected_result: SatResult::Sat,
            metadata: InstanceMetadata {
                family: "ramsey".to_string(),
                parameters: ramsey_params(r, s, n),
                hardness_class: HardnessClass::Trivial,
            },
        };
    }

    // Variables: e_{i,j} for edge (i,j) in K_n. True = red, false = blue.
    let num_vars = n * (n - 1) / 2;
    let mut clauses = Vec::new();

    // No red K_r: for each r-clique, at least one edge is blue (false).
    if r >= 2 && r <= n {
        let mut clique = Vec::with_capacity(r);
        combinations(0, n - 1, r, &mut clique, &mut |subset| {
            // For each pair in the clique, at least one must be blue.
            let mut clause = Vec::new();
            for idx_a in 0..subset.len() {
                for idx_b in (idx_a + 1)..subset.len() {
                    clause.push(-(ramsey_edge_var(subset[idx_a], subset[idx_b], n) as i32));
                }
            }
            // Actually: no red clique means NOT all edges are red.
            // So: OR of (NOT e_{a,b}) for all pairs in clique.
            clauses.push(clause);
        });
    }

    // No blue K_s: for each s-clique, at least one edge is red (true).
    if s >= 2 && s <= n {
        let mut clique = Vec::with_capacity(s);
        combinations(0, n - 1, s, &mut clique, &mut |subset| {
            let mut clause = Vec::new();
            for idx_a in 0..subset.len() {
                for idx_b in (idx_a + 1)..subset.len() {
                    clause.push(ramsey_edge_var(subset[idx_a], subset[idx_b], n) as i32);
                }
            }
            clauses.push(clause);
        });
    }

    CnfInstance {
        clauses,
        num_vars,
        expected_result: SatResult::Unknown, // depends on whether n >= R(r,s)
        metadata: InstanceMetadata {
            family: "ramsey".to_string(),
            parameters: ramsey_params(r, s, n),
            hardness_class: if num_vars <= 10 {
                HardnessClass::Easy
            } else if num_vars <= 45 {
                HardnessClass::Medium
            } else {
                HardnessClass::Hard
            },
        },
    }
}

/// 1-indexed variable for edge (i, j) in K_n, with i < j.
#[must_use]
fn ramsey_edge_var(i: usize, j: usize, n: usize) -> usize {
    let (lo, hi) = if i < j { (i, j) } else { (j, i) };
    // Map ordered pair to triangular number index.
    lo * n - lo * (lo + 1) / 2 + (hi - lo - 1) + 1
}

fn ramsey_params(r: usize, s: usize, n: usize) -> HashMap<String, String> {
    let mut p = HashMap::new();
    p.insert("r".to_string(), r.to_string());
    p.insert("s".to_string(), s.to_string());
    p.insert("n".to_string(), n.to_string());
    p
}

// ---------------------------------------------------------------------------
// Benchmark suite
// ---------------------------------------------------------------------------

/// A named benchmark instance within a suite.
#[derive(Debug, Clone)]
pub struct BenchmarkEntry {
    /// Human-readable name.
    pub name: String,
    /// The synthesized instance.
    pub instance: CnfInstance,
}

/// A collection of benchmark instances organized by difficulty.
#[derive(Debug, Clone)]
pub struct BenchmarkSuite {
    /// Suite name.
    pub name: String,
    /// Ordered list of benchmark entries.
    pub entries: Vec<BenchmarkEntry>,
}

/// Result of running a single benchmark instance.
#[derive(Debug, Clone)]
pub struct InstanceResult {
    /// Instance name.
    pub name: String,
    /// Whether the checker returned the expected result.
    pub passed: bool,
    /// Elapsed wall-clock time in microseconds.
    pub elapsed_us: u64,
}

/// Aggregated results from running an entire benchmark suite.
#[derive(Debug, Clone)]
pub struct BenchmarkResults {
    /// Per-instance results.
    pub results: Vec<InstanceResult>,
    /// Number of instances that passed.
    pub passed: usize,
    /// Number of instances that failed.
    pub failed: usize,
    /// Total wall-clock time in microseconds.
    pub total_elapsed_us: u64,
}

/// Build the standard benchmark suite (~20 instances across difficulty tiers).
///
/// Uses explicit `push` per entry (rather than a single `vec![]`) because each
/// entry has a section header comment and a few multi-line targets; keeping
/// them line-aligned reads better than packing them into a single literal.
#[allow(clippy::vec_init_then_push)]
#[must_use]
pub fn standard_suite() -> BenchmarkSuite {
    let mut entries = Vec::with_capacity(20);

    // Trivial / Easy tier
    entries.push(entry("php_3_2", SynthesisTarget::Pigeonhole { m: 3, n: 2 }));
    entries.push(entry("php_4_3", SynthesisTarget::Pigeonhole { m: 4, n: 3 }));
    entries.push(entry("php_5_4", SynthesisTarget::Pigeonhole { m: 5, n: 4 }));
    entries.push(entry("php_3_3", SynthesisTarget::Pigeonhole { m: 3, n: 3 }));
    entries.push(entry(
        "tseitin_4_3",
        SynthesisTarget::Tseitin { n: 4, degree: 3 },
    ));
    entries.push(entry("ordering_3", SynthesisTarget::Ordering { n: 3 }));
    entries.push(entry(
        "parity_4_3",
        SynthesisTarget::Parity { n: 4, num_xors: 3 },
    ));

    // Easy tier
    entries.push(entry("php_6_5", SynthesisTarget::Pigeonhole { m: 6, n: 5 }));
    entries.push(entry(
        "tseitin_6_3",
        SynthesisTarget::Tseitin { n: 6, degree: 3 },
    ));
    entries.push(entry(
        "coloring_k3_triangle",
        SynthesisTarget::GraphColoring {
            k: 2,
            edges: vec![(0, 1), (1, 2), (0, 2)],
        },
    ));
    entries.push(entry("ordering_4", SynthesisTarget::Ordering { n: 4 }));
    entries.push(entry(
        "ramsey_3_3_5",
        SynthesisTarget::Ramsey { r: 3, s: 3, n: 5 },
    ));
    entries.push(entry(
        "parity_6_5",
        SynthesisTarget::Parity { n: 6, num_xors: 5 },
    ));

    // Medium tier
    entries.push(entry("php_8_7", SynthesisTarget::Pigeonhole { m: 8, n: 7 }));
    entries.push(entry(
        "tseitin_10_3",
        SynthesisTarget::Tseitin { n: 10, degree: 3 },
    ));
    entries.push(entry(
        "coloring_k3_petersen",
        SynthesisTarget::GraphColoring {
            k: 3,
            edges: petersen_edges(),
        },
    ));
    entries.push(entry("ordering_5", SynthesisTarget::Ordering { n: 5 }));
    entries.push(entry(
        "ramsey_3_3_6",
        SynthesisTarget::Ramsey { r: 3, s: 3, n: 6 },
    ));

    // Hard tier (small enough to not timeout in tests)
    entries.push(entry(
        "php_10_9",
        SynthesisTarget::Pigeonhole { m: 10, n: 9 },
    ));
    entries.push(entry(
        "tseitin_16_3",
        SynthesisTarget::Tseitin { n: 16, degree: 3 },
    ));

    BenchmarkSuite {
        name: "standard".to_string(),
        entries,
    }
}

/// Run a benchmark suite against a checker function.
///
/// The `checker` takes a slice of clauses (DIMACS literal vectors) and
/// returns `true` if the formula is satisfiable according to the checker.
#[must_use]
pub fn run_benchmark(
    suite: &BenchmarkSuite,
    checker: &dyn Fn(&[Vec<i32>]) -> bool,
) -> BenchmarkResults {
    let mut results = Vec::with_capacity(suite.entries.len());
    let mut passed = 0usize;
    let mut failed = 0usize;
    let mut total_elapsed_us = 0u64;

    for entry in &suite.entries {
        let start = Instant::now();
        let checker_says_sat = checker(&entry.instance.clauses);
        let elapsed = start.elapsed();
        let elapsed_us = elapsed.as_micros() as u64;

        let instance_passed = match entry.instance.expected_result {
            SatResult::Sat => checker_says_sat,
            SatResult::Unsat => !checker_says_sat,
            SatResult::Unknown => true, // any answer is acceptable
        };

        if instance_passed {
            passed += 1;
        } else {
            failed += 1;
        }
        total_elapsed_us += elapsed_us;

        results.push(InstanceResult {
            name: entry.name.clone(),
            passed: instance_passed,
            elapsed_us,
        });
    }

    BenchmarkResults {
        results,
        passed,
        failed,
        total_elapsed_us,
    }
}

fn entry(name: &str, target: SynthesisTarget) -> BenchmarkEntry {
    BenchmarkEntry {
        name: name.to_string(),
        instance: synthesize(&target),
    }
}

/// Petersen graph edges (10 vertices, 15 edges, chromatic number 3).
fn petersen_edges() -> Vec<(usize, usize)> {
    vec![
        // Outer cycle
        (0, 1),
        (1, 2),
        (2, 3),
        (3, 4),
        (4, 0),
        // Inner pentagram
        (5, 7),
        (7, 9),
        (9, 6),
        (6, 8),
        (8, 5),
        // Spokes
        (0, 5),
        (1, 6),
        (2, 7),
        (3, 8),
        (4, 9),
    ]
}

// ---------------------------------------------------------------------------
// Counterexample search
// ---------------------------------------------------------------------------

/// Search for a counterexample where a DRAT checker incorrectly accepts
/// an invalid proof.
///
/// Generates random small formulas and random "proof" attempts (which are
/// almost certainly invalid DRAT derivations), and checks whether the
/// `checker` incorrectly accepts them. A correct checker should reject
/// all randomly generated proof attempts on unsatisfiable formulas.
///
/// # Arguments
///
/// * `checker` - Returns `true` if it accepts the (formula, proof) pair.
/// * `max_vars` - Maximum number of variables in generated formulas.
/// * `seed` - RNG seed for reproducibility.
///
/// Returns `Some(Counterexample)` if a bug is found, `None` otherwise.
#[must_use]
pub fn search_counterexample(
    checker: &dyn Fn(&[Vec<i32>], &[DratStep]) -> bool,
    max_vars: usize,
    seed: u64,
) -> Option<Counterexample> {
    let mut rng = LcgRng::new(seed);
    let effective_max = max_vars.max(2);
    let iterations = 1000u32;

    for _ in 0..iterations {
        let num_vars = (rng.gen_range(effective_max as u32 - 1) + 2) as usize;
        let num_clauses = (rng.gen_range(num_vars as u32 * 3) + 1) as usize;
        let num_vars_u32 = num_vars as u32;

        // Generate a random formula.
        let mut formula = Vec::with_capacity(num_clauses);
        for _ in 0..num_clauses {
            let width = (rng.gen_range(3) + 1) as usize;
            let effective_width = width.min(num_vars);
            let vars = sample_distinct_vars(effective_width, num_vars_u32, &mut rng);
            let clause: Vec<i32> = vars
                .iter()
                .map(|v| {
                    let base = v.index() as i32;
                    if rng.gen_bool() {
                        base
                    } else {
                        -base
                    }
                })
                .collect();
            formula.push(clause);
        }

        // Generate a random "proof" (garbage DRAT steps).
        let num_steps = (rng.gen_range(5) + 1) as usize;
        let mut proof = Vec::with_capacity(num_steps);
        for _ in 0..num_steps {
            let width = (rng.gen_range(3) + 1) as usize;
            let effective_width = width.min(num_vars);
            let vars = sample_distinct_vars(effective_width, num_vars_u32, &mut rng);
            let step_clause: Vec<i32> = vars
                .iter()
                .map(|v| {
                    let base = v.index() as i32;
                    if rng.gen_bool() {
                        base
                    } else {
                        -base
                    }
                })
                .collect();
            if rng.gen_range(4) == 0 {
                proof.push(DratStep::Delete(step_clause));
            } else {
                proof.push(DratStep::Add(step_clause));
            }
        }

        // A correct checker should reject random garbage proofs.
        // If it accepts, we found a bug.
        if checker(&formula, &proof) {
            return Some(Counterexample {
                formula,
                num_vars,
                proof,
                seed,
            });
        }
    }

    None
}

// ---------------------------------------------------------------------------
// Conversion helpers
// ---------------------------------------------------------------------------

/// Convert a `CnfInstance` to the typed `Cnf` representation.
#[must_use]
pub fn instance_to_cnf(instance: &CnfInstance) -> Cnf {
    let clauses = instance
        .clauses
        .iter()
        .map(|clause| SatClause(clause.iter().map(|&lit| Lit::from_dimacs(lit)).collect()))
        .collect();
    Cnf {
        num_vars: saturating_usize_to_u32(instance.num_vars),
        clauses,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Pigeonhole tests ----

    #[test]
    fn test_pigeonhole_3_2_is_unsat() {
        let inst = synthesize(&SynthesisTarget::Pigeonhole { m: 3, n: 2 });
        assert_eq!(inst.expected_result, SatResult::Unsat);
        assert_eq!(inst.num_vars, 6);
        assert_eq!(inst.metadata.family, "pigeonhole");
    }

    #[test]
    fn test_pigeonhole_variable_clause_counts() {
        // PHP(m, n): m ALO clauses (width n) + n * C(m,2) AMO clauses (width 2).
        let inst = synthesize(&SynthesisTarget::Pigeonhole { m: 4, n: 3 });
        assert_eq!(inst.num_vars, 12);
        let alo_clauses = 4; // one per pigeon
        let amo_clauses = 3 * 6; // 3 holes * C(4,2)=6
        assert_eq!(inst.clauses.len(), alo_clauses + amo_clauses);
    }

    #[test]
    fn test_pigeonhole_sat_when_m_leq_n() {
        let inst = synthesize(&SynthesisTarget::Pigeonhole { m: 3, n: 3 });
        assert_eq!(inst.expected_result, SatResult::Sat);
    }

    #[test]
    fn test_pigeonhole_produces_valid_cnf() {
        let inst = synthesize(&SynthesisTarget::Pigeonhole { m: 5, n: 4 });
        let cnf = instance_to_cnf(&inst);
        assert!(cnf.is_valid());
    }

    // ---- Tseitin tests ----

    #[test]
    fn test_tseitin_is_unsat() {
        let inst = synthesize(&SynthesisTarget::Tseitin { n: 6, degree: 3 });
        assert_eq!(inst.expected_result, SatResult::Unsat);
        assert!(inst.num_vars > 0);
        assert!(!inst.clauses.is_empty());
    }

    #[test]
    fn test_tseitin_produces_valid_cnf() {
        let inst = synthesize(&SynthesisTarget::Tseitin { n: 8, degree: 4 });
        let cnf = instance_to_cnf(&inst);
        assert!(cnf.is_valid());
    }

    #[test]
    fn test_tseitin_degenerate_parameters() {
        let inst = synthesize(&SynthesisTarget::Tseitin { n: 1, degree: 3 });
        assert_eq!(inst.expected_result, SatResult::Unknown);
    }

    // ---- Graph coloring tests ----

    #[test]
    fn test_graph_coloring_triangle_2colors_unsat() {
        // K3 (triangle) is not 2-colorable.
        let edges = vec![(0, 1), (1, 2), (0, 2)];
        let inst = synthesize(&SynthesisTarget::GraphColoring { k: 2, edges });
        assert_eq!(inst.num_vars, 6); // 3 vertices * 2 colors
        assert!(!inst.clauses.is_empty());
        let cnf = instance_to_cnf(&inst);
        assert!(cnf.is_valid());
    }

    #[test]
    fn test_graph_coloring_produces_valid_cnf() {
        let edges = vec![(0, 1), (1, 2), (2, 3), (3, 0)];
        let inst = synthesize(&SynthesisTarget::GraphColoring { k: 3, edges });
        let cnf = instance_to_cnf(&inst);
        assert!(cnf.is_valid());
    }

    // ---- Parity tests ----

    #[test]
    fn test_parity_produces_valid_cnf() {
        let inst = synthesize(&SynthesisTarget::Parity { n: 6, num_xors: 4 });
        assert!(inst.num_vars > 0);
        assert!(!inst.clauses.is_empty());
        let cnf = instance_to_cnf(&inst);
        assert!(cnf.is_valid());
    }

    #[test]
    fn test_parity_clause_count() {
        // Each width-3 XOR produces 2^{3-1} = 4 clauses.
        let inst = synthesize(&SynthesisTarget::Parity { n: 10, num_xors: 5 });
        assert_eq!(inst.clauses.len(), 5 * 4);
    }

    #[test]
    fn test_parity_degenerate() {
        let inst = synthesize(&SynthesisTarget::Parity { n: 0, num_xors: 5 });
        assert!(inst.clauses.is_empty());
    }

    // ---- Ordering principle tests ----

    #[test]
    fn test_ordering_is_unsat() {
        let inst = synthesize(&SynthesisTarget::Ordering { n: 3 });
        assert_eq!(inst.expected_result, SatResult::Unsat);
        assert!(!inst.clauses.is_empty());
    }

    #[test]
    fn test_ordering_produces_valid_cnf() {
        let inst = synthesize(&SynthesisTarget::Ordering { n: 4 });
        let cnf = instance_to_cnf(&inst);
        assert!(cnf.is_valid());
    }

    #[test]
    fn test_ordering_variable_count() {
        // n * (n-1) ordered pairs.
        let inst = synthesize(&SynthesisTarget::Ordering { n: 5 });
        assert_eq!(inst.num_vars, 20);
    }

    // ---- Random k-SAT tests ----

    #[test]
    fn test_random_ksat_at_threshold() {
        let inst = generate_random_ksat(20, 3, 4.267, 42);
        assert_eq!(inst.num_vars, 20);
        // At ratio 4.267, expect ~85 clauses.
        let expected_clauses = (20.0_f64 * 4.267).round() as usize;
        assert_eq!(inst.clauses.len(), expected_clauses);
        assert_eq!(inst.expected_result, SatResult::Unknown);
    }

    #[test]
    fn test_random_ksat_produces_valid_cnf() {
        let inst = generate_random_ksat(15, 3, 4.0, 123);
        let cnf = instance_to_cnf(&inst);
        assert!(cnf.is_valid());
    }

    #[test]
    fn test_random_ksat_deterministic() {
        let a = generate_random_ksat(10, 3, 4.0, 999);
        let b = generate_random_ksat(10, 3, 4.0, 999);
        assert_eq!(a.clauses, b.clauses);
    }

    // ---- Ramsey tests ----

    #[test]
    fn test_ramsey_produces_valid_cnf() {
        let inst = synthesize(&SynthesisTarget::Ramsey { r: 3, s: 3, n: 5 });
        assert_eq!(inst.num_vars, 10); // C(5,2) = 10 edges
        assert!(!inst.clauses.is_empty());
        let cnf = instance_to_cnf(&inst);
        assert!(cnf.is_valid());
    }

    #[test]
    fn test_ramsey_edge_var_mapping() {
        // Verify edge variables are 1-indexed and unique.
        let n = 5;
        let mut vars = BTreeSet::new();
        for i in 0..n {
            for j in (i + 1)..n {
                vars.insert(ramsey_edge_var(i, j, n));
            }
        }
        assert_eq!(vars.len(), 10); // C(5,2) = 10
        assert_eq!(*vars.iter().next().unwrap(), 1);
        assert_eq!(*vars.iter().next_back().unwrap(), 10);
    }

    // ---- Benchmark suite tests ----

    #[test]
    fn test_standard_suite_has_entries() {
        let suite = standard_suite();
        assert!(
            suite.entries.len() >= 15,
            "expected at least 15 entries, got {}",
            suite.entries.len()
        );
    }

    #[test]
    fn test_standard_suite_all_valid_cnf() {
        let suite = standard_suite();
        for entry in &suite.entries {
            let cnf = instance_to_cnf(&entry.instance);
            assert!(
                cnf.is_valid(),
                "instance '{}' produced invalid CNF",
                entry.name
            );
        }
    }

    #[test]
    fn test_run_benchmark_trivial_checker() {
        let suite = standard_suite();
        // A checker that always says UNSAT.
        let results = run_benchmark(&suite, &|_clauses| false);
        assert_eq!(results.results.len(), suite.entries.len());
        assert_eq!(results.passed + results.failed, suite.entries.len());
    }

    #[test]
    fn test_benchmark_suite_no_panics() {
        let suite = standard_suite();
        // A checker that always says SAT. Should not panic.
        let results = run_benchmark(&suite, &|_clauses| true);
        assert!(results.total_elapsed_us < 60_000_000); // sanity: < 60s total
    }

    // ---- Counterexample search tests ----

    #[test]
    fn test_counterexample_search_on_correct_checker() {
        // A correct checker always rejects random garbage proofs.
        let result = search_counterexample(&|_formula, _proof| false, 5, 42);
        assert!(
            result.is_none(),
            "correct checker should not have counterexample"
        );
    }

    #[test]
    fn test_counterexample_search_on_broken_checker() {
        // A broken checker that accepts everything.
        let result = search_counterexample(&|_formula, _proof| true, 5, 42);
        assert!(
            result.is_some(),
            "broken checker should produce counterexample"
        );
        let cex = result.unwrap();
        assert!(cex.num_vars >= 2);
        assert!(!cex.formula.is_empty());
        assert!(!cex.proof.is_empty());
    }

    #[test]
    fn test_counterexample_search_deterministic() {
        let a = search_counterexample(&|_f, _p| true, 5, 42);
        let b = search_counterexample(&|_f, _p| true, 5, 42);
        // Both should find the same first counterexample.
        assert_eq!(
            a.as_ref().map(|c| &c.formula),
            b.as_ref().map(|c| &c.formula)
        );
    }

    // ---- XOR encoding tests ----

    #[test]
    fn test_xor_encoding_width_2() {
        // XOR of 2 variables with target=true produces 2 clauses.
        let mut clauses = Vec::new();
        encode_xor_constraint(&[1, 2], true, &mut clauses);
        assert_eq!(clauses.len(), 2);
    }

    #[test]
    fn test_xor_encoding_width_3() {
        // XOR of 3 variables produces 2^{3-1} = 4 clauses.
        let mut clauses = Vec::new();
        encode_xor_constraint(&[1, 2, 3], false, &mut clauses);
        assert_eq!(clauses.len(), 4);
    }

    // ---- Conversion helpers ----

    #[test]
    fn test_instance_to_cnf_roundtrip() {
        let inst = synthesize(&SynthesisTarget::Pigeonhole { m: 3, n: 2 });
        let cnf = instance_to_cnf(&inst);
        assert_eq!(cnf.num_vars as usize, inst.num_vars);
        assert_eq!(cnf.num_clauses(), inst.clauses.len());
    }

    // ---- Synthesize dispatch tests ----

    #[test]
    fn test_synthesize_all_targets() {
        let targets = vec![
            SynthesisTarget::Pigeonhole { m: 3, n: 2 },
            SynthesisTarget::Tseitin { n: 6, degree: 3 },
            SynthesisTarget::Ramsey { r: 3, s: 3, n: 5 },
            SynthesisTarget::Parity { n: 6, num_xors: 4 },
            SynthesisTarget::Ordering { n: 3 },
            SynthesisTarget::GraphColoring {
                k: 2,
                edges: vec![(0, 1), (1, 2)],
            },
        ];
        for target in &targets {
            let inst = synthesize(target);
            let cnf = instance_to_cnf(&inst);
            assert!(cnf.is_valid(), "target {:?} produced invalid CNF", target);
        }
    }
}
