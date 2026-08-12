// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX Apache-2.0

//! Catalog of hard formula families for proof-complexity-guided proof system
//! selection.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::sat_verify::cdcl::{Clause, Literal};
use crate::sat_verify::proof_complexity::encodings::pigeonhole_cnf;
use crate::sat_verify::proof_complexity::lower_bounds::{
    random_cnf_resolution_threshold, ResolutionComplexity,
};
use crate::sat_verify::proof_complexity::tseitin_graphs::{
    expander_graph, formula_variable_count, tseitin_on_graph,
};
use crate::sat_verify::types::{Cnf, Lit, SatClause, Var};

use super::proof_complexity::separations::ProofSystem;

/// High-level benchmark family classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum FormulaFamily {
    /// PHP(n+1,n), hard for resolution.
    Pigeonhole,
    /// Parity constraints on graphs, hard for resolution on expanders.
    Tseitin,
    /// Random k-CNF near threshold.
    RandomKSat,
    /// Graph coloring instances, hard for cutting planes.
    CliqueColoring,
    /// Dominating-set constraints.
    DominatingSet,
    /// Pure XOR/parity formulas.
    ParityXor,
    /// AMO/EO/cardinality structure.
    CardinalityConstraint,
    /// High-symmetry formulas amenable to symmetry breaking.
    SymmetricFormula,
    /// Mixed structural signals.
    Hybrid,
    /// Unclassified formula.
    Unknown,
}

/// Coarse structural class used for routing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum StructureClass {
    /// Formula encodes a graph property.
    GraphBased,
    /// Formula has algebraic XOR/parity structure.
    Algebraic,
    /// Formula looks random and unstructured.
    Random,
    /// Formula is dominated by counting/cardinality constraints.
    Counting,
    /// Formula has strong symmetry.
    Symmetric,
}

/// Structural profile used for proof-system routing.
#[derive(Debug, Clone)]
pub struct FormulaProfile {
    pub family: FormulaFamily,
    pub structure: StructureClass,
    pub num_vars: u32,
    pub num_clauses: usize,
    pub avg_clause_width: f64,
    pub max_clause_width: usize,
    pub clause_var_ratio: f64,
    pub xor_fraction: f64,
    pub binary_fraction: f64,
    pub positive_negative_ratio: f64,
    pub estimated_treewidth: Option<u32>,
    pub recommended_system: ProofSystem,
}

/// Output of proof-system routing.
#[derive(Debug, Clone)]
pub struct RoutingDecision {
    pub primary_system: ProofSystem,
    pub confidence: f64,
    pub rationale: String,
    pub fallback_system: Option<ProofSystem>,
}

#[derive(Debug, Clone)]
pub(crate) struct LcgRng {
    state: u64,
}

impl LcgRng {
    #[must_use]
    pub(crate) fn new(seed: u64) -> Self {
        Self {
            state: seed ^ 0x9E37_79B9_7F4A_7C15,
        }
    }

    #[must_use]
    pub(crate) fn next_u32(&mut self) -> u32 {
        self.state = self
            .state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.state >> 32) as u32
    }

    #[must_use]
    pub(crate) fn gen_range(&mut self, upper: u32) -> u32 {
        if upper == 0 {
            0
        } else {
            self.next_u32() % upper
        }
    }

    #[must_use]
    pub(crate) fn gen_bool(&mut self) -> bool {
        self.next_u32() & 1 == 1
    }
}

/// Classify the structure of a CNF formula from raw clauses.
#[must_use]
pub fn classify_structure(clauses: &[Clause], num_vars: u32) -> FormulaProfile {
    let num_clauses = clauses.len();
    let total_width: usize = clauses.iter().map(Vec::len).sum();
    let avg_clause_width = if num_clauses == 0 {
        0.0
    } else {
        total_width as f64 / num_clauses as f64
    };
    let max_clause_width = clauses.iter().map(Vec::len).max().unwrap_or(0);
    let clause_var_ratio = if num_vars == 0 {
        0.0
    } else {
        num_clauses as f64 / f64::from(num_vars)
    };
    let xor_fraction = detect_xor_clauses(clauses, num_vars);
    let binary_count = clauses.iter().filter(|clause| clause.len() == 2).count();
    let binary_fraction = if num_clauses == 0 {
        0.0
    } else {
        binary_count as f64 / num_clauses as f64
    };

    let (positive_occurrences, negative_occurrences) = count_literal_polarities(clauses, num_vars);
    let positive_negative_ratio =
        (positive_occurrences as f64 + 1.0) / (negative_occurrences as f64 + 1.0);
    let estimated_treewidth = Some(estimate_treewidth_upper(clauses, num_vars));
    let width_histogram = estimate_clause_width_distribution(clauses);
    let three_clause_fraction = if num_clauses == 0 {
        0.0
    } else {
        width_histogram
            .iter()
            .find(|(width, _)| *width == 3)
            .map_or(0.0, |(_, count)| *count as f64 / num_clauses as f64)
    };
    let is_pigeonhole = detect_pigeonhole_structure(clauses, num_vars);
    let is_clique_coloring = detect_clique_coloring_structure(clauses, num_vars);
    let is_dominating = detect_dominating_cycle_structure(clauses, num_vars);
    let cardinality_like = detect_cardinality_structure(clauses);
    let symmetry_like = detect_symmetry(clauses, num_vars);
    let random_complexity = random_cnf_resolution_threshold(num_vars as usize, clause_var_ratio);

    let (family, structure) = if is_pigeonhole {
        (FormulaFamily::Pigeonhole, StructureClass::Counting)
    } else if xor_fraction >= 0.6 && max_clause_width > 2 {
        (FormulaFamily::Tseitin, StructureClass::GraphBased)
    } else if xor_fraction >= 0.6 {
        (FormulaFamily::ParityXor, StructureClass::Algebraic)
    } else if is_clique_coloring {
        (FormulaFamily::CliqueColoring, StructureClass::GraphBased)
    } else if is_dominating {
        (FormulaFamily::DominatingSet, StructureClass::GraphBased)
    } else if matches!(random_complexity, ResolutionComplexity::HardRefutable)
        && three_clause_fraction >= 0.75
        && positive_negative_ratio > 0.5
        && positive_negative_ratio < 2.0
        && xor_fraction < 0.25
    {
        (FormulaFamily::RandomKSat, StructureClass::Random)
    } else if xor_fraction >= 0.25 && cardinality_like {
        (
            FormulaFamily::Hybrid,
            if xor_fraction >= binary_fraction {
                StructureClass::Algebraic
            } else {
                StructureClass::Counting
            },
        )
    } else if cardinality_like {
        (
            FormulaFamily::CardinalityConstraint,
            StructureClass::Counting,
        )
    } else if symmetry_like {
        (FormulaFamily::SymmetricFormula, StructureClass::Symmetric)
    } else {
        let structure = if xor_fraction >= 0.25 {
            StructureClass::Algebraic
        } else if cardinality_like {
            StructureClass::Counting
        } else if symmetry_like {
            StructureClass::Symmetric
        } else {
            StructureClass::Random
        };
        (FormulaFamily::Unknown, structure)
    };

    let mut profile = FormulaProfile {
        family,
        structure,
        num_vars,
        num_clauses,
        avg_clause_width,
        max_clause_width,
        clause_var_ratio,
        xor_fraction,
        binary_fraction,
        positive_negative_ratio,
        estimated_treewidth,
        recommended_system: ProofSystem::Resolution,
    };
    let decision = route_to_proof_system(&profile);
    profile.recommended_system = decision.primary_system;
    profile
}

/// Route a profiled formula to the proof system that best matches it.
#[must_use]
pub fn route_to_proof_system(profile: &FormulaProfile) -> RoutingDecision {
    match profile.family {
        FormulaFamily::Pigeonhole => RoutingDecision {
            primary_system: ProofSystem::CuttingPlanes,
            confidence: 0.97,
            rationale: String::from(
                "Detected PHP-style ALO/AMO structure; Cutting Planes has polynomial refutations while resolution is exponential.",
            ),
            fallback_system: Some(ProofSystem::ExtendedResolution),
        },
        FormulaFamily::Tseitin => RoutingDecision {
            primary_system: ProofSystem::ExtendedResolution,
            confidence: if profile.estimated_treewidth.unwrap_or(0) >= 4 {
                0.86
            } else {
                0.8
            },
            rationale: format!(
                "Detected graph-based parity constraints with XOR fraction {:.2}; Extended Resolution is a strong lane for Tseitin-style instances.",
                profile.xor_fraction
            ),
            fallback_system: Some(ProofSystem::CuttingPlanes),
        },
        FormulaFamily::RandomKSat => RoutingDecision {
            primary_system: ProofSystem::Resolution,
            confidence: 0.9,
            rationale: format!(
                "Near-threshold random 3-CNF profile (clause/var ratio {:.2}) matches CDCL/Resolution strengths.",
                profile.clause_var_ratio
            ),
            fallback_system: Some(ProofSystem::TreeResolution),
        },
        FormulaFamily::ParityXor => RoutingDecision {
            primary_system: ProofSystem::ExtendedResolution,
            confidence: 0.94,
            rationale: format!(
                "Pure XOR/parity structure with XOR fraction {:.2} favors Extended Resolution over plain resolution.",
                profile.xor_fraction
            ),
            fallback_system: Some(ProofSystem::CuttingPlanes),
        },
        FormulaFamily::CardinalityConstraint => RoutingDecision {
            primary_system: ProofSystem::CuttingPlanes,
            confidence: 0.88,
            rationale: String::from(
                "Counting-heavy clauses are naturally handled by pseudo-Boolean reasoning in Cutting Planes.",
            ),
            fallback_system: Some(ProofSystem::Resolution),
        },
        FormulaFamily::CliqueColoring => RoutingDecision {
            primary_system: ProofSystem::CuttingPlanes,
            confidence: 0.84,
            rationale: String::from(
                "Clique-coloring combines graph structure with strong counting constraints, which favors Cutting Planes.",
            ),
            fallback_system: Some(ProofSystem::ExtendedResolution),
        },
        FormulaFamily::DominatingSet => RoutingDecision {
            primary_system: ProofSystem::CuttingPlanes,
            confidence: 0.72,
            rationale: String::from(
                "Dominating-set encodings mix graph coverage with cardinality bounds; Cutting Planes is the safest default.",
            ),
            fallback_system: Some(ProofSystem::Resolution),
        },
        FormulaFamily::SymmetricFormula => RoutingDecision {
            primary_system: ProofSystem::ExtendedResolution,
            confidence: 0.66,
            rationale: String::from(
                "High symmetry often benefits from extensions or symmetry-breaking auxiliaries before resolution.",
            ),
            fallback_system: Some(ProofSystem::Resolution),
        },
        FormulaFamily::Hybrid => {
            if matches!(profile.structure, StructureClass::Counting) {
                RoutingDecision {
                    primary_system: ProofSystem::CuttingPlanes,
                    confidence: 0.7,
                    rationale: String::from(
                        "Hybrid formula still has counting as the dominant signal, so Cutting Planes is preferred.",
                    ),
                    fallback_system: Some(ProofSystem::ExtendedResolution),
                }
            } else {
                RoutingDecision {
                    primary_system: ProofSystem::ExtendedResolution,
                    confidence: 0.7,
                    rationale: String::from(
                        "Hybrid formula retains strong algebraic structure, so Extended Resolution gets the primary route.",
                    ),
                    fallback_system: Some(ProofSystem::CuttingPlanes),
                }
            }
        }
        FormulaFamily::Unknown => match profile.structure {
            StructureClass::Algebraic => RoutingDecision {
                primary_system: ProofSystem::ExtendedResolution,
                confidence: 0.62,
                rationale: String::from(
                    "Unclassified formula still shows algebraic structure, so Extended Resolution is the safer lane.",
                ),
                fallback_system: Some(ProofSystem::Resolution),
            },
            StructureClass::Counting => RoutingDecision {
                primary_system: ProofSystem::CuttingPlanes,
                confidence: 0.62,
                rationale: String::from(
                    "Unclassified formula is counting-heavy, so pseudo-Boolean reasoning is the best default.",
                ),
                fallback_system: Some(ProofSystem::Resolution),
            },
            StructureClass::Symmetric => RoutingDecision {
                primary_system: ProofSystem::ExtendedResolution,
                confidence: 0.55,
                rationale: String::from(
                    "Symmetry is the dominant detected signal; Extended Resolution is a reasonable default.",
                ),
                fallback_system: Some(ProofSystem::Resolution),
            },
            StructureClass::GraphBased | StructureClass::Random => RoutingDecision {
                primary_system: ProofSystem::Resolution,
                confidence: 0.5,
                rationale: String::from(
                    "No stronger structural signal dominated the profile, so defaulting to Resolution.",
                ),
                fallback_system: Some(ProofSystem::CuttingPlanes),
            },
        },
    }
}

/// Detect the fraction of clauses that participate in XOR/parity patterns.
#[must_use]
pub fn detect_xor_clauses(clauses: &[Clause], num_vars: u32) -> f64 {
    if clauses.is_empty() || num_vars == 0 {
        return 0.0;
    }

    let mut groups: HashMap<Vec<u32>, Vec<Vec<bool>>> = HashMap::new();
    for clause in clauses {
        if let Some((support, sign_pattern)) = canonical_parity_clause(clause, num_vars) {
            groups.entry(support).or_default().push(sign_pattern);
        }
    }

    let mut xor_clause_count = 0usize;
    for (support, patterns) in groups {
        let width = support.len();
        if !(2..=12).contains(&width) {
            continue;
        }

        let expected_patterns = 1usize << (width - 1);
        let unique_patterns: HashSet<Vec<bool>> = patterns.iter().cloned().collect();
        if unique_patterns.len() != expected_patterns {
            continue;
        }

        let mut parity_class = None;
        let mut consistent = true;
        for pattern in &unique_patterns {
            let parity = pattern.iter().filter(|&&is_negative| is_negative).count() % 2 == 1;
            if let Some(expected) = parity_class {
                if expected != parity {
                    consistent = false;
                    break;
                }
            } else {
                parity_class = Some(parity);
            }
        }

        if consistent {
            xor_clause_count += patterns.len();
        }
    }

    xor_clause_count as f64 / clauses.len() as f64
}

/// Detect a pigeonhole-style ALO + binary-negative AMO structure.
#[must_use]
pub fn detect_pigeonhole_structure(clauses: &[Clause], num_vars: u32) -> bool {
    if clauses.is_empty() || num_vars == 0 {
        return false;
    }

    let num_vars_usize = num_vars as usize;
    let binary_negative_clauses: Vec<&Clause> = clauses
        .iter()
        .filter(|clause| clause.len() == 2 && clause.iter().all(|&lit| lit < 0))
        .collect();

    let mut positive_clause_counts = BTreeMap::new();
    for clause in clauses {
        if clause.len() >= 2 && clause.iter().all(|&lit| lit > 0) {
            *positive_clause_counts.entry(clause.len()).or_insert(0usize) += 1;
        }
    }

    for (holes, pigeons) in positive_clause_counts {
        if holes == 0 || pigeons < 2 {
            continue;
        }
        if num_vars_usize != holes.saturating_mul(pigeons) {
            continue;
        }

        let expected_binary =
            holes.saturating_mul(pigeons.saturating_mul(pigeons.saturating_sub(1)) / 2);
        if binary_negative_clauses.len() != expected_binary {
            continue;
        }

        let positive_clauses: Vec<&Clause> = clauses
            .iter()
            .filter(|clause| clause.len() == holes && clause.iter().all(|&lit| lit > 0))
            .collect();

        let mut owner = vec![None; num_vars_usize + 1];
        let mut positive_occurrences = vec![0usize; num_vars_usize + 1];
        let mut valid = true;
        for (owner_id, clause) in positive_clauses.iter().enumerate() {
            let mut seen = BTreeSet::new();
            for &lit in *clause {
                let var = lit.unsigned_abs() as usize;
                if var == 0 || var > num_vars_usize || !seen.insert(var) {
                    valid = false;
                    break;
                }
                positive_occurrences[var] += 1;
                if owner[var].replace(owner_id).is_some() {
                    valid = false;
                    break;
                }
            }
            if !valid {
                break;
            }
        }
        if !valid {
            continue;
        }

        if (1..=num_vars_usize).any(|var| positive_occurrences[var] != 1) {
            continue;
        }

        let mut negative_occurrences = vec![0usize; num_vars_usize + 1];
        for clause in &binary_negative_clauses {
            let var_a = clause[0].unsigned_abs() as usize;
            let var_b = clause[1].unsigned_abs() as usize;
            if var_a == 0
                || var_b == 0
                || var_a > num_vars_usize
                || var_b > num_vars_usize
                || var_a == var_b
                || owner[var_a] == owner[var_b]
            {
                valid = false;
                break;
            }
            negative_occurrences[var_a] += 1;
            negative_occurrences[var_b] += 1;
        }

        if valid && (1..=num_vars_usize).all(|var| negative_occurrences[var] == pigeons - 1) {
            return true;
        }
    }

    false
}

/// Estimate an upper bound on primal-graph treewidth via min-degree ordering.
#[must_use]
pub fn estimate_treewidth_upper(clauses: &[Clause], num_vars: u32) -> u32 {
    let mut graph = build_primal_graph(clauses, num_vars);
    let mut remaining: HashSet<usize> = (1..=num_vars as usize)
        .filter(|&var| !graph[var].is_empty() || variable_occurs(clauses, var as u32))
        .collect();
    let mut treewidth = 0usize;

    while !remaining.is_empty() {
        let next = remaining
            .iter()
            .copied()
            .min_by_key(|&var| graph[var].intersection(&remaining).count());
        let Some(var) = next else {
            break;
        };

        let neighbors: Vec<usize> = graph[var]
            .iter()
            .copied()
            .filter(|neighbor| remaining.contains(neighbor))
            .collect();
        treewidth = treewidth.max(neighbors.len());

        for i in 0..neighbors.len() {
            for j in (i + 1)..neighbors.len() {
                let a = neighbors[i];
                let b = neighbors[j];
                graph[a].insert(b);
                graph[b].insert(a);
            }
        }

        for neighbor in &neighbors {
            graph[*neighbor].remove(&var);
        }
        graph[var].clear();
        remaining.remove(&var);
    }

    saturating_usize_to_u32(treewidth)
}

/// Return a histogram of clause widths.
#[must_use]
pub fn estimate_clause_width_distribution(clauses: &[Clause]) -> Vec<(usize, usize)> {
    let mut histogram = BTreeMap::new();
    for clause in clauses {
        *histogram.entry(clause.len()).or_insert(0usize) += 1;
    }
    histogram.into_iter().collect()
}

/// Generate PHP(n+1,n) as a typed CNF.
#[must_use]
pub fn generate_php(n: usize) -> Cnf {
    let clauses = pigeonhole_cnf(n + 1, n);
    raw_clauses_to_cnf(saturating_usize_to_u32((n + 1).saturating_mul(n)), clauses)
}

/// Generate a Tseitin formula on a deterministic expander graph.
#[must_use]
pub fn generate_tseitin_expander(n: usize) -> Cnf {
    if n == 0 {
        return Cnf {
            num_vars: 0,
            clauses: Vec::new(),
        };
    }

    let graph = expander_graph(n, 3);
    let mut parity = vec![false; n];
    parity[0] = true;
    let clauses = tseitin_on_graph(&graph, &parity);
    raw_clauses_to_cnf(
        saturating_usize_to_u32(formula_variable_count(&graph)),
        clauses,
    )
}

/// Generate a deterministic random 3-SAT instance.
#[must_use]
pub fn generate_random_3sat(num_vars: u32, clause_var_ratio: f64) -> Cnf {
    if num_vars == 0 || clause_var_ratio <= 0.0 {
        return Cnf {
            num_vars,
            clauses: Vec::new(),
        };
    }

    let seed =
        u64::from(num_vars) ^ clause_var_ratio.to_bits().rotate_left(17) ^ 0xD1B5_4A32_1C2D_3E4F;
    let mut rng = LcgRng::new(seed);
    let width = (num_vars as usize).min(3);
    let num_clauses = ((f64::from(num_vars) * clause_var_ratio).round() as usize).max(1);
    let mut clauses = Vec::with_capacity(num_clauses);

    for _ in 0..num_clauses {
        let vars = sample_distinct_vars(width, num_vars, &mut rng);
        let mut clause = Vec::with_capacity(width);
        for var in vars {
            let literal = raw_literal_from_var(var, rng.gen_bool());
            clause.push(Lit::from_dimacs(literal));
        }
        clauses.push(SatClause(clause));
    }

    Cnf { num_vars, clauses }
}

/// Generate a deterministic XOR/parity formula.
#[must_use]
pub fn generate_xor_formula(num_vars: u32, num_xors: usize) -> Cnf {
    if num_vars < 2 || num_xors == 0 {
        return Cnf {
            num_vars,
            clauses: Vec::new(),
        };
    }

    let seed = u64::from(num_vars) ^ (num_xors as u64).rotate_left(11) ^ 0xA24B_6C81_92D3_E4F5;
    let mut rng = LcgRng::new(seed);
    let mut clauses = Vec::with_capacity(num_xors.saturating_mul(2));

    for _ in 0..num_xors {
        let vars = sample_distinct_vars(2, num_vars, &mut rng);
        let x = vars[0];
        let y = vars[1];
        let odd_parity = rng.gen_bool();

        if odd_parity {
            clauses.push(SatClause(vec![
                lit_from_var(x, true),
                lit_from_var(y, true),
            ]));
            clauses.push(SatClause(vec![
                lit_from_var(x, false),
                lit_from_var(y, false),
            ]));
        } else {
            clauses.push(SatClause(vec![
                lit_from_var(x, false),
                lit_from_var(y, true),
            ]));
            clauses.push(SatClause(vec![
                lit_from_var(x, true),
                lit_from_var(y, false),
            ]));
        }
    }

    Cnf { num_vars, clauses }
}

/// Generate the standard k-coloring encoding for K_n.
#[must_use]
pub fn generate_clique_coloring(n: usize, k: usize) -> Cnf {
    if n == 0 {
        return Cnf {
            num_vars: 0,
            clauses: Vec::new(),
        };
    }
    if k == 0 {
        return Cnf {
            num_vars: 0,
            clauses: (0..n).map(|_| SatClause(Vec::new())).collect(),
        };
    }

    let num_vars = saturating_usize_to_u32(n.saturating_mul(k));
    let mut clauses = Vec::new();

    for vertex in 0..n {
        let mut alo = Vec::with_capacity(k);
        for color in 0..k {
            let var = coloring_var(vertex, color, k);
            alo.push(lit_from_var(var, true));
        }
        clauses.push(SatClause(alo));

        for color_a in 0..k {
            for color_b in (color_a + 1)..k {
                let var_a = coloring_var(vertex, color_a, k);
                let var_b = coloring_var(vertex, color_b, k);
                clauses.push(SatClause(vec![
                    lit_from_var(var_a, false),
                    lit_from_var(var_b, false),
                ]));
            }
        }
    }

    for left in 0..n {
        for right in (left + 1)..n {
            for color in 0..k {
                let var_left = coloring_var(left, color, k);
                let var_right = coloring_var(right, color, k);
                clauses.push(SatClause(vec![
                    lit_from_var(var_left, false),
                    lit_from_var(var_right, false),
                ]));
            }
        }
    }

    Cnf { num_vars, clauses }
}

/// Generate a dominating-set instance on the cycle graph C_n with bound k.
#[must_use]
pub fn generate_dominating_set(n: usize, k: usize) -> Cnf {
    if n == 0 {
        return Cnf {
            num_vars: 0,
            clauses: Vec::new(),
        };
    }

    let num_vars = saturating_usize_to_u32(n);
    let mut clauses = Vec::new();

    for vertex in 0..n {
        let left = (vertex + n - 1) % n;
        let right = (vertex + 1) % n;
        let mut support = BTreeSet::new();
        support.insert(vertex + 1);
        support.insert(left + 1);
        support.insert(right + 1);

        let clause = support
            .into_iter()
            .map(|idx| lit_from_var(var_from_usize(idx), true))
            .collect();
        clauses.push(SatClause(clause));
    }

    if k < n {
        let mut current = Vec::with_capacity(k + 1);
        combinations(1, n, k + 1, &mut current, &mut |subset| {
            let clause = subset
                .iter()
                .copied()
                .map(|idx| lit_from_var(var_from_usize(idx), false))
                .collect();
            clauses.push(SatClause(clause));
        });
    }

    Cnf { num_vars, clauses }
}

/// Crude lower bound on resolution width from primal-graph minimum degree.
#[must_use]
pub fn width_lower_bound_heuristic(clauses: &[Clause], num_vars: u32) -> usize {
    let graph = build_primal_graph(clauses, num_vars);
    let active_vars: Vec<usize> = (1..=num_vars as usize)
        .filter(|&var| variable_occurs(clauses, var as u32))
        .collect();
    if active_vars.is_empty() {
        return 0;
    }

    active_vars
        .into_iter()
        .map(|var| graph[var].len())
        .min()
        .unwrap_or(0)
}

#[must_use]
pub(crate) fn raw_clauses_to_cnf(num_vars: u32, clauses: Vec<Clause>) -> Cnf {
    let sat_clauses = clauses
        .into_iter()
        .map(|clause| SatClause(clause.into_iter().map(Lit::from_dimacs).collect()))
        .collect();
    Cnf {
        num_vars,
        clauses: sat_clauses,
    }
}

#[must_use]
pub(crate) fn raw_literal_from_var(var: Var, positive: bool) -> Literal {
    let base = i32::try_from(var.index()).unwrap_or(i32::MAX);
    if positive {
        base
    } else {
        -base
    }
}

#[must_use]
pub(crate) fn lit_from_var(var: Var, positive: bool) -> Lit {
    Lit::from_dimacs(raw_literal_from_var(var, positive))
}

#[must_use]
pub(crate) fn var_from_usize(index: usize) -> Var {
    Var(saturating_usize_to_u32(index))
}

#[must_use]
pub(crate) fn saturating_usize_to_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

#[must_use]
pub(crate) fn coloring_var(vertex: usize, color: usize, num_colors: usize) -> Var {
    let index = vertex
        .saturating_mul(num_colors)
        .saturating_add(color)
        .saturating_add(1);
    var_from_usize(index)
}

#[must_use]
pub(crate) fn sample_distinct_vars(width: usize, num_vars: u32, rng: &mut LcgRng) -> Vec<Var> {
    let mut chosen = BTreeSet::new();
    while chosen.len() < width {
        let idx = rng.gen_range(num_vars).saturating_add(1) as usize;
        chosen.insert(var_from_usize(idx));
    }
    chosen.into_iter().collect()
}

pub(crate) fn combinations(
    start: usize,
    end: usize,
    choose: usize,
    current: &mut Vec<usize>,
    emit: &mut impl FnMut(&[usize]),
) {
    if current.len() == choose {
        emit(current);
        return;
    }
    if start > end {
        return;
    }

    let needed = choose - current.len();
    for value in start..=end {
        if end.saturating_sub(value).saturating_add(1) < needed {
            break;
        }
        current.push(value);
        combinations(value + 1, end, choose, current, emit);
        current.pop();
    }
}

#[must_use]
pub(crate) fn build_primal_graph(clauses: &[Clause], num_vars: u32) -> Vec<HashSet<usize>> {
    let mut graph = vec![HashSet::new(); num_vars as usize + 1];

    for clause in clauses {
        let vars: Vec<usize> = clause
            .iter()
            .filter_map(|&lit| {
                if lit == 0 {
                    return None;
                }
                let var = lit.unsigned_abs() as usize;
                if var == 0 || var > num_vars as usize {
                    None
                } else {
                    Some(var)
                }
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();

        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                let left = vars[i];
                let right = vars[j];
                graph[left].insert(right);
                graph[right].insert(left);
            }
        }
    }

    graph
}

#[must_use]
pub(crate) fn canonical_parity_clause(
    clause: &Clause,
    num_vars: u32,
) -> Option<(Vec<u32>, Vec<bool>)> {
    if clause.len() < 2 {
        return None;
    }

    let mut vars = BTreeMap::new();
    for &lit in clause {
        if lit == 0 {
            return None;
        }
        let var = lit.unsigned_abs();
        if var == 0 || var > num_vars {
            return None;
        }
        let is_negative = lit < 0;
        if vars.insert(var, is_negative).is_some() {
            return None;
        }
    }

    let mut support = Vec::with_capacity(vars.len());
    let mut pattern = Vec::with_capacity(vars.len());
    for (var, is_negative) in vars {
        support.push(var);
        pattern.push(is_negative);
    }
    Some((support, pattern))
}

#[must_use]
pub(crate) fn count_literal_polarities(clauses: &[Clause], num_vars: u32) -> (usize, usize) {
    let mut positive = 0usize;
    let mut negative = 0usize;
    for clause in clauses {
        for &lit in clause {
            if lit == 0 {
                continue;
            }
            let var = lit.unsigned_abs();
            if num_vars != 0 && var > num_vars {
                continue;
            }
            if lit > 0 {
                positive += 1;
            } else {
                negative += 1;
            }
        }
    }
    (positive, negative)
}

#[must_use]
pub(crate) fn detect_cardinality_structure(clauses: &[Clause]) -> bool {
    if clauses.is_empty() {
        return false;
    }

    let wide_positive = clauses
        .iter()
        .filter(|clause| clause.len() >= 3 && clause.iter().all(|&lit| lit > 0))
        .count();
    let binary_negative = clauses
        .iter()
        .filter(|clause| clause.len() == 2 && clause.iter().all(|&lit| lit < 0))
        .count();

    wide_positive > 0 && binary_negative.saturating_mul(10) >= clauses.len().saturating_mul(3)
}

#[must_use]
pub(crate) fn detect_symmetry(clauses: &[Clause], num_vars: u32) -> bool {
    if clauses.is_empty() || num_vars < 4 {
        return false;
    }

    let mut occurrences = vec![0usize; num_vars as usize + 1];
    for clause in clauses {
        let mut seen = BTreeSet::new();
        for &lit in clause {
            let var = lit.unsigned_abs() as usize;
            if var == 0 || var > num_vars as usize || !seen.insert(var) {
                continue;
            }
            occurrences[var] += 1;
        }
    }

    let active: Vec<usize> = occurrences
        .into_iter()
        .skip(1)
        .filter(|count| *count > 0)
        .collect();
    if active.len() < 4 {
        return false;
    }

    let min_occ = active.iter().copied().min().unwrap_or(0);
    let max_occ = active.iter().copied().max().unwrap_or(0);
    max_occ.saturating_sub(min_occ) <= 1
}

#[must_use]
pub(crate) fn detect_clique_coloring_structure(clauses: &[Clause], num_vars: u32) -> bool {
    if clauses.is_empty() || num_vars == 0 {
        return false;
    }

    let num_vars_usize = num_vars as usize;
    let mut positive_by_width = BTreeMap::new();
    let mut positive_occurrences = vec![0usize; num_vars_usize + 1];

    for clause in clauses {
        if clause.len() >= 2 && clause.iter().all(|&lit| lit > 0) {
            *positive_by_width.entry(clause.len()).or_insert(0usize) += 1;
            let mut seen = BTreeSet::new();
            for &lit in clause {
                let var = lit.unsigned_abs() as usize;
                if var == 0 || var > num_vars_usize || !seen.insert(var) {
                    return false;
                }
                positive_occurrences[var] += 1;
            }
        }
    }

    let binary_negative = clauses
        .iter()
        .filter(|clause| clause.len() == 2 && clause.iter().all(|&lit| lit < 0))
        .count();

    for (colors, vertices) in positive_by_width {
        if colors < 2 || vertices < 2 || num_vars_usize != vertices.saturating_mul(colors) {
            continue;
        }

        let expected_binary = vertices.saturating_mul(colors.saturating_mul(colors - 1) / 2)
            + (vertices.saturating_mul(vertices - 1) / 2).saturating_mul(colors);

        if binary_negative == expected_binary
            && (1..=num_vars_usize).all(|var| positive_occurrences[var] == 1)
        {
            return true;
        }
    }

    false
}

#[must_use]
pub(crate) fn detect_dominating_cycle_structure(clauses: &[Clause], num_vars: u32) -> bool {
    if clauses.is_empty() || num_vars < 3 {
        return false;
    }

    let positive_triplets: Vec<&Clause> = clauses
        .iter()
        .filter(|clause| clause.len() == 3 && clause.iter().all(|&lit| lit > 0))
        .collect();
    if positive_triplets.len() != num_vars as usize {
        return false;
    }

    let has_negative_cardinality = clauses
        .iter()
        .any(|clause| clause.len() >= 2 && clause.iter().all(|&lit| lit < 0));
    if !has_negative_cardinality {
        return false;
    }

    let mut positive_occurrences = vec![0usize; num_vars as usize + 1];
    for clause in positive_triplets {
        let mut seen = BTreeSet::new();
        for &lit in clause {
            let var = lit.unsigned_abs() as usize;
            if var == 0 || var > num_vars as usize || !seen.insert(var) {
                return false;
            }
            positive_occurrences[var] += 1;
        }
    }

    (1..=num_vars as usize).all(|var| (2..=3).contains(&positive_occurrences[var]))
}

#[must_use]
pub(crate) fn variable_occurs(clauses: &[Clause], var: u32) -> bool {
    clauses
        .iter()
        .any(|clause| clause.iter().any(|&lit| lit.unsigned_abs() == var))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn raw_clauses(cnf: &Cnf) -> Vec<Clause> {
        cnf.clauses.iter().map(SatClause::to_dimacs).collect()
    }

    #[test]
    fn test_classify_php() {
        let cnf = generate_php(3);
        let clauses = raw_clauses(&cnf);
        let profile = classify_structure(&clauses, cnf.num_vars);
        assert_eq!(profile.family, FormulaFamily::Pigeonhole);
    }

    #[test]
    fn test_classify_random() {
        let cnf = generate_random_3sat(32, 4.3);
        let clauses = raw_clauses(&cnf);
        let profile = classify_structure(&clauses, cnf.num_vars);
        assert_eq!(profile.family, FormulaFamily::RandomKSat);
    }

    #[test]
    fn test_classify_xor() {
        let cnf = generate_xor_formula(16, 12);
        let clauses = raw_clauses(&cnf);
        let profile = classify_structure(&clauses, cnf.num_vars);
        assert_eq!(profile.family, FormulaFamily::ParityXor);
    }

    #[test]
    fn test_route_php_to_cp() {
        let cnf = generate_php(3);
        let clauses = raw_clauses(&cnf);
        let profile = classify_structure(&clauses, cnf.num_vars);
        let route = route_to_proof_system(&profile);
        assert_eq!(route.primary_system, ProofSystem::CuttingPlanes);
    }

    #[test]
    fn test_route_random_to_resolution() {
        let cnf = generate_random_3sat(32, 4.3);
        let clauses = raw_clauses(&cnf);
        let profile = classify_structure(&clauses, cnf.num_vars);
        let route = route_to_proof_system(&profile);
        assert_eq!(route.primary_system, ProofSystem::Resolution);
    }

    #[test]
    fn test_route_xor_to_extended() {
        let cnf = generate_xor_formula(20, 18);
        let clauses = raw_clauses(&cnf);
        let profile = classify_structure(&clauses, cnf.num_vars);
        let route = route_to_proof_system(&profile);
        assert_eq!(route.primary_system, ProofSystem::ExtendedResolution);
    }

    #[test]
    fn test_treewidth_estimate_small() {
        let cnf = generate_php(3);
        let clauses = raw_clauses(&cnf);
        let treewidth = estimate_treewidth_upper(&clauses, cnf.num_vars);
        assert!(treewidth >= 2);
        assert!(treewidth <= cnf.num_vars);
    }

    #[test]
    fn test_width_distribution() {
        let cnf = generate_php(3);
        let clauses = raw_clauses(&cnf);
        let histogram = estimate_clause_width_distribution(&clauses);
        let histogram_map: BTreeMap<usize, usize> = histogram.into_iter().collect();
        assert_eq!(histogram_map.get(&3), Some(&4));
        assert_eq!(histogram_map.get(&2), Some(&18));
    }

    #[test]
    fn test_generate_all_families() {
        let php = generate_php(3);
        let tseitin = generate_tseitin_expander(8);
        let random = generate_random_3sat(24, 4.1);
        let xor = generate_xor_formula(12, 10);
        let clique = generate_clique_coloring(4, 3);
        let dominating = generate_dominating_set(6, 2);

        assert!(!php.clauses.is_empty());
        assert!(!tseitin.clauses.is_empty());
        assert!(!random.clauses.is_empty());
        assert!(!xor.clauses.is_empty());
        assert!(!clique.clauses.is_empty());
        assert!(!dominating.clauses.is_empty());
    }

    #[test]
    fn test_detect_xor_fraction() {
        let cnf = generate_xor_formula(16, 12);
        let clauses = raw_clauses(&cnf);
        let xor_fraction = detect_xor_clauses(&clauses, cnf.num_vars);
        assert!(xor_fraction > 0.8);
    }

    #[test]
    fn test_detect_pigeonhole() {
        let cnf = generate_php(4);
        let clauses = raw_clauses(&cnf);
        assert!(detect_pigeonhole_structure(&clauses, cnf.num_vars));
    }
}
