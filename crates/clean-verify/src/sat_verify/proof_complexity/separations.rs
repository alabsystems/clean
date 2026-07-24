// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof system hierarchy and separation witnesses.
//!
//! Formalizes the known proof complexity separations:
//! - Tree Resolution << Resolution (exponential gap on Tseitin/expanders)
//! - Resolution << Cutting Planes (exponential gap on PHP, Haken 1985)
//! - Cutting Planes << Extended Resolution (conjectured)
//! - Extended Resolution ~p Frege (polynomially equivalent)
//!
//! References:
//! - Haken (1985): "The intractability of resolution"
//! - Cook, Coullard, Turan (1987): CP proofs of PHP
//! - Ben-Sasson, Wigderson (1999): short proofs are narrow
//! - Krajicek (1997): proof complexity textbook

use super::cutting_planes::{CpInequality, CuttingPlanesProof};
use super::resolution::ResolutionProof;
use super::tree_resolution::TreeResolutionProof;

pub use super::separations_cp::{cp_proof_of_php, verify_cp_derivation, SepCpStep};

/// The proof systems in the standard proof complexity hierarchy,
/// ordered from weakest to strongest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum ProofSystem {
    /// Tree-like resolution: each derived clause used at most once.
    TreeResolution,
    /// General (DAG) resolution: clause reuse allowed.
    Resolution,
    /// Cutting Planes: operates over linear inequalities with integer
    /// rounding.  Strictly stronger than resolution.
    CuttingPlanes,
    /// Extended Resolution: resolution + introduction of new variables
    /// via extension axioms.  Polynomially equivalent to Frege.
    ExtendedResolution,
    /// Frege (a.k.a. textbook propositional logic).  Polynomially
    /// equivalent to Extended Resolution.
    Frege,
}

impl ProofSystem {
    /// Human-readable name.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::TreeResolution => "Tree Resolution",
            Self::Resolution => "Resolution",
            Self::CuttingPlanes => "Cutting Planes",
            Self::ExtendedResolution => "Extended Resolution",
            Self::Frege => "Frege",
        }
    }

    /// Whether `self` is known to be strictly weaker than `other`
    /// (there exist formulas with polynomial proofs in `other` but
    /// requiring super-polynomial proofs in `self`).
    #[must_use]
    pub fn is_strictly_weaker_than(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Self::TreeResolution, Self::Resolution)
                | (Self::TreeResolution, Self::CuttingPlanes)
                | (Self::TreeResolution, Self::ExtendedResolution)
                | (Self::TreeResolution, Self::Frege)
                | (Self::Resolution, Self::CuttingPlanes)
                | (Self::Resolution, Self::ExtendedResolution)
                | (Self::Resolution, Self::Frege)
        )
        // CP << ExtRes is conjectured but not proven; omitted.
    }
}

/// Records a concrete proof-size measurement for a specific formula family.
#[derive(Debug, Clone)]
pub struct ProofSizeWitness {
    /// Description of the formula family (e.g., "PHP(n+1,n)").
    pub formula_family: String,
    /// Parameter n for the family instance.
    pub parameter: usize,
    /// The weaker proof system.
    pub weaker_system: ProofSystem,
    /// Proof size in the weaker system (exact or asymptotic bound).
    pub weaker_size: ProofSizeBound,
    /// The stronger proof system.
    pub stronger_system: ProofSystem,
    /// Proof size in the stronger system (exact or asymptotic bound).
    pub stronger_size: ProofSizeBound,
}

/// A proof-size bound: exact count, or asymptotic lower/upper.
#[derive(Debug, Clone)]
pub enum ProofSizeBound {
    /// Exact proof size measured from a concrete proof.
    Exact(usize),
    /// Lower bound (e.g., Haken's 2^{n/20}).
    LowerBound(f64),
    /// Upper bound.
    UpperBound(usize),
}

/// Outcome of separation-witness verification.
#[derive(Debug, Clone)]
pub struct SeparationResult {
    /// The weaker proof system.
    pub weaker: ProofSystem,
    /// The stronger proof system.
    pub stronger: ProofSystem,
    /// Whether the stronger system has an exponential advantage at this parameter.
    pub exponential_separation: bool,
    /// Ratio of weaker-system size to stronger-system size.
    pub size_ratio: f64,
    /// Human-readable explanation.
    pub explanation: String,
}

// ---------------------------------------------------------------------------
// Proof size measurement
// ---------------------------------------------------------------------------

/// Count the number of steps in a resolution proof.
#[must_use]
pub fn resolution_proof_size(proof: &ResolutionProof) -> usize {
    proof.len()
}

/// Count the number of steps in a Cutting Planes proof.
#[must_use]
pub fn cp_proof_size(proof: &CuttingPlanesProof) -> usize {
    proof.len()
}

/// Count the number of nodes in a tree-resolution proof.
#[must_use]
pub fn tree_resolution_proof_size(proof: &TreeResolutionProof) -> usize {
    proof.root.size()
}

// ---------------------------------------------------------------------------
// Haken's lower bound for resolution proofs of PHP(n+1, n)
// ---------------------------------------------------------------------------

/// Haken's exponential lower bound on resolution proof size for PHP(n+1,n).
///
/// Theorem (Haken 1985): Any resolution refutation of PHP(n+1,n) has size
/// at least 2^{n/20}.
///
/// Returns the lower bound as a floating-point value.
#[must_use]
pub fn php_resolution_size_lower_bound(n: usize) -> f64 {
    2.0_f64.powf(n as f64 / 20.0)
}

/// Upper bound on Cutting Planes proof size for PHP(n+1,n).
///
/// Theorem (Cook, Coullard, Turan 1987): There exist CP refutations of
/// PHP(n+1,n) with O(n^3) lines.
///
/// We return a concrete bound: 2 * n^3 (a comfortable constant factor).
#[must_use]
pub fn php_cp_size_upper_bound(n: usize) -> usize {
    2 * n * n * n
}

// ---------------------------------------------------------------------------
// Separation witness verification
// ---------------------------------------------------------------------------

/// Verify a separation witness for Resolution vs Cutting Planes on PHP.
///
/// Given:
/// - The formula (PHP clauses as `Vec<Vec<i32>>`)
/// - An optional resolution proof (if available; for small n)
/// - The size of the CP proof
///
/// Returns a `SeparationResult` describing which system is exponentially
/// better.
pub fn verify_separation_witness(
    formula: &[Vec<i32>],
    res_proof: Option<&[Vec<i32>]>,
    cp_size: usize,
) -> SeparationResult {
    // Estimate n from the formula.  PHP(n+1, n) has (n+1)*n variables.
    let num_vars = formula
        .iter()
        .flat_map(|c| c.iter())
        .map(|l| l.unsigned_abs() as usize)
        .max()
        .unwrap_or(0);

    // Solve n^2 + n = num_vars => n = (-1 + sqrt(1 + 4*num_vars))/2
    let n_approx = ((-1.0 + (1.0 + 4.0 * num_vars as f64).sqrt()) / 2.0).floor() as usize;
    let n = n_approx.max(1);

    let res_size = res_proof.map(|p| p.len());
    let haken_lower = php_resolution_size_lower_bound(n);
    let cp_upper = php_cp_size_upper_bound(n);

    let effective_res_size = match res_size {
        Some(measured) => measured as f64,
        None => haken_lower,
    };

    let ratio = effective_res_size / cp_size.max(1) as f64;
    let exponential = haken_lower > cp_upper as f64;

    let explanation = if exponential {
        format!(
            "PHP({},{}) separates Resolution from Cutting Planes: \
             Haken lower bound {:.0} >> CP upper bound {}",
            n + 1,
            n,
            haken_lower,
            cp_upper
        )
    } else {
        format!(
            "PHP({},{}) at n={}: Haken bound {:.1}, CP bound {}. \
             Gap not yet exponential at this parameter size.",
            n + 1,
            n,
            n,
            haken_lower,
            cp_upper
        )
    };

    SeparationResult {
        weaker: ProofSystem::Resolution,
        stronger: ProofSystem::CuttingPlanes,
        exponential_separation: exponential,
        size_ratio: ratio,
        explanation,
    }
}

/// Build a `ProofSizeWitness` for the PHP family at parameter `n`.
#[must_use]
pub fn php_separation_witness(n: usize) -> ProofSizeWitness {
    ProofSizeWitness {
        formula_family: format!("PHP({},{})", n + 1, n),
        parameter: n,
        weaker_system: ProofSystem::Resolution,
        weaker_size: ProofSizeBound::LowerBound(php_resolution_size_lower_bound(n)),
        stronger_system: ProofSystem::CuttingPlanes,
        stronger_size: ProofSizeBound::UpperBound(php_cp_size_upper_bound(n)),
    }
}

/// Build a `ProofSizeWitness` for the Tseitin family (tree-res vs res)
/// at parameter `n` (number of vertices in the expander graph).
///
/// Ben-Sasson & Wigderson (1999): tree-resolution of Tseitin on
/// constant-degree expanders requires 2^{Mathverse(n)} size, while general
/// resolution has O(n^2) proofs.
#[must_use]
pub fn tseitin_separation_witness(n: usize) -> ProofSizeWitness {
    ProofSizeWitness {
        formula_family: format!("Tseitin(expander, {})", n),
        parameter: n,
        weaker_system: ProofSystem::TreeResolution,
        weaker_size: ProofSizeBound::LowerBound(2.0_f64.powf(n as f64 / 10.0)),
        stronger_system: ProofSystem::Resolution,
        stronger_size: ProofSizeBound::UpperBound(n * n),
    }
}

// ---------------------------------------------------------------------------
// Standalone resolution verification types
// ---------------------------------------------------------------------------

/// A single resolution step referencing prior clauses by index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SepResolutionStep {
    pub left: usize,
    pub right: usize,
    pub pivot: i32,
    pub result: Vec<i32>,
}

/// A node in a tree-like resolution proof.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SepTreeNode {
    Leaf(usize),
    Internal(Box<SepTreeResStep>),
}

/// A tree-resolution step combining two subtrees on a pivot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SepTreeResStep {
    pub left: SepTreeNode,
    pub right: SepTreeNode,
    pub pivot: i32,
}

/// Result of verifying a resolution proof.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ProofVerifyResult {
    pub valid: bool,
    pub derived_empty: bool,
    pub steps_verified: usize,
    pub errors: Vec<String>,
}

/// Witness for Haken's exponential lower bound (Haken 1985).
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct HakenWitness {
    pub n: usize,
    pub tree_size_lower_bound: u64,
    pub description: String,
}

// ---------------------------------------------------------------------------
// Resolution proof verification
// ---------------------------------------------------------------------------

/// Verify a resolution refutation step by step against input `clauses`.
#[must_use]
pub fn verify_resolution_proof(
    clauses: &[Vec<i32>],
    proof_steps: &[SepResolutionStep],
) -> ProofVerifyResult {
    let mut errors = Vec::new();
    let mut all: Vec<Vec<i32>> = clauses.to_vec();
    let mut steps_ok = 0usize;
    let mut derived_empty = false;

    for (i, step) in proof_steps.iter().enumerate() {
        if step.left >= all.len() || step.right >= all.len() {
            errors.push(format!("step {i}: index out of range"));
            all.push(step.result.clone());
            continue;
        }
        let (left_c, right_c) = (&all[step.left], &all[step.right]);
        let pvar = step.pivot.unsigned_abs();
        let (pos, neg) = (step.pivot.abs(), -step.pivot.abs());
        // Pivot polarity check: legal resolution requires (pos∈left ∧ neg∈right)
        // OR (neg∈left ∧ pos∈right). The De-Morgan-simplified form clippy
        // suggests obscures the symmetry between the two valid polarities.
        #[allow(clippy::nonminimal_bool)]
        if !(left_c.contains(&pos) && right_c.contains(&neg))
            && !(left_c.contains(&neg) && right_c.contains(&pos))
        {
            errors.push(format!(
                "step {i}: pivot {} not in expected polarities",
                step.pivot
            ));
            all.push(step.result.clone());
            continue;
        }
        let mut expected: Vec<i32> = left_c
            .iter()
            .chain(right_c.iter())
            .filter(|l| l.unsigned_abs() != pvar)
            .copied()
            .collect();
        expected.sort();
        expected.dedup();
        let mut actual = step.result.clone();
        actual.sort();
        actual.dedup();
        if actual != expected {
            errors.push(format!("step {i}: result mismatch"));
        } else {
            steps_ok += 1;
        }
        if step.result.is_empty() {
            derived_empty = true;
        }
        all.push(step.result.clone());
    }
    ProofVerifyResult {
        valid: errors.is_empty(),
        derived_empty,
        steps_verified: steps_ok,
        errors,
    }
}

/// Count derived steps in a standalone resolution proof.
#[must_use]
pub fn sep_resolution_proof_size(proof_steps: &[SepResolutionStep]) -> usize {
    proof_steps.len()
}

// ---------------------------------------------------------------------------
// Tree-to-DAG conversion
// ---------------------------------------------------------------------------

/// Convert tree-like resolution steps to DAG form (allowing clause reuse).
#[must_use]
pub fn tree_resolution_to_dag(
    tree_proof: &[SepTreeResStep],
    num_input: usize,
) -> Vec<SepResolutionStep> {
    let mut dag: Vec<SepResolutionStep> = Vec::new();
    for step in tree_proof {
        let li = tree_node_idx(&step.left, num_input, &dag);
        let ri = tree_node_idx(&step.right, num_input, &dag);
        let lc = clause_at_idx(li, num_input, &dag);
        let rc = clause_at_idx(ri, num_input, &dag);
        let pvar = step.pivot.unsigned_abs();
        let mut result: Vec<i32> = lc
            .iter()
            .chain(rc.iter())
            .filter(|l| l.unsigned_abs() != pvar)
            .copied()
            .collect();
        result.sort();
        result.dedup();
        dag.push(SepResolutionStep {
            left: li,
            right: ri,
            pivot: step.pivot,
            result,
        });
    }
    dag
}

fn tree_node_idx(node: &SepTreeNode, n: usize, dag: &[SepResolutionStep]) -> usize {
    match node {
        SepTreeNode::Leaf(idx) => *idx,
        SepTreeNode::Internal(step) => {
            let li = tree_node_idx(&step.left, n, dag);
            let ri = tree_node_idx(&step.right, n, dag);
            dag.iter()
                .enumerate()
                .find(|(_, ds)| ds.left == li && ds.right == ri && ds.pivot == step.pivot)
                .map_or(n + dag.len().saturating_sub(1), |(i, _)| n + i)
        }
    }
}

fn clause_at_idx(idx: usize, n: usize, dag: &[SepResolutionStep]) -> Vec<i32> {
    if idx < n {
        Vec::new()
    } else {
        dag.get(idx - n).map_or_else(Vec::new, |s| s.result.clone())
    }
}

// ---------------------------------------------------------------------------
// Haken lower bound witness
// ---------------------------------------------------------------------------

/// Construct witness for Haken's 2^{n/20} lower bound on PHP(n+1,n) resolution.
#[must_use]
pub fn haken_lower_bound_witness(n: usize) -> HakenWitness {
    let bound = 2.0_f64.powf(n as f64 / 20.0);
    let lb = if bound >= u64::MAX as f64 {
        u64::MAX
    } else {
        bound as u64
    };
    HakenWitness {
        n,
        tree_size_lower_bound: lb,
        description: format!(
            "Haken (1985): PHP({},{}) resolution lower bound 2^({}/20) = {:.2}. \
             CP upper bound: O(n^3) = {}.",
            n + 1,
            n,
            n,
            bound,
            php_cp_size_upper_bound(n)
        ),
    }
}

// ---------------------------------------------------------------------------
// Resolution → Cutting Planes simulation
// ---------------------------------------------------------------------------

/// Simulate a resolution proof step by step in the Cutting Planes system.
///
/// Each clause `(l1 v l2 v ... v lk)` is encoded as a linear inequality:
///   sum of x_i (for positive literals) + sum of (1 - x_j) (for negatives) >= 1
///
/// A resolution step on pivot variable p with clauses C1 (containing +p) and
/// C2 (containing -p) is simulated by adding the two inequalities and then
/// weakening (zeroing) the pivot variable coefficient.
///
/// This demonstrates that CP p-simulates Resolution: any resolution proof of
/// size S can be converted to a CP proof of size O(S).
///
/// Theorem (Cook, Coullard, Turan 1987): Cutting Planes p-simulates Resolution.
#[must_use]
pub fn simulate_resolution_in_cp(proof: &ResolutionProof) -> CuttingPlanesProof {
    use super::resolution::ResolutionStep;

    let mut cp_proof = CuttingPlanesProof::new();

    // Map from resolution step index to CP step index.
    let mut res_to_cp: Vec<usize> = Vec::new();

    for step in proof.steps() {
        match step {
            ResolutionStep::Input(clause) => {
                let ineq = clause_to_cp_inequality(clause);
                let idx = cp_proof.add_input(ineq);
                res_to_cp.push(idx);
            }
            ResolutionStep::Resolve { left, right, pivot } => {
                let left_cp = res_to_cp[*left];
                let right_cp = res_to_cp[*right];

                // Add the two inequalities.
                let sum_idx = cp_proof
                    .add(left_cp, right_cp)
                    .expect("CP add should succeed for valid resolution steps");

                // After addition, the pivot variable's coefficient should cancel.
                // However, when both clauses contain non-pivot literals that
                // contribute to the same variable's coefficient, the result may
                // have coefficients > rhs. Apply saturation to cap each
                // coefficient at the RHS value (valid for 0/1 variables), which
                // ensures the CP proof correctly simulates resolution.
                let sat_idx = cp_proof
                    .saturate(sum_idx)
                    .expect("CP saturate should succeed");
                res_to_cp.push(sat_idx);
            }
        }
    }

    cp_proof
}

/// Encode a clause as a pseudo-Boolean inequality for Cutting Planes.
///
/// Clause `(l1 v l2 v ... v lk)` becomes:
///   sum_i x_i (positive) + sum_j (1 - x_j) (negative) >= 1
///
/// Rearranging: sum_i x_i - sum_j x_j >= 1 - (number of negative literals)
fn clause_to_cp_inequality(clause: &[i32]) -> CpInequality {
    if clause.is_empty() {
        // Empty clause: 0 >= 1 (contradiction).
        return CpInequality::new(Vec::new(), 1);
    }

    // Determine the number of variables.
    let max_var = clause.iter().map(|l| l.unsigned_abs()).max().unwrap_or(0) as usize;
    let mut coeffs = vec![0i64; max_var];
    let mut rhs = 1i64;

    for &lit in clause {
        let var_idx = (lit.unsigned_abs() - 1) as usize;
        if lit > 0 {
            // Positive literal: contribute +x_i.
            coeffs[var_idx] += 1;
        } else {
            // Negative literal: contribute (1 - x_j).
            // So coefficient of x_j is -1, and rhs decreases by 1.
            coeffs[var_idx] -= 1;
            rhs -= 1;
        }
    }

    CpInequality::new(coeffs, rhs)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_system_ordering() {
        assert!(ProofSystem::TreeResolution < ProofSystem::Resolution);
        assert!(ProofSystem::Resolution < ProofSystem::CuttingPlanes);
        assert!(ProofSystem::CuttingPlanes < ProofSystem::ExtendedResolution);
        assert!(ProofSystem::ExtendedResolution < ProofSystem::Frege);
    }

    #[test]
    fn test_proof_system_names() {
        assert_eq!(ProofSystem::TreeResolution.name(), "Tree Resolution");
        assert_eq!(ProofSystem::CuttingPlanes.name(), "Cutting Planes");
        assert_eq!(ProofSystem::Frege.name(), "Frege");
    }

    #[test]
    fn test_strict_weakness_relations() {
        assert!(ProofSystem::TreeResolution.is_strictly_weaker_than(ProofSystem::Resolution));
        assert!(ProofSystem::Resolution.is_strictly_weaker_than(ProofSystem::CuttingPlanes));
        assert!(ProofSystem::TreeResolution.is_strictly_weaker_than(ProofSystem::CuttingPlanes));
        // CP << ExtRes is conjectured, not proven.
        assert!(
            !ProofSystem::CuttingPlanes.is_strictly_weaker_than(ProofSystem::ExtendedResolution)
        );
        // Same system is not strictly weaker.
        assert!(!ProofSystem::Resolution.is_strictly_weaker_than(ProofSystem::Resolution));
    }

    #[test]
    fn test_simulate_resolution_in_cp_simple() {
        // (1) AND (-1) => empty clause
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]);
        proof.add_input(vec![-1]);
        proof.add_resolve(0, 1, 1).expect("resolve");
        assert!(proof.verify());

        let cp = simulate_resolution_in_cp(&proof);
        // The CP proof should also derive a contradiction:
        // Input 0: x1 >= 1 (from clause [1])
        // Input 1: -x1 >= 0 (from clause [-1], i.e., 1-x1 >= 1 => -x1 >= 0)
        // Add: 0 >= 1 (contradiction)
        assert!(cp.verify());
    }

    #[test]
    fn test_simulate_resolution_in_cp_two_step() {
        // (1, 2) AND (-1, 2) AND (-2) => empty clause
        let mut proof = ResolutionProof::new();
        let a = proof.add_input(vec![1, 2]);
        let b = proof.add_input(vec![-1, 2]);
        let c = proof.add_resolve(a, b, 1).expect("resolve"); // => [2]
        let d = proof.add_input(vec![-2]);
        proof.add_resolve(c, d, 2).expect("resolve"); // => []
        assert!(proof.verify());

        let cp = simulate_resolution_in_cp(&proof);
        assert!(cp.verify());
    }

    #[test]
    fn test_simulate_resolution_in_cp_preserves_size() {
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]);
        proof.add_input(vec![-1]);
        proof.add_resolve(0, 1, 1).expect("resolve");

        let cp = simulate_resolution_in_cp(&proof);
        // 2 input axioms + 1 addition + 1 saturation = 4 steps
        assert_eq!(cp.len(), 4);
    }

    #[test]
    fn test_clause_to_cp_inequality_positive() {
        // Clause (x1 v x2): x1 + x2 >= 1
        let ineq = clause_to_cp_inequality(&[1, 2]);
        assert_eq!(ineq.coeffs, vec![1, 1]);
        assert_eq!(ineq.rhs, 1);
    }

    #[test]
    fn test_clause_to_cp_inequality_negative() {
        // Clause (-x1): (1 - x1) >= 1 => -x1 >= 0
        let ineq = clause_to_cp_inequality(&[-1]);
        assert_eq!(ineq.coeffs, vec![-1]);
        assert_eq!(ineq.rhs, 0);
    }

    #[test]
    fn test_clause_to_cp_inequality_mixed() {
        // Clause (x1 v -x2): x1 + (1 - x2) >= 1 => x1 - x2 >= 0
        let ineq = clause_to_cp_inequality(&[1, -2]);
        assert_eq!(ineq.coeffs, vec![1, -1]);
        assert_eq!(ineq.rhs, 0);
    }
}
