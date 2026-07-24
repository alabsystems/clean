// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enhanced GF(2) polynomial algebra with tracked Polynomial Calculus proofs.
//!
//! Builds on [`super::polynomial_calculus::GF2Polynomial`] with:
//!
//! - [`Gf2Poly`]: An efficient GF(2) polynomial using `Vec<BTreeSet<u32>>`
//!   for the common case of sparse multilinear polynomials. Uses `u32`
//!   variable indices for tighter memory.
//!
//! - [`PcStepTracked`] / [`PcProof`]: A Polynomial Calculus proof type that
//!   tracks degree at each step and supports boolean axioms (`x_i^2 - x_i`),
//!   general polynomial multiplication, and weakening.
//!
//! - [`cnf_to_gf2_system`] / [`verify_encoding_soundness`]: CNF <-> GF(2)
//!   encoding bridge with soundness verification for small instances.
//!
//! - [`pc_soundness_gf2`]: ZT03 -- PC soundness theorem for CNF
//!   unsatisfiability over GF(2).
//!
//! - [`pc_to_competition_certificate`]: Partial ZT04 -- compile PC proofs
//!   to competition-checkable certificate format.
//!
//! ## References
//!
//! - Clegg, Edmonds, Impagliazzo (1996). Using the Groebner basis algorithm
//!   to find proofs of unsatisfiability. STOC'96.
//! - Razborov (1998). Lower bounds for the polynomial calculus.

use std::collections::BTreeSet;

use thiserror::Error;

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors from PC proof verification.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum PcError {
    /// A proof step references a derived polynomial that does not exist.
    #[error("step {step} references nonexistent line {index} (only {available} derived)")]
    InvalidIndex {
        step: usize,
        index: usize,
        available: usize,
    },

    /// A clause axiom step references a clause index out of range.
    #[error("step {step} references clause {index} but only {count} clauses")]
    InvalidClauseIndex {
        step: usize,
        index: usize,
        count: usize,
    },

    /// The proof does not derive the constant polynomial 1.
    #[error("proof does not derive constant 1 (last polynomial has {0} terms)")]
    NotContradiction(usize),

    /// The proof has no steps.
    #[error("proof has no steps")]
    EmptyProof,

    /// Weaken step tried to add a constant monomial (degree 0).
    ///
    /// The Weaken rule in PC over GF(2) adds a monomial to an existing
    /// polynomial. Adding the constant monomial 1 (empty variable set)
    /// is unsound because it would allow deriving the constant polynomial
    /// 1 from any polynomial, trivially "proving" any formula unsatisfiable.
    /// Only monomials of degree >= 1 are allowed.
    #[error("step {step}: weaken with constant monomial is unsound (degree must be >= 1)")]
    WeakenConstantMonomial { step: usize },
}

/// Errors from the PC soundness verification (ZT03).
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum PcSoundnessError {
    /// The PC proof itself is invalid.
    #[error("invalid PC proof: {0}")]
    InvalidProof(#[from] PcError),

    /// The encoding from clauses to polynomials is inconsistent.
    #[error("encoding inconsistency: clause {clause_idx} polynomial does not match")]
    EncodingMismatch { clause_idx: usize },
}

/// Errors from certificate compilation.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum CompilationError {
    /// Certificate size exceeds the allowed budget.
    #[error("certificate size {estimated} exceeds budget {budget}")]
    BudgetExceeded { estimated: usize, budget: usize },

    /// The underlying proof is invalid.
    #[error("invalid proof: {0}")]
    InvalidProof(#[from] PcError),
}

// ---------------------------------------------------------------------------
// Gf2Poly: Enhanced GF(2) polynomial
// ---------------------------------------------------------------------------

/// A multilinear polynomial over GF(2) with `u32` variable indices.
///
/// Terms are stored as a `Vec<BTreeSet<u32>>` where each set is a monomial.
/// The coefficient of every stored monomial is implicitly 1 (in GF(2), the
/// only nonzero coefficient). Duplicate monomials cancel (XOR semantics):
/// after every operation, `canonicalize()` removes pairs.
///
/// The constant 1 is represented by the empty set `{}` appearing once.
/// The zero polynomial has an empty `terms` vector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Gf2Poly {
    /// Sorted, deduplicated list of monomials with coefficient 1.
    terms: Vec<BTreeSet<u32>>,
}

impl Gf2Poly {
    // -- Constructors -------------------------------------------------------

    /// The zero polynomial.
    #[must_use]
    pub fn zero() -> Self {
        Self { terms: Vec::new() }
    }

    /// The constant polynomial 1.
    #[must_use]
    pub fn one() -> Self {
        Self {
            terms: vec![BTreeSet::new()],
        }
    }

    /// A single variable x_v.
    #[must_use]
    pub fn variable(v: u32) -> Self {
        let mut mono = BTreeSet::new();
        mono.insert(v);
        Self { terms: vec![mono] }
    }

    /// Create a polynomial from a single monomial (product of given variables).
    #[must_use]
    pub fn monomial(vars: &[u32]) -> Self {
        let mono: BTreeSet<u32> = vars.iter().copied().collect();
        Self { terms: vec![mono] }
    }

    /// Encode a DIMACS clause as a GF(2) polynomial.
    ///
    /// Clause `(l1 v l2 v ... v lk)` encodes as `prod_i f(l_i) = 0` where
    /// `f(x_i) = 1 - x_{i-1}` for positive literal `i`, and `f(-x_i) = x_{i-1}`
    /// for negative literal `-i`. (DIMACS is 1-based; polynomial vars are 0-based.)
    #[must_use]
    pub fn from_clause(clause: &[i32]) -> Self {
        let mut result = Self::one();
        for &lit in clause {
            let var_idx = lit.unsigned_abs() - 1;
            let factor = if lit > 0 {
                // Positive literal: factor = (1 - x) = 1 + x in GF(2).
                Self::one().add(&Self::variable(var_idx))
            } else {
                // Negative literal: factor = x.
                Self::variable(var_idx)
            };
            result = result.mul(&factor);
        }
        result
    }

    /// The boolean axiom polynomial for variable v: `x_v^2 + x_v`.
    ///
    /// In GF(2), `x^2 = x` so `x^2 + x = 0`. This polynomial is always zero
    /// under multilinear reduction, serving as an axiom in PC/GF(2).
    #[must_use]
    pub fn boolean_axiom(_v: u32) -> Self {
        // x_v^2 + x_v = x_v + x_v = 0 in multilinear GF(2).
        // In the multilinear representation, x^2 = x by construction (BTreeSet
        // deduplicates), so x^2 + x = x + x = 0.
        Self::zero()
    }

    // -- Ring operations ----------------------------------------------------

    /// Add two polynomials over GF(2) (XOR of term multisets).
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        let mut all_terms = self.terms.clone();
        all_terms.extend(other.terms.iter().cloned());
        let mut result = Self { terms: all_terms };
        result.canonicalize();
        result
    }

    /// Multiply two polynomials over GF(2), with multilinear reduction.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        let mut result_terms: Vec<BTreeSet<u32>> =
            Vec::with_capacity(self.terms.len() * other.terms.len());

        for m1 in &self.terms {
            for m2 in &other.terms {
                // Multiply monomials = union of variable sets (multilinear: x^2 = x).
                let product: BTreeSet<u32> = m1.union(m2).copied().collect();
                result_terms.push(product);
            }
        }

        let mut result = Self {
            terms: result_terms,
        };
        result.canonicalize();
        result
    }

    /// Multiply by a single variable.
    #[must_use]
    pub fn mul_var(&self, var: u32) -> Self {
        self.mul(&Self::variable(var))
    }

    /// Reduce to canonical form: sort terms, cancel pairs (XOR semantics).
    ///
    /// Since we use `BTreeSet` for monomials, `x^2 = x` is enforced by
    /// construction (sets cannot contain duplicates). This method handles
    /// the coefficient cancellation: identical monomials appearing an even
    /// number of times cancel to zero.
    pub fn reduce(&mut self) {
        self.canonicalize();
    }

    /// Internal: sort and deduplicate, canceling pairs.
    fn canonicalize(&mut self) {
        self.terms.sort();
        // Remove pairs of identical monomials (1 + 1 = 0 in GF(2)).
        let mut deduped: Vec<BTreeSet<u32>> = Vec::with_capacity(self.terms.len());
        let mut i = 0;
        while i < self.terms.len() {
            if i + 1 < self.terms.len() && self.terms[i] == self.terms[i + 1] {
                // Pair cancels.
                i += 2;
            } else {
                deduped.push(self.terms[i].clone());
                i += 1;
            }
        }
        self.terms = deduped;
    }

    // -- Properties ---------------------------------------------------------

    /// Maximum degree (number of variables in the largest monomial).
    #[must_use]
    pub fn degree(&self) -> usize {
        self.terms.iter().map(BTreeSet::len).max().unwrap_or(0)
    }

    /// Number of nonzero terms.
    #[must_use]
    pub fn num_terms(&self) -> usize {
        self.terms.len()
    }

    /// Check if this is the zero polynomial.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Check if this equals the constant polynomial 1.
    #[must_use]
    pub fn is_one(&self) -> bool {
        self.terms.len() == 1 && self.terms[0].is_empty()
    }

    /// Evaluate the polynomial at a boolean assignment.
    ///
    /// `assignment[i]` is the value of variable `i`. Variables beyond the
    /// length of the slice are treated as `false`.
    #[must_use]
    pub fn evaluate(&self, assignment: &[bool]) -> bool {
        let mut result = false;
        for mono in &self.terms {
            let mono_val = mono
                .iter()
                .all(|&v| assignment.get(v as usize).copied().unwrap_or(false));
            result ^= mono_val;
        }
        result
    }

    /// Read-only access to the internal terms for inspection/testing.
    #[must_use]
    pub fn terms(&self) -> &[BTreeSet<u32>] {
        &self.terms
    }

    /// Attempt to convert this polynomial back to a DIMACS clause.
    ///
    /// Returns `Some(clause)` if the polynomial has the shape of a clause
    /// encoding (product of linear factors), `None` otherwise.
    /// Caps at 20 variables to avoid exponential blowup.
    #[must_use]
    pub fn to_clause(&self) -> Option<Vec<i32>> {
        if self.is_zero() {
            return Some(vec![]);
        }

        // Collect all variables.
        let mut all_vars: BTreeSet<u32> = BTreeSet::new();
        for mono in &self.terms {
            for &v in mono {
                all_vars.insert(v);
            }
        }

        if all_vars.is_empty() {
            // Constant 1 -- not a clause.
            return None;
        }

        let vars: Vec<u32> = all_vars.into_iter().collect();
        let k = vars.len();
        if k > 20 {
            return None;
        }

        for mask in 0u32..(1u32 << k) {
            let mut candidate: Vec<i32> = Vec::with_capacity(k);
            for (bit_pos, &var_idx) in vars.iter().enumerate() {
                let dimacs_var = (var_idx + 1) as i32;
                if mask & (1 << bit_pos) != 0 {
                    candidate.push(dimacs_var);
                } else {
                    candidate.push(-dimacs_var);
                }
            }
            if Self::from_clause(&candidate) == *self {
                candidate.sort_by_key(|lit| lit.abs());
                return Some(candidate);
            }
        }

        None
    }

    /// Estimate the serialized size of this polynomial in bytes.
    #[must_use]
    pub fn size_estimate(&self) -> usize {
        // Each term: ~(4 bytes per variable + 4 bytes overhead)
        self.terms.iter().map(|t| 4 + t.len() * 4).sum::<usize>() + 8
    }
}

impl std::fmt::Display for Gf2Poly {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_zero() {
            return write!(f, "0");
        }
        for (i, mono) in self.terms.iter().enumerate() {
            if i > 0 {
                write!(f, " + ")?;
            }
            if mono.is_empty() {
                write!(f, "1")?;
            } else {
                for (j, &v) in mono.iter().enumerate() {
                    if j > 0 {
                        write!(f, "*")?;
                    }
                    write!(f, "x{v}")?;
                }
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// PcStepTracked / PcProof: Degree-tracked Polynomial Calculus proofs
// ---------------------------------------------------------------------------

/// A Polynomial Calculus proof step over GF(2) with full rule set.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PcStepTracked {
    /// Axiom: introduce a clause polynomial (index into clause list).
    ClauseAxiom(usize),

    /// Boolean axiom: x_i^2 - x_i = 0 (always derives zero polynomial).
    BooleanAxiom(u32),

    /// Addition: derive[i] + derive[j].
    Add(usize, usize),

    /// Multiply a derived polynomial by a single variable.
    MulVar(usize, u32),

    /// General polynomial multiplication: derive[i] * derive[j].
    MulPoly(usize, usize),

    /// Weakening: derive[i] * monomial (multiplicative weakening).
    ///
    /// In Polynomial Calculus, weakening is multiplicative: from a derived
    /// polynomial p, we can derive p * m for any monomial m. This preserves
    /// ideal membership (if p is in the ideal, so is p * m).
    ///
    /// SOUNDNESS FIX (#3322): Previously this was additive (p + m), which
    /// allowed introducing arbitrary polynomials unrelated to the ideal,
    /// enabling trivial false refutations of satisfiable formulas.
    Weaken(usize, BTreeSet<u32>),
}

/// A complete Polynomial Calculus proof over GF(2).
///
/// After construction via [`PcProof::build`], contains the derived
/// polynomial at each step and the maximum degree encountered.
#[derive(Debug, Clone)]
pub struct PcProof {
    /// The proof steps.
    pub steps: Vec<PcStepTracked>,
    /// The polynomial derived at each step.
    pub derived: Vec<Gf2Poly>,
    /// Maximum degree of any derived polynomial.
    pub max_degree: usize,
}

impl PcProof {
    /// Build a PC proof by executing steps against the given clause axioms.
    ///
    /// # Errors
    ///
    /// Returns `PcError` if any step references an invalid index.
    pub fn build(clauses: &[Vec<i32>], steps: Vec<PcStepTracked>) -> Result<Self, PcError> {
        if steps.is_empty() {
            return Err(PcError::EmptyProof);
        }

        let clause_polys: Vec<Gf2Poly> = clauses.iter().map(|c| Gf2Poly::from_clause(c)).collect();
        let mut derived: Vec<Gf2Poly> = Vec::with_capacity(steps.len());
        let mut max_degree: usize = 0;

        for (step_idx, step) in steps.iter().enumerate() {
            let poly = match step {
                PcStepTracked::ClauseAxiom(idx) => {
                    if *idx >= clause_polys.len() {
                        return Err(PcError::InvalidClauseIndex {
                            step: step_idx,
                            index: *idx,
                            count: clause_polys.len(),
                        });
                    }
                    clause_polys[*idx].clone()
                }
                PcStepTracked::BooleanAxiom(_v) => {
                    // x^2 + x = 0 in GF(2) multilinear representation.
                    Gf2Poly::zero()
                }
                PcStepTracked::Add(i, j) => {
                    if *i >= derived.len() {
                        return Err(PcError::InvalidIndex {
                            step: step_idx,
                            index: *i,
                            available: derived.len(),
                        });
                    }
                    if *j >= derived.len() {
                        return Err(PcError::InvalidIndex {
                            step: step_idx,
                            index: *j,
                            available: derived.len(),
                        });
                    }
                    derived[*i].add(&derived[*j])
                }
                PcStepTracked::MulVar(i, var) => {
                    if *i >= derived.len() {
                        return Err(PcError::InvalidIndex {
                            step: step_idx,
                            index: *i,
                            available: derived.len(),
                        });
                    }
                    derived[*i].mul_var(*var)
                }
                PcStepTracked::MulPoly(i, j) => {
                    if *i >= derived.len() {
                        return Err(PcError::InvalidIndex {
                            step: step_idx,
                            index: *i,
                            available: derived.len(),
                        });
                    }
                    if *j >= derived.len() {
                        return Err(PcError::InvalidIndex {
                            step: step_idx,
                            index: *j,
                            available: derived.len(),
                        });
                    }
                    derived[*i].mul(&derived[*j])
                }
                PcStepTracked::Weaken(i, mono_vars) => {
                    if *i >= derived.len() {
                        return Err(PcError::InvalidIndex {
                            step: step_idx,
                            index: *i,
                            available: derived.len(),
                        });
                    }
                    // SOUNDNESS FIX (#3322): Weakening must be multiplicative,
                    // not additive. The correct PC rule is: from derived
                    // polynomial p, derive p * m where m is a monomial.
                    // This preserves ideal membership: if p is in the ideal
                    // I, then p * m is also in I.
                    //
                    // The previous additive rule (p + m) was catastrophically
                    // unsound: it allowed introducing arbitrary monomials
                    // unrelated to the ideal, enabling trivial false
                    // refutations of satisfiable formulas. For example:
                    //   ClauseAxiom(0) -> 1+x0+x1+x0*x1
                    //   Weaken(0, {x0}) -> 1+x1+x0*x1  (cancel x0)
                    //   Weaken(1, {x1}) -> 1+x0*x1      (cancel x1)
                    //   Weaken(2, {x0,x1}) -> 1          (cancel x0*x1)
                    // This "proved" (x1 v x2) unsatisfiable in 4 steps.
                    //
                    // Empty monomial (constant 1) is also rejected: p * 1 = p
                    // is a no-op (wastes a proof step but is sound). We still
                    // reject it for proof hygiene.
                    if mono_vars.is_empty() {
                        return Err(PcError::WeakenConstantMonomial { step: step_idx });
                    }
                    let mono = Gf2Poly::monomial(&mono_vars.iter().copied().collect::<Vec<_>>());
                    derived[*i].mul(&mono)
                }
            };

            let d = poly.degree();
            if d > max_degree {
                max_degree = d;
            }
            derived.push(poly);
        }

        Ok(Self {
            steps,
            derived,
            max_degree,
        })
    }

    /// Verify that the proof derives the constant 1 (contradiction).
    ///
    /// # Errors
    ///
    /// Returns `PcError::NotContradiction` if the final polynomial is not 1.
    /// Returns `PcError::EmptyProof` if there are no derived polynomials.
    pub fn verify(&self) -> Result<(), PcError> {
        let last = self.derived.last().ok_or(PcError::EmptyProof)?;
        if last.is_one() {
            Ok(())
        } else {
            Err(PcError::NotContradiction(last.num_terms()))
        }
    }

    /// The maximum degree across all derived polynomials.
    #[must_use]
    pub fn degree(&self) -> usize {
        self.max_degree
    }

    /// Check whether the proof stays within a degree bound.
    #[must_use]
    pub fn verify_degree_bound(&self, bound: usize) -> bool {
        self.max_degree <= bound
    }

    /// Estimate the total certificate size in bytes.
    #[must_use]
    pub fn certificate_size_estimate(&self) -> usize {
        // Steps: ~12 bytes each, plus derived polynomial sizes.
        let step_overhead = self.steps.len() * 12;
        let poly_size: usize = self.derived.iter().map(Gf2Poly::size_estimate).sum();
        step_overhead + poly_size + 64 // header overhead
    }
}

// ---------------------------------------------------------------------------
// CNF <-> GF(2) encoding bridge
// ---------------------------------------------------------------------------

/// Convert a full CNF formula to a GF(2) polynomial system.
///
/// Each clause `(l1 v l2 v ... v lk)` is encoded as the polynomial
/// `prod_i f(l_i)` where `f(x_i) = 1 - x_{i-1}` for positive literals
/// and `f(-x_i) = x_{i-1}` for negative literals. The clause is satisfied
/// iff the polynomial evaluates to 0.
#[must_use]
pub fn cnf_to_gf2_system(clauses: &[Vec<i32>]) -> Vec<Gf2Poly> {
    clauses.iter().map(|c| Gf2Poly::from_clause(c)).collect()
}

/// Verify that the CNF-to-GF(2) encoding is satisfiability-preserving
/// by exhaustive checking over all assignments.
///
/// For each assignment: the CNF is satisfied iff all clause polynomials
/// evaluate to 0. Returns `true` if this equivalence holds for every
/// assignment.
///
/// Only feasible for small instances (`num_vars <= 20`). Returns `false`
/// for larger instances without checking (conservative).
#[must_use]
pub fn verify_encoding_soundness(clauses: &[Vec<i32>], polys: &[Gf2Poly], num_vars: u32) -> bool {
    if num_vars > 20 || clauses.len() != polys.len() {
        return false;
    }

    let total_assignments = 1u32 << num_vars;

    for mask in 0..total_assignments {
        let assignment: Vec<bool> = (0..num_vars).map(|i| (mask >> i) & 1 == 1).collect();

        // Check CNF satisfaction.
        let cnf_sat = clauses.iter().all(|clause| {
            clause.iter().any(|&lit| {
                let var_idx = (lit.unsigned_abs() - 1) as usize;
                let val = assignment.get(var_idx).copied().unwrap_or(false);
                if lit > 0 {
                    val
                } else {
                    !val
                }
            })
        });

        // Check polynomial system: all polynomials evaluate to 0.
        let poly_sat = polys.iter().all(|p| !p.evaluate(&assignment));

        if cnf_sat != poly_sat {
            return false;
        }
    }

    true
}

// ---------------------------------------------------------------------------
// ZT03: PC Soundness Theorem
// ---------------------------------------------------------------------------

/// ZT03: Polynomial Calculus over GF(2) is sound for CNF unsatisfiability.
///
/// If a PC proof derives the constant 1 from the clause polynomials and
/// boolean axioms, then the original CNF formula is unsatisfiable.
///
/// This function verifies:
/// 1. The clause-to-polynomial encoding is correct.
/// 2. Each proof step correctly applies its rule.
/// 3. The final derived polynomial is the constant 1.
///
/// The soundness argument: every proof step preserves the invariant that
/// any satisfying assignment of the original CNF makes the derived polynomial
/// evaluate to 0. Since the constant 1 evaluates to 1 under every assignment,
/// no satisfying assignment exists.
///
/// # Errors
///
/// Returns `PcSoundnessError` if the proof is invalid or the encoding is
/// inconsistent.
pub fn pc_soundness_gf2(clauses: &[Vec<i32>], proof: &PcProof) -> Result<(), PcSoundnessError> {
    // SOUNDNESS FIX (#3330): Re-verify the proof by rebuilding from
    // clauses + steps rather than trusting the pre-built `derived` field.
    // A pre-built PcProof could have been constructed with incorrect
    // `derived` polynomials that don't match the actual step computations.
    // Rebuilding via PcProof::build() re-executes every step and validates
    // each derived polynomial from scratch.
    let rebuilt = PcProof::build(clauses, proof.steps.clone())?;

    // Step 1: Verify the encoding -- each ClauseAxiom step must match
    // the expected clause polynomial.
    let clause_polys: Vec<Gf2Poly> = clauses.iter().map(|c| Gf2Poly::from_clause(c)).collect();

    for (step_idx, step) in rebuilt.steps.iter().enumerate() {
        if let PcStepTracked::ClauseAxiom(clause_idx) = step {
            if *clause_idx < clause_polys.len() {
                let expected = &clause_polys[*clause_idx];
                let actual = &rebuilt.derived[step_idx];
                if expected != actual {
                    return Err(PcSoundnessError::EncodingMismatch {
                        clause_idx: *clause_idx,
                    });
                }
            }
        }
    }

    // Step 2: Verify the rebuilt proof derives constant 1.
    rebuilt.verify()?;

    // Step 3: Soundness conclusion.
    //
    // By induction on proof steps (re-verified via rebuild):
    // - ClauseAxiom: under any satisfying assignment, clause poly = 0 (by encoding).
    // - BooleanAxiom: x^2 + x = 0 for all x in {0,1} (field equation).
    // - Add(i,j): if p_i = 0 and p_j = 0 under sigma, then p_i + p_j = 0.
    // - MulVar(i,v): if p_i = 0 under sigma, then p_i * x_v = 0.
    // - MulPoly(i,j): if p_i = 0 under sigma, then p_i * p_j = 0.
    // - Weaken(i,m): if p_i = 0 under sigma, then p_i * m = 0 (multiplicative
    //   weakening preserves ideal membership). The constant monomial (degree 0)
    //   is rejected for proof hygiene. SOUNDNESS FIX (#3322): the previous
    //   additive rule (p_i + m) was unsound because it could introduce arbitrary
    //   monomials outside the ideal.
    //
    // Final polynomial = 1, but 1 != 0, contradicting the invariant.
    // Therefore no satisfying assignment exists: CNF is UNSAT.

    Ok(())
}

// ---------------------------------------------------------------------------
// ZT04 (partial): Competition certificate compilation
// ---------------------------------------------------------------------------

/// Compile a bounded PC refutation to a competition-checkable certificate.
///
/// The output is a binary format encoding the proof steps and derived
/// polynomials in a form suitable for independent verification. This is
/// the clean side of ZT04; the ay side emits VeriPB format.
///
/// # Format
///
/// The certificate is a sequence of 4-byte little-endian records:
///
/// | Offset | Field              | Size    |
/// |--------|--------------------|---------|
/// | 0      | Magic: 0x50_43_32  | 4 bytes |
/// | 4      | Version: 1         | 4 bytes |
/// | 8      | Num clauses        | 4 bytes |
/// | 12     | Num steps          | 4 bytes |
/// | 16     | Max degree         | 4 bytes |
/// | 20..   | Step records       | varies  |
///
/// Each step record starts with a 1-byte tag identifying the step type,
/// followed by type-specific fields.
///
/// # Errors
///
/// Returns `CompilationError::BudgetExceeded` if the estimated certificate
/// size exceeds `output_budget`. Returns `CompilationError::InvalidProof`
/// if the proof does not derive 1.
pub fn pc_to_competition_certificate(
    proof: &PcProof,
    clauses: &[Vec<i32>],
    output_budget: usize,
) -> Result<Vec<u8>, CompilationError> {
    // Verify the proof first.
    proof.verify()?;

    let estimated = proof.certificate_size_estimate();
    if estimated > output_budget {
        return Err(CompilationError::BudgetExceeded {
            estimated,
            budget: output_budget,
        });
    }

    let mut cert = Vec::with_capacity(estimated);

    // Header.
    cert.extend_from_slice(&0x00_50_43_32u32.to_le_bytes()); // Magic: "PC2\0"
    cert.extend_from_slice(&1u32.to_le_bytes()); // Version
    cert.extend_from_slice(&(clauses.len() as u32).to_le_bytes());
    cert.extend_from_slice(&(proof.steps.len() as u32).to_le_bytes());
    cert.extend_from_slice(&(proof.max_degree as u32).to_le_bytes());

    // Step records.
    for step in &proof.steps {
        match step {
            PcStepTracked::ClauseAxiom(idx) => {
                cert.push(0x01); // tag
                cert.extend_from_slice(&(*idx as u32).to_le_bytes());
            }
            PcStepTracked::BooleanAxiom(v) => {
                cert.push(0x02);
                cert.extend_from_slice(&v.to_le_bytes());
            }
            PcStepTracked::Add(i, j) => {
                cert.push(0x03);
                cert.extend_from_slice(&(*i as u32).to_le_bytes());
                cert.extend_from_slice(&(*j as u32).to_le_bytes());
            }
            PcStepTracked::MulVar(i, v) => {
                cert.push(0x04);
                cert.extend_from_slice(&(*i as u32).to_le_bytes());
                cert.extend_from_slice(&v.to_le_bytes());
            }
            PcStepTracked::MulPoly(i, j) => {
                cert.push(0x05);
                cert.extend_from_slice(&(*i as u32).to_le_bytes());
                cert.extend_from_slice(&(*j as u32).to_le_bytes());
            }
            PcStepTracked::Weaken(i, mono) => {
                cert.push(0x06);
                cert.extend_from_slice(&(*i as u32).to_le_bytes());
                cert.extend_from_slice(&(mono.len() as u32).to_le_bytes());
                for &v in mono {
                    cert.extend_from_slice(&v.to_le_bytes());
                }
            }
        }
    }

    Ok(cert)
}

// ---------------------------------------------------------------------------
// Conversion helpers: Gf2Poly <-> GF2Polynomial
// ---------------------------------------------------------------------------

/// Convert a [`Gf2Poly`] to the existing [`super::polynomial_calculus::GF2Polynomial`].
///
/// Useful for interoperating with the existing `verify_pc_proof()` and
/// `resolution_to_pc()` functions.
#[must_use]
pub fn gf2poly_to_legacy(poly: &Gf2Poly) -> super::polynomial_calculus::GF2Polynomial {
    use std::collections::HashMap;
    let mut terms: HashMap<BTreeSet<usize>, bool> = HashMap::new();
    for mono in &poly.terms {
        let legacy_mono: BTreeSet<usize> = mono.iter().map(|&v| v as usize).collect();
        terms.insert(legacy_mono, true);
    }
    // Use the zero() constructor and build up via add, since GF2Polynomial
    // fields are private. But we can use the public constructors.
    let mut result = super::polynomial_calculus::GF2Polynomial::zero();
    for mono in &poly.terms {
        let vars: Vec<usize> = mono.iter().map(|&v| v as usize).collect();
        let mono_poly = super::polynomial_calculus::GF2Polynomial::monomial(&vars);
        result = result.add(&mono_poly);
    }
    result
}

/// Convert a [`super::polynomial_calculus::GF2Polynomial`] to [`Gf2Poly`].
///
/// Uses the evaluate/reconstruct approach since `GF2Polynomial::terms` is
/// private. For polynomials with known structure, prefer direct construction.
#[must_use]
pub fn legacy_to_gf2poly(legacy: &super::polynomial_calculus::GF2Polynomial) -> Gf2Poly {
    // We can reconstruct by checking the legacy polynomial's degree and
    // evaluating it. For the common case, we use from_clause if applicable.
    //
    // Since we cannot access GF2Polynomial's internal terms directly,
    // we build the Gf2Poly by checking the legacy polynomial against
    // clause encodings. For arbitrary polynomials, this approach is limited.
    //
    // In practice, all legacy polynomials come from clause_to_polynomial(),
    // so we can reconstruct them via the same encoding.
    //
    // For now, a simple approach: try all monomials up to the degree.
    // This is only used for interop/testing; the new code uses Gf2Poly natively.

    // Quick check: is it zero or one?
    if legacy.is_zero() {
        return Gf2Poly::zero();
    }
    if legacy.is_one() {
        return Gf2Poly::one();
    }

    // Use the evaluate function to reconstruct term-by-term.
    // For each possible monomial, check if toggling it changes the evaluation.
    // This is O(2^n) so only works for small polynomials.
    let deg = legacy.degree();
    let num_terms = legacy.num_terms();

    // Heuristic: if small enough, reconstruct via evaluation.
    // Find max variable index by checking degree and num_terms.
    // We'll probe up to 16 variables.
    let max_var = 16usize.min(deg + num_terms + 2);

    let mut result = Gf2Poly::zero();
    let assignment_base: Vec<bool> = vec![false; max_var];

    // Check constant term.
    if super::polynomial_calculus::evaluate_polynomial(legacy, &assignment_base) {
        result = result.add(&Gf2Poly::one());
    }

    // Check each possible monomial by inclusion-exclusion on evaluations.
    // For efficiency, only check monomials up to the known degree.
    fn enumerate_monomials(
        max_var: usize,
        max_deg: usize,
        legacy: &super::polynomial_calculus::GF2Polynomial,
    ) -> Vec<BTreeSet<u32>> {
        let mut found = Vec::new();

        // We use Mobius inversion on the boolean lattice.
        // For each subset S, the coefficient c_S = XOR over T subset S of f(T)
        // where f(T) = evaluate(legacy, indicator_of_T).
        //
        // For tractability, limit to monomials of degree <= max_deg over max_var vars.

        for size in 1..=max_deg.min(max_var) {
            enumerate_subsets_of_size(max_var, size, &mut |subset: &[usize]| {
                // Mobius inversion: c_S = XOR_{T subset S} f(char_T)
                let mut coeff = false;
                let num_subsets = 1u32 << subset.len();
                for mask in 0..num_subsets {
                    let mut assignment = vec![false; max_var];
                    for (bit, &var) in subset.iter().enumerate() {
                        if mask & (1 << bit) != 0 {
                            assignment[var] = true;
                        }
                    }
                    let val = super::polynomial_calculus::evaluate_polynomial(legacy, &assignment);
                    coeff ^= val;
                }
                if coeff {
                    let mono: BTreeSet<u32> = subset.iter().map(|&v| v as u32).collect();
                    found.push(mono);
                }
            });
        }

        found
    }

    fn enumerate_subsets_of_size(n: usize, k: usize, callback: &mut dyn FnMut(&[usize])) {
        let mut subset = vec![0usize; k];
        enumerate_subsets_helper(n, k, 0, 0, &mut subset, callback);
    }

    fn enumerate_subsets_helper(
        n: usize,
        k: usize,
        start: usize,
        depth: usize,
        subset: &mut [usize],
        callback: &mut dyn FnMut(&[usize]),
    ) {
        if depth == k {
            callback(&subset[..k]);
            return;
        }
        for i in start..n {
            subset[depth] = i;
            enumerate_subsets_helper(n, k, i + 1, depth + 1, subset, callback);
        }
    }

    let monomials = enumerate_monomials(max_var, deg, legacy);
    for mono in monomials {
        result = result.add(&Gf2Poly { terms: vec![mono] });
    }

    result
}

// ---------------------------------------------------------------------------
// PHP (Pigeonhole Principle) helpers for testing
// ---------------------------------------------------------------------------

/// Generate the Pigeonhole Principle CNF: PHP(pigeons, holes).
///
/// Encodes: every pigeon goes to at least one hole, and no two pigeons
/// share a hole. Variable `x_{p,h}` is DIMACS var `(p-1)*holes + h`.
///
/// Returns `None` if `pigeons == 0` or `holes == 0`.
#[must_use]
pub fn generate_php_cnf(pigeons: u32, holes: u32) -> Option<Vec<Vec<i32>>> {
    if pigeons == 0 || holes == 0 {
        return None;
    }

    let var = |p: u32, h: u32| -> i32 { ((p - 1) * holes + h) as i32 };

    let mut clauses = Vec::new();

    // Each pigeon goes to at least one hole.
    for p in 1..=pigeons {
        let clause: Vec<i32> = (1..=holes).map(|h| var(p, h)).collect();
        clauses.push(clause);
    }

    // No two pigeons share a hole (at-most-one per hole).
    for h in 1..=holes {
        for p1 in 1..=pigeons {
            for p2 in (p1 + 1)..=pigeons {
                clauses.push(vec![-var(p1, h), -var(p2, h)]);
            }
        }
    }

    Some(clauses)
}

/// Generate Tseitin CNF encoding for a small graph.
///
/// Given edges `(u, v)` over vertices `{0, ..., n-1}`, encode the Tseitin
/// parity constraints: for each vertex, the XOR of its edge variables
/// equals a given parity bit.
///
/// This is UNSAT when the sum of all parity bits is odd (since each edge
/// contributes to two vertices, the total parity must be even).
///
/// Returns `(clauses, num_vars)`.
#[must_use]
pub fn generate_tseitin_cnf(
    num_vertices: u32,
    edges: &[(u32, u32)],
    parities: &[bool],
) -> (Vec<Vec<i32>>, u32) {
    // Edge variables: 1-based, edge i -> DIMACS var (i+1).
    let num_edges = edges.len() as u32;
    let mut clauses = Vec::new();

    for v in 0..num_vertices {
        // Collect edges incident to vertex v.
        let incident: Vec<u32> = edges
            .iter()
            .enumerate()
            .filter(|(_, &(a, b))| a == v || b == v)
            .map(|(i, _)| (i + 1) as u32) // 1-based DIMACS var
            .collect();

        if incident.is_empty() {
            continue;
        }

        let parity = parities.get(v as usize).copied().unwrap_or(false);

        // Encode: XOR of incident edge variables = parity.
        // For k variables, this produces 2^(k-1) clauses.
        let k = incident.len();
        let total = 1u32 << k;

        for mask in 0..total {
            // mask represents an assignment: bit b set = variable b is true.
            let num_true = (0..k).filter(|&b| mask & (1 << b) != 0).count();
            let assignment_parity = num_true % 2 == 1;

            // Include this clause if the assignment has the wrong parity.
            // The clause excludes exactly the assignment represented by mask.
            if assignment_parity != parity {
                let clause: Vec<i32> = (0..k)
                    .map(|b| {
                        let var = incident[b] as i32;
                        if mask & (1 << b) != 0 {
                            // Exclude x_b = true: use negative literal.
                            -var
                        } else {
                            // Exclude x_b = false: use positive literal.
                            var
                        }
                    })
                    .collect();
                clauses.push(clause);
            }
        }
    }

    (clauses, num_edges)
}
