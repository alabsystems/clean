// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof step types and error definitions for SMT proof reconstruction.

use crate::smt::TermId;
use clean_kernel::{Expr, FVarId, Level};

/// Error type for proof reconstruction failures
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
#[non_exhaustive]
pub enum ProofReconstructionError {
    /// Assertion has no hypothesis proof and terms are not definitionally equal
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the hypothesis-free reconstruction path remains reserved for future proof-builder call sites"
        )
    )]
    #[error("missing hypothesis for assertion: term {lhs} = term {rhs}")]
    MissingHypothesis { lhs: TermId, rhs: TermId },
    /// Congruence step has no argument proofs (unexpected)
    #[error("congruence for {func} has no argument proofs")]
    EmptyCongruenceArgs { func: String },
    /// No proof path found between e-classes
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the no-path error remains reserved for future egraph proof-path plumbing"
        )
    )]
    #[error("no proof path from e-class {ec1} to e-class {ec2}")]
    NoProofPath { ec1: u32, ec2: u32 },
    /// Sort inference failed (no environment or TypeChecker::infer_sort failed)
    #[error("sort inference failed: {0}")]
    SortInferenceFailed(String),
    /// Term ID not found in term_to_expr or term_to_type mapping
    #[error("missing term mapping for {0}")]
    MissingTermMapping(TermId),
    /// No environment available for type inference
    #[error("no environment available")]
    NoEnvironment,
    /// Congruence universe level inference failed (function type is not a Pi)
    #[error("congruence inference failed for {func}: {reason}")]
    CongruenceInferenceFailed { func: String, reason: String },
    /// Cannot determine the equality span (lhs, rhs) of a proof step
    /// (e.g., Hypothesis without hyp_terms tracking, or Congr/Axiom steps)
    #[error("cannot determine equality span of proof step for {context}")]
    StepSpanUnknown { context: String },
}

/// A proof step in the SMT proof trace
#[derive(Debug, Clone, PartialEq)]
pub enum ProofStep {
    /// Reflexivity: a = a
    Refl(TermId),
    /// Symmetry: if we have proof of a = b, get b = a
    Symm(Box<ProofStep>),
    /// Transitivity: if we have a = b and b = c, get a = c
    Trans(Box<ProofStep>, Box<ProofStep>),
    /// Congruence: if args are equal, function applications are equal.
    /// Carries the function expression (preserving universe levels) and arg proofs.
    Congr(Expr, Vec<ProofStep>),
    /// Direct hypothesis assertion (hypothesis FVar ID)
    Hypothesis(FVarId),
    /// Unverified axiom - MUST be registered in the environment.
    /// This variant should only be used for axioms that are explicitly declared.
    /// Using this for arbitrary unverified assertions undermines soundness.
    /// Carries the axiom name and its universe level parameters.
    Axiom(String, Vec<Level>),
    /// Propositional proof reconstruction (#2442 Phase 1).
    /// Records the strategy used (e.g., "True.intro", "And.intro", "hypothesis_match").
    Propositional(String),
}

impl ProofStep {
    /// Create a reflexivity proof step
    pub fn refl(term: TermId) -> Self {
        ProofStep::Refl(term)
    }

    /// Create a symmetry proof step
    pub fn symm(proof: ProofStep) -> Self {
        // Optimize: symm(symm(p)) = p
        if let ProofStep::Symm(inner) = proof {
            return *inner;
        }
        // Optimize: symm(refl) = refl
        if let ProofStep::Refl(t) = &proof {
            return ProofStep::Refl(*t);
        }
        ProofStep::Symm(Box::new(proof))
    }

    /// Create a transitivity proof step
    pub fn trans(p1: ProofStep, p2: ProofStep) -> Self {
        // Optimize: trans(refl, p) = p
        if matches!(&p1, ProofStep::Refl(_)) {
            return p2;
        }
        // Optimize: trans(p, refl) = p
        if matches!(&p2, ProofStep::Refl(_)) {
            return p1;
        }
        ProofStep::Trans(Box::new(p1), Box::new(p2))
    }

    /// Create a congruence proof step with a function expression
    pub fn congr(func_expr: Expr, arg_proofs: Vec<ProofStep>) -> Self {
        ProofStep::Congr(func_expr, arg_proofs)
    }

    /// Create a hypothesis proof step
    pub fn hypothesis(fvar: FVarId) -> Self {
        ProofStep::Hypothesis(fvar)
    }
}
