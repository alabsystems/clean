// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Discovery-specific prompt generation for LLM oracles.
//!
//! Builds prompts that ask LLMs to generate novel theorem statements with proofs
//! in the context of NN verification proof complexity, rather than the tactic-
//! focused prompts used by `clean-auto`'s oracle.

use crate::family::TheoremFamily;

/// A discovery prompt for an LLM oracle.
///
/// Contains the context and instructions needed for an LLM to generate
/// novel theorem-proof candidates in Lean 4 syntax.
#[derive(Debug, Clone)]
pub struct DiscoveryPrompt {
    /// The theorem family to generate candidates for.
    pub family: TheoremFamily,
    /// Number of candidates to request from the LLM.
    pub num_candidates: usize,
    /// Additional context declarations (existing axioms, types, etc.).
    pub context_decls: Vec<String>,
    /// Search-space constraints as natural language hints.
    pub constraints: Vec<String>,
}

impl DiscoveryPrompt {
    /// Create a new discovery prompt for the given theorem family.
    pub fn new(family: TheoremFamily) -> Self {
        Self {
            family,
            num_candidates: 4,
            context_decls: Vec::new(),
            constraints: Vec::new(),
        }
    }

    /// Set the number of candidates to request.
    pub fn with_num_candidates(mut self, n: usize) -> Self {
        self.num_candidates = n;
        self
    }

    /// Add a context declaration (shown to the LLM as background).
    pub fn with_context(mut self, decl: impl Into<String>) -> Self {
        self.context_decls.push(decl.into());
        self
    }

    /// Add a search-space constraint hint.
    pub fn with_constraint(mut self, constraint: impl Into<String>) -> Self {
        self.constraints.push(constraint.into());
        self
    }

    /// Format the prompt as a system message for the LLM.
    pub fn system_message(&self) -> String {
        format!(
            "You are a Lean 4 mathematician specializing in neural network verification \
             proof complexity. Generate novel theorem statements with proofs about {}. \
             Output each theorem in Lean 4 syntax as:\n\
             theorem <name> : <statement> := by\n  <proof tactics>\n\n\
             Separate multiple theorems with blank lines. \
             Do not include explanations or markdown formatting.",
            self.family
        )
    }

    /// Format the prompt as a user message for the LLM.
    ///
    /// Includes context declarations and constraints to guide generation.
    pub fn user_message(&self) -> String {
        let mut msg = String::with_capacity(1024);

        if !self.context_decls.is_empty() {
            msg.push_str("-- Available declarations:\n");
            for decl in &self.context_decls {
                msg.push_str("-- ");
                msg.push_str(decl);
                msg.push('\n');
            }
            msg.push('\n');
        }

        if !self.constraints.is_empty() {
            msg.push_str("-- Constraints:\n");
            for constraint in &self.constraints {
                msg.push_str("-- ");
                msg.push_str(constraint);
                msg.push('\n');
            }
            msg.push('\n');
        }

        msg.push_str(&format!(
            "Generate {} novel theorems about {} with complete proofs.\n",
            self.num_candidates, self.family
        ));

        msg.push_str(&family_hint(self.family));

        msg
    }

    /// Build an `OracleRequest` from this discovery prompt.
    pub fn to_oracle_request(&self) -> clean_auto::oracle::OracleRequest {
        clean_auto::oracle::OracleRequest::new(self.user_message())
            .with_candidates(self.num_candidates)
            .with_temperature(0.7)
            .with_max_tokens(4096)
    }
}

/// Family-specific generation hints for the LLM.
fn family_hint(family: TheoremFamily) -> String {
    match family {
        TheoremFamily::CertSizeBound => {
            "Focus on IBP certificate size bounds: relate ibp_cert_size to \
             network depth, width, and polynomial/exponential growth.\n\
             Key types: IBPCertificate, ibp_cert_size : IBPCertificate -> Nat\n\
             Example pattern: theorem cert_bound (c : IBPCertificate) (d w : Nat) : \
             ibp_cert_size c <= f(d, w) := by ..."
                .to_string()
        }
        TheoremFamily::DomainTightness => {
            "Focus on abstract domain tightness comparisons: zonotope vs DeepPoly \
             certificate sizes.\n\
             Key types: zonotope_cert_size, deep_poly_cert_size : Nat -> Nat\n\
             Example pattern: theorem tightness_ratio (n : Nat) : \
             zonotope_cert_size n <= k * deep_poly_cert_size n := by ..."
                .to_string()
        }
        TheoremFamily::VerificationComplexity => {
            "Focus on architecture-specific verification complexity bounds.\n\
             Key axioms: ibp_cert_plain_axiom, ibp_cert_skip_axiom, \
             ibp_cert_bottleneck_axiom, ibp_cert_residual_axiom\n\
             Example pattern: theorem arch_complexity (d w : Nat) (c : IBPCertificate) : \
             ibp_cert_size c <= d * w * w := by ..."
                .to_string()
        }
        TheoremFamily::NewAbstractDomain => {
            "Focus on novel abstract domain constructions and their certificate \
             size properties.\n\
             Key type: CertificateSize : Nat -> Nat (monotone)\n\
             Example pattern: theorem domain_composition (a b : Nat) : \
             CertificateSize (a + b) <= CertificateSize a + CertificateSize b := by ..."
                .to_string()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_discovery_prompt_system_message_contains_family() {
        let prompt = DiscoveryPrompt::new(TheoremFamily::CertSizeBound);
        let sys = prompt.system_message();
        assert!(sys.contains("CertSizeBound"));
        assert!(sys.contains("Lean 4"));
    }

    #[test]
    fn test_discovery_prompt_user_message_contains_context() {
        let prompt = DiscoveryPrompt::new(TheoremFamily::DomainTightness)
            .with_context("axiom foo : Nat -> Prop")
            .with_constraint("depth <= 5");
        let user = prompt.user_message();
        assert!(user.contains("axiom foo : Nat -> Prop"));
        assert!(user.contains("depth <= 5"));
        assert!(user.contains("DomainTightness"));
    }

    #[test]
    fn test_discovery_prompt_num_candidates() {
        let prompt = DiscoveryPrompt::new(TheoremFamily::CertSizeBound).with_num_candidates(8);
        assert_eq!(prompt.num_candidates, 8);
        let user = prompt.user_message();
        assert!(user.contains("8 novel theorems"));
    }

    #[test]
    fn test_discovery_prompt_to_oracle_request() {
        let prompt =
            DiscoveryPrompt::new(TheoremFamily::VerificationComplexity).with_num_candidates(3);
        let request = prompt.to_oracle_request();
        assert_eq!(request.num_candidates, 3);
        assert!(!request.goal.is_empty());
    }

    #[test]
    fn test_family_hint_all_families() {
        for family in [
            TheoremFamily::CertSizeBound,
            TheoremFamily::DomainTightness,
            TheoremFamily::VerificationComplexity,
            TheoremFamily::NewAbstractDomain,
        ] {
            let hint = family_hint(family);
            assert!(!hint.is_empty(), "hint should not be empty for {family}");
        }
    }
}
