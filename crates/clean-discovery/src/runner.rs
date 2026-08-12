// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Discovery runner: orchestrates candidate generation, kernel verification,
//! and result collection.
//!
//! The runner initializes the kernel environment with NN verification
//! declarations, generates candidates from the specified theorem families,
//! and verifies them using the `BatchVerifier`.
//!
//! Part of #3258.

use crate::abstract_domain::{self, AbstractDomainConfig};
use crate::candidate::CandidateTheorem;
use crate::complexity::{self, VerificationComplexityConfig};
use crate::error::DiscoveryError;
use crate::family::{self, CertSizeBoundConfig, TheoremFamily};
use crate::search::{ExhaustiveSearch, SearchResult};
use crate::tightness::{self, DomainTightnessConfig};
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};

/// Configuration for a discovery run.
#[derive(Debug, Clone)]
pub struct DiscoveryConfig {
    /// Which theorem families to search.
    pub families: Vec<TheoremFamily>,
    /// Configuration for CertSizeBound search (if that family is active).
    pub cert_size_config: CertSizeBoundConfig,
    /// Configuration for DomainTightness search (if that family is active).
    pub domain_tightness_config: DomainTightnessConfig,
    /// Configuration for VerificationComplexity search (if that family is active).
    pub complexity_config: VerificationComplexityConfig,
    /// Configuration for NewAbstractDomain search (if that family is active).
    pub abstract_domain_config: AbstractDomainConfig,
    /// Number of threads for parallel verification (None = rayon default).
    pub num_threads: Option<usize>,
}

impl Default for DiscoveryConfig {
    fn default() -> Self {
        Self {
            families: vec![TheoremFamily::CertSizeBound],
            cert_size_config: CertSizeBoundConfig::default(),
            domain_tightness_config: DomainTightnessConfig::default(),
            complexity_config: VerificationComplexityConfig::default(),
            abstract_domain_config: AbstractDomainConfig::default(),
            num_threads: None,
        }
    }
}

/// Results of a complete discovery run across all families.
#[derive(Debug)]
pub struct DiscoveryResults {
    /// Per-family search results.
    pub family_results: Vec<(TheoremFamily, SearchResult)>,
    /// Total candidates evaluated across all families.
    pub total_evaluated: u64,
    /// Total verified candidates across all families.
    pub total_verified: u64,
    /// Total wall-clock time in nanoseconds.
    pub total_wall_time_ns: u64,
}

/// The main discovery runner.
///
/// Owns the kernel environment and provides methods to run discovery
/// searches across theorem families.
pub struct DiscoveryRunner {
    env: Environment,
    config: DiscoveryConfig,
}

impl DiscoveryRunner {
    /// Create a new discovery runner with the given configuration.
    ///
    /// Initializes the kernel environment with all required NN verification
    /// declarations (Nat, ordering, proof complexity types and theorems).
    pub fn new(config: DiscoveryConfig) -> Result<Self, DiscoveryError> {
        let mut env = Environment::new();
        init_discovery_env(&mut env)?;
        Ok(Self { env, config })
    }

    /// Create a runner with a pre-initialized environment.
    ///
    /// Useful when the caller has already set up the environment with
    /// additional declarations.
    pub fn with_env(env: Environment, config: DiscoveryConfig) -> Self {
        Self { env, config }
    }

    /// Run discovery across all configured theorem families.
    ///
    /// Each candidate is GENUINELY verified: a candidate is counted as verified
    /// only when its proof term's inferred type is definitionally equal to its
    /// claimed statement (see [`ExhaustiveSearch::run`]). Candidates without a
    /// genuine proof are honestly reported as unverified.
    pub fn run(&self) -> Result<DiscoveryResults, DiscoveryError> {
        let wall_start = std::time::Instant::now();

        let mut family_results = Vec::new();
        let mut total_evaluated: u64 = 0;
        let mut total_verified: u64 = 0;

        for &fam in &self.config.families {
            let candidates = self.generate_candidates(fam)?;
            if candidates.is_empty() {
                return Err(DiscoveryError::NoCandidates {
                    family: fam.to_string(),
                });
            }

            let result = ExhaustiveSearch::run(&self.env, &candidates);
            total_evaluated += result.stats.total_evaluated;
            total_verified += result.stats.total_verified;
            family_results.push((fam, result));
        }

        let total_wall_time_ns = wall_start.elapsed().as_nanos() as u64;

        Ok(DiscoveryResults {
            family_results,
            total_evaluated,
            total_verified,
            total_wall_time_ns,
        })
    }

    /// Generate candidates for a single theorem family.
    fn generate_candidates(
        &self,
        family: TheoremFamily,
    ) -> Result<Vec<CandidateTheorem>, DiscoveryError> {
        match family {
            TheoremFamily::CertSizeBound => Ok(family::generate_cert_size_candidates(
                &self.config.cert_size_config,
            )),
            TheoremFamily::DomainTightness => Ok(tightness::generate_domain_tightness_candidates(
                &self.config.domain_tightness_config,
            )),
            TheoremFamily::VerificationComplexity => {
                Ok(complexity::generate_verification_complexity_candidates(
                    &self.config.complexity_config,
                ))
            }
            TheoremFamily::NewAbstractDomain => {
                Ok(abstract_domain::generate_abstract_domain_candidates(
                    &self.config.abstract_domain_config,
                ))
            }
        }
    }

    /// Access the underlying environment.
    pub fn env(&self) -> &Environment {
        &self.env
    }
}

/// Initialize the kernel environment with declarations needed for discovery.
///
/// Delegates to the kernel's `init_nn_verify_proof_complexity()` which
/// registers all NNVerify.ProofComplexity.* declarations (types, operations,
/// and theorems). Then registers discovery-specific axioms not in the kernel.
fn init_discovery_env(env: &mut Environment) -> Result<(), DiscoveryError> {
    env.init_nn_verify_proof_complexity()?;

    // Register architecture-specific axioms for VerificationComplexity family.
    // These are discovery-specific and not part of the kernel.
    register_architecture_axioms(env)?;

    // Register certificate size monotonicity axiom (used by NewAbstractDomain family)
    register_cert_size_monotone_axiom(env)?;

    Ok(())
}

/// Register architecture-specific axioms for the VerificationComplexity family.
fn register_architecture_axioms(env: &mut Environment) -> Result<(), DiscoveryError> {
    let nat = Expr::const_str("Nat");
    let ibp_cert_ref = Expr::const_str("NNVerify.ProofComplexity.IBPCertificate");
    let ibp_cert_size_ref = Expr::const_str("NNVerify.ProofComplexity.ibp_cert_size");
    let le_le = Expr::const_str_levels("LE.le", vec![clean_kernel::Level::zero()]);
    let inst_le_nat = Expr::const_str("instLENat");
    let nat_mul = Expr::const_str("Nat.mul");

    let cert_sz = Expr::app(ibp_cert_size_ref, Expr::bvar(0));
    let w_sq = Expr::apps(nat_mul.clone(), [Expr::bvar(1), Expr::bvar(1)]);
    let bound = Expr::apps(nat_mul, [Expr::bvar(2), w_sq]);
    let le_expr = Expr::apps(le_le, [nat.clone(), inst_le_nat, cert_sz, bound]);

    let axiom_ty = Expr::pi(BinderInfo::Default, ibp_cert_ref, le_expr);
    let axiom_ty = Expr::pi(BinderInfo::Default, nat.clone(), axiom_ty);
    let axiom_ty = Expr::pi(BinderInfo::Default, nat, axiom_ty);

    for suffix in &["plain", "skip", "bottleneck", "residual"] {
        register_if_missing(
            env,
            &format!("NNVerify.ProofComplexity.ibp_cert_{suffix}_axiom"),
            axiom_ty.clone(),
        )?;
    }

    Ok(())
}

/// Register the CertificateSize monotonicity axiom.
///
/// Type: `forall (a b : Nat),
///          LE.le @Nat instLENat a b ->
///          LE.le @Nat instLENat (CertificateSize a) (CertificateSize b)`
///
/// This axiom enables proofs about abstract domain certificate sizes by
/// composing input bounds with CertificateSize monotonicity.
fn register_cert_size_monotone_axiom(env: &mut Environment) -> Result<(), DiscoveryError> {
    let nat = Expr::const_str("Nat");
    let le_le = Expr::const_str_levels("LE.le", vec![clean_kernel::Level::zero()]);
    let inst_le_nat = Expr::const_str("instLENat");
    let cert_size = Expr::const_str("NNVerify.ProofComplexity.CertificateSize");

    // The premise is the type of the third binder, so only 2 binders above:
    // a = BVar(1), b = BVar(0)
    let premise = Expr::apps(
        le_le.clone(),
        [
            nat.clone(),
            inst_le_nat.clone(),
            Expr::bvar(1),
            Expr::bvar(0),
        ],
    );

    // The conclusion is the body of the third Pi, so 3 binders above:
    // a = BVar(2), b = BVar(1), proof = BVar(0)
    let cs_a = Expr::app(cert_size.clone(), Expr::bvar(2));
    let cs_b = Expr::app(cert_size, Expr::bvar(1));
    let conclusion = Expr::apps(le_le, [nat.clone(), inst_le_nat, cs_a, cs_b]);

    // forall (_ : LE.le a b), conclusion
    let body = Expr::pi(BinderInfo::Default, premise, conclusion);
    // forall (b : Nat), body
    let body = Expr::pi(BinderInfo::Default, nat.clone(), body);
    // forall (a : Nat), body
    let axiom_ty = Expr::pi(BinderInfo::Default, nat, body);

    register_if_missing(env, "NNVerify.ProofComplexity.cert_size_monotone", axiom_ty)
}

/// Register an axiom declaration if not already present.
fn register_if_missing(
    env: &mut Environment,
    name_str: &str,
    type_: Expr,
) -> Result<(), DiscoveryError> {
    let name = Name::from_string(name_str);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    env.add_decl(Declaration::Axiom {
        name,
        level_params: vec![],
        type_,
    })?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    #[test]
    fn test_discovery_runner_creation() {
        let config = DiscoveryConfig::default();
        let runner = DiscoveryRunner::new(config);
        assert!(runner.is_ok(), "runner creation should succeed");
    }

    #[test]
    fn test_init_discovery_env_registers_declarations() {
        let mut env = Environment::new();
        let result = init_discovery_env(&mut env);
        assert!(result.is_ok());

        assert!(
            env.get_const(&Name::from_string(
                "NNVerify.ProofComplexity.IBPCertificate"
            ))
            .is_some(),
            "IBPCertificate should be registered"
        );
        assert!(
            env.get_const(&Name::from_string("NNVerify.ProofComplexity.ibp_cert_size"))
                .is_some(),
            "ibp_cert_size should be registered"
        );
        assert!(
            env.get_const(&Name::from_string(
                "NNVerify.ProofComplexity.ibp_cert_polynomial_axiom"
            ))
            .is_some(),
            "ibp_cert_polynomial_axiom should be registered"
        );
    }

    #[test]
    fn test_init_discovery_env_idempotent() {
        let mut env = Environment::new();
        init_discovery_env(&mut env).expect("first init");
        init_discovery_env(&mut env).expect("second init should be idempotent");
    }

    #[test]
    fn test_discovery_run_cert_size_bound() {
        let config = DiscoveryConfig {
            families: vec![TheoremFamily::CertSizeBound],
            cert_size_config: CertSizeBoundConfig {
                max_depth: 2,
                max_width: 2,
                max_c: 1,
            },
            abstract_domain_config: AbstractDomainConfig::default(),
            num_threads: Some(1),
            ..DiscoveryConfig::default()
        };
        let runner = DiscoveryRunner::new(config).expect("runner creation");
        let results = runner.run().expect("discovery run");

        assert_eq!(results.total_evaluated, 16);
        assert!(results.total_wall_time_ns > 0);
    }

    #[test]
    fn test_discovery_results_structure() {
        let config = DiscoveryConfig {
            families: vec![TheoremFamily::CertSizeBound],
            cert_size_config: CertSizeBoundConfig {
                max_depth: 1,
                max_width: 1,
                max_c: 1,
            },
            abstract_domain_config: AbstractDomainConfig::default(),
            num_threads: Some(1),
            ..DiscoveryConfig::default()
        };
        let runner = DiscoveryRunner::new(config).expect("runner creation");
        let results = runner.run().expect("discovery run");

        assert_eq!(results.family_results.len(), 1);
        let (fam, ref search_result) = results.family_results[0];
        assert_eq!(fam, TheoremFamily::CertSizeBound);
        assert_eq!(search_result.outcomes.len() as u64, results.total_evaluated);
    }

    #[test]
    fn test_discovery_run_domain_tightness() {
        let config = DiscoveryConfig {
            families: vec![TheoremFamily::DomainTightness],
            domain_tightness_config: DomainTightnessConfig {
                max_ratio: 1,
                max_depth: 1,
                max_width: 2,
            },
            ..DiscoveryConfig::default()
        };
        let runner = DiscoveryRunner::new(config).expect("runner creation");
        let results = runner.run().expect("discovery run");

        assert_eq!(results.total_evaluated, 3);
        assert!(results.total_wall_time_ns > 0);
    }

    #[test]
    fn test_init_discovery_env_registers_tightness_declarations() {
        let mut env = Environment::new();
        init_discovery_env(&mut env).expect("env init");

        assert!(
            env.get_const(&Name::from_string(
                "NNVerify.ProofComplexity.zonotope_cert_size"
            ))
            .is_some(),
            "zonotope_cert_size should be registered"
        );
        assert!(
            env.get_const(&Name::from_string(
                "NNVerify.ProofComplexity.deep_poly_cert_size"
            ))
            .is_some(),
            "deep_poly_cert_size should be registered"
        );
        assert!(
            env.get_const(&Name::from_string(
                "NNVerify.ProofComplexity.cert_hierarchy_axiom"
            ))
            .is_some(),
            "cert_hierarchy_axiom should be registered"
        );
    }
}
