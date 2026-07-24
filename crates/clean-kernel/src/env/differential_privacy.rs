// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Differential Privacy module for Environment
//!
//! This module formalizes differential privacy concepts essential for
//! verifying privacy-preserving algorithms in AI systems:
//! - Pure (ε-DP) and Approximate ((ε,δ)-DP) differential privacy
//! - Rényi DP (RDP) and zero-Concentrated DP (zCDP)
//! - Privacy mechanisms (Laplace, Gaussian, exponential)
//! - Composition theorems (sequential, parallel, advanced)
//! - Privacy amplification (subsampling, shuffling)
//! - Local differential privacy (LDP) and randomized response
//! - DP-SGD for private ML training
//! - Privacy accounting and budget management
//!
//! Motivations for AI/ML:
//! - Verify privacy guarantees of ML training pipelines
//! - Reason about composition of private queries
//! - Formalize privacy-utility trade-offs
//! - Enable certified private inference

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Differential Privacy module
    ///
    /// Differential privacy provides mathematical guarantees that an
    /// algorithm's output reveals limited information about any individual
    /// in the dataset. This module adds axioms for:
    /// - ε-DP, (ε,δ)-DP definitions and basic properties
    /// - Rényi and concentrated DP variants
    /// - Common mechanisms (Laplace, Gaussian, exponential)
    /// - Composition and post-processing theorems
    /// - Privacy amplification by subsampling
    /// - Local DP and shuffle model
    /// - DP-SGD for private ML training
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.differential_privacy_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_differential_privacy(&mut self) -> Result<(), EnvError> {
        if self.differential_privacy_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_rat()?;
        self.init_real_complex_analysis()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Differential privacy constants
        for name in &[
            // ================================================================
            // Basic Types and Definitions
            // ================================================================
            "DP.Database",          // Database type (collection of records)
            "DP.Record",            // Individual record type
            "DP.Adjacency",         // Adjacency relation (differ by 1 record)
            "DP.IsAdjacent",        // Predicate: D1 adjacent to D2
            "DP.HammingDistance",   // Number of differing records
            "DP.AddRemoveAdjacent", // Adjacency by add/remove
            "DP.SwapAdjacent",      // Adjacency by replacement
            "DP.Mechanism",         // Randomized mechanism M : Database → Prob Output
            "DP.Query",             // Deterministic query q : Database → Output
            "DP.Prob",              // Probability distribution type
            "DP.ProbDensity",       // Probability density function
            "DP.OutputSpace",       // Output space of mechanism
            "DP.MeasurableSet",     // Measurable subset of outputs
            // ================================================================
            // Pure Differential Privacy (ε-DP)
            // ================================================================
            "DP.Epsilon",        // Privacy parameter ε ≥ 0
            "DP.IsPureDP",       // M is ε-DP (pure DP)
            "DP.PureDPDef",      // ∀adj D1 D2, S. P[M(D1)∈S] ≤ e^ε P[M(D2)∈S]
            "DP.PureDPEquiv",    // Equivalent formulations of ε-DP
            "DP.PureDPMonotone", // Smaller ε implies stronger privacy
            "DP.ZeroDP",         // 0-DP = deterministic (no privacy)
            "DP.InfiniteDP",     // ∞-DP = no privacy guarantee
            // ================================================================
            // Approximate Differential Privacy ((ε,δ)-DP)
            // ================================================================
            "DP.Delta",             // Failure probability δ ≥ 0
            "DP.IsApproxDP",        // M is (ε,δ)-DP
            "DP.ApproxDPDef",       // P[M(D1)∈S] ≤ e^ε P[M(D2)∈S] + δ
            "DP.ApproxDPTail",      // Tail bound interpretation of δ
            "DP.PureImpliesApprox", // ε-DP implies (ε,0)-DP
            "DP.ApproxDPMonotone",  // Monotonicity in both ε and δ
            // ================================================================
            // Rényi Differential Privacy (RDP)
            // ================================================================
            "DP.RenyiDivergence", // Dα(P||Q) = (1/(α-1)) log E_Q[(P/Q)^α]
            "DP.RenyiOrder",      // Order α > 1
            "DP.IsRDP",           // M is (α,ρ)-RDP
            "DP.RDPDef",          // Dα(M(D1)||M(D2)) ≤ ρ for all adjacent
            "DP.RDPToApproxDP",   // Convert RDP to (ε,δ)-DP
            "DP.RDPComposition",  // RDP composes additively in ρ
            "DP.RDPOptimal",      // Optimal RDP → (ε,δ) conversion
            // ================================================================
            // Zero-Concentrated DP (zCDP)
            // ================================================================
            "DP.IsZCDP",          // M is ρ-zCDP
            "DP.ZCDPDef",         // ∀α>1: Dα ≤ ρα
            "DP.GaussianZCDP",    // Gaussian mech gives Δ²/(2σ²)-zCDP
            "DP.ZCDPToApprox",    // Convert zCDP to (ε,δ)-DP
            "DP.ZCDPComposition", // zCDP composes additively
            // ================================================================
            // Sensitivity
            // ================================================================
            "DP.Sensitivity",        // Global sensitivity of query
            "DP.L1Sensitivity",      // L1/Manhattan sensitivity Δ₁
            "DP.L2Sensitivity",      // L2/Euclidean sensitivity Δ₂
            "DP.LpSensitivity",      // General Lp sensitivity
            "DP.LocalSensitivity",   // Local sensitivity at specific DB
            "DP.SmoothSensitivity",  // Smooth upper bound on local sens
            "DP.BoundedSensitivity", // Query has bounded sensitivity
            // ================================================================
            // Mechanisms
            // ================================================================
            "DP.LaplaceMech",           // Add Lap(Δ/ε) noise
            "DP.LaplaceDP",             // Laplace mech is ε-DP
            "DP.GaussianMech",          // Add N(0, σ²Δ²) noise
            "DP.GaussianDP",            // Gaussian mech is (ε,δ)-DP
            "DP.ExponentialMech",       // Sample prop. to exp(εu(d,r)/(2Δu))
            "DP.ExponentialDP",         // Exponential mech is ε-DP
            "DP.ReportNoisyMax",        // Report argmax with noise
            "DP.AboveThreshold",        // Sparse vector technique
            "DP.SVTPrivacy",            // SVT privacy analysis
            "DP.SparseVectorTechnique", // General SVT
            // ================================================================
            // Composition Theorems
            // ================================================================
            "DP.SequentialComposition",    // k queries: sum of ε, sum of δ
            "DP.BasicComposition",         // (ε₁,δ₁) ∘ (ε₂,δ₂) = (ε₁+ε₂, δ₁+δ₂)
            "DP.AdvancedComposition",      // Better bound: √(2k ln(1/δ'))ε + k ε(e^ε-1)
            "DP.OptimalComposition",       // Kairouz-Oh-Viswanath tight bound
            "DP.ParallelComposition",      // Disjoint data: max(ε)
            "DP.ParallelDisjoint",         // Disjointness condition
            "DP.HeterogeneousComposition", // Different ε values compose
            // ================================================================
            // Post-Processing and Stability
            // ================================================================
            "DP.PostProcessing",    // Any f ∘ M preserves DP
            "DP.PostProcessDP",     // Post-processing theorem
            "DP.DataIndependent",   // Function independent of data
            "DP.GroupPrivacy",      // k-adjacent: kε privacy loss
            "DP.GroupPrivacyBound", // ε-DP implies kε for k-adjacent
            // ================================================================
            // Privacy Amplification
            // ================================================================
            "DP.SubsamplingAmplification", // Sample q fraction → amplify
            "DP.PoissonSubsampling",       // Poisson sampling each record
            "DP.UniformSubsampling",       // Uniform without replacement
            "DP.SubsamplingBound",         // ε → log(1 + q(e^ε - 1))
            "DP.ShuffleAmplification",     // Shuffle model amplification
            "DP.SecureAggregation",        // Secure aggregation amplifies
            "DP.AmplificationByIteration", // Privacy via contractive iterations
            // ================================================================
            // Local Differential Privacy
            // ================================================================
            "DP.IsLocalDP",          // Local randomizer R is ε-LDP
            "DP.LocalDPDef",         // P[R(x)∈S]/P[R(x')∈S] ≤ e^ε
            "DP.RandomizedResponse", // Basic LDP mechanism
            "DP.RRPrivacy",          // RR is ε-LDP
            "DP.LocalToGlobal",      // n users with ε-LDP → central DP
            "DP.FrequencyOracle",    // Frequency estimation via LDP
            "DP.HeavyHitters",       // Heavy hitter detection
            "DP.RAPPOR",             // Google's RAPPOR protocol
            "DP.ShuffleModel",       // Shuffle model of DP
            "DP.ShuffleAmplifies",   // Shuffling amplifies LDP
            // ================================================================
            // DP-SGD (Private ML Training)
            // ================================================================
            "DP.Gradient",             // Gradient type
            "DP.GradientClipping",     // Clip to L2 norm C
            "DP.ClipGradient",         // ∥clip(g, C)∥ ≤ C
            "DP.NoisyGradient",        // Add Gaussian noise to gradient
            "DP.DPSGDStep",            // One step of DP-SGD
            "DP.DPSGDMechanism",       // DP-SGD as a mechanism
            "DP.DPSGDPrivacy",         // Privacy of DP-SGD
            "DP.MomentsAccountant",    // Moments accountant for DP-SGD
            "DP.RDPAccountant",        // RDP-based accounting
            "DP.PRVAccountant",        // Privacy loss RV accountant
            "DP.NoisyGradientDescent", // NGD = DP-SGD without clipping
            "DP.PrivateFedAvg",        // Federated learning with DP
            // ================================================================
            // Privacy Accounting
            // ================================================================
            "DP.PrivacyBudget",   // Total budget (ε, δ)
            "DP.PrivacyOdometer", // Track spent budget
            "DP.CompositionRule", // Rule for combining budgets
            "DP.PLRDistribution", // Privacy loss random variable
            "DP.HockeyStickDiv",  // Hockey stick divergence
            "DP.PLRComposition",  // PLR composition theorem
            "DP.MomentsMethod",   // Moments-based accounting
            "DP.FDP",             // f-differential privacy
            "DP.GDP",             // GDP (Gaussian DP)
            // ================================================================
            // Privacy-Utility Trade-offs
            // ================================================================
            "DP.Accuracy",                  // Accuracy/utility of mechanism
            "DP.MeanSquaredError",          // MSE of DP query
            "DP.VarianceBound",             // Variance bounds for mechanisms
            "DP.OptimalMechanism",          // Optimal mechanism for given query
            "DP.LaplaceOptimal",            // Laplace optimal for L1 queries
            "DP.GaussianOptimal",           // Gaussian optimal for L2 queries
            "DP.InformationTheoreticLimit", // Fundamental limits
            "DP.FingerprinteringLower",     // Fingerprinting lower bounds
            "DP.PackingLower",              // Packing-based lower bounds
            // ================================================================
            // Connections to Other Areas
            // ================================================================
            "DP.MaxDivergence",        // Max-divergence D∞
            "DP.DPEquivMaxDiv",        // ε-DP iff D∞ ≤ ε
            "DP.DPImpliesIndist",      // DP implies statistical indist.
            "DP.MutualInformation",    // MI bound for DP mechanisms
            "DP.DPGeneralization",     // DP implies generalization
            "DP.AdaptiveDataAnalysis", // Avoid overfitting with DP
            "DP.Fairness",             // DP and algorithmic fairness
            "DP.DPPACAffinity",        // DP implies group fairness approx
            // ================================================================
            // Specific Applications
            // ================================================================
            "DP.PrivateHistogram", // DP histogram release
            "DP.PrivateMean",      // DP mean estimation
            "DP.PrivateQuantiles", // DP quantile estimation
            "DP.PrivateSelection", // DP selection (report noisy max)
            "DP.PrivateTopK",      // DP top-k selection
            "DP.PrivateCounting",  // DP counting queries
            "DP.PrivateSum",       // DP sum queries
            "DP.PrivateFrequency", // DP frequency estimation
            "DP.SyntheticData",    // DP synthetic data generation
        ] {
            let decl = Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            };
            self.add_decl(decl)?;
        }

        self.differential_privacy_init = true;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::test_helpers::assert_const;

    fn setup_env() -> Environment {
        let mut env = Environment::new();
        env.init_differential_privacy().unwrap();
        env
    }

    #[test]
    fn test_basic_types() {
        let env = setup_env();
        for s in ["DP.Database", "DP.Mechanism", "DP.Query", "DP.IsAdjacent"] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_pure_dp() {
        let env = setup_env();
        for s in ["DP.Epsilon", "DP.IsPureDP", "DP.PureDPDef"] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_approx_dp() {
        let env = setup_env();
        for s in [
            "DP.Delta",
            "DP.IsApproxDP",
            "DP.ApproxDPDef",
            "DP.PureImpliesApprox",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_rdp() {
        let env = setup_env();
        for s in ["DP.RenyiDivergence", "DP.IsRDP", "DP.RDPToApproxDP"] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_zcdp() {
        let env = setup_env();
        for s in ["DP.IsZCDP", "DP.GaussianZCDP", "DP.ZCDPComposition"] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_sensitivity() {
        let env = setup_env();
        for s in [
            "DP.Sensitivity",
            "DP.L1Sensitivity",
            "DP.L2Sensitivity",
            "DP.SmoothSensitivity",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_mechanisms() {
        let env = setup_env();
        for s in [
            "DP.LaplaceMech",
            "DP.GaussianMech",
            "DP.ExponentialMech",
            "DP.SparseVectorTechnique",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_composition() {
        let env = setup_env();
        for s in [
            "DP.SequentialComposition",
            "DP.BasicComposition",
            "DP.AdvancedComposition",
            "DP.ParallelComposition",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_post_processing() {
        let env = setup_env();
        for s in ["DP.PostProcessing", "DP.PostProcessDP", "DP.GroupPrivacy"] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_amplification() {
        let env = setup_env();
        for s in [
            "DP.SubsamplingAmplification",
            "DP.PoissonSubsampling",
            "DP.ShuffleAmplification",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_local_dp() {
        let env = setup_env();
        for s in ["DP.IsLocalDP", "DP.RandomizedResponse", "DP.ShuffleModel"] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_dp_sgd() {
        let env = setup_env();
        for s in [
            "DP.GradientClipping",
            "DP.DPSGDStep",
            "DP.DPSGDPrivacy",
            "DP.MomentsAccountant",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_privacy_accounting() {
        let env = setup_env();
        for s in [
            "DP.PrivacyBudget",
            "DP.PrivacyOdometer",
            "DP.PLRDistribution",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_applications() {
        let env = setup_env();
        for s in ["DP.PrivateHistogram", "DP.PrivateMean", "DP.SyntheticData"] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_differential_privacy_key_types_well_formed() {
        use crate::expr::ExprKind;
        use crate::level::Level;
        use crate::tc::TypeChecker;

        let env = setup_env();
        let tc = TypeChecker::new(&env);

        for name in &["DP.Database", "DP.Mechanism", "DP.Query"] {
            let n = Name::from_string(name);
            let ci = env.get_const(&n).expect(name);
            let levels: Vec<Level> = ci.level_params.iter().map(|_| Level::zero()).collect();
            let expr = Expr::const_(n, levels);
            let ty = tc
                .infer_type(&expr)
                .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
            assert!(
                matches!(&ty.kind, ExprKind::Sort(_)),
                "{name}: expected Sort type, got {ty:?}"
            );
        }
    }
}
