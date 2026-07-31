// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Causal Inference module for Environment
//!
//! This module formalizes structural causal models and identification theory:
//! - Causal graphs (DAGs, CPDAGs, MAGs) and assumptions (Markov + faithfulness)
//! - Interventions, do-calculus, and identification (ID algorithm)
//! - Adjustment criteria (backdoor, frontdoor) and instrumental variables
//! - Counterfactuals and potential outcomes
//! - Causal discovery algorithms (PC/FCI/GES) and robustness
//! - Fairness and distribution shift via causal reasoning
//!
//! Motivations for AI/ML:
//! - Formalize interventions for policy learning and evaluation
//! - Reason about domain shifts and transportability
//! - Verify fairness constraints via counterfactual definitions
//! - Provide axioms for causal discovery and identifiability proofs

#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::Expr;
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
impl Environment {
    /// Initialize Causal Inference module
    ///
    /// Structural causal models (SCMs) capture how interventions change
    /// distributions. This module adds axioms for:
    /// - Graphical models (DAG/CPDAG/MAG) and separations
    /// - Do-calculus rules and identification algorithms
    /// - Adjustment criteria (backdoor/frontdoor/IV)
    /// - Counterfactual semantics (potential outcomes)
    /// - Fairness constraints and robustness under shift
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.causal_inference_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_causal_inference(&mut self) -> Result<(), EnvError> {
        if self.causal_inference_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_rat()?;
        self.init_set_theory()?;
        self.init_measure_theory()?;
        self.init_list()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Causal inference constants
        for name in &[
            // ================================================================
            // Structural Causal Models (SCMs)
            // ================================================================
            "Causal.Variable",                // Random variable in SCM
            "Causal.ExogenousVar",            // Exogenous noise variable U
            "Causal.EndogenousVar",           // Endogenous variable V
            "Causal.StructuralEquation",      // Equation V := f(pa(V), U_V)
            "Causal.StructuralModel",         // Collection of structural equations
            "Causal.CausalGraph",             // Graph over variables (with latents)
            "Causal.DAG",                     // Directed acyclic graph
            "Causal.CPDAG",                   // Completed partially directed acyclic graph
            "Causal.MaximalAncestralGraph",   // MAG for latent confounding
            "Causal.LatentVariable",          // Hidden/unobserved variable
            "Causal.SelectionVariable",       // Selection bias indicator
            "Causal.MarkovCondition",         // Global Markov property for DAG
            "Causal.Faithfulness",            // No cancellations of independences
            "Causal.CausalSufficiency",       // No unmeasured confounders
            "Causal.MarkovEquivalence",       // Same conditional independences
            "Causal.MarkovBlanket",           // Parents, children, co-parents
            "Causal.Independence",            // X ⟂ Y
            "Causal.ConditionalIndependence", // X ⟂ Y | Z
            "Causal.dSeparation",             // Graphical separation in DAG
            "Causal.mSeparation",             // Separation in MAG
            // ================================================================
            // Interventions and Do-Calculus
            // ================================================================
            "Causal.Intervention",                 // do(X := x)
            "Causal.HardIntervention",             // Replace equation
            "Causal.SoftIntervention",             // Modify mechanism softly
            "Causal.AtomicIntervention",           // Intervention on single variable
            "Causal.DoOperator",                   // do(·) operator
            "Causal.DoDistribution",               // P(Y | do(X))
            "Causal.PostInterventionDistribution", // Distribution after intervention
            "Causal.TruncatedFactorization",       // Factorization under intervention
            "Causal.GFormula",                     // G-formula / g-computation
            "Causal.Identifiability",              // P(Y|do(X)) identified from P(V)
            "Causal.DoCalculusRule1",              // Insertion/deletion of observations
            "Causal.DoCalculusRule2",              // Action/observation exchange
            "Causal.DoCalculusRule3",              // Insertion/deletion of actions
            "Causal.DoCalculusSound",              // Do-calculus rules soundness
            "Causal.DoCalculusComplete",           // Do-calculus completeness
            "Causal.IDAlgorithm",                  // Identification (ID) algorithm
            "Causal.IDComplete",                   // ID algorithm completeness for DAGs
            "Causal.SelectionDiagram",             // Graph encoding selection bias
            "Causal.Transportability",             // Transport causal effects across domains
            "Causal.TransportFormula",             // S-transport formula
            // ================================================================
            // Adjustment and Identification
            // ================================================================
            "Causal.BackdoorPath",         // Path with arrow into treatment
            "Causal.BackdoorCriterion",    // Z blocks backdoor paths and is not descendant
            "Causal.ValidAdjustmentSet",   // Z satisfies backdoor criterion
            "Causal.AdjustmentFormula",    // P(Y|do(X)) = Σ_z P(Y|X,z)P(z)
            "Causal.MinimalAdjustment",    // Minimal sufficient adjustment set
            "Causal.BackdoorATE",          // ATE identified via backdoor
            "Causal.FrontdoorCriterion",   // Mediator meets frontdoor conditions
            "Causal.FrontdoorAdjustment",  // Frontdoor identification formula
            "Causal.FrontdoorATE",         // ATE identified via frontdoor
            "Causal.Mediator",             // Mediating variable M
            "Causal.MediationFormula",     // Decomposition via mediator
            "Causal.InstrumentalVariable", // Z affects X, independent of Y|do(X)
            "Causal.IVAssumptions",        // Relevance + exclusion + independence
            "Causal.IVIdentification",     // Identify causal effect via IV
            "Causal.Monotonicity",         // No defiers (LATE assumption)
            "Causal.ComplianceClass",      // Complier/always-taker/never-taker/defier
            "Causal.LATE",                 // Local average treatment effect
            "Causal.ComplierATE",          // Effect on compliers
            "Causal.TwoStageLeastSquares", // 2SLS estimator for linear IV
            // ================================================================
            // Effects and Estimators
            // ================================================================
            "Causal.AverageTreatmentEffect",      // E[Y1 - Y0]
            "Causal.ConditionalATE",              // Conditional ATE (CATE)
            "Causal.TotalEffect",                 // Total causal effect
            "Causal.DirectEffect",                // Controlled direct effect
            "Causal.NaturalDirectEffect",         // NDE = E[Yx,Mx*] - E[Yx*,Mx*]
            "Causal.NaturalIndirectEffect",       // NIE = E[Yx,Mx] - E[Yx,Mx*]
            "Causal.ControlledDirectEffect",      // Fix mediator value
            "Causal.MarginalStructuralModel",     // MSM with stabilized weights
            "Causal.PropensityScore",             // e(X) = P(T=1|X)
            "Causal.PropensityScoreWeighting",    // IPTW using e(X)
            "Causal.PropensityScoreMatching",     // Matching on propensity score
            "Causal.InverseProbabilityWeighting", // IPW estimator
            "Causal.DoublyRobustEstimator",       // AIPW estimator
            "Causal.TargetedMLE",                 // TMLE estimator
            "Causal.GEstimation",                 // G-estimation of structural models
            "Causal.StabilizedWeights",           // Stabilized IPW weights
            "Causal.BalancingScores",             // Functions balancing covariates
            "Causal.SensitivityAnalysis",         // Assess sensitivity to unmeasured confounding
            "Causal.BoundingApproach",            // Bounds on causal effects
            // ================================================================
            // Counterfactuals and Potential Outcomes
            // ================================================================
            "Causal.PotentialOutcome",        // Y_x potential outcome
            "Causal.ConsistencyAxiom",        // If X=x then Y=Y_x
            "Causal.SUTVA",                   // Stable unit treatment value assumption
            "Causal.CrossWorldIndependence", // Independence across worlds (sequential ignorability)
            "Causal.Counterfactual",         // Counterfactual query
            "Causal.NestedCounterfactual",   // Sequential counterfactuals
            "Causal.CrossWorldEquality",     // Y_{x,m} = Y_{x',m} under assumptions
            "Causal.PNS",                    // Probability of necessity and sufficiency
            "Causal.PN",                     // Probability of necessity
            "Causal.PS",                     // Probability of sufficiency
            "Causal.RubinCausalModel",       // Potential outcomes framework
            "Causal.PrincipalStratification", // Stratification on post-treatment variables
            "Causal.MediationAssumptions",   // Assumptions for NDE/NIE identification
            // ================================================================
            // Causal Discovery and Robustness
            // ================================================================
            "Causal.CausalDiscovery", // Problem of recovering causal graph
            "Causal.PCAlgorithm",     // Constraint-based discovery for DAGs
            "Causal.FCIAlgorithm",    // Discovery with latent confounders
            "Causal.GESAlgorithm",    // Score-based greedy equivalence search
            "Causal.ScoreBasedLearning", // Maximize score over DAGs
            "Causal.ConstraintBasedLearning", // Learn independences to orient edges
            "Causal.InterventionalDiscovery", // Use interventions to orient edges
            "Causal.LiNGAM",          // Linear non-Gaussian acyclic model
            "Causal.InvariantCausalPrediction", // Invariant conditional distributions across environments
            "Causal.CausalOrdering",            // Topological ordering of DAG
            "Causal.CausalSkeleton",            // Undirected skeleton of causal graph
            "Causal.StabilityAssumption",       // Invariance across environments
            "Causal.DomainShiftAdjustment",     // Correct for covariate shift via causality
            // ================================================================
            // Fairness and Policy Evaluation
            // ================================================================
            "Causal.CounterfactualFairness", // Decision invariant across counterfactual worlds
            "Causal.EqualizedOdds",          // Fairness via equalized odds
            "Causal.EqualOpportunity",       // Fairness via equal opportunity
            "Causal.DemographicParity",      // Fairness via demographic parity
            "Causal.FairnessIntervention",   // Intervening to enforce fairness
            "Causal.CausalFairnessConstraints", // Graph-based fairness constraints
            "Causal.CausalBandit",           // Bandits with causal structure
            "Causal.OffPolicyEvaluation",    // Evaluate policies using causal assumptions
            "Causal.PolicyIdentification",   // Identify optimal policy via SCM
            "Causal.CausalReinforcementLearning", // RL leveraging causal structure
            // ================================================================
            // Fundamental Theorems and Guarantees
            // ================================================================
            "Causal.do_calculus_completeness_theorem", // Do-calculus identifies all identifiable effects
            "Causal.backdoor_adjustment_soundness",    // Backdoor adjustment yields P(Y|do(X))
            "Causal.frontdoor_identifiability_theorem", // Frontdoor identifies causal effect
            "Causal.iv_identifiability_theorem",       // IV identifies LATE under assumptions
            "Causal.transportability_soundness",       // Transport formula soundness
            "Causal.counterfactual_identifiability_theorem", // Counterfactuals identified under assumptions
            "Causal.doubly_robust_consistency", // AIPW/TMLE consistent if either model correct
            "Causal.ate_identifiable_via_backdoor", // ATE identified when valid adjustment exists
            "Causal.frontdoor_effect_formula",  // Effect computed via mediator expectations
            "Causal.fci_sound_complete_partial_ancestral", // FCI sound/complete for PAGs
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.causal_inference_init = true;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::test_helpers::assert_const;

    #[test]
    fn test_causal_inference_init() {
        let mut env = Environment::new();
        env.init_causal_inference().unwrap();
        assert!(env.causal_inference_init);
    }

    #[test]
    fn test_causal_inference_idempotent() {
        let mut env = Environment::new();
        env.init_causal_inference().unwrap();
        env.init_causal_inference().unwrap();
        assert!(env.causal_inference_init);
    }

    #[test]
    fn test_do_calculus_constants_exist() {
        let mut env = Environment::new();
        env.init_causal_inference().unwrap();

        assert_const(&env, "Causal.DoCalculusRule1");
        assert_const(&env, "Causal.DoCalculusRule2");
        assert_const(&env, "Causal.DoCalculusRule3");
        assert_const(&env, "Causal.IDAlgorithm");
    }

    #[test]
    fn test_adjustment_concepts_exist() {
        let mut env = Environment::new();
        env.init_causal_inference().unwrap();

        for name in &[
            "Causal.BackdoorCriterion",
            "Causal.FrontdoorAdjustment",
            "Causal.InstrumentalVariable",
            "Causal.DoublyRobustEstimator",
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("Missing adjustment constant: {name}"));
            assert_eq!(
                info.name.to_string(),
                *name,
                "constant name mismatch for {name}"
            );
        }
    }

    #[test]
    fn test_counterfactual_concepts_exist() {
        let mut env = Environment::new();
        env.init_causal_inference().unwrap();

        let potential = Name::from_string("Causal.PotentialOutcome");
        let sutva = Name::from_string("Causal.SUTVA");
        let pn = Name::from_string("Causal.PN");
        let pot_info = env
            .get_const(&potential)
            .expect("Missing Causal.PotentialOutcome");
        assert_eq!(pot_info.name, potential);
        let sutva_info = env.get_const(&sutva).expect("Missing Causal.SUTVA");
        assert_eq!(sutva_info.name, sutva);
        let pn_info = env.get_const(&pn).expect("Missing Causal.PN");
        assert_eq!(pn_info.name, pn);
    }

    #[test]
    fn test_fairness_and_policy_constants_exist() {
        let mut env = Environment::new();
        env.init_causal_inference().unwrap();

        let fairness = [
            "Causal.CounterfactualFairness",
            "Causal.EqualizedOdds",
            "Causal.OffPolicyEvaluation",
            "Causal.CausalReinforcementLearning",
        ];

        for name in fairness {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("Missing fairness constant: {name}"));
            assert_eq!(
                info.name.to_string(),
                name,
                "constant name mismatch for {name}"
            );
        }
    }

    #[test]
    fn test_causal_inference_dependencies() {
        let mut env = Environment::new();
        env.init_causal_inference().unwrap();

        assert!(env.eq_init);
        assert!(env.nat_init);
        assert!(env.rat_init);
        assert!(env.set_theory_init);
        assert!(env.measure_theory_init);
        assert!(env.list_init);
    }

    #[test]
    fn test_causal_key_types_well_formed() {
        use crate::expr::ExprKind;
        use crate::level::Level;
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_causal_inference().unwrap();
        let tc = TypeChecker::new(&env);

        for name in &[
            "Causal.Variable",
            "Causal.DoOperator",
            "Causal.Identifiability",
            "Causal.PotentialOutcome",
        ] {
            let expr = Expr::const_(Name::from_string(name), vec![Level::zero()]);
            let ty = tc
                .infer_type(&expr)
                .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
            assert!(
                matches!(&ty.kind, ExprKind::Sort(_)),
                "{name}: expected Sort type, got {ty:?}"
            );
        }

        // Verify universe level params
        let var_info = env
            .get_const(&Name::from_string("Causal.Variable"))
            .expect("Causal.Variable");
        assert!(
            !var_info.level_params.is_empty(),
            "Causal.Variable should have universe parameters"
        );
    }
}
