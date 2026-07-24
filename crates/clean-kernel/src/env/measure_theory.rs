// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Measure theory structures for Environment
//!
//! This module contains measure theory initialization:
//! - Sigma-algebras: collections closed under countable operations
//! - Measurable spaces: sets with sigma-algebra structure
//! - Measures: countably additive set functions
//! - Integration: Lebesgue integral theory
//! - Probability: probability spaces and random variables

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize MeasureTheory module
    ///
    /// Measure theory provides the foundation for modern analysis, probability,
    /// and integration. It extends the notion of "size" (length, area, volume)
    /// to arbitrary sets in a rigorous way.
    ///
    /// Key concepts:
    /// - Sigma-algebras: collections of sets closed under complements and countable unions
    /// - Measures: functions assigning non-negative values to sets
    /// - Lebesgue integral: generalization of Riemann integral
    /// - Probability measures: measures with total mass 1
    ///
    /// This module provides axioms for:
    /// - Sigma-algebras and measurable spaces
    /// - Measures (finite, sigma-finite, probability)
    /// - Measurable functions
    /// - Integration (simple functions, Lebesgue integral)
    /// - Convergence theorems
    /// - Probability theory basics
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.measure_theory_init == true`
    /// ENSURES: On success, required dependencies (`eq`, `nat`, `rat`, `topological_space`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_measure_theory(&mut self) -> Result<(), EnvError> {
        if self.measure_theory_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_rat()?;
        self.init_topological_space()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Measure theory constants
        for name in &[
            // ================================================================
            // Sigma-Algebras
            // ================================================================
            "MeasureTheory.MeasurableSpace",    // σ-algebra on a type
            "MeasureTheory.MeasurableSet",      // predicate: set is measurable
            "MeasureTheory.measurable_empty",   // ∅ is measurable
            "MeasureTheory.measurable_univ",    // universal set is measurable
            "MeasureTheory.measurable_compl",   // complement of measurable is measurable
            "MeasureTheory.measurable_union",   // countable union of measurable is measurable
            "MeasureTheory.measurable_inter", // countable intersection of measurable is measurable
            "MeasureTheory.generateMeasurable", // generated σ-algebra from collection
            "MeasureTheory.generateMeasurable_basic", // generators are measurable
            "MeasureTheory.generateMeasurable_minimal", // smallest containing σ-algebra
            "MeasureTheory.BorelSpace",       // Borel σ-algebra on topological space
            "MeasureTheory.borel",            // Borel σ-algebra constructor
            "MeasureTheory.borel_open",       // open sets are Borel
            "MeasureTheory.borel_closed",     // closed sets are Borel
            // ================================================================
            // Measurable Functions
            // ================================================================
            "MeasureTheory.Measurable",         // f : X → Y is measurable
            "MeasureTheory.measurable_id",      // identity is measurable
            "MeasureTheory.measurable_const",   // constants are measurable
            "MeasureTheory.measurable_comp",    // composition of measurable is measurable
            "MeasureTheory.StronglyMeasurable", // f is strongly measurable
            "MeasureTheory.AEMeasurable",       // almost everywhere measurable
            "MeasureTheory.MeasurableEquiv",    // measurable equivalence
            "MeasureTheory.measurable_equiv_symm", // inverse of measurable equiv
            "MeasureTheory.measurable_equiv_trans", // composition of equivs
            // ================================================================
            // Measures - Basic
            // ================================================================
            "MeasureTheory.Measure", // measure μ on measurable space
            "MeasureTheory.Measure.toOuterMeasure", // underlying outer measure
            "MeasureTheory.measure_empty", // μ(∅) = 0
            "MeasureTheory.measure_mono", // A ⊆ B → μ(A) ≤ μ(B)
            "MeasureTheory.measure_union_null", // μ(A ∪ B) ≤ μ(A) + μ(B) when disjoint
            "MeasureTheory.measure_countable_union", // countable additivity
            "MeasureTheory.measure_diff", // μ(A \ B) = μ(A) - μ(A ∩ B) for finite
            "MeasureTheory.measure_union", // μ(A ∪ B) = μ(A) + μ(B) - μ(A ∩ B)
            // ================================================================
            // Outer Measures
            // ================================================================
            "MeasureTheory.OuterMeasure",       // outer measure
            "MeasureTheory.OuterMeasure.empty", // outer measure of ∅ is 0
            "MeasureTheory.OuterMeasure.mono",  // monotonicity
            "MeasureTheory.OuterMeasure.countable_subadditive", // countable subadditivity
            "MeasureTheory.caratheodory",       // Carathéodory's criterion
            "MeasureTheory.toMeasure",          // construct measure from outer measure
            // ================================================================
            // Special Measures
            // ================================================================
            "MeasureTheory.FiniteMeasure",      // μ(X) < ∞
            "MeasureTheory.ProbabilityMeasure", // μ(X) = 1
            "MeasureTheory.SigmaFinite",        // X = ⋃ᵢ Aᵢ with μ(Aᵢ) < ∞
            "MeasureTheory.LocallyFinite",      // locally finite measure
            "MeasureTheory.counting",           // counting measure
            "MeasureTheory.dirac",              // Dirac measure δₓ
            "MeasureTheory.dirac_apply",        // δₓ(A) = 1 if x ∈ A, 0 otherwise
            "MeasureTheory.restrict",           // restriction μ.restrict s
            "MeasureTheory.restrict_apply",     // (μ.restrict s)(t) = μ(s ∩ t)
            // ================================================================
            // Lebesgue Measure
            // ================================================================
            "MeasureTheory.LebesgueMeasure", // Lebesgue measure on ℝⁿ
            "MeasureTheory.lebesgue_interval", // λ([a,b]) = b - a
            "MeasureTheory.lebesgue_translation", // translation invariance
            "MeasureTheory.lebesgue_scaling", // λ(cA) = |c|ⁿ λ(A)
            "MeasureTheory.lebesgue_borel",  // Lebesgue is Borel
            "MeasureTheory.lebesgue_complete", // Lebesgue is complete
            "MeasureTheory.lebesgue_regular", // Lebesgue is regular
            // ================================================================
            // Null Sets and Almost Everywhere
            // ================================================================
            "MeasureTheory.NullSet",           // μ(A) = 0
            "MeasureTheory.NullMeasurableSet", // measurable up to null set
            "MeasureTheory.ae",                // almost everywhere filter
            "MeasureTheory.ae_eq",             // f =ᵐ g (equal a.e.)
            "MeasureTheory.ae_le",             // f ≤ᵐ g (≤ a.e.)
            "MeasureTheory.ae_of_all",         // ∀ x, P x → ∀ᵐ x, P x
            "MeasureTheory.Eventually.ae",     // filter property for a.e.
            "MeasureTheory.ae_restrict",       // a.e. for restricted measure
            // ================================================================
            // Simple Functions
            // ================================================================
            "MeasureTheory.SimpleFunc", // simple function (finite range)
            "MeasureTheory.SimpleFunc.mk", // constructor for simple functions
            "MeasureTheory.SimpleFunc.range", // finite range of simple function
            "MeasureTheory.SimpleFunc.map", // map over simple function
            "MeasureTheory.SimpleFunc.piecewise", // piecewise simple function
            "MeasureTheory.SimpleFunc.const", // constant simple function
            "MeasureTheory.SimpleFunc.indicator", // indicator function
            "MeasureTheory.SimpleFunc.lintegral", // integral of simple function
            // ================================================================
            // Lebesgue Integral
            // ================================================================
            "MeasureTheory.lintegral", // ∫⁻ f dμ - integral of f : X → [0,∞]
            "MeasureTheory.lintegral_zero", // ∫⁻ 0 dμ = 0
            "MeasureTheory.lintegral_add", // ∫⁻ (f + g) = ∫⁻ f + ∫⁻ g
            "MeasureTheory.lintegral_const", // ∫⁻ c dμ = c · μ(X)
            "MeasureTheory.lintegral_mono", // f ≤ g → ∫⁻ f ≤ ∫⁻ g
            "MeasureTheory.lintegral_indicator", // ∫⁻ 1ₛ dμ = μ(s)
            // ================================================================
            // Bochner Integral
            // ================================================================
            "MeasureTheory.integral",            // ∫ f dμ - Bochner integral
            "MeasureTheory.Integrable",          // f is integrable
            "MeasureTheory.integrable_def",      // ‖f‖ has finite integral
            "MeasureTheory.integral_zero",       // ∫ 0 dμ = 0
            "MeasureTheory.integral_add",        // ∫ (f + g) = ∫ f + ∫ g
            "MeasureTheory.integral_neg",        // ∫ (-f) = -(∫ f)
            "MeasureTheory.integral_sub",        // ∫ (f - g) = ∫ f - ∫ g
            "MeasureTheory.integral_smul",       // ∫ (c • f) = c • ∫ f
            "MeasureTheory.integral_const",      // ∫ c dμ = c · μ(X)
            "MeasureTheory.integral_mono",       // f ≤ g → ∫ f ≤ ∫ g
            "MeasureTheory.integral_nonneg",     // 0 ≤ f → 0 ≤ ∫ f
            "MeasureTheory.integral_norm_bound", // |∫ f| ≤ ∫ ‖f‖
            // ================================================================
            // Convergence Theorems
            // ================================================================
            "MeasureTheory.lintegral_mono_ae", // a.e. monotone implies integral monotone
            "MeasureTheory.monotone_convergence", // MCT: fₙ ↑ f → ∫ fₙ → ∫ f
            "MeasureTheory.fatou",             // Fatou's lemma: ∫ liminf fₙ ≤ liminf ∫ fₙ
            "MeasureTheory.dominated_convergence", // DCT: |fₙ| ≤ g integrable → ∫ fₙ → ∫ f
            "MeasureTheory.tendsto_integral_of_dominated", // generalized DCT
            "MeasureTheory.vitali_convergence", // Vitali convergence theorem
            // ================================================================
            // Fubini-Tonelli
            // ================================================================
            "MeasureTheory.MeasureProd",   // product measure μ × ν
            "MeasureTheory.prod_apply",    // (μ × ν)(A × B) = μ(A) · ν(B)
            "MeasureTheory.fubini",        // Fubini: ∫∫ f = ∫∫ f (order)
            "MeasureTheory.tonelli",       // Tonelli: for non-negative
            "MeasureTheory.integral_prod", // ∫ f d(μ × ν) = ∫∫ f dμ dν
            // ================================================================
            // Radon-Nikodym
            // ================================================================
            "MeasureTheory.AbsolutelyContinuous",   // ν ≪ μ
            "MeasureTheory.MutuallySingular",       // μ ⊥ ν
            "MeasureTheory.radon_nikodym",          // Radon-Nikodym derivative dν/dμ
            "MeasureTheory.rnDeriv",                // Radon-Nikodym derivative function
            "MeasureTheory.withDensity",            // μ.withDensity f
            "MeasureTheory.integral_rnDeriv",       // ∫ (dν/dμ) dμ = ν(X)
            "MeasureTheory.lebesgue_decomposition", // ν = νₐ + νₛ unique
            // ================================================================
            // Lp Spaces
            // ================================================================
            "MeasureTheory.Lp",             // Lp space
            "MeasureTheory.Lp.norm",        // ‖f‖ₚ = (∫ |f|ᵖ)^(1/p)
            "MeasureTheory.Memℒp",          // f ∈ Lp
            "MeasureTheory.snorm",          // seminorm for Lp
            "MeasureTheory.snorm_exponent", // p for Lp
            "MeasureTheory.Lp.complete",    // Lp is complete
            "MeasureTheory.holder",         // Hölder: ‖fg‖₁ ≤ ‖f‖ₚ ‖g‖ᵧ
            "MeasureTheory.minkowski",      // Minkowski: ‖f+g‖ₚ ≤ ‖f‖ₚ + ‖g‖ₚ
            "MeasureTheory.Lp.dual",        // (Lp)* ≅ Lq for 1 < p < ∞
            // ================================================================
            // Probability - Basic
            // ================================================================
            "MeasureTheory.ProbabilitySpace", // (Ω, F, P) with P(Ω) = 1
            "MeasureTheory.prob_univ",        // P(Ω) = 1
            "MeasureTheory.prob_empty",       // P(∅) = 0
            "MeasureTheory.prob_compl",       // P(Aᶜ) = 1 - P(A)
            "MeasureTheory.prob_union",       // P(A ∪ B) ≤ P(A) + P(B)
            "MeasureTheory.prob_inter",       // P(A ∩ B) ≤ min(P(A), P(B))
            // ================================================================
            // Random Variables
            // ================================================================
            "MeasureTheory.RandomVariable", // measurable function X : Ω → E
            "MeasureTheory.rv_measurable",  // random variable is measurable
            "MeasureTheory.pushforward",    // pushforward measure X_* P
            "MeasureTheory.Distribution",   // distribution of random variable
            "MeasureTheory.IdenticallyDistributed", // X =ᵈ Y
            // ================================================================
            // Expectation
            // ================================================================
            "MeasureTheory.Expectation",           // E[X] = ∫ X dP
            "MeasureTheory.expectation_const",     // E[c] = c
            "MeasureTheory.expectation_add",       // E[X + Y] = E[X] + E[Y]
            "MeasureTheory.expectation_smul",      // E[cX] = c E[X]
            "MeasureTheory.expectation_nonneg",    // X ≥ 0 → E[X] ≥ 0
            "MeasureTheory.expectation_mono",      // X ≤ Y → E[X] ≤ E[Y]
            "MeasureTheory.expectation_indicator", // E[1_A] = P(A)
            // ================================================================
            // Variance and Moments
            // ================================================================
            "MeasureTheory.Variance",          // Var(X) = E[(X - E[X])²]
            "MeasureTheory.variance_def",      // Var(X) = E[X²] - E[X]²
            "MeasureTheory.variance_nonneg",   // Var(X) ≥ 0
            "MeasureTheory.variance_const",    // Var(c) = 0
            "MeasureTheory.variance_smul",     // Var(cX) = c² Var(X)
            "MeasureTheory.StandardDeviation", // σ = √Var(X)
            "MeasureTheory.Moment",            // E[Xⁿ] - nth moment
            "MeasureTheory.CentralMoment",     // E[(X - E[X])ⁿ]
            "MeasureTheory.Skewness",          // third standardized moment
            "MeasureTheory.Kurtosis",          // fourth standardized moment
            // ================================================================
            // Independence
            // ================================================================
            "MeasureTheory.IndepSets",         // independent sets
            "MeasureTheory.Indep",             // independent σ-algebras
            "MeasureTheory.IndepFun",          // independent random variables
            "MeasureTheory.indep_prod",        // P(A ∩ B) = P(A) · P(B)
            "MeasureTheory.indep_expectation", // E[XY] = E[X] · E[Y] when indep
            "MeasureTheory.indep_variance",    // Var(X + Y) = Var(X) + Var(Y) when indep
            "MeasureTheory.iIndep",            // mutual independence
            // ================================================================
            // Conditional Expectation
            // ================================================================
            "MeasureTheory.condexp",       // E[X | G] conditional expectation
            "MeasureTheory.condexp_const", // E[c | G] = c
            "MeasureTheory.condexp_add",   // E[X + Y | G] = E[X|G] + E[Y|G]
            "MeasureTheory.condexp_smul",  // E[cX | G] = c E[X|G]
            "MeasureTheory.condexp_of_measurable", // E[X | G] = X if X is G-meas
            "MeasureTheory.condexp_tower", // E[E[X|G]|H] = E[X|H] for H ⊆ G
            "MeasureTheory.condexp_integral", // ∫_A E[X|G] = ∫_A X for A ∈ G
            // ================================================================
            // Convergence of Random Variables
            // ================================================================
            "MeasureTheory.TendstoInMeasure", // convergence in measure
            "MeasureTheory.TendstoInLp",      // convergence in Lp
            "MeasureTheory.TendstoAe",        // almost sure convergence
            "MeasureTheory.TendstoProb",      // convergence in probability
            "MeasureTheory.TendstoDistr",     // convergence in distribution
            "MeasureTheory.ae_implies_prob",  // a.s. → in probability
            "MeasureTheory.Lp_implies_prob",  // Lp → in probability
            "MeasureTheory.prob_implies_distr", // in probability → in distribution
            // ================================================================
            // Laws of Large Numbers
            // ================================================================
            "MeasureTheory.strong_law", // strong law of large numbers
            "MeasureTheory.weak_law",   // weak law of large numbers
            "MeasureTheory.SLLN_iid",   // SLLN for iid sequences
            "MeasureTheory.WLLN_iid",   // WLLN for iid sequences
            // ================================================================
            // Central Limit Theorem
            // ================================================================
            "MeasureTheory.CLT",                // central limit theorem
            "MeasureTheory.CLT_iid",            // CLT for iid sequences
            "MeasureTheory.NormalDistribution", // N(μ, σ²)
            "MeasureTheory.StandardNormal",     // N(0, 1)
            "MeasureTheory.normal_pdf",         // density of normal
            "MeasureTheory.normal_cdf",         // CDF of normal
            // ================================================================
            // Common Distributions
            // ================================================================
            "MeasureTheory.Bernoulli",   // Bernoulli(p)
            "MeasureTheory.Binomial",    // Binomial(n, p)
            "MeasureTheory.Poisson",     // Poisson(λ)
            "MeasureTheory.Geometric",   // Geometric(p)
            "MeasureTheory.Exponential", // Exponential(λ)
            "MeasureTheory.Uniform",     // Uniform(a, b)
            "MeasureTheory.Gamma",       // Gamma(α, β)
            "MeasureTheory.Beta",        // Beta(α, β)
            // ================================================================
            // Martingales
            // ================================================================
            "MeasureTheory.Martingale",    // martingale w.r.t. filtration
            "MeasureTheory.Submartingale", // submartingale
            "MeasureTheory.Supermartingale", // supermartingale
            "MeasureTheory.Filtration",    // filtration Fₙ ⊆ Fₙ₊₁
            "MeasureTheory.Adapted",       // adapted process
            "MeasureTheory.StoppingTime",  // stopping time τ
            "MeasureTheory.optional_stopping", // optional stopping theorem
            "MeasureTheory.martingale_convergence", // martingale convergence
            "MeasureTheory.DoobMaximal",   // Doob's maximal inequality
            // ================================================================
            // Characteristic Functions
            // ================================================================
            "MeasureTheory.CharFun", // characteristic function φ_X(t) = E[e^{itX}]
            "MeasureTheory.charfun_unique", // φ determines distribution
            "MeasureTheory.charfun_normal", // φ for normal distribution
            "MeasureTheory.charfun_sum", // φ_{X+Y} = φ_X · φ_Y when indep
            "MeasureTheory.levy_continuity", // Lévy continuity theorem
            // ================================================================
            // Measure Preserving Maps
            // ================================================================
            "MeasureTheory.MeasurePreserving", // T : X → X preserves μ
            "MeasureTheory.QuasiMeasurePreserving", // pushforward equivalent
            "MeasureTheory.Ergodic",           // ergodic transformation
            "MeasureTheory.ergodic_theorem",   // Birkhoff ergodic theorem
            "MeasureTheory.MixingOn",          // mixing property
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.measure_theory_init = true;
        Ok(())
    }

    /// Check if MeasureTheory has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_measure_theory` has completed successfully
    /// ENSURES: Pure - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_measure_theory(&self) -> bool {
        self.measure_theory_init
    }
}
