// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stochastic processes and concentration inequalities for Environment
//!
//! This module contains stochastic process theory:
//! - Markov chains: discrete and continuous time
//! - Concentration inequalities: Hoeffding, Chernoff, McDiarmid, etc.
//! - Advanced stochastic calculus: Ito calculus, martingale theory
//! - Queueing theory: M/M/1, Jackson networks
//!
//! Critical for ML verification and statistical learning theory.

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize StochasticProcesses module
    ///
    /// Stochastic processes extend probability theory to random evolution over time.
    /// Essential for:
    /// - Machine learning generalization bounds
    /// - Statistical learning theory
    /// - Probabilistic algorithm analysis
    /// - Queueing and performance modeling
    /// - Financial mathematics
    ///
    /// This module provides axioms for:
    /// - Discrete and continuous-time Markov chains
    /// - Concentration inequalities for ML bounds
    /// - Advanced stochastic calculus
    /// - Queueing theory fundamentals
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.stochastic_processes_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_stochastic_processes(&mut self) -> Result<(), EnvError> {
        if self.stochastic_processes_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_rat()?;
        self.init_measure_theory()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Stochastic process constants
        for name in &[
            // ================================================================
            // Stochastic Processes - Fundamentals
            // ================================================================
            "StochasticProcess.Process", // X : T → Ω → E indexed process
            "StochasticProcess.SamplePath", // ω ↦ (t ↦ X(t, ω)) sample path
            "StochasticProcess.Adapted", // process adapted to filtration
            "StochasticProcess.Predictable", // predictable process
            "StochasticProcess.Progressively", // progressively measurable
            "StochasticProcess.Cadlag",  // right-continuous, left limits
            "StochasticProcess.Caglad",  // left-continuous, right limits
            "StochasticProcess.Modification", // X is modification of Y
            "StochasticProcess.Indistinguishable", // X and Y indistinguishable
            // ================================================================
            // Discrete-Time Markov Chains
            // ================================================================
            "StochasticProcess.MarkovChain", // discrete-time Markov chain
            "StochasticProcess.MarkovProperty", // P(X_{n+1}|X_0,...,X_n) = P(X_{n+1}|X_n)
            "StochasticProcess.TransitionMatrix", // P[i,j] = P(X_{n+1}=j|X_n=i)
            "StochasticProcess.HomogeneousChain", // time-homogeneous chain
            "StochasticProcess.InitialDistribution", // distribution of X_0
            "StochasticProcess.ChapmanKolmogorov", // P^{m+n} = P^m · P^n
            "StochasticProcess.StationaryDistribution", // πP = π
            "StochasticProcess.stationary_exists", // existence of stationary dist
            "StochasticProcess.stationary_unique", // uniqueness conditions
            // ================================================================
            // Classification of States
            // ================================================================
            "StochasticProcess.Accessible",  // j accessible from i
            "StochasticProcess.Communicate", // i ↔ j communicate
            "StochasticProcess.Irreducible", // all states communicate
            "StochasticProcess.Aperiodic",   // gcd of return times = 1
            "StochasticProcess.Period",      // period of state i
            "StochasticProcess.Recurrent",   // P(return to i | start i) = 1
            "StochasticProcess.Transient",   // P(return to i | start i) < 1
            "StochasticProcess.PositiveRecurrent", // expected return time < ∞
            "StochasticProcess.NullRecurrent", // recurrent but E[return] = ∞
            "StochasticProcess.Absorbing",   // P[i,i] = 1
            // ================================================================
            // Ergodic Theory for Markov Chains
            // ================================================================
            "StochasticProcess.Ergodic", // irreducible + aperiodic + positive recurrent
            "StochasticProcess.ergodic_theorem_mc", // (1/n)Σ f(X_k) → E_π[f] a.s.
            "StochasticProcess.convergence_to_stationary", // P^n → 1π as n → ∞
            "StochasticProcess.mixing_time", // time to approach stationarity
            "StochasticProcess.spectral_gap", // 1 - λ_2 (convergence rate)
            // ================================================================
            // Reversibility
            // ================================================================
            "StochasticProcess.DetailedBalance", // π_i P_{ij} = π_j P_{ji}
            "StochasticProcess.Reversible",      // satisfies detailed balance
            "StochasticProcess.reversible_stationary", // detailed balance implies stationary
            "StochasticProcess.metropolis_hastings", // MH algorithm preserves π
            // ================================================================
            // Continuous-Time Markov Chains
            // ================================================================
            "StochasticProcess.CTMC",      // continuous-time Markov chain
            "StochasticProcess.Generator", // Q-matrix (generator)
            "StochasticProcess.generator_row_sum", // Q1 = 0 (rows sum to 0)
            "StochasticProcess.HoldingTime", // exponential holding times
            "StochasticProcess.JumpChain", // embedded jump chain
            "StochasticProcess.KolmogorovForward", // dP/dt = PQ (forward equation)
            "StochasticProcess.KolmogorovBackward", // dP/dt = QP (backward equation)
            "StochasticProcess.ctmc_stationary", // πQ = 0 stationary
            "StochasticProcess.ExpMatrix", // P(t) = exp(Qt)
            // ================================================================
            // Birth-Death Processes
            // ================================================================
            "StochasticProcess.BirthDeathProcess", // birth-death on integers
            "StochasticProcess.BirthRate",         // λ_n birth rate at n
            "StochasticProcess.DeathRate",         // μ_n death rate at n
            "StochasticProcess.bd_stationary",     // stationary distribution
            "StochasticProcess.bd_reversible",     // birth-death is reversible
            // ================================================================
            // Concentration Inequalities - Basic
            // ================================================================
            "StochasticProcess.MarkovInequality", // P(X ≥ a) ≤ E[X]/a for X ≥ 0
            "StochasticProcess.ChebyshevInequality", // P(|X-μ| ≥ kσ) ≤ 1/k²
            "StochasticProcess.ChernoffBound",    // P(X ≥ a) ≤ inf_t e^{-ta} E[e^{tX}]
            "StochasticProcess.MGF",              // moment generating function E[e^{tX}]
            "StochasticProcess.mgf_sum_indep",    // MGF of sum = product of MGFs
            // ================================================================
            // Concentration - Bounded Random Variables
            // ================================================================
            "StochasticProcess.HoeffdingLemma", // E[e^{t(X-E[X])}] ≤ e^{t²(b-a)²/8}
            "StochasticProcess.HoeffdingInequality", // P(S_n - E[S_n] ≥ t) ≤ exp(-2t²/Σ(b_i-a_i)²)
            "StochasticProcess.hoeffding_two_sided", // P(|S_n - E[S_n]| ≥ t) ≤ 2exp(...)
            "StochasticProcess.SubGaussian",    // X has sub-Gaussian tails
            "StochasticProcess.subgaussian_param", // sub-Gaussian parameter σ
            "StochasticProcess.subgaussian_sum", // sum of sub-Gaussians is sub-Gaussian
            // ================================================================
            // Concentration - Binomial/Bernoulli
            // ================================================================
            "StochasticProcess.ChernoffMultiplicative", // P(X ≥ (1+δ)μ) ≤ e^{-δ²μ/3}
            "StochasticProcess.ChernoffAdditive",       // additive form
            "StochasticProcess.bernstein_inequality",   // Bernstein's inequality
            "StochasticProcess.bennett_inequality",     // Bennett's inequality
            "StochasticProcess.binomial_tail_bound",    // bounds for binomial tails
            // ================================================================
            // Concentration - Martingale Methods
            // ================================================================
            "StochasticProcess.AzumaHoeffding", // Azuma-Hoeffding inequality
            "StochasticProcess.azuma_bound",    // P(M_n ≥ t) ≤ exp(-t²/2Σc_i²)
            "StochasticProcess.BoundedDifference", // |f(x) - f(x')| ≤ c_i for x,x' differ in i
            "StochasticProcess.McDiarmid",      // McDiarmid's inequality
            "StochasticProcess.mcdiarmmid_bound", // P(f - E[f] ≥ t) ≤ exp(-2t²/Σc_i²)
            "StochasticProcess.DoobMartingale", // Doob martingale construction
            // ================================================================
            // Concentration - Subexponential
            // ================================================================
            "StochasticProcess.SubExponential", // X has sub-exponential tails
            "StochasticProcess.subexp_param",   // (ν, α) sub-exponential parameters
            "StochasticProcess.subexp_concentration", // concentration for sub-exponential
            "StochasticProcess.bernstein_condition", // Bernstein moment condition
            // ================================================================
            // Concentration - Lipschitz Functions
            // ================================================================
            "StochasticProcess.GaussianConcentration", // for Lipschitz on Gaussian
            "StochasticProcess.LogSobolevInequality",  // log-Sobolev inequality
            "StochasticProcess.TalagrandInequality",   // Talagrand's convex distance
            "StochasticProcess.TransportationCostInequality", // T_1 inequality
            // ================================================================
            // Concentration - Matrix
            // ================================================================
            "StochasticProcess.MatrixHoeffding", // matrix Hoeffding
            "StochasticProcess.MatrixBernstein", // matrix Bernstein
            "StochasticProcess.MatrixChernoff",  // matrix Chernoff
            "StochasticProcess.operator_norm_bound", // bounds on ‖Σ X_i‖
            // ================================================================
            // PAC Learning Bounds
            // ================================================================
            "StochasticProcess.VC_dimension",      // VC dimension
            "StochasticProcess.shattering",        // concept of shattering
            "StochasticProcess.vc_generalization", // generalization via VC
            "StochasticProcess.Rademacher",        // Rademacher complexity
            "StochasticProcess.rademacher_bound",  // generalization via Rademacher
            "StochasticProcess.symmetrization",    // symmetrization lemma
            "StochasticProcess.contraction",       // contraction lemma
            // ================================================================
            // Empirical Process Theory
            // ================================================================
            "StochasticProcess.EmpiricalMeasure", // (1/n)Σδ_{X_i}
            "StochasticProcess.EmpiricalProcess", // √n(P_n - P)
            "StochasticProcess.GlivenkoCantelli", // uniform convergence of CDF
            "StochasticProcess.Donsker",          // Donsker's theorem
            "StochasticProcess.DKW_inequality",   // Dvoretzky-Kiefer-Wolfowitz
            "StochasticProcess.CoveringNumber",   // ε-covering number
            "StochasticProcess.MetricEntropy",    // log of covering number
            "StochasticProcess.Bracketing",       // bracketing number
            // ================================================================
            // Brownian Motion
            // ================================================================
            "StochasticProcess.BrownianMotion", // standard Brownian motion
            "StochasticProcess.bm_continuous",  // a.s. continuous paths
            "StochasticProcess.bm_independent_increments", // independent increments
            "StochasticProcess.bm_gaussian_increments", // Gaussian increments
            "StochasticProcess.bm_quadratic_variation", // [B,B]_t = t
            "StochasticProcess.bm_nowhere_differentiable", // a.s. nowhere differentiable
            "StochasticProcess.bm_martingale",  // B_t is martingale
            "StochasticProcess.bm_reflection",  // reflection principle
            "StochasticProcess.bm_max_distribution", // distribution of max_{s≤t} B_s
            "StochasticProcess.GeometricBM",    // dS = μSdt + σSdW
            "StochasticProcess.OrnsteinUhlenbeck", // dX = -θXdt + σdW
            // ================================================================
            // Ito Calculus
            // ================================================================
            "StochasticProcess.ItoIntegral", // ∫H dM for martingale M
            "StochasticProcess.ito_isometry", // E[(∫H dM)²] = E[∫H² d[M]]
            "StochasticProcess.ItoProcess",  // dX = b dt + σ dW
            "StochasticProcess.ItoFormula",  // df(X) = f'dX + ½f''d[X]
            "StochasticProcess.ito_product_rule", // d(XY) = X dY + Y dX + d[X,Y]
            "StochasticProcess.QuadraticCovariation", // [X,Y] quadratic covariation
            "StochasticProcess.LocalMartingale", // local martingale
            "StochasticProcess.Semimartingale", // semimartingale
            // ================================================================
            // Stochastic Differential Equations
            // ================================================================
            "StochasticProcess.SDE", // dX = b(t,X)dt + σ(t,X)dW
            "StochasticProcess.sde_strong_solution", // strong solution existence
            "StochasticProcess.sde_weak_solution", // weak solution existence
            "StochasticProcess.sde_uniqueness", // pathwise uniqueness
            "StochasticProcess.LipschitzCondition", // Lipschitz for existence
            "StochasticProcess.LinearGrowth", // linear growth for non-explosion
            "StochasticProcess.Girsanov", // Girsanov's theorem
            "StochasticProcess.FeynmanKac", // Feynman-Kac formula
            // ================================================================
            // Levy Processes
            // ================================================================
            "StochasticProcess.LevyProcess", // stationary independent increments
            "StochasticProcess.LevyKhintchine", // Lévy-Khintchine formula
            "StochasticProcess.PoissonProcess", // Poisson process
            "StochasticProcess.CompoundPoisson", // compound Poisson process
            "StochasticProcess.JumpDiffusion", // diffusion + jumps
            "StochasticProcess.LevyMeasure", // Lévy measure
            // ================================================================
            // Queueing Theory
            // ================================================================
            "StochasticProcess.Queue",               // queueing system
            "StochasticProcess.ArrivalProcess",      // arrival process
            "StochasticProcess.ServiceProcess",      // service process
            "StochasticProcess.MM1Queue",            // M/M/1 queue
            "StochasticProcess.MM1_stationary",      // stationary dist for M/M/1
            "StochasticProcess.MMcQueue",            // M/M/c queue
            "StochasticProcess.MG1Queue",            // M/G/1 queue
            "StochasticProcess.PollaczekKhintchine", // P-K formula for M/G/1
            "StochasticProcess.LittleLaw",           // L = λW (Little's law)
            "StochasticProcess.PASTA",               // Poisson arrivals see time averages
            "StochasticProcess.JacksonNetwork",      // Jackson network
            "StochasticProcess.BurkeTheorem",        // Burke's theorem
            // ================================================================
            // Random Walks
            // ================================================================
            "StochasticProcess.RandomWalk",       // S_n = Σ X_i
            "StochasticProcess.SimpleRandomWalk", // X_i ∈ {-1, +1} uniform
            "StochasticProcess.rw_recurrence",    // recurrence in d ≤ 2
            "StochasticProcess.rw_transience",    // transience in d ≥ 3
            "StochasticProcess.rw_clt",           // S_n/√n → N(0,1)
            "StochasticProcess.rw_reflection",    // reflection principle for RW
            "StochasticProcess.BallotProblem",    // ballot problem
            "StochasticProcess.ArcsineLaw",       // arcsine law for zeros
            // ================================================================
            // Point Processes
            // ================================================================
            "StochasticProcess.PointProcess", // random measure on space
            "StochasticProcess.PoissonPointProcess", // Poisson point process
            "StochasticProcess.IntensityMeasure", // intensity measure
            "StochasticProcess.Superposition", // superposition of PP
            "StochasticProcess.Thinning",     // thinning of PP
            "StochasticProcess.HawkesProcess", // self-exciting point process
            // ================================================================
            // Renewal Theory
            // ================================================================
            "StochasticProcess.RenewalProcess", // N(t) = max{n: S_n ≤ t}
            "StochasticProcess.RenewalEquation", // renewal equation
            "StochasticProcess.ElementaryRenewal", // E[N(t)]/t → 1/E[X]
            "StochasticProcess.BlackwellRenewal", // Blackwell's theorem
            "StochasticProcess.KeyRenewalTheorem", // key renewal theorem
            "StochasticProcess.RegenerativeProcess", // regenerative process
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.stochastic_processes_init = true;
        Ok(())
    }

    /// Check if StochasticProcesses has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.stochastic_processes_init == true`
    pub(crate) fn has_stochastic_processes(&self) -> bool {
        self.stochastic_processes_init
    }
}
