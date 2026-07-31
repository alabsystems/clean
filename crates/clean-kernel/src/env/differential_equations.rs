// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Differential equations structures for Environment
//!
//! This module contains differential equations initialization:
//! - Ordinary differential equations (ODEs)
//! - Partial differential equations (PDEs)
//! - Dynamical systems
//! - Stability theory
//! - Numerical methods

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
    /// Initialize DifferentialEquations module
    ///
    /// Differential equations study equations involving functions and their
    /// derivatives. They are fundamental to:
    /// - Physics (mechanics, electromagnetism, quantum)
    /// - Engineering (control systems, signal processing)
    /// - Biology (population dynamics, epidemiology)
    /// - Finance (option pricing, risk modeling)
    ///
    /// Key concepts:
    /// - ODEs: equations with derivatives in one variable
    /// - PDEs: equations with partial derivatives
    /// - Dynamical systems: evolution of state spaces
    /// - Stability: behavior near equilibria
    ///
    /// This module provides axioms for:
    /// - ODE existence and uniqueness
    /// - Linear and nonlinear systems
    /// - Stability and Lyapunov theory
    /// - PDE fundamentals and classification
    /// - Numerical analysis basics
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.differential_equations_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_differential_equations(&mut self) -> Result<(), EnvError> {
        if self.differential_equations_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_rat()?;
        self.init_topological_space()?;
        self.init_algebra_linear()?;
        self.init_functional_analysis()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Differential equations constants
        for name in &[
            // ================================================================
            // Basic ODE Concepts
            // ================================================================
            "DiffEq.ODE",                  // ordinary differential equation
            "DiffEq.InitialValueProblem",  // x' = f(t, x), x(t₀) = x₀
            "DiffEq.BoundaryValueProblem", // ODE with boundary conditions
            "DiffEq.Solution",             // solution to ODE
            "DiffEq.MaximalSolution",      // solution with maximal interval
            "DiffEq.GlobalSolution",       // solution defined for all t
            "DiffEq.FlowLine",             // integral curve of vector field
            // ================================================================
            // Existence and Uniqueness
            // ================================================================
            "DiffEq.LipschitzCondition",   // |f(t,x) - f(t,y)| ≤ L|x - y|
            "DiffEq.LocalLipschitz",       // locally Lipschitz condition
            "DiffEq.PicardLindelof",       // existence-uniqueness theorem
            "DiffEq.CauchyPeano",          // existence (continuity only)
            "DiffEq.PicardIteration",      // successive approximations
            "DiffEq.picard_convergence",   // Picard iterates converge
            "DiffEq.GronwallInequality",   // differential inequality
            "DiffEq.gronwall_lemma",       // integral form of Gronwall
            "DiffEq.ContinuousDependence", // continuous dependence on IC
            // ================================================================
            // Linear ODEs
            // ================================================================
            "DiffEq.LinearODE",              // x' = A(t)x + b(t)
            "DiffEq.HomogeneousLinearODE",   // x' = A(t)x
            "DiffEq.ConstantCoeffODE",       // x' = Ax + b
            "DiffEq.FundamentalMatrix",      // matrix of solutions
            "DiffEq.Wronskian",              // det of fundamental matrix
            "DiffEq.AbelFormula",            // Wronskian evolution
            "DiffEq.MatrixExponential",      // exp(tA) solution
            "DiffEq.matrix_exp_derivative",  // d/dt exp(tA) = A exp(tA)
            "DiffEq.VariationOfConstants",   // particular solution formula
            "DiffEq.LinearSuperposition",    // solutions form vector space
            "DiffEq.CharacteristicEquation", // det(A - λI) = 0
            "DiffEq.eigenvalue_solution",    // eλt v for eigenvalue λ
            // ================================================================
            // Higher-Order ODEs
            // ================================================================
            "DiffEq.HigherOrderODE",        // y⁽ⁿ⁾ = f(t, y, y', ..., y⁽ⁿ⁻¹⁾)
            "DiffEq.ReductionToFirstOrder", // convert to first-order system
            "DiffEq.SecondOrderLinear",     // y'' + p(t)y' + q(t)y = g(t)
            "DiffEq.ReductionOfOrder",      // reduce order given one solution
            "DiffEq.ConstantCoeffHigher",   // y⁽ⁿ⁾ + aₙ₋₁y⁽ⁿ⁻¹⁾ + ... = 0
            "DiffEq.characteristic_roots",  // solutions from char. equation
            "DiffEq.repeated_root_solution", // tᵏeλt for multiplicity k+1
            // ================================================================
            // Nonlinear ODEs and Phase Space
            // ================================================================
            "DiffEq.AutonomousODE", // x' = f(x) (no explicit t)
            "DiffEq.PhaseSpace",    // state space of system
            "DiffEq.PhasePortrait", // geometric picture of solutions
            "DiffEq.Orbit",         // trajectory in phase space
            "DiffEq.Equilibrium",   // fixed point f(x*) = 0
            "DiffEq.PeriodicOrbit", // closed trajectory
            "DiffEq.LimitCycle",    // isolated periodic orbit
            "DiffEq.Separatrix",    // boundary between basins
            "DiffEq.Nullcline",     // where component of f is zero
            "DiffEq.Isocline",      // where slope is constant
            // ================================================================
            // Stability Theory
            // ================================================================
            "DiffEq.StableEquilibrium",         // Lyapunov stable
            "DiffEq.AsymptoticStability",       // stable + solutions converge
            "DiffEq.UnstableEquilibrium",       // not stable
            "DiffEq.ExponentialStability",      // converges exponentially fast
            "DiffEq.GlobalAsymptoticStability", // globally asymptotically stable
            "DiffEq.LinearizationStability",    // stability via linearization
            "DiffEq.HartmanGrobman",            // topological conjugacy theorem
            // ================================================================
            // Lyapunov Theory
            // ================================================================
            "DiffEq.LyapunovFunction",        // V : Ω → ℝ with V̇ ≤ 0
            "DiffEq.LyapunovStrictFunction",  // V with V̇ < 0 off equilibrium
            "DiffEq.LyapunovDirect",          // stability via Lyapunov function
            "DiffEq.LaSalleInvariance",       // convergence to largest invariant
            "DiffEq.lyapunov_stable_iff",     // V exists ↔ stable
            "DiffEq.lyapunov_asymp_iff",      // strict V exists ↔ asymp stable
            "DiffEq.LyapunovExponent",        // exponential growth rate
            "DiffEq.MaximalLyapunovExponent", // largest exponent
            // ================================================================
            // Dynamical Systems
            // ================================================================
            "DiffEq.DynamicalSystem",     // continuous-time dynamics
            "DiffEq.Flow",                // φ : ℝ × M → M flow map
            "DiffEq.flow_group_property", // φ(t, φ(s, x)) = φ(t+s, x)
            "DiffEq.flow_identity",       // φ(0, x) = x
            "DiffEq.InvariantSet",        // set preserved by flow
            "DiffEq.AttractingSet",       // set that attracts nearby points
            "DiffEq.BasinOfAttraction",   // set of points converging to attractor
            "DiffEq.StrangeAttractor",    // chaotic attractor
            "DiffEq.MathverseLimitSet",   // asymptotic behavior as t → ∞
            "DiffEq.AlphaLimitSet",       // asymptotic behavior as t → -∞
            // ================================================================
            // Bifurcation Theory
            // ================================================================
            "DiffEq.BifurcationPoint", // parameter value where dynamics change
            "DiffEq.BifurcationDiagram", // equilibria vs parameter
            "DiffEq.SaddleNodeBifurcation", // creation/destruction of equilibria
            "DiffEq.TranscriticalBifurcation", // exchange of stability
            "DiffEq.PitchforkBifurcation", // symmetry-breaking bifurcation
            "DiffEq.HopfBifurcation",  // birth of limit cycle
            "DiffEq.hopf_supercritical", // stable limit cycle emerges
            "DiffEq.hopf_subcritical", // unstable limit cycle exists before
            "DiffEq.PeriodDoublingBifurcation", // period-doubling cascade
            "DiffEq.HomoclinicBifurcation", // homoclinic orbit appears/disappears
            // ================================================================
            // Chaos and Complexity
            // ================================================================
            "DiffEq.Chaos",                    // sensitive dependence on IC
            "DiffEq.SensitiveDependence",      // small changes → large divergence
            "DiffEq.PositiveLyapunovExponent", // criterion for chaos
            "DiffEq.TopologicalTransitivity",  // dense orbit exists
            "DiffEq.DensePeriodicOrbits",      // periodic orbits dense
            "DiffEq.LorenzSystem",             // canonical chaotic system
            "DiffEq.RosslerSystem",            // simple chaotic system
            "DiffEq.FractalDimension",         // dimension of strange attractor
            // ================================================================
            // Hamiltonian Systems
            // ================================================================
            "DiffEq.HamiltonianSystem",    // q̇ = ∂H/∂p, ṗ = -∂H/∂q
            "DiffEq.Hamiltonian",          // H : T*M → ℝ energy function
            "DiffEq.CanonicalCoordinates", // (q, p) phase space coords
            "DiffEq.PoissonBracket",       // {f, g} = ∑ ∂f/∂q·∂g/∂p - ...
            "DiffEq.hamilton_equations",   // ẋ = {x, H}
            "DiffEq.energy_conservation",  // dH/dt = 0 along solutions
            "DiffEq.SymplecticForm",       // ω = ∑ dqᵢ ∧ dpᵢ
            "DiffEq.LiouvilleTheorem",     // phase space volume preserved
            "DiffEq.IntegrableSystem",     // n independent integrals
            "DiffEq.ArnoldLiouville",      // integrable → action-angle
            // ================================================================
            // Partial Differential Equations
            // ================================================================
            "DiffEq.PDE",               // partial differential equation
            "DiffEq.LinearPDE",         // linear in u and derivatives
            "DiffEq.QuasilinearPDE",    // linear in highest derivatives
            "DiffEq.FullyNonlinearPDE", // nonlinear in highest derivatives
            "DiffEq.Order",             // order of PDE
            "DiffEq.PDEClassification", // elliptic/parabolic/hyperbolic
            // ================================================================
            // First-Order PDEs
            // ================================================================
            "DiffEq.FirstOrderPDE",           // F(x, u, Du) = 0
            "DiffEq.TransportEquation",       // uₜ + c·∇u = 0
            "DiffEq.transport_solution",      // u(x,t) = u₀(x - ct)
            "DiffEq.CharacteristicCurve",     // curve along which PDE becomes ODE
            "DiffEq.MethodOfCharacteristics", // solve via characteristics
            "DiffEq.BurgersEquation",         // uₜ + uuₓ = νuₓₓ
            "DiffEq.HamiltonJacobi",          // uₜ + H(x, Du) = 0
            "DiffEq.EikonalEquation",         // |∇u| = n(x)
            // ================================================================
            // Second-Order Linear PDEs
            // ================================================================
            "DiffEq.SecondOrderLinearPDE", // a·uₓₓ + b·uₓᵧ + c·uᵧᵧ + ... = 0
            "DiffEq.Discriminant",         // b² - 4ac for classification
            "DiffEq.EllipticPDE",          // Δ < 0 (e.g., Laplace)
            "DiffEq.ParabolicPDE",         // Δ = 0 (e.g., heat)
            "DiffEq.HyperbolicPDE",        // Δ > 0 (e.g., wave)
            // ================================================================
            // Laplace and Poisson
            // ================================================================
            "DiffEq.LaplaceEquation",        // Δu = 0
            "DiffEq.Laplacian",              // Δ = ∇² = ∑ ∂²/∂xᵢ²
            "DiffEq.HarmonicFunction",       // solution of Δu = 0
            "DiffEq.PoissonEquation",        // Δu = f
            "DiffEq.MaximumPrinciple",       // max on boundary
            "DiffEq.MeanValueProperty",      // u(x) = average over sphere
            "DiffEq.DirichletProblem",       // solve with boundary values
            "DiffEq.NeumannProblem",         // solve with boundary derivatives
            "DiffEq.GreenFunction",          // fundamental solution
            "DiffEq.poisson_representation", // u = ∫ G·f + boundary
            // ================================================================
            // Heat Equation
            // ================================================================
            "DiffEq.HeatEquation",         // uₜ = α²Δu
            "DiffEq.HeatKernel",           // fundamental solution
            "DiffEq.heat_kernel_formula",  // Φ(x,t) = (4παt)^(-n/2) exp(-|x|²/4αt)
            "DiffEq.heat_convolution",     // u = Φ * u₀
            "DiffEq.HeatMaximumPrinciple", // max on parabolic boundary
            "DiffEq.heat_smoothing",       // instantaneous smoothing
            "DiffEq.heat_decay",           // L^p decay as t → ∞
            "DiffEq.heat_uniqueness",      // uniqueness with growth bound
            // ================================================================
            // Wave Equation
            // ================================================================
            "DiffEq.WaveEquation",             // uₜₜ = c²Δu
            "DiffEq.dAlembertFormula",         // 1D: u = f(x+ct) + g(x-ct)
            "DiffEq.KirchhoffFormula",         // 3D wave solution
            "DiffEq.HuyghensPrinciple",        // waves from boundary
            "DiffEq.FinitePropagationSpeed",   // signals travel at speed c
            "DiffEq.DomainOfDependence",       // backward light cone
            "DiffEq.RangeOfInfluence",         // forward light cone
            "DiffEq.wave_energy",              // E = ½∫(uₜ² + c²|∇u|²)
            "DiffEq.wave_energy_conservation", // dE/dt = 0
            // ================================================================
            // Schrodinger Equation
            // ================================================================
            "DiffEq.SchrodingerEquation",      // iℏψₜ = Ĥψ
            "DiffEq.FreeSchrodinger",          // iψₜ = -Δψ
            "DiffEq.schrodinger_kernel",       // fundamental solution
            "DiffEq.schrodinger_dispersion",   // dispersive decay estimates
            "DiffEq.schrodinger_conservation", // ∫|ψ|² = const
            "DiffEq.NonlinearSchrodinger",     // iψₜ = -Δψ + |ψ|²ψ
            // ================================================================
            // Reaction-Diffusion
            // ================================================================
            "DiffEq.ReactionDiffusion",    // uₜ = DΔu + f(u)
            "DiffEq.FisherKPP",            // uₜ = Δu + u(1-u)
            "DiffEq.TravelingWave",        // solution u(x-ct)
            "DiffEq.traveling_wave_speed", // minimal speed c*
            "DiffEq.PatternFormation",     // Turing patterns
            "DiffEq.TuringInstability",    // diffusion-driven instability
            // ================================================================
            // Fluid Dynamics
            // ================================================================
            "DiffEq.NavierStokes",      // incompressible NS equations
            "DiffEq.EulerEquations",    // inviscid fluid
            "DiffEq.StokesEquations",   // linearized NS
            "DiffEq.Incompressibility", // ∇·u = 0
            "DiffEq.VorticityEquation", // evolution of ∇×u
            "DiffEq.KelvinCirculation", // circulation conservation
            "DiffEq.HelmsholtzVortex",  // vortex dynamics
            "DiffEq.ReynoldsNumber",    // Re = UL/ν
            // ================================================================
            // Weak Solutions
            // ================================================================
            "DiffEq.WeakSolution",           // solution in distributional sense
            "DiffEq.WeakDerivative",         // generalized derivative
            "DiffEq.TestFunction",           // smooth compactly supported
            "DiffEq.DistributionalSolution", // satisfies weak formulation
            "DiffEq.WeakFormulation",        // integral form of PDE
            "DiffEq.SobolevRegularity",      // solution in Sobolev space
            "DiffEq.EllipticRegularity",     // weak sol. of elliptic is smooth
            // ================================================================
            // Variational Methods
            // ================================================================
            "DiffEq.EulerLagrange",           // δJ = 0 ⟹ PDE
            "DiffEq.Functional",              // J : function space → ℝ
            "DiffEq.FirstVariation",          // δJ[u]v
            "DiffEq.DirichletPrinciple",      // Δu = 0 minimizes ∫|∇u|²
            "DiffEq.RayleighRitz",            // finite-dimensional approximation
            "DiffEq.DirectMethod",            // minimizing sequence
            "DiffEq.WeakLowerSemicontinuity", // J[u] ≤ lim inf J[uₙ]
            "DiffEq.Coercivity",              // J[u] → ∞ as ‖u‖ → ∞
            // ================================================================
            // Semigroups and Evolution
            // ================================================================
            "DiffEq.EvolutionEquation",           // du/dt = Au
            "DiffEq.AbstractCauchyProblem",       // u' = Au, u(0) = u₀
            "DiffEq.StronglyContinuousSemigroup", // C₀-semigroup
            "DiffEq.InfinitesimalGenerator",      // A = lim_{t→0} (T(t) - I)/t
            "DiffEq.HilleYosida",                 // characterization of generators
            "DiffEq.LumerPhillips",               // dissipative generators
            "DiffEq.AnalyticSemigroup",           // extends to sector
            "DiffEq.analytic_smoothing",          // T(t)u ∈ D(A^n) for t > 0
            // ================================================================
            // Spectral Methods for PDEs
            // ================================================================
            "DiffEq.SeparationOfVariables",    // product ansatz
            "DiffEq.FourierSeries",            // expand in eigenfunctions
            "DiffEq.Eigenfunction",            // Au = λu
            "DiffEq.SturmLiouville",           // (pu')' + qu = λwu
            "DiffEq.sturm_liouville_spectrum", // discrete real spectrum
            "DiffEq.eigenfunction_expansion",  // u = Σ cₙφₙ
            "DiffEq.completeness",             // eigenfunctions form basis
            // ================================================================
            // Conservation Laws
            // ================================================================
            "DiffEq.ConservationLaw", // uₜ + ∇·f(u) = 0
            "DiffEq.WeakSolutionCL",  // weak solution concept
            "DiffEq.RankineHugoniot", // jump condition
            "DiffEq.Entropy",         // entropy function η
            "DiffEq.EntropySolution", // satisfies entropy inequality
            "DiffEq.Shock",           // discontinuity in solution
            "DiffEq.RarefactionWave", // expansion wave
            "DiffEq.RiemannProblem",  // piecewise constant IC
            // ================================================================
            // Numerical Methods - ODE
            // ================================================================
            "DiffEq.EulerMethod",      // xₙ₊₁ = xₙ + hf(tₙ, xₙ)
            "DiffEq.euler_error",      // O(h) global error
            "DiffEq.ImplicitEuler",    // xₙ₊₁ = xₙ + hf(tₙ₊₁, xₙ₊₁)
            "DiffEq.RungeKutta",       // general RK method
            "DiffEq.RK4",              // classical 4th order
            "DiffEq.rk4_error",        // O(h⁴) global error
            "DiffEq.AdaptiveStepSize", // adjust h based on error
            "DiffEq.Stiffness",        // widely varying timescales
            "DiffEq.AStability",       // stability for stiff problems
            "DiffEq.BDF",              // backward differentiation formula
            // ================================================================
            // Numerical Methods - PDE
            // ================================================================
            "DiffEq.FiniteDifference",    // discretize derivatives
            "DiffEq.CFL",                 // Courant-Friedrichs-Lewy condition
            "DiffEq.VonNeumannStability", // Fourier stability analysis
            "DiffEq.FiniteElement",       // weak form discretization
            "DiffEq.GalerkinMethod",      // test with basis functions
            "DiffEq.FEM_convergence",     // convergence rate
            "DiffEq.FiniteVolume",        // conservation form
            "DiffEq.SpectralMethod",      // global basis functions
            // ================================================================
            // Control Theory
            // ================================================================
            "DiffEq.ControlSystem",     // ẋ = f(x, u)
            "DiffEq.LinearControl",     // ẋ = Ax + Bu
            "DiffEq.Controllability",   // can reach any state
            "DiffEq.Observability",     // can determine state from output
            "DiffEq.KalmanRank",        // rank condition
            "DiffEq.Stabilizability",   // can stabilize by feedback
            "DiffEq.OptimalControl",    // minimize J[u]
            "DiffEq.PontryaginMaximum", // maximum principle
            "DiffEq.LQR",               // linear-quadratic regulator
            "DiffEq.RiccatiEquation",   // matrix Riccati for LQR
            // ================================================================
            // Delay and Functional Differential Equations
            // ================================================================
            "DiffEq.DelayDE",             // x'(t) = f(t, x(t), x(t-τ))
            "DiffEq.delay_existence",     // existence for DDE
            "DiffEq.delay_stability",     // stability analysis
            "DiffEq.NeutralDDE",          // derivative also delayed
            "DiffEq.IntegroDifferential", // x' = f + ∫K(t,s,x(s))ds
            "DiffEq.VolterraIntegral",    // integral equation
            // ================================================================
            // Stochastic Differential Equations
            // ================================================================
            "DiffEq.SDE",                  // dX = b(X)dt + σ(X)dW
            "DiffEq.BrownianMotion",       // Wiener process W
            "DiffEq.ItoIntegral",          // ∫fdW Ito integral
            "DiffEq.ItoFormula",           // df(X) = ...
            "DiffEq.StratonovichIntegral", // ∫f∘dW
            "DiffEq.sde_existence",        // strong solution existence
            "DiffEq.FokkerPlanck",         // evolution of density
            "DiffEq.LangevinEquation",     // overdamped dynamics
            "DiffEq.ErgodicitySDE",        // long-time behavior
            // ================================================================
            // Geometric PDEs
            // ================================================================
            "DiffEq.MeanCurvatureFlow", // move by mean curvature
            "DiffEq.RicciFlow",         // ∂g/∂t = -2Ric
            "DiffEq.YangMills",         // gauge theory equations
            "DiffEq.EinsteinField",     // G = 8πT
            "DiffEq.MinimalSurface",    // H = 0
            "DiffEq.WillmoreFlow",      // evolution by Willmore energy
            // ================================================================
            // Inverse Problems
            // ================================================================
            "DiffEq.InverseProblem",    // determine coefficients from data
            "DiffEq.CalderonProblem",   // EIT inverse problem
            "DiffEq.InverseScattering", // potential from scattering data
            "DiffEq.DataAssimilation",  // combine model with observations
            "DiffEq.Regularization",    // stabilize ill-posed problems
            "DiffEq.Tikhonov",          // Tikhonov regularization
        ] {
            let decl = Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            };
            self.add_decl(decl)?;
        }

        self.differential_equations_init = true;
        Ok(())
    }

    /// Check if DifferentialEquations has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.differential_equations_init == true`
    #[cfg(test)]
    pub(crate) fn has_differential_equations(&self) -> bool {
        self.differential_equations_init
    }
}
