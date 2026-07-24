// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for advanced mathematical structures
//!
//! This module tests:
//! - Linear algebra (modules, vector spaces, linear maps, matrices)
//! - Category theory (categories, functors, natural transformations, adjunctions)
//! - Homological algebra (chain complexes, homology, derived categories)
//! - Number theory (primes, algebraic number theory, Galois theory)
//! - Algebraic geometry (varieties, schemes, sheaves)
//! - Representation theory (Lie groups, algebras, symmetric groups)
//! - Measure theory (measures, probability, integration)
//! - Functional analysis (Banach/Hilbert spaces, operators)
//! - Differential equations (ODEs, PDEs, dynamical systems)
//! - Combinatorics (graphs, matroids, enumeration)
//! - Optimization (convex, variational calculus, operations research)
//! - Computability (Turing machines, decidability, complexity theory)

use crate::env::test_helpers::assert_const;
use crate::env::*;

#[test]
fn test_differential_equations_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_differential_equations());
    env.init_differential_equations().unwrap();
    assert!(env.has_differential_equations());
}

#[test]
fn test_differential_equations_idempotent() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();
    env.init_differential_equations().unwrap();
    assert!(env.has_differential_equations());
}

#[test]
fn test_differential_equations_basic_ode_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let ode_names = [
        "DiffEq.ODE",
        "DiffEq.InitialValueProblem",
        "DiffEq.BoundaryValueProblem",
        "DiffEq.Solution",
        "DiffEq.MaximalSolution",
        "DiffEq.GlobalSolution",
        "DiffEq.FlowLine",
    ];

    for name in &ode_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_existence_uniqueness_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let eu_names = [
        "DiffEq.LipschitzCondition",
        "DiffEq.LocalLipschitz",
        "DiffEq.PicardLindelof",
        "DiffEq.CauchyPeano",
        "DiffEq.PicardIteration",
        "DiffEq.GronwallInequality",
        "DiffEq.ContinuousDependence",
    ];

    for name in &eu_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_linear_ode_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let linear_names = [
        "DiffEq.LinearODE",
        "DiffEq.HomogeneousLinearODE",
        "DiffEq.ConstantCoeffODE",
        "DiffEq.FundamentalMatrix",
        "DiffEq.Wronskian",
        "DiffEq.MatrixExponential",
        "DiffEq.VariationOfConstants",
    ];

    for name in &linear_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_nonlinear_phase_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let phase_names = [
        "DiffEq.AutonomousODE",
        "DiffEq.PhaseSpace",
        "DiffEq.PhasePortrait",
        "DiffEq.Orbit",
        "DiffEq.Equilibrium",
        "DiffEq.PeriodicOrbit",
        "DiffEq.LimitCycle",
        "DiffEq.Separatrix",
    ];

    for name in &phase_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_stability_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let stability_names = [
        "DiffEq.StableEquilibrium",
        "DiffEq.AsymptoticStability",
        "DiffEq.UnstableEquilibrium",
        "DiffEq.ExponentialStability",
        "DiffEq.GlobalAsymptoticStability",
        "DiffEq.LinearizationStability",
        "DiffEq.HartmanGrobman",
    ];

    for name in &stability_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_lyapunov_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let lyapunov_names = [
        "DiffEq.LyapunovFunction",
        "DiffEq.LyapunovStrictFunction",
        "DiffEq.LyapunovDirect",
        "DiffEq.LaSalleInvariance",
        "DiffEq.LyapunovExponent",
        "DiffEq.MaximalLyapunovExponent",
    ];

    for name in &lyapunov_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_dynamical_systems_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let dyn_names = [
        "DiffEq.DynamicalSystem",
        "DiffEq.Flow",
        "DiffEq.InvariantSet",
        "DiffEq.AttractingSet",
        "DiffEq.BasinOfAttraction",
        "DiffEq.StrangeAttractor",
        "DiffEq.MathverseLimitSet",
    ];

    for name in &dyn_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_bifurcation_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let bif_names = [
        "DiffEq.BifurcationPoint",
        "DiffEq.BifurcationDiagram",
        "DiffEq.SaddleNodeBifurcation",
        "DiffEq.TranscriticalBifurcation",
        "DiffEq.PitchforkBifurcation",
        "DiffEq.HopfBifurcation",
    ];

    for name in &bif_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_chaos_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let chaos_names = [
        "DiffEq.Chaos",
        "DiffEq.SensitiveDependence",
        "DiffEq.PositiveLyapunovExponent",
        "DiffEq.TopologicalTransitivity",
        "DiffEq.LorenzSystem",
        "DiffEq.FractalDimension",
    ];

    for name in &chaos_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_hamiltonian_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let ham_names = [
        "DiffEq.HamiltonianSystem",
        "DiffEq.Hamiltonian",
        "DiffEq.CanonicalCoordinates",
        "DiffEq.PoissonBracket",
        "DiffEq.SymplecticForm",
        "DiffEq.LiouvilleTheorem",
        "DiffEq.IntegrableSystem",
    ];

    for name in &ham_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_pde_basic_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let pde_names = [
        "DiffEq.PDE",
        "DiffEq.LinearPDE",
        "DiffEq.QuasilinearPDE",
        "DiffEq.FullyNonlinearPDE",
        "DiffEq.Order",
        "DiffEq.PDEClassification",
    ];

    for name in &pde_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_first_order_pde_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let first_order_names = [
        "DiffEq.FirstOrderPDE",
        "DiffEq.TransportEquation",
        "DiffEq.CharacteristicCurve",
        "DiffEq.MethodOfCharacteristics",
        "DiffEq.BurgersEquation",
        "DiffEq.HamiltonJacobi",
    ];

    for name in &first_order_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_second_order_pde_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let second_order_names = [
        "DiffEq.SecondOrderLinearPDE",
        "DiffEq.Discriminant",
        "DiffEq.EllipticPDE",
        "DiffEq.ParabolicPDE",
        "DiffEq.HyperbolicPDE",
    ];

    for name in &second_order_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_laplace_poisson_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let laplace_names = [
        "DiffEq.LaplaceEquation",
        "DiffEq.Laplacian",
        "DiffEq.HarmonicFunction",
        "DiffEq.PoissonEquation",
        "DiffEq.MaximumPrinciple",
        "DiffEq.MeanValueProperty",
        "DiffEq.DirichletProblem",
        "DiffEq.GreenFunction",
    ];

    for name in &laplace_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_heat_equation_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let heat_names = [
        "DiffEq.HeatEquation",
        "DiffEq.HeatKernel",
        "DiffEq.heat_convolution",
        "DiffEq.HeatMaximumPrinciple",
        "DiffEq.heat_smoothing",
        "DiffEq.heat_uniqueness",
    ];

    for name in &heat_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_wave_equation_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let wave_names = [
        "DiffEq.WaveEquation",
        "DiffEq.dAlembertFormula",
        "DiffEq.KirchhoffFormula",
        "DiffEq.HuyghensPrinciple",
        "DiffEq.FinitePropagationSpeed",
        "DiffEq.DomainOfDependence",
    ];

    for name in &wave_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_schrodinger_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let schrodinger_names = [
        "DiffEq.SchrodingerEquation",
        "DiffEq.FreeSchrodinger",
        "DiffEq.schrodinger_conservation",
        "DiffEq.NonlinearSchrodinger",
    ];

    for name in &schrodinger_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_fluid_dynamics_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let fluid_names = [
        "DiffEq.NavierStokes",
        "DiffEq.EulerEquations",
        "DiffEq.StokesEquations",
        "DiffEq.Incompressibility",
        "DiffEq.VorticityEquation",
        "DiffEq.ReynoldsNumber",
    ];

    for name in &fluid_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_weak_solutions_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let weak_names = [
        "DiffEq.WeakSolution",
        "DiffEq.WeakDerivative",
        "DiffEq.TestFunction",
        "DiffEq.DistributionalSolution",
        "DiffEq.WeakFormulation",
        "DiffEq.SobolevRegularity",
    ];

    for name in &weak_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_variational_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let var_names = [
        "DiffEq.EulerLagrange",
        "DiffEq.Functional",
        "DiffEq.FirstVariation",
        "DiffEq.DirichletPrinciple",
        "DiffEq.RayleighRitz",
        "DiffEq.DirectMethod",
    ];

    for name in &var_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_semigroups_evolution_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let semi_names = [
        "DiffEq.EvolutionEquation",
        "DiffEq.AbstractCauchyProblem",
        "DiffEq.StronglyContinuousSemigroup",
        "DiffEq.InfinitesimalGenerator",
        "DiffEq.HilleYosida",
        "DiffEq.LumerPhillips",
    ];

    for name in &semi_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_conservation_laws_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let cons_names = [
        "DiffEq.ConservationLaw",
        "DiffEq.WeakSolutionCL",
        "DiffEq.RankineHugoniot",
        "DiffEq.Entropy",
        "DiffEq.EntropySolution",
        "DiffEq.Shock",
        "DiffEq.RiemannProblem",
    ];

    for name in &cons_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_numerical_ode_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let num_ode_names = [
        "DiffEq.EulerMethod",
        "DiffEq.ImplicitEuler",
        "DiffEq.RungeKutta",
        "DiffEq.RK4",
        "DiffEq.AdaptiveStepSize",
        "DiffEq.Stiffness",
        "DiffEq.BDF",
    ];

    for name in &num_ode_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_numerical_pde_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let num_pde_names = [
        "DiffEq.FiniteDifference",
        "DiffEq.CFL",
        "DiffEq.VonNeumannStability",
        "DiffEq.FiniteElement",
        "DiffEq.GalerkinMethod",
        "DiffEq.FiniteVolume",
        "DiffEq.SpectralMethod",
    ];

    for name in &num_pde_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_control_theory_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let control_names = [
        "DiffEq.ControlSystem",
        "DiffEq.LinearControl",
        "DiffEq.Controllability",
        "DiffEq.Observability",
        "DiffEq.KalmanRank",
        "DiffEq.OptimalControl",
        "DiffEq.PontryaginMaximum",
        "DiffEq.LQR",
    ];

    for name in &control_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_stochastic_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let stoch_names = [
        "DiffEq.SDE",
        "DiffEq.BrownianMotion",
        "DiffEq.ItoIntegral",
        "DiffEq.ItoFormula",
        "DiffEq.StratonovichIntegral",
        "DiffEq.FokkerPlanck",
        "DiffEq.LangevinEquation",
    ];

    for name in &stoch_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_geometric_pde_exist() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();

    let geom_names = [
        "DiffEq.MeanCurvatureFlow",
        "DiffEq.RicciFlow",
        "DiffEq.YangMills",
        "DiffEq.EinsteinField",
        "DiffEq.MinimalSurface",
    ];

    for name in &geom_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_differential_equations_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_differential_equations().unwrap();
    assert!(env.has_eq());
    assert!(env.has_nat());
    assert!(env.has_rat());
    assert!(env.has_topological_space());
    assert!(env.has_algebra_linear());
    assert!(env.has_functional_analysis());
}

#[test]
fn test_differential_equations_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_differential_equations().unwrap();
    let after = env.constants.len();

    // Expect a rich collection of differential equations constants plus dependencies
    let diff_eq_count = after - before;
    assert!(
        diff_eq_count >= 250,
        "Expected at least 250 new constants for differential equations (including deps), got {diff_eq_count}"
    );
}

#[test]
fn test_differential_equations_key_types_well_formed() {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_differential_equations().unwrap();
    let tc = TypeChecker::new(&env);

    for name in &[
        "DiffEq.ODE",
        "DiffEq.PDE",
        "DiffEq.LyapunovFunction",
        "DiffEq.NavierStokes",
    ] {
        let expr = Expr::const_(Name::from_string(name), vec![Level::zero()]);
        let ty = tc
            .infer_type(&expr)
            .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
        assert!(
            matches!(&ty.kind, ExprKind::Sort(_) | ExprKind::Pi(..)),
            "{name}: expected Sort or Pi type, got {ty:?}"
        );
    }
}

// ============================================================================
// Combinatorics Tests
// ============================================================================
