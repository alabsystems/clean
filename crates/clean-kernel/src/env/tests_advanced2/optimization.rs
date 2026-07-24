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
fn test_optimization_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_optimization());
    env.init_optimization().unwrap();
    assert!(env.has_optimization());
}

#[test]
fn test_optimization_idempotent() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();
    env.init_optimization().unwrap(); // Should not error
    assert!(env.has_optimization());
}

#[test]
fn test_optimization_convex_sets_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let convex_set_names = [
        "Optimization.ConvexSet",
        "Optimization.AffineSets",
        "Optimization.ConvexHull",
        "Optimization.AffineHull",
        "Optimization.ConicHull",
        "Optimization.Cone",
        "Optimization.ConvexCone",
        "Optimization.ProperCone",
        "Optimization.Polyhedron",
        "Optimization.Polytope",
        "Optimization.Simplex",
        "Optimization.Halfspace",
        "Optimization.Hyperplane",
        "Optimization.Ellipsoid",
        "Optimization.NormBall",
    ];

    for name in convex_set_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_convex_set_operations_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let op_names = [
        "Optimization.ConvexIntersection",
        "Optimization.AffineImage",
        "Optimization.AffinePreimage",
        "Optimization.PerspectiveMap",
        "Optimization.LinearFractional",
        "Optimization.SupportFunction",
        "Optimization.SeparationTheorem",
        "Optimization.SupportingHyperplane",
        "Optimization.ExtremePoint",
        "Optimization.ExposedFace",
    ];

    for name in op_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_convex_functions_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let func_names = [
        "Optimization.ConvexFunction",
        "Optimization.ConcaveFunction",
        "Optimization.StrictlyConvex",
        "Optimization.StronglyConcave",
        "Optimization.QuasiConvex",
        "Optimization.LogConvex",
        "Optimization.LogConcave",
        "Optimization.Epigraph",
        "Optimization.Hypograph",
        "Optimization.Sublevel",
        "Optimization.Indicator",
        "Optimization.ClosedConvex",
        "Optimization.LowerSemicontinuous",
    ];

    for name in func_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_gradients_subgradients_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let grad_names = [
        "Optimization.Gradient",
        "Optimization.Hessian",
        "Optimization.Subgradient",
        "Optimization.Subdifferential",
        "Optimization.DirectionalDerivative",
        "Optimization.ProximalOperator",
        "Optimization.MoreauEnvelope",
        "Optimization.SubgradientMethod",
    ];

    for name in grad_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_problems_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let prob_names = [
        "Optimization.OptimizationProblem",
        "Optimization.Minimizer",
        "Optimization.LocalMinimizer",
        "Optimization.GlobalMinimizer",
        "Optimization.OptimalValue",
        "Optimization.Feasible",
        "Optimization.StrictlyFeasible",
        "Optimization.Infeasible",
        "Optimization.Unbounded",
    ];

    for name in prob_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_constrained_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let constrained_names = [
        "Optimization.EqualityConstraint",
        "Optimization.InequalityConstraint",
        "Optimization.ActiveConstraint",
        "Optimization.Lagrangian",
        "Optimization.LagrangeMultiplier",
        "Optimization.DualFunction",
        "Optimization.DualProblem",
        "Optimization.WeakDuality",
        "Optimization.StrongDuality",
        "Optimization.DualityGap",
        "Optimization.SlaterCondition",
    ];

    for name in constrained_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_kkt_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let kkt_names = [
        "Optimization.KKT",
        "Optimization.Stationarity",
        "Optimization.PrimalFeasibility",
        "Optimization.DualFeasibility",
        "Optimization.ComplementarySlackness",
        "Optimization.ConstraintQualification",
        "Optimization.LICQ",
        "Optimization.MFCQ",
        "Optimization.SCQ",
        "Optimization.SecondOrderConditions",
    ];

    for name in kkt_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_linear_programming_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let lp_names = [
        "Optimization.LinearProgram",
        "Optimization.StandardFormLP",
        "Optimization.BasicFeasibleSolution",
        "Optimization.BasicVariables",
        "Optimization.NonbasicVariables",
        "Optimization.SimplexMethod",
        "Optimization.SimplexTableau",
        "Optimization.PivotOperation",
        "Optimization.ReducedCost",
        "Optimization.DualLP",
        "Optimization.LPDuality",
        "Optimization.ComplementarySlacknessLP",
        "Optimization.DualSimplexMethod",
        "Optimization.InteriorPointLP",
    ];

    for name in lp_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_integer_programming_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let ip_names = [
        "Optimization.IntegerProgram",
        "Optimization.MixedIntegerProgram",
        "Optimization.BinaryProgram",
        "Optimization.LPRelaxation",
        "Optimization.IntegralityGap",
        "Optimization.BranchAndBound",
        "Optimization.BranchAndCut",
        "Optimization.CuttingPlane",
        "Optimization.GomorysCut",
        "Optimization.TotalUnimodularity",
    ];

    for name in ip_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_conic_programming_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let conic_names = [
        "Optimization.ConicProgram",
        "Optimization.SecondOrderConeProgram",
        "Optimization.SecondOrderCone",
        "Optimization.SemidefiniteProgram",
        "Optimization.SemidefiniteCone",
        "Optimization.LinearMatrixInequality",
        "Optimization.SDPDuality",
        "Optimization.SDPRelaxation",
    ];

    for name in conic_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_algorithms_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let algo_names = [
        "Optimization.GradientDescent",
        "Optimization.SteepestDescent",
        "Optimization.NewtonsMethod",
        "Optimization.QuasiNewton",
        "Optimization.BFGS",
        "Optimization.LBFGS",
        "Optimization.ConjugateGradient",
        "Optimization.TrustRegion",
        "Optimization.LineSearch",
        "Optimization.ArmijoCondition",
        "Optimization.WolfeConditions",
        "Optimization.BacktrackingLineSearch",
        "Optimization.ConvergenceRate",
    ];

    for name in algo_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_proximal_methods_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let proximal_names = [
        "Optimization.ProximalGradient",
        "Optimization.ISTA",
        "Optimization.FISTA",
        "Optimization.ADMM",
        "Optimization.DouglasRachford",
        "Optimization.ForwardBackward",
        "Optimization.PrimalDualSplitting",
    ];

    for name in proximal_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_stochastic_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let stoch_names = [
        "Optimization.StochasticOptimization",
        "Optimization.SGD",
        "Optimization.MiniBatchSGD",
        "Optimization.Adam",
        "Optimization.Momentum",
        "Optimization.NesterovMomentum",
        "Optimization.VarianceReduction",
        "Optimization.SampleAverageApproximation",
        "Optimization.ExpectedValue",
        "Optimization.ChanceConstraint",
        "Optimization.RobustOptimization",
    ];

    for name in stoch_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_variational_calculus_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let var_names = [
        "Optimization.Functional",
        "Optimization.EulerLagrangeEquation",
        "Optimization.FirstVariation",
        "Optimization.SecondVariation",
        "Optimization.NecessaryCondition",
        "Optimization.SufficientCondition",
        "Optimization.NaturalBoundary",
        "Optimization.EssentialBoundary",
        "Optimization.TransversalityCondition",
        "Optimization.WeierstrassCondition",
        "Optimization.LegendreCondition",
        "Optimization.JacobiCondition",
        "Optimization.ConjugatePoints",
    ];

    for name in var_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_variational_problems_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let prob_names = [
        "Optimization.Brachistochrone",
        "Optimization.Geodesic",
        "Optimization.Catenary",
        "Optimization.MinimalSurface",
        "Optimization.IsoperimetricProblem",
        "Optimization.IsoperimetricConstraint",
        "Optimization.LagrangeMultiplierVC",
        "Optimization.BolzaProblem",
        "Optimization.MayerProblem",
        "Optimization.LagrangeProblem",
    ];

    for name in prob_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_optimal_control_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let control_names = [
        "Optimization.OptimalControl",
        "Optimization.StateVariable",
        "Optimization.ControlVariable",
        "Optimization.ControlHamiltonian",
        "Optimization.Costate",
        "Optimization.PontryaginMaximum",
        "Optimization.HamiltonJacobiBellman",
        "Optimization.BellmanEquation",
        "Optimization.ValueFunction",
        "Optimization.BangBangControl",
        "Optimization.SingularArc",
        "Optimization.LQR",
        "Optimization.RiccatiEquation",
    ];

    for name in control_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_dynamic_programming_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let dp_names = [
        "Optimization.DynamicProgramming",
        "Optimization.OptimalSubstructure",
        "Optimization.OverlappingSubproblems",
        "Optimization.Memoization",
        "Optimization.Tabulation",
        "Optimization.StateSpace",
        "Optimization.TransitionFunction",
        "Optimization.BellmanOptimality",
        "Optimization.PolicyIteration",
        "Optimization.ValueIteration",
        "Optimization.MarkovDecisionProcess",
    ];

    for name in dp_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_combinatorial_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let comb_names = [
        "Optimization.CombinatorialOpt",
        "Optimization.TravelingSalesman",
        "Optimization.Knapsack",
        "Optimization.BinPacking",
        "Optimization.VehicleRouting",
        "Optimization.AssignmentProblem",
        "Optimization.HungarianAlgorithm",
        "Optimization.MaximumFlow",
        "Optimization.MinimumCostFlow",
        "Optimization.ShortestPath",
        "Optimization.SetCover",
        "Optimization.MaxCut",
        "Optimization.GraphColoring",
    ];

    for name in comb_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_scheduling_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let sched_names = [
        "Optimization.Scheduling",
        "Optimization.JobShop",
        "Optimization.FlowShop",
        "Optimization.SingleMachine",
        "Optimization.ParallelMachines",
        "Optimization.Makespan",
        "Optimization.TotalWeightedTardiness",
        "Optimization.PreemptiveScheduling",
        "Optimization.PrecedenceConstraints",
        "Optimization.ResourceConstraints",
    ];

    for name in sched_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_approximation_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let approx_names = [
        "Optimization.ApproximationAlgorithm",
        "Optimization.ApproximationRatio",
        "Optimization.PTAS",
        "Optimization.FPTAS",
        "Optimization.GreedyAlgorithm",
        "Optimization.LocalSearch",
        "Optimization.SimulatedAnnealing",
        "Optimization.TabuSearch",
        "Optimization.GeneticAlgorithm",
        "Optimization.AntColony",
        "Optimization.ParticleSwarm",
    ];

    for name in approx_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_game_theory_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let game_names = [
        "Optimization.Game",
        "Optimization.Player",
        "Optimization.Strategy",
        "Optimization.Payoff",
        "Optimization.NashEquilibrium",
        "Optimization.MixedStrategy",
        "Optimization.PureStrategy",
        "Optimization.DominantStrategy",
        "Optimization.DominatedStrategy",
        "Optimization.BestResponse",
        "Optimization.ZeroSumGame",
        "Optimization.MinimaxTheorem",
        "Optimization.SaddlePoint",
        "Optimization.CooperativeGame",
        "Optimization.ShapleyValue",
        "Optimization.CoreGame",
    ];

    for name in game_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_mechanism_design_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let mech_names = [
        "Optimization.MechanismDesign",
        "Optimization.SocialChoice",
        "Optimization.IncentiveCompatibility",
        "Optimization.IndividualRationality",
        "Optimization.VCGMechanism",
        "Optimization.AuctionDesign",
        "Optimization.RevenueEquivalence",
    ];

    for name in mech_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_multi_objective_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let mo_names = [
        "Optimization.MultiObjective",
        "Optimization.ParetoOptimal",
        "Optimization.ParetoFrontier",
        "Optimization.Dominance",
        "Optimization.NonDominated",
        "Optimization.WeightedSum",
        "Optimization.EpsilonConstraint",
        "Optimization.UtopiaPoint",
        "Optimization.NadirPoint",
    ];

    for name in mo_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_global_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let global_names = [
        "Optimization.GlobalOptimization",
        "Optimization.NonConvex",
        "Optimization.MultiModal",
        "Optimization.BranchAndBoundGlobal",
        "Optimization.ConvexRelaxation",
        "Optimization.LipschitzOptimization",
        "Optimization.BasinHopping",
        "Optimization.DifferentialEvolution",
    ];

    for name in global_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_bilevel_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let bilevel_names = [
        "Optimization.BilevelOptimization",
        "Optimization.LeaderFollower",
        "Optimization.OptimalityConditionReformulation",
        "Optimization.ValueFunctionReformulation",
    ];

    for name in bilevel_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_theorems_exist() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();

    let thm_names = [
        "Optimization.ExistenceTheorem",
        "Optimization.UniquenessTheorem",
        "Optimization.WeakConvergence",
        "Optimization.StrongConvergence",
        "Optimization.CompactnessArgument",
        "Optimization.CoerciveFunction",
        "Optimization.FenchelDuality",
        "Optimization.MinimaxInequality",
        "Optimization.SaddlePointTheorem",
        "Optimization.KKTSufficiency",
    ];

    for name in thm_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_optimization_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_optimization().unwrap();
    assert!(env.has_eq());
    assert!(env.has_nat());
    assert!(env.has_int());
    assert!(env.has_rat());
    assert!(env.has_list());
}

#[test]
fn test_optimization_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_optimization().unwrap();
    let after = env.constants.len();

    // Expect a rich collection of optimization constants plus dependencies
    let opt_count = after - before;
    assert!(
        opt_count >= 250,
        "Expected at least 250 new constants for optimization (including deps), got {opt_count}"
    );
}

#[test]
fn test_optimization_key_types_well_formed() {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_optimization().unwrap();
    let tc = TypeChecker::new(&env);

    for name in &[
        "Optimization.ConvexSet",
        "Optimization.LinearProgram",
        "Optimization.GradientDescent",
        "Optimization.NashEquilibrium",
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
// Computability Theory Tests
// ============================================================================
