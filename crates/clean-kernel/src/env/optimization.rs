// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Optimization structures for Environment
//!
//! This module contains optimization initialization:
//! - Convex optimization (convex sets, functions, duality)
//! - Variational calculus (Euler-Lagrange, functionals)
//! - Linear programming (LP, simplex, duality)
//! - Nonlinear programming (KKT, constrained optimization)
//! - Operations research (scheduling, assignment, networks)
//! - Dynamic programming (Bellman, optimal control)
//! - Game theory (Nash equilibrium, minimax)

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
    /// Initialize Optimization module
    ///
    /// Optimization is the mathematics of finding best solutions within
    /// constraints. It underpins:
    /// - Machine learning (gradient descent, convex optimization)
    /// - Resource allocation (linear programming, scheduling)
    /// - Control systems (optimal control, dynamic programming)
    /// - Economics (game theory, mechanism design)
    ///
    /// Key areas:
    /// - Convex optimization: convex sets/functions, duality theory
    /// - Variational calculus: functionals, Euler-Lagrange equations
    /// - Linear programming: simplex method, LP duality
    /// - Nonlinear programming: KKT conditions, constraint qualification
    /// - Operations research: combinatorial optimization, scheduling
    /// - Dynamic programming: Bellman optimality, optimal control
    /// - Game theory: Nash equilibrium, minimax theorems
    ///
    /// This module provides axioms for:
    /// - Convexity and convex analysis
    /// - Optimality conditions (first-order, second-order)
    /// - Duality theory (Lagrangian, Fenchel)
    /// - Algorithmic foundations
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.optimization_init == true`
    /// ENSURES: On success, required dependencies (`eq`, `nat`, `int`, `rat`, `list`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_optimization(&mut self) -> Result<(), EnvError> {
        if self.optimization_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_rat()?;
        self.init_list()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Optimization constants
        for name in &[
            // ================================================================
            // Convex Sets
            // ================================================================
            "Optimization.ConvexSet",  // λx y θ. θx + (1-θ)y ∈ S
            "Optimization.AffineSets", // affine subspace
            "Optimization.ConvexHull", // conv(S)
            "Optimization.AffineHull", // aff(S)
            "Optimization.ConicHull",  // cone(S)
            "Optimization.Cone",       // closed under positive scaling
            "Optimization.ConvexCone", // convex cone
            "Optimization.ProperCone", // pointed, closed, solid
            "Optimization.Polyhedron", // intersection of halfspaces
            "Optimization.Polytope",   // bounded polyhedron
            "Optimization.Simplex",    // n-simplex
            "Optimization.Halfspace",  // {x : aᵀx ≤ b}
            "Optimization.Hyperplane", // {x : aᵀx = b}
            "Optimization.Ellipsoid",  // {x : (x-c)ᵀP⁻¹(x-c) ≤ 1}
            "Optimization.NormBall",   // {x : ‖x‖ ≤ r}
            // ================================================================
            // Convex Set Operations
            // ================================================================
            "Optimization.ConvexIntersection", // intersection preserves convexity
            "Optimization.AffineImage",        // f(C) convex if C convex, f affine
            "Optimization.AffinePreimage",     // f⁻¹(C) convex
            "Optimization.PerspectiveMap",     // (x,t) ↦ x/t
            "Optimization.LinearFractional",   // (Ax+b)/(cᵀx+d)
            "Optimization.SupportFunction",    // σ_C(y) = sup{yᵀx : x ∈ C}
            "Optimization.SeparationTheorem",  // hyperplane separation
            "Optimization.SupportingHyperplane", // supporting hyperplane
            "Optimization.ExtremePoint",       // vertex of convex set
            "Optimization.ExposedFace",        // face exposed by hyperplane
            // ================================================================
            // Convex Functions
            // ================================================================
            "Optimization.ConvexFunction", // f(θx + (1-θ)y) ≤ θf(x) + (1-θ)f(y)
            "Optimization.ConcaveFunction", // -f convex
            "Optimization.StrictlyConvex", // strict inequality for θ ∈ (0,1)
            "Optimization.StronglyConcave", // f - (m/2)‖x‖² convex
            "Optimization.QuasiConvex",    // sublevel sets convex
            "Optimization.LogConvex",      // log f convex
            "Optimization.LogConcave",     // log f concave
            "Optimization.Epigraph",       // epi f = {(x,t) : f(x) ≤ t}
            "Optimization.Hypograph",      // hypo f = {(x,t) : f(x) ≥ t}
            "Optimization.Sublevel",       // {x : f(x) ≤ α}
            "Optimization.Indicator",      // I_C(x) = 0 if x ∈ C, ∞ otherwise
            "Optimization.ClosedConvex",   // closed and convex
            "Optimization.LowerSemicontinuous", // lim inf f(xₙ) ≥ f(x)
            // ================================================================
            // Convex Function Operations
            // ================================================================
            "Optimization.ConvexSum",           // αf + βg convex for α,β ≥ 0
            "Optimization.PointwiseMaximum",    // max{f,g} convex
            "Optimization.PointwiseSupremum",   // sup_i f_i convex
            "Optimization.Composition",         // h(g(x)) convex when...
            "Optimization.PerspectiveFunction", // tf(x/t)
            "Optimization.InfimalConvolution",  // (f □ g)(x) = inf_y f(y) + g(x-y)
            "Optimization.Conjugate",           // f*(y) = sup_x yᵀx - f(x)
            "Optimization.Biconjugate",         // f** = cl(conv(f))
            // ================================================================
            // Gradients and Subgradients
            // ================================================================
            "Optimization.Gradient",              // ∇f(x)
            "Optimization.Hessian",               // ∇²f(x)
            "Optimization.Subgradient",           // g : f(y) ≥ f(x) + gᵀ(y-x) ∀y
            "Optimization.Subdifferential",       // ∂f(x) = set of subgradients
            "Optimization.DirectionalDerivative", // f'(x;d) = lim (f(x+td)-f(x))/t
            "Optimization.ProximalOperator",      // prox_f(x) = argmin_y f(y) + ‖y-x‖²/2
            "Optimization.MoreauEnvelope",        // M_f(x) = min_y f(y) + ‖y-x‖²/2λ
            "Optimization.SubgradientMethod",     // x_{k+1} = x_k - α_k g_k
            // ================================================================
            // Optimization Problems
            // ================================================================
            "Optimization.OptimizationProblem", // minimize f(x) s.t. x ∈ C
            "Optimization.Minimizer",           // x* : f(x*) ≤ f(x) ∀x ∈ C
            "Optimization.LocalMinimizer",      // local minimum
            "Optimization.GlobalMinimizer",     // global minimum
            "Optimization.OptimalValue",        // p* = inf f(x)
            "Optimization.Feasible",            // x ∈ C
            "Optimization.StrictlyFeasible",    // x ∈ int(C)
            "Optimization.Infeasible",          // C = ∅
            "Optimization.Unbounded",           // p* = -∞
            // ================================================================
            // Constrained Optimization
            // ================================================================
            "Optimization.EqualityConstraint",   // h(x) = 0
            "Optimization.InequalityConstraint", // g(x) ≤ 0
            "Optimization.ActiveConstraint",     // g_i(x*) = 0
            "Optimization.Lagrangian",           // L(x,λ,ν) = f(x) + λᵀg(x) + νᵀh(x)
            "Optimization.LagrangeMultiplier",   // λ, ν
            "Optimization.DualFunction",         // g(λ,ν) = inf_x L(x,λ,ν)
            "Optimization.DualProblem",          // maximize g(λ,ν)
            "Optimization.WeakDuality",          // d* ≤ p*
            "Optimization.StrongDuality",        // d* = p*
            "Optimization.DualityGap",           // p* - d*
            "Optimization.SlaterCondition",      // strictly feasible point exists
            // ================================================================
            // KKT Conditions
            // ================================================================
            "Optimization.KKT",                     // KKT conditions
            "Optimization.Stationarity",            // ∇f + Σλ_i∇g_i + Σν_j∇h_j = 0
            "Optimization.PrimalFeasibility",       // g(x) ≤ 0, h(x) = 0
            "Optimization.DualFeasibility",         // λ ≥ 0
            "Optimization.ComplementarySlackness",  // λ_i g_i(x) = 0
            "Optimization.ConstraintQualification", // CQ for KKT necessity
            "Optimization.LICQ",                    // linear independence CQ
            "Optimization.MFCQ",                    // Mangasarian-Fromovitz CQ
            "Optimization.SCQ",                     // Slater's CQ
            "Optimization.SecondOrderConditions",   // sufficient conditions
            // ================================================================
            // Linear Programming
            // ================================================================
            "Optimization.LinearProgram",         // min cᵀx s.t. Ax ≤ b
            "Optimization.StandardFormLP",        // min cᵀx s.t. Ax = b, x ≥ 0
            "Optimization.BasicFeasibleSolution", // BFS
            "Optimization.BasicVariables",        // basic variables
            "Optimization.NonbasicVariables",     // nonbasic variables
            "Optimization.SimplexMethod",         // simplex algorithm
            "Optimization.SimplexTableau",        // tableau form
            "Optimization.PivotOperation",        // pivot step
            "Optimization.ReducedCost",           // c̄_j = c_j - c_B^T B^{-1} A_j
            "Optimization.DualLP",                // max bᵀy s.t. Aᵀy ≤ c
            "Optimization.LPDuality",             // strong duality for LP
            "Optimization.ComplementarySlacknessLP", // LP complementary slackness
            "Optimization.DualSimplexMethod",     // dual simplex
            "Optimization.InteriorPointLP",       // interior point for LP
            // ================================================================
            // Integer Programming
            // ================================================================
            "Optimization.IntegerProgram", // IP with integer variables
            "Optimization.MixedIntegerProgram", // MIP
            "Optimization.BinaryProgram",  // 0-1 IP
            "Optimization.LPRelaxation",   // LP relaxation of IP
            "Optimization.IntegralityGap", // ratio of LP to IP optima
            "Optimization.BranchAndBound", // B&B algorithm
            "Optimization.BranchAndCut",   // B&C with cutting planes
            "Optimization.CuttingPlane",   // valid inequality
            "Optimization.GomorysCut",     // Gomory fractional cut
            "Optimization.TotalUnimodularity", // TU matrices
            // ================================================================
            // Quadratic Programming
            // ================================================================
            "Optimization.QuadraticProgram", // min ½xᵀQx + cᵀx
            "Optimization.QP",               // QP shorthand
            "Optimization.ConvexQP",         // Q ≽ 0
            "Optimization.ActiveSetMethod",  // active set for QP
            "Optimization.InteriorPointQP",  // interior point for QP
            // ================================================================
            // Conic Programming
            // ================================================================
            "Optimization.ConicProgram", // min cᵀx s.t. Ax = b, x ∈ K
            "Optimization.SecondOrderConeProgram", // SOCP
            "Optimization.SecondOrderCone", // ‖Ax+b‖₂ ≤ cᵀx+d
            "Optimization.SemidefiniteProgram", // SDP
            "Optimization.SemidefiniteCone", // X ≽ 0 (PSD cone)
            "Optimization.LinearMatrixInequality", // LMI: F₀ + Σx_iF_i ≽ 0
            "Optimization.SDPDuality",   // SDP duality theory
            "Optimization.SDPRelaxation", // SDP relaxation of hard problems
            // ================================================================
            // Nonlinear Optimization Algorithms
            // ================================================================
            "Optimization.GradientDescent", // x_{k+1} = x_k - α∇f(x_k)
            "Optimization.SteepestDescent", // optimal step size
            "Optimization.NewtonsMethod",   // x_{k+1} = x_k - [∇²f]⁻¹∇f
            "Optimization.QuasiNewton",     // approximate Hessian
            "Optimization.BFGS",            // BFGS update
            "Optimization.LBFGS",           // limited-memory BFGS
            "Optimization.ConjugateGradient", // CG method
            "Optimization.TrustRegion",     // trust region method
            "Optimization.LineSearch",      // line search
            "Optimization.ArmijoCondition", // sufficient decrease
            "Optimization.WolfeConditions", // Armijo + curvature
            "Optimization.BacktrackingLineSearch", // backtracking
            "Optimization.ConvergenceRate", // linear, superlinear, quadratic
            // ================================================================
            // Proximal Methods
            // ================================================================
            "Optimization.ProximalGradient", // proximal gradient method
            "Optimization.ISTA",             // iterative shrinkage-thresholding
            "Optimization.FISTA",            // fast ISTA (accelerated)
            "Optimization.ADMM",             // alternating direction method of multipliers
            "Optimization.DouglasRachford",  // Douglas-Rachford splitting
            "Optimization.ForwardBackward",  // forward-backward splitting
            "Optimization.PrimalDualSplitting", // primal-dual methods
            // ================================================================
            // Stochastic Optimization
            // ================================================================
            "Optimization.StochasticOptimization", // E[f(x,ξ)]
            "Optimization.SGD",                    // stochastic gradient descent
            "Optimization.MiniBatchSGD",           // mini-batch SGD
            "Optimization.Adam",                   // Adam optimizer
            "Optimization.Momentum",               // momentum method
            "Optimization.NesterovMomentum",       // Nesterov accelerated gradient
            "Optimization.VarianceReduction",      // SVRG, SAGA
            "Optimization.SampleAverageApproximation", // SAA
            "Optimization.ExpectedValue",          // expected value problem
            "Optimization.ChanceConstraint",       // P[g(x,ξ) ≤ 0] ≥ 1-ε
            "Optimization.RobustOptimization",     // min max_ξ f(x,ξ)
            // ================================================================
            // Variational Calculus
            // ================================================================
            "Optimization.Functional",              // J[y] = ∫F(x,y,y')dx
            "Optimization.EulerLagrangeEquation",   // Fy - d/dx Fy' = 0
            "Optimization.FirstVariation",          // δJ[y; η]
            "Optimization.SecondVariation",         // δ²J[y; η]
            "Optimization.NecessaryCondition",      // first variation = 0
            "Optimization.SufficientCondition",     // second variation ≥ 0
            "Optimization.NaturalBoundary",         // natural boundary conditions
            "Optimization.EssentialBoundary",       // essential boundary conditions
            "Optimization.TransversalityCondition", // free endpoint condition
            "Optimization.WeierstrassCondition",    // Weierstrass E-function ≥ 0
            "Optimization.LegendreCondition",       // Fyy' ≥ 0
            "Optimization.JacobiCondition",         // Jacobi equation/accessory problem
            "Optimization.ConjugatePoints",         // conjugate points
            // ================================================================
            // Variational Problems
            // ================================================================
            "Optimization.Brachistochrone",         // fastest descent
            "Optimization.Geodesic",                // shortest path
            "Optimization.Catenary",                // hanging chain
            "Optimization.MinimalSurface",          // minimal surface area
            "Optimization.IsoperimetricProblem",    // max area for fixed perimeter
            "Optimization.IsoperimetricConstraint", // ∫G(x,y,y')dx = const
            "Optimization.LagrangeMultiplierVC",    // multiplier for constraints
            "Optimization.BolzaProblem",            // Mayer + Lagrange terms
            "Optimization.MayerProblem",            // minimize Φ(x(T),T)
            "Optimization.LagrangeProblem",         // minimize ∫L dt
            // ================================================================
            // Optimal Control
            // ================================================================
            "Optimization.OptimalControl",     // min J s.t. ẋ = f(x,u)
            "Optimization.StateVariable",      // x(t)
            "Optimization.ControlVariable",    // u(t)
            "Optimization.ControlHamiltonian", // H(x,u,p) = L + pᵀf
            "Optimization.Costate",            // adjoint variable p(t)
            "Optimization.PontryaginMaximum",  // Pontryagin's maximum principle
            "Optimization.HamiltonJacobiBellman", // HJB equation
            "Optimization.BellmanEquation",    // V(x) = min_u [L + V(f)]
            "Optimization.ValueFunction",      // optimal cost-to-go
            "Optimization.BangBangControl",    // control at extremes
            "Optimization.SingularArc",        // singular control
            "Optimization.LQR",                // linear-quadratic regulator
            "Optimization.RiccatiEquation",    // matrix Riccati equation
            // ================================================================
            // Dynamic Programming
            // ================================================================
            "Optimization.DynamicProgramming",     // DP principle
            "Optimization.OptimalSubstructure",    // optimal subproblems
            "Optimization.OverlappingSubproblems", // reuse computations
            "Optimization.Memoization",            // top-down with cache
            "Optimization.Tabulation",             // bottom-up DP
            "Optimization.StateSpace",             // DP state space
            "Optimization.TransitionFunction",     // state transition
            "Optimization.BellmanOptimality",      // Bellman optimality principle
            "Optimization.PolicyIteration",        // policy iteration
            "Optimization.ValueIteration",         // value iteration
            "Optimization.MarkovDecisionProcess",  // MDP
            // ================================================================
            // Combinatorial Optimization
            // ================================================================
            "Optimization.CombinatorialOpt",  // discrete optimization
            "Optimization.TravelingSalesman", // TSP
            "Optimization.Knapsack",          // knapsack problem
            "Optimization.BinPacking",        // bin packing
            "Optimization.VehicleRouting",    // VRP
            "Optimization.AssignmentProblem", // bipartite assignment
            "Optimization.HungarianAlgorithm", // Hungarian method
            "Optimization.MaximumFlow",       // max flow
            "Optimization.MinimumCostFlow",   // min cost flow
            "Optimization.ShortestPath",      // shortest path
            "Optimization.SetCover",          // set cover
            "Optimization.MaxCut",            // maximum cut
            "Optimization.GraphColoring",     // graph coloring
            // ================================================================
            // Scheduling
            // ================================================================
            "Optimization.Scheduling",             // scheduling problems
            "Optimization.JobShop",                // job shop scheduling
            "Optimization.FlowShop",               // flow shop scheduling
            "Optimization.SingleMachine",          // single machine scheduling
            "Optimization.ParallelMachines",       // parallel machines
            "Optimization.Makespan",               // completion time
            "Optimization.TotalWeightedTardiness", // tardiness objective
            "Optimization.PreemptiveScheduling",   // preemption allowed
            "Optimization.PrecedenceConstraints",  // precedence
            "Optimization.ResourceConstraints",    // resource-constrained
            // ================================================================
            // Approximation Algorithms
            // ================================================================
            "Optimization.ApproximationAlgorithm", // polynomial approximation
            "Optimization.ApproximationRatio",     // c-approximation
            "Optimization.PTAS",                   // polynomial-time approx scheme
            "Optimization.FPTAS",                  // fully PTAS
            "Optimization.GreedyAlgorithm",        // greedy approach
            "Optimization.LocalSearch",            // local search
            "Optimization.SimulatedAnnealing",     // simulated annealing
            "Optimization.TabuSearch",             // tabu search
            "Optimization.GeneticAlgorithm",       // genetic/evolutionary
            "Optimization.AntColony",              // ant colony optimization
            "Optimization.ParticleSwarm",          // particle swarm
            // ================================================================
            // Game Theory
            // ================================================================
            "Optimization.Game",              // strategic game
            "Optimization.Player",            // player
            "Optimization.Strategy",          // strategy
            "Optimization.Payoff",            // payoff function
            "Optimization.NashEquilibrium",   // Nash equilibrium
            "Optimization.MixedStrategy",     // randomized strategy
            "Optimization.PureStrategy",      // deterministic strategy
            "Optimization.DominantStrategy",  // dominant strategy
            "Optimization.DominatedStrategy", // dominated strategy
            "Optimization.BestResponse",      // best response
            "Optimization.ZeroSumGame",       // zero-sum game
            "Optimization.MinimaxTheorem",    // von Neumann minimax
            "Optimization.SaddlePoint",       // saddle point
            "Optimization.CooperativeGame",   // coalitional game
            "Optimization.ShapleyValue",      // Shapley value
            "Optimization.CoreGame",          // core of a game
            // ================================================================
            // Mechanism Design
            // ================================================================
            "Optimization.MechanismDesign",        // mechanism design
            "Optimization.SocialChoice",           // social choice function
            "Optimization.IncentiveCompatibility", // incentive compatibility
            "Optimization.IndividualRationality",  // IR constraint
            "Optimization.VCGMechanism",           // Vickrey-Clarke-Groves
            "Optimization.AuctionDesign",          // optimal auction
            "Optimization.RevenueEquivalence",     // revenue equivalence
            // ================================================================
            // Multi-objective Optimization
            // ================================================================
            "Optimization.MultiObjective",    // multi-objective problem
            "Optimization.ParetoOptimal",     // Pareto optimal
            "Optimization.ParetoFrontier",    // Pareto frontier
            "Optimization.Dominance",         // Pareto dominance
            "Optimization.NonDominated",      // non-dominated solution
            "Optimization.WeightedSum",       // weighted sum scalarization
            "Optimization.EpsilonConstraint", // ε-constraint method
            "Optimization.UtopiaPoint",       // ideal point
            "Optimization.NadirPoint",        // nadir point
            // ================================================================
            // Global Optimization
            // ================================================================
            "Optimization.GlobalOptimization", // global optimization
            "Optimization.NonConvex",          // non-convex problem
            "Optimization.MultiModal",         // multiple local optima
            "Optimization.BranchAndBoundGlobal", // B&B for global
            "Optimization.ConvexRelaxation",   // convex relaxation
            "Optimization.LipschitzOptimization", // Lipschitz global opt
            "Optimization.BasinHopping",       // basin hopping
            "Optimization.DifferentialEvolution", // differential evolution
            // ================================================================
            // Bilevel Optimization
            // ================================================================
            "Optimization.BilevelOptimization", // bilevel program
            "Optimization.LeaderFollower",      // Stackelberg game
            "Optimization.OptimalityConditionReformulation", // KKT reformulation
            "Optimization.ValueFunctionReformulation", // value function approach
            // ================================================================
            // Theorems and Properties
            // ================================================================
            "Optimization.ExistenceTheorem", // existence of minimizers
            "Optimization.UniquenessTheorem", // uniqueness conditions
            "Optimization.WeakConvergence",  // weak convergence
            "Optimization.StrongConvergence", // strong convergence
            "Optimization.CompactnessArgument", // Weierstrass theorem
            "Optimization.CoerciveFunction", // f(x) → ∞ as ‖x‖ → ∞
            "Optimization.FenchelDuality",   // Fenchel duality theorem
            "Optimization.MinimaxInequality", // sup inf ≤ inf sup
            "Optimization.SaddlePointTheorem", // saddle point existence
            "Optimization.KKTSufficiency",   // KKT sufficient for convex
        ] {
            let decl = Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            };
            self.add_decl(decl)?;
        }

        self.optimization_init = true;
        Ok(())
    }

    /// Check if Optimization has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_optimization` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_optimization(&self) -> bool {
        self.optimization_init
    }
}
