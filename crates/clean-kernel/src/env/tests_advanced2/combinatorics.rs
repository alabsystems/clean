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
fn test_combinatorics_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_combinatorics());
    env.init_combinatorics().unwrap();
    assert!(env.has_combinatorics());
}

#[test]
fn test_combinatorics_idempotent() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();
    env.init_combinatorics().unwrap();
    assert!(env.has_combinatorics());
}

#[test]
fn test_combinatorics_basic_graphs_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    // Basic graph structures
    for name in &[
        "Combinatorics.Graph",
        "Combinatorics.SimpleGraph",
        "Combinatorics.Digraph",
        "Combinatorics.Multigraph",
        "Combinatorics.Hypergraph",
        "Combinatorics.Vertex",
        "Combinatorics.Edge",
        "Combinatorics.adj",
        "Combinatorics.degree",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_paths_cycles_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.Walk",
        "Combinatorics.Path",
        "Combinatorics.Cycle",
        "Combinatorics.Trail",
        "Combinatorics.EulerianPath",
        "Combinatorics.HamiltonianPath",
        "Combinatorics.Girth",
        "Combinatorics.Diameter",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_connectivity_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.Connected",
        "Combinatorics.ConnectedComponent",
        "Combinatorics.StronglyConnected",
        "Combinatorics.Biconnected",
        "Combinatorics.ArticulationPoint",
        "Combinatorics.Bridge",
        "Combinatorics.connectivity",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_special_graphs_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.CompleteGraph",
        "Combinatorics.CompleteBipartite",
        "Combinatorics.Bipartite",
        "Combinatorics.Tree",
        "Combinatorics.Forest",
        "Combinatorics.PlanarGraph",
        "Combinatorics.PetersenGraph",
        "Combinatorics.RegularGraph",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_graph_coloring_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.Coloring",
        "Combinatorics.EdgeColoring",
        "Combinatorics.ChromaticNumber",
        "Combinatorics.ChromaticPolynomial",
        "Combinatorics.BrooksTheorem",
        "Combinatorics.VizingTheorem",
        "Combinatorics.FourColorTheorem",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_matchings_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.Matching",
        "Combinatorics.MaximumMatching",
        "Combinatorics.PerfectMatching",
        "Combinatorics.VertexCover",
        "Combinatorics.IndependentSet",
        "Combinatorics.Clique",
        "Combinatorics.HallMarriageTheorem",
        "Combinatorics.KonigTheorem",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_graph_operations_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.Subgraph",
        "Combinatorics.InducedSubgraph",
        "Combinatorics.GraphUnion",
        "Combinatorics.CartesianProduct",
        "Combinatorics.LineGraph",
        "Combinatorics.Complement",
        "Combinatorics.GraphMinor",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_graph_theorems_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.HandshakingLemma",
        "Combinatorics.EulerFormula",
        "Combinatorics.KuratowskiTheorem",
        "Combinatorics.MengerTheorem",
        "Combinatorics.DilworthTheorem",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_trees_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.SpanningTree",
        "Combinatorics.MinimumSpanningTree",
        "Combinatorics.CayleyFormula",
        "Combinatorics.PruferCode",
        "Combinatorics.MatrixTreeTheorem",
        "Combinatorics.RootedTree",
        "Combinatorics.BinaryTree",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_network_flows_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.Network",
        "Combinatorics.Flow",
        "Combinatorics.MaxFlow",
        "Combinatorics.MinCut",
        "Combinatorics.MaxFlowMinCut",
        "Combinatorics.FordFulkerson",
        "Combinatorics.AugmentingPath",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_matroids_basic_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.Matroid",
        "Combinatorics.IndependentSet_M",
        "Combinatorics.Basis_M",
        "Combinatorics.Circuit_M",
        "Combinatorics.Rank",
        "Combinatorics.Closure",
        "Combinatorics.Flat",
        "Combinatorics.Hyperplane",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_matroid_examples_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.UniformMatroid",
        "Combinatorics.VectorMatroid",
        "Combinatorics.GraphicMatroid",
        "Combinatorics.CographicMatroid",
        "Combinatorics.TransversalMatroid",
        "Combinatorics.FanoMatroid",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_matroid_operations_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.MatroidDual",
        "Combinatorics.MatroidMinor",
        "Combinatorics.Deletion",
        "Combinatorics.Contraction",
        "Combinatorics.MatroidUnion",
        "Combinatorics.MatroidIntersection",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_ogf_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.OGF",
        "Combinatorics.ogf_add",
        "Combinatorics.ogf_mul",
        "Combinatorics.ogf_shift",
        "Combinatorics.ogf_derivative",
        "Combinatorics.ogf_composition",
        "Combinatorics.ogf_extract",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_egf_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.EGF",
        "Combinatorics.egf_add",
        "Combinatorics.egf_mul",
        "Combinatorics.egf_composition",
        "Combinatorics.egf_derivative",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_standard_gf_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.ogf_geometric",
        "Combinatorics.ogf_binomial",
        "Combinatorics.egf_exp",
        "Combinatorics.ogf_fibonacci",
        "Combinatorics.ogf_catalan",
        "Combinatorics.egf_bell",
        "Combinatorics.ogf_partition",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_counting_basic_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.factorial",
        "Combinatorics.binomial",
        "Combinatorics.multinomial",
        "Combinatorics.permutation",
        "Combinatorics.derangement",
        "Combinatorics.subfactorial",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_identities_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.pascals_identity",
        "Combinatorics.vandermonde_identity",
        "Combinatorics.binomial_theorem",
        "Combinatorics.hockey_stick",
        "Combinatorics.lucas_theorem",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_special_numbers_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.StirlingFirst",
        "Combinatorics.StirlingSecond",
        "Combinatorics.BellNumber",
        "Combinatorics.CatalanNumber",
        "Combinatorics.MotzkinNumber",
        "Combinatorics.EulerNumber",
        "Combinatorics.BernoulliNumber",
        "Combinatorics.FibonacciNumber",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_partitions_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.IntegerPartition",
        "Combinatorics.PartitionNumber",
        "Combinatorics.PartitionFunction",
        "Combinatorics.DistinctPartition",
        "Combinatorics.FerrersDiagram",
        "Combinatorics.ConjugatePartition",
        "Combinatorics.partition_identity",
        "Combinatorics.pentagonal_theorem",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_compositions_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.Composition",
        "Combinatorics.CompositionNumber",
        "Combinatorics.WeakComposition",
        "Combinatorics.SetPartition",
        "Combinatorics.NonCrossingPartition",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_permutations_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.Permutation",
        "Combinatorics.CycleType",
        "Combinatorics.Inversion",
        "Combinatorics.InversionNumber",
        "Combinatorics.Descent",
        "Combinatorics.MajorIndex",
        "Combinatorics.SignOfPermutation",
        "Combinatorics.Transposition",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_inclusion_exclusion_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.InclusionExclusion",
        "Combinatorics.Sieve",
        "Combinatorics.Bonferroni",
        "Combinatorics.MobiusInversion",
        "Combinatorics.MobiusFunction",
        "Combinatorics.ZetaFunction",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_polya_enumeration_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.GroupAction",
        "Combinatorics.Orbit",
        "Combinatorics.Stabilizer",
        "Combinatorics.OrbitStabilizer",
        "Combinatorics.BurnsideLemma",
        "Combinatorics.CycleIndex",
        "Combinatorics.PolyaEnumeration",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_ramsey_theory_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.RamseyNumber",
        "Combinatorics.RamseyTheorem",
        "Combinatorics.InfiniteRamsey",
        "Combinatorics.SchurNumber",
        "Combinatorics.SchurTheorem",
        "Combinatorics.VanDerWaerden",
        "Combinatorics.HalesJewett",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_extremal_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.TuranNumber",
        "Combinatorics.TuranGraph",
        "Combinatorics.TuranTheorem",
        "Combinatorics.ErdosKoRado",
        "Combinatorics.SunflowerLemma",
        "Combinatorics.KruskalKatona",
        "Combinatorics.SzemerediRegularity",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_probabilistic_method_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.FirstMoment",
        "Combinatorics.SecondMoment",
        "Combinatorics.LovaszLocalLemma",
        "Combinatorics.Alteration",
        "Combinatorics.RandomGraphs",
        "Combinatorics.ThresholdFunction",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_design_theory_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.BlockDesign",
        "Combinatorics.BalancedDesign",
        "Combinatorics.SteinerSystem",
        "Combinatorics.SteinerTriple",
        "Combinatorics.LatinSquare",
        "Combinatorics.MOLS",
        "Combinatorics.HadamardMatrix",
        "Combinatorics.Fisher_inequality",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_lattice_theory_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.PartialOrder",
        "Combinatorics.Chain",
        "Combinatorics.Antichain",
        "Combinatorics.Width",
        "Combinatorics.Height",
        "Combinatorics.Lattice",
        "Combinatorics.BooleanLattice",
        "Combinatorics.YoungLattice",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_codes_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.HammingDistance",
        "Combinatorics.ErrorCorrectingCode",
        "Combinatorics.LinearCode",
        "Combinatorics.HammingBound",
        "Combinatorics.SingletonBound",
        "Combinatorics.PerfectCode",
        "Combinatorics.HammingCode",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_algebraic_combinatorics_exist() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();

    for name in &[
        "Combinatorics.SymmetricFunction",
        "Combinatorics.ElementarySymmetric",
        "Combinatorics.PowerSum",
        "Combinatorics.SchurFunction",
        "Combinatorics.JacobiTrudi",
        "Combinatorics.LittlewoodRichardson",
        "Combinatorics.YoungTableau",
        "Combinatorics.HookLengthFormula",
    ] {
        assert_const(&env, name);
    }
}

#[test]
fn test_combinatorics_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_combinatorics().unwrap();
    assert!(env.has_eq());
    assert!(env.has_nat());
    assert!(env.has_int());
    assert!(env.has_rat());
    assert!(env.has_list());
}

#[test]
fn test_combinatorics_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_combinatorics().unwrap();
    let after = env.constants.len();

    // Expect a rich collection of combinatorics constants plus dependencies
    let comb_count = after - before;
    assert!(
        comb_count >= 250,
        "Expected at least 250 new constants for combinatorics (including deps), got {comb_count}"
    );
}

#[test]
fn test_combinatorics_key_types_well_formed() {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_combinatorics().unwrap();
    let tc = TypeChecker::new(&env);

    for name in &[
        "Combinatorics.Graph",
        "Combinatorics.Matroid",
        "Combinatorics.factorial",
        "Combinatorics.binomial",
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
// Optimization Tests
// ============================================================================
