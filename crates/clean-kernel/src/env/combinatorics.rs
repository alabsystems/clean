// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Combinatorics structures for Environment
//!
//! This module contains combinatorics initialization:
//! - Graph theory (graphs, digraphs, connectivity, coloring)
//! - Matroids (independence systems, circuits, bases)
//! - Generating functions (ordinary, exponential)
//! - Enumerative combinatorics (counting, partitions)
//! - Polya enumeration and group actions
//! - Ramsey theory and extremal combinatorics

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Combinatorics module
    ///
    /// Combinatorics is the mathematics of counting, arranging, and
    /// analyzing discrete structures. It underpins:
    /// - Algorithm analysis (complexity, data structures)
    /// - Cryptography (permutations, combinations)
    /// - Probability (sample spaces, events)
    /// - Optimization (networks, scheduling)
    ///
    /// Key areas:
    /// - Graph theory: vertices, edges, paths, connectivity
    /// - Matroids: abstract independence systems
    /// - Generating functions: algebraic enumeration
    /// - Enumerative combinatorics: counting techniques
    ///
    /// This module provides axioms for:
    /// - Graph structures and properties
    /// - Matroid axioms and operations
    /// - Generating function algebra
    /// - Counting formulas and identities
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.combinatorics_init == true`
    /// ENSURES: On success, required dependencies (`eq`, `nat`, `int`, `rat`, `list`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_combinatorics(&mut self) -> Result<(), EnvError> {
        if self.combinatorics_init {
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

        // Combinatorics constants
        for name in &[
            // ================================================================
            // Basic Graph Theory
            // ================================================================
            "Combinatorics.Graph",       // simple undirected graph
            "Combinatorics.SimpleGraph", // no loops, no multi-edges
            "Combinatorics.Digraph",     // directed graph
            "Combinatorics.Multigraph",  // allows multiple edges
            "Combinatorics.Hypergraph",  // edges connect multiple vertices
            "Combinatorics.Vertex",      // vertex type
            "Combinatorics.Edge",        // edge type
            "Combinatorics.adj",         // adjacency relation
            "Combinatorics.incidence",   // incidence relation
            "Combinatorics.degree",      // degree of vertex
            "Combinatorics.in_degree",   // in-degree (digraphs)
            "Combinatorics.out_degree",  // out-degree (digraphs)
            // ================================================================
            // Paths and Cycles
            // ================================================================
            "Combinatorics.Walk",             // sequence of adjacent vertices
            "Combinatorics.Path",             // walk with no repeated vertices
            "Combinatorics.Cycle",            // closed path
            "Combinatorics.Trail",            // walk with no repeated edges
            "Combinatorics.Circuit",          // closed trail
            "Combinatorics.EulerianPath",     // trail visiting each edge once
            "Combinatorics.EulerianCircuit",  // closed Eulerian path
            "Combinatorics.HamiltonianPath",  // path visiting each vertex once
            "Combinatorics.HamiltonianCycle", // closed Hamiltonian path
            "Combinatorics.Girth",            // length of shortest cycle
            "Combinatorics.Diameter",         // max distance between vertices
            // ================================================================
            // Connectivity
            // ================================================================
            "Combinatorics.Connected",          // connected graph
            "Combinatorics.ConnectedComponent", // maximal connected subgraph
            "Combinatorics.StronglyConnected",  // strongly connected (digraphs)
            "Combinatorics.WeaklyConnected",    // weakly connected (digraphs)
            "Combinatorics.Biconnected",        // 2-vertex-connected
            "Combinatorics.kConnected",         // k-vertex-connected
            "Combinatorics.kEdgeConnected",     // k-edge-connected
            "Combinatorics.ArticulationPoint",  // cut vertex
            "Combinatorics.Bridge",             // cut edge
            "Combinatorics.Block",              // maximal biconnected subgraph
            "Combinatorics.connectivity",       // vertex connectivity κ(G)
            "Combinatorics.edge_connectivity",  // edge connectivity λ(G)
            // ================================================================
            // Special Graphs
            // ================================================================
            "Combinatorics.CompleteGraph",     // Kₙ
            "Combinatorics.CompleteBipartite", // Kₘ,ₙ
            "Combinatorics.Bipartite",         // bipartite graph
            "Combinatorics.Tree",              // connected acyclic
            "Combinatorics.Forest",            // acyclic
            "Combinatorics.Star",              // K₁,ₙ₋₁
            "Combinatorics.Wheel",             // Wₙ
            "Combinatorics.CycleGraph",        // Cₙ
            "Combinatorics.PathGraph",         // Pₙ
            "Combinatorics.PetersenGraph",     // Petersen graph
            "Combinatorics.PlanarGraph",       // embeddable in plane
            "Combinatorics.OuterplanarGraph",  // outer planar
            "Combinatorics.RegularGraph",      // all degrees equal
            "Combinatorics.CubicGraph",        // 3-regular
            // ================================================================
            // Graph Coloring
            // ================================================================
            "Combinatorics.Coloring",            // proper vertex coloring
            "Combinatorics.EdgeColoring",        // proper edge coloring
            "Combinatorics.ChromaticNumber",     // χ(G)
            "Combinatorics.ChromaticIndex",      // χ'(G)
            "Combinatorics.ChromaticPolynomial", // P(G, k)
            "Combinatorics.kColorable",          // admits k-coloring
            "Combinatorics.GreedyColoring",      // greedy algorithm
            "Combinatorics.BrooksTheorem",       // χ(G) ≤ Δ(G) + 1
            "Combinatorics.VizingTheorem",       // χ'(G) ∈ {Δ, Δ+1}
            "Combinatorics.FourColorTheorem",    // planar graphs are 4-colorable
            // ================================================================
            // Matchings and Covers
            // ================================================================
            "Combinatorics.Matching",            // set of disjoint edges
            "Combinatorics.MaximumMatching",     // largest matching
            "Combinatorics.PerfectMatching",     // covers all vertices
            "Combinatorics.VertexCover",         // covers all edges
            "Combinatorics.EdgeCover",           // covers all vertices
            "Combinatorics.IndependentSet",      // no two adjacent
            "Combinatorics.Clique",              // all pairs adjacent
            "Combinatorics.CliqueNumber",        // ω(G)
            "Combinatorics.IndependenceNumber",  // α(G)
            "Combinatorics.HallMarriageTheorem", // perfect matching condition
            "Combinatorics.KonigTheorem",        // bipartite matching/cover
            // ================================================================
            // Graph Operations
            // ================================================================
            "Combinatorics.Subgraph",         // subgraph relation
            "Combinatorics.InducedSubgraph",  // induced by vertex set
            "Combinatorics.SpanningSubgraph", // same vertex set
            "Combinatorics.GraphUnion",       // disjoint union
            "Combinatorics.GraphJoin",        // complete join
            "Combinatorics.CartesianProduct", // G □ H
            "Combinatorics.TensorProduct",    // G × H
            "Combinatorics.LineGraph",        // L(G)
            "Combinatorics.Complement",       // Ḡ
            "Combinatorics.GraphMinor",       // minor relation
            "Combinatorics.Subdivision",      // subdivision
            "Combinatorics.GraphContraction", // edge contraction
            // ================================================================
            // Graph Invariants and Theorems
            // ================================================================
            "Combinatorics.HandshakingLemma",    // Σdeg(v) = 2|E|
            "Combinatorics.EulerFormula",        // V - E + F = 2 (planar)
            "Combinatorics.TurnsFormula",        // |E| ≤ 3|V| - 6 (planar)
            "Combinatorics.KuratowskiTheorem",   // K₅, K₃,₃ subdivision
            "Combinatorics.WagnerTheorem",       // K₅, K₃,₃ minor
            "Combinatorics.MengerTheorem",       // connectivity paths
            "Combinatorics.DilworthTheorem",     // chain/antichain duality
            "Combinatorics.MirzakhaniRecursion", // recursion for counting
            // ================================================================
            // Trees and Spanning Trees
            // ================================================================
            "Combinatorics.SpanningTree",        // spanning tree
            "Combinatorics.MinimumSpanningTree", // MST
            "Combinatorics.CayleyFormula",       // n^(n-2) labeled trees on n vertices
            "Combinatorics.PruferCode",          // bijection trees ↔ sequences
            "Combinatorics.MatrixTreeTheorem",   // spanning tree count
            "Combinatorics.RootedTree",          // tree with distinguished root
            "Combinatorics.BinaryTree",          // at most 2 children
            "Combinatorics.CatalanTree",         // full binary tree
            // ================================================================
            // Network Flows
            // ================================================================
            "Combinatorics.Network",        // flow network
            "Combinatorics.Flow",           // flow function
            "Combinatorics.MaxFlow",        // maximum flow
            "Combinatorics.MinCut",         // minimum cut
            "Combinatorics.MaxFlowMinCut",  // max-flow min-cut theorem
            "Combinatorics.FordFulkerson",  // augmenting path algorithm
            "Combinatorics.ResidualGraph",  // residual network
            "Combinatorics.AugmentingPath", // path in residual graph
            // ================================================================
            // Matroids - Basic
            // ================================================================
            "Combinatorics.Matroid",          // matroid axioms
            "Combinatorics.IndependentSet_M", // independent set in matroid
            "Combinatorics.Basis_M",          // maximal independent set
            "Combinatorics.Circuit_M",        // minimal dependent set
            "Combinatorics.Rank",             // rank function
            "Combinatorics.Closure",          // closure operator
            "Combinatorics.Flat",             // closed set
            "Combinatorics.Hyperplane",       // rank n-1 flat
            "Combinatorics.Coloop",           // element in every basis
            "Combinatorics.Loop_M",           // element in no basis
            // ================================================================
            // Matroid Examples
            // ================================================================
            "Combinatorics.UniformMatroid",     // U_{r,n}
            "Combinatorics.VectorMatroid",      // linear matroid
            "Combinatorics.GraphicMatroid",     // cycle matroid of graph
            "Combinatorics.CographicMatroid",   // dual of graphic
            "Combinatorics.TransversalMatroid", // from bipartite graph
            "Combinatorics.PartitionMatroid",   // union of uniform
            "Combinatorics.FreeMatroid",        // all sets independent
            "Combinatorics.FanoMatroid",        // F₇
            // ================================================================
            // Matroid Operations
            // ================================================================
            "Combinatorics.MatroidDual",         // dual matroid M*
            "Combinatorics.MatroidMinor",        // deletion and contraction
            "Combinatorics.Deletion",            // M \ e
            "Combinatorics.Contraction",         // M / e
            "Combinatorics.MatroidUnion",        // union of matroids
            "Combinatorics.MatroidIntersection", // intersection
            "Combinatorics.Truncation",          // reduce rank
            // ================================================================
            // Matroid Theorems
            // ================================================================
            "Combinatorics.matroid_rank_axioms", // rank function properties
            "Combinatorics.basis_exchange",      // basis exchange property
            "Combinatorics.matroid_duality",     // (M*)* = M
            "Combinatorics.RadoEdmondsTheorem",  // matroid intersection algorithm
            "Combinatorics.MatroidPartitionTheorem", // partition into bases
            "Combinatorics.WelshDuality",        // chromatic/flow polynomials
            // ================================================================
            // Generating Functions - Ordinary
            // ================================================================
            "Combinatorics.OGF",             // ordinary generating function
            "Combinatorics.ogf_add",         // (A + B)(x) = A(x) + B(x)
            "Combinatorics.ogf_mul",         // convolution: Σaᵢbₙ₋ᵢ
            "Combinatorics.ogf_shift",       // xA(x), A(x)/x
            "Combinatorics.ogf_derivative",  // d/dx A(x)
            "Combinatorics.ogf_composition", // A(B(x))
            "Combinatorics.ogf_hadamard",    // Hadamard product
            "Combinatorics.ogf_extract",     // [xⁿ]A(x) = aₙ
            // ================================================================
            // Generating Functions - Exponential
            // ================================================================
            "Combinatorics.EGF",             // exponential generating function
            "Combinatorics.egf_add",         // addition
            "Combinatorics.egf_mul",         // binomial convolution
            "Combinatorics.egf_composition", // compositional formula
            "Combinatorics.egf_derivative",  // differentiation shifts
            "Combinatorics.egf_integral",    // integration
            // ================================================================
            // Generating Functions - Special
            // ================================================================
            "Combinatorics.DirichletSeries", // Σaₙn⁻ˢ
            "Combinatorics.LambertSeries",   // Σaₙxⁿ/(1-xⁿ)
            "Combinatorics.PolyaSeries",     // cycle index series
            "Combinatorics.BellSeries",      // Σaₙxⁿ/n!
            // ================================================================
            // Generating Functions - Standard Examples
            // ================================================================
            "Combinatorics.ogf_geometric", // 1/(1-x) = Σxⁿ
            "Combinatorics.ogf_binomial",  // (1+x)ⁿ = Σ(n choose k)xᵏ
            "Combinatorics.egf_exp",       // eˣ = Σxⁿ/n!
            "Combinatorics.ogf_fibonacci", // x/(1-x-x²)
            "Combinatorics.ogf_catalan",   // (1-√(1-4x))/(2x)
            "Combinatorics.egf_bell",      // e^(eˣ-1)
            "Combinatorics.ogf_partition", // Π 1/(1-xᵏ)
            // ================================================================
            // Counting - Basic
            // ================================================================
            "Combinatorics.factorial",    // n!
            "Combinatorics.binomial",     // (n choose k)
            "Combinatorics.multinomial",  // n!/(k₁!...kₘ!)
            "Combinatorics.permutation",  // P(n,k) = n!/(n-k)!
            "Combinatorics.derangement",  // D_n (no fixed points)
            "Combinatorics.subfactorial", // !n = D_n
            // ================================================================
            // Counting - Identities
            // ================================================================
            "Combinatorics.pascals_identity", // (n,k) = (n-1,k-1) + (n-1,k)
            "Combinatorics.vandermonde_identity", // Σ(m,i)(n,k-i) = (m+n,k)
            "Combinatorics.binomial_theorem", // (x+y)ⁿ = Σ(n,k)xᵏyⁿ⁻ᵏ
            "Combinatorics.hockey_stick",     // Σ(r,i) = (r+1,k+1)
            "Combinatorics.lucas_theorem",    // (m,n) mod p
            "Combinatorics.kummer_theorem",   // p-adic val of binomial
            // ================================================================
            // Counting - Special Numbers
            // ================================================================
            "Combinatorics.StirlingFirst",   // s(n,k) unsigned
            "Combinatorics.StirlingSecond",  // S(n,k)
            "Combinatorics.BellNumber",      // Bₙ = Σ S(n,k)
            "Combinatorics.CatalanNumber",   // Cₙ = (1/(n+1))(2n,n)
            "Combinatorics.MotzkinNumber",   // Mₙ
            "Combinatorics.EulerNumber",     // zigzag permutations
            "Combinatorics.BernoulliNumber", // Bₙ
            "Combinatorics.HarmonicNumber",  // Hₙ = Σ 1/k
            "Combinatorics.FibonacciNumber", // Fₙ
            "Combinatorics.LucasNumber",     // Lₙ
            // ================================================================
            // Partitions
            // ================================================================
            "Combinatorics.IntegerPartition",   // partition of n
            "Combinatorics.PartitionNumber",    // p(n)
            "Combinatorics.PartitionFunction",  // p(n,k) into k parts
            "Combinatorics.DistinctPartition",  // distinct parts
            "Combinatorics.OddPartition",       // odd parts only
            "Combinatorics.FerrersDiagram",     // Young diagram
            "Combinatorics.ConjugatePartition", // transpose diagram
            "Combinatorics.partition_identity", // distinct = odd parts
            "Combinatorics.pentagonal_theorem", // Euler's pentagonal
            // ================================================================
            // Compositions and Set Partitions
            // ================================================================
            "Combinatorics.Composition",          // ordered partition
            "Combinatorics.CompositionNumber",    // 2^(n-1)
            "Combinatorics.WeakComposition",      // allows zeros
            "Combinatorics.SetPartition",         // partition of set
            "Combinatorics.SetPartitionNumber",   // Bₙ (Bell number)
            "Combinatorics.CrossingPartition",    // crossing partitions
            "Combinatorics.NonCrossingPartition", // NC(n)
            // ================================================================
            // Permutations
            // ================================================================
            "Combinatorics.Permutation",       // bijection [n] → [n]
            "Combinatorics.CycleType",         // cycle structure
            "Combinatorics.Inversion",         // i < j, π(i) > π(j)
            "Combinatorics.InversionNumber",   // inv(π)
            "Combinatorics.Descent",           // π(i) > π(i+1)
            "Combinatorics.DescentSet",        // {i : π(i) > π(i+1)}
            "Combinatorics.MajorIndex",        // Σ descents
            "Combinatorics.Excedance",         // π(i) > i
            "Combinatorics.FixedPoint",        // π(i) = i
            "Combinatorics.PermutationCycle",  // cycle in permutation
            "Combinatorics.Transposition",     // 2-cycle
            "Combinatorics.SignOfPermutation", // sgn(π) = (-1)^inv(π)
            // ================================================================
            // Inclusion-Exclusion
            // ================================================================
            "Combinatorics.InclusionExclusion", // |A₁ ∪ ... ∪ Aₙ|
            "Combinatorics.Sieve",              // sieve formula
            "Combinatorics.Bonferroni",         // Bonferroni inequalities
            "Combinatorics.MobiusInversion",    // μ * f = g ↔ f = g * ζ
            "Combinatorics.MobiusFunction",     // μ on poset
            "Combinatorics.ZetaFunction",       // ζ on poset
            // ================================================================
            // Polya Enumeration
            // ================================================================
            "Combinatorics.GroupAction",      // G acts on X
            "Combinatorics.Orbit",            // orbit of element
            "Combinatorics.Stabilizer",       // stabilizer subgroup
            "Combinatorics.OrbitStabilizer",  // |G| = |Orb||Stab|
            "Combinatorics.BurnsideLemma",    // |X/G| = Σ|Xᵍ|/|G|
            "Combinatorics.CycleIndex",       // Z(G; x₁,...,xₙ)
            "Combinatorics.PolyaEnumeration", // counting up to symmetry
            "Combinatorics.PatternInventory", // weighted counting
            // ================================================================
            // Ramsey Theory
            // ================================================================
            "Combinatorics.RamseyNumber",         // R(r,s)
            "Combinatorics.RamseyTheorem",        // finite Ramsey theorem
            "Combinatorics.InfiniteRamsey",       // infinite version
            "Combinatorics.SchurNumber",          // S(k)
            "Combinatorics.SchurTheorem",         // monochromatic x+y=z
            "Combinatorics.VanDerWaerden",        // W(k,r)
            "Combinatorics.VanDerWaerdenTheorem", // monochromatic AP
            "Combinatorics.HalesJewett",          // Hales-Jewett theorem
            // ================================================================
            // Extremal Combinatorics
            // ================================================================
            "Combinatorics.TuranNumber",         // ex(n,H)
            "Combinatorics.TuranGraph",          // T(n,r)
            "Combinatorics.TuranTheorem",        // ex(n,Kᵣ₊₁) = |T(n,r)|
            "Combinatorics.ErdosKoRado",         // intersecting families
            "Combinatorics.SunflowerLemma",      // Erdős-Rado sunflower
            "Combinatorics.KruskalKatona",       // shadow sizes
            "Combinatorics.SzemerediRegularity", // regularity lemma
            "Combinatorics.BlowupLemma",         // embedding lemma
            // ================================================================
            // Probabilistic Method
            // ================================================================
            "Combinatorics.FirstMoment",       // E[X] > 0 → P[X>0] > 0
            "Combinatorics.SecondMoment",      // P[X>0] ≥ E[X]²/E[X²]
            "Combinatorics.LovaszLocalLemma",  // avoiding dependencies
            "Combinatorics.LLLSymmetric",      // symmetric LLL
            "Combinatorics.Alteration",        // alteration method
            "Combinatorics.RandomGraphs",      // G(n,p) model
            "Combinatorics.ThresholdFunction", // phase transitions
            // ================================================================
            // Design Theory
            // ================================================================
            "Combinatorics.BlockDesign",           // (v,b,r,k,λ)-design
            "Combinatorics.BalancedDesign",        // BIBD
            "Combinatorics.SteinerSystem",         // S(t,k,v)
            "Combinatorics.SteinerTriple",         // S(2,3,v)
            "Combinatorics.LatinSquare",           // n×n with each symbol once
            "Combinatorics.MOLS",                  // mutually orthogonal
            "Combinatorics.OrthogonalLatinSquare", // pair of orthogonal
            "Combinatorics.HadamardMatrix",        // orthogonal ±1 matrix
            "Combinatorics.IncidenceMatrix",       // design incidence
            "Combinatorics.Fisher_inequality",     // b ≥ v
            // ================================================================
            // Lattice Theory / Partial Orders
            // ================================================================
            "Combinatorics.PartialOrder",        // poset
            "Combinatorics.Chain",               // totally ordered subset
            "Combinatorics.Antichain",           // no two comparable
            "Combinatorics.Width",               // max antichain size
            "Combinatorics.Height",              // max chain length
            "Combinatorics.Lattice",             // meet and join exist
            "Combinatorics.DistributiveLattice", // distributive
            "Combinatorics.ModularLattice",      // modular
            "Combinatorics.BooleanLattice",      // power set lattice
            "Combinatorics.YoungLattice",        // partitions ordered by inclusion
            "Combinatorics.TamariLattice",       // binary trees
            // ================================================================
            // Codes and Information
            // ================================================================
            "Combinatorics.HammingDistance", // # differing positions
            "Combinatorics.ErrorCorrectingCode", // [n,k,d]-code
            "Combinatorics.LinearCode",      // subspace code
            "Combinatorics.HammingBound",    // sphere-packing bound
            "Combinatorics.SingletonBound",  // d ≤ n - k + 1
            "Combinatorics.PerfectCode",     // achieves Hamming bound
            "Combinatorics.HammingCode",     // [2^r-1, 2^r-r-1, 3]
            "Combinatorics.ReedSolomonCode", // polynomial evaluation
            // ================================================================
            // Algebraic Combinatorics
            // ================================================================
            "Combinatorics.SymmetricFunction", // symmetric in x₁,...,xₙ
            "Combinatorics.ElementarySymmetric", // eₖ
            "Combinatorics.PowerSum",          // pₖ = Σxᵢᵏ
            "Combinatorics.CompleteHomogeneous", // hₖ
            "Combinatorics.SchurFunction",     // sλ
            "Combinatorics.JacobiTrudi",       // Schur = det of h's
            "Combinatorics.LittlewoodRichardson", // sλsμ = Σcλμνsν
            "Combinatorics.RobinsonSchensted", // bijection π ↔ (P,Q)
            "Combinatorics.YoungTableau",      // standard/semistandard
            "Combinatorics.HookLengthFormula", // |SYT(λ)| = n!/Πhooks
        ] {
            let decl = Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            };
            self.add_decl(decl)?;
        }

        self.combinatorics_init = true;
        Ok(())
    }

    /// Check if Combinatorics has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_combinatorics` has completed successfully
    /// ENSURES: Pure - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_combinatorics(&self) -> bool {
        self.combinatorics_init
    }
}
