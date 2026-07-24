// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Graph Theory module for Environment
//!
//! This module formalizes graph theory, providing foundations for reasoning
//! about networks, algorithms, and combinatorial structures:
//! - Basic graphs (directed, undirected, weighted, multigraphs)
//! - Graph properties (connectivity, planarity, coloring)
//! - Graph algorithms (shortest paths, spanning trees, flow)
//! - Special graph classes (trees, DAGs, bipartite, complete)
//! - Graph decompositions and representations
//! - Spectral graph theory
//! - Random graphs and probabilistic methods
//!
//! These foundations enable formal verification of:
//! - Network protocols and routing algorithms
//! - Compiler optimizations (control flow graphs)
//! - Social network analysis
//! - Constraint satisfaction and scheduling
//! - Circuit layout and VLSI design
//!
//! Applications in AI/ML and verification:
//! - Graph neural networks and message passing
//! - Knowledge graph reasoning
//! - Program analysis via control/data flow graphs
//! - Dependency analysis and topological sorting
//! - Network flow optimization

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Graph Theory module
    ///
    /// This module adds axioms for formally reasoning about graphs,
    /// their properties, and fundamental algorithms - foundations for
    /// network analysis, algorithm verification, and combinatorial optimization.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.graph_theory_init == true`
    /// ENSURES: On success, required dependencies (`eq`, `nat`, `bool`, `list`, `set_theory`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_graph_theory(&mut self) -> Result<(), EnvError> {
        if self.graph_theory_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_list()?;
        self.init_set_theory()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Graph theory constants
        for name in &[
            // ================================================================
            // Basic Graph Structures
            // ================================================================
            "Graph.Vertex",          // V - vertex type
            "Graph.Edge",            // E - edge type
            "Graph.Graph",           // G = (V, E) - undirected graph
            "Graph.Digraph",         // D = (V, E) - directed graph
            "Graph.WeightedGraph",   // G = (V, E, w) - weighted graph
            "Graph.WeightedDigraph", // D = (V, E, w) - weighted directed graph
            "Graph.Multigraph",      // Multiple edges between vertices
            "Graph.Hypergraph",      // Edges connect arbitrary subsets
            "Graph.SimpleGraph",     // No loops, no multi-edges
            "Graph.Vertices",        // V(G) - vertex set
            "Graph.Edges",           // E(G) - edge set
            "Graph.Order",           // |V(G)| - number of vertices
            "Graph.Size",            // |E(G)| - number of edges
            "Graph.AdjacencyMatrix", // n×n matrix representation
            "Graph.AdjacencyList",   // List-based representation
            "Graph.IncidenceMatrix", // Vertex-edge incidence
            "Graph.LaplacianMatrix", // L = D - A (degree minus adjacency)
            // ================================================================
            // Vertex and Edge Properties
            // ================================================================
            "Graph.Adjacent",           // u ~ v (u and v are adjacent)
            "Graph.Incident",           // v incident to e
            "Graph.Endpoint",           // v is endpoint of e
            "Graph.SelfLoop",           // Edge from v to v
            "Graph.ParallelEdges",      // Multiple edges between same vertices
            "Graph.Neighbor",           // Neighbor of vertex
            "Graph.Neighborhood",       // N(v) - set of neighbors
            "Graph.ClosedNeighborhood", // N[v] = N(v) ∪ {v}
            "Graph.CommonNeighbors",    // N(u) ∩ N(v)
            "Graph.Degree",             // deg(v) - degree of vertex
            "Graph.InDegree",           // in-degree (digraphs)
            "Graph.OutDegree",          // out-degree (digraphs)
            "Graph.MinDegree",          // δ(G) - minimum degree
            "Graph.MaxDegree",          // Δ(G) - maximum degree
            "Graph.AvgDegree",          // Average degree
            "Graph.DegreeSequence",     // Sorted list of degrees
            "Graph.Regular",            // All vertices same degree
            "Graph.KRegular",           // k-regular graph
            "Graph.IsolatedVertex",     // deg(v) = 0
            "Graph.PendantVertex",      // deg(v) = 1 (leaf)
            "Graph.UniversalVertex",    // Adjacent to all others
            // ================================================================
            // Subgraphs and Graph Operations
            // ================================================================
            "Graph.Subgraph",             // H ⊆ G
            "Graph.InducedSubgraph",      // G[S] - subgraph induced by vertex set
            "Graph.SpanningSubgraph",     // Same vertices, subset of edges
            "Graph.EdgeSubgraph",         // Subgraph induced by edge set
            "Graph.GraphUnion",           // G ∪ H
            "Graph.GraphIntersection",    // G ∩ H
            "Graph.GraphDifference",      // G - H
            "Graph.GraphComplement",      // Ḡ - complement graph
            "Graph.LineGraph",            // L(G) - edge becomes vertex
            "Graph.GraphPower",           // G^k - vertices at distance ≤ k
            "Graph.GraphSquare",          // G² = G²
            "Graph.GraphProduct",         // Various graph products
            "Graph.CartesianProduct",     // G □ H
            "Graph.TensorProduct",        // G × H
            "Graph.StrongProduct",        // G ⊠ H
            "Graph.LexicographicProduct", // G ∘ H
            "Graph.Subdivision",          // Subdivide edges
            "Graph.EdgeContraction",      // Contract edge
            "Graph.VertexDeletion",       // G - v
            "Graph.EdgeDeletion",         // G - e
            "Graph.VertexIdentification", // Merge vertices
            // ================================================================
            // Paths and Walks
            // ================================================================
            "Graph.Walk",             // Sequence of adjacent vertices
            "Graph.Trail",            // Walk with distinct edges
            "Graph.Path",             // Walk with distinct vertices
            "Graph.Cycle",            // Path returning to start
            "Graph.Circuit",          // Trail returning to start
            "Graph.PathLength",       // Number of edges in path
            "Graph.ShortestPath",     // Path with minimum length
            "Graph.Distance",         // d(u,v) - shortest path length
            "Graph.Diameter",         // max distance between vertices
            "Graph.Radius",           // min eccentricity
            "Graph.Eccentricity",     // max distance from vertex
            "Graph.Center",           // Vertices with min eccentricity
            "Graph.Periphery",        // Vertices with max eccentricity
            "Graph.Girth",            // Length of shortest cycle
            "Graph.Circumference",    // Length of longest cycle
            "Graph.HamiltonianPath",  // Path visiting all vertices
            "Graph.HamiltonianCycle", // Cycle visiting all vertices
            "Graph.EulerianPath",     // Path using all edges exactly once
            "Graph.EulerianCycle",    // Cycle using all edges exactly once
            "Graph.Geodesic",         // Shortest path between vertices
            "Graph.AllPairsDistance", // Distance matrix
            // ================================================================
            // Connectivity
            // ================================================================
            "Graph.Connected",           // Path between any two vertices
            "Graph.Disconnected",        // Not connected
            "Graph.StronglyConnected",   // Digraph: path both directions
            "Graph.WeaklyConnected",     // Underlying undirected is connected
            "Graph.Component",           // Maximal connected subgraph
            "Graph.ConnectedComponents", // Set of components
            "Graph.NumComponents",       // Number of components
            "Graph.StrongComponent",     // Strongly connected component
            "Graph.Bridge",              // Edge whose removal disconnects
            "Graph.CutVertex",           // Vertex whose removal disconnects
            "Graph.ArticulationPoint",   // Same as cut vertex
            "Graph.KConnected",          // k-vertex-connected
            "Graph.KEdgeConnected",      // k-edge-connected
            "Graph.VertexConnectivity",  // κ(G) - min vertex cut size
            "Graph.EdgeConnectivity",    // λ(G) - min edge cut size
            "Graph.MinCut",              // Minimum cut
            "Graph.MaxCut",              // Maximum cut
            "Graph.VertexCut",           // Set of vertices whose removal disconnects
            "Graph.EdgeCut",             // Set of edges whose removal disconnects
            "Graph.Menger",              // Menger's theorem
            "Graph.Block",               // Maximal 2-connected subgraph
            "Graph.BlockCutTree",        // Block-cut tree decomposition
            // ================================================================
            // Trees and Forests
            // ================================================================
            "Graph.Tree",            // Connected acyclic graph
            "Graph.Forest",          // Acyclic graph (union of trees)
            "Graph.RootedTree",      // Tree with designated root
            "Graph.BinaryTree",      // Each vertex has ≤ 2 children
            "Graph.SpanningTree",    // Tree spanning all vertices
            "Graph.SpanningForest",  // Forest spanning all vertices
            "Graph.MinSpanningTree", // Minimum weight spanning tree
            "Graph.MaxSpanningTree", // Maximum weight spanning tree
            "Graph.Leaf",            // Degree-1 vertex in tree
            "Graph.InternalVertex",  // Non-leaf vertex
            "Graph.Root",            // Root of rooted tree
            "Graph.Parent",          // Parent in rooted tree
            "Graph.Child",           // Child in rooted tree
            "Graph.Ancestor",        // Ancestor in rooted tree
            "Graph.Descendant",      // Descendant in rooted tree
            "Graph.Sibling",         // Same parent
            "Graph.Subtree",         // Subtree rooted at vertex
            "Graph.TreeHeight",      // Max depth of tree
            "Graph.TreeDepth",       // Depth of vertex
            "Graph.TreeLevel",       // Vertices at same depth
            "Graph.PruferSequence",  // Encoding of labeled tree
            "Graph.CayleyFormula",   // n^(n-2) labeled trees on n vertices
            // ================================================================
            // Directed Acyclic Graphs (DAGs)
            // ================================================================
            "Graph.DAG",                 // Directed acyclic graph
            "Graph.TopologicalSort",     // Linear ordering respecting edges
            "Graph.TopologicalOrder",    // Result of topological sort
            "Graph.Source",              // Vertex with in-degree 0
            "Graph.Sink",                // Vertex with out-degree 0
            "Graph.LongestPath",         // Longest path in DAG
            "Graph.CriticalPath",        // Critical path method
            "Graph.Reachable",           // v reachable from u
            "Graph.TransitiveClosure",   // All reachable pairs
            "Graph.TransitiveReduction", // Minimum edges for same reachability
            "Graph.DAGLayering",         // Partition into layers
            // ================================================================
            // Bipartite Graphs
            // ================================================================
            "Graph.Bipartite",          // V = X ∪ Y, edges only between X and Y
            "Graph.BipartitePartition", // The two parts (X, Y)
            "Graph.CompleteBipartite",  // K_{m,n} - all edges between parts
            "Graph.Matching",           // Set of non-adjacent edges
            "Graph.PerfectMatching",    // Matching covering all vertices
            "Graph.MaximumMatching",    // Matching with max edges
            "Graph.MatchingNumber",     // Size of maximum matching
            "Graph.HallCondition",      // Hall's marriage theorem condition
            "Graph.KonigTheorem",       // Matching = vertex cover in bipartite
            "Graph.VertexCover",        // Set covering all edges
            "Graph.MinVertexCover",     // Minimum vertex cover
            "Graph.EdgeCover",          // Set covering all vertices
            "Graph.MinEdgeCover",       // Minimum edge cover
            "Graph.IndependentSet",     // Set of non-adjacent vertices
            "Graph.MaxIndependentSet",  // Maximum independent set
            "Graph.IndependenceNumber", // α(G) - size of max independent set
            "Graph.Clique",             // Complete subgraph
            "Graph.MaxClique",          // Maximum clique
            "Graph.CliqueNumber",       // ω(G) - size of max clique
            "Graph.CliqueCover",        // Partition into cliques
            "Graph.CliqueCoverNumber",  // θ(G) - min cliques to cover
            // ================================================================
            // Graph Coloring
            // ================================================================
            "Graph.VertexColoring",      // Assignment of colors to vertices
            "Graph.ProperColoring",      // Adjacent vertices different colors
            "Graph.ChromaticNumber",     // χ(G) - min colors needed
            "Graph.KColorable",          // Can be colored with k colors
            "Graph.Chromatic",           // Proper vertex coloring
            "Graph.EdgeColoring",        // Assignment of colors to edges
            "Graph.EdgeChromaticNumber", // χ'(G) - edge chromatic number
            "Graph.VizingTheorem",       // Δ ≤ χ' ≤ Δ + 1
            "Graph.ListColoring",        // Color from lists
            "Graph.ChoiceNumber",        // List chromatic number
            "Graph.FractionalChromatic", // Fractional chromatic number
            "Graph.AcyclicColoring",     // No 2-colored cycle
            "Graph.StarColoring",        // No 4-vertex path 2-colored
            "Graph.TotalColoring",       // Color vertices and edges
            "Graph.ChromaticPolynomial", // P(G, k) - colorings with k colors
            "Graph.Greedy",              // Greedy coloring algorithm
            "Graph.BrooksTheorem",       // χ ≤ Δ (except complete/odd cycle)
            // ================================================================
            // Planar Graphs
            // ================================================================
            "Graph.Planar",            // Embeddable in plane
            "Graph.PlaneGraph",        // Graph with fixed embedding
            "Graph.Face",              // Region bounded by edges
            "Graph.OuterFace",         // Unbounded face
            "Graph.EulerFormula",      // V - E + F = 2
            "Graph.Dual",              // Dual graph
            "Graph.K5Free",            // No K₅ minor
            "Graph.K33Free",           // No K_{3,3} minor
            "Graph.KuratowskiTheorem", // Planar ⟺ K₅-free and K_{3,3}-free
            "Graph.WagnerTheorem",     // Minor-closed characterization
            "Graph.FourColorTheorem",  // χ(planar) ≤ 4
            "Graph.Outerplanar",       // All vertices on outer face
            "Graph.SeriesParallel",    // No K₄ minor
            "Graph.Genus",             // Min genus of embedding surface
            "Graph.ToroidalGraph",     // Embeddable on torus
            "Graph.CrossingNumber",    // Min edge crossings
            "Graph.Thickness",         // Min planar subgraphs to decompose
            // ================================================================
            // Network Flow
            // ================================================================
            "Graph.FlowNetwork",        // (G, c, s, t) - capacity, source, sink
            "Graph.Capacity",           // c(e) - edge capacity
            "Graph.Flow",               // f(e) - flow on edge
            "Graph.ValidFlow",          // 0 ≤ f ≤ c, conservation
            "Graph.FlowValue",          // |f| - total flow
            "Graph.MaxFlow",            // Maximum flow
            "Graph.MinCutFlow",         // Minimum cut capacity
            "Graph.MaxFlowMinCut",      // Max flow = min cut
            "Graph.FordFulkerson",      // Augmenting path method
            "Graph.EdmondsKarp",        // BFS-based Ford-Fulkerson
            "Graph.Dinic",              // Blocking flow algorithm
            "Graph.PushRelabel",        // Push-relabel algorithm
            "Graph.ResidualGraph",      // Residual capacities
            "Graph.AugmentingPath",     // Path with positive residual
            "Graph.BottleneckCapacity", // Min capacity on path
            "Graph.MinCostFlow",        // Minimum cost max flow
            "Graph.Circulation",        // Flow with demands
            "Graph.MultiCommodityFlow", // Multiple source-sink pairs
            // ================================================================
            // Shortest Path Algorithms
            // ================================================================
            "Graph.BFS",                 // Breadth-first search
            "Graph.DFS",                 // Depth-first search
            "Graph.Dijkstra",            // Single-source shortest paths (non-negative)
            "Graph.BellmanFord",         // Single-source (allows negative)
            "Graph.FloydWarshall",       // All-pairs shortest paths
            "Graph.Johnson",             // All-pairs with reweighting
            "Graph.AStar",               // Heuristic shortest path
            "Graph.BidirectionalSearch", // Search from both ends
            "Graph.NegativeCycle",       // Cycle with negative total weight
            "Graph.ShortestPathTree",    // Tree of shortest paths
            // ================================================================
            // Spanning Tree Algorithms
            // ================================================================
            "Graph.Kruskal",                     // Greedy MST (edges)
            "Graph.Prim",                        // Greedy MST (vertices)
            "Graph.Boruvka",                     // Parallel MST
            "Graph.SteinerTree",                 // Minimum tree connecting terminals
            "Graph.MinimumSpanningArborescence", // Directed MST (Edmonds)
            // ================================================================
            // Special Graph Classes
            // ================================================================
            "Graph.CompleteGraph",       // K_n - all edges present
            "Graph.CycleGraph",          // C_n - single cycle
            "Graph.PathGraph",           // P_n - single path
            "Graph.StarGraph",           // K_{1,n-1}
            "Graph.WheelGraph",          // W_n - cycle with hub
            "Graph.GridGraph",           // m × n grid
            "Graph.HypercubeGraph",      // Q_n - n-dimensional hypercube
            "Graph.PetersenGraph",       // Famous 3-regular graph
            "Graph.PlatonicGraph",       // Graphs of Platonic solids
            "Graph.Interval",            // Intersection graph of intervals
            "Graph.Chordal",             // No induced cycle > 3
            "Graph.PerfectGraph",        // χ(H) = ω(H) for all induced H
            "Graph.CographGraph",        // P₄-free graph
            "Graph.SplitGraph",          // Clique + independent set
            "Graph.ThresholdGraph",      // Special split graphs
            "Graph.PermutationGraph",    // Intersection of line segments
            "Graph.CircleGraph",         // Chord intersection graph
            "Graph.ArcGraph",            // Arc intersection graph
            "Graph.CompGraph",           // Comparability graph
            "Graph.CayleyGraph",         // Graph from group
            "Graph.KneserGraph",         // K(n,k) - subset disjointness
            "Graph.PetersonGeneralized", // GP(n,k)
            "Graph.RegularGraph",        // All vertices same degree
            "Graph.StronglyRegular",     // srg(n,k,λ,μ)
            "Graph.DistanceRegular",     // Intersection array
            "Graph.VertexTransitive",    // Automorphism acts transitively
            "Graph.EdgeTransitive",      // Edge-transitive
            "Graph.ArcTransitive",       // Arc-transitive
            // ================================================================
            // Graph Decomposition
            // ================================================================
            "Graph.TreeDecomposition",    // Decomposition into tree of bags
            "Graph.Treewidth",            // tw(G) - min width of tree decomposition
            "Graph.PathDecomposition",    // Linear tree decomposition
            "Graph.Pathwidth",            // pw(G) - min width of path decomposition
            "Graph.BranchDecomposition",  // Edge-based decomposition
            "Graph.Branchwidth",          // bw(G)
            "Graph.CliqueDecomposition",  // Decomposition via cliques
            "Graph.ModularDecomposition", // Decomposition via modules
            "Graph.Module",               // Set with uniform external adjacency
            "Graph.PrimeGraph",           // Only trivial modules
            "Graph.EarDecomposition",     // Decomposition into paths
            "Graph.StrongEarDecomposition", // For 2-connected graphs
            // ================================================================
            // Graph Automorphisms
            // ================================================================
            "Graph.Automorphism",        // Bijection preserving adjacency
            "Graph.AutomorphismGroup",   // Aut(G)
            "Graph.GraphIsomorphism",    // G ≅ H
            "Graph.Isomorphic",          // Two graphs are isomorphic
            "Graph.CanonicalForm",       // Canonical representative
            "Graph.Invariant",           // Property preserved by isomorphism
            "Graph.CertificatePositive", // Isomorphism certificate
            "Graph.CertificateNegative", // Non-isomorphism certificate
            // ================================================================
            // Spectral Graph Theory
            // ================================================================
            "Graph.AdjacencySpectrum",   // Eigenvalues of adjacency matrix
            "Graph.LaplacianSpectrum",   // Eigenvalues of Laplacian
            "Graph.NormalizedLaplacian", // Normalized Laplacian matrix
            "Graph.SpectralGap",         // λ₂ - second smallest eigenvalue
            "Graph.AlgebraicConnectivity", // Fiedler value λ₂(L)
            "Graph.SpectralRadius",      // Largest eigenvalue
            "Graph.Expander",            // High expansion (spectral gap)
            "Graph.RamanujanGraph",      // Optimal spectral gap
            "Graph.CheegerInequality",   // Connects spectral gap to expansion
            "Graph.FiedlerVector",       // Eigenvector for λ₂
            "Graph.SpectralClustering",  // Clustering via eigenvectors
            // ================================================================
            // Random Graphs
            // ================================================================
            "Graph.ErdosRenyiG",        // G(n,p) random graph
            "Graph.ErdosRenyiGnm",      // G(n,m) random graph
            "Graph.RandomRegular",      // Random regular graph
            "Graph.BarabasiAlbert",     // Preferential attachment
            "Graph.WattsStrogatz",      // Small-world model
            "Graph.ConfigurationModel", // Random with fixed degrees
            "Graph.GiantComponent",     // Phase transition
            "Graph.ThresholdFunction",  // Property threshold
            "Graph.Monotone",           // Monotone graph property
            "Graph.ZeroOneLaw",         // Property has probability 0 or 1
            // ================================================================
            // Extremal Graph Theory
            // ================================================================
            "Graph.TuranNumber",       // ex(n, H) - max edges without H
            "Graph.TuranGraph",        // T(n,r) - extremal graph
            "Graph.TuranTheorem",      // ex(n, K_r)
            "Graph.ErdosStone",        // Asymptotic Turán number
            "Graph.RamseyNumber",      // R(s,t) - guaranteed clique/independent
            "Graph.RamseyTheorem",     // R(s,t) exists
            "Graph.Extremal",          // Extremal graph for property
            "Graph.Forbidden",         // Forbidden subgraph
            "Graph.MinorFree",         // No forbidden minor
            "Graph.RobertsonSeymour",  // Graph minor theorem
            "Graph.WellQuasiOrdering", // Minors form WQO
            // ================================================================
            // Algebraic Graph Theory
            // ================================================================
            "Graph.IncidenceAlgebra",  // Algebraic structure from poset
            "Graph.MobiusFunction",    // Möbius function on graph poset
            "Graph.GraphZetaFunction", // Ihara zeta function
            "Graph.CycleSpace",        // Vector space of cycles
            "Graph.CutSpace",          // Vector space of cuts
            "Graph.BondSpace",         // Space of bonds
            "Graph.CircuitRank",       // m - n + c (cyclomatic complexity)
            // ================================================================
            // Computational Complexity
            // ================================================================
            "Graph.HamiltonianNP", // Hamiltonian cycle is NP-complete
            "Graph.CliqueNP",      // Max clique is NP-complete
            "Graph.ColoringNP",    // k-coloring (k≥3) is NP-complete
            "Graph.IsomorphismGI", // Graph isomorphism in GI
            "Graph.PlanarityP",    // Planarity testing in P
            "Graph.TreewidthFPT",  // Fixed-parameter tractable
            // ================================================================
            // Graph Metrics and Centrality
            // ================================================================
            "Graph.DegreeCentrality",      // Based on degree
            "Graph.ClosenessCentrality",   // Based on distances
            "Graph.BetweennessCentrality", // Based on shortest paths through
            "Graph.EigenvectorCentrality", // Based on eigenvector
            "Graph.PageRank",              // Random walk centrality
            "Graph.Katz",                  // Katz centrality
            "Graph.HITS",                  // Hub and authority scores
            "Graph.ClusteringCoefficient", // Local clustering
            "Graph.GlobalClustering",      // Global clustering coefficient
            "Graph.Transitivity",          // Fraction of transitive triples
            "Graph.Assortivity",           // Degree correlation
            "Graph.Density",               // |E| / (|V| choose 2)
            // ================================================================
            // Graph Drawing
            // ================================================================
            "Graph.Embedding",           // Mapping to geometric space
            "Graph.PlanarEmbedding",     // Embedding in plane
            "Graph.OrthogonalDrawing",   // Grid drawing with bends
            "Graph.StraightLineDrawing", // Edges as line segments
            "Graph.ConvexDrawing",       // Faces are convex
            "Graph.UpwardDrawing",       // DAG with edges pointing up
            "Graph.LayeredDrawing",      // Sugiyama-style
            "Graph.ForceDirected",       // Spring-based layout
            "Graph.SpectralDrawing",     // Based on eigenvectors
            // ================================================================
            // Hypergraphs
            // ================================================================
            "Graph.Hyperedge",          // Edge connecting multiple vertices
            "Graph.HypergraphRank",     // Max size of hyperedge
            "Graph.HypergraphDual",     // Vertices ↔ hyperedges
            "Graph.HypergraphColoring", // Hyperedge not monochromatic
            "Graph.HypergraphMatching", // Pairwise disjoint hyperedges
            "Graph.HypergraphCover",    // Cover all vertices
            // ================================================================
            // Directed Graph Properties
            // ================================================================
            "Graph.Acyclic",              // No directed cycles
            "Graph.Tournament",           // Complete directed graph
            "Graph.TransitiveTournament", // Total order
            "Graph.StrongOrientation",    // Make graph strongly connected
            "Graph.Condensation",         // DAG of SCCs
            "Graph.SCC",                  // Strongly connected component
            "Graph.TarjanSCC",            // Tarjan's SCC algorithm
            "Graph.KosarajuSCC",          // Kosaraju's SCC algorithm
            // ================================================================
            // Applications
            // ================================================================
            "Graph.DependencyGraph",    // Dependencies between tasks
            "Graph.ControlFlowGraph",   // CFG for program analysis
            "Graph.DataFlowGraph",      // DFG for data dependencies
            "Graph.CallGraph",          // Function call relationships
            "Graph.SocialNetwork",      // Social relationships
            "Graph.KnowledgeGraph",     // Entity-relation structure
            "Graph.BayesianNetwork",    // DAG for probabilistic inference
            "Graph.MarkovRandomField",  // Undirected probabilistic model
            "Graph.FactorGraph",        // Bipartite representation of MRF
            "Graph.NeuralNetworkGraph", // Computation graph for NN
            "Graph.CircuitGraph",       // Digital circuit representation
        ] {
            let decl = Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            };
            self.add_decl(decl)?;
        }

        self.graph_theory_init = true;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::test_helpers::assert_const;

    #[test]
    fn test_init_graph_theory() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in ["Graph.Vertex", "Graph.Edge", "Graph.Graph", "Graph.Digraph"] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_adjacency() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.Adjacent",
            "Graph.Neighbor",
            "Graph.Neighborhood",
            "Graph.Degree",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_paths() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.Walk",
            "Graph.Path",
            "Graph.Cycle",
            "Graph.ShortestPath",
            "Graph.Distance",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_connectivity() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.Connected",
            "Graph.StronglyConnected",
            "Graph.Component",
            "Graph.Bridge",
            "Graph.CutVertex",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_trees() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.Tree",
            "Graph.Forest",
            "Graph.SpanningTree",
            "Graph.MinSpanningTree",
            "Graph.RootedTree",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_bipartite() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.Bipartite",
            "Graph.Matching",
            "Graph.PerfectMatching",
            "Graph.HallCondition",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_coloring() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.VertexColoring",
            "Graph.ChromaticNumber",
            "Graph.EdgeColoring",
            "Graph.VizingTheorem",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_planar() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.Planar",
            "Graph.EulerFormula",
            "Graph.KuratowskiTheorem",
            "Graph.FourColorTheorem",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_flow() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.FlowNetwork",
            "Graph.MaxFlow",
            "Graph.MaxFlowMinCut",
            "Graph.FordFulkerson",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_algorithms() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.BFS",
            "Graph.DFS",
            "Graph.Dijkstra",
            "Graph.BellmanFord",
            "Graph.Kruskal",
            "Graph.Prim",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_special_classes() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.CompleteGraph",
            "Graph.CycleGraph",
            "Graph.PetersenGraph",
            "Graph.HypercubeGraph",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_decomposition() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.TreeDecomposition",
            "Graph.Treewidth",
            "Graph.ModularDecomposition",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_spectral() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.AdjacencySpectrum",
            "Graph.LaplacianSpectrum",
            "Graph.SpectralGap",
            "Graph.Expander",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_random() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.ErdosRenyiG",
            "Graph.BarabasiAlbert",
            "Graph.WattsStrogatz",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_applications() {
        let mut env = Environment::new();
        env.init_graph_theory().unwrap();

        for s in [
            "Graph.ControlFlowGraph",
            "Graph.DataFlowGraph",
            "Graph.KnowledgeGraph",
            "Graph.BayesianNetwork",
        ] {
            assert_const(&env, s);
        }
    }

    #[test]
    fn test_graph_theory_key_types_well_formed() {
        use crate::expr::ExprKind;
        use crate::level::Level;
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_graph_theory().unwrap();
        let tc = TypeChecker::new(&env);

        for name in &["Graph.Graph", "Graph.Digraph", "Graph.Vertex"] {
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
