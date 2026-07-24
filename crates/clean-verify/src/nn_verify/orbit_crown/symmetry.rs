// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Symmetry group formalization for neural network equivariance.
//!
//! Provides the [`SymmetryGroup`] trait with `orbit()`, `stabilizer()`, and
//! `quotient_dim()` operations, plus concrete implementations for:
//!
//! - [`TranslationGroup`]: Cyclic translations (convolution equivariance).
//! - [`PermutationGroup`]: Permutations of node indices (graph NN equivariance).
//!
//! ## Group Theory Recap
//!
//! For a group G acting on a set X:
//! - **Orbit** of x: `G.x = { g.x | g in G }`
//! - **Stabilizer** of x: `Stab(x) = { g in G | g.x = x }`
//! - **Orbit-stabilizer theorem**: `|G| = |Orb(x)| * |Stab(x)|`
//! - **Quotient dimension**: `dim(X/G) = dim(X) / |orbit|` for free actions.

/// A group element represented as a permutation matrix (stored as index mapping).
///
/// For element sigma, `mapping[i] = j` means position i maps to position j.
/// The permutation matrix rho(sigma) has rho[i][sigma(i)] = 1.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GroupElement {
    /// Permutation mapping: `mapping[i] = j` means element at position i
    /// is sent to position j under this group action.
    pub(crate) mapping: Vec<usize>,
}

impl GroupElement {
    /// Create a new group element from a permutation mapping.
    ///
    /// # Panics
    ///
    /// Debug-asserts that `mapping` is a valid permutation (bijection on `0..n`).
    #[must_use]
    pub fn new(mapping: Vec<usize>) -> Self {
        debug_assert!(
            is_valid_permutation(&mapping),
            "mapping must be a valid permutation"
        );
        Self { mapping }
    }

    /// Dimension of the space this group element acts on.
    #[must_use]
    pub fn dim(&self) -> usize {
        self.mapping.len()
    }

    /// The identity element on `n` dimensions.
    #[must_use]
    pub fn identity(n: usize) -> Self {
        Self {
            mapping: (0..n).collect(),
        }
    }

    /// Compose two group elements: `(self * other)(x) = self(other(x))`.
    #[must_use]
    pub fn compose(&self, other: &Self) -> Self {
        debug_assert_eq!(
            self.dim(),
            other.dim(),
            "group elements must act on same dimension"
        );
        let mapping = other.mapping.iter().map(|&j| self.mapping[j]).collect();
        Self { mapping }
    }

    /// Compute the inverse permutation.
    #[must_use]
    pub fn inverse(&self) -> Self {
        let n = self.dim();
        let mut inv = vec![0; n];
        for (i, &j) in self.mapping.iter().enumerate() {
            inv[j] = i;
        }
        Self { mapping: inv }
    }

    /// Apply this group element to a vector: `g.x[i] = x[sigma^{-1}(i)]`.
    ///
    /// This is the standard left action: the value at position `sigma(j)` in
    /// the output equals the value at position `j` in the input.
    #[must_use]
    pub fn act_on_vec(&self, x: &[f64]) -> Vec<f64> {
        debug_assert_eq!(
            x.len(),
            self.dim(),
            "vector dimension must match group element"
        );
        let mut result = vec![0.0; x.len()];
        for (j, &sigma_j) in self.mapping.iter().enumerate() {
            result[sigma_j] = x[j];
        }
        result
    }

    /// Apply this group element to a matrix: `rho(g) * W * rho(g)^{-1}`.
    ///
    /// For equivariant layers, `rho(g) * W = W * rho(g)`, so this is the
    /// conjugation action. Rows are permuted by sigma, columns by sigma^{-1}.
    #[must_use]
    pub fn conjugate_matrix(&self, w: &[Vec<f64>]) -> Vec<Vec<f64>> {
        let n = self.dim();
        debug_assert_eq!(w.len(), n, "matrix row count must match group dimension");
        let inv = self.inverse();
        let mut result = vec![vec![0.0; n]; n];
        for i in 0..n {
            debug_assert_eq!(w[i].len(), n, "matrix must be square");
            for j in 0..n {
                result[self.mapping[i]][self.mapping[j]] = w[i][j];
            }
        }
        let _ = inv; // inv used implicitly through the permutation
        result
    }

    /// Build the permutation matrix rho(sigma) as a dense matrix.
    ///
    /// `rho[i][j] = 1.0` if `sigma(j) == i`, else `0.0`.
    #[must_use]
    pub fn to_permutation_matrix(&self) -> Vec<Vec<f64>> {
        let n = self.dim();
        let mut rho = vec![vec![0.0; n]; n];
        for (j, &sigma_j) in self.mapping.iter().enumerate() {
            rho[sigma_j][j] = 1.0;
        }
        rho
    }
}

/// An orbit under a group action: a set of indices related by symmetry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Orbit {
    /// Indices in this orbit, sorted ascending.
    pub indices: Vec<usize>,
}

impl Orbit {
    /// Size of this orbit.
    #[must_use]
    pub fn size(&self) -> usize {
        self.indices.len()
    }

    /// The representative element (smallest index in the orbit).
    #[must_use]
    pub fn representative(&self) -> usize {
        self.indices[0]
    }
}

/// Trait for finite symmetry groups acting on R^n.
///
/// Implementors provide the group generators, orbit computation, stabilizer
/// size, and quotient dimension. The key invariant is the orbit-stabilizer
/// theorem: `|G| = |orbit(x)| * |stabilizer(x)|` for all x.
pub trait SymmetryGroup: std::fmt::Debug {
    /// Dimension of the space this group acts on.
    fn dim(&self) -> usize;

    /// Order of the group (number of elements).
    fn order(&self) -> usize;

    /// Return the group generators.
    ///
    /// Every group element can be written as a product of generators.
    fn generators(&self) -> Vec<GroupElement>;

    /// Compute the orbit of position `index` under the group action.
    ///
    /// Returns the set of all positions reachable from `index` by applying
    /// group elements.
    fn orbit(&self, index: usize) -> Orbit;

    /// Compute all distinct orbits partitioning `{0, ..., dim-1}`.
    fn all_orbits(&self) -> Vec<Orbit> {
        let n = self.dim();
        let mut visited = vec![false; n];
        let mut orbits = Vec::new();
        for i in 0..n {
            if !visited[i] {
                let orb = self.orbit(i);
                for &idx in &orb.indices {
                    visited[idx] = true;
                }
                orbits.push(orb);
            }
        }
        orbits
    }

    /// Size of the stabilizer of `index`.
    ///
    /// By the orbit-stabilizer theorem: `stabilizer_size(i) = order / orbit(i).size()`.
    fn stabilizer_size(&self, index: usize) -> usize {
        let orbit_size = self.orbit(index).size();
        self.order() / orbit_size
    }

    /// Dimension of the quotient space X/G.
    ///
    /// Equal to the number of distinct orbits.
    fn quotient_dim(&self) -> usize {
        self.all_orbits().len()
    }
}

// ---------------------------------------------------------------------------
// Translation Group (cyclic shifts — convolution equivariance)
// ---------------------------------------------------------------------------

/// Cyclic translation group Z_n acting on R^n by index shifts.
///
/// The generator is the cyclic shift `sigma(i) = (i + 1) mod n`.
/// This captures the translation equivariance of circular convolutions:
/// shifting the input by one position shifts the output by one position.
///
/// Order: n (for Z_n).
/// Orbits: if n divides dim evenly, one orbit of size n containing all indices.
///         Otherwise, depends on gcd structure.
#[derive(Debug, Clone)]
pub struct TranslationGroup {
    /// Dimension of the vector space.
    dim: usize,
    /// Translation step size (default 1 for standard cyclic shift).
    step: usize,
}

impl TranslationGroup {
    /// Create a cyclic translation group on `dim` dimensions with step size 1.
    #[must_use]
    pub fn new(dim: usize) -> Self {
        Self { dim, step: 1 }
    }

    /// Create a cyclic translation group with a custom step size.
    ///
    /// The orbit size will be `dim / gcd(dim, step)`.
    #[must_use]
    pub fn with_step(dim: usize, step: usize) -> Self {
        debug_assert!(step > 0, "step must be positive");
        Self { dim, step }
    }
}

impl SymmetryGroup for TranslationGroup {
    fn dim(&self) -> usize {
        self.dim
    }

    fn order(&self) -> usize {
        // Order of the cyclic subgroup generated by shift-by-step.
        self.dim / gcd(self.dim, self.step)
    }

    fn generators(&self) -> Vec<GroupElement> {
        let n = self.dim;
        let mapping: Vec<usize> = (0..n).map(|i| (i + self.step) % n).collect();
        vec![GroupElement::new(mapping)]
    }

    fn orbit(&self, index: usize) -> Orbit {
        let n = self.dim;
        let orbit_size = n / gcd(n, self.step);
        let mut indices = Vec::with_capacity(orbit_size);
        let mut current = index;
        for _ in 0..orbit_size {
            indices.push(current);
            current = (current + self.step) % n;
        }
        indices.sort_unstable();
        indices.dedup();
        Orbit { indices }
    }
}

// ---------------------------------------------------------------------------
// Permutation Group (specified by generators)
// ---------------------------------------------------------------------------

/// Finite permutation group on n elements, specified by generators.
///
/// Captures symmetries like:
/// - Graph automorphisms (for graph neural networks)
/// - Channel permutation symmetry
/// - Node relabeling invariance
///
/// The group is the closure of the generator set under composition.
#[derive(Debug, Clone)]
pub struct PermutationGroup {
    dim: usize,
    generators: Vec<GroupElement>,
    /// Cached group order (computed lazily on first call).
    cached_order: Option<usize>,
}

impl PermutationGroup {
    /// Create a permutation group from generators.
    ///
    /// # Panics
    ///
    /// Debug-asserts that all generators have the same dimension.
    #[must_use]
    pub fn new(dim: usize, generators: Vec<GroupElement>) -> Self {
        for g in &generators {
            debug_assert_eq!(
                g.dim(),
                dim,
                "generator dimension must match group dimension"
            );
        }
        Self {
            dim,
            generators,
            cached_order: None,
        }
    }

    /// Enumerate all group elements by closing the generators under composition.
    ///
    /// Uses BFS from the identity through all generator products.
    /// For large groups, this can be expensive — use only when the group
    /// is known to be small (e.g., S_3, D_4, small graph automorphism groups).
    #[must_use]
    pub fn enumerate_elements(&self) -> Vec<GroupElement> {
        let identity = GroupElement::identity(self.dim);
        let mut elements = vec![identity.clone()];
        let mut seen: std::collections::HashSet<Vec<usize>> = std::collections::HashSet::new();
        seen.insert(identity.mapping.clone());

        let mut queue = std::collections::VecDeque::new();
        queue.push_back(identity);

        while let Some(current) = queue.pop_front() {
            for generator in &self.generators {
                let product = current.compose(generator);
                if seen.insert(product.mapping.clone()) {
                    queue.push_back(product.clone());
                    elements.push(product);
                }
                // Also try the inverse direction
                let inv_product = current.compose(&generator.inverse());
                if seen.insert(inv_product.mapping.clone()) {
                    queue.push_back(inv_product.clone());
                    elements.push(inv_product);
                }
            }
        }
        elements
    }
}

impl SymmetryGroup for PermutationGroup {
    fn dim(&self) -> usize {
        self.dim
    }

    fn order(&self) -> usize {
        if let Some(order) = self.cached_order {
            return order;
        }
        self.enumerate_elements().len()
    }

    fn generators(&self) -> Vec<GroupElement> {
        self.generators.clone()
    }

    fn orbit(&self, index: usize) -> Orbit {
        let elements = self.enumerate_elements();
        let mut indices: Vec<usize> = elements.iter().map(|g| g.mapping[index]).collect();
        indices.sort_unstable();
        indices.dedup();
        Orbit { indices }
    }
}

// ---------------------------------------------------------------------------
// Utility functions
// ---------------------------------------------------------------------------

/// Check that a mapping is a valid permutation (bijection on `0..n`).
fn is_valid_permutation(mapping: &[usize]) -> bool {
    let n = mapping.len();
    let mut seen = vec![false; n];
    for &v in mapping {
        if v >= n || seen[v] {
            return false;
        }
        seen[v] = true;
    }
    true
}

/// Greatest common divisor (Euclidean algorithm).
fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}
