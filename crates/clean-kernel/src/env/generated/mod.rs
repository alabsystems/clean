// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Namespace overlay payload modules for #1444.

// Live production module — called from prelude_providers via init_topological_space
pub(crate) mod topology_topological_space;

// All remaining generated overlay modules are test/feature-gated (~20K LOC).
// They are only consumed from dead-code topology init modules and tests.
#[cfg(any(test, feature = "math-overlays"))]
mod simple_axioms;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_characteristic;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_cobordism;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_connection;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_contractible;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_coproduct;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_covering_space;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_cw;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_derham;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_embedding;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_fiber_bundle;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_filtration;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_fundamental_group;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_higher_homotopy;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_homology;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_homotopy_equivalence;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_kahler;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_ktheory;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_lie_group;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_manifold;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_morse;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_path_connected;
#[cfg(any(test, feature = "math-overlays"))]
mod topology_payload_legacy;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_principal_bundle;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_product;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_quotient;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_retract;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_scheme;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_sheaf;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_simplicial;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_simply_connected;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_spectral;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_spin;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_subspace;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_suspension;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_symplectic;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod topology_vector_bundle;
