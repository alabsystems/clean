// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::env::generated::simple_axioms::build_simple_type_u_payload;
use crate::env::types::ConstantInfo;

pub(crate) const NAMESPACE: &str = "Topology.Symplectic";
pub(crate) const DECL_COUNT: usize = 27;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    // Core symplectic structures
    "Topology.Symplectic.SymplecticForm",
    "Topology.Symplectic.SymplecticManifold",
    "Topology.Symplectic.symplectic_form_closed",
    "Topology.Symplectic.symplectic_form_nondegenerate",
    "Topology.Symplectic.symplectic_dim_even",
    // Symplectomorphisms
    "Topology.Symplectic.Symplectomorphism",
    "Topology.Symplectic.symplectomorphism_compose",
    "Topology.Symplectic.symplectomorphism_inv",
    // Hamiltonian mechanics
    "Topology.Symplectic.HamiltonianVector",
    "Topology.Symplectic.HamiltonianFlow",
    "Topology.Symplectic.PoissonBracket",
    "Topology.Symplectic.poisson_jacobi",
    "Topology.Symplectic.poisson_leibniz",
    // Submanifolds
    "Topology.Symplectic.LagrangianSubmanifold",
    "Topology.Symplectic.CoisotropicSubmanifold",
    "Topology.Symplectic.IsotropicSubmanifold",
    // Symplectic reduction
    "Topology.Symplectic.MomentMap",
    "Topology.Symplectic.moment_equivariant",
    "Topology.Symplectic.SymplecticReduction",
    // Fundamental theorems
    "Topology.Symplectic.Darboux",
    "Topology.Symplectic.Moser",
    // Contact geometry (odd-dimensional analog)
    "Topology.Symplectic.ContactManifold",
    "Topology.Symplectic.ContactForm",
    "Topology.Symplectic.Reeb",
    "Topology.Symplectic.Contactomorphism",
    "Topology.Symplectic.Legendrian",
    "Topology.Symplectic.GrayStability",
];

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let p = build_simple_type_u_payload(&DECL_NAMES);
    debug_assert_eq!(p.len(), DECL_COUNT, "payload size mismatch for {NAMESPACE}");
    p
}
