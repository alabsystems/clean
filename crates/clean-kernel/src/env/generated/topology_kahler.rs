// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::env::generated::simple_axioms::build_simple_type_u_payload;
use crate::env::types::ConstantInfo;

pub(crate) const NAMESPACE: &str = "Topology.Kahler";
pub(crate) const DECL_COUNT: usize = 37;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    // Complex structures
    "Topology.Kahler.ComplexStructure",
    "Topology.Kahler.complex_structure_sq",
    "Topology.Kahler.AlmostComplexManifold",
    "Topology.Kahler.Integrable",
    "Topology.Kahler.ComplexManifold",
    // Compatibility conditions
    "Topology.Kahler.Hermitian",
    "Topology.Kahler.KahlerForm",
    "Topology.Kahler.kahler_form_compatibility",
    "Topology.Kahler.KahlerManifold",
    // Holomorphic structures
    "Topology.Kahler.HolomorphicMap",
    "Topology.Kahler.Biholomorphism",
    "Topology.Kahler.HolomorphicVectorBundle",
    "Topology.Kahler.HolomorphicSection",
    // Connections and curvature
    "Topology.Kahler.ChernConnection",
    "Topology.Kahler.chern_connection_unique",
    "Topology.Kahler.ChernCurvature",
    "Topology.Kahler.ChernClass",
    "Topology.Kahler.first_chern_class",
    // Ricci geometry
    "Topology.Kahler.RicciForm",
    "Topology.Kahler.ricci_form_closed",
    "Topology.Kahler.ScalarCurvature",
    "Topology.Kahler.KahlerEinstein",
    "Topology.Kahler.CalabiYau",
    "Topology.Kahler.CalabiConjecture",
    // Cohomology and Hodge theory
    "Topology.Kahler.HodgeDecomposition",
    "Topology.Kahler.hodge_symmetry",
    "Topology.Kahler.DolbeaultCohomology",
    "Topology.Kahler.DolbeaultOperator",
    "Topology.Kahler.HardLefschetz",
    "Topology.Kahler.LefschetzDecomposition",
    "Topology.Kahler.KodairaVanishing",
    // Standard examples
    "Topology.Kahler.FubiniStudyMetric",
    "Topology.Kahler.FubiniStudyKahler",
    // Hypercomplex and quaternionic
    "Topology.Kahler.HyperKahlerManifold",
    "Topology.Kahler.hypercomplex_relation",
    "Topology.Kahler.QuaternionicKahler",
    "Topology.Kahler.hyperkahler_holonomy",
];

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let p = build_simple_type_u_payload(&DECL_NAMES);
    debug_assert_eq!(p.len(), DECL_COUNT, "payload size mismatch for {NAMESPACE}");
    p
}
