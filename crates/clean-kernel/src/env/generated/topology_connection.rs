// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::env::generated::simple_axioms::build_simple_type_u_payload;
use crate::env::types::ConstantInfo;

pub(crate) const NAMESPACE: &str = "Topology.Connection";
pub(crate) const DECL_COUNT: usize = 20;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Connection.Connection",
    "Topology.Connection.form",
    "Topology.Connection.curvature",
    "Topology.Connection.flat",
    "Topology.Connection.holonomy",
    "Topology.Connection.flat_trivial_holonomy",
    "Topology.Connection.VectorConnection",
    "Topology.Connection.covariant_derivative",
    "Topology.Connection.LeviCivita",
    "Topology.Connection.levi_civita_metric_compatible",
    "Topology.Connection.levi_civita_torsion_free",
    "Topology.Connection.levi_civita_unique",
    "Topology.Connection.Christoffel",
    "Topology.Connection.RiemannCurvature",
    "Topology.Connection.RicciTensor",
    "Topology.Connection.ScalarCurvature",
    "Topology.Connection.Geodesic",
    "Topology.Connection.ParallelTransport",
    "Topology.Connection.HorizontalLift",
    "Topology.Connection.BianchiIdentity",
];

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let p = build_simple_type_u_payload(&DECL_NAMES);
    debug_assert_eq!(p.len(), DECL_COUNT, "payload size mismatch for {NAMESPACE}");
    p
}
