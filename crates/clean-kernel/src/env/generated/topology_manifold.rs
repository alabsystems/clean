// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::env::generated::topology_payload_legacy;
use crate::env::types::ConstantInfo;

pub(crate) const NAMESPACE: &str = "Topology.Manifold";
pub(crate) const DECL_COUNT: usize = 29;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Manifold.Chart",
    "Topology.Manifold.Chart.domain",
    "Topology.Manifold.Chart.toFun",
    "Topology.Manifold.Atlas",
    "Topology.Manifold.Atlas.charts",
    "Topology.Manifold.SmoothAtlas",
    "Topology.Manifold.SmoothManifold",
    "Topology.Manifold.TangentSpace",
    "Topology.Manifold.TangentBundle",
    "Topology.Manifold.CotangentSpace",
    "Topology.Manifold.SmoothMap",
    "Topology.Manifold.Diffeomorphism",
    "Topology.Manifold.IsDiffeomorphic",
    "Topology.Manifold.Immersion",
    "Topology.Manifold.Submersion",
    "Topology.Manifold.Embedding",
    "Topology.Manifold.LocalDiffeomorphism",
    "Topology.Manifold.Submanifold",
    "Topology.Manifold.VectorField",
    "Topology.Manifold.DifferentialForm",
    "Topology.Manifold.ExteriorDerivative",
    "Topology.Manifold.Orientable",
    "Topology.Manifold.Orientation",
    "Topology.Manifold.RiemannianMetric",
    "Topology.Manifold.RiemannianManifold",
    "Topology.Manifold.ManifoldWithBoundary",
    "Topology.Manifold.Boundary",
    "Topology.Manifold.PartitionOfUnity",
    "Topology.Manifold.paracompact_smooth_manifold",
];

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let p = topology_payload_legacy::build_topology_manifold_payload();
    debug_assert_eq!(p.len(), DECL_COUNT, "payload size mismatch for {NAMESPACE}");
    debug_assert_eq!(
        p.iter().map(|c| c.name.to_string()).collect::<Vec<_>>(),
        DECL_NAMES.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
        "payload names mismatch for {NAMESPACE}"
    );
    p
}
