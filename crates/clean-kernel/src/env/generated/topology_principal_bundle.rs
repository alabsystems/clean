// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::env::generated::simple_axioms::build_simple_type_u_payload;
use crate::env::types::ConstantInfo;

pub(crate) const NAMESPACE: &str = "Topology.PrincipalBundle";
pub(crate) const DECL_COUNT: usize = 16;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.PrincipalBundle.PrincipalBundle",
    "Topology.PrincipalBundle.proj",
    "Topology.PrincipalBundle.action",
    "Topology.PrincipalBundle.action_free",
    "Topology.PrincipalBundle.action_transitive",
    "Topology.PrincipalBundle.GaugeTrans",
    "Topology.PrincipalBundle.GaugeGroup",
    "Topology.PrincipalBundle.gauge_trans_compose",
    "Topology.PrincipalBundle.gauge_trans_id",
    "Topology.PrincipalBundle.AssociatedBundle",
    "Topology.PrincipalBundle.PullbackBundle",
    "Topology.PrincipalBundle.BundleMorphism",
    "Topology.PrincipalBundle.FrameBundle",
    "Topology.PrincipalBundle.TrivialBundle",
    "Topology.PrincipalBundle.Reduction",
    "Topology.PrincipalBundle.Extension",
];

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let p = build_simple_type_u_payload(&DECL_NAMES);
    debug_assert_eq!(p.len(), DECL_COUNT, "payload size mismatch for {NAMESPACE}");
    p
}
