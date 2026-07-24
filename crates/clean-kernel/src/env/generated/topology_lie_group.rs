// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::env::generated::topology_payload_legacy;
use crate::env::types::ConstantInfo;

pub(crate) const NAMESPACE: &str = "Topology.LieGroup";
pub(crate) const DECL_COUNT: usize = 20;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.LieGroup.LieGroup",
    "Topology.LieGroup.LieAlgebra",
    "Topology.LieGroup.LieBracket",
    "Topology.LieGroup.ExpMap",
    "Topology.LieGroup.LieGroupHom",
    "Topology.LieGroup.LieSubgroup",
    "Topology.LieGroup.OneParameterSubgroup",
    "Topology.LieGroup.AdjointRep",
    "Topology.LieGroup.adjoint_rep",
    "Topology.LieGroup.IsConnected",
    "Topology.LieGroup.IsSimplyConnected",
    "Topology.LieGroup.IsCompact",
    "Topology.LieGroup.IsSemisimple",
    "Topology.LieGroup.IsSimple",
    "Topology.LieGroup.IsAbelian",
    "Topology.LieGroup.UniversalCover",
    "Topology.LieGroup.KillingForm",
    "Topology.LieGroup.killing_form_semisimple",
    "Topology.LieGroup.exp_one_param",
    "Topology.LieGroup.LieAlgebraHom",
];

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let p = topology_payload_legacy::build_topology_lie_group_payload();
    debug_assert_eq!(p.len(), DECL_COUNT, "payload size mismatch for {NAMESPACE}");
    debug_assert_eq!(
        p.iter().map(|c| c.name.to_string()).collect::<Vec<_>>(),
        DECL_NAMES.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
        "payload names mismatch for {NAMESPACE}"
    );
    p
}
