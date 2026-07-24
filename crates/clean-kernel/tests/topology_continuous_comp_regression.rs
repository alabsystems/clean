// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression guard for Topology.continuous_comp declaration closure (#1453).

use clean_kernel::{Environment, Name};

#[test]
fn topology_continuous_comp_type_has_no_loose_bvars() {
    let mut env = Environment::with_prelude();
    env.init_topology_continuous()
        .expect("topology continuous init should succeed");

    let comp_info = env
        .get_const(&Name::from_string("Topology.continuous_comp"))
        .expect("Topology.continuous_comp should exist after init_topology_continuous");

    assert!(
        !comp_info.type_.has_loose_bvars(),
        "Topology.continuous_comp type should be closed (no loose bvars), got {:?}",
        comp_info.type_
    );
}
