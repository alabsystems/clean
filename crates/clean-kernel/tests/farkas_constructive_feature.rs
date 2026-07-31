// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proves that the production library, without `cfg(test)` overlays, can
//! initialize the constructive Farkas anchor through its narrow feature.

use clean_kernel::env::Environment;
use clean_kernel::name::Name;

#[test]
fn narrow_feature_initializes_only_the_constructive_anchor() {
    let mut env = Environment::new();
    env.init_nn_verify_farkas_constructive()
        .expect("initialize constructive Farkas anchor");

    for name in [
        "NNVerify.farkas_scale",
        "NNVerify.farkas_combine_2",
        "NNVerify.farkas_combine_2_le_bound",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} must be registered"));
        assert!(info.value.is_some(), "{name} must carry a proof term");
        assert!(
            !info.sorry_summary().has_sorry,
            "{name} must remain constructive"
        );
    }

    assert!(
        env.get_const(&Name::from_string("NNVerify.ibp_linear_sound"))
            .is_none(),
        "the narrow feature must not initialize the full IBP overlay"
    );
}
