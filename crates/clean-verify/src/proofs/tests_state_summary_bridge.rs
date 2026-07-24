// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_impl_state_matches_spec_bridge_proofs_use_and_witnesses() {
    let lib = ProofLibrary::new();
    for (proof_name, expected_fragment) in [
        ("impl_state_matches_spec_mk", "AndType.intro"),
        ("impl_state_matches_spec_env_valid", "AndType.left"),
        ("impl_state_matches_spec_ctx_well_formed", "AndType.right"),
    ] {
        let proof = lib
            .get(proof_name)
            .unwrap_or_else(|| panic!("missing proof {proof_name}"));
        assert!(
            proof.proof_src.contains(expected_fragment),
            "{proof_name} should witness the summary bridge via {expected_fragment}, got {:?}",
            proof.proof_src
        );
    }
}
