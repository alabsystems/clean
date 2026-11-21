// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeSet, HashSet};

use clean_kernel::expr::UsedConstants;
use clean_kernel::{ConstantKind, Environment, Name, ReferenceKernel};

use super::{under_init, StoredModule};

pub(super) fn compare_monomorphic_proof_transport(
    pinned: &ReferenceKernel,
    source: &ReferenceKernel,
    stored: &[StoredModule],
) {
    let mut compared = 0;
    let mut accepted = 0;
    for name in stored.iter().flat_map(|module| &module.theorems) {
        let Some(actual) = source.environment().get_const(name) else {
            continue;
        };
        let expected = pinned
            .environment()
            .get_const(name)
            .expect("pinned theorem");
        // A single level assignment could hide a failure of a polymorphic
        // proof. This comparison uses the full monomorphic statement.
        if !expected.level_params.is_empty() {
            continue;
        }
        let Some(value) = actual.value.as_ref() else {
            continue;
        };
        assert_eq!(actual.kind, ConstantKind::Theorem);
        let result = pinned
            .check_closed_term(&expected.type_, value)
            .map(|_| ())
            .map_err(|error| error.to_string());
        compared += 1;
        if result.is_ok() {
            accepted += 1;
        }
        eprintln!(
            "I0_PROOF_TRANSPORT {name} {}",
            serde_json::json!({
                "name": name,
                "source_proof_at_original_pinned_type": result,
                "source_statement_equal": actual.level_params.is_empty() && actual.type_ == expected.type_,
                "source_proof": value,
            })
        );
    }
    eprintln!(
        "I0_PROOF_TRANSPORT_TOTAL monomorphic={compared} accepted_in_pinned_world={accepted}"
    );
}

pub(super) fn proof_transport_seed_names(
    source: &Environment,
    pinned: &Environment,
    imported: &Environment,
    stored: &[StoredModule],
) -> BTreeSet<Name> {
    let mut cited = HashSet::new();
    for name in stored.iter().flat_map(|module| &module.theorems) {
        if let Some(info) = source.get_const(name) {
            if info.level_params.is_empty() {
                if let Some(proof) = &info.value {
                    proof.used_constants_dag(UsedConstants::WithProjectionStructures, &mut cited);
                }
            }
        }
    }
    cited
        .into_iter()
        .filter(|name| {
            pinned.get_const(name).is_none()
                && imported
                    .get_constant_origin(name)
                    .and_then(|origin| origin.module_name())
                    .is_some_and(|module| under_init(&Name::from_string(module)))
        })
        .collect()
}
