// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{finish_import_module, ImportPolicy, ImportResolution};
use crate::ElabError;
use clean_kernel::{Environment, Name};
use clean_olean::ImportError;
use std::collections::HashSet;

#[test]
fn resource_refusals_never_take_import_fallbacks() {
    let module = Name::from_string("Lean.ResourceProbe");
    let satisfied = HashSet::from([module.clone()]);
    for policy in [ImportPolicy::FailClosed, ImportPolicy::Permissive] {
        let resolution = ImportResolution {
            policy,
            satisfied_from_source: &satisfied,
        };
        let mut env = Environment::new();
        // The same name normally resolves through the source record.
        finish_import_module(&mut env, &module, None, resolution)
            .expect("positive fallback control");
        let before = env.num_constants();
        for error in [
            ImportError::Interrupted,
            ImportError::ResourceLimit {
                operation: "structure-field validation".to_owned(),
                reason: "declaration budget exhausted".to_owned(),
            },
        ] {
            let message = error.to_string();
            let result = finish_import_module(&mut env, &module, Some(Err(error)), resolution);
            assert!(matches!(
                result,
                Err(ElabError::UnresolvedImport { ref reason, .. }) if reason == &message
            ));
            assert_eq!(env.num_constants(), before, "no stand-in may be registered");
        }
    }
}
