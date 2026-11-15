// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Public replay diagnostics cannot grant a completed reference kernel.

use clean_kernel::{Environment, Name};
use clean_olean::{reference_base_closed, ClosedRecheckOptions};
use std::collections::BTreeSet;

#[test]
fn edited_replay_diagnostics_cannot_grant_completion() {
    let env = Environment::for_lean_replay();
    let targets = BTreeSet::from([Name::from_string("MissingCompletionTarget")]);
    let mut base = reference_base_closed(&env, &targets, &ClosedRecheckOptions::default()).unwrap();
    assert!(!base.report.passed());
    let original_failure = serde_json::to_value(&base.report).unwrap();

    base.report.refusals.clear();
    base.report.extension_bindings_pinned = true;
    base.entry_refusals.clear();
    base.admitted
        .insert(Name::from_string("MissingCompletionTarget"));
    assert!(base.report.passed() && base.report.extension_bindings_pinned);

    let failure = base
        .into_kernel()
        .expect_err("edited public diagnostics cannot complete the original failed replay");
    assert_eq!(serde_json::to_value(failure).unwrap(), original_failure);
}
