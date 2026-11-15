// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use std::collections::BTreeSet;

/// Check real three-part private completion, then re-derive its projection
/// closure through the strict ReferenceKernel entry boundary.
#[test]
fn test_checked_stub_private_artifact_keeps_closed_replay() {
    let dir = compiled_fixture_dir("import_passes");
    let mut env = Environment::for_lean_replay();
    clean_olean::load_module_with_deps(&mut env, "ImportPassesStubs", &[dir])
        .expect("the pinned private-part fixture loads");
    let targets = BTreeSet::from([
        Name::from_string("StubParts.Pair.first"),
        Name::from_string("StubParts.Pair.second"),
    ]);
    for target in &targets {
        assert!(env
            .get_const(target)
            .and_then(|info| info.value.as_ref())
            .is_some());
    }
    let checked =
        clean_olean::reference_base_closed(&env, &targets, &ClosedRecheckOptions::default())
            .expect("the real private completions remain dependency-closed");
    assert!(
        checked.report.passed(),
        "{}",
        checked.report.verdict_sentence()
    );
    assert!(checked.entry_refusals.is_empty());
    assert!(targets
        .iter()
        .all(|target| checked.admitted.contains(target)));
    eprintln!("{}", checked.report.verdict_sentence());
}
