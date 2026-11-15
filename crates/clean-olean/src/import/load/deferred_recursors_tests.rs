// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::import::{
    load_register::load_module_direct_with_cache_and_policy, DeferredRecursorStatus,
};
use crate::test_support::compiled_fixture_dir;

const MODULE: &str = "PrivateFamilyDependencies";

fn parts() -> [LoadModule; 3] {
    let path = compiled_fixture_dir("private_family_dependencies").join(format!("{MODULE}.olean"));
    let base = std::fs::read(&path).expect("pinned base");
    let server = std::fs::read(path.with_extension("olean.server")).expect("pinned server");
    let private = std::fs::read(path.with_extension("olean.private")).expect("pinned private");
    [
        parse_load_module(base.clone()).expect("parse base"),
        parse_load_module_incremental(&base, None, server.clone()).expect("parse server"),
        parse_load_module_incremental(&base, Some(&server), private).expect("parse private"),
    ]
}

fn load(
    env: &mut Environment,
    module: &str,
    parts: &[LoadModule; 3],
) -> (Result<(), ImportError>, Vec<LoadSummary>) {
    let mut summaries = Vec::new();
    let result = load_artifact_parts(
        env,
        module,
        &parts[0],
        Some(&parts[1]),
        Some(&parts[2]),
        &mut summaries,
        &mut ExprInternCache::default(),
        OleanImportPolicy::default(),
    );
    (result, summaries)
}

fn name(parts: &[LoadModule; 3], suffix: &str) -> Name {
    parts[2]
        .constants
        .iter()
        .find(|c| c.name.ends_with(suffix))
        .expect("exact fixture declaration")
        .kernel_name
        .clone()
}

#[test]
fn private_family_dependency_staging_preserves_honest_records_and_flags() {
    let parts = parts();
    let proof = name(&parts, ".ProofOnly");
    let proof_rec = name(&parts, ".ProofOnly.rec");
    let data = name(&parts, ".DataField");
    let data_rec = name(&parts, ".DataField.rec");
    let mut env = Environment::new();
    let (result, summaries) = load(&mut env, MODULE, &parts);
    result.expect("complete honest artifact");
    let deferred: Vec<_> = summaries
        .iter()
        .flat_map(|s| &s.deferred_recursors)
        .collect();
    assert!(
        !deferred.is_empty(),
        "fixture must exercise staging, not only final admission"
    );
    assert_eq!(
        deferred.len(),
        2,
        "only genuinely rejected early records should wait"
    );
    assert!(deferred
        .iter()
        .all(|row| row.name == proof_rec && !row.initial_refusal.is_empty()));
    assert!(deferred
        .iter()
        .all(|row| row.status == DeferredRecursorStatus::Resolved));
    assert!(summaries.iter().all(|s| s.skipped_constants.is_empty()));
    assert_eq!(
        env.get_recursor(&proof_rec)
            .expect("strictly admitted recursor")
            .level_params
            .len(),
        1
    );
    assert!(
        env.get_inductive(&proof)
            .expect("resident proof family")
            .is_large_elim
    );
    assert!(
        !env.get_inductive(&data)
            .expect("resident data family")
            .is_large_elim
    );
    assert!(env
        .get_recursor(&data_rec)
        .expect("strictly admitted data-family recursor")
        .level_params
        .is_empty());
    for (part_index, summary) in summaries.iter().enumerate() {
        for row in &summary.deferred_recursors {
            assert_eq!(
                parts[part_index].constants[row.source_constant_ordinal].kernel_name,
                row.name
            );
            assert!(!row.missing_dependencies.is_empty());
        }
    }
}

#[test]
fn private_family_dependency_direct_load_stays_strict() {
    let parts = parts();
    let rec = name(&parts, ".ProofOnly.rec");
    let data = name(&parts, ".DataField.rec");
    let mut env = Environment::new();
    let summary = load_module_direct_with_cache_and_policy(
        &mut env,
        &parts[0],
        Some(MODULE.into()),
        &mut ExprInternCache::default(),
        OleanImportPolicy::default(),
    )
    .expect("direct structural load");
    assert!(summary.deferred_recursors.is_empty());
    assert!(summary
        .skipped_constants
        .iter()
        .any(|row| row.name == rec.to_string()));
    assert!(env.get_recursor(&rec).is_none());
    assert!(
        env.get_recursor(&data).is_some(),
        "irrelevant missing proof terms must not delay a successful strict admission"
    );
}

#[test]
fn private_family_dependency_missing_private_or_dependency_refuses() {
    let mut parts = parts();
    let mut env = Environment::new();
    assert!(load_artifact_parts(
        &mut env,
        MODULE,
        &parts[0],
        Some(&parts[1]),
        None,
        &mut Vec::new(),
        &mut ExprInternCache::default(),
        OleanImportPolicy::default()
    )
    .is_err());
    let secret = name(&parts, ".secret");
    parts[2]
        .constants
        .iter_mut()
        .find(|c| c.kernel_name == secret)
        .unwrap()
        .type_ptr = 0;
    let (result, summaries) = load(&mut Environment::new(), MODULE, &parts);
    assert!(
        result.is_err(),
        "a missing private dependency must fail the whole artifact"
    );
    let deferred: Vec<_> = summaries
        .iter()
        .flat_map(|s| &s.deferred_recursors)
        .collect();
    assert!(
        !deferred.is_empty(),
        "must reach finalization with real staged records"
    );
    assert!(deferred
        .iter()
        .any(|row| matches!(row.status, DeferredRecursorStatus::Refused(_))));
}

#[test]
fn private_family_dependency_changed_and_forged_large_recursors_refuse() {
    let genuine = parts();
    let proof = name(&genuine, ".ProofOnly.rec");
    let mut changed = parts();
    changed[2]
        .constants
        .iter_mut()
        .find(|c| c.kernel_name == proof)
        .unwrap()
        .recursor_val
        .as_mut()
        .unwrap()
        .num_minors += 1;
    assert!(load(&mut Environment::new(), MODULE, &changed).0.is_err());
    let data = name(&genuine, ".DataField.rec");
    let mut forged = genuine;
    for part in &mut forged {
        part.constants
            .iter_mut()
            .find(|c| c.kernel_name == data)
            .unwrap()
            .kernel_level_params
            .push(Name::from_string("forged"));
    }
    let mut env = Environment::new();
    let (result, summaries) = load(&mut env, MODULE, &forged);
    assert!(
        result.is_err(),
        "forged queued record must refuse the whole artifact: {summaries:?}"
    );
    assert!(env.get_recursor(&data).is_none());
}

#[test]
fn private_family_dependency_cannot_rebind_a_foreign_family() {
    let parts = parts();
    let proof = name(&parts, ".ProofOnly");
    let mut env = Environment::new();
    load(&mut env, MODULE, &parts).0.expect("original owner");
    let before = env.get_inductive(&proof).unwrap().clone();
    let (result, _) = load(&mut env, "DifferentOwner", &parts);
    assert!(result.is_err());
    assert_eq!(
        env.get_inductive(&proof).unwrap().is_large_elim,
        before.is_large_elim
    );
}
