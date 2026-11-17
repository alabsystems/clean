// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Negative controls of `designs/2026-11-16-p6-acceptance-identity.md`
//! section 4 for the manifest type itself (controls 1, 2, 3, 4, 6 and 7, plus
//! the review's discipline, executable-capture and migration-arm controls).

use clean_kernel::env::KernelTheory;
use clean_kernel::Environment;
use serde_json::{json, Value};

use super::identity::{test_run, test_run_in};
use super::*;

fn sharded(names: &[&str], run: DevelopmentRun) -> KernelVerifiedManifest {
    KernelVerifiedManifest::from_sharded_worker(
        "M",
        names.len(),
        0,
        0,
        0.0,
        names.iter().map(|n| (*n).to_string()).collect(),
        run,
    )
}

fn valid_value() -> Value {
    serde_json::to_value(sharded(&["a", "b"], test_run(Elision::None))).expect("serialize")
}

fn refusal(value: Value) -> ManifestError {
    KernelVerifiedManifest::from_value(value).expect_err("the control must be refused")
}

#[test]
fn test_manifest_round_trip_keeps_identity_names_and_counts() {
    let dir = tempfile::tempdir().expect("tmp");
    let path = dir.path().join("kernel-verified.json");
    let m = sharded(&["b", "a", "a"], test_run(Elision::Opaque));
    m.write_to_file(&path).expect("write");
    let back = KernelVerifiedManifest::from_file(&path).expect("a written manifest reads back");
    back.identity()
        .same_build(m.identity())
        .expect("same identity");
    assert_eq!(
        back.accepted_names(),
        ["a", "b"],
        "names are sorted and distinct"
    );
    assert_eq!(back.accepted(), 2);
    assert_eq!(back.tier(), AcceptanceTier::Development);
    assert_eq!(back.identity().imports(), Imports::Trusted);
}

#[test]
fn test_manifest_schema1_without_identity_refused() {
    // The inverted `test_legacy_manifest_without_fingerprint_deserializes_to_none`:
    // a schema-1 manifest names no theory and no checker, so it is refused,
    // never defaulted.
    let schema1 = json!({
        "schema_version": 1, "tool": "t", "clean_version": "0", "created_at": "x",
        "shard_dir": "d", "shards_loaded": 1, "total_constants": 1, "kernel_verified": 1,
        "axiom_accepted": 0, "axiom_fallback": 0, "failed": 0, "cycle_skipped": 0,
        "reconstruct_failed": 0, "elapsed_secs": 0.0, "kernel_verified_names": ["a"]
    });
    assert!(matches!(
        refusal(schema1.clone()),
        ManifestError::UnsupportedSchema { found } if found == "1"
    ));
    let err = serde_json::from_value::<KernelVerifiedManifest>(schema1)
        .expect_err("the serde path validates too");
    assert!(err.to_string().contains("schema_version 1"), "{err}");
    let mut absent = valid_value();
    absent
        .as_object_mut()
        .expect("object")
        .remove("schema_version");
    assert!(matches!(
        refusal(absent),
        ManifestError::UnsupportedSchema { found } if found == "absent"
    ));
}

#[test]
fn test_manifest_schema2_without_identity_refused() {
    let mut v = valid_value();
    v.as_object_mut().expect("object").remove("identity");
    assert_eq!(refusal(v), ManifestError::NoIdentity);
}

#[test]
fn test_manifest_profile_with_reference_entry_refused_as_forged() {
    let mut v = valid_value();
    v["identity"]["checker"]["entry"] = json!("clean-kernel/reference-entry/v1");
    assert!(matches!(refusal(v), ManifestError::ForgedIdentity(_)));
}

#[test]
fn test_manifest_reference_theory_with_legacy_entry_refused_as_forged() {
    let mut v = valid_value();
    v["identity"]["theory"] = json!({"reference": {"id": "lean-reference/v1", "digest": "00"}});
    assert!(matches!(refusal(v), ManifestError::ForgedIdentity(_)));
}

#[test]
fn test_manifest_reference_tier_refused_no_reference_producer() {
    let mut v = valid_value();
    v["identity"]["theory"] = json!({"reference": {"id": "lean-reference/v1", "digest": "00"}});
    v["identity"]["checker"]["entry"] = json!("clean-kernel/reference-entry/v1");
    v["identity"]["tier"] = json!("reference");
    assert_eq!(refusal(v), ManifestError::NoReferenceProducer);
}

#[test]
fn test_manifest_lean_reference_profile_claiming_reference_tier_refused() {
    let mut env = Environment::for_lean_replay();
    env.set_kernel_theory(KernelTheory::LeanReference);
    let m = sharded(
        &["a"],
        test_run_in(&env, BaseVariant::LeanReplay, Elision::None),
    );
    let mut v = serde_json::to_value(&m).expect("serialize");
    assert_eq!(
        v["identity"]["theory"]["profile"]["kernel_theory"],
        json!("LeanReference")
    );
    v["identity"]["tier"] = json!("reference");
    assert_eq!(
        refusal(v),
        ManifestError::TierMismatch {
            stored: "reference",
            derived: "development"
        }
    );
}

#[test]
fn test_manifest_unknown_entry_theory_or_field_refused() {
    let mut entry = valid_value();
    entry["identity"]["checker"]["entry"] = json!("clean-mathverse/new-entry/v9");
    assert!(matches!(refusal(entry), ManifestError::Malformed(_)));
    let mut theory = valid_value();
    theory["identity"]["theory"] = json!({"ccic": {"id": "x"}});
    assert!(matches!(refusal(theory), ManifestError::Malformed(_)));
    // A development file carrying a reference block beside its profile.
    let mut both = valid_value();
    both["identity"]["reference"] = json!({"id": "lean-reference/v1", "digest": "00"});
    assert!(matches!(refusal(both), ManifestError::Malformed(_)));
    // A hybrid schema-2 file with a leftover `kernel_verified_names`.
    let mut hybrid = valid_value();
    hybrid["kernel_verified_names"] = json!(["a", "b"]);
    assert!(matches!(refusal(hybrid), ManifestError::Malformed(_)));
}

#[test]
fn test_manifest_discipline_not_derived_from_profile_refused() {
    let mut v = valid_value();
    v["identity"]["checker"]["discipline"] = json!("coq-cumulative-incremental/1");
    assert!(matches!(
        refusal(v),
        ManifestError::DisciplineMismatch { stored, derived }
            if stored == "coq-cumulative-incremental/1"
                && derived == "lean-replay-order+lean-kernel-theory/1"
    ));
}

#[test]
fn test_manifest_count_or_duplicate_names_refused() {
    let mut count = valid_value();
    count["accepted"] = json!(3);
    assert!(matches!(
        refusal(count),
        ManifestError::CountMismatch { .. }
    ));
    let mut dup = valid_value();
    dup["accepted_names"] = json!(["a", "a"]);
    assert!(matches!(refusal(dup), ManifestError::CountMismatch { .. }));
}

#[test]
fn test_manifest_sharded_entry_with_replayed_imports_refused() {
    let mut v = valid_value();
    v["identity"]["checker"]["imports"] = json!("replayed");
    assert!(matches!(refusal(v), ManifestError::ForgedIdentity(_)));
}

#[test]
fn test_manifest_bad_digest_refused() {
    let mut v = valid_value();
    v["identity"]["checker"]["build"]["exe"]["sha256"] = json!("not-hex");
    assert!(matches!(refusal(v), ManifestError::Malformed(_)));
}

#[test]
fn test_manifest_legacy_identity_never_yields_reference_tier() {
    for theory in [
        KernelTheory::Extended,
        KernelTheory::Lean,
        KernelTheory::LeanReference,
    ] {
        let mut env = Environment::for_lean_replay();
        env.set_kernel_theory(theory);
        let run = || test_run_in(&env, BaseVariant::LeanReplay, Elision::None);
        let manifests = [
            sharded(&["a"], run()),
            KernelVerifiedManifest::merge("d", &[sharded(&["a"], run())]).expect("merge one"),
        ];
        for m in manifests {
            assert_eq!(m.tier(), AcceptanceTier::Development, "{theory:?}");
            assert_eq!(m.identity().validate(), Ok(AcceptanceTier::Development));
            assert_eq!(
                m.grant_refusal("a stamp"),
                ManifestError::DevelopmentTier { purpose: "a stamp" }
            );
        }
    }
}

#[test]
fn test_discipline_coq_cumulative_is_not_lean_replay() {
    // W4: the Coq lane checks with cumulative subtyping over Clean's import
    // prelude, so it can never claim Lean's replay discipline.
    let mut coq = Environment::try_with_prelude_for_import().expect("prelude");
    coq.set_cumulative(true);
    let m = sharded(
        &["a"],
        test_run_in(&coq, BaseVariant::ImportPrelude, Elision::None),
    );
    assert_eq!(m.identity().discipline(), Discipline::CoqCumulative);
    let extended = Environment::for_lean_replay();
    let m = sharded(
        &["a"],
        test_run_in(&extended, BaseVariant::LeanReplay, Elision::None),
    );
    assert_eq!(m.identity().discipline(), Discipline::ExtendedPrelude);
    assert_eq!(
        sharded(&["a"], test_run(Elision::None))
            .identity()
            .discipline(),
        Discipline::LeanReplay
    );
}

#[test]
fn test_merge_refuses_sidecar_from_another_build() {
    let a = sharded(&["a"], test_run(Elision::None));
    let mut other = test_run(Elision::None);
    let dir = tempfile::tempdir().expect("tmp");
    let fake = dir.path().join("other-binary");
    std::fs::write(&fake, b"another build").expect("write");
    other.build = BuildIdentity::with_executable(ExecutableIdentity::capture(&fake).expect("hash"));
    let b = sharded(&["b"], other);
    let err = KernelVerifiedManifest::merge("d", &[a.clone(), b]).expect_err("refused");
    assert!(
        matches!(&err, ManifestError::IdentityMismatch(m) if m.contains("checker.build")),
        "{err}"
    );
    let c = sharded(&["c"], test_run(Elision::Opaque));
    assert!(matches!(
        KernelVerifiedManifest::merge("d", &[a.clone(), c]),
        Err(ManifestError::IdentityMismatch(_))
    ));
    assert_eq!(
        KernelVerifiedManifest::merge("d", &[]),
        Err(ManifestError::EmptyMerge)
    );
    let merged = KernelVerifiedManifest::merge("d", &[a.clone(), a]).expect("uniform");
    assert_eq!(merged.accepted_names(), ["a"]);
}

#[test]
fn test_executable_identity_captured_before_first_verdict() {
    // The identity hashes the bytes at capture; a rebuild of the same path
    // afterwards does not change what the manifest names.
    let dir = tempfile::tempdir().expect("tmp");
    let exe = dir.path().join("clean");
    std::fs::write(&exe, b"build A").expect("write");
    let at_start = ExecutableIdentity::capture(&exe).expect("hash A");
    std::fs::write(&exe, b"build B, rebuilt mid-run").expect("rewrite");
    let later = ExecutableIdentity::capture(&exe).expect("hash B");
    assert_ne!(at_start.sha256(), later.sha256());
    let first = BuildIdentity::current().expect("current");
    assert_eq!(
        BuildIdentity::current().expect("current"),
        first,
        "captured once per process"
    );
}

#[test]
fn test_cache_key_differs_by_entry_and_executable() {
    let base = StampEnvFingerprint {
        checker_entry: CheckerEntry::ParallelReadonlyReplay.as_str().to_string(),
        exe_sha256: "a".repeat(64),
        ..StampEnvFingerprint::default()
    };
    let entry = StampEnvFingerprint {
        checker_entry: CheckerEntry::IncrementalReplay.as_str().to_string(),
        ..base.clone()
    };
    let exe = StampEnvFingerprint {
        exe_sha256: "b".repeat(64),
        ..base.clone()
    };
    assert_ne!(base.cache_key(), entry.cache_key());
    assert_ne!(base.cache_key(), exe.cache_key());
}

#[test]
fn test_regression_reference_schema1_read_only_inside_window() {
    let dir = tempfile::tempdir().expect("tmp");
    let path = dir.path().join("kernel-verified.json");
    std::fs::write(
        &path,
        json!({"schema_version": 1, "kernel_verified_names": ["x", "y"]}).to_string(),
    )
    .expect("write");
    let inside = RegressionReference::read(&path, SCHEMA1_MIGRATION_ENDS_UNIX - 1).expect("read");
    assert_eq!(inside.names(), ["x", "y"]);
    assert!(
        inside.identity().is_none(),
        "a schema-1 baseline has no identity"
    );
    let after = RegressionReference::read(&path, SCHEMA1_MIGRATION_ENDS_UNIX);
    assert!(matches!(
        after,
        Err(MathverseError::Manifest {
            source: ManifestError::UnsupportedSchema { .. },
            ..
        })
    ));
    // A schema-1 file is still refused by every other reader.
    assert!(KernelVerifiedManifest::from_file(&path).is_err());
}

#[test]
fn test_regression_reference_schema1_arm_removed_by_its_date() {
    // F14: the schema-1 migration arm has a dated removal condition. This
    // control fails once the date has passed, until the arm (and this test)
    // are deleted.
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock after the epoch")
        .as_secs();
    assert!(
        now < SCHEMA1_MIGRATION_ENDS_UNIX,
        "the schema-1 migration window of RegressionReference has closed: delete its \
         schema-1 arm, SCHEMA1_MIGRATION_ENDS_UNIX and this test"
    );
}
