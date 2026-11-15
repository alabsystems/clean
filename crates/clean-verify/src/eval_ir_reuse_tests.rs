// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    build_byte_prelude_spec_v1_with_stack, build_on_stack, shared_specification_with_stack,
    EvalIrVocabulary, VocabularyCell,
};
use crate::spec::{SpecError, Specification};
use clean_kernel::Name;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Barrier,
};

#[test]
fn vocabulary_concurrent_requests_initialize_once() {
    let cell = VocabularyCell::new();
    let barrier = Barrier::new(8);
    let builds = AtomicUsize::new(0);
    std::thread::scope(|scope| {
        let handles = (0..8)
            .map(|_| {
                scope.spawn(|| {
                    barrier.wait();
                    let spec = cell
                        .get_or_try_init(|| {
                            builds.fetch_add(1, Ordering::SeqCst);
                            build_on_stack(
                                "vocabulary-once-test",
                                "test",
                                Specification::new_eval_ir_spec,
                            )
                        })
                        .expect("one checked construction shared by concurrent callers");
                    spec as *const Specification as usize
                })
            })
            .collect::<Vec<_>>();
        let addresses = handles
            .into_iter()
            .map(|handle| handle.join().unwrap())
            .collect::<Vec<_>>();
        assert!(addresses.iter().all(|address| *address == addresses[0]));
    });
    assert_eq!(builds.load(Ordering::SeqCst), 1);
}

#[test]
fn vocabulary_failed_initialization_can_retry_without_changing_error() {
    let cell = VocabularyCell::new();
    let error = cell
        .get_or_try_init(|| {
            Err(SpecError::DeclarationBudgetExhausted {
                declaration: "test-exhausted-root".into(),
                limit: 17,
            })
        })
        .unwrap_err();
    assert!(
        matches!(error, SpecError::DeclarationBudgetExhausted { declaration, limit: 17 }
        if declaration == "test-exhausted-root")
    );
    assert!(cell.value.get().is_none());
    let first = cell
        .get_or_try_init(|| {
            build_on_stack(
                "vocabulary-retry-test",
                "test",
                Specification::new_eval_ir_spec,
            )
        })
        .expect("later successful construction");
    let second = cell
        .get_or_try_init(|| panic!("successful cache must not invoke builder again"))
        .expect("reuse successful construction");
    assert!(std::ptr::eq(first, second));
}

#[test]
fn vocabulary_worker_panic_does_not_poison_successful_retry() {
    let cell = VocabularyCell::new();
    let error = cell
        .get_or_try_init(|| {
            build_on_stack("vocabulary-panic-test", "test", || {
                panic!("intentional construction panic")
            })
        })
        .unwrap_err();
    assert!(
        matches!(error, SpecError::EnvError(message) if message == "test specification thread panicked")
    );
    assert!(cell.value.get().is_none());
    cell.get_or_try_init(|| {
        build_on_stack(
            "vocabulary-after-panic-test",
            "test",
            Specification::new_eval_ir_spec,
        )
    })
    .expect("worker panic leaves miss mutex usable");
}

#[test]
fn vocabulary_profiles_are_distinct_and_owned_extensions_are_isolated() {
    let mut shared_profiles: Vec<&Specification> = Vec::new();
    for profile in [
        EvalIrVocabulary::DependencyScoped,
        EvalIrVocabulary::Prelude,
        EvalIrVocabulary::ByteV1,
    ] {
        let first =
            shared_specification_with_stack(profile).expect("fixed constructor, no cache reentry");
        let second = shared_specification_with_stack(profile).expect("same fixed profile");
        assert!(std::ptr::eq(first, second));
        assert!(shared_profiles
            .iter()
            .all(|previous| !std::ptr::eq(*previous, first)));
        shared_profiles.push(first);
    }
    let shared = shared_profiles[2];
    let mut owned = build_byte_prelude_spec_v1_with_stack().unwrap();
    let sibling = build_byte_prelude_spec_v1_with_stack().unwrap();
    owned
        .env_mut()
        .set_option("maxHeartbeats".into(), Some("1".into()));
    owned
        .env_mut()
        .set_option("reuse-isolation".into(), Some("private".into()));
    assert_eq!(
        owned.env().get_option("maxHeartbeats"),
        Some(&Some("1".into()))
    );
    assert_ne!(
        shared.env().get_option("maxHeartbeats"),
        owned.env().get_option("maxHeartbeats")
    );
    // The tiny limit belongs only to this owned environment; restore it before
    // requesting a real extension so the test does not depend on its cost.
    owned.env_mut().set_option(
        "maxHeartbeats".into(),
        shared.env().get_option("maxHeartbeats").cloned().flatten(),
    );
    owned
        .add_recursive_def(
            "def byte_reuse_private_extension : Nat := 19",
            "clone isolation",
        )
        .expect("checked extension in owned copy");
    owned
        .definitions_mut()
        .remove("ir_byte_run_v1")
        .expect("independent spec map entry");
    for untouched in [shared, &sibling] {
        assert!(untouched.env().get_option("reuse-isolation").is_none());
        assert!(untouched
            .env()
            .get_const(&Name::from_string("byte_reuse_private_extension"))
            .is_none());
        assert!(untouched
            .get_definition("byte_reuse_private_extension")
            .is_none());
        assert!(untouched.get_definition("ir_byte_run_v1").is_some());
    }
    assert_eq!(
        sibling.env().get_option("maxHeartbeats"),
        shared.env().get_option("maxHeartbeats")
    );
    let term = clean_kernel::Expr::const_str("True.intro");
    assert!(shared
        .env()
        .audit_certification(&clean_kernel::Expr::const_str("True"), &term)
        .is_certified());
    assert!(!shared
        .env()
        .audit_certification(&clean_kernel::Expr::const_str("False"), &term)
        .is_certified());
}

#[test]
fn vocabulary_overrides_use_fresh_checked_path() {
    const PROBE: &str = "CLEAN_VOCABULARY_OVERRIDE_TEST";
    if let Ok(mode) = std::env::var(PROBE) {
        assert!(super::construction_override());
        assert!(shared_specification_with_stack(EvalIrVocabulary::DependencyScoped).is_err());
        let owned = super::build_spec_with_stack();
        let fresh = super::build_fresh(EvalIrVocabulary::DependencyScoped);
        if mode == "budget" {
            assert!(
                matches!(&owned, Err(SpecError::ParseError(message)) if message.contains("CLEAN_SPEC_DECL_BUDGET"))
            );
        }
        match (owned, fresh) {
            (Ok(owned), Ok(fresh)) => {
                assert_eq!(owned.definitions().len(), fresh.definitions().len())
            }
            (Err(owned), Err(fresh)) => assert_eq!(format!("{owned:?}"), format!("{fresh:?}")),
            other => panic!("owned override must preserve the actual fresh result: {other:?}"),
        }
        assert!(super::DEPENDENCY_SCOPED.value.get().is_none());
        return;
    }
    // Child-process environments avoid unsafe process-global set_var races
    // against concurrently registering tests in this test binary.
    for mode in ["budget", "strict"] {
        let mut command = std::process::Command::new(std::env::current_exe().unwrap());
        command
            .args([
                "eval_ir::reuse_tests::vocabulary_overrides_use_fresh_checked_path",
                "--exact",
                "--test-threads=1",
                "--nocapture",
            ])
            .env(PROBE, mode)
            .env_remove("CLEAN_SPEC_DECL_BUDGET")
            .env_remove("CLEAN_STRICT_PROOF_QUALITY");
        if mode == "budget" {
            command.env("CLEAN_SPEC_DECL_BUDGET", "not-a-budget");
        } else {
            command.env("CLEAN_STRICT_PROOF_QUALITY", "1");
        }
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{mode} child failed:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
