// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::Environment;
use clean_olean::{require_clean_payload_imports, ImportError, LoadSummary};

type Outcome = Option<Result<Vec<LoadSummary>, ImportError>>;

fn finish(
    env: &mut Environment,
    name: &Name,
    outcome: Outcome,
    policy: ImportPolicy,
    source: bool,
) -> Result<(), ElabError> {
    let satisfied = if source {
        [name.clone()].into_iter().collect()
    } else {
        HashSet::new()
    };
    finish_import_module(
        env,
        name,
        outcome,
        ImportResolution {
            policy,
            requires_artifact: false,
            satisfied_from_source: &satisfied,
        },
    )
}

fn exact_refusal(result: Result<(), ElabError>, name: &Name, expected: &str) {
    match result.expect_err("bootstrap must not substitute imported semantics") {
        ElabError::UnresolvedImport { module, reason } => {
            assert_eq!(module, name.to_string());
            assert_eq!(reason, expected, "preserve original loader diagnostic");
        }
        other => panic!("expected named hard import refusal, got {other:?}"),
    }
}

#[test]
fn clean_payload_requirement_frontend_rejects_actual_malformed_and_missing_artifacts() {
    for policy in [ImportPolicy::FailClosed, ImportPolicy::Permissive] {
        for module in ["Lean", "TotallyUnknown"] {
            for malformed in [false, true] {
                let dir = tempfile::tempdir().expect("isolated artifact directory");
                if malformed {
                    std::fs::write(dir.path().join(format!("{module}.olean")), b"invalid")
                        .expect("actual malformed replacement");
                }
                let mut env = Environment::default();
                require_clean_payload_imports(&mut env);
                let error = clean_olean::load_module_with_deps(
                    &mut env,
                    module,
                    &[dir.path().to_path_buf()],
                )
                .expect_err("actual file-backed loader refuses malformed/missing bytes");
                let reason = error.to_string();
                let name = Name::from_string(module);
                exact_refusal(
                    finish(&mut env, &name, Some(Err(error)), policy, false),
                    &name,
                    &reason,
                );
            }
        }
    }
}

#[test]
fn clean_payload_requirement_frontend_rejects_no_path_before_provider_or_permissive() {
    for policy in [ImportPolicy::FailClosed, ImportPolicy::Permissive] {
        for module in ["Lean", "TotallyUnknown"] {
            let mut env = Environment::default();
            require_clean_payload_imports(&mut env);
            let name = Name::from_string(module);
            let error = finish(&mut env, &name, None, policy, false)
                .expect_err("no search path cannot select a provider/permissive substitute");
            assert!(
                matches!(error, ElabError::UnresolvedImport { module, reason }
                if module == name.to_string() && reason.contains("no `.olean` search path"))
            );
        }
    }
}

#[test]
fn clean_payload_requirement_frontend_keeps_generic_source_satisfied_exception() {
    let name = Name::from_string("Project.Sibling");
    for policy in [ImportPolicy::FailClosed, ImportPolicy::Permissive] {
        let mut env = Environment::default();
        require_clean_payload_imports(&mut env);
        finish(&mut env, &name, None, policy, true)
            .expect("source elaborated in this run is a resolved import");
        let dir = tempfile::tempdir().expect("missing artifact");
        let missing = clean_olean::load_module_with_deps(
            &mut env,
            "Project.Sibling",
            &[dir.path().to_path_buf()],
        )
        .expect_err("no compiled artifact exists for source-only sibling");
        finish(&mut env, &name, Some(Err(missing)), policy, true)
            .expect("existing generic missing-artifact exception stays valid");
        let malformed: ImportError = clean_olean::OleanError::FileTooSmall {
            expected: 56,
            actual: 1,
        }
        .into();
        finish(&mut env, &name, Some(Err(malformed)), policy, true)
            .expect("existing generic parse-error exception stays valid for satisfied source");
    }
}

#[test]
fn clean_payload_requirement_frontend_keeps_hard_errors_even_for_satisfied_source() {
    let name = Name::from_string("Lean");
    for policy in [ImportPolicy::FailClosed, ImportPolicy::Permissive] {
        for error in [
            ImportError::UnsupportedModule {
                module: "Lean".into(),
                reason: "unsupported fixture refuses before provider".into(),
            },
            ImportError::CleanPayloadRequired {
                module: "Lean".into(),
            },
            ImportError::Interrupted,
            ImportError::ResourceLimit {
                operation: "fixture".into(),
                reason: "resource bound".into(),
            },
            ImportError::UnknownLeanWorld {
                world: "fixture".into(),
                reason: "unqualified world".into(),
            },
        ] {
            let mut env = Environment::default();
            require_clean_payload_imports(&mut env);
            let reason = error.to_string();
            exact_refusal(
                finish(&mut env, &name, Some(Err(error)), policy, true),
                &name,
                &reason,
            );
        }
    }
}

#[test]
fn clean_payload_requirement_frontend_leaves_unmarked_permissive_behavior_unchanged() {
    let mut env = Environment::default();
    let name = Name::from_string("TotallyUnknown");
    finish(&mut env, &name, None, ImportPolicy::Permissive, false)
        .expect("unmarked permissive route retains its existing behavior");
    assert!(!clean_olean::clean_payload_imports_required(&env));
}
