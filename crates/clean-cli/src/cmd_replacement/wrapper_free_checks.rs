// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Wrapper-free assertion pointer/JSON validation helpers.

use super::*;

pub(crate) fn certification_wrapper_free_reviewer_proof_completeness_fingerprint(
    status: &str,
    blocker_count: usize,
    required_json_pointer_count: usize,
    required_json_pointers_fingerprint_sha256: &str,
    required_json_pointers: &[&str],
    blockers: &[&str],
) -> String {
    let mut hasher = Sha256::new();
    hasher.update(status.as_bytes());
    hasher.update(b"\0");
    hasher.update(blocker_count.to_string().as_bytes());
    hasher.update(b"\0");
    hasher.update(required_json_pointer_count.to_string().as_bytes());
    hasher.update(b"\0");
    hasher.update(required_json_pointers_fingerprint_sha256.as_bytes());
    hasher.update(b"\0");
    for pointer in required_json_pointers {
        hasher.update(pointer.as_bytes());
        hasher.update(b"\0");
    }
    for blocker in blockers {
        hasher.update(blocker.as_bytes());
        hasher.update(b"\0");
    }
    hasher.update(b"\n");
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
}

pub(crate) fn certification_wrapper_free_required_json_pointers_fingerprint(
    pointers: &[&str],
) -> String {
    let mut hasher = Sha256::new();
    for pointer in pointers {
        hasher.update(pointer.as_bytes());
        hasher.update(b"\n");
    }
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
}

pub(crate) fn certification_wrapper_free_required_json_pointers_match_assertions(
    pointers: &[&str],
    assertions: &[CertificationWrapperFreeReviewerAssertion],
) -> bool {
    pointers.len() == assertions.len()
        && pointers
            .iter()
            .zip(assertions)
            .all(|(pointer, assertion)| *pointer == assertion.json_pointer)
}

pub(crate) fn certification_wrapper_free_assertion_json_pointers_unique(
    assertions: &[CertificationWrapperFreeReviewerAssertion],
) -> bool {
    assertions
        .iter()
        .map(|assertion| assertion.json_pointer)
        .collect::<BTreeSet<_>>()
        .len()
        == assertions.len()
}

pub(crate) fn certification_wrapper_free_assertion_json_pointers_parseable(
    assertions: &[CertificationWrapperFreeReviewerAssertion],
) -> bool {
    assertions
        .iter()
        .all(|assertion| json_pointer_is_absolute_and_parseable(assertion.json_pointer))
}

pub(crate) fn certification_wrapper_free_assertion_json_pointers_dereferenceable(
    assertions: &[CertificationWrapperFreeReviewerAssertion],
    certifying_python_dependency_count: usize,
    wrapper_dependent_proof_surface_count: usize,
    wrapper_dependent_command_count: usize,
    launch_blocking_wrapper_dependent_command_count: usize,
    wrapper_dependency_blocker_ids: &[&str],
    rust_reviewer_command_wrapper_free: bool,
) -> bool {
    assertions.iter().all(|assertion| {
        certification_wrapper_free_assertion_actual_json(
            assertion.json_pointer,
            certifying_python_dependency_count,
            wrapper_dependent_proof_surface_count,
            wrapper_dependent_command_count,
            launch_blocking_wrapper_dependent_command_count,
            wrapper_dependency_blocker_ids,
            rust_reviewer_command_wrapper_free,
        )
        .is_some()
    })
}

pub(crate) fn json_pointer_is_absolute_and_parseable(pointer: &str) -> bool {
    pointer.starts_with('/')
        && pointer
            .split('/')
            .skip(1)
            .all(json_pointer_token_has_valid_escapes)
}

pub(crate) fn json_pointer_token_has_valid_escapes(token: &str) -> bool {
    let mut chars = token.chars();
    while let Some(ch) = chars.next() {
        if ch == '~' && !matches!(chars.next(), Some('0' | '1')) {
            return false;
        }
    }
    true
}

pub(crate) fn certification_wrapper_free_assertion_expected_json_parseable(
    assertions: &[CertificationWrapperFreeReviewerAssertion],
) -> bool {
    assertions
        .iter()
        .all(|assertion| serde_json::from_str::<serde_json::Value>(assertion.expected_json).is_ok())
}

pub(crate) fn certification_wrapper_free_reviewer_proof_completeness_blockers(
    certifying_python_dependency_count: usize,
    wrapper_dependent_proof_surface_count: usize,
    wrapper_dependent_command_count: usize,
    launch_blocking_wrapper_dependent_command_count: usize,
    wrapper_dependency_blocker_ids: &[&str],
    rust_reviewer_command_wrapper_free: bool,
    required_reviewer_assertion_count: usize,
    required_reviewer_assertions_json_pointers_unique: bool,
    required_reviewer_assertions_json_pointers_parseable: bool,
    required_reviewer_assertions_json_pointers_dereferenceable: bool,
    required_reviewer_assertions_expected_json_parseable: bool,
    required_reviewer_assertions_cover_blocking_fields: bool,
    required_reviewer_assertions_live_value_mismatch_count: usize,
) -> Vec<&'static str> {
    let mut blockers = Vec::new();
    if certifying_python_dependency_count != 0 {
        blockers.push("certifying_python_dependency_count");
    }
    if wrapper_dependent_proof_surface_count != 0 {
        blockers.push("wrapper_dependent_proof_surface_count");
    }
    if wrapper_dependent_command_count != 0 {
        blockers.push("wrapper_dependent_command_count");
    }
    if launch_blocking_wrapper_dependent_command_count != 0 {
        blockers.push("launch_blocking_wrapper_dependent_command_count");
    }
    if !wrapper_dependency_blocker_ids.is_empty() {
        blockers.push("wrapper_dependency_blocker_ids");
    }
    if !rust_reviewer_command_wrapper_free {
        blockers.push("rust_reviewer_command_wrapper_free");
    }
    if required_reviewer_assertion_count != CERTIFICATION_WRAPPER_FREE_ASSERTION_COUNT {
        blockers.push("required_reviewer_assertion_count");
    }
    if !required_reviewer_assertions_json_pointers_unique {
        blockers.push("required_reviewer_assertions_json_pointers_unique");
    }
    if !required_reviewer_assertions_json_pointers_parseable {
        blockers.push("required_reviewer_assertions_json_pointers_parseable");
    }
    if !required_reviewer_assertions_json_pointers_dereferenceable {
        blockers.push("required_reviewer_assertions_json_pointers_dereferenceable");
    }
    if !required_reviewer_assertions_expected_json_parseable {
        blockers.push("required_reviewer_assertions_expected_json_parseable");
    }
    if !required_reviewer_assertions_cover_blocking_fields {
        blockers.push("required_reviewer_assertions_cover_blocking_fields");
    }
    if required_reviewer_assertions_live_value_mismatch_count != 0 {
        blockers.push("required_reviewer_assertions_live_value_mismatch_count");
    }
    blockers
}

pub(crate) fn certification_wrapper_free_reviewer_assertions_fingerprint(
    assertions: &[CertificationWrapperFreeReviewerAssertion],
) -> String {
    let mut hasher = Sha256::new();
    for assertion in assertions {
        hasher.update(assertion.json_pointer.as_bytes());
        hasher.update(b"\0");
        hasher.update(assertion.expected_json.as_bytes());
        hasher.update(b"\n");
    }
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
}

pub(crate) fn missing_certification_wrapper_free_assertion_pointers(
    assertions: &[CertificationWrapperFreeReviewerAssertion],
) -> Vec<&'static str> {
    certification_wrapper_free_required_assertion_pointers()
        .into_iter()
        .filter(|required| {
            !assertions
                .iter()
                .any(|assertion| assertion.json_pointer == *required)
        })
        .collect()
}

pub(crate) fn mismatched_certification_wrapper_free_assertion_pointers(
    assertions: &[CertificationWrapperFreeReviewerAssertion],
    certifying_python_dependency_count: usize,
    wrapper_dependent_proof_surface_count: usize,
    wrapper_dependent_command_count: usize,
    launch_blocking_wrapper_dependent_command_count: usize,
    wrapper_dependency_blocker_ids: &[&str],
    rust_reviewer_command_wrapper_free: bool,
) -> Vec<&'static str> {
    assertions
        .iter()
        .filter_map(|assertion| {
            certification_wrapper_free_assertion_actual_json(
                assertion.json_pointer,
                certifying_python_dependency_count,
                wrapper_dependent_proof_surface_count,
                wrapper_dependent_command_count,
                launch_blocking_wrapper_dependent_command_count,
                wrapper_dependency_blocker_ids,
                rust_reviewer_command_wrapper_free,
            )
            .filter(|actual| actual != assertion.expected_json)
            .map(|_| assertion.json_pointer)
        })
        .collect()
}

pub(crate) fn certification_wrapper_free_assertion_actual_json(
    pointer: &str,
    certifying_python_dependency_count: usize,
    wrapper_dependent_proof_surface_count: usize,
    wrapper_dependent_command_count: usize,
    launch_blocking_wrapper_dependent_command_count: usize,
    wrapper_dependency_blocker_ids: &[&str],
    rust_reviewer_command_wrapper_free: bool,
) -> Option<String> {
    match pointer {
        "/readiness_accounting/certification_wrapper_free_gate/status" => {
            Some("\"passed\"".to_owned())
        }
        "/readiness_accounting/certification_wrapper_free_gate/certifying_python_dependency_count" => {
            Some(certifying_python_dependency_count.to_string())
        }
        "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependent_proof_surface_count" => {
            Some(wrapper_dependent_proof_surface_count.to_string())
        }
        "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependent_command_count" => {
            Some(wrapper_dependent_command_count.to_string())
        }
        "/readiness_accounting/certification_wrapper_free_gate/launch_blocking_wrapper_dependent_command_count" => {
            Some(launch_blocking_wrapper_dependent_command_count.to_string())
        }
        "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependency_blocker_ids" => {
            serde_json::to_string(wrapper_dependency_blocker_ids).ok()
        }
        "/readiness_accounting/certification_wrapper_free_gate/rust_reviewer_command_wrapper_free" => {
            Some(rust_reviewer_command_wrapper_free.to_string())
        }
        _ => None,
    }
}

pub(crate) fn certification_wrapper_free_required_assertion_pointers() -> Vec<&'static str> {
    vec![
        "/readiness_accounting/certification_wrapper_free_gate/status",
        "/readiness_accounting/certification_wrapper_free_gate/certifying_python_dependency_count",
        "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependent_proof_surface_count",
        "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependent_command_count",
        "/readiness_accounting/certification_wrapper_free_gate/launch_blocking_wrapper_dependent_command_count",
        "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependency_blocker_ids",
        "/readiness_accounting/certification_wrapper_free_gate/rust_reviewer_command_wrapper_free",
    ]
}

pub(crate) fn certification_wrapper_free_reviewer_assertions(
) -> Vec<CertificationWrapperFreeReviewerAssertion> {
    vec![
        CertificationWrapperFreeReviewerAssertion {
            json_pointer: "/readiness_accounting/certification_wrapper_free_gate/status",
            expected_json: "\"passed\"",
        },
        CertificationWrapperFreeReviewerAssertion {
            json_pointer:
                "/readiness_accounting/certification_wrapper_free_gate/certifying_python_dependency_count",
            expected_json: "0",
        },
        CertificationWrapperFreeReviewerAssertion {
            json_pointer:
                "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependent_proof_surface_count",
            expected_json: "0",
        },
        CertificationWrapperFreeReviewerAssertion {
            json_pointer:
                "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependent_command_count",
            expected_json: "0",
        },
        CertificationWrapperFreeReviewerAssertion {
            json_pointer:
                "/readiness_accounting/certification_wrapper_free_gate/launch_blocking_wrapper_dependent_command_count",
            expected_json: "0",
        },
        CertificationWrapperFreeReviewerAssertion {
            json_pointer:
                "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependency_blocker_ids",
            expected_json: "[]",
        },
        CertificationWrapperFreeReviewerAssertion {
            json_pointer:
                "/readiness_accounting/certification_wrapper_free_gate/rust_reviewer_command_wrapper_free",
            expected_json: "true",
        },
    ]
}

pub(crate) fn extend_unique(
    ids: &mut Vec<&'static str>,
    new_ids: impl IntoIterator<Item = &'static str>,
) {
    for id in new_ids {
        if !ids.contains(&id) {
            ids.push(id);
        }
    }
}
