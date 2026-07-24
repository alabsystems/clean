// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certification wrapper-free gate and reviewer assertions.

use super::*;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct CertificationWrapperFreeGate {
    pub(crate) status: &'static str,
    pub(crate) certifying_python_dependency_count: usize,
    pub(crate) wrapper_dependent_proof_surface_count: usize,
    pub(crate) wrapper_dependent_command_count: usize,
    pub(crate) launch_blocking_wrapper_dependent_command_count: usize,
    pub(crate) wrapper_dependency_blocker_ids: Vec<&'static str>,
    pub(crate) rust_reviewer_command: &'static str,
    pub(crate) rust_reviewer_json_pointer: &'static str,
    pub(crate) rust_reviewer_command_wrapper_free: bool,
    pub(crate) required_reviewer_assertions_schema_version: &'static str,
    pub(crate) required_reviewer_assertion_count: usize,
    pub(crate) required_reviewer_assertions: Vec<CertificationWrapperFreeReviewerAssertion>,
    pub(crate) required_reviewer_assertions_json_pointers_unique: bool,
    pub(crate) required_reviewer_assertions_json_pointers_parseable: bool,
    pub(crate) required_reviewer_assertions_json_pointers_dereferenceable: bool,
    pub(crate) required_reviewer_assertions_expected_json_parseable: bool,
    pub(crate) required_reviewer_assertions_cover_blocking_fields: bool,
    pub(crate) missing_required_reviewer_assertion_json_pointers: Vec<&'static str>,
    pub(crate) required_reviewer_assertions_match_live_values: bool,
    pub(crate) required_reviewer_assertions_live_value_mismatch_count: usize,
    pub(crate) mismatched_required_reviewer_assertion_json_pointers: Vec<&'static str>,
    pub(crate) reviewer_proof_completeness_status: &'static str,
    pub(crate) reviewer_proof_completeness_blocker_count: usize,
    pub(crate) reviewer_proof_completeness_blockers: Vec<&'static str>,
    pub(crate) reviewer_proof_completeness_required_json_pointer_count: usize,
    pub(crate) reviewer_proof_completeness_required_json_pointers: Vec<&'static str>,
    pub(crate) reviewer_proof_completeness_required_json_pointers_match_assertions: bool,
    pub(crate) reviewer_proof_completeness_required_json_pointers_fingerprint_algorithm:
        &'static str,
    pub(crate) reviewer_proof_completeness_required_json_pointers_fingerprint_sha256: String,
    pub(crate) reviewer_proof_completeness_fingerprint_algorithm: &'static str,
    pub(crate) reviewer_proof_completeness_fingerprint_sha256: String,
    pub(crate) required_reviewer_assertions_fingerprint_algorithm: &'static str,
    pub(crate) required_reviewer_assertions_fingerprint_sha256: String,
    pub(crate) fingerprint_algorithm: &'static str,
    pub(crate) fingerprint_sha256: String,
    pub(crate) reviewer_rule: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct CertificationWrapperFreeReviewerAssertion {
    pub(crate) json_pointer: &'static str,
    pub(crate) expected_json: &'static str,
}

pub(crate) const CERTIFICATION_WRAPPER_FREE_ASSERTIONS_SCHEMA_VERSION: &str =
    "clean-certification-wrapper-free-assertions-v1";
pub(crate) const CERTIFICATION_WRAPPER_FREE_ASSERTION_COUNT: usize = 7;

impl CertificationWrapperFreeGate {
    pub(crate) fn new(
        certification_python_dependency_ids: &[&'static str],
        proof_surface_audit: &ReplacementRowProofSurfaceAudit,
        command_deck: &ReviewerProofCommandDeck,
    ) -> Self {
        let wrapper_dependent_proof_surface_count = proof_surface_audit.wrapper_gate_row_count
            + proof_surface_audit.wrapper_evidence_artifact_row_count;
        let mut wrapper_dependency_blocker_ids = Vec::new();
        extend_unique(
            &mut wrapper_dependency_blocker_ids,
            certification_python_dependency_ids.iter().copied(),
        );
        extend_unique(
            &mut wrapper_dependency_blocker_ids,
            proof_surface_audit.wrapper_gate_row_ids.iter().copied(),
        );
        extend_unique(
            &mut wrapper_dependency_blocker_ids,
            proof_surface_audit
                .wrapper_evidence_artifact_row_ids
                .iter()
                .copied(),
        );
        extend_unique(
            &mut wrapper_dependency_blocker_ids,
            command_deck.wrapper_dependent_row_ids.iter().copied(),
        );
        extend_unique(
            &mut wrapper_dependency_blocker_ids,
            command_deck
                .launch_blocking_wrapper_dependent_row_ids
                .iter()
                .copied(),
        );
        let rust_reviewer_command = "clean replacement status --json";
        let rust_reviewer_command_wrapper_free = !is_wrapper_proof_surface(rust_reviewer_command);
        let required_reviewer_assertions = certification_wrapper_free_reviewer_assertions();
        let required_reviewer_assertions_json_pointers_unique =
            certification_wrapper_free_assertion_json_pointers_unique(
                &required_reviewer_assertions,
            );
        let required_reviewer_assertions_json_pointers_parseable =
            certification_wrapper_free_assertion_json_pointers_parseable(
                &required_reviewer_assertions,
            );
        let required_reviewer_assertions_expected_json_parseable =
            certification_wrapper_free_assertion_expected_json_parseable(
                &required_reviewer_assertions,
            );
        let required_reviewer_assertions_json_pointers_dereferenceable =
            certification_wrapper_free_assertion_json_pointers_dereferenceable(
                &required_reviewer_assertions,
                certification_python_dependency_ids.len(),
                wrapper_dependent_proof_surface_count,
                command_deck.wrapper_dependent_command_count,
                command_deck.launch_blocking_wrapper_dependent_command_count,
                &wrapper_dependency_blocker_ids,
                rust_reviewer_command_wrapper_free,
            );
        let missing_required_reviewer_assertion_json_pointers =
            missing_certification_wrapper_free_assertion_pointers(&required_reviewer_assertions);
        let required_reviewer_assertions_cover_blocking_fields =
            missing_required_reviewer_assertion_json_pointers.is_empty();
        let mismatched_required_reviewer_assertion_json_pointers =
            mismatched_certification_wrapper_free_assertion_pointers(
                &required_reviewer_assertions,
                certification_python_dependency_ids.len(),
                wrapper_dependent_proof_surface_count,
                command_deck.wrapper_dependent_command_count,
                command_deck.launch_blocking_wrapper_dependent_command_count,
                &wrapper_dependency_blocker_ids,
                rust_reviewer_command_wrapper_free,
            );
        let required_reviewer_assertions_match_live_values =
            mismatched_required_reviewer_assertion_json_pointers.is_empty();
        let required_reviewer_assertions_live_value_mismatch_count =
            mismatched_required_reviewer_assertion_json_pointers.len();
        let reviewer_proof_completeness_blockers =
            certification_wrapper_free_reviewer_proof_completeness_blockers(
                certification_python_dependency_ids.len(),
                wrapper_dependent_proof_surface_count,
                command_deck.wrapper_dependent_command_count,
                command_deck.launch_blocking_wrapper_dependent_command_count,
                &wrapper_dependency_blocker_ids,
                rust_reviewer_command_wrapper_free,
                required_reviewer_assertions.len(),
                required_reviewer_assertions_json_pointers_unique,
                required_reviewer_assertions_json_pointers_parseable,
                required_reviewer_assertions_json_pointers_dereferenceable,
                required_reviewer_assertions_expected_json_parseable,
                required_reviewer_assertions_cover_blocking_fields,
                required_reviewer_assertions_live_value_mismatch_count,
            );
        let reviewer_proof_completeness_status = if reviewer_proof_completeness_blockers.is_empty()
        {
            "complete"
        } else {
            "blocked"
        };
        let reviewer_proof_completeness_blocker_count = reviewer_proof_completeness_blockers.len();
        let reviewer_proof_completeness_required_json_pointers =
            certification_wrapper_free_required_assertion_pointers();
        let reviewer_proof_completeness_required_json_pointer_count =
            reviewer_proof_completeness_required_json_pointers.len();
        let reviewer_proof_completeness_required_json_pointers_match_assertions =
            certification_wrapper_free_required_json_pointers_match_assertions(
                &reviewer_proof_completeness_required_json_pointers,
                &required_reviewer_assertions,
            );
        let reviewer_proof_completeness_required_json_pointers_fingerprint_sha256 =
            certification_wrapper_free_required_json_pointers_fingerprint(
                &reviewer_proof_completeness_required_json_pointers,
            );
        let reviewer_proof_completeness_fingerprint_sha256 =
            certification_wrapper_free_reviewer_proof_completeness_fingerprint(
                reviewer_proof_completeness_status,
                reviewer_proof_completeness_blocker_count,
                reviewer_proof_completeness_required_json_pointer_count,
                &reviewer_proof_completeness_required_json_pointers_fingerprint_sha256,
                &reviewer_proof_completeness_required_json_pointers,
                &reviewer_proof_completeness_blockers,
            );
        let required_reviewer_assertions_fingerprint_sha256 =
            certification_wrapper_free_reviewer_assertions_fingerprint(
                &required_reviewer_assertions,
            );
        let status = if certification_python_dependency_ids.is_empty()
            && wrapper_dependent_proof_surface_count == 0
            && command_deck.wrapper_dependent_command_count == 0
            && command_deck.launch_blocking_wrapper_dependent_command_count == 0
            && wrapper_dependency_blocker_ids.is_empty()
            && rust_reviewer_command_wrapper_free
            && required_reviewer_assertions.len() == CERTIFICATION_WRAPPER_FREE_ASSERTION_COUNT
            && required_reviewer_assertions_json_pointers_unique
            && required_reviewer_assertions_json_pointers_parseable
            && required_reviewer_assertions_json_pointers_dereferenceable
            && required_reviewer_assertions_expected_json_parseable
            && required_reviewer_assertions_cover_blocking_fields
            && required_reviewer_assertions_match_live_values
            && required_reviewer_assertions_live_value_mismatch_count == 0
            && reviewer_proof_completeness_status == "complete"
            && reviewer_proof_completeness_blocker_count == 0
            && reviewer_proof_completeness_required_json_pointer_count
                == CERTIFICATION_WRAPPER_FREE_ASSERTION_COUNT
            && reviewer_proof_completeness_required_json_pointers_match_assertions
        {
            "passed"
        } else {
            "blocked"
        };
        let fingerprint_sha256 = certification_wrapper_free_gate_fingerprint(
            status,
            certification_python_dependency_ids.len(),
            wrapper_dependent_proof_surface_count,
            command_deck.wrapper_dependent_command_count,
            command_deck.launch_blocking_wrapper_dependent_command_count,
            &wrapper_dependency_blocker_ids,
            rust_reviewer_command,
            rust_reviewer_command_wrapper_free,
            &required_reviewer_assertions,
            required_reviewer_assertions_json_pointers_unique,
            required_reviewer_assertions_json_pointers_parseable,
            required_reviewer_assertions_json_pointers_dereferenceable,
            required_reviewer_assertions_expected_json_parseable,
            required_reviewer_assertions_cover_blocking_fields,
            &missing_required_reviewer_assertion_json_pointers,
            required_reviewer_assertions_match_live_values,
            required_reviewer_assertions_live_value_mismatch_count,
            &mismatched_required_reviewer_assertion_json_pointers,
            reviewer_proof_completeness_status,
            reviewer_proof_completeness_blocker_count,
            &reviewer_proof_completeness_fingerprint_sha256,
            reviewer_proof_completeness_required_json_pointer_count,
            reviewer_proof_completeness_required_json_pointers_match_assertions,
            &reviewer_proof_completeness_required_json_pointers_fingerprint_sha256,
            &reviewer_proof_completeness_required_json_pointers,
            &reviewer_proof_completeness_blockers,
        );

        Self {
            status,
            certifying_python_dependency_count: certification_python_dependency_ids.len(),
            wrapper_dependent_proof_surface_count,
            wrapper_dependent_command_count: command_deck.wrapper_dependent_command_count,
            launch_blocking_wrapper_dependent_command_count: command_deck
                .launch_blocking_wrapper_dependent_command_count,
            wrapper_dependency_blocker_ids,
            rust_reviewer_command,
            rust_reviewer_json_pointer:
                "/readiness_accounting/certification_wrapper_free_gate",
            rust_reviewer_command_wrapper_free,
            required_reviewer_assertions_schema_version:
                CERTIFICATION_WRAPPER_FREE_ASSERTIONS_SCHEMA_VERSION,
            required_reviewer_assertion_count: required_reviewer_assertions.len(),
            required_reviewer_assertions,
            required_reviewer_assertions_json_pointers_unique,
            required_reviewer_assertions_json_pointers_parseable,
            required_reviewer_assertions_json_pointers_dereferenceable,
            required_reviewer_assertions_expected_json_parseable,
            required_reviewer_assertions_cover_blocking_fields,
            missing_required_reviewer_assertion_json_pointers,
            required_reviewer_assertions_match_live_values,
            required_reviewer_assertions_live_value_mismatch_count,
            mismatched_required_reviewer_assertion_json_pointers,
            reviewer_proof_completeness_status,
            reviewer_proof_completeness_blocker_count,
            reviewer_proof_completeness_blockers,
            reviewer_proof_completeness_required_json_pointer_count,
            reviewer_proof_completeness_required_json_pointers,
            reviewer_proof_completeness_required_json_pointers_match_assertions,
            reviewer_proof_completeness_required_json_pointers_fingerprint_algorithm:
                "sha256(json_pointer || LF) for each reviewer_proof_completeness_required_json_pointers entry in emitted order",
            reviewer_proof_completeness_required_json_pointers_fingerprint_sha256,
            reviewer_proof_completeness_fingerprint_algorithm:
                "sha256(reviewer_proof_completeness_status || NUL || reviewer_proof_completeness_blocker_count || NUL || reviewer_proof_completeness_required_json_pointer_count || NUL || reviewer_proof_completeness_required_json_pointers_fingerprint_sha256 || NUL || reviewer_proof_completeness_required_json_pointers joined by NUL || reviewer_proof_completeness_blockers joined by NUL || LF)",
            reviewer_proof_completeness_fingerprint_sha256,
            required_reviewer_assertions_fingerprint_algorithm:
                "sha256(json_pointer || NUL || expected_json || LF) for each required_reviewer_assertions entry in emitted order",
            required_reviewer_assertions_fingerprint_sha256,
            fingerprint_algorithm:
                "sha256(status || NUL || certifying_python_dependency_count || NUL || wrapper_dependent_proof_surface_count || NUL || wrapper_dependent_command_count || NUL || launch_blocking_wrapper_dependent_command_count || NUL || wrapper_dependency_blocker_ids joined by NUL || rust_reviewer_command || NUL || rust_reviewer_command_wrapper_free_bit || NUL || required_reviewer_assertions(json_pointer, expected_json) || NUL || required_reviewer_assertions_json_pointers_unique_bit || NUL || required_reviewer_assertions_json_pointers_parseable_bit || NUL || required_reviewer_assertions_json_pointers_dereferenceable_bit || NUL || required_reviewer_assertions_expected_json_parseable_bit || NUL || required_reviewer_assertions_cover_blocking_fields_bit || NUL || missing_required_reviewer_assertion_json_pointers joined by NUL || required_reviewer_assertions_match_live_values_bit || NUL || required_reviewer_assertions_live_value_mismatch_count || NUL || mismatched_required_reviewer_assertion_json_pointers joined by NUL || reviewer_proof_completeness_status || NUL || reviewer_proof_completeness_blocker_count || NUL || reviewer_proof_completeness_fingerprint_sha256 || NUL || reviewer_proof_completeness_required_json_pointer_count || NUL || reviewer_proof_completeness_required_json_pointers_match_assertions_bit || NUL || reviewer_proof_completeness_required_json_pointers_fingerprint_sha256 || NUL || reviewer_proof_completeness_required_json_pointers joined by NUL || reviewer_proof_completeness_blockers joined by NUL || LF)",
            fingerprint_sha256,
            reviewer_rule:
                "External certification is wrapper-free only when certifying_python_dependency_count, wrapper_dependent_proof_surface_count, wrapper_dependent_command_count, and launch_blocking_wrapper_dependent_command_count are all zero.",
        }
    }
}

pub(crate) fn certification_wrapper_free_gate_fingerprint(
    status: &str,
    certifying_python_dependency_count: usize,
    wrapper_dependent_proof_surface_count: usize,
    wrapper_dependent_command_count: usize,
    launch_blocking_wrapper_dependent_command_count: usize,
    wrapper_dependency_blocker_ids: &[&str],
    rust_reviewer_command: &str,
    rust_reviewer_command_wrapper_free: bool,
    required_reviewer_assertions: &[CertificationWrapperFreeReviewerAssertion],
    required_reviewer_assertions_json_pointers_unique: bool,
    required_reviewer_assertions_json_pointers_parseable: bool,
    required_reviewer_assertions_json_pointers_dereferenceable: bool,
    required_reviewer_assertions_expected_json_parseable: bool,
    required_reviewer_assertions_cover_blocking_fields: bool,
    missing_required_reviewer_assertion_json_pointers: &[&str],
    required_reviewer_assertions_match_live_values: bool,
    required_reviewer_assertions_live_value_mismatch_count: usize,
    mismatched_required_reviewer_assertion_json_pointers: &[&str],
    reviewer_proof_completeness_status: &str,
    reviewer_proof_completeness_blocker_count: usize,
    reviewer_proof_completeness_fingerprint_sha256: &str,
    reviewer_proof_completeness_required_json_pointer_count: usize,
    reviewer_proof_completeness_required_json_pointers_match_assertions: bool,
    reviewer_proof_completeness_required_json_pointers_fingerprint_sha256: &str,
    reviewer_proof_completeness_required_json_pointers: &[&str],
    reviewer_proof_completeness_blockers: &[&str],
) -> String {
    let mut hasher = Sha256::new();
    hasher.update(status.as_bytes());
    hasher.update(b"\0");
    hasher.update(certifying_python_dependency_count.to_string().as_bytes());
    hasher.update(b"\0");
    hasher.update(wrapper_dependent_proof_surface_count.to_string().as_bytes());
    hasher.update(b"\0");
    hasher.update(wrapper_dependent_command_count.to_string().as_bytes());
    hasher.update(b"\0");
    hasher.update(
        launch_blocking_wrapper_dependent_command_count
            .to_string()
            .as_bytes(),
    );
    hasher.update(b"\0");
    for id in wrapper_dependency_blocker_ids {
        hasher.update(id.as_bytes());
        hasher.update(b"\0");
    }
    hasher.update(rust_reviewer_command.as_bytes());
    hasher.update(b"\0");
    hasher.update(if rust_reviewer_command_wrapper_free {
        b"1"
    } else {
        b"0"
    });
    hasher.update(b"\0");
    for assertion in required_reviewer_assertions {
        hasher.update(assertion.json_pointer.as_bytes());
        hasher.update(b"\0");
        hasher.update(assertion.expected_json.as_bytes());
        hasher.update(b"\0");
    }
    hasher.update(if required_reviewer_assertions_json_pointers_unique {
        b"1"
    } else {
        b"0"
    });
    hasher.update(b"\0");
    hasher.update(if required_reviewer_assertions_json_pointers_parseable {
        b"1"
    } else {
        b"0"
    });
    hasher.update(b"\0");
    hasher.update(
        if required_reviewer_assertions_json_pointers_dereferenceable {
            b"1"
        } else {
            b"0"
        },
    );
    hasher.update(b"\0");
    hasher.update(if required_reviewer_assertions_expected_json_parseable {
        b"1"
    } else {
        b"0"
    });
    hasher.update(b"\0");
    hasher.update(if required_reviewer_assertions_cover_blocking_fields {
        b"1"
    } else {
        b"0"
    });
    hasher.update(b"\0");
    for pointer in missing_required_reviewer_assertion_json_pointers {
        hasher.update(pointer.as_bytes());
        hasher.update(b"\0");
    }
    hasher.update(if required_reviewer_assertions_match_live_values {
        b"1"
    } else {
        b"0"
    });
    hasher.update(b"\0");
    hasher.update(
        required_reviewer_assertions_live_value_mismatch_count
            .to_string()
            .as_bytes(),
    );
    hasher.update(b"\0");
    for pointer in mismatched_required_reviewer_assertion_json_pointers {
        hasher.update(pointer.as_bytes());
        hasher.update(b"\0");
    }
    hasher.update(reviewer_proof_completeness_status.as_bytes());
    hasher.update(b"\0");
    hasher.update(
        reviewer_proof_completeness_blocker_count
            .to_string()
            .as_bytes(),
    );
    hasher.update(b"\0");
    hasher.update(reviewer_proof_completeness_fingerprint_sha256.as_bytes());
    hasher.update(b"\0");
    hasher.update(
        reviewer_proof_completeness_required_json_pointer_count
            .to_string()
            .as_bytes(),
    );
    hasher.update(b"\0");
    hasher.update(
        if reviewer_proof_completeness_required_json_pointers_match_assertions {
            b"1"
        } else {
            b"0"
        },
    );
    hasher.update(b"\0");
    hasher.update(reviewer_proof_completeness_required_json_pointers_fingerprint_sha256.as_bytes());
    hasher.update(b"\0");
    for pointer in reviewer_proof_completeness_required_json_pointers {
        hasher.update(pointer.as_bytes());
        hasher.update(b"\0");
    }
    for blocker in reviewer_proof_completeness_blockers {
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
