// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Distinguish a checked negative fixture from an interrupted check.

use crate::spec::SpecError;

// clean_elab::error_render::term emits this exact marker only when limiting
// diagnostic printing after the underlying type mismatch has been found.
// It is not evidence that elaboration or kernel checking exhausted a budget.
const OMITTED_DIAGNOSTIC_TERM: &str = "<term omitted: rendering budget exceeded>";

#[derive(Debug, PartialEq, Eq)]
enum RejectionIssue {
    NotTyping,
    NotTypeMismatch,
    CheckingResource(&'static str),
}

fn type_mismatch_rejection(error: &SpecError) -> Result<(), RejectionIssue> {
    let detail = match error {
        SpecError::ElabError(detail) | SpecError::TypeError(detail) => detail,
        _ => return Err(RejectionIssue::NotTyping),
    };
    if !detail.contains("Type mismatch: expected ") {
        return Err(RejectionIssue::NotTypeMismatch);
    }
    // Remove only the known printer marker, before normalizing case. Actual
    // resource failures alongside it, and unrecognized lookalikes, still fail.
    let checking_detail = detail
        .replace(OMITTED_DIAGNOSTIC_TERM, "")
        .to_ascii_lowercase();
    for resource in [
        "fuel",
        "budget",
        "heartbeat",
        "timeout",
        "recursion limit",
        "depth limit",
    ] {
        if checking_detail.contains(resource) {
            return Err(RejectionIssue::CheckingResource(resource));
        }
    }
    Ok(())
}

/// Require an actual type-mismatch rejection, not a checking resource failure.
///
/// `SpecError` retains these elaborator/kernel messages as strings. Keep the
/// existing conservative resource-word guard, excluding only the exact bounded
/// diagnostic-rendering marker. Definition non-registration and successful
/// recovery checks remain each fixture's responsibility.
pub(crate) fn assert_type_mismatch_rejection(error: &SpecError, context: &str) {
    assert_eq!(
        type_mismatch_rejection(error),
        Ok(()),
        "{context}: expected a checked type mismatch, not a resource or unrelated failure: {error}"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_mismatch_rejection_accepts_the_observed_bounded_diagnostic() {
        let detail = format!(
            "Failed to elaborate def (Invalid allocation-world claim): Type mismatch: \
             expected {OMITTED_DIAGNOSTIC_TERM}, got {OMITTED_DIAGNOSTIC_TERM}"
        );
        for error in [
            SpecError::ElabError(detail.clone()),
            SpecError::TypeError(detail),
        ] {
            assert_eq!(type_mismatch_rejection(&error), Ok(()));
        }
        assert_eq!(
            type_mismatch_rejection(&SpecError::TypeError(
                "Type mismatch: expected Nat, got Bool".into()
            )),
            Ok(())
        );
    }

    #[test]
    fn type_mismatch_rejection_keeps_every_checking_resource_guard() {
        for resource in [
            "fuel",
            "budget",
            "heartbeat",
            "timeout",
            "recursion limit",
            "depth limit",
        ] {
            for notice in ["", OMITTED_DIAGNOSTIC_TERM] {
                let error = SpecError::ElabError(format!(
                    "Type mismatch: expected {notice} Nat, got Bool; {} exhausted",
                    resource.to_ascii_uppercase()
                ));
                assert_eq!(
                    type_mismatch_rejection(&error),
                    Err(RejectionIssue::CheckingResource(resource)),
                    "{error}"
                );
            }
        }
    }

    #[test]
    fn type_mismatch_rejection_does_not_exempt_similar_rendering_messages() {
        for notice in [
            "<term omitted: rendering budget exhausted>",
            "<term omitted: Rendering budget exceeded>",
            "<term omitted: rendering budget exceeded >",
        ] {
            let error = SpecError::ElabError(format!("Type mismatch: expected {notice}, got Nat"));
            assert_eq!(
                type_mismatch_rejection(&error),
                Err(RejectionIssue::CheckingResource("budget"))
            );
        }
    }

    #[test]
    fn type_mismatch_rejection_requires_a_typing_error_and_mismatch() {
        for error in [
            SpecError::ParseError("Type mismatch: expected Nat, got Bool".into()),
            SpecError::EnvError("Type mismatch: expected Nat, got Bool".into()),
            SpecError::DeclarationBudgetExhausted {
                declaration: "Type mismatch: expected Nat, got Bool".into(),
                limit: 1,
            },
        ] {
            assert_eq!(
                type_mismatch_rejection(&error),
                Err(RejectionIssue::NotTyping)
            );
        }
        assert_eq!(
            type_mismatch_rejection(&SpecError::ElabError("Unknown constant: probe".into())),
            Err(RejectionIssue::NotTypeMismatch)
        );
        assert_eq!(
            type_mismatch_rejection(&SpecError::ElabError(
                "automation budget exhausted; Type mismatch: expected Nat, got Bool".into()
            )),
            Err(RejectionIssue::CheckingResource("budget"))
        );
    }
}
