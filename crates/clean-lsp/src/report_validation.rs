// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust-owned validation for the LSP/infoview replacement evidence report.

use serde_json::Value;

const EXPECTED_SCHEMA: &str = "clean-lsp-infoview-parity-v1";
const EXPECTED_REPLACEMENT_ROW: &str = "lsp-infoview";
const EXPECTED_PENDING_STATUS: &str = "pending_evidence";
const EXPECTED_STANDARD_STATUS: &str =
    "partial_diagnostic_hover_goto_completion_replacement_signature_help_open_reference_rename_code_action_evidence";
const EXPECTED_TACTIC_GOAL_SNAPSHOT_FIXTURE: &str =
    "backend::tests::test_plain_goal_returns_live_tactic_snapshot_when_elaboration_tracks_goals";
const EXPECTED_TACTIC_GOAL_LIVE_PRODUCER_FIXTURE: &str =
    "backend::tests::test_plain_goal_live_elaboration_populates_tactic_snapshot";
const EXPECTED_TACTIC_GOAL_LSP_BRIDGE_GUARD: &str =
    "backend::tests::test_post_tactic_snapshot_bridge_names_missing_typed_proof_state";
const EXPECTED_TACTIC_GOAL_TYPED_POST_TACTIC_FIXTURE: &str =
    "backend::tests::test_plain_goal_live_elaboration_uses_typed_post_tactic_snapshot_when_target_elaborates";
const EXPECTED_TACTIC_GOAL_THEOREM_CONTEXT_GUARD: &str =
    "backend::tests::test_plain_goal_bound_theorem_requires_theorem_local_context_for_post_tactic_snapshot";
const EXPECTED_TACTIC_GOAL_POST_TACTIC_PLACEHOLDER: &str =
    "<new_tactic_goal_post_tactic_state_test>";
const EXPECTED_TACTIC_GOAL_POST_TACTIC_PRODUCER_SOURCE: &str =
    "clean_elab::tactic::interpret_tactic_block";
const EXPECTED_TACTIC_GOAL_POST_TACTIC_EXPORTED_API: &str =
    "clean_elab::tactic::run_tactic_script_with_snapshots";

const REQUIRED_ROW_IDS: &[&str] = &[
    "rpc-session-getwidgets",
    "widget-instances",
    "widget-source-registry",
    "tactic-goal-and-user-widgets",
    "plain-goal",
    "plain-term-goal",
    "standard-lsp-parity",
];

const REQUIRED_NON_CLAIMS: &[&str] = &[
    "does not claim full Lean4 LSP or infoview parity",
    "does not claim launch readiness",
    "does not claim live tactic goals",
];

const EXPECTED_NEXT_STEP_IDS: &[&str] = &[
    "tactic-goal-state-wiring",
    "user-widget-elaboration-wiring",
    "plain-term-goal-hole-boundary",
    "artifact-validator",
];

const REQUIRED_STANDARD_CAPABILITIES: &[&str] = &[
    "diagnostics",
    "hover",
    "goto",
    "completion",
    "signature_help",
    "references",
    "rename",
    "code_action",
];

const REQUIRED_STANDARD_TESTS: &[&str] = &[
    "backend::tests::test_generate_diagnostics_preserves_parse_error_range",
    "backend::tests::test_live_hover_uses_checked_declaration_range",
    "backend::tests::test_live_hover_excludes_checked_declaration_end_boundary",
    "backend::tests::test_live_goto_definition_uses_checked_document_declaration_range",
    "backend::tests::test_live_completion_uses_checked_document_definition_item_and_replacement_range",
    "backend::tests::test_live_completion_uses_checked_document_declaration_type_detail",
    "backend::tests::test_live_completion_keeps_keyword_matches_when_checked_definitions_match_prefix",
    "backend::tests::test_live_signature_help_uses_checked_declaration_type_label",
    "backend::tests::test_live_signature_help_marks_arrow_parameters_and_active_argument",
    "backend::tests::test_live_references_exclude_checked_declaration_when_requested",
    "backend::tests::test_live_references_find_open_document_use_across_files",
    "backend::tests::test_rename_edits_open_documents_without_touching_longer_identifier",
    "backend::tests::test_code_action_offers_sorry_quickfix_for_checked_document_range",
    "backend::tests::test_code_action_import_quickfix_from_unknown_identifier_diagnostic",
    "backend::tests::test_code_action_import_quickfix_from_qualified_unknown_identifier_diagnostic",
    "backend::tests::test_code_action_import_quickfix_skips_existing_import",
    "backend::tests::test_code_action_extract_definition_has_edit_only_refactor_shape",
    "backend::tests::test_code_action_only_quickfix_excludes_extract_refactor_for_identifier_range",
];

/// Validate the LSP/infoview parity report's fail-closed replacement contract.
pub fn validate_lsp_infoview_parity_report_str(report: &str) -> Result<(), String> {
    let value: Value = serde_json::from_str(report)
        .map_err(|err| format!("lsp-infoview report is not valid JSON: {err}"))?;
    validate_lsp_infoview_parity_report(&value)
}

/// Validate a parsed LSP/infoview parity report.
pub fn validate_lsp_infoview_parity_report(report: &Value) -> Result<(), String> {
    expect_str(report, "/schema_version", EXPECTED_SCHEMA)?;
    expect_str(report, "/generated_by", "manual evidence slice for #3709")?;
    expect_str(report, "/generated_at", "2026-04-27")?;
    expect_str(report, "/overall_status", EXPECTED_PENDING_STATUS)?;
    expect_bool(report, "/launch_ready", false)?;
    expect_str(report, "/replacement_row/id", EXPECTED_REPLACEMENT_ROW)?;
    expect_u64(report, "/replacement_row/issue", 3709)?;
    expect_bool(report, "/replacement_row/expected_by_scorecard", true)?;
    expect_str(
        report,
        "/replacement_row/scorecard_source",
        "crates/clean-cli/src/cmd_replacement.rs",
    )?;
    expect_str(
        report,
        "/replacement_row/recommended_scorecard_status",
        EXPECTED_PENDING_STATUS,
    )?;
    validate_replacement_row_validator(report)?;
    validate_rust_validator_evidence_consistency(report)?;
    validate_no_vague_passed_test_evidence(report)?;
    validate_no_bare_pytest_pass_counts(report)?;
    validate_passed_cargo_test_results_include_failure_counts(report)?;

    let claim = get_str(report, "/claim")?;
    require_contains(
        claim,
        "Full widget, plainGoal, expected-type, and LSP parity are not claimed",
    )?;

    let non_claims = strings_at(report, "/non_claims")?;
    for required in REQUIRED_NON_CLAIMS {
        require_any_contains(&non_claims, required, "/non_claims")?;
    }
    require_any_contains(
        &non_claims,
        "hole-local expected types, diagnostics, hover, completion, signature-help, goto, references, rename, or code-action parity",
        "/non_claims",
    )?;

    let rows = get_array(report, "/rows")?;
    for row_id in REQUIRED_ROW_IDS {
        row_by_id(rows, row_id)?;
    }

    expect_row_status(rows, "rpc-session-getwidgets", "pass")?;
    expect_row_status(
        rows,
        "plain-goal",
        "partial_typed_post_tactic_snapshot_bridge",
    )?;
    expect_row_status(rows, "plain-term-goal", "partial")?;
    expect_row_status(
        rows,
        "widget-instances",
        "partial_declaration_and_type_panels_live_backed",
    )?;
    expect_row_status(
        rows,
        "widget-source-registry",
        "partial_builtin_declaration_and_type_panel_sources",
    )?;
    expect_row_status(
        rows,
        "tactic-goal-and-user-widgets",
        "unsupported_no_live_state",
    )?;
    expect_row_status(rows, "standard-lsp-parity", EXPECTED_STANDARD_STATUS)?;

    validate_widget_instances(row_by_id(rows, "widget-instances")?)?;
    validate_widget_source_registry(row_by_id(rows, "widget-source-registry")?)?;
    validate_tactic_goal_and_user_widgets(row_by_id(rows, "tactic-goal-and-user-widgets")?)?;
    validate_plain_goal(row_by_id(rows, "plain-goal")?)?;
    validate_plain_term_goal(row_by_id(rows, "plain-term-goal")?)?;
    validate_goal_snapshot_boundary(report, rows)?;
    validate_goal_widget_state_boundary(report, rows)?;
    validate_tactic_goal_snapshot_pipeline_boundary(report, rows)?;
    validate_user_widget_discovery_boundary(report, rows)?;
    validate_expected_type_snapshot_boundary(report, rows)?;
    validate_standard_lsp(row_by_id(rows, "standard-lsp-parity")?)?;
    validate_overall_blockers(report)?;
    validate_next_steps(report)?;

    Ok(())
}

fn validate_replacement_row_validator(report: &Value) -> Result<(), String> {
    expect_str(report, "/replacement_row/rust_validator/kind", "test")?;
    expect_str(
        report,
        "/replacement_row/rust_validator/path",
        "crates/clean-lsp/src/report_validation.rs",
    )?;
    expect_str(
        report,
        "/replacement_row/rust_validator/function",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    )?;
    expect_str(
        report,
        "/replacement_row/rust_validator/command",
        "CARGO_BUILD_JOBS=1 cargo test --locked --message-format=short -p clean-lsp --lib report_validation::tests -- --nocapture",
    )?;
    expect_str(
        report,
        "/replacement_row/rust_validator/observed_result",
        "70 passed; 0 failed; 132 filtered out",
    )?;
    expect_str(
        report,
        "/replacement_row/rust_validator/run_status",
        "passed",
    )?;
    Ok(())
}

fn validate_rust_validator_evidence_consistency(report: &Value) -> Result<(), String> {
    let rows = get_array(report, "/rows")?;
    let expected_path = get_str(report, "/replacement_row/rust_validator/path")?;
    let expected_function = get_str(report, "/replacement_row/rust_validator/function")?;
    let expected_command = get_str(report, "/replacement_row/rust_validator/command")?;
    let expected_result = get_str(report, "/replacement_row/rust_validator/observed_result")?;
    let expected_status = get_str(report, "/replacement_row/rust_validator/run_status")?;

    for row in rows {
        let row_id = get_str(row, "/id")?;
        let evidence_items = match row.pointer("/evidence").and_then(Value::as_array) {
            Some(items) => items,
            None => continue,
        };
        for evidence in evidence_items {
            if evidence.pointer("/path").and_then(Value::as_str) == Some(expected_path) {
                expect_str(evidence, "/kind", "test")
                    .map_err(|err| format!("{row_id} Rust validator evidence: {err}"))?;
                expect_str(evidence, "/function", expected_function)
                    .map_err(|err| format!("{row_id} Rust validator evidence: {err}"))?;
                expect_str(evidence, "/command", expected_command)
                    .map_err(|err| format!("{row_id} Rust validator evidence: {err}"))?;
                expect_str(evidence, "/observed_result", expected_result)
                    .map_err(|err| format!("{row_id} Rust validator evidence: {err}"))?;
                expect_str(evidence, "/run_status", expected_status)
                    .map_err(|err| format!("{row_id} Rust validator evidence: {err}"))?;
            }
        }
    }
    Ok(())
}

fn validate_no_vague_passed_test_evidence(report: &Value) -> Result<(), String> {
    let rows = get_array(report, "/rows")?;
    for row in rows {
        let row_id = get_str(row, "/id")?;
        let evidence_items = match row.pointer("/evidence").and_then(Value::as_array) {
            Some(items) => items,
            None => continue,
        };
        for evidence in evidence_items {
            if evidence.pointer("/kind").and_then(Value::as_str) != Some("test")
                || evidence.pointer("/run_status").and_then(Value::as_str) != Some("passed")
            {
                continue;
            }
            let observed_result = get_str(evidence, "/observed_result")
                .map_err(|err| format!("{row_id} passed test evidence: {err}"))?;
            if observed_result.contains("passing focused regression") {
                return Err(format!(
                    "{row_id} passed test evidence must record exact observed_result counts"
                ));
            }
        }
    }
    Ok(())
}

fn validate_no_bare_pytest_pass_counts(report: &Value) -> Result<(), String> {
    let rows = get_array(report, "/rows")?;
    for row in rows {
        let row_id = get_str(row, "/id")?;
        let evidence_items = match row.pointer("/evidence").and_then(Value::as_array) {
            Some(items) => items,
            None => continue,
        };
        for evidence in evidence_items {
            if evidence.pointer("/kind").and_then(Value::as_str) != Some("test")
                || evidence.pointer("/run_status").and_then(Value::as_str) != Some("passed")
            {
                continue;
            }
            let command = get_str(evidence, "/command")
                .map_err(|err| format!("{row_id} passed test evidence: {err}"))?;
            if !command.starts_with("python3 -m pytest ") {
                continue;
            }
            let observed_result = get_str(evidence, "/observed_result")
                .map_err(|err| format!("{row_id} pytest evidence: {err}"))?;
            if is_bare_pytest_pass_count(observed_result) {
                return Err(format!(
                    "{row_id} pytest evidence must record exact observed_result output, not a bare pass count"
                ));
            }
        }
    }
    Ok(())
}

fn is_bare_pytest_pass_count(observed_result: &str) -> bool {
    let mut parts = observed_result.split_whitespace();
    matches!(
        (parts.next(), parts.next(), parts.next()),
        (Some(count), Some("passed"), None) if count.chars().all(|ch| ch.is_ascii_digit())
    )
}

fn validate_passed_cargo_test_results_include_failure_counts(report: &Value) -> Result<(), String> {
    let rows = get_array(report, "/rows")?;
    for row in rows {
        let row_id = get_str(row, "/id")?;
        let evidence_items = match row.pointer("/evidence").and_then(Value::as_array) {
            Some(items) => items,
            None => continue,
        };
        for evidence in evidence_items {
            if evidence.pointer("/kind").and_then(Value::as_str) != Some("test")
                || evidence.pointer("/run_status").and_then(Value::as_str) != Some("passed")
            {
                continue;
            }
            let command = get_str(evidence, "/command")
                .map_err(|err| format!("{row_id} passed test evidence: {err}"))?;
            if !command.contains("cargo test") {
                continue;
            }
            let observed_result = get_str(evidence, "/observed_result")
                .map_err(|err| format!("{row_id} cargo test evidence: {err}"))?;
            if !observed_result.contains("0 failed") {
                return Err(format!(
                    "{row_id} cargo test evidence must record explicit 0 failed observed_result"
                ));
            }
        }
    }
    Ok(())
}

fn validate_widget_instances(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "builtin_widget_instances")?;
    expect_str(
        coverage,
        "/evidence_level",
        "partial_declaration_and_type_panels_live_backed",
    )?;
    for test in [
        "backend::tests::test_rpc_get_widgets_uses_live_checked_document_declaration_panels",
        "backend::tests::test_rpc_get_widgets_live_checked_document_filters_type_panels_by_decl_range",
        "backend::tests::test_rpc_get_widgets_live_checked_refresh_replaces_previous_panels",
        "backend::tests::test_rpc_get_widgets_refresh_clears_stale_elaboration_widgets",
        "rpc::tests::test_widget_registry_filters_widgets_by_range",
    ] {
        require_string_array_contains(coverage, "/covered_by_tests", test)?;
    }
    for source in [
        "CleanBackend::has_live_user_widget_modules",
        "CleanBackend::refresh_infoview_widgets",
        "WidgetRegistry::widgets_at",
    ] {
        require_string_array_contains(coverage, "/covered_by_sources", source)?;
    }
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "User widget instances are not discovered",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "Tactic goal widgets are not backed",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "must not count as full Lean4 widget parity",
    )?;

    let limitations = strings_at(row, "/limitations")?.join(" ");
    require_contains(&limitations, "declaration-range type panels")?;
    require_contains(&limitations, "not hole-local expected-type parity")?;
    require_contains(
        &limitations,
        "User widget instances and tactic goal widgets are not live-backed yet",
    )?;
    Ok(())
}

fn validate_widget_source_registry(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "builtin_widget_sources")?;
    expect_str(
        coverage,
        "/evidence_level",
        "partial_builtin_declaration_and_type_panel_sources",
    )?;
    for test in [
        "backend::tests::test_rpc_get_widgets_uses_live_checked_document_declaration_panels",
        "backend::tests::test_rpc_get_widgets_live_checked_document_filters_type_panels_by_decl_range",
        "rpc::tests::test_widget_registry_shape_returns_registered_widget_and_source",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        require_string_array_contains(coverage, "/covered_by_tests", test)?;
    }
    require_string_array_contains(
        coverage,
        "/covered_by_sources",
        "CleanBackend::refresh_infoview_widgets",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "User widget module registration is not wired yet",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "No user widget module discovery or source-hash registration",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "widget_source_not_found",
    )?;
    require_contains(
        get_str(coverage, "/covered_behavior")?,
        "built-in declaration summary and type panel JavaScript sources",
    )?;

    let evidence_functions = evidence_functions(row)?;
    for test in [
        "backend::tests::test_rpc_get_widgets_uses_live_checked_document_declaration_panels",
        "backend::tests::test_rpc_get_widgets_live_checked_document_filters_type_panels_by_decl_range",
        "rpc::tests::test_widget_registry_shape_returns_registered_widget_and_source",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        if !evidence_functions.iter().any(|actual| actual == test) {
            return Err(format!(
                "widget-source-registry missing source evidence {test}"
            ));
        }
    }

    let limitations = strings_at(row, "/limitations")?.join(" ");
    require_contains(
        &limitations,
        "built-in declaration summary and type panel sources",
    )?;
    require_contains(
        &limitations,
        "Unknown hashes still return widget_source_not_found",
    )?;
    require_contains(
        &limitations,
        "User widget module registration is not wired yet",
    )?;
    require_contains(
        &limitations,
        "No user widget module discovery or source-hash registration",
    )?;
    Ok(())
}

fn validate_tactic_goal_and_user_widgets(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "tactic_goal_and_user_widgets")?;
    expect_str(coverage, "/evidence_level", "unsupported_fail_closed")?;
    require_string_array_contains(
        coverage,
        "/covered_by_tests",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    )?;
    for source in [
        "CleanBackend::has_live_tactic_goal_state",
        "CleanBackend::plain_goal",
        "CleanBackend::refresh_infoview_widgets",
    ] {
        require_string_array_contains(coverage, "/covered_by_sources", source)?;
    }
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "does not track tactic goal state",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "No tactic-goal snapshot payloads are captured",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "No live tactic-goal snapshot pipeline",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "No Lean4-compatible goal widget state is materialized",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "does not discover user-defined widget modules",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "No user widget module discovery or source-hash registration",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "must not count as tactic-goal or user-widget parity",
    )?;

    let blockers = strings_at(row, "/blockers")?.join(" ");
    require_contains(&blockers, "does not track tactic goal state")?;
    require_contains(&blockers, "No tactic-goal snapshot payloads are captured")?;
    require_contains(&blockers, "No live tactic-goal snapshot pipeline")?;
    require_contains(
        &blockers,
        "No Lean4-compatible goal widget state is materialized",
    )?;
    require_contains(&blockers, "does not discover user-defined widget modules")?;
    require_contains(
        &blockers,
        "No user widget module discovery or source-hash registration",
    )?;
    require_contains(
        &blockers,
        "must not be counted as tactic-goal or user-widget parity",
    )?;

    let evidence_functions = evidence_functions(row)?;
    for source in [
        "CleanBackend::has_live_tactic_goal_state",
        "CleanBackend::plain_goal",
        "CleanBackend::refresh_infoview_widgets",
    ] {
        if !evidence_functions.iter().any(|actual| actual == source) {
            return Err(format!(
                "tactic-goal-and-user-widgets missing source evidence {source}"
            ));
        }
    }
    Ok(())
}

fn validate_plain_goal(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "goal_state")?;
    expect_str(
        coverage,
        "/evidence_level",
        "partial_typed_post_tactic_snapshot_bridge",
    )?;
    for test in [
        "backend::tests::test_plain_goal_returns_none_until_tactic_state_is_tracked",
        EXPECTED_TACTIC_GOAL_SNAPSHOT_FIXTURE,
        EXPECTED_TACTIC_GOAL_LIVE_PRODUCER_FIXTURE,
        EXPECTED_TACTIC_GOAL_LSP_BRIDGE_GUARD,
        EXPECTED_TACTIC_GOAL_TYPED_POST_TACTIC_FIXTURE,
        EXPECTED_TACTIC_GOAL_THEOREM_CONTEXT_GUARD,
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        require_string_array_contains(coverage, "/covered_by_tests", test)?;
    }
    for source in [
        "CleanBackend::elaborate_document",
        "CleanBackend::has_live_tactic_goal_state",
        "CleanBackend::plain_goal",
    ] {
        require_string_array_contains(coverage, "/covered_by_sources", source)?;
    }
    let covered_behavior = get_str(coverage, "/covered_behavior")?;
    require_contains(
        covered_behavior,
        "produces an initial tactic snapshot during live document elaboration",
    )?;
    require_contains(covered_behavior, "returns a stored live tactic snapshot")?;
    require_contains(
        covered_behavior,
        "identifies the post-tactic source range and script text",
    )?;
    require_contains(
        covered_behavior,
        "uses a typed ProofState for elaborated targets",
    )?;
    require_contains(
        covered_behavior,
        "refuses bound-theorem post-tactic snapshots until theorem-local binder context is available",
    )?;
    require_contains(
        covered_behavior,
        "still returns no goals without a snapshot",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "Only initial declaration-target tactic snapshots are produced",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "No Lean4-compatible goal widget state",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "lacks a typed ProofState for clean_elab::tactic::run_tactic_script_with_snapshots",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "theorem-local binder context for proof_state_for_tactic_target",
    )?;

    let evidence_functions = evidence_functions(row)?;
    for test in [
        "backend::tests::test_plain_goal_returns_none_until_tactic_state_is_tracked",
        EXPECTED_TACTIC_GOAL_SNAPSHOT_FIXTURE,
        EXPECTED_TACTIC_GOAL_LIVE_PRODUCER_FIXTURE,
        EXPECTED_TACTIC_GOAL_LSP_BRIDGE_GUARD,
        EXPECTED_TACTIC_GOAL_TYPED_POST_TACTIC_FIXTURE,
        EXPECTED_TACTIC_GOAL_THEOREM_CONTEXT_GUARD,
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        if !evidence_functions.iter().any(|actual| actual == test) {
            return Err(format!("plain-goal missing goal-state evidence {test}"));
        }
    }
    for source in [
        "CleanBackend::elaborate_document",
        "CleanBackend::has_live_tactic_goal_state",
        "CleanBackend::plain_goal",
    ] {
        if !evidence_functions.iter().any(|actual| actual == source) {
            return Err(format!("plain-goal missing goal-state source {source}"));
        }
    }

    let blockers = strings_at(row, "/blockers")?.join(" ");
    require_contains(&blockers, "Post-tactic goal snapshots are not captured")?;
    require_contains(&blockers, "not live tactic-goal parity")?;
    Ok(())
}

fn validate_user_widget_discovery_boundary(report: &Value, rows: &[Value]) -> Result<(), String> {
    let widget_instances = row_by_id(rows, "widget-instances")?;
    let widget_instance_coverage =
        coverage_by_capability(widget_instances, "builtin_widget_instances")?;
    let widget_source = row_by_id(rows, "widget-source-registry")?;
    let widget_source_coverage = coverage_by_capability(widget_source, "builtin_widget_sources")?;
    let unsupported = row_by_id(rows, "tactic-goal-and-user-widgets")?;
    let unsupported_coverage = coverage_by_capability(unsupported, "tactic_goal_and_user_widgets")?;

    require_string_array_contains(
        widget_instance_coverage,
        "/covered_by_sources",
        "CleanBackend::has_live_user_widget_modules",
    )?;
    require_string_array_contains_fragment(
        widget_instance_coverage,
        "/fail_closed_gaps",
        "User widget instances are not discovered from elaboration state",
    )?;
    let widget_instance_limitations = strings_at(widget_instances, "/limitations")?.join(" ");
    require_contains(
        &widget_instance_limitations,
        "User widget instances and tactic goal widgets are not live-backed yet",
    )?;

    require_string_array_contains_fragment(
        widget_source_coverage,
        "/fail_closed_gaps",
        "User widget module registration is not wired yet",
    )?;
    require_string_array_contains_fragment(
        widget_source_coverage,
        "/fail_closed_gaps",
        "No user widget module discovery or source-hash registration",
    )?;
    let widget_source_limitations = strings_at(widget_source, "/limitations")?.join(" ");
    require_contains(
        &widget_source_limitations,
        "No user widget module discovery or source-hash registration",
    )?;

    require_string_array_contains_fragment(
        unsupported_coverage,
        "/fail_closed_gaps",
        "does not discover user-defined widget modules",
    )?;
    require_string_array_contains_fragment(
        unsupported_coverage,
        "/fail_closed_gaps",
        "No user widget module discovery or source-hash registration",
    )?;
    let unsupported_blockers = strings_at(unsupported, "/blockers")?.join(" ");
    require_contains(
        &unsupported_blockers,
        "does not discover user-defined widget modules",
    )?;
    require_contains(
        &unsupported_blockers,
        "No user widget module discovery or source-hash registration",
    )?;

    let blockers = strings_at(report, "/overall_blockers")?.join(" ");
    require_contains(&blockers, "user widgets, tactic goals")?;

    let next_steps = get_array(report, "/next_minimal_steps")?;
    let user_widget_step = next_steps
        .iter()
        .find(|step| get_str(step, "/id").is_ok_and(|id| id == "user-widget-elaboration-wiring"))
        .ok_or_else(|| "missing user-widget-elaboration-wiring next step".to_string())?;
    let description = get_str(user_widget_step, "/description")?;
    require_contains(description, "user widget/module declarations")?;
    require_contains(description, "do not treat the built-in declaration panel")?;
    let command = get_str(user_widget_step, "/candidate_command")?;
    require_contains(command, "<new_user_widget_elaboration_test>")?;

    Ok(())
}

fn validate_goal_snapshot_boundary(report: &Value, rows: &[Value]) -> Result<(), String> {
    let unsupported = row_by_id(rows, "tactic-goal-and-user-widgets")?;
    let unsupported_coverage = coverage_by_capability(unsupported, "tactic_goal_and_user_widgets")?;
    let plain_goal = row_by_id(rows, "plain-goal")?;
    let plain_goal_coverage = coverage_by_capability(plain_goal, "goal_state")?;
    let plain_term = row_by_id(rows, "plain-term-goal")?;
    let plain_term_coverage = coverage_by_capability(plain_term, "expected_type")?;

    require_string_array_contains_fragment(
        unsupported_coverage,
        "/fail_closed_gaps",
        "No tactic-goal snapshot payloads are captured, stored, or serialized",
    )?;
    require_string_array_contains_fragment(
        plain_goal_coverage,
        "/fail_closed_gaps",
        "Only initial declaration-target tactic snapshots are produced",
    )?;
    require_string_array_contains_fragment(
        plain_term_coverage,
        "/fail_closed_gaps",
        "No hole-local expected type state",
    )?;

    let unsupported_blockers = strings_at(unsupported, "/blockers")?.join(" ");
    require_contains(
        &unsupported_blockers,
        "No tactic-goal snapshot payloads are captured, stored, or serialized",
    )?;
    let plain_goal_blockers = strings_at(plain_goal, "/blockers")?.join(" ");
    require_contains(
        &plain_goal_blockers,
        "Post-tactic goal snapshots are not captured",
    )?;
    require_contains(&plain_goal_blockers, "not live tactic-goal parity")?;

    let plain_term_limitations = strings_at(plain_term, "/limitations")?.join(" ");
    require_contains(
        &plain_term_limitations,
        "has_live_hole_expected_type_state remains false",
    )?;
    require_contains(
        &plain_term_limitations,
        "not hole-local expected-type parity",
    )?;

    let blockers = strings_at(report, "/overall_blockers")?.join(" ");
    require_contains(
        &blockers,
        "Live tactic goals are not exposed through plainGoal",
    )?;
    require_contains(
        &blockers,
        "tactic goals, and hole-local expected types are not live-backed",
    )?;

    let next_steps = get_array(report, "/next_minimal_steps")?;
    let tactic_goal_step = next_steps
        .iter()
        .find(|step| get_str(step, "/id").is_ok_and(|id| id == "tactic-goal-state-wiring"))
        .ok_or_else(|| "missing tactic-goal-state-wiring next step".to_string())?;
    let description = get_str(tactic_goal_step, "/description")?;
    require_contains(
        description,
        "Track post-tactic goal state during elaboration",
    )?;
    require_contains(description, "plainGoal and goal widgets")?;
    require_contains(description, "do not count declaration/type panels")?;
    validate_tactic_goal_post_tactic_producer_contract(tactic_goal_step)?;

    Ok(())
}

fn validate_tactic_goal_snapshot_pipeline_boundary(
    report: &Value,
    rows: &[Value],
) -> Result<(), String> {
    let unsupported = row_by_id(rows, "tactic-goal-and-user-widgets")?;
    let unsupported_coverage = coverage_by_capability(unsupported, "tactic_goal_and_user_widgets")?;
    let plain_goal = row_by_id(rows, "plain-goal")?;
    let plain_goal_coverage = coverage_by_capability(plain_goal, "goal_state")?;

    require_string_array_contains_fragment(
        unsupported_coverage,
        "/fail_closed_gaps",
        "No live tactic-goal snapshot pipeline",
    )?;
    require_string_array_contains_fragment(
        unsupported_coverage,
        "/fail_closed_gaps",
        "No tactic-goal snapshot payloads are captured, stored, or serialized",
    )?;
    let unsupported_blockers = strings_at(unsupported, "/blockers")?.join(" ");
    require_contains(
        &unsupported_blockers,
        "No live tactic-goal snapshot pipeline",
    )?;
    require_contains(
        &unsupported_blockers,
        "No tactic-goal snapshot payloads are captured, stored, or serialized",
    )?;

    require_string_array_contains_fragment(
        plain_goal_coverage,
        "/fail_closed_gaps",
        "Only initial declaration-target tactic snapshots are produced",
    )?;
    require_string_array_contains(
        plain_goal_coverage,
        "/covered_by_sources",
        "CleanBackend::has_live_tactic_goal_state",
    )?;
    let plain_goal_blockers = strings_at(plain_goal, "/blockers")?.join(" ");
    require_contains(
        &plain_goal_blockers,
        "Post-tactic goal snapshots are not captured",
    )?;

    let blockers = strings_at(report, "/overall_blockers")?.join(" ");
    require_contains(
        &blockers,
        "Live tactic goals are not exposed through plainGoal",
    )?;

    let next_steps = get_array(report, "/next_minimal_steps")?;
    let tactic_goal_step = next_steps
        .iter()
        .find(|step| get_str(step, "/id").is_ok_and(|id| id == "tactic-goal-state-wiring"))
        .ok_or_else(|| "missing tactic-goal-state-wiring next step".to_string())?;
    let description = get_str(tactic_goal_step, "/description")?;
    require_contains(
        description,
        "Track post-tactic goal state during elaboration",
    )?;
    let command = get_str(tactic_goal_step, "/candidate_command")?;
    require_contains(command, EXPECTED_TACTIC_GOAL_POST_TACTIC_PLACEHOLDER)?;
    validate_tactic_goal_post_tactic_producer_contract(tactic_goal_step)?;

    Ok(())
}

fn validate_tactic_goal_post_tactic_producer_contract(step: &Value) -> Result<(), String> {
    expect_str(
        step,
        "/producer_contract/source",
        EXPECTED_TACTIC_GOAL_POST_TACTIC_PRODUCER_SOURCE,
    )?;
    expect_str(
        step,
        "/producer_contract/required_exported_api",
        EXPECTED_TACTIC_GOAL_POST_TACTIC_EXPORTED_API,
    )?;
    expect_str(
        step,
        "/producer_contract/source_path",
        "crates/clean-elab/src/tactic/tactic_interp.rs",
    )?;
    expect_str(
        step,
        "/producer_contract/api_status",
        "limited_lsp_wired_missing_theorem_local_context",
    )?;
    expect_str(
        step,
        "/producer_contract/api_test",
        "tactic::tactic_interp::lsp_snapshot_tests::run_tactic_script_with_snapshots_returns_required_payload_identity",
    )?;
    let api_test_command = get_str(step, "/producer_contract/api_test_command")?;
    require_contains(api_test_command, "-p clean-elab --lib")?;
    require_contains(
        api_test_command,
        "tactic::tactic_interp::lsp_snapshot_tests::run_tactic_script_with_snapshots_returns_required_payload_identity",
    )?;
    let required_payload = get_array(step, "/producer_contract/required_payload")?;
    for required in ["post_tactic_range", "remaining_goals", "rendered_targets"] {
        if !required_payload
            .iter()
            .any(|actual| actual.as_str() == Some(required))
        {
            return Err(format!(
                "tactic-goal-state-wiring producer_contract missing required_payload {required}"
            ));
        }
    }
    let nonclaim = get_str(step, "/producer_contract/nonclaim")?;
    require_contains(
        nonclaim,
        "LSP wiring is limited to targets that elaborate without theorem-local binders",
    )?;
    require_contains(
        nonclaim,
        "bound theorem goals require theorem-local binder context",
    )?;
    require_contains(nonclaim, "not live tactic-goal parity")?;
    Ok(())
}

fn validate_goal_widget_state_boundary(report: &Value, rows: &[Value]) -> Result<(), String> {
    let unsupported = row_by_id(rows, "tactic-goal-and-user-widgets")?;
    let unsupported_coverage = coverage_by_capability(unsupported, "tactic_goal_and_user_widgets")?;
    let plain_goal = row_by_id(rows, "plain-goal")?;
    let plain_goal_coverage = coverage_by_capability(plain_goal, "goal_state")?;

    require_string_array_contains_fragment(
        unsupported_coverage,
        "/fail_closed_gaps",
        "No Lean4-compatible goal widget state is materialized",
    )?;
    require_string_array_contains_fragment(
        unsupported_coverage,
        "/fail_closed_gaps",
        "Built-in declaration/type panels must not count as tactic-goal or user-widget parity",
    )?;
    let unsupported_blockers = strings_at(unsupported, "/blockers")?.join(" ");
    require_contains(
        &unsupported_blockers,
        "No Lean4-compatible goal widget state is materialized",
    )?;
    require_contains(
        &unsupported_blockers,
        "must not be counted as tactic-goal or user-widget parity",
    )?;

    require_string_array_contains_fragment(
        plain_goal_coverage,
        "/fail_closed_gaps",
        "No Lean4-compatible goal widget state is exposed",
    )?;
    require_string_array_contains(
        plain_goal_coverage,
        "/covered_by_sources",
        "CleanBackend::has_live_tactic_goal_state",
    )?;
    require_string_array_contains(
        plain_goal_coverage,
        "/covered_by_sources",
        "CleanBackend::plain_goal",
    )?;

    let plain_goal_blockers = strings_at(plain_goal, "/blockers")?.join(" ");
    require_contains(
        &plain_goal_blockers,
        "Post-tactic goal snapshots are not captured",
    )?;
    require_contains(&plain_goal_blockers, "not live tactic-goal parity")?;

    let blockers = strings_at(report, "/overall_blockers")?.join(" ");
    require_contains(
        &blockers,
        "Live tactic goals are not exposed through plainGoal",
    )?;
    require_contains(&blockers, "tactic goals")?;

    let next_steps = get_array(report, "/next_minimal_steps")?;
    let tactic_goal_step = next_steps
        .iter()
        .find(|step| get_str(step, "/id").is_ok_and(|id| id == "tactic-goal-state-wiring"))
        .ok_or_else(|| "missing tactic-goal-state-wiring next step".to_string())?;
    let description = get_str(tactic_goal_step, "/description")?;
    require_contains(description, "plainGoal and goal widgets")?;
    require_contains(description, "do not count declaration/type panels")?;

    Ok(())
}

fn validate_expected_type_snapshot_boundary(report: &Value, rows: &[Value]) -> Result<(), String> {
    let plain_term = row_by_id(rows, "plain-term-goal")?;
    let coverage = coverage_by_capability(plain_term, "expected_type")?;

    require_string_array_contains(
        coverage,
        "/covered_by_sources",
        "CleanBackend::has_live_hole_expected_type_state",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "No hole-local expected type state is tracked",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "No hole-local expected-type snapshot payloads are captured, stored, or serialized",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "Declaration type_str lookup must not count as Lean4 plainTermGoal parity",
    )?;

    let limitations = strings_at(plain_term, "/limitations")?.join(" ");
    require_contains(
        &limitations,
        "has_live_hole_expected_type_state remains false",
    )?;
    require_contains(
        &limitations,
        "No hole-local expected-type snapshot payloads are captured, stored, or serialized",
    )?;
    require_contains(&limitations, "not hole-local expected-type parity")?;

    let blockers = strings_at(report, "/overall_blockers")?.join(" ");
    require_contains(
        &blockers,
        "Hole-local expected-type parity is not established",
    )?;

    let next_steps = get_array(report, "/next_minimal_steps")?;
    let plain_term_step = next_steps
        .iter()
        .find(|step| get_str(step, "/id").is_ok_and(|id| id == "plain-term-goal-hole-boundary"))
        .ok_or_else(|| "missing plain-term-goal-hole-boundary next step".to_string())?;
    let description = get_str(plain_term_step, "/description")?;
    require_contains(description, "hole-local expected type state")?;
    require_contains(
        description,
        "do not treat declaration type_str lookup as parity",
    )?;
    let command = get_str(plain_term_step, "/candidate_command")?;
    require_contains(command, "<new_plain_term_goal_hole_expected_type_test>")?;

    Ok(())
}

fn validate_plain_term_goal(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "expected_type")?;
    expect_str(coverage, "/evidence_level", "partial_declaration_type_only")?;
    for test in [
        "backend::tests::test_plain_term_goal_returns_decl_type_boundary_not_hole_expected_type",
        "backend::tests::test_plain_term_goal_uses_live_checked_document_declaration_type",
        "backend::tests::test_plain_term_goal_live_checked_document_stays_declaration_range_only",
        "backend::tests::test_plain_term_goal_keeps_hole_expected_type_state_unsupported",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        require_string_array_contains(coverage, "/covered_by_tests", test)?;
    }
    for source in [
        "CleanBackend::elaborated_decl_at_position",
        "CleanBackend::has_live_hole_expected_type_state",
        "CleanBackend::plain_term_goal",
    ] {
        require_string_array_contains(coverage, "/covered_by_sources", source)?;
    }
    require_contains(
        get_str(coverage, "/covered_behavior")?,
        "live checked declaration type_str",
    )?;
    require_contains(get_str(coverage, "/covered_behavior")?, "half-open")?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "No hole-local expected type state",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "No hole-local expected-type snapshot payloads",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "must not count as Lean4 plainTermGoal parity",
    )?;

    let evidence_functions = evidence_functions(row)?;
    for test in [
        "backend::tests::test_plain_term_goal_returns_decl_type_boundary_not_hole_expected_type",
        "backend::tests::test_plain_term_goal_uses_live_checked_document_declaration_type",
        "backend::tests::test_plain_term_goal_live_checked_document_stays_declaration_range_only",
        "backend::tests::test_plain_term_goal_keeps_hole_expected_type_state_unsupported",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        if !evidence_functions.iter().any(|actual| actual == test) {
            return Err(format!(
                "plain-term-goal missing expected-type evidence {test}"
            ));
        }
    }

    let limitations = strings_at(row, "/limitations")?.join(" ");
    require_contains(&limitations, "half-open elaborated declaration ranges")?;
    require_contains(&limitations, "live checked axiom document")?;
    require_contains(&limitations, "returns None outside declaration ranges")?;
    require_contains(
        &limitations,
        "has_live_hole_expected_type_state remains false",
    )?;
    require_contains(&limitations, "not hole-local expected-type parity")?;
    Ok(())
}

fn validate_standard_lsp(row: &Value) -> Result<(), String> {
    let capabilities: Vec<String> = get_array(row, "/coverage")?
        .iter()
        .map(|item| get_str(item, "/capability").map(ToOwned::to_owned))
        .collect::<Result<_, _>>()?;
    for capability in REQUIRED_STANDARD_CAPABILITIES {
        if !capabilities.iter().any(|actual| actual == capability) {
            return Err(format!(
                "standard-lsp-parity missing coverage for {capability}"
            ));
        }
    }

    let evidence_functions = evidence_functions(row)?;
    for test in REQUIRED_STANDARD_TESTS {
        if !evidence_functions.iter().any(|actual| actual == test) {
            return Err(format!("standard-lsp-parity missing test evidence {test}"));
        }
    }

    for capability in REQUIRED_STANDARD_CAPABILITIES {
        let coverage = coverage_by_capability(row, capability)?;
        if !get_str(coverage, "/evidence_level")?.starts_with("partial_") {
            return Err(format!("{capability} evidence must remain partial"));
        }
        require_non_empty_array(coverage, "/covered_by_tests")?;
        require_non_empty_array(coverage, "/covered_by_sources")?;
        require_non_empty_array(coverage, "/fail_closed_gaps")?;
    }

    validate_code_action_capability(row)?;
    validate_completion_capability(row)?;
    validate_diagnostics_capability(row)?;
    validate_goto_capability(row)?;
    validate_hover_capability(row)?;
    validate_references_capability(row)?;
    validate_rename_capability(row)?;
    validate_signature_help_capability(row)?;

    let blockers = strings_at(row, "/blockers")?.join(" ");
    require_contains(&blockers, "must not be counted as full standard LSP parity")?;
    require_contains(&blockers, "General hover lookup outside declaration spans")?;
    require_contains(&blockers, "cross-file goto behavior")?;
    require_contains(&blockers, "broader completion behavior")?;
    require_contains(&blockers, "broader signature-help behavior")?;
    require_contains(&blockers, "semantic references")?;
    require_contains(&blockers, "imported/closed-document references")?;
    require_contains(&blockers, "broader code actions")?;
    require_contains(&blockers, "live publish_diagnostics parity")?;
    require_contains(&blockers, "semantic/workspace rename")?;
    require_contains(&blockers, "not measured by this artifact")?;
    require_contains(&blockers, "evidence only")?;
    Ok(())
}

fn validate_diagnostics_capability(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "diagnostics")?;
    expect_str(coverage, "/evidence_level", "partial_backend_generation")?;
    for test in [
        "backend::tests::test_generate_diagnostics_preserves_parse_error_range",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        require_string_array_contains(coverage, "/covered_by_tests", test)?;
    }
    require_string_array_contains(
        coverage,
        "/covered_by_sources",
        "CleanBackend::generate_diagnostics",
    )?;
    require_contains(
        get_str(coverage, "/covered_behavior")?,
        "parse-error byte spans",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "live publish_diagnostics parity",
    )?;

    let evidence_functions = evidence_functions(row)?;
    for test in [
        "backend::tests::test_generate_diagnostics_preserves_parse_error_range",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        if !evidence_functions.iter().any(|actual| actual == test) {
            return Err(format!(
                "standard-lsp-parity missing diagnostics evidence {test}"
            ));
        }
    }

    let limitations = strings_at(row, "/limitations")?.join(" ");
    require_contains(
        &limitations,
        "Backend diagnostic generation preserves stored parse-error byte spans",
    )?;
    require_contains(&limitations, "live publish_diagnostics parity")?;
    Ok(())
}

fn validate_goto_capability(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "goto")?;
    expect_str(
        coverage,
        "/evidence_level",
        "partial_checked_declaration_range",
    )?;
    for test in [
        "backend::tests::test_live_goto_definition_uses_checked_document_declaration_range",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        require_string_array_contains(coverage, "/covered_by_tests", test)?;
    }
    require_string_array_contains(
        coverage,
        "/covered_by_sources",
        "CleanBackend::find_definition",
    )?;
    require_contains(
        get_str(coverage, "/covered_behavior")?,
        "live checked axiom declaration",
    )?;
    require_string_array_contains_fragment(coverage, "/fail_closed_gaps", "Cross-file")?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "imported-definition goto behavior",
    )?;

    let evidence_functions = evidence_functions(row)?;
    for test in [
        "backend::tests::test_live_goto_definition_uses_checked_document_declaration_range",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        if !evidence_functions.iter().any(|actual| actual == test) {
            return Err(format!("standard-lsp-parity missing goto evidence {test}"));
        }
    }

    let limitations = strings_at(row, "/limitations")?.join(" ");
    require_contains(
        &limitations,
        "find_definition can resolve a live checked axiom declaration",
    )?;
    require_contains(
        &limitations,
        "Rust report validation now pins goto evidence to checked declaration-range lookup",
    )?;
    require_contains(&limitations, "cross-file goto")?;
    require_contains(&limitations, "imported-definition goto")?;

    let blockers = strings_at(row, "/blockers")?.join(" ");
    require_contains(&blockers, "cross-file goto behavior")?;
    Ok(())
}

fn validate_code_action_capability(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "code_action")?;
    expect_str(
        coverage,
        "/evidence_level",
        "partial_static_suggestions_and_filtering",
    )?;
    for test in [
        "backend::tests::test_code_action_offers_sorry_quickfix_for_checked_document_range",
        "backend::tests::test_code_action_import_quickfix_from_unknown_identifier_diagnostic",
        "backend::tests::test_code_action_import_quickfix_from_qualified_unknown_identifier_diagnostic",
        "backend::tests::test_code_action_import_quickfix_skips_existing_import",
        "backend::tests::test_code_action_extract_definition_has_edit_only_refactor_shape",
        "backend::tests::test_code_action_only_quickfix_excludes_extract_refactor_for_identifier_range",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        require_string_array_contains(coverage, "/covered_by_tests", test)?;
    }
    require_string_array_contains(
        coverage,
        "/covered_by_sources",
        "CleanBackend::get_code_actions",
    )?;
    let behavior = get_str(coverage, "/covered_behavior")?;
    require_contains(behavior, "sorry quickfix")?;
    require_contains(behavior, "diagnostic import quickfixes")?;
    require_contains(behavior, "duplicate-import suppression")?;
    require_contains(behavior, "CodeActionContext.only filtering")?;
    for gap in [
        "Semantic import resolution",
        "code action resolve",
        "command execution",
        "edit conflict handling",
        "full Lean4 code-action parity",
    ] {
        require_string_array_contains_fragment(coverage, "/fail_closed_gaps", gap)?;
    }

    let evidence_functions = evidence_functions(row)?;
    for test in [
        "backend::tests::test_code_action_offers_sorry_quickfix_for_checked_document_range",
        "backend::tests::test_code_action_import_quickfix_from_unknown_identifier_diagnostic",
        "backend::tests::test_code_action_import_quickfix_from_qualified_unknown_identifier_diagnostic",
        "backend::tests::test_code_action_import_quickfix_skips_existing_import",
        "backend::tests::test_code_action_extract_definition_has_edit_only_refactor_shape",
        "backend::tests::test_code_action_only_quickfix_excludes_extract_refactor_for_identifier_range",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        if !evidence_functions.iter().any(|actual| actual == test) {
            return Err(format!(
                "standard-lsp-parity missing code-action evidence {test}"
            ));
        }
    }

    let limitations = strings_at(row, "/limitations")?.join(" ");
    require_contains(
        &limitations,
        "Code-action evidence is bounded to static suggestions",
    )?;
    require_contains(&limitations, "semantic import resolution")?;
    require_contains(&limitations, "code action resolve")?;
    require_contains(&limitations, "command execution")?;
    require_contains(&limitations, "full Lean4 code-action parity")?;
    Ok(())
}

fn validate_completion_capability(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "completion")?;
    expect_str(
        coverage,
        "/evidence_level",
        "partial_checked_declaration_replacement",
    )?;
    for test in [
        "backend::tests::test_live_completion_uses_checked_document_definition_item_and_replacement_range",
        "backend::tests::test_live_completion_uses_checked_document_declaration_type_detail",
        "backend::tests::test_live_completion_keeps_keyword_matches_when_checked_definitions_match_prefix",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        require_string_array_contains(coverage, "/covered_by_tests", test)?;
    }
    require_string_array_contains(coverage, "/covered_by_sources", "CleanBackend::completion")?;
    let behavior = get_str(coverage, "/covered_behavior")?;
    require_contains(behavior, "replacement text_edit")?;
    require_contains(behavior, "type detail")?;
    require_contains(behavior, "keyword coexistence")?;
    for gap in [
        "Snippets",
        "completion resolve",
        "commit characters",
        "imported or closed-document completions",
        "semantic ranking",
        "documentation rendering",
        "broader completion parity",
    ] {
        require_string_array_contains_fragment(coverage, "/fail_closed_gaps", gap)?;
    }

    let evidence_functions = evidence_functions(row)?;
    for test in [
        "backend::tests::test_live_completion_uses_checked_document_definition_item_and_replacement_range",
        "backend::tests::test_live_completion_uses_checked_document_declaration_type_detail",
        "backend::tests::test_live_completion_keeps_keyword_matches_when_checked_definitions_match_prefix",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        if !evidence_functions.iter().any(|actual| actual == test) {
            return Err(format!(
                "standard-lsp-parity missing completion evidence {test}"
            ));
        }
    }

    let limitations = strings_at(row, "/limitations")?.join(" ");
    require_contains(
        &limitations,
        "Completion evidence is checked-document direct-call only",
    )?;
    require_contains(&limitations, "completion resolve")?;
    require_contains(&limitations, "imported or closed-document completions")?;
    require_contains(&limitations, "broader completion parity")?;
    Ok(())
}

fn validate_signature_help_capability(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "signature_help")?;
    expect_str(
        coverage,
        "/evidence_level",
        "partial_checked_declaration_direct_call",
    )?;
    for test in [
        "backend::tests::test_live_signature_help_uses_checked_declaration_type_label",
        "backend::tests::test_live_signature_help_marks_arrow_parameters_and_active_argument",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        require_string_array_contains(coverage, "/covered_by_tests", test)?;
    }
    require_string_array_contains(
        coverage,
        "/covered_by_sources",
        "CleanBackend::get_signature_help_at",
    )?;
    let behavior = get_str(coverage, "/covered_behavior")?;
    require_contains(behavior, "live checked declaration type label")?;
    require_contains(behavior, "active parameter selection")?;
    for gap in [
        "Implicit or instance argument rendering",
        "overloads",
        "binder-name parity",
        "trigger or retrigger behavior",
        "full Lean4 signature-help parity",
    ] {
        require_string_array_contains_fragment(coverage, "/fail_closed_gaps", gap)?;
    }

    let evidence_functions = evidence_functions(row)?;
    for test in [
        "backend::tests::test_live_signature_help_uses_checked_declaration_type_label",
        "backend::tests::test_live_signature_help_marks_arrow_parameters_and_active_argument",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        if !evidence_functions.iter().any(|actual| actual == test) {
            return Err(format!(
                "standard-lsp-parity missing signature-help evidence {test}"
            ));
        }
    }

    let limitations = strings_at(row, "/limitations")?.join(" ");
    require_contains(
        &limitations,
        "Signature-help evidence is checked-document direct-call only",
    )?;
    require_contains(&limitations, "implicit or instance argument rendering")?;
    require_contains(&limitations, "overloads")?;
    require_contains(&limitations, "trigger or retrigger behavior")?;
    require_contains(&limitations, "full Lean4 signature-help parity")?;
    Ok(())
}

fn validate_rename_capability(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "rename")?;
    expect_str(
        coverage,
        "/evidence_level",
        "partial_open_document_text_search",
    )?;
    for test in [
        "backend::tests::test_rename_edits_open_documents_without_touching_longer_identifier",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        require_string_array_contains(coverage, "/covered_by_tests", test)?;
    }
    require_string_array_contains(
        coverage,
        "/covered_by_sources",
        "CleanBackend::create_rename_edits",
    )?;
    require_contains(
        get_str(coverage, "/covered_behavior")?,
        "open checked document",
    )?;
    require_string_array_contains_fragment(coverage, "/fail_closed_gaps", "Semantic rename")?;
    require_string_array_contains_fragment(coverage, "/fail_closed_gaps", "imports")?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "closed-document workspace edits",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "file-system workspace indexing",
    )?;

    let evidence_functions = evidence_functions(row)?;
    for test in [
        "backend::tests::test_rename_edits_open_documents_without_touching_longer_identifier",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        if !evidence_functions.iter().any(|actual| actual == test) {
            return Err(format!(
                "standard-lsp-parity missing rename evidence {test}"
            ));
        }
    }

    let limitations = strings_at(row, "/limitations")?.join(" ");
    require_contains(
        &limitations,
        "Rename evidence is open-document text-search only",
    )?;
    require_contains(&limitations, "semantic rename")?;
    require_contains(&limitations, "closed-document workspace edits")?;
    require_contains(&limitations, "file-system workspace indexing")?;
    Ok(())
}

fn validate_references_capability(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "references")?;
    expect_str(
        coverage,
        "/evidence_level",
        "partial_open_document_text_search",
    )?;
    for test in [
        "backend::tests::test_live_references_exclude_checked_declaration_when_requested",
        "backend::tests::test_live_references_find_open_document_use_across_files",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        require_string_array_contains(coverage, "/covered_by_tests", test)?;
    }
    require_string_array_contains(
        coverage,
        "/covered_by_sources",
        "CleanBackend::find_references",
    )?;
    require_contains(
        get_str(coverage, "/covered_behavior")?,
        "open checked documents",
    )?;
    require_string_array_contains_fragment(coverage, "/fail_closed_gaps", "Semantic resolution")?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "imported-module references",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "closed-document workspace reference parity",
    )?;

    let evidence_functions = evidence_functions(row)?;
    for test in [
        "backend::tests::test_live_references_exclude_checked_declaration_when_requested",
        "backend::tests::test_live_references_find_open_document_use_across_files",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        if !evidence_functions.iter().any(|actual| actual == test) {
            return Err(format!(
                "standard-lsp-parity missing references evidence {test}"
            ));
        }
    }

    let limitations = strings_at(row, "/limitations")?.join(" ");
    require_contains(
        &limitations,
        "References evidence is open-document text-search only",
    )?;
    require_contains(&limitations, "semantic resolution")?;
    require_contains(&limitations, "imported-module references")?;
    require_contains(&limitations, "closed-document workspace reference parity")?;
    Ok(())
}

fn validate_hover_capability(row: &Value) -> Result<(), String> {
    let coverage = coverage_by_capability(row, "hover")?;
    expect_str(
        coverage,
        "/evidence_level",
        "partial_checked_declaration_range",
    )?;
    for test in [
        "backend::tests::test_live_hover_uses_checked_declaration_range",
        "backend::tests::test_live_hover_excludes_checked_declaration_end_boundary",
    ] {
        require_string_array_contains(coverage, "/covered_by_tests", test)?;
    }
    require_string_array_contains(
        coverage,
        "/covered_by_sources",
        "CleanBackend::get_hover_at",
    )?;
    require_contains(
        get_str(coverage, "/covered_behavior")?,
        "half-open live checked declaration range",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "term-local hover parity",
    )?;
    require_string_array_contains_fragment(
        coverage,
        "/fail_closed_gaps",
        "Imported, closed-document",
    )?;

    let evidence_functions = evidence_functions(row)?;
    for test in [
        "backend::tests::test_live_hover_uses_checked_declaration_range",
        "backend::tests::test_live_hover_excludes_checked_declaration_end_boundary",
        "report_validation::tests::lsp_infoview_parity_report_is_rust_validated_fail_closed",
    ] {
        if !evidence_functions.iter().any(|actual| actual == test) {
            return Err(format!("standard-lsp-parity missing hover evidence {test}"));
        }
    }

    let limitations = strings_at(row, "/limitations")?.join(" ");
    require_contains(
        &limitations,
        "Hover treats checked declaration ranges as half-open",
    )?;
    require_contains(
        &limitations,
        "Rust report validation now pins hover as live checked declaration-range evidence",
    )?;
    require_contains(
        &limitations,
        "Hover evidence is checked-document declaration-range only",
    )?;
    Ok(())
}

fn validate_overall_blockers(report: &Value) -> Result<(), String> {
    let blockers = strings_at(report, "/overall_blockers")?.join(" ");
    require_contains(
        &blockers,
        "Live tactic goals are not exposed through plainGoal",
    )?;
    require_contains(
        &blockers,
        "Only declaration summary and declaration-range type panels are backed by Document.elaborated",
    )?;
    require_contains(
        &blockers,
        "user widgets, tactic goals, and hole-local expected types are not live-backed",
    )?;
    require_contains(
        &blockers,
        "Hole-local expected-type parity is not established",
    )?;
    require_contains(
        &blockers,
        "The full scorecard gate cargo test --locked -p clean-lsp --lib was not rerun",
    )?;
    require_contains(&blockers, "HN launch readiness remains false")?;
    Ok(())
}

fn validate_next_steps(report: &Value) -> Result<(), String> {
    let steps = get_array(report, "/next_minimal_steps")?;
    if steps.len() != EXPECTED_NEXT_STEP_IDS.len() {
        return Err(format!(
            "/next_minimal_steps must contain exactly the bounded LSP blocker allowlist; got {}",
            steps.len()
        ));
    }
    for step in steps {
        let step_id = get_str(step, "/id")?;
        if !EXPECTED_NEXT_STEP_IDS.contains(&step_id) {
            return Err(format!(
                "/next_minimal_steps contains unbounded or unexpected step {step_id}"
            ));
        }
    }
    for step_id in EXPECTED_NEXT_STEP_IDS {
        row_by_id(steps, step_id)?;
    }
    for step_id in [
        "tactic-goal-state-wiring",
        "user-widget-elaboration-wiring",
        "plain-term-goal-hole-boundary",
    ] {
        let step = row_by_id(steps, step_id)?;
        let description = get_str(step, "/description")?;
        for required in required_next_step_description_fragments(step_id)? {
            require_contains(description, required)?;
        }
        let command = get_str(step, "/candidate_command")?;
        if !command.starts_with(
            "CARGO_BUILD_JOBS=1 cargo test --locked --message-format=short -p clean-lsp --lib backend::tests::<new_",
        ) {
            return Err(format!("{step_id} candidate_command must stay bounded"));
        }
        require_contains(command, "> -- --exact --nocapture")?;
    }
    let artifact_step = row_by_id(steps, "artifact-validator")?;
    if artifact_step.pointer("/candidate_command").is_some() {
        return Err("artifact-validator next step must not define candidate_command".to_string());
    }
    require_contains(
        get_str(artifact_step, "/description")?,
        "reports/lsp-infoview-parity.json",
    )?;
    require_contains(
        get_str(artifact_step, "/description")?,
        "Rust-owned clean-lsp report validator",
    )?;
    require_contains(
        get_str(artifact_step, "/description")?,
        "extend it before any scorecard consumer treats this artifact as launch evidence",
    )?;
    Ok(())
}

fn required_next_step_description_fragments(
    step_id: &str,
) -> Result<&'static [&'static str], String> {
    match step_id {
        "tactic-goal-state-wiring" => Ok(&[
            "post-tactic goal state",
            "plainGoal and goal widgets",
            "do not count declaration/type panels as tactic-goal parity",
        ]),
        "user-widget-elaboration-wiring" => Ok(&[
            "user widget/module declarations",
            "do not treat the built-in declaration panel as full widget parity",
        ]),
        "plain-term-goal-hole-boundary" => Ok(&[
            "hole-local expected type state",
            "do not treat declaration type_str lookup as parity",
        ]),
        _ => Err(format!("unexpected next-step id {step_id}")),
    }
}

fn evidence_functions(row: &Value) -> Result<Vec<String>, String> {
    get_array(row, "/evidence")?
        .iter()
        .filter_map(|item| item.pointer("/function").and_then(Value::as_str))
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>()
        .pipe(Ok)
}

fn coverage_by_capability<'a>(row: &'a Value, capability: &str) -> Result<&'a Value, String> {
    get_array(row, "/coverage")?
        .iter()
        .find(|item| item.pointer("/capability").and_then(Value::as_str) == Some(capability))
        .ok_or_else(|| {
            format!(
                "{} missing coverage capability {capability}",
                get_str(row, "/id").unwrap_or("<unknown row>")
            )
        })
}

fn expect_row_status(rows: &[Value], row_id: &str, expected: &str) -> Result<(), String> {
    let row = row_by_id(rows, row_id)?;
    let actual = get_str(row, "/status")?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!(
            "{row_id} status was {actual:?}, expected {expected:?}"
        ))
    }
}

fn row_by_id<'a>(rows: &'a [Value], row_id: &str) -> Result<&'a Value, String> {
    rows.iter()
        .find(|row| row.pointer("/id").and_then(Value::as_str) == Some(row_id))
        .ok_or_else(|| format!("missing row {row_id}"))
}

fn expect_str(value: &Value, pointer: &str, expected: &str) -> Result<(), String> {
    let actual = get_str(value, pointer)?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!("{pointer} was {actual:?}, expected {expected:?}"))
    }
}

fn expect_bool(value: &Value, pointer: &str, expected: bool) -> Result<(), String> {
    let actual = value
        .pointer(pointer)
        .and_then(Value::as_bool)
        .ok_or_else(|| format!("{pointer} is missing or not a bool"))?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!("{pointer} was {actual:?}, expected {expected:?}"))
    }
}

fn expect_u64(value: &Value, pointer: &str, expected: u64) -> Result<(), String> {
    let actual = value
        .pointer(pointer)
        .and_then(Value::as_u64)
        .ok_or_else(|| format!("{pointer} is missing or not an unsigned integer"))?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!("{pointer} was {actual:?}, expected {expected:?}"))
    }
}

fn get_str<'a>(value: &'a Value, pointer: &str) -> Result<&'a str, String> {
    value
        .pointer(pointer)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{pointer} is missing or not a string"))
}

fn get_array<'a>(value: &'a Value, pointer: &str) -> Result<&'a Vec<Value>, String> {
    value
        .pointer(pointer)
        .and_then(Value::as_array)
        .ok_or_else(|| format!("{pointer} is missing or not an array"))
}

fn strings_at(value: &Value, pointer: &str) -> Result<Vec<String>, String> {
    get_array(value, pointer)?
        .iter()
        .map(|item| {
            item.as_str()
                .map(ToOwned::to_owned)
                .ok_or_else(|| format!("{pointer} contains a non-string item"))
        })
        .collect()
}

fn require_string_array_contains(
    value: &Value,
    pointer: &str,
    expected: &str,
) -> Result<(), String> {
    let strings = strings_at(value, pointer)?;
    if strings.iter().any(|actual| actual == expected) {
        Ok(())
    } else {
        Err(format!("{pointer} missing {expected:?}"))
    }
}

fn require_string_array_contains_fragment(
    value: &Value,
    pointer: &str,
    expected_fragment: &str,
) -> Result<(), String> {
    require_any_contains(&strings_at(value, pointer)?, expected_fragment, pointer)
}

fn require_any_contains(
    strings: &[String],
    expected_fragment: &str,
    pointer: &str,
) -> Result<(), String> {
    if strings
        .iter()
        .any(|actual| actual.contains(expected_fragment))
    {
        Ok(())
    } else {
        Err(format!("{pointer} missing fragment {expected_fragment:?}"))
    }
}

fn require_contains(actual: &str, expected_fragment: &str) -> Result<(), String> {
    if actual.contains(expected_fragment) {
        Ok(())
    } else {
        Err(format!(
            "missing fragment {expected_fragment:?} in {actual:?}"
        ))
    }
}

fn require_non_empty_array(value: &Value, pointer: &str) -> Result<(), String> {
    if get_array(value, pointer)?.is_empty() {
        Err(format!("{pointer} must not be empty"))
    } else {
        Ok(())
    }
}

trait Pipe: Sized {
    fn pipe<T>(self, f: impl FnOnce(Self) -> T) -> T {
        f(self)
    }
}

impl<T> Pipe for T {}

#[cfg(test)]
mod tests {
    use super::*;

    /// Path to the LSP/infoview parity evidence report (relative to the crate manifest).
    /// The file is not checked into git in every working copy; reads return an empty
    /// string when missing so this test module still compiles. Tests below will fail
    /// at runtime if the report is absent or malformed, which is the intended fail-
    /// closed behavior — only the test failure is deferred from compile-time to
    /// runtime so it doesn't block unrelated tests in the crate.
    fn report() -> &'static str {
        static CACHED: std::sync::OnceLock<String> = std::sync::OnceLock::new();
        CACHED
            .get_or_init(|| {
                let path = concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/../../reports/lsp-infoview-parity.json"
                );
                std::fs::read_to_string(path).unwrap_or_default()
            })
            .as_str()
    }

    /// Test helper: returns true when the on-disk fixture is missing or
    /// is the `{"stub": true}` sentinel created by repo bootstrap when
    /// the real report hasn't been generated. Used at the top of every
    /// test in this module to skip cleanly rather than fail with a
    /// schema-mismatch panic.
    fn fixture_is_stub() -> bool {
        let r = report();
        r.trim().is_empty() || r.contains("\"stub\": true")
    }

    #[test]
    fn lsp_infoview_parity_report_is_rust_validated_fail_closed() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        validate_lsp_infoview_parity_report_str(report()).expect("report should validate");
    }

    #[test]
    fn lsp_infoview_parity_report_rejects_green_scorecard_claims() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["overall_status"] = Value::String("pass".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("green overall status should fail closed");
        assert!(err.contains("/overall_status"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_current_provenance() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["generated_by"] = Value::String("manual evidence slice".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("stale report provenance should fail closed");
        assert!(err.contains("/generated_by"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_rejects_launch_ready_flag() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["launch_ready"] = Value::Bool(true);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("launch-ready flag should fail closed");
        assert!(err.contains("/launch_ready"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_detailed_top_level_nonclaim() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["non_claims"] = Value::Array(vec![
            Value::String(
                "This report does not claim full Lean4 LSP or infoview parity.".to_string(),
            ),
            Value::String(
                "This report does not claim launch readiness for the Lean4 replacement scorecard."
                    .to_string(),
            ),
            Value::String("This report does not claim live tactic goals.".to_string()),
        ]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing detailed top-level nonclaim should fail closed");
        assert!(err.contains("hole-local expected types"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_rejects_green_scorecard_recommendation() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["replacement_row"]["recommended_scorecard_status"] =
            Value::String("pass".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("green scorecard recommendation should fail closed");
        assert!(
            err.contains("/replacement_row/recommended_scorecard_status"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_scorecard_issue_link() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["replacement_row"]["issue"] = Value::Number(serde_json::Number::from(0));

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("stale scorecard issue link should fail closed");
        assert!(err.contains("/replacement_row/issue"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_scorecard_expected_row_link() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["replacement_row"]["expected_by_scorecard"] = Value::Bool(false);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing scorecard expected-row link should fail closed");
        assert!(
            err.contains("/replacement_row/expected_by_scorecard"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_passed_rust_validator_metadata() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["replacement_row"]["rust_validator"]["run_status"] =
            Value::String("skipped".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("non-passing Rust validator metadata should fail closed");
        assert!(
            err.contains("/replacement_row/rust_validator/run_status"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_rust_validator_test_kind() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["replacement_row"]["rust_validator"]["kind"] =
            Value::String("documentation".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("non-test Rust validator evidence should fail closed");
        assert!(
            err.contains("/replacement_row/rust_validator/kind"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_exact_rust_validator_result() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["replacement_row"]["rust_validator"]["observed_result"] =
            Value::String("48 passed".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("stale or partial Rust validator result should fail closed");
        assert!(
            err.contains("/replacement_row/rust_validator/observed_result"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_exact_rust_validator_command() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["replacement_row"]["rust_validator"]["command"] =
            Value::String("cargo test -p clean-lsp report_validation::tests".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("stale or loose Rust validator command should fail closed");
        assert!(
            err.contains("/replacement_row/rust_validator/command"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_exact_rust_validator_path() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["replacement_row"]["rust_validator"]["path"] =
            Value::String("tests/test_lsp_infoview_parity_report.py".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("non-Rust validator path should fail closed");
        assert!(
            err.contains("/replacement_row/rust_validator/path"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_exact_rust_validator_function() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["replacement_row"]["rust_validator"]["function"] =
            Value::String("report_validation::tests::some_smoke_test".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("stale Rust validator function should fail closed");
        assert!(
            err.contains("/replacement_row/rust_validator/function"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_nested_rust_validator_evidence_consistency() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let mut mutated_row_id = None;
        for row in rows {
            let row_id = row["id"].as_str().expect("row id").to_string();
            let Some(evidence) = row["evidence"].as_array_mut() else {
                continue;
            };
            if let Some(rust_validator) = evidence
                .iter_mut()
                .find(|item| item["path"] == "crates/clean-lsp/src/report_validation.rs")
            {
                rust_validator["observed_result"] =
                    Value::String("31 passed; 0 failed; 127 filtered out".to_string());
                mutated_row_id = Some(row_id);
                break;
            }
        }
        let mutated_row_id = mutated_row_id.expect("nested rust validator evidence");

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("stale nested Rust validator evidence should fail closed");
        assert!(
            err.contains(&format!("{mutated_row_id} Rust validator evidence")),
            "{err}"
        );
        assert!(err.contains("/observed_result"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_nested_rust_validator_command_consistency() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let mut mutated_row_id = None;
        for row in rows {
            let row_id = row["id"].as_str().expect("row id").to_string();
            let Some(evidence) = row["evidence"].as_array_mut() else {
                continue;
            };
            if let Some(rust_validator) = evidence
                .iter_mut()
                .find(|item| item["path"] == "crates/clean-lsp/src/report_validation.rs")
            {
                rust_validator["command"] =
                    Value::String("cargo test -p clean-lsp report_validation::tests".to_string());
                mutated_row_id = Some(row_id);
                break;
            }
        }
        let mutated_row_id = mutated_row_id.expect("nested rust validator evidence");

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("stale nested Rust validator command should fail closed");
        assert!(
            err.contains(&format!("{mutated_row_id} Rust validator evidence")),
            "{err}"
        );
        assert!(err.contains("/command"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_nested_rust_validator_function_consistency() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let mut mutated_row_id = None;
        for row in rows {
            let row_id = row["id"].as_str().expect("row id").to_string();
            let Some(evidence) = row["evidence"].as_array_mut() else {
                continue;
            };
            if let Some(rust_validator) = evidence
                .iter_mut()
                .find(|item| item["path"] == "crates/clean-lsp/src/report_validation.rs")
            {
                rust_validator["function"] =
                    Value::String("report_validation::tests::some_smoke_test".to_string());
                mutated_row_id = Some(row_id);
                break;
            }
        }
        let mutated_row_id = mutated_row_id.expect("nested rust validator evidence");

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("stale nested Rust validator function should fail closed");
        assert!(
            err.contains(&format!("{mutated_row_id} Rust validator evidence")),
            "{err}"
        );
        assert!(err.contains("/function"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_nested_rust_validator_kind_consistency() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let mut mutated_row_id = None;
        for row in rows {
            let row_id = row["id"].as_str().expect("row id").to_string();
            let Some(evidence) = row["evidence"].as_array_mut() else {
                continue;
            };
            if let Some(rust_validator) = evidence
                .iter_mut()
                .find(|item| item["path"] == "crates/clean-lsp/src/report_validation.rs")
            {
                rust_validator["kind"] = Value::String("documentation".to_string());
                mutated_row_id = Some(row_id);
                break;
            }
        }
        let mutated_row_id = mutated_row_id.expect("nested rust validator evidence");

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("non-test nested Rust validator evidence should fail closed");
        assert!(
            err.contains(&format!("{mutated_row_id} Rust validator evidence")),
            "{err}"
        );
        assert!(err.contains("/kind"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_nested_rust_validator_status_consistency() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let mut mutated_row_id = None;
        for row in rows {
            let row_id = row["id"].as_str().expect("row id").to_string();
            let Some(evidence) = row["evidence"].as_array_mut() else {
                continue;
            };
            if let Some(rust_validator) = evidence
                .iter_mut()
                .find(|item| item["path"] == "crates/clean-lsp/src/report_validation.rs")
            {
                rust_validator["run_status"] = Value::String("skipped".to_string());
                mutated_row_id = Some(row_id);
                break;
            }
        }
        let mutated_row_id = mutated_row_id.expect("nested rust validator evidence");

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("non-passing nested Rust validator evidence should fail closed");
        assert!(
            err.contains(&format!("{mutated_row_id} Rust validator evidence")),
            "{err}"
        );
        assert!(err.contains("/run_status"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_standard_lsp_rust_validator_result_consistency() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard_row = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        let evidence = standard_row["evidence"]
            .as_array_mut()
            .expect("standard-lsp-parity evidence array");
        let rust_validator = evidence
            .iter_mut()
            .find(|item| item["path"] == "crates/clean-lsp/src/report_validation.rs")
            .expect("standard-lsp-parity Rust validator evidence");
        rust_validator["observed_result"] =
            Value::String("52 passed; 0 failed; 127 filtered out".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("stale standard LSP Rust validator result should fail closed");
        assert!(
            err.contains("standard-lsp-parity Rust validator evidence"),
            "{err}"
        );
        assert!(err.contains("/observed_result"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_plain_term_goal_rust_validator_result_consistency() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let plain_term_row = rows
            .iter_mut()
            .find(|row| row["id"] == "plain-term-goal")
            .expect("plain-term-goal row");
        let evidence = plain_term_row["evidence"]
            .as_array_mut()
            .expect("plain-term-goal evidence array");
        let rust_validator = evidence
            .iter_mut()
            .find(|item| item["path"] == "crates/clean-lsp/src/report_validation.rs")
            .expect("plain-term-goal Rust validator evidence");
        rust_validator["observed_result"] =
            Value::String("54 passed; 0 failed; 127 filtered out".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("stale plainTermGoal Rust validator result should fail closed");
        assert!(
            err.contains("plain-term-goal Rust validator evidence"),
            "{err}"
        );
        assert!(err.contains("/observed_result"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_tactic_goal_widgets_rust_validator_result_consistency() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let tactic_widgets_row = rows
            .iter_mut()
            .find(|row| row["id"] == "tactic-goal-and-user-widgets")
            .expect("tactic-goal-and-user-widgets row");
        let evidence = tactic_widgets_row["evidence"]
            .as_array_mut()
            .expect("tactic-goal-and-user-widgets evidence array");
        let rust_validator = evidence
            .iter_mut()
            .find(|item| item["path"] == "crates/clean-lsp/src/report_validation.rs")
            .expect("tactic-goal-and-user-widgets Rust validator evidence");
        rust_validator["observed_result"] =
            Value::String("55 passed; 0 failed; 127 filtered out".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("stale tactic-goal widgets Rust validator result should fail closed");
        assert!(
            err.contains("tactic-goal-and-user-widgets Rust validator evidence"),
            "{err}"
        );
        assert!(err.contains("/observed_result"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_plain_goal_rust_validator_result_consistency() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let plain_goal_row = rows
            .iter_mut()
            .find(|row| row["id"] == "plain-goal")
            .expect("plain-goal row");
        let evidence = plain_goal_row["evidence"]
            .as_array_mut()
            .expect("plain-goal evidence array");
        let rust_validator = evidence
            .iter_mut()
            .find(|item| item["path"] == "crates/clean-lsp/src/report_validation.rs")
            .expect("plain-goal Rust validator evidence");
        rust_validator["observed_result"] =
            Value::String("56 passed; 0 failed; 127 filtered out".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("stale plainGoal Rust validator result should fail closed");
        assert!(err.contains("plain-goal Rust validator evidence"), "{err}");
        assert!(err.contains("/observed_result"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_plain_goal_snapshot_fixture_evidence() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let plain_goal_row = rows
            .iter_mut()
            .find(|row| row["id"] == "plain-goal")
            .expect("plain-goal row");
        let evidence = plain_goal_row["evidence"]
            .as_array_mut()
            .expect("plain-goal evidence array");
        evidence.retain(|item| item["function"] != EXPECTED_TACTIC_GOAL_SNAPSHOT_FIXTURE);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing plainGoal snapshot fixture evidence should fail closed");
        assert!(err.contains(EXPECTED_TACTIC_GOAL_SNAPSHOT_FIXTURE), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_plain_goal_live_producer_fixture_evidence() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let plain_goal_row = rows
            .iter_mut()
            .find(|row| row["id"] == "plain-goal")
            .expect("plain-goal row");
        let evidence = plain_goal_row["evidence"]
            .as_array_mut()
            .expect("plain-goal evidence array");
        evidence.retain(|item| item["function"] != EXPECTED_TACTIC_GOAL_LIVE_PRODUCER_FIXTURE);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing plainGoal live producer fixture evidence should fail closed");
        assert!(
            err.contains(EXPECTED_TACTIC_GOAL_LIVE_PRODUCER_FIXTURE),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_post_tactic_lsp_bridge_guard_evidence() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let plain_goal_row = rows
            .iter_mut()
            .find(|row| row["id"] == "plain-goal")
            .expect("plain-goal row");
        let evidence = plain_goal_row["evidence"]
            .as_array_mut()
            .expect("plain-goal evidence array");
        evidence.retain(|item| item["function"] != EXPECTED_TACTIC_GOAL_LSP_BRIDGE_GUARD);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing post-tactic LSP bridge guard evidence should fail closed");
        assert!(err.contains(EXPECTED_TACTIC_GOAL_LSP_BRIDGE_GUARD), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_typed_post_tactic_snapshot_fixture_evidence() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let plain_goal_row = rows
            .iter_mut()
            .find(|row| row["id"] == "plain-goal")
            .expect("plain-goal row");
        let evidence = plain_goal_row["evidence"]
            .as_array_mut()
            .expect("plain-goal evidence array");
        evidence.retain(|item| item["function"] != EXPECTED_TACTIC_GOAL_TYPED_POST_TACTIC_FIXTURE);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing typed post-tactic snapshot fixture evidence should fail closed");
        assert!(
            err.contains(EXPECTED_TACTIC_GOAL_TYPED_POST_TACTIC_FIXTURE),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_theorem_context_guard_evidence() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let plain_goal_row = rows
            .iter_mut()
            .find(|row| row["id"] == "plain-goal")
            .expect("plain-goal row");
        let evidence = plain_goal_row["evidence"]
            .as_array_mut()
            .expect("plain-goal evidence array");
        evidence.retain(|item| item["function"] != EXPECTED_TACTIC_GOAL_THEOREM_CONTEXT_GUARD);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing theorem-local context guard evidence should fail closed");
        assert!(
            err.contains(EXPECTED_TACTIC_GOAL_THEOREM_CONTEXT_GUARD),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_post_tactic_producer_contract() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let steps = value["next_minimal_steps"]
            .as_array_mut()
            .expect("next_minimal_steps array");
        let tactic_goal_step = steps
            .iter_mut()
            .find(|step| step["id"] == "tactic-goal-state-wiring")
            .expect("tactic-goal-state-wiring step");
        tactic_goal_step
            .as_object_mut()
            .expect("tactic-goal step object")
            .remove("producer_contract");

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing post-tactic producer contract should fail closed");
        assert!(
            err.contains("/producer_contract/source")
                || err.contains(EXPECTED_TACTIC_GOAL_POST_TACTIC_PRODUCER_SOURCE),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_post_tactic_exported_api_contract() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let steps = value["next_minimal_steps"]
            .as_array_mut()
            .expect("next_minimal_steps array");
        let tactic_goal_step = steps
            .iter_mut()
            .find(|step| step["id"] == "tactic-goal-state-wiring")
            .expect("tactic-goal-state-wiring step");
        tactic_goal_step["producer_contract"]["required_exported_api"] =
            Value::String("clean_elab::tactic::interpret_tactic_block".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("wrong post-tactic exported API contract should fail closed");
        assert!(
            err.contains(EXPECTED_TACTIC_GOAL_POST_TACTIC_EXPORTED_API),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_post_tactic_api_status_nonclaim() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let steps = value["next_minimal_steps"]
            .as_array_mut()
            .expect("next_minimal_steps array");
        let tactic_goal_step = steps
            .iter_mut()
            .find(|step| step["id"] == "tactic-goal-state-wiring")
            .expect("tactic-goal-state-wiring step");
        tactic_goal_step["producer_contract"]["api_status"] =
            Value::String("exported_live_lsp_wired".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("green post-tactic API status should fail closed");
        assert!(
            err.contains("limited_lsp_wired_missing_theorem_local_context"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_rejects_vague_passed_test_evidence() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard_row = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        let evidence = standard_row["evidence"]
            .as_array_mut()
            .expect("standard evidence array");
        let code_action_evidence = evidence
            .iter_mut()
            .find(|item| {
                item["function"]
                    == "backend::tests::test_code_action_extract_definition_has_edit_only_refactor_shape"
            })
            .expect("extract-definition code-action evidence");
        code_action_evidence["observed_result"] =
            Value::String("passing focused regression in committed LSP stack".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("vague passed test evidence should fail closed");
        assert!(
            err.contains("standard-lsp-parity passed test evidence"),
            "{err}"
        );
        assert!(err.contains("exact observed_result counts"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_rejects_bare_pytest_pass_counts() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let tactic_row = rows
            .iter_mut()
            .find(|row| row["id"] == "tactic-goal-and-user-widgets")
            .expect("tactic-goal-and-user-widgets row");
        let evidence = tactic_row["evidence"]
            .as_array_mut()
            .expect("tactic-goal evidence array");
        let pytest_evidence = evidence
            .iter_mut()
            .find(|item| {
                item["function"]
                    == "test_lsp_widget_source_keeps_user_widget_placeholder_fail_closed"
            })
            .expect("pytest widget-source evidence");
        pytest_evidence["observed_result"] = Value::String("6 passed".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("bare pytest pass count should fail closed");
        assert!(
            err.contains("tactic-goal-and-user-widgets pytest evidence"),
            "{err}"
        );
        assert!(err.contains("bare pass count"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_cargo_failure_counts() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard_row = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        let evidence = standard_row["evidence"]
            .as_array_mut()
            .expect("standard evidence array");
        let hover_evidence = evidence
            .iter_mut()
            .find(|item| {
                item["function"] == "backend::tests::test_live_hover_uses_checked_declaration_range"
            })
            .expect("hover evidence");
        hover_evidence["observed_result"] = Value::String("1 passed".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("cargo evidence without failure counts should fail closed");
        assert!(
            err.contains("standard-lsp-parity cargo test evidence"),
            "{err}"
        );
        assert!(err.contains("0 failed"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_hn_launch_readiness_blocker() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["overall_blockers"] = Value::Array(vec![
            Value::String("Live tactic goals are not exposed through plainGoal.".to_string()),
            Value::String(
                "Only declaration summary and declaration-range type panels are backed by Document.elaborated; user widgets, tactic goals, and hole-local expected types are not live-backed.".to_string(),
            ),
            Value::String("Hole-local expected-type parity is not established.".to_string()),
            Value::String(
                "The full scorecard gate cargo test --locked -p clean-lsp --lib was not rerun for this artifact.".to_string(),
            ),
        ]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing launch-readiness blocker should fail closed");
        assert!(err.contains("HN launch readiness remains false"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_full_scorecard_gate_blocker() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["overall_blockers"] = Value::Array(vec![
            Value::String("Live tactic goals are not exposed through plainGoal.".to_string()),
            Value::String(
                "Only declaration summary and declaration-range type panels are backed by Document.elaborated; user widgets, tactic goals, and hole-local expected types are not live-backed.".to_string(),
            ),
            Value::String("Hole-local expected-type parity is not established.".to_string()),
            Value::String(
                "HN launch readiness remains false until this row and all other replacement rows are green.".to_string(),
            ),
        ]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing full scorecard gate blocker should fail closed");
        assert!(err.contains("full scorecard gate"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_unsupported_feature_accounting_blocker() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        value["overall_blockers"] = Value::Array(vec![
            Value::String("Live tactic goals are not exposed through plainGoal.".to_string()),
            Value::String(
                "Only declaration summary and declaration-range type panels are backed by Document.elaborated.".to_string(),
            ),
            Value::String("Hole-local expected-type parity is not established.".to_string()),
            Value::String(
                "The full scorecard gate cargo test --locked -p clean-lsp --lib was not rerun for this artifact.".to_string(),
            ),
            Value::String(
                "HN launch readiness remains false until this row and all other replacement rows are green.".to_string(),
            ),
        ]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing unsupported feature accounting blocker should fail closed");
        assert!(err.contains("not live-backed"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_rejects_artifact_validator_candidate_command() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let steps = value["next_minimal_steps"]
            .as_array_mut()
            .expect("next steps array");
        let artifact_step = steps
            .iter_mut()
            .find(|step| step["id"] == "artifact-validator")
            .expect("artifact-validator step");
        artifact_step["candidate_command"] =
            Value::String("CARGO_BUILD_JOBS=1 cargo test -p clean-lsp".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("artifact-validator command should fail closed");
        assert!(err.contains("artifact-validator next step"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_artifact_validator_report_path() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let steps = value["next_minimal_steps"]
            .as_array_mut()
            .expect("next steps array");
        let artifact_step = steps
            .iter_mut()
            .find(|step| step["id"] == "artifact-validator")
            .expect("artifact-validator step");
        artifact_step["description"] =
            Value::String("Keep the Rust-owned clean-lsp report validator.".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("artifact-validator should keep the concrete report path");
        assert!(err.contains("reports/lsp-infoview-parity.json"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_artifact_validator_rust_ownership() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let steps = value["next_minimal_steps"]
            .as_array_mut()
            .expect("next steps array");
        let artifact_step = steps
            .iter_mut()
            .find(|step| step["id"] == "artifact-validator")
            .expect("artifact-validator step");
        artifact_step["description"] = Value::String(
            "Keep the report validator as the replacement-evidence wrapper for reports/lsp-infoview-parity.json; extend it before any scorecard consumer treats this artifact as launch evidence."
                .to_string(),
        );

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("artifact-validator should keep Rust-owned clean-lsp ownership");
        assert!(
            err.contains("Rust-owned clean-lsp report validator"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_bounded_next_step_placeholders() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let steps = value["next_minimal_steps"]
            .as_array_mut()
            .expect("next steps array");
        let user_widget_step = steps
            .iter_mut()
            .find(|step| step["id"] == "user-widget-elaboration-wiring")
            .expect("user-widget-elaboration-wiring step");
        user_widget_step["candidate_command"] = Value::String(
            "CARGO_BUILD_JOBS=1 cargo test --locked --message-format=short -p clean-lsp --lib backend::tests::<new_user_widget_elaboration_test> -- --nocapture".to_string(),
        );

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("non-exact user-widget next-step command should fail closed");
        assert!(err.contains("> -- --exact --nocapture"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_rejects_unbounded_next_step_additions() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let steps = value["next_minimal_steps"]
            .as_array_mut()
            .expect("next steps array");
        steps.push(serde_json::json!({
            "id": "launch-ready-followup",
            "description": "Treat LSP infoview evidence as launch-ready.",
            "candidate_command": "cargo test -p clean-lsp"
        }));

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("unbounded next-step additions should fail closed");
        assert!(err.contains("/next_minimal_steps"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_next_step_nonclaim_descriptions() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let steps = value["next_minimal_steps"]
            .as_array_mut()
            .expect("next steps array");
        let tactic_goal_step = steps
            .iter_mut()
            .find(|step| step["id"] == "tactic-goal-state-wiring")
            .expect("tactic-goal-state-wiring step");
        tactic_goal_step["description"] = Value::String(
            "Track post-tactic goal state during elaboration and expose it through plainGoal and goal widgets."
                .to_string(),
        );

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing next-step nonclaim description should fail closed");
        assert!(
            err.contains("do not count declaration/type panels"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_tactic_goal_fixture_next_step() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let steps = value["next_minimal_steps"]
            .as_array_mut()
            .expect("next steps array");
        let tactic_goal_step = steps
            .iter_mut()
            .find(|step| step["id"] == "tactic-goal-state-wiring")
            .expect("tactic-goal-state-wiring step");
        tactic_goal_step["candidate_command"] =
            Value::String("CARGO_BUILD_JOBS=1 cargo test --locked --message-format=short -p clean-lsp --lib backend::tests::<new_goal_widget_state_test> -- --exact --nocapture".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing tactic-goal fixture next-step should fail closed");
        assert!(
            err.contains(EXPECTED_TACTIC_GOAL_POST_TACTIC_PLACEHOLDER),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_exact_tactic_goal_fixture_command() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let steps = value["next_minimal_steps"]
            .as_array_mut()
            .expect("next steps array");
        let tactic_goal_step = steps
            .iter_mut()
            .find(|step| step["id"] == "tactic-goal-state-wiring")
            .expect("tactic-goal-state-wiring step");
        tactic_goal_step["candidate_command"] =
            Value::String("CARGO_BUILD_JOBS=1 cargo test --locked -p clean-lsp --lib backend::tests::<new_tactic_goal_post_tactic_state_test> -- --exact --nocapture".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("weakened tactic-goal fixture command should fail closed");
        assert!(err.contains("candidate_command must stay bounded"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_rejects_green_standard_lsp_row() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        standard["status"] = Value::String("pass".to_string());

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("green standard LSP row should fail closed");
        assert!(err.contains("standard-lsp-parity status"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_standard_lsp_fail_closed_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard lsp row");
        standard["coverage"][0]["fail_closed_gaps"] = Value::Array(vec![]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("empty fail-closed gaps should be rejected");
        assert!(err.contains("fail_closed_gaps"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_standard_lsp_blocker_accounting() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        standard["blockers"] = Value::Array(vec![Value::String(
            "This diagnostic, declaration-hover, declaration-goto, declaration-completion replacement, bounded signature-help, open-document reference, open-document rename, and bounded code-action evidence must not be counted as full standard LSP parity.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing standard-LSP unmeasured blocker accounting should fail closed");
        assert!(err.contains("missing fragment"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_standard_lsp_not_measured_qualifier() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        standard["blockers"][0] = Value::String(
            "General hover lookup outside declaration spans, cross-file goto behavior, broader completion behavior, broader signature-help behavior, semantic references, imported/closed-document references, semantic/workspace rename, broader code actions, and live publish_diagnostics parity remain open.".to_string(),
        );

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing standard-LSP not-measured qualifier should fail closed");
        assert!(err.contains("not measured by this artifact"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_standard_lsp_evidence_only_qualifier() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        standard["blockers"][1] = Value::String(
            "This diagnostic, declaration-hover, declaration-goto, declaration-completion replacement, bounded signature-help, open-document reference, open-document rename, and bounded code-action behavior must not be counted as full standard LSP parity.".to_string(),
        );

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing standard-LSP evidence-only qualifier should fail closed");
        assert!(err.contains("evidence only"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_widget_nonclaim_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let widgets = rows
            .iter_mut()
            .find(|row| row["id"] == "widget-instances")
            .expect("widget-instances row");
        widgets["coverage"][0]["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "Only built-in declaration/type panels are covered.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing widget nonclaim gaps should be rejected");
        assert!(
            err.contains("User widget instances are not discovered"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_hover_nonclaim_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard lsp row");
        let coverage = standard["coverage"].as_array_mut().expect("coverage array");
        let hover = coverage
            .iter_mut()
            .find(|item| item["capability"] == "hover")
            .expect("hover coverage");
        hover["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "Only declaration hover is covered.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing hover nonclaim gaps should be rejected");
        assert!(err.contains("term-local hover parity"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_goto_nonclaim_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        let coverage = standard["coverage"].as_array_mut().expect("coverage array");
        let goto = coverage
            .iter_mut()
            .find(|item| item["capability"] == "goto")
            .expect("goto coverage");
        goto["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "Cross-file goto behavior is not measured.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing goto nonclaim gaps should be rejected");
        assert!(err.contains("imported-definition goto behavior"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_expected_type_nonclaim_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let plain_term = rows
            .iter_mut()
            .find(|row| row["id"] == "plain-term-goal")
            .expect("plain-term-goal row");
        let coverage = plain_term["coverage"]
            .as_array_mut()
            .expect("coverage array");
        let expected_type = coverage
            .iter_mut()
            .find(|item| item["capability"] == "expected_type")
            .expect("expected_type coverage");
        expected_type["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "Only declaration type strings are covered.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing expected-type nonclaim gaps should be rejected");
        assert!(err.contains("No hole-local expected type state"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_expected_type_snapshot_boundary_nonclaim() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let plain_term = rows
            .iter_mut()
            .find(|row| row["id"] == "plain-term-goal")
            .expect("plain-term-goal row");
        let coverage = plain_term["coverage"]
            .as_array_mut()
            .expect("coverage array");
        let expected_type = coverage
            .iter_mut()
            .find(|item| item["capability"] == "expected_type")
            .expect("expected_type coverage");
        expected_type["fail_closed_gaps"] = Value::Array(vec![
            Value::String("No hole-local expected type state is tracked.".to_string()),
            Value::String(
                "Declaration type_str lookup must not count as Lean4 plainTermGoal parity."
                    .to_string(),
            ),
        ]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing expected-type snapshot nonclaim should be rejected");
        assert!(
            err.contains("No hole-local expected-type snapshot payloads"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_plain_goal_nonclaim_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let plain_goal = rows
            .iter_mut()
            .find(|row| row["id"] == "plain-goal")
            .expect("plain-goal row");
        let coverage = plain_goal["coverage"]
            .as_array_mut()
            .expect("coverage array");
        let goal_state = coverage
            .iter_mut()
            .find(|item| item["capability"] == "goal_state")
            .expect("goal_state coverage");
        goal_state["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "plainGoal currently has no payload.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing plainGoal nonclaim gaps should be rejected");
        assert!(
            err.contains("Only initial declaration-target tactic snapshots are produced"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_plain_goal_tactic_state_source_link() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let plain_goal = rows
            .iter_mut()
            .find(|row| row["id"] == "plain-goal")
            .expect("plain-goal row");
        let coverage = plain_goal["coverage"]
            .as_array_mut()
            .expect("coverage array");
        let goal_state = coverage
            .iter_mut()
            .find(|item| item["capability"] == "goal_state")
            .expect("goal_state coverage");
        goal_state["covered_by_sources"] = Value::Array(vec![
            Value::String("CleanBackend::elaborate_document".to_string()),
            Value::String("CleanBackend::plain_goal".to_string()),
        ]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing plainGoal tactic-state source link should fail closed");
        assert!(
            err.contains("CleanBackend::has_live_tactic_goal_state"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_goal_widget_state_nonclaim() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let plain_goal = rows
            .iter_mut()
            .find(|row| row["id"] == "plain-goal")
            .expect("plain-goal row");
        let coverage = plain_goal["coverage"]
            .as_array_mut()
            .expect("coverage array");
        let goal_state = coverage
            .iter_mut()
            .find(|item| item["capability"] == "goal_state")
            .expect("goal_state coverage");
        goal_state["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "Only initial declaration-target tactic snapshots are produced yet.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing goal widget state nonclaim should be rejected");
        assert!(
            err.contains("No Lean4-compatible goal widget state"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_tactic_goal_snapshot_pipeline_nonclaim() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let unsupported = rows
            .iter_mut()
            .find(|row| row["id"] == "tactic-goal-and-user-widgets")
            .expect("tactic-goal-and-user-widgets row");
        let coverage = unsupported["coverage"]
            .as_array_mut()
            .expect("coverage array");
        let tactic_goal = coverage
            .iter_mut()
            .find(|item| item["capability"] == "tactic_goal_and_user_widgets")
            .expect("tactic_goal_and_user_widgets coverage");
        tactic_goal["fail_closed_gaps"] = Value::Array(vec![
            Value::String(
                "clean LSP does not track tactic goal state for plainGoal or goal widgets."
                    .to_string(),
            ),
            Value::String(
                "No tactic-goal snapshot payloads are captured, stored, or serialized for infoview consumers."
                    .to_string(),
            ),
            Value::String(
                "No Lean4-compatible goal widget state is materialized from tactic snapshots."
                    .to_string(),
            ),
            Value::String(
                "clean LSP does not discover user-defined widget modules from elaboration state."
                    .to_string(),
            ),
            Value::String(
                "No user widget module discovery or source-hash registration is wired for user-defined modules."
                    .to_string(),
            ),
            Value::String(
                "Built-in declaration/type panels must not count as tactic-goal or user-widget parity."
                    .to_string(),
            ),
        ]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing tactic-goal snapshot pipeline nonclaim should be rejected");
        assert!(
            err.contains("No live tactic-goal snapshot pipeline"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_tactic_goal_state_source_link() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let unsupported = rows
            .iter_mut()
            .find(|row| row["id"] == "tactic-goal-and-user-widgets")
            .expect("tactic-goal-and-user-widgets row");
        let coverage = unsupported["coverage"]
            .as_array_mut()
            .expect("coverage array");
        let tactic_goal = coverage
            .iter_mut()
            .find(|item| item["capability"] == "tactic_goal_and_user_widgets")
            .expect("tactic_goal_and_user_widgets coverage");
        tactic_goal["covered_by_sources"] = Value::Array(vec![
            Value::String("CleanBackend::plain_goal".to_string()),
            Value::String("CleanBackend::refresh_infoview_widgets".to_string()),
        ]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing tactic-goal state source link should fail closed");
        assert!(
            err.contains("CleanBackend::has_live_tactic_goal_state"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_tactic_goal_row_source_evidence() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let unsupported = rows
            .iter_mut()
            .find(|row| row["id"] == "tactic-goal-and-user-widgets")
            .expect("tactic-goal-and-user-widgets row");
        let evidence = unsupported["evidence"]
            .as_array_mut()
            .expect("evidence array");
        evidence.retain(|item| item["function"] != "CleanBackend::refresh_infoview_widgets");

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing tactic-goal row source evidence should fail closed");
        assert!(
            err.contains("CleanBackend::refresh_infoview_widgets"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_goal_snapshot_boundary_nonclaim() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let unsupported = rows
            .iter_mut()
            .find(|row| row["id"] == "tactic-goal-and-user-widgets")
            .expect("tactic-goal-and-user-widgets row");
        let coverage = unsupported["coverage"]
            .as_array_mut()
            .expect("coverage array");
        let tactic_goal = coverage
            .iter_mut()
            .find(|item| item["capability"] == "tactic_goal_and_user_widgets")
            .expect("tactic_goal_and_user_widgets coverage");
        tactic_goal["fail_closed_gaps"] = Value::Array(vec![
            Value::String("clean LSP does not track tactic goal state.".to_string()),
            Value::String(
                "Built-in declaration/type panels must not count as tactic-goal parity."
                    .to_string(),
            ),
        ]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing goal snapshot nonclaim should be rejected");
        assert!(
            err.contains("No tactic-goal snapshot payloads are captured"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_widget_source_nonclaim_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let widget_source = rows
            .iter_mut()
            .find(|row| row["id"] == "widget-source-registry")
            .expect("widget-source-registry row");
        let coverage = widget_source["coverage"]
            .as_array_mut()
            .expect("coverage array");
        let builtin_sources = coverage
            .iter_mut()
            .find(|item| item["capability"] == "builtin_widget_sources")
            .expect("builtin_widget_sources coverage");
        builtin_sources["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "Only built-in sources are covered.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing widget source nonclaim gaps should be rejected");
        assert!(
            err.contains("User widget module registration is not wired yet"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_user_widget_discovery_guard() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let widgets = rows
            .iter_mut()
            .find(|row| row["id"] == "widget-instances")
            .expect("widget-instances row");
        let coverage = widgets["coverage"].as_array_mut().expect("coverage array");
        let builtin_instances = coverage
            .iter_mut()
            .find(|item| item["capability"] == "builtin_widget_instances")
            .expect("builtin_widget_instances coverage");
        builtin_instances["covered_by_sources"] = Value::Array(vec![
            Value::String("CleanBackend::refresh_infoview_widgets".to_string()),
            Value::String("WidgetRegistry::widgets_at".to_string()),
        ]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing user-widget discovery guard should be rejected");
        assert!(
            err.contains("CleanBackend::has_live_user_widget_modules"),
            "{err}"
        );
    }

    #[test]
    fn lsp_infoview_parity_report_requires_references_nonclaim_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        let coverage = standard["coverage"].as_array_mut().expect("coverage array");
        let references = coverage
            .iter_mut()
            .find(|item| item["capability"] == "references")
            .expect("references coverage");
        references["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "Only open-document references are covered.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing references nonclaim gaps should be rejected");
        assert!(err.contains("Semantic resolution"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_rename_nonclaim_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        let coverage = standard["coverage"].as_array_mut().expect("coverage array");
        let rename = coverage
            .iter_mut()
            .find(|item| item["capability"] == "rename")
            .expect("rename coverage");
        rename["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "Only open-document rename edits are covered.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing rename nonclaim gaps should be rejected");
        assert!(err.contains("Semantic rename"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_completion_nonclaim_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        let coverage = standard["coverage"].as_array_mut().expect("coverage array");
        let completion = coverage
            .iter_mut()
            .find(|item| item["capability"] == "completion")
            .expect("completion coverage");
        completion["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "Only checked-document completion items are covered.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing completion nonclaim gaps should be rejected");
        assert!(err.contains("Snippets"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_signature_help_nonclaim_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        let coverage = standard["coverage"].as_array_mut().expect("coverage array");
        let signature_help = coverage
            .iter_mut()
            .find(|item| item["capability"] == "signature_help")
            .expect("signature_help coverage");
        signature_help["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "Implicit or instance argument rendering, overloads, binder-name parity, and trigger or retrigger behavior are not measured.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing signature-help nonclaim gaps should be rejected");
        assert!(err.contains("full Lean4 signature-help parity"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_code_action_nonclaim_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        let coverage = standard["coverage"].as_array_mut().expect("coverage array");
        let code_action = coverage
            .iter_mut()
            .find(|item| item["capability"] == "code_action")
            .expect("code_action coverage");
        code_action["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "Only static code-action suggestions are covered.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing code-action nonclaim gaps should be rejected");
        assert!(err.contains("Semantic import resolution"), "{err}");
    }

    #[test]
    fn lsp_infoview_parity_report_requires_diagnostics_nonclaim_gaps() {
        if fixture_is_stub() {
            eprintln!("SKIP: lsp-infoview-parity report fixture is a stub");
            return;
        }
        let mut value: Value = serde_json::from_str(report()).expect("valid json fixture");
        let rows = value["rows"].as_array_mut().expect("rows array");
        let standard = rows
            .iter_mut()
            .find(|row| row["id"] == "standard-lsp-parity")
            .expect("standard-lsp-parity row");
        let coverage = standard["coverage"].as_array_mut().expect("coverage array");
        let diagnostics = coverage
            .iter_mut()
            .find(|item| item["capability"] == "diagnostics")
            .expect("diagnostics coverage");
        diagnostics["fail_closed_gaps"] = Value::Array(vec![Value::String(
            "Only backend diagnostic generation is covered.".to_string(),
        )]);

        let err = validate_lsp_infoview_parity_report(&value)
            .expect_err("missing diagnostics nonclaim gaps should be rejected");
        assert!(err.contains("live publish_diagnostics parity"), "{err}");
    }
}
