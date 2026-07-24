// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust validator for the Mathverse replay replacement report.
//!
//! This is the Rust-owned equivalent of
//! `tests/test_mathverse_replay_replacement_report.py` for the replacement gate:
//! it validates schema, scorecard scoping, evidence paths, production-corpus
//! accounting, and rejects Python wrapper references in the gate contract.

use std::fs;
use std::path::{Path, PathBuf};

use serde::Serialize;
use serde_json::Value;

use crate::replay_corpus::{build_replay_corpus_report, ReplayCorpusCounts};

/// Default mathverse replay replacement report path.
pub const DEFAULT_REPLAY_REPLACEMENT_REPORT: &str = "reports/mathverse-replay-replacement.json";

const EXPECTED_NATIVE_GATE_WITNESSES: &[&str] = &[
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:65",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:67",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:71",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:73",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:74",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:76",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:77",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:79",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:80",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:82",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:84",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:85",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:87",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:88",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:90",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:92",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:93",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:95",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:96",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:100",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:102",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:104",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:110",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:112",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:118",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:120",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:122",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:124",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:126",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:128",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:130",
    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:132",
];

/// Validation error while reading or parsing report artifacts.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ReplayReportError {
    /// Artifact read failed.
    #[error("failed to read `{path}`: {source}")]
    Io {
        /// Path being read.
        path: PathBuf,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// JSON parse failed.
    #[error("failed to parse `{path}` as JSON: {source}")]
    Json {
        /// Path being parsed.
        path: PathBuf,
        /// Underlying error.
        #[source]
        source: serde_json::Error,
    },
    /// Corpus generation failed.
    #[error(transparent)]
    Corpus(#[from] crate::replay_corpus::ReplayCorpusError),
}

/// JSON-ready validation outcome.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MathverseReplayReportValidation {
    /// Whether all checks passed.
    pub ok: bool,
    /// Validator identity.
    pub generated_by: &'static str,
    /// Report artifact path.
    pub report: String,
    /// Corpus artifact path.
    pub corpus: String,
    /// Number of checks executed.
    pub check_count: usize,
    /// Number of checks that passed.
    pub passed_count: usize,
    /// Production corpus summary seen by the validator.
    pub production_corpus: ValidatedCorpusSummary,
    /// Validation failures.
    pub errors: Vec<String>,
}

/// Production corpus summary copied into validation output.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ValidatedCorpusSummary {
    /// Found obligations.
    pub found: usize,
    /// Native-gate verified obligations.
    pub native_gate_verified: usize,
    /// Obligations applied through strict `mathverse_use`.
    pub applied_through_strict_mathverse_use: usize,
    /// Rejected obligations.
    pub rejected: usize,
    /// Unsupported obligations.
    pub unsupported: usize,
    /// Corpus status.
    pub status: String,
}

struct Validator {
    check_count: usize,
    passed_count: usize,
    errors: Vec<String>,
}

impl Validator {
    fn new() -> Self {
        Self {
            check_count: 0,
            passed_count: 0,
            errors: Vec::new(),
        }
    }

    fn check(&mut self, condition: bool, message: impl Into<String>) {
        self.check_count += 1;
        if condition {
            self.passed_count += 1;
        } else {
            self.errors.push(message.into());
        }
    }
}

/// Validate the mathverse replay replacement report and production corpus artifact.
pub fn validate_mathverse_replay_report(
    root: &Path,
    report_path: &Path,
    corpus_path: &Path,
) -> Result<MathverseReplayReportValidation, ReplayReportError> {
    let report = read_json(report_path)?;
    let corpus = read_json(corpus_path)?;
    let generated_corpus = build_replay_corpus_report(root)?;
    let mut v = Validator::new();

    v.check(
        str_at(&report, &["schema_version"]) == Some("clean-mathverse-replay-replacement-v1"),
        "report schema_version must be clean-mathverse-replay-replacement-v1",
    );
    v.check(
        str_at(&report, &["status"]) == Some("in_progress"),
        "report status must remain in_progress",
    );
    v.check(
        str_at(&report, &["replacement_row", "id"]) == Some("mathverse-replay"),
        "replacement_row.id must be mathverse-replay",
    );
    v.check(
        u64_at(&report, &["replacement_row", "issue"]) == Some(3714),
        "replacement_row.issue must be 3714",
    );
    v.check(
        str_at(
            &report,
            &["replacement_row", "recommended_scorecard_status"],
        ) == Some("in_progress"),
        "mathverse replay must stay scorecard-scoped until production replay coverage lands",
    );
    v.check(
        !contains_text(&report["gate_command"], "python3")
            && !contains_text(&report["gate_command"], "pytest")
            && contains_text(
                &report["gate_command"],
                "clean mathverse replay-corpus --production --json --output reports/mathverse-replay-production-corpus.json",
            )
            && contains_text(&report["gate_command"], "clean mathverse validate-replay-report"),
        "gate_command must use Rust mathverse replay-corpus --production --json and validate-replay-report, not Python wrappers",
    );

    let rows = report["rows"].as_array().cloned().unwrap_or_default();
    let row_count = rows.len();
    v.check(
        u64_at(&report, &["summary", "row_count"]) == Some(row_count as u64),
        "summary.row_count must match rows length",
    );
    let native_gate_count = count_tests(
        root.join("crates/clean-mathverse/tests/native_gate_integration.rs")
            .as_path(),
    )?;
    v.check(
        u64_at(&report, &["summary", "native_gate_test_count"]) == Some(native_gate_count as u64),
        "summary.native_gate_test_count must match native_gate_integration.rs",
    );
    v.check(
        native_gate_count == 76,
        "native gate integration suite should remain the fixed 76-test evidence set",
    );

    for (idx, row) in rows.iter().enumerate() {
        let id = str_at(row, &["id"]).unwrap_or("<missing>");
        let evidence = row["evidence"].as_array().cloned().unwrap_or_default();
        v.check(
            !evidence.is_empty(),
            format!("row {id} must list evidence paths"),
        );
        for evidence_path in evidence {
            let Some(path) = evidence_path.as_str() else {
                v.check(false, format!("row {id} evidence entry must be a string"));
                continue;
            };
            let path_obj = Path::new(path);
            v.check(
                !path_obj.is_absolute()
                    && !path_obj
                        .components()
                        .any(|c| matches!(c, std::path::Component::ParentDir)),
                format!("row {id} evidence path must be repo-relative and non-escaping: {path}"),
            );
            v.check(
                root.join(path_obj).exists(),
                format!("row {id} evidence path is missing: {path}"),
            );
        }
        v.check(
            str_at(row, &["status"]).is_some(),
            format!("row #{idx} ({id}) must carry status"),
        );
    }

    let report_counts = summary_counts(&report);
    let corpus_counts = corpus_counts(&corpus);
    let generated_counts = generated_corpus.counts;
    v.check(
        corpus_counts == generated_counts,
        "checked-in production corpus counts must match Rust replay-corpus generator",
    );
    v.check(
        report_counts == generated_counts,
        "report summary production_corpus counts must match Rust replay-corpus generator",
    );
    v.check(
        u64_at(&corpus, &["obligation_count"]) == Some(generated_counts.found as u64),
        "corpus obligation_count must match found count",
    );
    v.check(
        str_at(&corpus, &["generated_by"]) == Some("clean mathverse replay-corpus"),
        "production corpus generated_by must name the Rust CLI",
    );
    v.check(
        str_at(&corpus, &["status"]) == Some("incomplete"),
        "production corpus must remain incomplete until strict replay lands",
    );
    let native_gate_witnesses = corpus["native_gate_witnesses"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    v.check(
        native_gate_witnesses.len() == generated_counts.native_gate_verified,
        "native_gate_witnesses length must match native_gate_verified count",
    );
    v.check(
        native_gate_witnesses.iter().all(|witness| {
            str_at(witness, &["obligation_id"]).is_some_and(|id| {
                EXPECTED_NATIVE_GATE_WITNESSES.contains(&id)
            }) && witness
                    .get("source_line_verified")
                    .and_then(Value::as_bool)
                    == Some(true)
                    && witness
                        .get("native_gate_verified")
                        .and_then(Value::as_bool)
                        == Some(true)
                    && witness
                        .get("applied_through_strict_mathverse_use")
                        .and_then(Value::as_bool)
                        == Some(false)
        }),
        "native_gate_witnesses must contain only the bounded benchmark.lean witnesses and must not claim strict mathverse_use",
    );
    v.check(
        EXPECTED_NATIVE_GATE_WITNESSES.iter().all(|expected| {
            native_gate_witnesses
                .iter()
                .any(|witness| str_at(witness, &["obligation_id"]) == Some(*expected))
        }),
        "native_gate_witnesses must include every expected bounded benchmark witness",
    );

    let extraction_fixtures = corpus["production_extraction_fixtures"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    v.check(
        extraction_fixtures.len() == 2,
        "production_extraction_fixtures must contain the first two narrow Batteries extractor fixtures",
    );
    let expected_extractions = [
        (
            "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:65",
            "(1 : Int) < (0 : Int)",
        ),
        (
            "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:67",
            "(0 : Int) < (0 : Int)",
        ),
    ];
    v.check(
        expected_extractions
            .iter()
            .all(|(expected_id, expected_hyp)| {
                extraction_fixtures.iter().any(|extraction| {
                    str_at(extraction, &["obligation_id"]) == Some(*expected_id)
                        && str_at(extraction, &["status"])
                            == Some("extracted_fail_closed_without_strict_replay")
                        && str_at(extraction, &["clean_goal"]) == Some("False")
                        && bool_at(extraction, &["native_gate_verified"]) == Some(true)
                        && bool_at(extraction, &["applied_through_strict_mathverse_use"])
                            == Some(false)
                        && extraction["clean_local_hypotheses"]
                            .as_array()
                            .is_some_and(|hyps| {
                                hyps.iter().any(|hyp| hyp.as_str() == Some(*expected_hyp))
                            })
                })
            }),
        "production extraction fixtures must record the first two False-producing Batteries contradictions without strict mathverse_use",
    );
    v.check(
        extraction_fixtures.iter().all(|extraction| {
            str_at(extraction, &["extractor"])
                == Some("clean-mathverse batteries standalone-by-mathverse fixture extractor v1")
        }),
        "production extraction fixtures must be owned by the standalone Batteries extractor scaffold",
    );
    v.check(
        extraction_fixtures.iter().all(|extraction| {
            str_at(extraction, &["proof_state_entry_point"])
                .is_some_and(|entry| entry.contains("ProofState"))
                && str_at(extraction, &["native_mathverse_search_entry_point"])
                    .is_some_and(|entry| entry.contains("premise_select"))
                && str_at(extraction, &["native_shard_verification_entry_point"])
                    == Some("clean_mathverse::shard_verify::verify_native_shard")
                && str_at(extraction, &["strict_mathverse_use_entry_point"])
                    .is_some_and(|entry| entry.contains("mathverse_use"))
        }),
        "production extraction fixtures must name ProofState/search/native-gate/strict mathverse_use handoff points",
    );
    let expected_typed_obligations = [
        (
            "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:65",
            "(1 : Int) < (0 : Int)",
        ),
        (
            "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:67",
            "(0 : Int) < (0 : Int)",
        ),
    ];
    v.check(
        expected_typed_obligations.iter().all(|(expected_id, expected_hyp)| {
            extraction_fixtures.iter().any(|extraction| {
                str_at(extraction, &["obligation_id"]) == Some(*expected_id)
                    && str_at(extraction, &["typed_obligation_status"])
                        == Some("typed_internal_obligation_constructed_fail_closed")
                    && str_at(&extraction["typed_internal_obligation"], &["obligation_id"])
                        == Some(*expected_id)
                    && str_at(&extraction["typed_internal_obligation"], &["adapter"])
                        == Some("clean-mathverse production fixture typed-obligation adapter v1")
                    && str_at(&extraction["typed_internal_obligation"], &["goal_sort"])
                        == Some("Prop")
                    && str_at(&extraction["typed_internal_obligation"], &["goal_expr"])
                        == Some("False")
                    && bool_at(
                        &extraction["typed_internal_obligation"],
                        &["proof_state_constructed"],
                    ) == Some(false)
                    && bool_at(
                        &extraction["typed_internal_obligation"],
                        &["strict_replay_ready"],
                    ) == Some(false)
                    && extraction["typed_internal_obligation"]["local_hypotheses"]
                        .as_array()
                        .is_some_and(|hyps| {
                            hyps.len() == 1
                                && str_at(&hyps[0], &["sort"]) == Some("Prop")
                                && str_at(&hyps[0], &["expr"]) == Some(*expected_hyp)
                        })
            })
        }),
        "production extraction fixtures must construct typed internal obligations and remain fail-closed",
    );
    let line65_search = extraction_fixtures.iter().find(|extraction| {
        str_at(&extraction["typed_internal_obligation"], &["obligation_id"])
            == Some(
                "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:65",
            )
    });
    v.check(
        line65_search.is_some_and(|extraction| {
            let attempt = &extraction["typed_internal_obligation"]["native_search_attempt"];
            str_at(attempt, &["obligation_id"])
                == Some(
                    "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:65",
                )
                && str_at(attempt, &["runner"])
                    == Some("clean-mathverse typed production native search adapter v1")
                && str_at(attempt, &["status"])
                    == Some("native_candidate_selected_without_verification")
                && str_at(attempt, &["goal_text"]) == Some("False (1 : Int) < (0 : Int)")
                && bool_at(attempt, &["native_search_invoked"]) == Some(true)
                && u64_at(attempt, &["candidate_count"]) == Some(1)
                && str_at(attempt, &["selected_native_declaration"])
                    == Some("clean.Mathverse.Production.BatteriesBenchmark.line65.nativeGateWitness")
                && str_at(attempt, &["selected_native_shard"])
                    == Some("bounded-native-gate-witness:BatteriesBenchmark.line65")
                && str_at(attempt, &["native_shard_verification_status"])
                    == Some("verified_native_shard")
                && str_at(
                    &attempt["native_shard_verifier_input"],
                    &["input_kind"],
                ) == Some("bounded_native_gate_witness_verifier_input")
                && str_at(
                    &attempt["native_shard_verifier_input"],
                    &["verifier_entry_point"],
                ) == Some("clean_mathverse::shard_verify::verify_native_shard")
                && str_at(
                    &attempt["native_shard_verifier_input"],
                    &["native_declaration"],
                ) == Some("clean.Mathverse.Production.BatteriesBenchmark.line65.nativeGateWitness")
                && str_at(
                    &attempt["native_shard_verifier_input"],
                    &["expected_source_system"],
                ) == Some("CleanNative")
                && str_at(
                    &attempt["native_shard_verifier_input"],
                    &["expected_import_confidence"],
                ) == Some("KernelVerified")
                && str_at(
                    &attempt["native_shard_verifier_input"],
                    &["serialized_shard_path"],
                ) == Some("crates/clean-mathverse/tests/fixtures/mathverse-replay/line65-clean-native.mathverse")
                && bool_at(
                    &attempt["native_shard_verifier_input"],
                    &["serialized_shard_path_exists"],
                ) == Some(true)
                && attempt["candidate_sources"]
                    .as_array()
                    .is_some_and(|sources| {
                        sources.len() == 1
                            && str_at(&sources[0], &["source_kind"])
                                == Some("bounded_native_gate_witness")
                            && str_at(&sources[0], &["native_declaration"])
                                == Some(
                                    "clean.Mathverse.Production.BatteriesBenchmark.line65.nativeGateWitness",
                                )
                            && str_at(&sources[0], &["native_shard"])
                                == Some("bounded-native-gate-witness:BatteriesBenchmark.line65")
                            && bool_at(&sources[0], &["native_shard_verified"]) == Some(true)
                    })
                && bool_at(attempt, &["native_shard_verification_attempted"]) == Some(true)
                && bool_at(attempt, &["native_shard_verified"]) == Some(true)
                && str_at(&attempt["proof_state_bridge_attempt"], &["bridge"])
                    == Some("clean-mathverse verified-shard to elaborator ProofState bridge v1")
                && str_at(&attempt["proof_state_bridge_attempt"], &["status"])
                    == Some("blocked_missing_elaborator_proof_state")
                && str_at(&attempt["proof_state_bridge_attempt"], &["goal_sort"]) == Some("Prop")
                && str_at(&attempt["proof_state_bridge_attempt"], &["goal_expr"]) == Some("False")
                && str_at(
                    &attempt["proof_state_bridge_attempt"],
                    &["selected_native_declaration"],
                ) == Some("clean.Mathverse.Production.BatteriesBenchmark.line65.nativeGateWitness")
                && bool_at(
                    &attempt["proof_state_bridge_attempt"],
                    &["native_shard_verified"],
                ) == Some(true)
                && bool_at(
                    &attempt["proof_state_bridge_attempt"],
                    &["proof_state_constructed"],
                ) == Some(false)
                && bool_at(
                    &attempt["proof_state_bridge_attempt"],
                    &["strict_mathverse_use_closed"],
                ) == Some(false)
                && bool_at(
                    &attempt["proof_state_bridge_attempt"],
                    &["semantic_goal_matches_selected_native_shard"],
                ) == Some(false)
                && str_at(
                    &attempt["proof_state_bridge_attempt"],
                    &["required_proof_state_constructor"],
                ) == Some("clean_elab::tactic::ProofState::with_context")
                && str_at(
                    &attempt["proof_state_bridge_attempt"],
                    &["required_target_expr"],
                ) == Some("clean_kernel::Expr::const_(Name::from_string(\"False\"), vec![])")
                && str_at(
                    &attempt["proof_state_bridge_attempt"],
                    &["required_local_decl"],
                )
                .is_some_and(|decl| decl.contains("elaborated `(1 : Int) < (0 : Int)`"))
                && str_at(
                    &attempt["proof_state_bridge_attempt"],
                    &["required_strict_tactic_entry_point"],
                )
                .is_some_and(|entry| entry.contains("strict evaluator"))
                && contains_text(
                    &attempt["proof_state_bridge_attempt"]["available_elab_surfaces"],
                    "ProofState::with_context",
                )
                && contains_text(
                    &attempt["proof_state_bridge_attempt"]["available_elab_surfaces"],
                    "set_mathverse_library",
                )
                && contains_text(
                    &attempt["proof_state_bridge_attempt"]["available_elab_surfaces"],
                    "run_strict_mathverse_use",
                )
                && contains_text(
                    &attempt["proof_state_bridge_attempt"]["missing_elab_surfaces"],
                    "kernel Expr lowering",
                )
                && contains_text(
                    &attempt["proof_state_bridge_attempt"]["missing_elab_surfaces"],
                    "integration-layer runner",
                )
                && contains_text(
                    &attempt["proof_state_bridge_attempt"]["missing_elab_surfaces"],
                    "matches the production goal False",
                )
                && str_at(
                    &attempt["proof_state_bridge_attempt"]["strict_replay_runner_attempt"],
                    &["runner"],
                ) == Some("clean-mathverse line65 strict replay runner prototype contract v1")
                && str_at(
                    &attempt["proof_state_bridge_attempt"]["strict_replay_runner_attempt"],
                    &["status"],
                ) == Some("blocked_before_proof_state_construction")
                && str_at(
                    &attempt["proof_state_bridge_attempt"]["strict_replay_runner_attempt"],
                    &["required_runner_owner"],
                ) == Some("clean-cli integration layer")
                && bool_at(
                    &attempt["proof_state_bridge_attempt"]["strict_replay_runner_attempt"],
                    &["mathverse_to_elab_dependency_allowed"],
                ) == Some(false)
                && str_at(
                    &attempt["proof_state_bridge_attempt"]["strict_replay_runner_attempt"],
                    &["first_blocking_step"],
                ) == Some("lower_typed_production_fixture_to_kernel_exprs")
                && bool_at(
                    &attempt["proof_state_bridge_attempt"]["strict_replay_runner_attempt"],
                    &["target_expr_lowered"],
                ) == Some(false)
                && bool_at(
                    &attempt["proof_state_bridge_attempt"]["strict_replay_runner_attempt"],
                    &["local_decls_lowered"],
                ) == Some(false)
                && bool_at(
                    &attempt["proof_state_bridge_attempt"]["strict_replay_runner_attempt"],
                    &["proof_state_constructed"],
                ) == Some(false)
                && bool_at(
                    &attempt["proof_state_bridge_attempt"]["strict_replay_runner_attempt"],
                    &["mathverse_library_loaded"],
                ) == Some(false)
                && bool_at(
                    &attempt["proof_state_bridge_attempt"]["strict_replay_runner_attempt"],
                    &["strict_mathverse_use_invoked"],
                ) == Some(false)
                && bool_at(
                    &attempt["proof_state_bridge_attempt"]["strict_replay_runner_attempt"],
                    &["strict_mathverse_use_closed"],
                ) == Some(false)
                && attempt["proof_state_bridge_attempt"]["strict_replay_runner_attempt"]["steps"]
                    .as_array()
                    .is_some_and(|steps| {
                        steps.len() == 6
                            && str_at(&steps[0], &["step"]) == Some("lower_target_expr")
                            && str_at(&steps[0], &["status"])
                                == Some("blocked_missing_fixture_to_kernel_expr_lowerer")
                            && str_at(&steps[4], &["step"]) == Some("invoke_strict_mathverse_use")
                            && str_at(&steps[4], &["status"])
                                == Some("not_attempted_until_proof_state_exists")
                            && str_at(&steps[4], &["required_boundary"])
                                .is_some_and(|boundary| boundary.contains("run_strict_mathverse_use"))
                    })
                && attempt["proof_state_bridge_attempt"]["local_hypotheses"]
                    .as_array()
                    .is_some_and(|hyps| {
                        hyps.len() == 1
                            && str_at(&hyps[0], &["sort"]) == Some("Prop")
                            && str_at(&hyps[0], &["expr"]) == Some("(1 : Int) < (0 : Int)")
                    })
                && contains_text(
                    &attempt["proof_state_bridge_attempt"]["fail_closed_reasons"],
                    "ProofState",
                )
                && contains_text(
                    &attempt["proof_state_bridge_attempt"]["fail_closed_reasons"],
                    "goal False",
                )
                && contains_text(
                    &attempt["proof_state_bridge_attempt"]["fail_closed_reasons"],
                    "metavariable target",
                )
                && bool_at(attempt, &["proof_state_constructed"]) == Some(false)
                && bool_at(attempt, &["strict_mathverse_use_closed"]) == Some(false)
                && bool_at(attempt, &["strict_replay_ready"]) == Some(false)
                && contains_text(&attempt["fail_closed_reasons"], "native verifier input")
                && contains_text(&attempt["fail_closed_reasons"], "verification alone")
                && contains_text(&attempt["fail_closed_reasons"], "ProofState")
        }),
        "line65 typed obligation must expose a fail-closed native search attempt",
    );
    v.check(
        extraction_fixtures.iter().any(|extraction| {
            str_at(extraction, &["obligation_id"])
                == Some("data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:67")
                && extraction["typed_internal_obligation"]["native_search_attempt"].is_null()
        }),
        "line67 typed obligation must not claim a native search attempt yet",
    );
    v.check(
        extraction_fixtures.iter().all(|extraction| {
            contains_text(&extraction["required_for_strict_credit"], "ProofState")
                && contains_text(&extraction["required_for_strict_credit"], "premise_select")
                && contains_text(
                    &extraction["required_for_strict_credit"],
                    "verify_native_shard",
                )
                && contains_text(&extraction["required_for_strict_credit"], "strict mathverse_use")
        }),
        "production extraction fixture must remain fail-closed on ProofState/search/strict mathverse_use requirements",
    );

    let replay_smoke_attempts = corpus["replay_smoke"]["attempts"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let strict_replay_attempted = replay_smoke_attempts
        .iter()
        .filter(|attempt| bool_at(attempt, &["strict_replay_attempted"]) == Some(true))
        .count();
    let strict_mathverse_use_applied = replay_smoke_attempts
        .iter()
        .filter(|attempt| bool_at(attempt, &["applied_through_strict_mathverse_use"]) == Some(true))
        .count();
    v.check(
        u64_at(&corpus, &["replay_smoke", "strict_replay_attempted"])
            == Some(strict_replay_attempted as u64),
        "replay_smoke.strict_replay_attempted must match sampled strict replay attempts",
    );
    v.check(
        u64_at(
            &corpus,
            &["replay_smoke", "applied_through_strict_mathverse_use"],
        ) == Some(strict_mathverse_use_applied as u64),
        "replay_smoke.applied_through_strict_mathverse_use must match sampled strict applications",
    );
    v.check(
        generated_counts.applied_through_strict_mathverse_use == strict_mathverse_use_applied,
        "production strict mathverse_use count must equal replay-smoke strict applications",
    );
    v.check(
        replay_smoke_attempts
            .iter()
            .filter(|attempt| bool_at(attempt, &["applied_through_strict_mathverse_use"]) == Some(true))
            .all(|attempt| {
                bool_at(attempt, &["strict_replay_attempted"]) == Some(true)
                    && bool_at(attempt, &["native_gate_verified"]) == Some(true)
                    && bool_at(attempt, &["native_gate_attempted"]) == Some(true)
            }),
        "strict mathverse_use credit requires strict replay attempted plus native-gate verification",
    );

    let focused_validation = report["focused_validation"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let focused_commands = focused_validation
        .iter()
        .filter_map(|entry| str_at(entry, &["command"]))
        .collect::<Vec<_>>();
    v.check(
        focused_commands.iter().any(|cmd| {
            *cmd == "clean mathverse replay-corpus --production --json --output reports/mathverse-replay-production-corpus.json"
        }),
        "focused_validation must include clean mathverse replay-corpus --production --json",
    );
    v.check(
        focused_commands
            .iter()
            .any(|cmd| cmd.starts_with("clean mathverse validate-replay-report")),
        "focused_validation must include clean mathverse validate-replay-report",
    );
    v.check(
        focused_commands
            .iter()
            .all(|cmd| !cmd.contains("python3") && !cmd.contains("pytest")),
        "focused_validation must not depend on Python wrappers",
    );

    let summary = ValidatedCorpusSummary {
        found: generated_counts.found,
        native_gate_verified: generated_counts.native_gate_verified,
        applied_through_strict_mathverse_use: generated_counts.applied_through_strict_mathverse_use,
        rejected: generated_counts.rejected,
        unsupported: generated_counts.unsupported,
        status: str_at(&corpus, &["status"])
            .unwrap_or("<missing>")
            .to_owned(),
    };

    Ok(MathverseReplayReportValidation {
        ok: v.errors.is_empty(),
        generated_by: "clean mathverse validate-replay-report",
        report: report_path.display().to_string(),
        corpus: corpus_path.display().to_string(),
        check_count: v.check_count,
        passed_count: v.passed_count,
        production_corpus: summary,
        errors: v.errors,
    })
}

fn read_json(path: &Path) -> Result<Value, ReplayReportError> {
    let text = fs::read_to_string(path).map_err(|source| ReplayReportError::Io {
        path: path.to_path_buf(),
        source,
    })?;
    serde_json::from_str(&text).map_err(|source| ReplayReportError::Json {
        path: path.to_path_buf(),
        source,
    })
}

fn count_tests(path: &Path) -> Result<usize, ReplayReportError> {
    let text = fs::read_to_string(path).map_err(|source| ReplayReportError::Io {
        path: path.to_path_buf(),
        source,
    })?;
    Ok(text.lines().filter(|line| line.trim() == "#[test]").count())
}

fn str_at<'a>(value: &'a Value, path: &[&str]) -> Option<&'a str> {
    let mut current = value;
    for key in path {
        current = current.get(*key)?;
    }
    current.as_str()
}

fn u64_at(value: &Value, path: &[&str]) -> Option<u64> {
    let mut current = value;
    for key in path {
        current = current.get(*key)?;
    }
    current.as_u64()
}

fn bool_at(value: &Value, path: &[&str]) -> Option<bool> {
    let mut current = value;
    for key in path {
        current = current.get(*key)?;
    }
    current.as_bool()
}

fn contains_text(value: &Value, needle: &str) -> bool {
    match value {
        Value::String(text) => text.contains(needle),
        Value::Array(values) => values.iter().any(|value| contains_text(value, needle)),
        Value::Object(map) => map.values().any(|value| contains_text(value, needle)),
        _ => false,
    }
}

fn summary_counts(report: &Value) -> ReplayCorpusCounts {
    ReplayCorpusCounts {
        found: u64_at(report, &["summary", "production_corpus", "found"]).unwrap_or(0) as usize,
        native_gate_verified: u64_at(
            report,
            &["summary", "production_corpus", "native_gate_verified"],
        )
        .unwrap_or(0) as usize,
        applied_through_strict_mathverse_use: u64_at(
            report,
            &[
                "summary",
                "production_corpus",
                "applied_through_strict_mathverse_use",
            ],
        )
        .unwrap_or(0) as usize,
        rejected: u64_at(report, &["summary", "production_corpus", "rejected"]).unwrap_or(0)
            as usize,
        unsupported: u64_at(report, &["summary", "production_corpus", "unsupported"]).unwrap_or(0)
            as usize,
    }
}

fn corpus_counts(corpus: &Value) -> ReplayCorpusCounts {
    ReplayCorpusCounts {
        found: u64_at(corpus, &["counts", "found"]).unwrap_or(0) as usize,
        native_gate_verified: u64_at(corpus, &["counts", "native_gate_verified"]).unwrap_or(0)
            as usize,
        applied_through_strict_mathverse_use: u64_at(
            corpus,
            &["counts", "applied_through_strict_mathverse_use"],
        )
        .unwrap_or(0) as usize,
        rejected: u64_at(corpus, &["counts", "rejected"]).unwrap_or(0) as usize,
        unsupported: u64_at(corpus, &["counts", "unsupported"]).unwrap_or(0) as usize,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn repo_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("repo root")
            .to_path_buf()
    }

    #[test]
    fn mathverse_replay_replacement_report_matches_rust_contract() {
        let root = repo_root();
        // Requires the checked-in replacement-report JSON AND the
        // production corpus JSON, both built by an external pipeline
        // and not always present on this machine.
        let replacement = root.join(DEFAULT_REPLAY_REPLACEMENT_REPORT);
        let corpus = root.join(crate::replay_corpus::DEFAULT_REPLAY_CORPUS_OUTPUT);
        // validate_mathverse_replay_report also needs the upstream mathlib4
        // source tree to resolve corpus paths. On a fresh checkout that's
        // not present — SKIP rather than fail.
        let mathlib4 = root.join("data/raw/mathlib4/Mathlib");
        let batteries =
            root.join("data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse");
        if !replacement.exists() || !corpus.exists() || !mathlib4.exists() || !batteries.exists() {
            eprintln!(
                "SKIP: replacement-report, production-corpus JSON, \
                 data/raw/mathlib4/Mathlib, or batteries replay corpus not present"
            );
            return;
        }
        let validation = validate_mathverse_replay_report(&root, &replacement, &corpus)
            .expect("validate report");

        assert!(validation.ok, "{:?}", validation.errors);
        assert!(validation.check_count >= 20);
        assert_eq!(validation.check_count, validation.passed_count);
        assert_eq!(validation.production_corpus.found, 202);
        assert_eq!(validation.production_corpus.native_gate_verified, 32);
        assert_eq!(
            validation
                .production_corpus
                .applied_through_strict_mathverse_use,
            0
        );
    }
}
