// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guards the #3711 tactic parity matrix metadata against drifting away from
//! the tactic proof-carry/fallback tests that back the replacement scorecard.

use std::path::{Path, PathBuf};

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

const REQUIRED_ROWS: &[(&str, &str, bool, &[&str])] = &[
    (
        "simp",
        "proof-carrying",
        false,
        &[
            "crates/clean-elab/src/tactic/tests/simp_proof_carry.rs",
            "crates/clean-elab/src/tactic/tests/sorry_absence/simp.rs",
            "crates/clean-elab/src/tactic/tests/tactic_parity_registry.rs",
        ],
    ),
    (
        "ring",
        "proof-carrying",
        false,
        &[
            "crates/clean-elab/src/tactic/tests/ring_proof_carry.rs",
            "crates/clean-elab/src/tactic/tests/ring_kernel_proof.rs",
        ],
    ),
    (
        "mathverse",
        "proof-carrying",
        false,
        &[
            "crates/clean-elab/src/tactic/tests/mathverse_proof_carry.rs",
            "crates/clean-elab/src/tactic/tests/sorry_absence/mathverse.rs",
            "crates/clean-elab/src/tactic/tests/certified_arithmetic_fail_closed.rs",
        ],
    ),
    (
        "linarith",
        "proof-carrying",
        true,
        &[
            "crates/clean-elab/src/tactic/tests/linarith_proof_type/term_soundness.rs",
            "crates/clean-elab/src/tactic/tests/linarith_real_proof_carry.rs",
        ],
    ),
    (
        "nlinarith",
        "proof-carrying",
        false,
        &[
            "crates/clean-elab/src/tactic/tests/nlinarith_proof_carry.rs",
            "crates/clean-elab/src/tactic/arith_nlinarith/certified.rs",
        ],
    ),
    (
        "ay-strict-qf-uf",
        "strict-zero-trust",
        true,
        &[
            "crates/clean-elab/src/tactic/smt/ay_tactics_tests.rs",
            "crates/clean-elab/src/tactic/tests/ay_smt/trusted_counter.rs",
        ],
    ),
    (
        "trusted-fallback-sites",
        "fallback-classified",
        false,
        &[
            "crates/clean-elab/src/tactic/tests/trusted_axiom_fallback_sites.rs",
            "crates/clean-elab/src/tactic/tests/trusted_axiom_state.rs",
        ],
    ),
];

struct ExecutableCheckSpec {
    tactic: &'static str,
    id: &'static str,
    source: &'static str,
    module_path: &'static str,
    test_fn: &'static str,
}

const HIGH_VALUE_EXECUTABLE_CHECKS: &[ExecutableCheckSpec] = &[
    ExecutableCheckSpec {
        tactic: "simp",
        id: "simp-proof-carry",
        source: "crates/clean-elab/src/tactic/tests/simp_proof_carry.rs",
        module_path: "tactic::tests::simp_proof_carry::test_simp_transitivity_chain_no_trusted_arith",
        test_fn: "test_simp_transitivity_chain_no_trusted_arith",
    },
    ExecutableCheckSpec {
        tactic: "simp",
        id: "simp-all-opaque-fail-closed",
        source: "crates/clean-elab/src/tactic/tests/tactic_parity_registry.rs",
        module_path: "tactic::tests::tactic_parity_registry::test_tactic_parity_simp_lane_executable_fixture_fails_closed_without_fallback",
        test_fn: "test_tactic_parity_simp_lane_executable_fixture_fails_closed_without_fallback",
    },
    ExecutableCheckSpec {
        tactic: "rw",
        id: "rw-checked-rewrite",
        source: "crates/clean-elab/src/tactic/tests/conv_proof_carry.rs",
        module_path: "tactic::tests::conv_proof_carry::test_conv_rw_direct_path_uses_checked_rewrite",
        test_fn: "test_conv_rw_direct_path_uses_checked_rewrite",
    },
    ExecutableCheckSpec {
        tactic: "rw",
        id: "rw-parity-fixture",
        source: "crates/clean-elab/src/tactic/tests/tactic_parity_registry.rs",
        module_path: "tactic::tests::tactic_parity_registry::test_tactic_parity_rw_lane_executable_fixture_closes_without_fallback",
        test_fn: "test_tactic_parity_rw_lane_executable_fixture_closes_without_fallback",
    },
    ExecutableCheckSpec {
        tactic: "ring",
        id: "ring-parity-fixture",
        source: "crates/clean-elab/src/tactic/tests/tactic_parity_registry.rs",
        module_path: "tactic::tests::tactic_parity_registry::test_tactic_parity_ring_lane_executable_fixture_closes_without_fallback",
        test_fn: "test_tactic_parity_ring_lane_executable_fixture_closes_without_fallback",
    },
    ExecutableCheckSpec {
        tactic: "norm_num",
        id: "norm-num-fail-closed",
        source: "crates/clean-elab/src/tactic/tests/advanced/algebraic_reasoning_ext.rs",
        module_path: "tactic::tests::advanced::algebraic_reasoning_ext::test_norm_num_at_fails_closed_on_non_defeq_rewrite",
        test_fn: "test_norm_num_at_fails_closed_on_non_defeq_rewrite",
    },
    ExecutableCheckSpec {
        tactic: "mathverse",
        id: "mathverse-proof-carry",
        source: "crates/clean-elab/src/tactic/tests/mathverse_proof_carry.rs",
        module_path: "tactic::tests::mathverse_proof_carry::test_mathverse_avoids_trusted_arith_on_contradictory_nat_le",
        test_fn: "test_mathverse_avoids_trusted_arith_on_contradictory_nat_le",
    },
    ExecutableCheckSpec {
        tactic: "mathverse",
        id: "mathverse-certified-arithmetic-fail-closed",
        source: "crates/clean-elab/src/tactic/tests/certified_arithmetic_fail_closed.rs",
        module_path: "tactic::tests::certified_arithmetic_fail_closed::test_mathverse_certified_arithmetic_fail_closed_without_trusted_axioms",
        test_fn: "test_mathverse_certified_arithmetic_fail_closed_without_trusted_axioms",
    },
    ExecutableCheckSpec {
        tactic: "linarith",
        id: "linarith-proof-carry",
        source: "crates/clean-elab/src/tactic/tests/linarith_proof_type/term_soundness.rs",
        module_path: "tactic::tests::linarith_proof_type::term_soundness::test_linarith_end_to_end_no_trusted_arith_fallback",
        test_fn: "test_linarith_end_to_end_no_trusted_arith_fallback",
    },
    ExecutableCheckSpec {
        tactic: "nlinarith",
        id: "nlinarith-certified-unsat-fail-closed",
        source: "crates/clean-elab/src/tactic/tests/nlinarith_proof_carry.rs",
        module_path: "tactic::tests::nlinarith_proof_carry::test_certified_nlinarith_outcome_distinguishes_fail_closed_unsat",
        test_fn: "test_certified_nlinarith_outcome_distinguishes_fail_closed_unsat",
    },
];

#[derive(Debug, Clone, Copy)]
struct MatrixRow<'a> {
    tactic: &'a str,
    proof_behavior: &'a str,
    fallback_behavior: &'a str,
    fully_verified_gate: bool,
    block: &'a str,
}

impl MatrixRow<'_> {
    fn has_executable_checks(self) -> bool {
        self.block
            .lines()
            .any(|line| line.trim() == "executable_checks:")
    }
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn read_repo_file(path: &str) -> String {
    std::fs::read_to_string(repo_root().join(path))
        .unwrap_or_else(|err| panic!("failed to read {path}: {err}"))
}

/// Load the canonical, committed tactic-parity matrix fixture, panicking if it
/// is absent. The fixture (`evals/registry/tactic-parity.yaml`) plus its source
/// corpora are committed deterministic data that these guards exist to police,
/// so a missing fixture is a real regression — it must FAIL LOUD, never skip.
/// (A previous skip-on-missing variant let ~12 of these guards report PASSED
/// while asserting nothing; that false assurance is exactly what this guard
/// must not allow.)
macro_rules! tactic_parity_source {
    () => {
        $crate::tactic::tests::tactic_parity_registry::read_repo_file(
            "evals/registry/tactic-parity.yaml",
        )
    };
}

fn row_block<'a>(source: &'a str, tactic: &str) -> &'a str {
    let marker = format!("    - tactic: {tactic}");
    let start = source
        .find(&marker)
        .unwrap_or_else(|| panic!("tactic-parity matrix is missing row {tactic}"));
    let tail = &source[start..];
    let next = tail[marker.len()..]
        .find("\n    - tactic: ")
        .map(|idx| marker.len() + idx)
        .unwrap_or(tail.len());
    &tail[..next]
}

fn yaml_field<'a>(block: &'a str, field: &str) -> &'a str {
    let prefix = format!("{field}: ");
    block
        .lines()
        .map(str::trim)
        .find_map(|line| line.strip_prefix(&prefix))
        .unwrap_or_else(|| panic!("matrix row is missing {field}: {block}"))
}

fn yaml_bool_field(block: &str, field: &str) -> bool {
    match yaml_field(block, field) {
        "true" => true,
        "false" => false,
        value => panic!("{field} must be true/false, got {value:?} in {block}"),
    }
}

fn matrix_rows(source: &str) -> Vec<MatrixRow<'_>> {
    let matrix = source
        .split_once("  tactic_matrix:\n")
        .expect("tactic-parity eval must define inputs.tactic_matrix")
        .1
        .split_once("\nmetrics:")
        .expect("tactic-parity eval must define metrics after tactic_matrix")
        .0;

    matrix
        .split("    - tactic: ")
        .skip(1)
        .map(|block| MatrixRow {
            tactic: block
                .lines()
                .next()
                .expect("matrix row must start with tactic")
                .trim(),
            proof_behavior: yaml_field(block, "proof_behavior"),
            fallback_behavior: yaml_field(block, "fallback_behavior"),
            fully_verified_gate: yaml_bool_field(block, "fully_verified_gate"),
            block,
        })
        .collect()
}

fn assert_metric_present(source: &str, metric: &str) {
    assert!(
        source.contains(&format!("  - {metric}\n")),
        "tactic-parity metrics must include {metric}"
    );
}

fn generated_count_manifest_section(source: &str) -> &str {
    source
        .split_once("  generated_count_manifests:\n")
        .expect("tactic-parity eval must define inputs.generated_count_manifests")
        .1
        .split_once("\n  issue_refs:")
        .expect("generated_count_manifests must be followed by issue_refs")
        .0
}

fn generated_count_manifest_blocks(source: &str) -> Vec<&str> {
    generated_count_manifest_section(source)
        .split("    - tactic_lane: ")
        .skip(1)
        .collect()
}

fn generated_count_manifest_block<'a>(source: &'a str, tactic_lane: &str) -> &'a str {
    let section = generated_count_manifest_section(source);
    let marker = format!("    - tactic_lane: {tactic_lane}");
    let start = section
        .find(&marker)
        .unwrap_or_else(|| panic!("generated-count manifests are missing lane {tactic_lane}"));
    let tail = &section[start..];
    let next = tail[marker.len()..]
        .find("\n    - tactic_lane: ")
        .map(|idx| marker.len() + idx)
        .unwrap_or(tail.len());
    &tail[..next]
}

fn generated_lean4_vs_clean_count_buckets(source: &str) -> usize {
    generated_count_manifest_blocks(source)
        .into_iter()
        .filter(|manifest| yaml_bool_field(manifest, "generated"))
        .count()
}

fn generated_count_runner_artifact_candidates(expected_artifact_path: &str) -> Vec<PathBuf> {
    let (base_dir, run_scoped_suffix) = expected_artifact_path
        .split_once("/{run_id}/")
        .unwrap_or_else(|| panic!("generated-count artifact path must be run-scoped"));
    let root = repo_root().join(base_dir);
    if !root.exists() {
        return Vec::new();
    }

    std::fs::read_dir(&root)
        .unwrap_or_else(|err| {
            panic!("failed to scan generated-count artifact root {root:?}: {err}")
        })
        .filter_map(Result::ok)
        .map(|entry| entry.path().join(run_scoped_suffix))
        .filter(|candidate| candidate.exists())
        .collect()
}

fn generated_count_runner_artifact_contract_section(source: &str) -> &str {
    source
        .split_once("  generated_count_runner_artifact_contract:\n")
        .expect("tactic-parity eval must define inputs.generated_count_runner_artifact_contract")
        .1
        .split_once("\n  generated_count_manifests:")
        .expect("generated_count_runner_artifact_contract must precede generated_count_manifests")
        .0
}

fn generated_count_runner_dry_run_artifact(
    tactic_lane: &str,
    runner_path: &str,
) -> serde_json::Value {
    let output = std::process::Command::new("python3")
        .current_dir(repo_root())
        .arg(runner_path)
        .arg("--lane")
        .arg(tactic_lane)
        .arg("--dry-run")
        .output()
        .unwrap_or_else(|err| {
            panic!("failed to run generated-count runner for {tactic_lane}: {err}")
        });
    assert!(
        output.status.success(),
        "generated-count runner dry-run failed for {tactic_lane}: status={:?}, stderr={}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap_or_else(|err| {
        panic!(
            "generated-count runner dry-run for {tactic_lane} did not emit JSON: {err}; stdout={}",
            String::from_utf8_lossy(&output.stdout)
        )
    })
}

fn assert_generated_count_dry_run_artifact(
    artifact: &serde_json::Value,
    tactic_lane: &str,
    source_corpus_path: &str,
    expected_case_ids: &[&str],
) {
    for required_field in [
        "schema_version",
        "tactic_lane",
        "run_id",
        "cases_total",
        "lean4_successes",
        "clean_successes",
        "matched_successes",
        "source_corpus_path",
        "source_corpus_sha256",
        "artifact_status",
        "dry_run",
        "case_ids",
    ] {
        assert!(
            artifact.get(required_field).is_some(),
            "{tactic_lane} generated-count dry-run artifact is missing {required_field}"
        );
    }
    assert_eq!(
        artifact
            .get("schema_version")
            .and_then(serde_json::Value::as_str),
        Some("clean-tactic-generated-count-runner-artifact-v1"),
        "{tactic_lane} generated-count dry-run artifact must self-identify the contract"
    );
    assert_eq!(
        artifact
            .get("tactic_lane")
            .and_then(serde_json::Value::as_str),
        Some(tactic_lane)
    );
    assert_eq!(
        artifact
            .get("source_corpus_path")
            .and_then(serde_json::Value::as_str),
        Some(source_corpus_path)
    );
    assert_eq!(
        artifact
            .get("cases_total")
            .and_then(serde_json::Value::as_u64),
        Some(expected_case_ids.len() as u64),
        "{tactic_lane} generated-count dry-run artifact must count source corpus cases"
    );
    for empty_count_field in ["lean4_successes", "clean_successes", "matched_successes"] {
        assert!(
            matches!(artifact.get(empty_count_field), Some(value) if value.is_null()),
            "{tactic_lane} dry-run artifact must not mark {empty_count_field} present"
        );
    }
    assert_eq!(
        artifact
            .get("artifact_status")
            .and_then(serde_json::Value::as_str),
        Some("fail-closed-missing-lean4-runner-artifact")
    );
    assert_eq!(
        artifact.get("dry_run").and_then(serde_json::Value::as_bool),
        Some(true)
    );
    let actual_case_ids: Vec<&str> = artifact
        .get("case_ids")
        .and_then(serde_json::Value::as_array)
        .unwrap_or_else(|| panic!("{tactic_lane} dry-run artifact case_ids must be an array"))
        .iter()
        .map(|case_id| {
            case_id.as_str().unwrap_or_else(|| {
                panic!("{tactic_lane} dry-run artifact case_ids must contain strings")
            })
        })
        .collect();
    assert_eq!(
        actual_case_ids, expected_case_ids,
        "{tactic_lane} dry-run artifact case_ids must track the source corpus order"
    );
    assert_eq!(
        artifact
            .get("source_corpus_sha256")
            .and_then(serde_json::Value::as_str)
            .map(str::len),
        Some(64),
        "{tactic_lane} dry-run artifact must include a sha256 source corpus digest"
    );
}

fn parity_nat_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), lhs),
        rhs,
    )
}

fn parity_nat_mul(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.mul"), vec![]), lhs),
        rhs,
    )
}

fn parity_nat_zero() -> Expr {
    Expr::const_(Name::from_string("Nat.zero"), vec![])
}

fn parity_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

#[derive(Clone, Copy)]
struct RwFixtureRow {
    id: &'static str,
    reverse: bool,
    target_lhs: &'static str,
    target_rhs: &'static str,
}

fn parity_ring_env() -> (Environment, Expr) {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas().unwrap();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }

    (env, nat)
}

fn assert_rw_fixture_row_closes_without_fallback(row: RwFixtureRow) {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = parity_var("x");
    let y = parity_var("y");
    let h_ty = make_eq_n(x, y);
    let target = make_eq_n(parity_var(row.target_lhs), parity_var(row.target_rhs));
    let goal_ty = Expr::pi(BinderInfo::Default, h_ty, target);
    let mut state = ProofState::new(env, goal_ty.clone());
    intro(&mut state, "h").expect("rw fixture should introduce the local equality");
    let axiom_before = axiom_snapshot();

    rewrite(&mut state, "h", row.reverse)
        .unwrap_or_else(|err| panic!("rw fixture row {} should rewrite: {err:?}", row.id));
    rfl(&mut state)
        .unwrap_or_else(|err| panic!("rw fixture row {} should close with rfl: {err:?}", row.id));
    assert!(
        state.is_complete(),
        "rw fixture row {} should leave no open goals",
        row.id
    );
    assert_no_trusted_axiom_usage("rw", row.id, axiom_before);

    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "rw fixture row {} must not use trustedArith",
        row.id
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "rw fixture row {} must not use trustedAy",
        row.id
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "rw fixture row {} must not close through sorry",
        row.id
    );
    let proof = state
        .closed_proof()
        .unwrap_or_else(|| panic!("rw fixture row {} should expose proof", row.id));
    let typecheck = TypeChecker::new(state.env()).check_type(&proof, &goal_ty);
    assert!(
        typecheck.is_ok(),
        "rw fixture row {} produced a non-kernel-valid proof: {typecheck:?}",
        row.id
    );
}

#[test]
#[serial]
fn test_tactic_parity_simp_lane_executable_fixture_fails_closed_without_fallback() {
    reset_all_counters();
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target.clone());
    let axiom_before = axiom_snapshot();
    let sorry_before = sorry_count();

    let result = simp_all(&mut state);
    assert!(
        result.is_err(),
        "simp_all opaque-target fixture should fail closed with no applicable lemmas, got {result:?}"
    );
    assert!(
        !state.is_complete(),
        "simp_all opaque-target fixture must not close the original goal on failure"
    );
    assert_eq!(
        state.goals.len(),
        1,
        "simp_all opaque-target fixture should preserve the single open goal"
    );
    assert_eq!(
        state.goals[0].target, target,
        "simp_all opaque-target fixture should leave the target unchanged"
    );
    assert_eq!(
        sorry_count(),
        sorry_before,
        "simp_all opaque-target fixture must not create sorry terms"
    );
    assert_no_trusted_axiom_usage(
        "simp_all",
        "opaque target fail-closed fixture",
        axiom_before,
    );

    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "simp_all opaque-target fixture must not use trustedArith"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "simp_all opaque-target fixture must not use trustedAy"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "simp_all opaque-target fixture must not record sorry fallback"
    );
}

#[test]
fn test_tactic_parity_eval_matrix_tracks_proof_behavior() {
    let source = tactic_parity_source!();

    assert!(source.contains("id: tactic-parity"));
    assert!(
        source.contains("#3701") && source.contains("#3711") && source.contains("#3712"),
        "tactic-parity eval must stay tied to the replacement tactic issues"
    );
    assert!(
        source.contains("entrypoint: clean replacement tactic-parity --json"),
        "matrix should point at the Rust-owned tactic parity report"
    );
    assert!(
        source.contains("fully_verified_gate_rows"),
        "matrix metrics must keep fully_verified gate coverage visible"
    );

    let mut strict_gate_rows = 0;
    let mut fallback_rows = 0;
    for (tactic, proof_behavior, fully_verified_gate, evidence_paths) in REQUIRED_ROWS {
        let row = row_block(&source, tactic);
        assert!(
            row.contains(&format!("proof_behavior: {proof_behavior}")),
            "{tactic} row must classify proof behavior as {proof_behavior}"
        );
        assert!(
            row.contains(&format!("fully_verified_gate: {fully_verified_gate}")),
            "{tactic} row has the wrong fully_verified gate classification"
        );
        assert!(
            row.contains("fallback_behavior: "),
            "{tactic} row must classify fallback behavior"
        );
        for evidence_path in *evidence_paths {
            assert!(
                row.contains(evidence_path),
                "{tactic} row is missing evidence path {evidence_path}"
            );
            assert!(
                repo_root().join(evidence_path).exists(),
                "{tactic} evidence path does not exist: {evidence_path}"
            );
        }
        if *fully_verified_gate {
            strict_gate_rows += 1;
        }
        if *proof_behavior == "fallback-classified" {
            fallback_rows += 1;
        }
    }

    assert!(
        strict_gate_rows >= 2,
        "matrix should keep multiple strict fully_verified gates visible"
    );
    assert!(
        fallback_rows >= 1,
        "matrix should classify trusted fallback behavior instead of omitting it"
    );

    for evidence_path in source.lines().filter_map(|line| {
        line.trim()
            .strip_prefix("- crates/")
            .map(|suffix| format!("crates/{suffix}"))
    }) {
        assert!(
            repo_root().join(&evidence_path).exists(),
            "matrix evidence path does not exist: {evidence_path}"
        );
    }
}

#[test]
fn test_tactic_parity_high_value_rows_have_executable_checks() {
    let source = tactic_parity_source!();

    for spec in HIGH_VALUE_EXECUTABLE_CHECKS {
        let row = row_block(&source, spec.tactic);
        let command = format!(
            "command: cargo test -p clean-elab {} --lib -- --exact",
            spec.module_path
        );

        assert!(
            row.contains("fallback_behavior: fail-closed"),
            "{} executable tactic lane must remain fail-closed while parity blockers remain",
            spec.tactic
        );
        assert!(
            row.contains("executable_checks:"),
            "{} row must name at least one executable check",
            spec.tactic
        );
        assert!(
            row.contains(&format!("- id: {}", spec.id)),
            "{} row is missing executable check id {}",
            spec.tactic,
            spec.id
        );
        assert!(
            row.contains(&format!("source: {}", spec.source)),
            "{} row must point executable check {} at source {}",
            spec.tactic,
            spec.id,
            spec.source
        );
        assert!(
            row.contains(&command),
            "{} row must expose exact cargo test command: {}",
            spec.tactic,
            command
        );
        assert!(
            row.contains("proves: "),
            "{} executable check must state what behavior it proves",
            spec.tactic
        );

        let test_source = read_repo_file(spec.source);
        assert!(
            test_source.contains(&format!("fn {}", spec.test_fn)),
            "{} executable check {} references missing Rust test {} in {}",
            spec.tactic,
            spec.id,
            spec.test_fn,
            spec.source
        );
    }
}

#[test]
#[serial]
fn test_tactic_parity_rw_lane_executable_fixture_closes_without_fallback() {
    let fixture_rows = [
        RwFixtureRow {
            id: "rw_local_forward_refl",
            reverse: false,
            target_lhs: "x",
            target_rhs: "x",
        },
        RwFixtureRow {
            id: "rw_local_reverse_refl",
            reverse: true,
            target_lhs: "y",
            target_rhs: "y",
        },
    ];

    for row in fixture_rows {
        assert_rw_fixture_row_closes_without_fallback(row);
    }
}

#[test]
#[serial]
fn test_tactic_parity_ring_lane_executable_fixture_closes_without_fallback() {
    reset_all_counters();
    let (env, nat) = parity_ring_env();
    let a = parity_var("a");
    let b = parity_var("b");
    let goal_ty = make_eq(
        nat,
        parity_nat_add(b.clone(), a.clone()),
        parity_nat_add(a, b),
    );
    let mut state = ProofState::new(env, goal_ty.clone());
    let axiom_before = axiom_snapshot();

    let result = ring_nf(&mut state);
    assert!(
        result.is_ok(),
        "tactic-parity ring executable check is blocked: ring_nf should close b + a = a + b, got {result:?}"
    );
    assert!(
        state.is_complete(),
        "tactic-parity ring executable check is blocked: ring_nf succeeded but left goals open"
    );
    assert_no_trusted_axiom_usage(
        "ring_nf",
        "tactic-parity ring commutativity fixture",
        axiom_before,
    );

    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "tactic-parity ring executable check must not use trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "tactic-parity ring executable check must not close through sorry"
    );
    let proof = state
        .closed_proof()
        .expect("tactic-parity ring executable check should expose a closed proof term");
    let typecheck = TypeChecker::new(state.env()).check_type(&proof, &goal_ty);
    assert!(
        typecheck.is_ok(),
        "tactic-parity ring executable check produced a non-kernel-valid proof: {typecheck:?}"
    );
}

#[test]
#[serial]
fn test_tactic_parity_ring_corpus_fixture_rows_close_without_fallback() {
    let fixture_rows = [
        (
            "ring_nat_add_comm",
            parity_nat_add(parity_var("b"), parity_var("a")),
            parity_nat_add(parity_var("a"), parity_var("b")),
        ),
        (
            "ring_nat_add_zero_right",
            parity_nat_add(parity_var("a"), parity_nat_zero()),
            parity_var("a"),
        ),
        (
            "ring_nat_mul_zero_right",
            parity_nat_mul(parity_var("a"), parity_nat_zero()),
            parity_nat_zero(),
        ),
    ];

    assert_eq!(
        fixture_rows.len(),
        3,
        "ring corpus fixture bucket must stay a bounded 3-row evidence bucket until generated parity counts replace it"
    );

    for (row_id, lhs, rhs) in fixture_rows {
        reset_all_counters();
        let (env, nat) = parity_ring_env();
        let goal_ty = make_eq(nat, lhs, rhs);
        let mut state = ProofState::new(env, goal_ty.clone());
        let axiom_before = axiom_snapshot();

        let result = ring_nf(&mut state);
        assert!(
            result.is_ok(),
            "ring corpus fixture row {row_id} should close with ring_nf, got {result:?}"
        );
        assert!(
            state.is_complete(),
            "ring corpus fixture row {row_id} succeeded but left goals open"
        );
        assert_no_trusted_axiom_usage("ring_nf", row_id, axiom_before);

        let ledger = state.trust_ledger();
        assert_eq!(
            ledger.trusted_arith_count, 0,
            "ring corpus fixture row {row_id} must not use trustedArith"
        );
        assert_eq!(
            ledger.sorry_count, 0,
            "ring corpus fixture row {row_id} must not close through sorry"
        );
        let proof = state
            .closed_proof()
            .unwrap_or_else(|| panic!("ring corpus fixture row {row_id} should expose proof"));
        let typecheck = TypeChecker::new(state.env()).check_type(&proof, &goal_ty);
        assert!(
            typecheck.is_ok(),
            "ring corpus fixture row {row_id} produced a non-kernel-valid proof: {typecheck:?}"
        );
    }
}

#[test]
fn test_tactic_parity_simp_corpus_bucket_blocks_until_generated_counts_exist() {
    let source = tactic_parity_source!();
    let row = row_block(&source, "simp");

    assert!(
        row.contains("lean4_corpus_evidence:"),
        "simp row must carry the bounded fail-closed fixture bucket"
    );
    assert!(
        row.contains("bucket: simp-all-opaque-fail-closed-fixture"),
        "simp row must name the fixture bucket"
    );
    assert!(
        row.contains("generated: false"),
        "simp fixture bucket must stay non-generated until Lean4-vs-clean counts exist"
    );
    assert!(
        row.contains("fixture_rows: 1"),
        "simp fixture bucket must expose the exact fixture row count"
    );
    assert!(
        row.contains("lean4_successes: 0")
            && row.contains("clean_successes: 0")
            && row.contains("clean_fail_closed_rows: 1")
            && row.contains("matched_successes: 0"),
        "fixture-only simp bucket must not claim Lean4 matched parity counts"
    );
    assert!(
        row.contains("parity_status: fixture-only-blocking"),
        "simp fixture bucket must stay blocking, not launch-green"
    );
    assert!(
        row.contains("required_next_artifact: generated Lean4-vs-clean parity counts"),
        "simp bucket must state the generated parity-count artifact that unlocks readiness"
    );
    assert!(
        row.contains("fully_verified_gate: false"),
        "fixture-only corpus evidence must not mark simp fully verified"
    );
    assert!(
        row.contains("- id: simp_all_opaque_target_no_progress"),
        "simp fixture bucket is missing the fail-closed row id"
    );
    assert!(
        row.contains(
            "blocker: simp has 1 bounded clean fail-closed fixture row, but launch readiness stays blocked until generated Lean4-vs-clean parity counts exist."
        ),
        "simp blocker must be more specific than a generic Lean4 parity blocker"
    );
}

#[test]
fn test_tactic_parity_rw_corpus_bucket_blocks_until_generated_counts_exist() {
    let source = tactic_parity_source!();
    let row = row_block(&source, "rw");
    let required_rows = ["rw_local_forward_refl", "rw_local_reverse_refl"];

    assert!(
        row.contains("lean4_corpus_evidence:"),
        "rw row must carry the bounded corpus fixture bucket"
    );
    assert!(
        row.contains("bucket: rw-local-equality-fixture"),
        "rw row must name the fixture bucket"
    );
    assert!(
        row.contains("generated: false"),
        "rw fixture bucket must stay non-generated until Lean4-vs-clean counts exist"
    );
    assert!(
        row.contains("fixture_rows: 2"),
        "rw fixture bucket must expose the exact fixture row count"
    );
    assert!(
        row.contains("lean4_successes: 0")
            && row.contains("clean_successes: 2")
            && row.contains("matched_successes: 0"),
        "fixture-only rw bucket must not claim Lean4 matched parity counts"
    );
    assert!(
        row.contains("parity_status: fixture-only-blocking"),
        "rw fixture bucket must stay blocking, not launch-green"
    );
    assert!(
        row.contains("required_next_artifact: generated Lean4-vs-clean parity counts"),
        "rw bucket must state the generated parity-count artifact that unlocks readiness"
    );
    assert!(
        row.contains("fully_verified_gate: false"),
        "fixture-only corpus evidence must not mark rw fully verified"
    );
    assert!(
        row.contains(
            "blocker: Rewrite has 2 bounded clean checked-rewrite fixture rows, but launch readiness stays blocked until generated Lean4-vs-clean parity counts exist."
        ),
        "rw blocker must be more specific than a generic Lean4 parity blocker"
    );
    for row_id in required_rows {
        assert!(
            row.contains(&format!("- id: {row_id}")),
            "rw fixture bucket is missing row id {row_id}"
        );
    }
}

#[test]
fn test_tactic_parity_ring_corpus_bucket_blocks_until_generated_counts_exist() {
    let source = tactic_parity_source!();
    let row = row_block(&source, "ring");
    let required_rows = [
        "ring_nat_add_comm",
        "ring_nat_add_zero_right",
        "ring_nat_mul_zero_right",
    ];

    assert!(
        row.contains("lean4_corpus_evidence:"),
        "ring row must carry the bounded corpus fixture bucket"
    );
    assert!(
        row.contains("bucket: ring-nat-normalization-fixture"),
        "ring row must name the fixture bucket"
    );
    assert!(
        row.contains("generated: false"),
        "ring fixture bucket must stay non-generated until Lean4-vs-clean counts exist"
    );
    assert!(
        row.contains("fixture_rows: 3"),
        "ring fixture bucket must expose the exact fixture row count"
    );
    assert!(
        row.contains("lean4_successes: 0")
            && row.contains("clean_successes: 3")
            && row.contains("matched_successes: 0"),
        "fixture-only ring bucket must not claim Lean4 matched parity counts"
    );
    assert!(
        row.contains("parity_status: fixture-only-blocking"),
        "ring fixture bucket must stay blocking, not launch-green"
    );
    assert!(
        row.contains("required_next_artifact: generated Lean4-vs-clean parity counts"),
        "ring bucket must state the generated parity-count artifact that unlocks readiness"
    );
    assert!(
        row.contains("fully_verified_gate: false"),
        "fixture-only corpus evidence must not mark ring fully verified"
    );
    assert!(
        row.contains(
            "blocker: Ring/ring_nf has 3 bounded clean fixture rows, but launch readiness stays blocked until generated Lean4-vs-clean parity counts exist."
        ),
        "ring blocker must be more specific than a generic Lean4 parity blocker"
    );
    for row_id in required_rows {
        assert!(
            row.contains(&format!("- id: {row_id}")),
            "ring fixture bucket is missing row id {row_id}"
        );
    }
}

#[test]
fn test_tactic_parity_norm_num_corpus_bucket_blocks_until_generated_counts_exist() {
    let source = tactic_parity_source!();
    let row = row_block(&source, "norm_num");

    assert!(
        row.contains("lean4_corpus_evidence:"),
        "norm_num row must carry the bounded fail-closed fixture bucket"
    );
    assert!(
        row.contains("bucket: norm-num-at-fail-closed-fixture"),
        "norm_num row must name the fixture bucket"
    );
    assert!(
        row.contains("generated: false"),
        "norm_num fixture bucket must stay non-generated until Lean4-vs-clean counts exist"
    );
    assert!(
        row.contains("fixture_rows: 1"),
        "norm_num fixture bucket must expose the exact fixture row count"
    );
    assert!(
        row.contains("lean4_successes: 0")
            && row.contains("clean_successes: 0")
            && row.contains("clean_fail_closed_rows: 1")
            && row.contains("matched_successes: 0"),
        "fixture-only norm_num bucket must not claim Lean4 matched parity counts"
    );
    assert!(
        row.contains("parity_status: fixture-only-blocking"),
        "norm_num fixture bucket must stay blocking, not launch-green"
    );
    assert!(
        row.contains("required_next_artifact: generated Lean4-vs-clean parity counts"),
        "norm_num bucket must state the generated parity-count artifact that unlocks readiness"
    );
    assert!(
        row.contains("fully_verified_gate: false"),
        "fixture-only corpus evidence must not mark norm_num fully verified"
    );
    assert!(
        row.contains("- id: norm_num_at_non_defeq_rewrite"),
        "norm_num fixture bucket is missing the fail-closed row id"
    );
    assert!(
        row.contains(
            "blocker: norm_num has 1 bounded clean fail-closed fixture row, but launch readiness stays blocked until generated Lean4-vs-clean parity counts exist."
        ),
        "norm_num blocker must be more specific than a generic Lean4 parity blocker"
    );
}

#[test]
fn test_tactic_parity_mathverse_corpus_bucket_blocks_until_generated_counts_exist() {
    let source = tactic_parity_source!();
    let row = row_block(&source, "mathverse");

    assert!(
        row.contains("lean4_corpus_evidence:"),
        "mathverse row must carry the bounded fail-closed fixture bucket"
    );
    assert!(
        row.contains("bucket: mathverse-certified-arithmetic-fail-closed-fixture"),
        "mathverse row must name the fixture bucket"
    );
    assert!(
        row.contains("generated: false"),
        "mathverse fixture bucket must stay non-generated until Lean4-vs-clean counts exist"
    );
    assert!(
        row.contains("fixture_rows: 1"),
        "mathverse fixture bucket must expose the exact fixture row count"
    );
    assert!(
        row.contains("lean4_successes: 0")
            && row.contains("clean_successes: 0")
            && row.contains("clean_fail_closed_rows: 1")
            && row.contains("matched_successes: 0"),
        "fixture-only mathverse bucket must not claim Lean4 matched parity counts"
    );
    assert!(
        row.contains("parity_status: fixture-only-blocking"),
        "mathverse fixture bucket must stay blocking, not launch-green"
    );
    assert!(
        row.contains("required_next_artifact: generated Lean4-vs-clean parity counts"),
        "mathverse bucket must state the generated parity-count artifact that unlocks readiness"
    );
    assert!(
        row.contains("fully_verified_gate: false"),
        "fixture-only corpus evidence must not mark mathverse fully verified"
    );
    assert!(
        row.contains("- id: mathverse_certified_arithmetic_replay_rejected"),
        "mathverse fixture bucket is missing the fail-closed row id"
    );
    assert!(
        row.contains(
            "blocker: mathverse has 1 bounded clean fail-closed certified-replay fixture row, but launch readiness stays blocked until generated Lean4-vs-clean parity counts exist."
        ),
        "mathverse blocker must be more specific than a generic Lean4 parity blocker"
    );
}

#[test]
fn test_tactic_parity_nlinarith_corpus_bucket_blocks_until_generated_counts_exist() {
    let source = tactic_parity_source!();
    let row = row_block(&source, "nlinarith");

    assert!(
        row.contains("lean4_corpus_evidence:"),
        "nlinarith row must carry the bounded fail-closed fixture bucket"
    );
    assert!(
        row.contains("bucket: nlinarith-certified-unsat-fail-closed-fixture"),
        "nlinarith row must name the fixture bucket"
    );
    assert!(
        row.contains("generated: false"),
        "nlinarith fixture bucket must stay non-generated until Lean4-vs-clean counts exist"
    );
    assert!(
        row.contains("fixture_rows: 1"),
        "nlinarith fixture bucket must expose the exact fixture row count"
    );
    assert!(
        row.contains("lean4_successes: 0")
            && row.contains("clean_successes: 0")
            && row.contains("clean_fail_closed_rows: 1")
            && row.contains("matched_successes: 0"),
        "fixture-only nlinarith bucket must not claim Lean4 matched parity counts"
    );
    assert!(
        row.contains("parity_status: fixture-only-blocking"),
        "nlinarith fixture bucket must stay blocking, not launch-green"
    );
    assert!(
        row.contains("required_next_artifact: generated Lean4-vs-clean parity counts"),
        "nlinarith bucket must state the generated parity-count artifact that unlocks readiness"
    );
    assert!(
        row.contains("fully_verified_gate: false"),
        "fixture-only corpus evidence must not mark nlinarith fully verified"
    );
    assert!(
        row.contains("- id: nlinarith_forced_certified_unsat_no_kernel_proof"),
        "nlinarith fixture bucket is missing the fail-closed row id"
    );
    assert!(
        row.contains(
            "blocker: nlinarith has 1 bounded clean fail-closed certified-replay fixture row, but launch readiness stays blocked until generated Lean4-vs-clean parity counts exist."
        ),
        "nlinarith blocker must be more specific than a generic Lean4 parity blocker"
    );
}

#[test]
fn test_tactic_parity_generated_count_manifest_schema_records_missing_runner_absence() {
    let source = tactic_parity_source!();
    let expected_manifests = [
        (
            "simp",
            "simp-generated-lean4-vs-clean-counts",
            "evals/tactic-parity/corpora/simp-count-corpus.yaml",
            "metrics/benchmarks/tactic-parity/{run_id}/lean4/simp-counts.json",
            &["simp_all_opaque_target_no_progress"][..],
        ),
        (
            "rw",
            "rw-generated-lean4-vs-clean-counts",
            "evals/tactic-parity/corpora/rw-count-corpus.yaml",
            "metrics/benchmarks/tactic-parity/{run_id}/lean4/rw-counts.json",
            &["rw_local_forward_refl", "rw_local_reverse_refl"][..],
        ),
        (
            "ring",
            "ring-generated-lean4-vs-clean-counts",
            "evals/tactic-parity/corpora/ring-count-corpus.yaml",
            "metrics/benchmarks/tactic-parity/{run_id}/lean4/ring-counts.json",
            &[
                "ring_nat_add_comm",
                "ring_nat_add_zero_right",
                "ring_nat_mul_zero_right",
            ][..],
        ),
        (
            "norm_num",
            "norm-num-generated-lean4-vs-clean-counts",
            "evals/tactic-parity/corpora/norm-num-count-corpus.yaml",
            "metrics/benchmarks/tactic-parity/{run_id}/lean4/norm-num-counts.json",
            &["norm_num_at_non_defeq_rewrite"][..],
        ),
        (
            "mathverse",
            "mathverse-generated-lean4-vs-clean-counts",
            "evals/tactic-parity/corpora/mathverse-count-corpus.yaml",
            "metrics/benchmarks/tactic-parity/{run_id}/lean4/mathverse-counts.json",
            &["mathverse_certified_arithmetic_replay_rejected"][..],
        ),
        (
            "linarith",
            "linarith-generated-lean4-vs-clean-counts",
            "evals/tactic-parity/corpora/linarith-count-corpus.yaml",
            "metrics/benchmarks/tactic-parity/{run_id}/lean4/linarith-counts.json",
            &["linarith-proof-carry"][..],
        ),
        (
            "nlinarith",
            "nlinarith-generated-lean4-vs-clean-counts",
            "evals/tactic-parity/corpora/nlinarith-count-corpus.yaml",
            "metrics/benchmarks/tactic-parity/{run_id}/lean4/nlinarith-counts.json",
            &["nlinarith_forced_certified_unsat_no_kernel_proof"][..],
        ),
    ];

    assert!(
        source.contains("generated_count_manifest_schema:")
            && source.contains("version: clean-tactic-generated-count-manifest-v1"),
        "tactic-parity eval must define the generated-count manifest schema"
    );
    for required_field in [
        "tactic_lane",
        "bucket",
        "generated",
        "source_corpus_path",
        "runner_path",
        "runner_command",
        "runner_artifact_contract",
        "expected_lean4_runner_artifact_path",
        "missing_runner_status",
        "parity_status",
    ] {
        assert!(
            source.contains(&format!("      - {required_field}\n")),
            "generated-count manifest schema must require {required_field}"
        );
    }

    let runner_contract = generated_count_runner_artifact_contract_section(&source);
    assert_eq!(
        yaml_field(runner_contract, "version"),
        "clean-tactic-generated-count-runner-artifact-v1",
        "tactic-parity eval must define the generated-count Lean4 runner artifact contract"
    );
    assert_eq!(
        yaml_field(runner_contract, "artifact_format"),
        "json",
        "generated-count runner artifacts must be JSON"
    );
    assert_eq!(
        yaml_field(runner_contract, "expected_schema_version"),
        "clean-tactic-generated-count-runner-artifact-v1",
        "generated-count runner artifacts must self-identify their schema"
    );
    for required_field in [
        "schema_version",
        "tactic_lane",
        "run_id",
        "cases_total",
        "lean4_successes",
        "clean_successes",
        "matched_successes",
        "source_corpus_path",
        "source_corpus_sha256",
    ] {
        assert!(
            runner_contract.contains(&format!("      - {required_field}\n")),
            "generated-count runner artifact contract must require {required_field}"
        );
    }
    for matching_rule in [
        "schema_version must equal expected_schema_version",
        "tactic_lane must equal the generated-count manifest tactic_lane",
        "source_corpus_path must equal the generated-count manifest source_corpus_path",
        "source_corpus_sha256 must equal the sha256 digest of source_corpus_path contents",
        "cases_total must equal the number of cases in source_corpus_path",
    ] {
        assert!(
            runner_contract.contains(matching_rule),
            "generated-count runner artifact contract must spell out matching rule: {matching_rule}"
        );
    }
    assert_eq!(
        yaml_field(runner_contract, "missing_or_mismatched_artifact_status"),
        "fail-closed-missing-lean4-runner-artifact",
        "missing or mismatched generated-count artifacts must fail closed"
    );

    let manifest_blocks = generated_count_manifest_blocks(&source);
    assert_eq!(
        manifest_blocks.len(),
        expected_manifests.len(),
        "every generated-count manifest must be covered by this schema test"
    );

    for (lane, bucket, corpus_path, expected_artifact_path, expected_case_ids) in expected_manifests
    {
        let manifest = generated_count_manifest_block(&source, lane);

        assert!(
            manifest.contains(&format!("- tactic_lane: {lane}")),
            "generated-count manifest must name the {lane} tactic lane"
        );
        assert_eq!(
            yaml_field(manifest, "bucket"),
            bucket,
            "{lane} generated-count manifest must use the lane bucket"
        );
        assert!(
            !yaml_bool_field(manifest, "generated"),
            "{lane} generated-count manifest must fail closed until the Lean4 runner artifact exists"
        );

        let source_corpus_path = yaml_field(manifest, "source_corpus_path");
        assert_eq!(source_corpus_path, corpus_path);
        let runner_path = yaml_field(manifest, "runner_path");
        assert_eq!(
            runner_path, "scripts/tactic_parity/generated_count_runner.py",
            "{lane} generated-count manifest must point at the generated-count runner"
        );
        assert!(
            repo_root().join(runner_path).is_file(),
            "{lane} generated-count manifest runner path does not exist: {runner_path}"
        );
        assert_eq!(
            yaml_field(manifest, "runner_command"),
            format!("python3 {runner_path} --lane {lane} --dry-run"),
            "{lane} generated-count manifest must advertise the dry-run runner command"
        );
        assert_eq!(
            yaml_field(manifest, "runner_artifact_contract"),
            "clean-tactic-generated-count-runner-artifact-v1",
            "{lane} generated-count manifest must point at the Lean4 runner artifact contract"
        );
        assert!(
            repo_root().join(source_corpus_path).exists(),
            "generated-count manifest source corpus path does not exist: {source_corpus_path}"
        );
        let source_corpus = read_repo_file(source_corpus_path);
        assert!(
            source_corpus.contains("schema_version: clean-tactic-generated-count-source-corpus-v1")
                && source_corpus.contains(&format!("tactic_lane: {lane}"))
                && source_corpus.contains("generated: false"),
            "{lane} source corpus must stay deterministic and non-generated"
        );
        for expected_case_id in expected_case_ids {
            assert!(
                source_corpus.contains(&format!("- id: {expected_case_id}")),
                "{lane} source corpus is missing deterministic case {expected_case_id}"
            );
        }
        let dry_run_artifact = generated_count_runner_dry_run_artifact(lane, runner_path);
        assert_generated_count_dry_run_artifact(
            &dry_run_artifact,
            lane,
            source_corpus_path,
            expected_case_ids,
        );

        let expected_artifact = yaml_field(manifest, "expected_lean4_runner_artifact_path");
        assert_eq!(expected_artifact, expected_artifact_path);
        assert!(
            expected_artifact.contains("{run_id}"),
            "{lane} generated-count artifact path must be run-scoped"
        );
        let matching_artifacts = generated_count_runner_artifact_candidates(expected_artifact);
        assert!(
            matching_artifacts.is_empty(),
            "{lane} generated-count manifest must remain fail-closed until a matching artifact exists; found {matching_artifacts:?}"
        );
        assert_eq!(
            yaml_field(manifest, "missing_runner_status"),
            "fail-closed-missing-lean4-runner-artifact"
        );
        assert_eq!(
            yaml_field(manifest, "parity_status"),
            "generated-counts-missing"
        );
        assert_eq!(
            yaml_field(manifest, "readiness_effect"),
            "blocks-launch-readiness"
        );
    }
}

#[test]
fn test_tactic_parity_readiness_blocks_without_generated_counts() {
    let source = tactic_parity_source!();
    let rows = matrix_rows(&source);
    let generated_count_buckets = generated_lean4_vs_clean_count_buckets(&source);

    assert_eq!(
        generated_count_buckets, 0,
        "fixture-only tactic parity evidence must not be counted as generated Lean4-vs-clean counts"
    );
    assert!(
        source.contains("  readiness_gate:\n"),
        "tactic-parity eval must expose an explicit readiness gate"
    );
    assert!(
        source.contains("status: blocked-pending-generated-counts"),
        "readiness must stay blocked while generated count buckets are absent"
    );
    assert!(
        source.contains("generated_lean4_vs_clean_counts_required: true"),
        "readiness gate must require generated Lean4-vs-clean counts"
    );
    assert!(
        source.contains("generated_lean4_vs_clean_count_buckets: 0"),
        "readiness gate must state that no generated count buckets exist yet"
    );
    assert!(
        source.contains("generated_count_manifests_checked: 7"),
        "readiness gate must state how many generated-count manifests are schema-checked"
    );
    assert!(
        source.contains("missing_runner_status: fail-closed-missing-lean4-runner-artifact"),
        "readiness must name the missing Lean4 runner artifact as fail-closed"
    );
    assert!(
        source.contains("required_next_artifact: generated Lean4-vs-clean parity counts"),
        "readiness gate must name generated parity counts as the unlock artifact"
    );
    assert!(
        !source.contains("status: launch-ready"),
        "matrix must not advertise launch readiness without generated counts"
    );

    for row in rows {
        let blocker = yaml_field(row.block, "blocker");
        assert!(
            row.proof_behavior == "fallback-classified"
                || blocker.contains("Lean4")
                || blocker.contains("corpus")
                || blocker.contains("parity")
                || blocker.contains("counts"),
            "{} must keep a parity/counts blocker while readiness is blocked",
            row.tactic
        );
    }
}

#[test]
fn test_tactic_parity_eval_rejects_overclaiming_rows() {
    let source = tactic_parity_source!();
    let rows = matrix_rows(&source);

    assert_eq!(
        rows.len(),
        9,
        "adding/removing tactic matrix rows must update the overclaiming guard"
    );

    let proof_carrying_rows = rows
        .iter()
        .filter(|row| row.proof_behavior == "proof-carrying")
        .count();
    let strict_zero_trust_rows = rows
        .iter()
        .filter(|row| row.proof_behavior == "strict-zero-trust")
        .count();
    let fallback_classified_rows = rows
        .iter()
        .filter(|row| row.proof_behavior == "fallback-classified")
        .count();
    let fully_verified_gate_rows = rows.iter().filter(|row| row.fully_verified_gate).count();
    let executable_check_rows = rows
        .iter()
        .filter(|row| row.has_executable_checks())
        .count();

    assert_eq!(proof_carrying_rows, 7);
    assert_eq!(strict_zero_trust_rows, 1);
    assert_eq!(fallback_classified_rows, 1);
    assert_eq!(fully_verified_gate_rows, 2);
    assert_eq!(executable_check_rows, 7);
    assert_eq!(
        rows.iter()
            .filter(|row| row.block.contains("lean4_corpus_evidence:"))
            .count(),
        6,
        "only bounded fixture buckets should be counted until generated corpus parity buckets exist"
    );
    for metric in [
        "tactic_rows",
        "proof_carrying_rows",
        "strict_zero_trust_rows",
        "fallback_classified_rows",
        "fully_verified_gate_rows",
        "executable_check_rows",
        "lean4_corpus_fixture_rows",
        "generated_lean4_vs_clean_count_buckets",
    ] {
        assert_metric_present(&source, metric);
    }

    for row in &rows {
        if row.fully_verified_gate {
            assert!(
                matches!(
                    row.fallback_behavior,
                    "fail-closed" | "reject-trusted-direct-proof"
                ),
                "{} sets fully_verified_gate=true but fallback_behavior={} is not fail-closed/rejecting",
                row.tactic,
                row.fallback_behavior
            );
        }

        if row.proof_behavior == "fallback-classified" {
            assert!(
                !row.fully_verified_gate,
                "{} is fallback-classified and must not be a fully_verified gate",
                row.tactic
            );
            assert!(
                !row.has_executable_checks(),
                "{} is fallback-classified and must stay blocking, not executable parity evidence",
                row.tactic
            );
            assert_eq!(
                row.fallback_behavior, "counted-and-blocking",
                "{} fallback-classified row must remain counted-and-blocking",
                row.tactic
            );
        } else {
            assert_ne!(
                row.fallback_behavior, "counted-and-blocking",
                "{} uses counted-and-blocking fallback behavior without fallback-classified proof behavior",
                row.tactic
            );
        }
    }
}

#[test]
fn test_tactic_parity_eval_is_listed_in_registry_readme() {
    let readme = read_repo_file("evals/registry/README.md");
    assert!(
        readme.contains("| `tactic-parity` |")
            && readme.contains("proof-carry/fallback classification"),
        "eval registry README must advertise the tactic parity matrix"
    );
}
