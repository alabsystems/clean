// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared Phase 1 corpus helpers used by both the AC6 gate and the dedicated
//! full-corpus measurement sweep.

// Test scaffolding not exercised by every including build — kept per the 2026-07-30
// keep-and-annotate sweep; see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md.
#![allow(dead_code)]
use clean_kernel::{BinderData, BinderInfo, Declaration, Environment, Expr, Name};
use clean_parser::{parse_file, SurfaceDecl};
use std::borrow::Cow;
use std::collections::HashMap;
use std::path::Path;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Level {
    Elab,
    ParseOnly,
}

pub(crate) struct ManifestEntry {
    pub(crate) filename: String,
    #[allow(dead_code)] // used by AC6 gate, ignored by the measurement sweep
    pub(crate) level: Level,
}

/// Raw result of elaborating a single declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DeclStatus {
    Pass,
    Fail,
    Timeout,
}

/// Per-declaration elaboration outcome.
#[derive(Debug, Clone)]
pub(crate) struct DeclElabOutcome {
    #[allow(dead_code)] // used by AC6 profile checks, ignored by some consumers
    pub(crate) index: usize,
    pub(crate) status: DeclStatus,
    pub(crate) error: Option<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct Phase1ElabMeasurement {
    pub(crate) outcomes: Vec<DeclElabOutcome>,
    pub(crate) succeeded: usize,
    pub(crate) total: usize,
    pub(crate) first_error: Option<String>,
}

/// What the expected-outcome profile says about one declaration.
#[derive(Debug, Clone)]
pub(crate) enum ExpectedDeclOutcome {
    Pass,
    FailContains(String),
}

/// Expected outcomes for all declarations in one corpus file.
#[derive(Debug, Clone)]
pub(crate) struct FileExpectedProfile {
    pub(crate) decls: Vec<ExpectedDeclOutcome>,
}

/// Profile-aware evaluation result for one elab file.
#[derive(Debug, Clone)]
pub(crate) struct ProfileEvalResult {
    /// Declarations expected to succeed that did succeed.
    pub(crate) must_succeed_passed: usize,
    /// Total declarations expected to succeed.
    pub(crate) must_succeed_total: usize,
    /// Expected-failure declarations that matched.
    pub(crate) expected_fail_matched: usize,
    /// Total expected-failure declarations.
    pub(crate) expected_fail_total: usize,
    /// Unexpected artifact failures (expected-fail decl got wrong error shape).
    pub(crate) artifact_mismatches: Vec<String>,
}

impl ProfileEvalResult {
    #[allow(dead_code)] // used by the AC6 gate, not by the full-corpus measurement lane
    pub(crate) fn file_passed(&self) -> bool {
        self.must_succeed_passed == self.must_succeed_total
            && self.expected_fail_matched == self.expected_fail_total
    }
}

pub(crate) fn read_manifest(manifest_path: &Path) -> Vec<ManifestEntry> {
    let content = std::fs::read_to_string(manifest_path)
        .unwrap_or_else(|e| panic!("Failed to read manifest at {manifest_path:?}: {e}"));

    content
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            !trimmed.is_empty() && !trimmed.starts_with('#')
        })
        .map(|line| {
            let parts: Vec<&str> = line.trim().splitn(2, ',').collect();
            assert!(
                parts.len() == 2,
                "Invalid manifest line (expected 'filename,level'): {line}"
            );
            let level = match parts[1].trim() {
                "elab" => Level::Elab,
                "parse_only" => Level::ParseOnly,
                other => panic!("Unknown level '{other}' in manifest line: {line}"),
            };
            ManifestEntry {
                filename: parts[0].trim().to_string(),
                level,
            }
        })
        .collect()
}

pub(crate) fn read_corpus_file(corpus_dir: &Path, filename: &str) -> Result<String, String> {
    let file_path = corpus_dir.join(filename);
    match std::fs::read(&file_path) {
        Ok(bytes) => match String::from_utf8_lossy(&bytes) {
            Cow::Owned(s) => Ok(s),
            Cow::Borrowed(s) => Ok(s.to_string()),
        },
        Err(e) => Err(format!("IO error: {e}")),
    }
}

pub(crate) fn try_parse(content: &str) -> Result<Vec<SurfaceDecl>, String> {
    let content_owned = content.to_string();
    let handle = std::thread::Builder::new()
        .stack_size(clean_kernel::test_utils::SMALL_STACK)
        .spawn(move || parse_file(&content_owned))
        .map_err(|e| format!("Thread spawn error: {e}"))?;

    match handle.join() {
        Ok(Ok(decls)) => Ok(decls),
        Ok(Err(e)) => Err(format!("Parse error: {e}")),
        Err(_) => Err("Thread panic (possible stack overflow)".to_string()),
    }
}

pub(crate) fn parse_manifest_entry(
    entry: &ManifestEntry,
    corpus_dir: &Path,
) -> Result<Vec<SurfaceDecl>, String> {
    let content = read_corpus_file(corpus_dir, &entry.filename)?;
    try_parse(&content)
}

pub(crate) fn phase1_elab_env() -> Environment {
    let mut env = Environment::new();
    // Core types (already initialized)
    env.init_nat().ok();
    env.init_and().ok();
    env.init_exists().ok();
    env.init_true_false().ok();
    env.init_classical().ok();
    env.init_eq().ok();
    // Additional prelude types needed by elab corpus files
    env.init_bool().ok();
    env.init_unit().ok();
    env.init_pempty().ok();
    env.init_empty().ok();
    env.init_list().ok();
    env.init_int().ok();
    env.init_heq().ok();
    env.init_prod().ok();
    env.init_sigma().ok();
    env.init_ordering().ok();
    env.init_decidable().ok();
    // `init_nat` no longer seeds the equality-decision cluster implicitly.
    // Phase-1 fixtures call `Nat.decEq` directly and use equality conditions in
    // `ite`, so initialize the constructive DecidableEq surface explicitly.
    env.init_decidable_eq().ok();
    // `1079.lean` and other compat files rely on if-expressions lowering
    // through `ite`, which is not implied by `Decidable` alone.
    env.init_ite().ok();
    init_prelude_id(&mut env);
    env
}

fn init_prelude_id(env: &mut Environment) {
    if env.get_const(&Name::from_string("id")).is_some() {
        return;
    }
    let implicit = BinderData::unrestricted(BinderInfo::Implicit);
    let explicit = BinderData::unrestricted(BinderInfo::Default);
    let id_type = Expr::pi(
        implicit,
        Expr::type_(),
        Expr::pi(explicit, Expr::bvar(0), Expr::bvar(1)),
    );
    let id_value = Expr::lam(
        implicit,
        Expr::type_(),
        Expr::lam(explicit, Expr::bvar(0), Expr::bvar(0)),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("id"),
        level_params: Vec::new(),
        type_: id_type,
        value: id_value,
        is_reducible: true,
    })
    .ok();
}

fn try_elab_per_decl_inner(decls: &[SurfaceDecl]) -> Vec<DeclElabOutcome> {
    let mut env = phase1_elab_env();
    let mut file_ctx = clean_elab::FileContext::new();
    // The Phase 1 corpus is a Clean frontend authority lane.  Resolve imports
    // through Clean's deterministic native prelude providers instead of
    // searching for and loading an arbitrary host Lean installation.  Besides
    // making the result host-dependent, loading Lean.Elab.Tactic's external
    // transitive closure can consume the entire per-file timeout before the
    // declarations under test are reached.
    file_ctx.disable_external_import_search();
    let mut outcomes = Vec::with_capacity(decls.len());

    for (index, decl) in decls.iter().enumerate() {
        let result =
            clean_elab::elaborate_decl_and_register_with_context(&mut env, decl, &mut file_ctx);
        let (status, error) = match result {
            Ok(result) => match first_nested_failure(&result) {
                Some(error) => (DeclStatus::Fail, Some(error.to_string())),
                None => (DeclStatus::Pass, None),
            },
            Err(e) => (DeclStatus::Fail, Some(format!("{e}"))),
        };
        outcomes.push(DeclElabOutcome {
            index,
            status,
            error,
        });
    }

    outcomes
}

/// A section/namespace block preserves successful siblings by returning a
/// `Multiple` result with explicit `Failed` leaves.  The corpus lane profiles
/// each top-level source declaration, so a block containing such a leaf is a
/// failed declaration even though the recovery-oriented driver returned `Ok`.
fn first_nested_failure(result: &clean_elab::ElabResult) -> Option<&clean_elab::ElabError> {
    match result {
        clean_elab::ElabResult::Failed { error, .. } => Some(error),
        clean_elab::ElabResult::Multiple(results) => results.iter().find_map(first_nested_failure),
        _ => None,
    }
}

/// Run per-declaration elaboration with a per-file timeout.
pub(crate) fn try_elab_per_decl(decls: Vec<SurfaceDecl>) -> Vec<DeclElabOutcome> {
    use std::sync::mpsc;
    use std::sync::mpsc::RecvTimeoutError;
    use std::time::Duration;

    let total = decls.len();
    let (tx, rx) = mpsc::channel();

    let handle = std::thread::Builder::new()
        .stack_size(clean_kernel::test_utils::SMALL_STACK)
        .spawn(move || {
            let result = try_elab_per_decl_inner(&decls);
            let _ = tx.send(result);
        })
        .expect("elab thread spawn");

    match rx.recv_timeout(Duration::from_secs(30)) {
        Ok(result) => result,
        Err(RecvTimeoutError::Timeout) => {
            // On timeout, report all declarations as timed out.
            (0..total)
                .map(|index| DeclElabOutcome {
                    index,
                    status: DeclStatus::Timeout,
                    error: Some("Elaboration timed out (30s)".to_string()),
                })
                .collect()
        }
        Err(RecvTimeoutError::Disconnected) => {
            let detail = match handle.join() {
                Ok(_) => "Elaboration thread disconnected before reporting results".to_string(),
                Err(_) => "Elaboration thread panicked (possible stack overflow)".to_string(),
            };
            (0..total)
                .map(|index| DeclElabOutcome {
                    index,
                    status: DeclStatus::Fail,
                    error: Some(detail.clone()),
                })
                .collect()
        }
    }
}

/// Summarize per-declaration outcomes as (succeeded, total, first_error).
pub(crate) fn summarize_outcomes(outcomes: &[DeclElabOutcome]) -> (usize, usize, Option<String>) {
    let succeeded = outcomes
        .iter()
        .filter(|o| o.status == DeclStatus::Pass)
        .count();
    let total = outcomes.len();
    let first_error = outcomes
        .iter()
        .find(|o| o.status != DeclStatus::Pass)
        .and_then(|o| o.error.clone());
    (succeeded, total, first_error)
}

pub(crate) fn elaborate_manifest_entry(
    entry: &ManifestEntry,
    corpus_dir: &Path,
) -> Result<Phase1ElabMeasurement, String> {
    let decls = parse_manifest_entry(entry, corpus_dir)?;
    let total = decls.len();
    let outcomes = try_elab_per_decl(decls);
    let (succeeded, _, first_error) = summarize_outcomes(&outcomes);
    Ok(Phase1ElabMeasurement {
        outcomes,
        succeeded,
        total,
        first_error,
    })
}

/// Load expected-outcome profiles from JSON metadata file.
/// Returns empty map if the file does not exist (all files use default contract).
pub(crate) fn load_expected_profiles(metadata_path: &Path) -> HashMap<String, FileExpectedProfile> {
    let content = match std::fs::read_to_string(metadata_path) {
        Ok(c) => c,
        Err(_) => return HashMap::new(),
    };

    let parsed: serde_json::Value = serde_json::from_str(&content)
        .unwrap_or_else(|e| panic!("Invalid JSON in {metadata_path:?}: {e}"));

    let obj = parsed
        .as_object()
        .unwrap_or_else(|| panic!("Expected JSON object at top level in {metadata_path:?}"));

    let mut profiles = HashMap::new();
    for (filename, entries) in obj {
        let arr = entries
            .as_array()
            .unwrap_or_else(|| panic!("Expected array for {filename:?} in {metadata_path:?}"));

        let mut decls = Vec::new();
        for entry in arr {
            let outcome_str = entry
                .get("outcome")
                .and_then(|v| v.as_str())
                .unwrap_or_else(|| {
                    panic!("Missing 'outcome' field for {filename:?} in {metadata_path:?}")
                });

            let expected = match outcome_str {
                "pass" => ExpectedDeclOutcome::Pass,
                "fail" => {
                    let contains = entry
                        .get("contains")
                        .and_then(|v| v.as_str())
                        .unwrap_or_else(|| {
                            panic!(
                                "Expected 'contains' for fail outcome in {filename:?} \
                                 in {metadata_path:?}"
                            )
                        });
                    ExpectedDeclOutcome::FailContains(contains.to_string())
                }
                other => panic!("Unknown outcome '{other}' for {filename:?} in {metadata_path:?}"),
            };
            decls.push(expected);
        }

        profiles.insert(filename.clone(), FileExpectedProfile { decls });
    }

    profiles
}

/// Evaluate per-declaration outcomes against an expected-outcome profile.
pub(crate) fn evaluate_against_profile(
    filename: &str,
    outcomes: &[DeclElabOutcome],
    profile: &FileExpectedProfile,
) -> ProfileEvalResult {
    let mut must_succeed_passed = 0;
    let mut must_succeed_total = 0;
    let mut expected_fail_matched = 0;
    let mut expected_fail_total = 0;
    let mut artifact_mismatches = Vec::new();

    for (i, outcome) in outcomes.iter().enumerate() {
        let expected = profile.decls.get(i);

        match expected {
            Some(ExpectedDeclOutcome::Pass) | None => {
                // Default: declaration must succeed (None = no profile entry = must pass).
                must_succeed_total += 1;
                if outcome.status == DeclStatus::Pass {
                    must_succeed_passed += 1;
                }
            }
            Some(ExpectedDeclOutcome::FailContains(pattern)) => {
                expected_fail_total += 1;
                match &outcome.status {
                    DeclStatus::Fail => {
                        let err = outcome.error.as_deref().unwrap_or("");
                        if err.contains(pattern.as_str()) {
                            expected_fail_matched += 1;
                        } else {
                            artifact_mismatches.push(format!(
                                "{filename}[{i}]: expected error containing {pattern:?}, \
                                 got: {err}"
                            ));
                        }
                    }
                    DeclStatus::Timeout => {
                        artifact_mismatches.push(format!(
                            "{filename}[{i}]: expected explicit failure, got timeout"
                        ));
                    }
                    DeclStatus::Pass => {
                        artifact_mismatches.push(format!(
                            "{filename}[{i}]: expected failure containing {pattern:?}, \
                             but declaration succeeded"
                        ));
                    }
                }
            }
        }
    }

    for i in outcomes.len()..profile.decls.len() {
        match &profile.decls[i] {
            ExpectedDeclOutcome::Pass => {
                must_succeed_total += 1;
            }
            ExpectedDeclOutcome::FailContains(_) => {
                expected_fail_total += 1;
                artifact_mismatches.push(format!(
                    "{filename}[{i}]: profile entry exists but no declaration found"
                ));
            }
        }
    }

    ProfileEvalResult {
        must_succeed_passed,
        must_succeed_total,
        expected_fail_matched,
        expected_fail_total,
        artifact_mismatches,
    }
}

/// Evaluate outcomes for a file with no profile: all decls must succeed (legacy behavior).
pub(crate) fn evaluate_no_profile(
    _filename: &str,
    outcomes: &[DeclElabOutcome],
) -> ProfileEvalResult {
    let passed = outcomes
        .iter()
        .filter(|o| o.status == DeclStatus::Pass)
        .count();
    ProfileEvalResult {
        must_succeed_passed: passed,
        must_succeed_total: outcomes.len(),
        expected_fail_matched: 0,
        expected_fail_total: 0,
        artifact_mismatches: Vec::new(),
    }
}
