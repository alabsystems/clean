// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The typed W0 comparator-mutation receipt and its in-memory checks.

use super::{CheckError, BOARD, COMPARATOR, REPLAY};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fmt::Write as _;

const SCHEMA: &str = "clean.w0_comparator_mutation.v1";
const COUNT_FIELD: &str = "headline.planted_false_mints_clean.minted_under_mutant";
const COUNT_POINTER: &str = "/headline/planted_false_mints_clean/minted_under_mutant";
const BEFORE: &str = "if saved != expected {";
const AFTER: &str = "if false && saved != expected {";
const EXIT_ASSERTION: &str = "    assert_eq!(output.status.code(), Some(1), \"{diagnostic}\");";
const SUCCESS: &str = "SELF_PROOF_SCOREBOARD=ok the record matches its sources\n";
const REFUSAL: &str = concat!(
    "Error: data/self_proof_scoreboard.json differs from a re-derivation. ",
    "Re-mint with scripts/self_proof_scoreboard.py --write\n",
);
const COMMAND: &[&str] = &[
    "targo",
    "--unverified",
    "test",
    "--locked",
    "--offline",
    "-p",
    "clean",
    "--test",
    "w0_scoreboard_cli",
    "--",
    "--ignored",
    "--exact",
    "w0_scoreboard_replays_checkout_artifacts_and_refuses_mutations",
];

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Record {
    schema: String,
    pub(super) source_commit: String,
    pub(super) source_tree: String,
    pub(super) source_files_sha256: BTreeMap<String, String>,
    pub(super) fixture_paths_sha256: BTreeMap<String, String>,
    build: Build,
    toolchain: Toolchain,
    mutation: Mutation,
    lowered_board: LoweredBoard,
    phases: Phases,
    incumbent_checks: IncumbentChecks,
    toolchain_measurement_retry: MeasurementRetry,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Build {
    command: Vec<String>,
    environment: Environment,
    wrapper: String,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields, rename_all = "SCREAMING_SNAKE_CASE")]
struct Environment {
    cargo_net_offline: String,
    cargo_profile_dev_debug: String,
    cargo_profile_test_debug: String,
    cargo_term_color: String,
    source_date_epoch: String,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Toolchain {
    executable_sha256: ToolExecutables,
    targo_version: String,
    trustc_version: String,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct ToolExecutables {
    targo: String,
    trustc: String,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Mutation {
    before: String,
    after: String,
    path: String,
    restored_source_sha256: String,
    worktree_status_after_restore: String,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct LoweredBoard {
    path: String,
    field: String,
    original: u64,
    lowered: u64,
    sha256: String,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Phases {
    baseline: Phase,
    mutant: Phase,
    restored: Phase,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Phase {
    checks: Checks,
    cli_sha256: String,
    cli_version: String,
    comparator_sha256: String,
    replay_exit: u16,
    replay_summary: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    replay_failure: Option<Failure>,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Checks {
    canonical: CliOutput,
    lowered: CliOutput,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct CliOutput {
    exit: u16,
    stdout: String,
    stdout_sha256: String,
    stderr: String,
    stderr_sha256: String,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Failure {
    actual_cli_exit: u16,
    expected_cli_exit: u16,
    file: String,
    line: usize,
}

// Typed historical notes. This check does not rerun these observations.
#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct IncumbentChecks {
    coverage_and_scoreboard_match: bool,
    coverage_control_arms: u64,
    derivation_status: DerivationStatus,
    scoreboard_control_arms: u64,
    trustcore_fresh: bool,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct DerivationStatus {
    failed: Vec<String>,
    gate_registry_detail: String,
    nodes: u64,
    verdict_set_detail: String,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct MeasurementRetry {
    diagnostic: String,
    recovery: String,
    setup_exit: u16,
}

fn require(condition: bool, reason: &str) -> Result<(), CheckError> {
    if condition {
        Ok(())
    } else {
        Err(CheckError::Invalid(reason.to_owned()))
    }
}

fn hex(value: &str, width: usize) -> bool {
    value.len() == width
        && value
            .bytes()
            .all(|ch| ch.is_ascii_digit() || (b'a'..=b'f').contains(&ch))
}

pub(super) fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn canonical_json(value: &impl Serialize) -> Result<Vec<u8>, CheckError> {
    let render_error =
        |error| CheckError::Invalid(format!("cannot render canonical JSON: {error}"));
    let mut sorted = serde_json::to_value(value).map_err(render_error)?;
    sorted.sort_all_objects();
    let pretty = serde_json::to_string_pretty(&sorted).map_err(render_error)?;
    let mut ascii = String::with_capacity(pretty.len() + 1);
    for ch in pretty.chars() {
        if ch.is_ascii() && ch != '\x7f' {
            ascii.push(ch);
        } else {
            for unit in ch.encode_utf16(&mut [0; 2]) {
                write!(ascii, "\\u{unit:04x}").expect("writing to a String cannot fail");
            }
        }
    }
    ascii.push('\n');
    Ok(ascii.into_bytes())
}

impl Build {
    fn validate(&self) -> Result<(), CheckError> {
        require(
            self.command
                .iter()
                .map(String::as_str)
                .eq(COMMAND.iter().copied())
                && self.wrapper == "scripts/cargo_test_nonvacuous.sh",
            "receipt build must name the exact nonvacuous Trust replay command",
        )?;
        let env = &self.environment;
        require(
            env.cargo_net_offline == "true"
                && env.cargo_profile_dev_debug == "0"
                && env.cargo_profile_test_debug == "0"
                && env.cargo_term_color == "never"
                && env
                    .source_date_epoch
                    .parse::<u64>()
                    .is_ok_and(|value| value.to_string() == env.source_date_epoch),
            "receipt build environment does not match the offline replay",
        )
    }
}

impl CliOutput {
    fn validate(&self, refuse: bool) -> Result<(), CheckError> {
        let (exit, stdout, stderr) = if refuse {
            (1, "", REFUSAL)
        } else {
            (0, SUCCESS, "")
        };
        require(
            self.exit == exit && self.stdout == stdout && self.stderr == stderr,
            "recorded CLI exit or output does not match the expected W0 verdict",
        )?;
        require(
            self.stdout_sha256 == sha256(self.stdout.as_bytes())
                && self.stderr_sha256 == sha256(self.stderr.as_bytes()),
            "recorded W0 CLI stream digest does not match its bytes",
        )
    }
}

impl Phase {
    fn validate(&self, revision: &str, mutant: bool) -> Result<(), CheckError> {
        let version = self
            .cli_version
            .strip_prefix("clean ")
            .and_then(|line| line.strip_suffix(revision))
            .and_then(|line| line.strip_suffix("+g"));
        require(
            version.is_some_and(|value| !value.is_empty() && !value.contains(char::is_whitespace))
                && hex(&self.cli_sha256, 64)
                && hex(&self.comparator_sha256, 64),
            "recorded CLI version or executable/comparator digest is invalid",
        )?;
        let (exit, summary) = if mutant {
            (
                101,
                "test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out",
            )
        } else {
            (
                0,
                "test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out",
            )
        };
        let duration = self
            .replay_summary
            .strip_prefix(summary)
            .and_then(|tail| tail.strip_prefix("; finished in "))
            .and_then(|tail| tail.strip_suffix('s'))
            .and_then(|time| time.split_once('.'));
        require(
            self.replay_exit == exit
                && duration.is_some_and(|(seconds, fraction)| {
                    !seconds.is_empty()
                        && seconds.bytes().all(|ch| ch.is_ascii_digit())
                        && fraction.len() == 2
                        && fraction.bytes().all(|ch| ch.is_ascii_digit())
                }),
            "recorded replay must have the exact single-test verdict",
        )?;
        require(
            match &self.replay_failure {
                Some(failure) => {
                    mutant
                        && failure.file == REPLAY
                        && failure.line != 0
                        && failure.actual_cli_exit == 0
                        && failure.expected_cli_exit == 1
                }
                None => !mutant,
            },
            "recorded replay failure does not describe the expected false acceptance",
        )?;
        self.checks.canonical.validate(false)?;
        self.checks.lowered.validate(!mutant)
    }
}

impl Record {
    pub(super) fn parse(bytes: &[u8]) -> Result<Self, CheckError> {
        let record: Self = serde_json::from_slice(bytes)
            .map_err(|error| CheckError::Invalid(format!("cannot read receipt JSON: {error}")))?;
        require(
            canonical_json(&record)? == bytes,
            "receipt does not use canonical JSON bytes",
        )?;
        require(
            record.schema == SCHEMA,
            "unsupported W0 comparator receipt schema",
        )?;
        require(
            hex(&record.source_commit, 40)
                && hex(&record.source_tree, 40)
                && record
                    .source_files_sha256
                    .values()
                    .chain(record.fixture_paths_sha256.values())
                    .all(|digest| hex(digest, 64)),
            "invalid Git object ID or SHA-256 spelling in the receipt pins",
        )?;
        record.build.validate()?;
        let tools = &record.toolchain;
        require(
            hex(&tools.executable_sha256.targo, 64)
                && hex(&tools.executable_sha256.trustc, 64)
                && tools.targo_version.starts_with("targo ")
                && tools.trustc_version.starts_with("rustc ")
                && tools
                    .trustc_version
                    .lines()
                    .any(|line| line == "binary: trustc"),
            "invalid recorded Trust toolchain identity",
        )?;
        require(
            record.mutation.path == COMPARATOR
                && record.mutation.before == BEFORE
                && record.mutation.after == AFTER
                && record.mutation.worktree_status_after_restore == "clean"
                && hex(&record.mutation.restored_source_sha256, 64),
            "receipt does not name the supported single restored comparator mutation",
        )?;
        require(
            record.lowered_board.path == BOARD
                && record.lowered_board.field == COUNT_FIELD
                && record.lowered_board.original.checked_sub(1)
                    == Some(record.lowered_board.lowered)
                && hex(&record.lowered_board.sha256, 64),
            "receipt does not name the supported one-count saved board mutation",
        )?;
        let Phases {
            baseline,
            mutant,
            restored,
        } = &record.phases;
        baseline.validate(&record.source_commit, false)?;
        mutant.validate(&record.source_commit, true)?;
        restored.validate(&record.source_commit, false)?;
        require(
            baseline.cli_sha256 == restored.cli_sha256
                && baseline.cli_sha256 != mutant.cli_sha256
                && baseline.cli_version == restored.cli_version
                && baseline.cli_version == mutant.cli_version,
            "recorded baseline and restored executable must match and differ from the mutant",
        )?;
        Ok(record)
    }

    pub(super) fn validate_inputs(
        &self,
        comparator: &[u8],
        test: &[u8],
        board: &[u8],
        epoch: &str,
    ) -> Result<(), CheckError> {
        require(
            self.build.environment.source_date_epoch == epoch,
            "recorded source epoch differs from the pinned commit",
        )?;
        let digest = sha256(comparator);
        let source = std::str::from_utf8(comparator).map_err(|error| {
            CheckError::Invalid(format!("pinned comparator is not UTF-8: {error}"))
        })?;
        let before = format!("    {BEFORE}\n");
        let after = format!("    {AFTER}\n");
        require(
            source.matches(&before).count() == 1 && !source.contains(&after),
            "pinned comparator must have one unaltered mutation site",
        )?;
        let mutated = source.replacen(&before, &after, 1);
        let Phases {
            baseline,
            mutant,
            restored,
        } = &self.phases;
        require(
            baseline.comparator_sha256 == digest
                && restored.comparator_sha256 == digest
                && self.mutation.restored_source_sha256 == digest
                && mutant.comparator_sha256 == sha256(mutated.as_bytes()),
            "recorded comparator digests do not match the pinned and exactly mutated bytes",
        )?;

        let test = std::str::from_utf8(test).map_err(|error| {
            CheckError::Invalid(format!("pinned replay test is not UTF-8: {error}"))
        })?;
        let mut assertions = test
            .lines()
            .enumerate()
            .filter_map(|(index, line)| (line == EXIT_ASSERTION).then_some(index + 1));
        let actual_line = assertions.next();
        let recorded_line = mutant.replay_failure.as_ref().map(|failure| failure.line);
        require(
            actual_line.is_some() && actual_line == recorded_line && assertions.next().is_none(),
            "recorded replay failure line does not match the pinned exit assertion",
        )?;
        let mut saved: Value = serde_json::from_slice(board).map_err(|error| {
            CheckError::Invalid(format!("cannot read pinned board JSON: {error}"))
        })?;
        require(
            canonical_json(&saved)? == board,
            "pinned saved board is not canonical JSON",
        )?;
        let count = saved.pointer_mut(COUNT_POINTER).ok_or_else(|| {
            CheckError::Invalid("pinned saved board has no Clean P3 mutant count".to_owned())
        })?;
        require(
            count.as_u64() == Some(self.lowered_board.original),
            "pinned Clean P3 count differs from the receipt",
        )?;
        *count = Value::from(self.lowered_board.lowered);
        require(
            sha256(&canonical_json(&saved)?) == self.lowered_board.sha256,
            "recorded lowered board digest does not match the one-count edit",
        )
    }
}
