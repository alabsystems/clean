// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reviewer proof command deck and fingerprints.

use super::*;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReviewerProofCommandDeck {
    pub(crate) command_count: usize,
    pub(crate) wrapper_free_command_count: usize,
    pub(crate) wrapper_dependent_command_count: usize,
    pub(crate) wrapper_dependent_row_ids: Vec<&'static str>,
    pub(crate) launch_blocking_command_count: usize,
    pub(crate) launch_blocking_row_ids: Vec<&'static str>,
    pub(crate) launch_blocking_wrapper_free_command_count: usize,
    pub(crate) launch_blocking_wrapper_dependent_command_count: usize,
    pub(crate) launch_blocking_wrapper_dependent_row_ids: Vec<&'static str>,
    pub(crate) launch_blocking_fingerprint_sha256: String,
    pub(crate) fingerprint_algorithm: &'static str,
    pub(crate) fingerprint_sha256: String,
    pub(crate) launch_blocking_commands: Vec<ReviewerProofCommand>,
    pub(crate) commands: Vec<ReviewerProofCommand>,
    pub(crate) reviewer_rule: &'static str,
}

impl ReviewerProofCommandDeck {
    pub(crate) fn from_rows(rows: &[ReplacementRow]) -> Self {
        let commands: Vec<_> = rows.iter().map(ReviewerProofCommand::from_row).collect();
        let wrapper_dependent_row_ids = commands
            .iter()
            .filter(|command| !command.wrapper_free)
            .map(|command| command.row_id)
            .collect();
        let launch_blocking_command_count = commands
            .iter()
            .filter(|command| command.launch_blocking_until_green)
            .count();
        let launch_blocking_row_ids = commands
            .iter()
            .filter(|command| command.launch_blocking_until_green)
            .map(|command| command.row_id)
            .collect();
        let launch_blocking_wrapper_free_command_count = commands
            .iter()
            .filter(|command| command.launch_blocking_until_green && command.wrapper_free)
            .count();
        let launch_blocking_wrapper_dependent_row_ids = commands
            .iter()
            .filter(|command| command.launch_blocking_until_green && !command.wrapper_free)
            .map(|command| command.row_id)
            .collect::<Vec<_>>();
        let launch_blocking_wrapper_dependent_command_count =
            launch_blocking_wrapper_dependent_row_ids.len();
        let fingerprint_sha256 = reviewer_proof_command_deck_fingerprint(&commands);
        let launch_blocking_fingerprint_sha256 =
            reviewer_proof_command_deck_fingerprint_filtered(&commands, true);
        let launch_blocking_commands = commands
            .iter()
            .filter(|command| command.launch_blocking_until_green)
            .cloned()
            .collect();

        Self {
            command_count: commands.len(),
            wrapper_free_command_count: commands
                .iter()
                .filter(|command| command.wrapper_free)
                .count(),
            wrapper_dependent_command_count: commands
                .iter()
                .filter(|command| !command.wrapper_free)
                .count(),
            wrapper_dependent_row_ids,
            launch_blocking_command_count,
            launch_blocking_row_ids,
            launch_blocking_wrapper_free_command_count,
            launch_blocking_wrapper_dependent_command_count,
            launch_blocking_wrapper_dependent_row_ids,
            launch_blocking_fingerprint_sha256,
            fingerprint_algorithm:
                "sha256(row_id || NUL || status || NUL || command || NUL || evidence_artifact || NUL || wrapper_free_bit || NUL || launch_blocking_until_green_bit || LF) for each command in emitted order",
            fingerprint_sha256,
            launch_blocking_commands,
            commands,
            reviewer_rule:
                "External reviewers can rerun these replacement row commands without Python wrapper proof surfaces; non-green rows remain launch blockers even when their command is wrapper-free.",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReviewerProofCommand {
    pub(crate) row_id: &'static str,
    pub(crate) status: ReplacementStatus,
    pub(crate) command: &'static str,
    pub(crate) evidence_artifact: &'static str,
    pub(crate) wrapper_free: bool,
    pub(crate) launch_blocking_until_green: bool,
}

impl ReviewerProofCommand {
    pub(crate) fn from_row(row: &ReplacementRow) -> Self {
        Self {
            row_id: row.id,
            status: row.status,
            command: row.gate_command,
            evidence_artifact: row.evidence_artifact,
            wrapper_free: !is_wrapper_proof_surface(row.gate_command)
                && !is_wrapper_proof_surface(row.evidence_artifact),
            launch_blocking_until_green: row.required_for_launch
                && row.status != ReplacementStatus::Green,
        }
    }
}

pub(crate) fn reviewer_proof_command_deck_fingerprint(commands: &[ReviewerProofCommand]) -> String {
    reviewer_proof_command_deck_fingerprint_filtered(commands, false)
}

pub(crate) fn reviewer_proof_command_deck_fingerprint_filtered(
    commands: &[ReviewerProofCommand],
    launch_blocking_only: bool,
) -> String {
    let mut hasher = Sha256::new();
    for command in commands {
        if launch_blocking_only && !command.launch_blocking_until_green {
            continue;
        }
        hasher.update(command.row_id.as_bytes());
        hasher.update(b"\0");
        hasher.update(command.status.as_str().as_bytes());
        hasher.update(b"\0");
        hasher.update(command.command.as_bytes());
        hasher.update(b"\0");
        hasher.update(command.evidence_artifact.as_bytes());
        hasher.update(b"\0");
        hasher.update(if command.wrapper_free { b"1" } else { b"0" });
        hasher.update(b"\0");
        hasher.update(if command.launch_blocking_until_green {
            b"1"
        } else {
            b"0"
        });
        hasher.update(b"\n");
    }
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
}
