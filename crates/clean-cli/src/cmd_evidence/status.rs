// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean evidence status`: the board in section-4 order, then the other
//! registered figures. Each row shows value, denominator and digest, labels
//! and non-claims, commit, age and freshness, or why it has no reading.

use super::age::age_days;
use super::board::{row_of, BOARD};
use super::catalog::{find_figure, Figure, FIGURES};
use super::evaluate::{evaluate, FigureResult};
use super::git_record::last_commit_date;
use super::reading::{Outcome, Reading};
use crate::EvidenceCheckError;
use serde::Serialize;
use std::io::Write;
use std::path::Path;

#[derive(Serialize)]
pub(super) struct StatusRow {
    pub(super) board_row: Option<u8>,
    pub(super) id: &'static str,
    pub(super) registered: bool,
    #[serde(flatten)]
    pub(super) state: RowState,
}

#[derive(Serialize)]
#[serde(tag = "state", rename_all = "snake_case")]
pub(super) enum RowState {
    Measured {
        #[serde(flatten)]
        reading: Box<Reading>,
        #[serde(skip_serializing_if = "Option::is_none")]
        age_days: Option<i64>,
    },
    Absent {
        reason: String,
    },
    Inconsistent {
        reason: String,
    },
    Unavailable {
        reason: String,
    },
}

fn row_state(
    root: &Path,
    figure: &Figure,
    result: FigureResult,
) -> Result<RowState, EvidenceCheckError> {
    Ok(match result {
        Ok(Outcome::Measured(reading)) => {
            let recorded = reading
                .recorded_at
                .clone()
                .or_else(|| last_commit_date(root, figure.input_scope.first()?));
            RowState::Measured {
                age_days: recorded.as_deref().and_then(age_days),
                reading,
            }
        }
        Ok(Outcome::Absent { reason }) => RowState::Absent { reason },
        Err(EvidenceCheckError::Invalid(reason)) => RowState::Inconsistent { reason },
        Err(EvidenceCheckError::Unavailable(reason)) => RowState::Unavailable { reason },
        Err(error @ EvidenceCheckError::Usage(_)) => return Err(error),
    })
}

/// Every row of the board and then every registered figure not on it.
pub(super) fn survey(root: &Path) -> Result<Vec<StatusRow>, EvidenceCheckError> {
    let mut order = BOARD
        .iter()
        .flat_map(|row| row.iter())
        .map(|id| find_figure(id))
        .collect::<Result<Vec<&'static Figure>, _>>()?;
    order.extend(FIGURES.iter().filter(|figure| row_of(figure.id).is_none()));
    order
        .iter()
        .zip(evaluate(root, &order))
        .map(|(figure, result)| {
            Ok(StatusRow {
                board_row: row_of(figure.id),
                id: figure.id,
                registered: true,
                state: row_state(root, figure, result)?,
            })
        })
        .collect()
}

fn position(row: &StatusRow) -> String {
    row.board_row
        .map_or_else(|| "--".to_owned(), |number| format!("{number:>2}"))
}

/// Record text for one terminal line: control characters escaped, quotes kept.
fn printable(text: &str) -> String {
    let mut line = String::with_capacity(text.len());
    for ch in text.chars() {
        if ch.is_control() {
            line.extend(ch.escape_default());
        } else {
            line.push(ch);
        }
    }
    line
}

pub(super) fn write_text(rows: &[StatusRow], output: &mut impl Write) -> anyhow::Result<()> {
    for row in rows {
        let id = row.id;
        let position = position(row);
        match &row.state {
            RowState::Measured { reading, age_days } => {
                writeln!(
                    output,
                    "{position} {id} — {} ({})",
                    reading.freshness.label(),
                    printable(&reading.freshness.reason)
                )?;
                writeln!(output, "   {}", printable(&reading.summary))?;
                if let Some(denominator) = &reading.denominator {
                    writeln!(
                        output,
                        "   denominator {} ({}) {}",
                        denominator.count, denominator.scope, denominator.digest
                    )?;
                }
                let commit = reading.commit.as_deref().unwrap_or("not recorded");
                let age =
                    age_days.map_or_else(|| "unknown".to_owned(), |days| format!("{days} days"));
                writeln!(output, "   commit {}, age {age}", printable(commit))?;
            }
            RowState::Absent { reason } => {
                writeln!(output, "{position} {id} — absent: {}", printable(reason))?;
            }
            RowState::Inconsistent { reason } => {
                writeln!(
                    output,
                    "{position} {id} — inconsistent: {}",
                    printable(reason)
                )?;
            }
            RowState::Unavailable { reason } => {
                writeln!(
                    output,
                    "{position} {id} — unavailable: {}",
                    printable(reason)
                )?;
            }
        }
    }
    Ok(())
}

/// One Markdown table cell: no pipes, no line breaks.
fn cell(text: &str) -> String {
    text.replace('|', "\\|").replace(['\n', '\r'], " ")
}

pub(super) fn write_markdown(rows: &[StatusRow], output: &mut impl Write) -> anyhow::Result<()> {
    writeln!(output, "# Evidence board\n")?;
    writeln!(
        output,
        "Generated by `clean evidence status --markdown`. Rows 1 to 17 follow section 4 of \
         `designs/2026-11-16-full-rust-lean-models-combined-trust.md`; `--` rows are the \
         other registered figures. Freshness is decided only by a recorded input digest; \
         `unknown` is never fresh. Age is shown and never decides.\n"
    )?;
    writeln!(
        output,
        "| # | Figure | Value | Denominator | Labels and non-claims | Commit | Age (days) | Freshness |"
    )?;
    writeln!(output, "|---|---|---|---|---|---|---|---|")?;
    for row in rows {
        let position = position(row);
        let id = row.id;
        match &row.state {
            RowState::Measured { reading, age_days } => {
                let denominator = reading.denominator.as_ref().map_or_else(
                    || "none".to_owned(),
                    |denominator| {
                        format!(
                            "{} ({}) `{}`",
                            denominator.count, denominator.scope, denominator.digest
                        )
                    },
                );
                let notes: Vec<String> = reading
                    .labels
                    .iter()
                    .map(|label| format!("label: {label}"))
                    .chain(
                        reading
                            .non_claims
                            .iter()
                            .map(|claim| format!("not claimed: {claim}")),
                    )
                    .collect();
                writeln!(
                    output,
                    "| {position} | `{id}` | {} | {} | {} | {} | {} | {}: {} |",
                    cell(&reading.summary),
                    cell(&denominator),
                    cell(&notes.join("; ")),
                    reading
                        .commit
                        .as_deref()
                        .map_or_else(|| "not recorded".to_owned(), cell),
                    age_days.map_or_else(|| "unknown".to_owned(), |days| days.to_string()),
                    reading.freshness.label(),
                    cell(&reading.freshness.reason)
                )?;
            }
            RowState::Absent { reason } => writeln!(
                output,
                "| {position} | `{id}` | absent: {} | | | | | |",
                cell(reason)
            )?,
            RowState::Inconsistent { reason } => writeln!(
                output,
                "| {position} | `{id}` | inconsistent: {} | | | | | |",
                cell(reason)
            )?,
            RowState::Unavailable { reason } => writeln!(
                output,
                "| {position} | `{id}` | unavailable: {} | | | | | |",
                cell(reason)
            )?,
        }
    }
    Ok(())
}
