// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-check the recorded frames, declaration rows, and summary.

use super::detail::{accepted_detail, outside_detail};
use super::tokens::scan_tokens;
use super::transcript::{DeclarationRow, Summary, Transcript};
use std::cmp::Ordering;

#[derive(Debug)]
pub(super) struct AcceptedStatement<'input> {
    pub(super) index: usize,
    pub(super) level_params: &'input str,
    pub(super) type_echo: &'input str,
    pub(super) value_echo: &'input str,
}

#[derive(Default)]
struct Counts {
    accepted: usize,
    recognised: usize,
    outside: usize,
    refused: usize,
}

fn line_cmp(left: &str, right: &str) -> Ordering {
    // Both numbers have canonical decimal spelling, so width precedes lexical
    // order even for line numbers larger than a machine integer.
    left.len().cmp(&right.len()).then_with(|| left.cmp(right))
}

fn check_accepted<'input>(
    index: usize,
    row: &DeclarationRow<'input>,
    frame: &[u8],
) -> Result<AcceptedStatement<'input>, String> {
    let line = row.line;
    let statement = row
        .statement
        .as_ref()
        .ok_or_else(|| format!("line {line}: an accepted row requires a statement line"))?;
    if frame.is_empty() {
        return Err(format!("line {line}: accepted on an empty advice frame"));
    }
    let flags = scan_tokens(frame).map_err(|reason| format!("line {line}: {reason}"))?;
    let (reported_flags, level_params) = accepted_detail(row.detail)
        .ok_or_else(|| format!("line {line}: invalid version-1 detail for an accepted row"))?;
    if reported_flags != flags {
        return Err(format!(
            "line {line}: the reported IOTA and K flags disagree with the advice frame"
        ));
    }
    Ok(AcceptedStatement {
        index,
        level_params,
        type_echo: statement.type_echo,
        value_echo: statement.value_echo,
    })
}

fn check_outside_frame(
    row: &DeclarationRow<'_>,
    frame: &[u8],
    detail_matches: bool,
) -> Result<(), String> {
    if !frame.is_empty() {
        return Err(format!(
            "line {}: a {} row requires an empty advice frame",
            row.line, row.class
        ));
    }
    if !detail_matches {
        return Err(format!(
            "line {}: invalid version-1 detail for a {} row",
            row.line, row.class
        ));
    }
    Ok(())
}

fn check_summary(summary: &Summary<'_>, total: usize, counts: Counts) -> Result<(), String> {
    for (field, reported, actual) in [
        ("declarations", summary.declarations, total),
        ("accepted", summary.accepted, counts.accepted),
        ("recognised", summary.recognised, counts.recognised),
        ("outside", summary.outside, counts.outside),
        ("refused", summary.refused, counts.refused),
    ] {
        if reported != actual.to_string() {
            return Err(format!(
                "the summary reports {reported} for {field}, but the transcript has {actual}"
            ));
        }
    }
    Ok(())
}

pub(super) fn check<'input>(
    transcript: &Transcript<'input>,
    frames: &[&[u8]],
    mut visit_accepted: impl FnMut(AcceptedStatement<'input>),
) -> Result<(), String> {
    let rows = &transcript.rows;
    if rows.first().is_some_and(|row| row.line == "0") {
        return Err("line 0 is not a positive declaration line number".into());
    }
    if let Some(pair) = rows
        .windows(2)
        .find(|pair| line_cmp(pair[0].line, pair[1].line) != Ordering::Less)
    {
        return Err(format!(
            "declaration line numbers must increase strictly ({} followed by {})",
            pair[0].line, pair[1].line
        ));
    }
    if frames.len() != rows.len() {
        return Err(format!(
            "the advice has {} frames for {} declaration records",
            frames.len(),
            rows.len()
        ));
    }

    let mut counts = Counts::default();
    for (index, (row, frame)) in rows.iter().zip(frames.iter().copied()).enumerate() {
        if matches!(row.class, "accepted" | "refused")
            && !matches!(row.kind, "def" | "thm" | "opaque")
        {
            return Err(format!(
                "line {}: only definitions, theorems, and opaques can have class {}",
                row.line, row.class
            ));
        }
        match row.class {
            "accepted" => {
                visit_accepted(check_accepted(index, row, frame)?);
                counts.accepted += 1;
            }
            "recognised" => {
                check_outside_frame(row, frame, row.detail == "base")?;
                counts.recognised += 1;
            }
            "outside" => {
                check_outside_frame(row, frame, outside_detail(row.detail))?;
                counts.outside += 1;
            }
            // A dependency refusal can precede token decoding.
            "refused" => counts.refused += 1,
            _ => {
                return Err(format!(
                    "line {}: unknown version-1 declaration class {:?}",
                    row.line, row.class
                ));
            }
        }
    }
    check_summary(&transcript.summary, rows.len(), counts)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cmd_evidence::k3_packet::transcript::StatementRow;

    fn fixture() -> Transcript<'static> {
        Transcript {
            rows: vec![
                DeclarationRow {
                    line: "9",
                    kind: "def",
                    class: "accepted",
                    detail: "bound=0;1+2 iota=1 k=1 lparams=2",
                    name: "example",
                    statement: Some(StatementRow {
                        type_echo: "type",
                        value_echo: "value",
                    }),
                },
                DeclarationRow {
                    line: "10",
                    kind: "inductive",
                    class: "recognised",
                    detail: "base",
                    name: "Nat",
                    statement: None,
                },
                DeclarationRow {
                    line: "100",
                    kind: "axiom",
                    class: "outside",
                    detail: "axiomDecl",
                    name: "outside",
                    statement: None,
                },
                DeclarationRow {
                    line: "1844674407370955161600000000000",
                    kind: "opaque",
                    class: "refused",
                    detail: "dependency:missing",
                    name: "refused",
                    statement: None,
                },
            ],
            summary: Summary {
                declarations: "4",
                accepted: "1",
                recognised: "1",
                outside: "1",
                refused: "1",
            },
        }
    }

    // The refused frame has an invalid tag and remains opaque.
    const FRAMES: [&[u8]; 4] = [&[0x01, 0x0b, 0x0b, 0x0c], &[], &[], &[0xff]];

    fn refuse(transcript: &Transcript<'_>, frames: &[&[u8]], reason: &str) {
        let error = check(transcript, frames, |_| {}).unwrap_err();
        assert!(error.contains(reason), "expected {reason:?}, got {error:?}");
    }

    #[test]
    fn agrees_on_frames_classes_order_and_summary() {
        let mut transcript = fixture();
        transcript.rows.swap(0, 1);
        transcript.rows[0].line = "9";
        transcript.rows[1].line = "10";
        let mut frames = FRAMES;
        frames.swap(0, 1);
        let mut accepted = Vec::new();
        check(&transcript, &frames, |statement| accepted.push(statement)).unwrap();
        let [statement] = accepted.as_slice() else {
            panic!("expected exactly one accepted statement");
        };
        assert_eq!(statement.index, 1);
        assert_eq!(statement.level_params, "2");
        assert_eq!(statement.type_echo, "type");
        assert_eq!(statement.value_echo, "value");
    }

    #[test]
    fn refuses_missing_frames_zero_duplicate_and_descending_rows() {
        let mut transcript = fixture();
        refuse(&transcript, &FRAMES[..3], "3 frames for 4");
        transcript.rows[0].line = "0";
        refuse(&transcript, &FRAMES, "positive declaration line number");
        transcript.rows[0].line = "10";
        refuse(&transcript, &FRAMES, "10 followed by 10");
        transcript.rows[0].line = "11";
        refuse(&transcript, &FRAMES, "11 followed by 10");
    }

    #[test]
    fn refuses_an_unknown_class_and_a_nonordinary_refused_row() {
        let mut transcript = fixture();
        transcript.rows[3].kind = "axiom";
        refuse(&transcript, &FRAMES, "only definitions");
        transcript.rows[3].class = "future";
        refuse(&transcript, &FRAMES, "unknown version-1 declaration class");
    }

    #[test]
    fn requires_a_statement_and_valid_tokens_for_an_accepted_row() {
        let mut transcript = fixture();
        transcript.rows[0].statement = None;
        refuse(&transcript, &FRAMES, "requires a statement");
        let transcript = fixture();
        let mut frames = FRAMES;
        frames[0] = &[];
        refuse(&transcript, &frames, "empty advice frame");
        frames[0] = &[0x0b, 0x01, 0x80];
        refuse(&transcript, &frames, "truncated operand");
        // The 0x0c is part of the operand and must not set the K flag.
        frames[0] = &[0x0b, 0x01, 0x0c];
        refuse(&transcript, &frames, "IOTA and K flags");
    }

    #[test]
    fn requires_empty_frames_and_the_detail_for_base_and_outside_rows() {
        for (index, class) in [(1, "recognised"), (2, "outside")] {
            let mut transcript = fixture();
            let mut frames = FRAMES;
            frames[index] = &[0x02];
            refuse(
                &transcript,
                &frames,
                &format!("{class} row requires an empty advice frame"),
            );
            transcript.rows[index].detail = "";
            refuse(
                &transcript,
                &FRAMES,
                &format!("invalid version-1 detail for a {class} row"),
            );
        }
    }

    #[test]
    fn compares_each_of_the_reported_summary_fields_to_the_recount() {
        let mut transcript = fixture();
        transcript.summary.declarations = "1844674407370955161600000000000";
        refuse(&transcript, &FRAMES, "for declarations");
        transcript.summary.declarations = "4";
        transcript.summary.accepted = "0";
        refuse(&transcript, &FRAMES, "for accepted");
        transcript.summary.accepted = "1";
        transcript.summary.recognised = "0";
        refuse(&transcript, &FRAMES, "for recognised");
        transcript.summary.recognised = "1";
        transcript.summary.outside = "0";
        refuse(&transcript, &FRAMES, "for outside");
        transcript.summary.outside = "1";
        transcript.summary.refused = "0";
        refuse(&transcript, &FRAMES, "for refused");
    }
}
