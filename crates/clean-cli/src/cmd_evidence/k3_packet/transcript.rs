// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The syntax of a version 1 interim KCheck transcript.

use serde::Serialize;

const HEADERS: [&str; 4] = [
    "kcheck-run-interim\t1",
    "checker\tkcheck_labelled\tKCheck.kcheckBytes\tsoundness=not-claimed-by-this-run",
    "loader\tinterim\tproved=false\treprint=absent\trecs=dropped-unchecked",
    "base\tEq\tPUnit\tNat",
];

#[derive(Debug, Serialize)]
pub(super) struct Transcript<'a> {
    pub(super) rows: Vec<DeclarationRow<'a>>,
    pub(super) summary: Summary<'a>,
}

#[derive(Debug, Serialize)]
pub(super) struct DeclarationRow<'a> {
    pub(super) line: &'a str,
    pub(super) kind: &'a str,
    pub(super) class: &'a str,
    pub(super) detail: &'a str,
    pub(super) name: &'a str,
    pub(super) statement: Option<StatementRow<'a>>,
}

#[derive(Debug, Serialize)]
pub(super) struct StatementRow<'a> {
    pub(super) type_echo: &'a str,
    pub(super) value_echo: &'a str,
}

#[derive(Debug, Serialize)]
pub(super) struct Summary<'a> {
    pub(super) declarations: &'a str,
    pub(super) accepted: &'a str,
    pub(super) recognised: &'a str,
    pub(super) outside: &'a str,
    pub(super) refused: &'a str,
}

pub(super) fn canonical_decimal(text: &str) -> bool {
    match text.as_bytes() {
        [b'0'] => true,
        [b'1'..=b'9', digits @ ..] => digits.iter().all(u8::is_ascii_digit),
        _ => false,
    }
}

pub(super) fn parse_transcript(text: &str) -> Result<Transcript<'_>, String> {
    if text.contains('\r') {
        return Err(
            "the transcript holds a carriage return; the checker prints line feeds only".into(),
        );
    }
    let body = text
        .strip_suffix('\n')
        .ok_or_else(|| "the transcript does not end with a line feed".to_owned())?;
    let mut lines = body.split('\n');
    if !HEADERS
        .into_iter()
        .all(|header| lines.next() == Some(header))
    {
        return Err("the transcript's four header lines are not the ones version 1 prints".into());
    }
    let summary_fields = lines
        .next_back()
        .and_then(|line| line.strip_prefix("summary\t"))
        .ok_or_else(|| "the transcript has no summary line".to_owned())?;

    let mut rows = Vec::new();
    for raw in lines {
        let fields: Vec<_> = raw.splitn(7, '\t').collect();
        match fields[..] {
            ["decl", line, kind, class, detail, name] if canonical_decimal(line) => {
                rows.push(DeclarationRow {
                    line,
                    kind,
                    class,
                    detail,
                    name,
                    statement: None,
                });
            }
            ["stmt", line, type_echo, value_echo] if canonical_decimal(line) => {
                let Some(row) = rows.last_mut().filter(|row| {
                    row.line == line && row.class == "accepted" && row.statement.is_none()
                }) else {
                    return Err(format!(
                        "a statement line for {line} does not follow that declaration's accepted row"
                    ));
                };
                row.statement = Some(StatementRow {
                    type_echo,
                    value_echo,
                });
            }
            _ => {
                let prefix: String = raw.chars().take(60).collect();
                return Err(format!(
                    "the transcript holds a line of no known shape: {prefix:?}"
                ));
            }
        }
    }

    let summary =
        parse_summary(summary_fields).ok_or_else(|| "the summary line is malformed".to_owned())?;
    Ok(Transcript { rows, summary })
}

fn parse_summary(fields: &str) -> Option<Summary<'_>> {
    let mut fields = fields.split('\t');
    let mut count = |expected_key| {
        let (key, value) = fields.next()?.split_once('=')?;
        (key == expected_key && canonical_decimal(value)).then_some(value)
    };
    let summary = Summary {
        declarations: count("declarations")?,
        accepted: count("accepted")?,
        recognised: count("recognised")?,
        outside: count("outside")?,
        refused: count("refused")?,
    };
    fields.next().is_none().then_some(summary)
}

#[cfg(test)]
mod tests {
    use super::*;

    const DECL: &str = "decl\t12\tdef\taccepted\tbound=0 iota=0 k=0 lparams=0\t[s2:id]";
    const STMT: &str = "stmt\t12\t(b 1)\t(b 0)";
    const OUTSIDE: &str = "decl\t14\taxiom\toutside\taxiomDecl\t[s2:ax]";
    const SUMMARY: &str = "summary\tdeclarations=2\taccepted=1\trecognised=0\toutside=1\trefused=0";

    fn transcript(rows: &[&str], summary: &str) -> String {
        HEADERS
            .into_iter()
            .chain(rows.iter().copied())
            .chain([summary, ""])
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn expect_refusal(text: &str, reason: &str) {
        let error = parse_transcript(text).expect_err("malformed transcript was accepted");
        assert!(error.contains(reason), "expected {reason:?}, got {error:?}");
    }

    #[test]
    fn keeps_declaration_fields_statement_echoes_and_counts() {
        let text = transcript(&[DECL, STMT, OUTSIDE], SUMMARY);
        let parsed = parse_transcript(&text).expect("valid transcript");
        assert_eq!(parsed.rows.len(), 2);
        let first = &parsed.rows[0];
        assert_eq!(first.line, "12");
        assert_eq!(first.kind, "def");
        assert_eq!(first.class, "accepted");
        assert_eq!(first.detail, "bound=0 iota=0 k=0 lparams=0");
        assert_eq!(first.name, "[s2:id]");
        let statement = first.statement.as_ref().expect("attached statement");
        assert_eq!(statement.type_echo, "(b 1)");
        assert_eq!(statement.value_echo, "(b 0)");
        assert!(parsed.rows[1].statement.is_none());
        assert_eq!(parsed.summary.declarations, "2");
        assert_eq!(parsed.summary.accepted, "1");
        assert_eq!(parsed.summary.recognised, "0");
        assert_eq!(parsed.summary.outside, "1");
        assert_eq!(parsed.summary.refused, "0");

        let empty = transcript(
            &[],
            "summary\tdeclarations=0\taccepted=0\trecognised=0\toutside=0\trefused=0",
        );
        let parsed_empty = parse_transcript(&empty).expect("transcript with no rows");
        assert!(parsed_empty.rows.is_empty());
    }

    #[test]
    fn keeps_numbers_as_tokens_and_leaves_recounts_and_row_semantics_to_callers() {
        let number = "1844674407370955161600000000000";
        let accepted = DECL.replace("\t12\t", &format!("\t{number}\t"));
        let statement = STMT.replace("\t12\t", &format!("\t{number}\t"));
        let unrelated = "decl\t0\tunknown\tunknown\t\t";
        let summary = SUMMARY.replace("declarations=2", &format!("declarations={number}"));
        let text = transcript(&[&accepted, &statement, unrelated, DECL, DECL], &summary);
        let parsed = parse_transcript(&text).expect("syntax alone is well formed");
        assert_eq!(parsed.rows[0].line, number);
        assert_eq!(parsed.rows[1].line, "0");
        assert_eq!(parsed.rows[1].name, "");
        assert_eq!(parsed.rows[1].class, "unknown");
        assert!(parsed.rows[2].statement.is_none());
        assert_eq!(parsed.summary.declarations, number);
    }

    #[test]
    fn requires_lf_headers_and_a_final_summary() {
        let text = transcript(&[DECL, STMT, OUTSIDE], SUMMARY);
        expect_refusal(&text.replace('\n', "\r\n"), "carriage return");
        expect_refusal(text.trim_end_matches('\n'), "does not end with a line feed");
        expect_refusal(
            &text.replacen("not-claimed-by-this-run", "proved", 1),
            "header lines",
        );
        expect_refusal(&transcript(&[DECL, STMT, OUTSIDE], "summary"), "no summary");
        expect_refusal(&format!("{text}\n"), "no summary");
        let headers_only = HEADERS.join("\n") + "\n";
        expect_refusal(&headers_only, "no summary");
    }

    #[test]
    fn requires_exact_row_arity_and_canonical_decimal_lines() {
        for row in [
            "note\thello",
            "decl\t12\tdef\taccepted\tdetail",
            "decl\t12\tdef\taccepted\tdetail\tname\textra",
            "decl\t012\tdef\taccepted\tdetail\tname",
            "decl\t+12\tdef\taccepted\tdetail\tname",
            "decl\t١٢\tdef\taccepted\tdetail\tname",
            "stmt\t12\ttype",
            "stmt\t12\ttype\tvalue\textra",
            "stmt\t012\ttype\tvalue",
        ] {
            expect_refusal(&transcript(&[DECL, row], SUMMARY), "line of no known shape");
        }
    }

    #[test]
    fn requires_each_statement_to_immediately_follow_its_own_accepted_row() {
        let wrong_line = "stmt\t14\t(b 1)\t(b 0)";
        let refused = "decl\t12\tdef\trefused\tKCheck.Refusal.sort\t[s2:id]";
        for rows in [
            &[STMT][..],
            &[DECL, wrong_line],
            &[DECL, STMT, STMT],
            &[DECL, OUTSIDE, STMT],
            &[refused, STMT],
        ] {
            expect_refusal(&transcript(rows, SUMMARY), "does not follow");
        }
    }

    #[test]
    fn requires_the_five_distinct_summary_keys_in_order() {
        for tail in [
            "summary\tdeclarations=2\taccepted=1\trecognised=0\toutside=1",
            "summary\tdeclarations=2\taccepted=1\trecognised=0\toutside=1\trefused=0\taccepted=1",
            "summary\taccepted=1\tdeclarations=2\trecognised=0\toutside=1\trefused=0",
            "summary\tdeclarations=2\taccepted=1\trecognised=0\taccepted=1\trefused=0",
            "summary\tdeclarations=02\taccepted=1\trecognised=0\toutside=1\trefused=0",
            "summary\tdeclarations=2\taccepted=\trecognised=0\toutside=1\trefused=0",
            "summary\tdeclarations=2\taccepted=1\trecognised=0\toutside=1\trefused=0=0",
        ] {
            expect_refusal(
                &transcript(&[DECL, STMT, OUTSIDE], tail),
                "summary line is malformed",
            );
        }
    }
}
