// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Derive the coverage figures from the validated export and transcript rows.

use super::super::{k3_export::digest_hex, k3_json};
use super::{consistency::AcceptedStatement, transcript::DeclarationRow};
use anyhow::{bail, ensure, Context};
use clean_olean::k3_export_syntax::{K3DeclarationIndexRow, K3DeclarationKind};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::io::Write;

// Serde emits fields in this order. Match Python's canonical sorted key order.
#[derive(Default, Serialize)]
pub(in crate::cmd_evidence) struct Figures<'input> {
    pub(in crate::cmd_evidence) accepted: usize,
    accepted_declarations: Vec<AcceptedDeclaration<'input>>,
    declaration_records: usize,
    pub(in crate::cmd_evidence) inside_fragment: usize,
    pub(in crate::cmd_evidence) ordinary_declarations: usize,
    outside_fragment: usize,
    recognised_families: usize,
    refused_inside: usize,
}

#[derive(Serialize)]
struct AcceptedDeclaration<'input> {
    advice_frame_sha256: String,
    detail: &'input str,
    kind: &'static str,
    level_params: usize,
    line: usize,
    name: &'input str,
    statement_sha256: String,
}

pub(super) fn write_figures(
    output: &mut impl Write,
    declarations: &[K3DeclarationIndexRow],
    rows: &[DeclarationRow<'_>],
    accepted: &[AcceptedStatement<'_>],
    frames: &[&[u8]],
) -> anyhow::Result<()> {
    let figures = derive(declarations, rows, accepted, frames)?;
    k3_json::write(output, &figures)
}

pub(super) fn derive<'input>(
    declarations: &[K3DeclarationIndexRow],
    rows: &[DeclarationRow<'input>],
    accepted: &[AcceptedStatement<'_>],
    frames: &[&[u8]],
) -> anyhow::Result<Figures<'input>> {
    ensure!(
        declarations.len() == rows.len() && rows.len() == frames.len(),
        "K3 figures require aligned declaration, transcript and frame rows"
    );
    let mut figures = Figures {
        accepted_declarations: Vec::with_capacity(accepted.len()),
        declaration_records: declarations.len(),
        ..Figures::default()
    };
    let mut accepted = accepted.iter();
    for (index, ((declaration, row), frame)) in
        declarations.iter().zip(rows).zip(frames).enumerate()
    {
        let line = declaration.line;
        figures.ordinary_declarations += usize::from(matches!(
            declaration.kind,
            K3DeclarationKind::Def | K3DeclarationKind::Thm | K3DeclarationKind::Opaque
        ));
        match row.class {
            "accepted" => {
                let statement = accepted
                    .next()
                    .filter(|statement| statement.index == index)
                    .with_context(|| {
                        format!("K3 figures need the accepted statement at export line {line}")
                    })?;
                let level_params = statement.level_params.parse().with_context(|| {
                    format!("K3 figures need a numeric level parameter count at export line {line}")
                })?;
                figures.accepted_declarations.push(AcceptedDeclaration {
                    advice_frame_sha256: sha256([*frame]),
                    detail: row.detail,
                    kind: declaration.kind.as_str(),
                    level_params,
                    line,
                    name: row.name,
                    statement_sha256: sha256([
                        statement.type_echo.as_bytes(),
                        b"\t",
                        statement.value_echo.as_bytes(),
                    ]),
                });
            }
            "refused" => figures.refused_inside += 1,
            "outside" => figures.outside_fragment += 1,
            "recognised" => figures.recognised_families += 1,
            class => bail!("K3 figures found unknown class {class:?} at export line {line}"),
        }
    }
    ensure!(
        accepted.next().is_none(),
        "K3 figures have an accepted statement without a matching declaration"
    );
    figures.accepted = figures.accepted_declarations.len();
    figures.inside_fragment = figures.accepted + figures.refused_inside;
    Ok(figures)
}

fn sha256<'bytes>(parts: impl IntoIterator<Item = &'bytes [u8]>) -> String {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update(part);
    }
    digest_hex(&digest.finalize())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cmd_evidence::k3_packet::transcript::StatementRow;
    use serde_json::{json, Value};
    use K3DeclarationKind::{Axiom, Def, Inductive, Opaque, Quot, Thm};

    fn row<'input>(
        line: &'input str,
        kind: &'input str,
        class: &'input str,
        detail: &'input str,
        name: &'input str,
    ) -> DeclarationRow<'input> {
        DeclarationRow {
            line,
            kind,
            class,
            detail,
            name,
            statement: None,
        }
    }

    #[test]
    fn derives_distinct_denominators_and_hashes_in_declaration_order() {
        let declarations = [
            (22, Def),
            (40, Axiom),
            (65, Thm),
            (90, Opaque),
            (100, Inductive),
            (112, Def),
            (113, Quot),
        ]
        .map(|(line, kind)| K3DeclarationIndexRow { line, kind });
        let mut rows = [
            row(
                "22",
                "def",
                "accepted",
                "bound=0 iota=0 k=0 lparams=0",
                "[s1:A]",
            ),
            row("40", "axiom", "outside", "axiomDecl", "[s1:B]"),
            row(
                "65",
                "thm",
                "accepted",
                "bound=2 iota=1 k=0 lparams=2",
                "[s2:β]",
            ),
            row("90", "opaque", "refused", "opaque detail", "[s1:D]"),
            row("100", "inductive", "recognised", "base", "[s3:Nat]"),
            row("112", "def", "outside", "unsafe", "[s1:F]"),
            row("113", "quot", "outside", "quotient", "[s1:G]"),
        ];
        let accepted = [
            AcceptedStatement {
                index: 0,
                level_params: "0",
                type_echo: "(sort 0)",
                value_echo: "(b 0)",
            },
            AcceptedStatement {
                index: 2,
                level_params: "2",
                type_echo: "(sort (s 0))",
                value_echo: "(c [s2:π])",
            },
        ];
        for statement in &accepted {
            rows[statement.index].statement = Some(StatementRow {
                type_echo: statement.type_echo,
                value_echo: statement.value_echo,
            });
        }
        let frames: [&[u8]; 7] = [&[1, 0], &[], &[1, 0x80, 1, 0x0b], &[0xff], &[], &[], &[]];
        let mut output = Vec::new();
        write_figures(&mut output, &declarations, &rows, &accepted, &frames).unwrap();
        let actual: Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(
            actual,
            json!({
                "accepted": 2,
                "accepted_declarations": [
                    {
                        "advice_frame_sha256": "47dc540c94ceb704a23875c11273e16bb0b8a87aed84de911f2133568115f254",
                        "detail": rows[0].detail,
                        "kind": "def",
                        "level_params": 0,
                        "line": 22,
                        "name": "[s1:A]",
                        "statement_sha256": "0c94dd1fd3a110e5405bd58de83562647bbc0e476c01a7b3e7248d3b42c4e900"
                    },
                    {
                        "advice_frame_sha256": "b2e65a030e935cda256d13f0df971817d945f983311d7e7e5edd303b7dfbe905",
                        "detail": rows[2].detail,
                        "kind": "thm",
                        "level_params": 2,
                        "line": 65,
                        "name": "[s2:β]",
                        "statement_sha256": "2cef2452b73ab33a9a5a14d8f9ebea8720bca1eb15deb69dfed5a5fd266189f8"
                    }
                ],
                "declaration_records": 7,
                "inside_fragment": 3,
                "ordinary_declarations": 4,
                "outside_fragment": 3,
                "recognised_families": 1,
                "refused_inside": 1
            }),
        );
    }

    #[test]
    fn writes_an_empty_figure_payload_in_canonical_key_order() {
        let mut output = Vec::new();
        write_figures(&mut output, &[], &[], &[], &[]).unwrap();
        let expected = concat!(
            "{\n",
            "  \"accepted\": 0,\n",
            "  \"accepted_declarations\": [],\n",
            "  \"declaration_records\": 0,\n",
            "  \"inside_fragment\": 0,\n",
            "  \"ordinary_declarations\": 0,\n",
            "  \"outside_fragment\": 0,\n",
            "  \"recognised_families\": 0,\n",
            "  \"refused_inside\": 0\n",
            "}\n",
        );
        assert_eq!(output.as_slice(), expected.as_bytes());
    }
}
