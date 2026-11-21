// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Offline parsing of the framed advice and version-1 transcript.

mod advice;
mod consistency;
mod detail;
mod figures;
mod tokens;
mod transcript;

use super::k3_export;
use super::k3_inputs::{canonical_root, find_regular_file};
use crate::EvidenceCheckError;
use clean_olean::k3_export_syntax::{
    K3AcceptedStatementSummary, K3BaseRecognitionSummary, K3DeclarationBodySummary,
    K3DeclarationIndexRow, K3DeclarationNameSummary, K3DependencyReport, K3FragmentClass,
    K3FragmentSummary,
};
use serde::Serialize;
use std::fs;
use std::io::Write;
use std::path::Path;

pub(super) use figures::Figures;

pub(super) const ADVICE: &str = "data/kcheck_coverage/prelude_roots.advice.bin";
pub(super) const TRANSCRIPT: &str = "data/kcheck_coverage/prelude_roots.transcript.txt";

#[derive(PartialEq, Eq)]
pub(super) enum Check {
    Syntax,
    Consistency,
    DeclarationIndex,
    NonInductiveBodies,
    DeclarationBodies,
    DeclarationNames,
    AcceptedStatements,
    BaseFamilies,
    FragmentClasses,
    DependencyRefusals,
    CoverageFigures,
}

#[derive(Serialize)]
struct PacketSyntax<'input> {
    frame_lengths: Vec<usize>,
    declarations: Vec<transcript::DeclarationRow<'input>>,
    reported_summary: transcript::Summary<'input>,
}

struct PacketBytes {
    advice: Vec<u8>,
    transcript: Vec<u8>,
}

struct Packet<'input> {
    transcript: transcript::Transcript<'input>,
    frames: Vec<&'input [u8]>,
    accepted: Vec<consistency::AcceptedStatement<'input>>,
}

pub(super) struct ReceiptPacket<'input> {
    pub(super) figures: Figures<'input>,
    pub(super) export_gzip_sha256: String,
    pub(super) export_raw_sha256: String,
    pub(super) advice_sha256: String,
    pub(super) transcript_sha256: String,
}

fn read_input(root: &Path, relative: &str) -> Result<Vec<u8>, EvidenceCheckError> {
    let path = find_regular_file(root, relative)?
        .ok_or_else(|| EvidenceCheckError::Unavailable(format!("{relative} does not exist")))?;
    fs::read(&path)
        .map_err(|error| EvidenceCheckError::Unavailable(format!("{}: {error}", path.display())))
}

impl PacketBytes {
    fn read(root: &Path) -> Result<Self, EvidenceCheckError> {
        Ok(Self {
            advice: read_input(root, ADVICE)?,
            transcript: read_input(root, TRANSCRIPT)?,
        })
    }

    fn parse(&self, check: &Check) -> Result<Packet<'_>, EvidenceCheckError> {
        let text = std::str::from_utf8(&self.transcript).map_err(|error| {
            EvidenceCheckError::Invalid(format!("{TRANSCRIPT} is not UTF-8: {error}"))
        })?;
        let transcript = transcript::parse_transcript(text)
            .map_err(|reason| EvidenceCheckError::Invalid(format!("{TRANSCRIPT}: {reason}")))?;
        let frames = advice::split_frames(&self.advice)
            .map_err(|reason| EvidenceCheckError::Invalid(format!("{ADVICE}: {reason}")))?;
        let mut accepted = Vec::new();
        if *check != Check::Syntax {
            consistency::check(&transcript, &frames, |statement| {
                if matches!(
                    check,
                    Check::AcceptedStatements
                        | Check::BaseFamilies
                        | Check::FragmentClasses
                        | Check::DependencyRefusals
                        | Check::CoverageFigures
                ) {
                    accepted.push(statement);
                }
            })
            .map_err(|reason| EvidenceCheckError::Invalid(format!("K3 packet: {reason}")))?;
        }
        Ok(Packet {
            transcript,
            frames,
            accepted,
        })
    }
}

fn compare_declaration_index(
    declarations: &[K3DeclarationIndexRow],
    rows: &[transcript::DeclarationRow<'_>],
) -> Result<(), EvidenceCheckError> {
    if declarations.len() != rows.len() {
        return Err(EvidenceCheckError::Invalid(format!(
            "K3 declaration index has {} export rows for {} transcript rows",
            declarations.len(),
            rows.len(),
        )));
    }
    for (export, row) in declarations.iter().zip(rows) {
        if export.line.to_string() != row.line {
            return Err(EvidenceCheckError::Invalid(format!(
                "K3 declaration index expected export line {}, but the transcript reports line {}",
                export.line, row.line
            )));
        }
        if export.kind.as_str() != row.kind {
            return Err(EvidenceCheckError::Invalid(format!(
                "K3 declaration index at line {} has export kind {}, but the transcript reports {}",
                export.line,
                export.kind.as_str(),
                row.kind
            )));
        }
    }
    Ok(())
}

fn compare_declaration_names(
    summary: &K3DeclarationNameSummary,
    rows: &[transcript::DeclarationRow<'_>],
) -> Result<(), EvidenceCheckError> {
    let declarations = &summary.bodies().declarations;
    compare_declaration_index(declarations, rows)?;
    for (index, (export, row)) in declarations.iter().zip(rows).enumerate() {
        if !summary.matches_name(index, row.name) {
            return Err(EvidenceCheckError::Invalid(format!(
                "K3 declaration name at export line {} differs from the transcript",
                export.line
            )));
        }
    }
    Ok(())
}

fn declaration_body_counts(summary: &K3DeclarationBodySummary) -> String {
    format!(
        ", {} non-inductive bodies, {} inductive blocks, {} distinct declared names",
        summary.declarations.len() - summary.inductive_blocks,
        summary.inductive_blocks,
        summary.declared_names,
    )
}

fn compare_accepted_statements(
    summary: &K3AcceptedStatementSummary,
    rows: &[transcript::DeclarationRow<'_>],
    accepted: &[consistency::AcceptedStatement<'_>],
) -> Result<String, EvidenceCheckError> {
    let declarations = summary.declarations();
    compare_declaration_names(declarations, rows)?;
    for statement in accepted {
        summary
            .compare_statement(
                statement.index,
                statement.level_params,
                statement.type_echo,
                statement.value_echo,
            )
            .map_err(k3_export::input_error)?;
    }
    let body_counts = declaration_body_counts(declarations.bodies());
    Ok(format!(
        "{body_counts}, {} accepted statements",
        accepted.len()
    ))
}

fn compare_base_recognition(
    summary: &K3BaseRecognitionSummary,
    rows: &[transcript::DeclarationRow<'_>],
) -> Result<usize, EvidenceCheckError> {
    let mut recognised = 0;
    for (index, row) in rows.iter().enumerate() {
        let recognised_base = summary.recognised_members(index).is_some();
        if recognised_base != (row.class == "recognised") {
            return Err(EvidenceCheckError::Invalid(format!(
                "K3 base recognition at export line {} differs from the transcript",
                row.line
            )));
        }
        recognised += usize::from(recognised_base);
    }
    Ok(recognised)
}

fn compare_base_families(
    summary: &K3BaseRecognitionSummary,
    rows: &[transcript::DeclarationRow<'_>],
    accepted: &[consistency::AcceptedStatement<'_>],
) -> Result<String, EvidenceCheckError> {
    let body_counts = compare_accepted_statements(summary.accepted_statements(), rows, accepted)?;
    let recognised = compare_base_recognition(summary, rows)?;
    Ok(format!(
        "{body_counts}, {recognised} recognised base families"
    ))
}

fn compare_fragment_classes(
    summary: &K3FragmentSummary,
    rows: &[transcript::DeclarationRow<'_>],
) -> Result<(usize, usize), EvidenceCheckError> {
    let mut inside = 0;
    let mut outside = 0;
    for (index, row) in rows.iter().enumerate() {
        let class = summary.class(index).ok_or_else(|| {
            EvidenceCheckError::Invalid(format!(
                "K3 fragment class is missing at export line {}",
                row.line
            ))
        })?;
        let agrees = match class {
            K3FragmentClass::Inside => matches!(row.class, "accepted" | "refused"),
            K3FragmentClass::Outside => row.class == "outside",
            K3FragmentClass::Recognised => row.class == "recognised",
        };
        if !agrees {
            return Err(EvidenceCheckError::Invalid(format!(
                "K3 fragment class at export line {} is {}, but the transcript reports {}",
                row.line,
                class.as_str(),
                row.class
            )));
        }
        inside += usize::from(matches!(class, K3FragmentClass::Inside));
        outside += usize::from(matches!(class, K3FragmentClass::Outside));
    }
    Ok((inside, outside))
}

fn compare_dependency_refusals(
    summary: &K3FragmentSummary,
    rows: &[transcript::DeclarationRow<'_>],
) -> Result<usize, EvidenceCheckError> {
    let reports = rows.iter().map(|row| match row.class {
        "accepted" => K3DependencyReport::Accepted,
        "refused" => K3DependencyReport::Refused(row.detail),
        _ => K3DependencyReport::NonInside,
    });
    summary
        .compare_dependency_refusals(reports)
        .map_err(k3_export::input_error)
}

fn compare_fragment_packet(
    summary: &K3FragmentSummary,
    rows: &[transcript::DeclarationRow<'_>],
    accepted: &[consistency::AcceptedStatement<'_>],
) -> Result<String, EvidenceCheckError> {
    let body_counts = compare_base_families(summary.base_families(), rows, accepted)?;
    let (inside, outside) = compare_fragment_classes(summary, rows)?;
    Ok(format!("{body_counts}, {inside} inside, {outside} outside"))
}

fn coverage_declarations(summary: &K3FragmentSummary) -> &[K3DeclarationIndexRow] {
    &summary
        .base_families()
        .accepted_statements()
        .declarations()
        .bodies()
        .declarations
}

fn required_for_receipt(error: EvidenceCheckError) -> EvidenceCheckError {
    match error {
        EvidenceCheckError::Unavailable(message) => EvidenceCheckError::Invalid(message),
        error => error,
    }
}

pub(super) fn with_receipt_packet<T>(
    root: &Path,
    consume: impl FnOnce(ReceiptPacket<'_>) -> anyhow::Result<T>,
) -> anyhow::Result<T> {
    let bytes = PacketBytes::read(root).map_err(required_for_receipt)?;
    let Packet {
        transcript,
        frames,
        accepted,
    } = bytes.parse(&Check::CoverageFigures)?;
    let export = k3_export::fragment_classes_with_hashes(root).map_err(required_for_receipt)?;
    compare_fragment_packet(&export.summary, &transcript.rows, &accepted)?;
    compare_dependency_refusals(&export.summary, &transcript.rows)?;
    let figures = figures::derive(
        coverage_declarations(&export.summary),
        &transcript.rows,
        &accepted,
        &frames,
    )?;
    consume(ReceiptPacket {
        figures,
        export_gzip_sha256: export.gzip_sha256,
        export_raw_sha256: export.raw_sha256,
        advice_sha256: k3_export::sha256_bytes(&bytes.advice),
        transcript_sha256: k3_export::sha256_bytes(&bytes.transcript),
    })
}

pub(super) fn run(
    root: &Path,
    json: bool,
    check: Check,
    output: &mut impl Write,
) -> anyhow::Result<()> {
    let root = canonical_root(root)?;
    let bytes = PacketBytes::read(&root)?;
    let Packet {
        transcript,
        frames,
        accepted,
    } = bytes.parse(&check)?;

    let rows = transcript.rows.len();
    let (verdict, body_counts) = match check {
        Check::FragmentClasses | Check::DependencyRefusals | Check::CoverageFigures => {
            let summary = k3_export::fragment_classes(&root)?;
            let counts = compare_fragment_packet(&summary, &transcript.rows, &accepted)?;
            if check == Check::FragmentClasses {
                ("K3 fragment classes match transcript", counts)
            } else {
                let dependency_refusals = compare_dependency_refusals(&summary, &transcript.rows)?;
                if check == Check::CoverageFigures {
                    return figures::write_figures(
                        output,
                        coverage_declarations(&summary),
                        &transcript.rows,
                        &accepted,
                        &frames,
                    );
                }
                (
                    "K3 dependency refusals match transcript",
                    format!("{counts}, {dependency_refusals} dependency refusals"),
                )
            }
        }
        Check::BaseFamilies => {
            let summary = k3_export::base_families(&root)?;
            (
                "K3 base families match transcript",
                compare_base_families(&summary, &transcript.rows, &accepted)?,
            )
        }
        Check::AcceptedStatements => {
            let summary = k3_export::accepted_statements(&root)?;
            (
                "K3 accepted statement echoes match export",
                compare_accepted_statements(&summary, &transcript.rows, &accepted)?,
            )
        }
        Check::DeclarationNames => {
            let summary = k3_export::declaration_names(&root)?;
            compare_declaration_names(&summary, &transcript.rows)?;
            (
                "K3 declaration names match transcript",
                declaration_body_counts(summary.bodies()),
            )
        }
        Check::DeclarationBodies => {
            let summary = k3_export::declaration_bodies(&root)?;
            compare_declaration_index(&summary.declarations, &transcript.rows)?;
            (
                "K3 declaration bodies are valid",
                declaration_body_counts(&summary),
            )
        }
        Check::NonInductiveBodies => {
            let summary = k3_export::non_inductive_bodies(&root)?;
            compare_declaration_index(&summary.declarations, &transcript.rows)?;
            let checked = summary.checked_bodies;
            (
                "K3 non-inductive declaration bodies are valid",
                format!(
                    ", {checked} non-inductive bodies, {} inductive envelopes",
                    rows - checked,
                ),
            )
        }
        Check::DeclarationIndex => {
            let declarations = k3_export::declaration_index(&root)?;
            compare_declaration_index(&declarations, &transcript.rows)?;
            ("K3 declaration index matches transcript", String::new())
        }
        Check::Consistency => ("K3 packet is consistent", String::new()),
        Check::Syntax => ("K3 packet syntax is valid", String::new()),
    };

    if json {
        let syntax = PacketSyntax {
            frame_lengths: frames.iter().map(|frame| frame.len()).collect(),
            declarations: transcript.rows,
            reported_summary: transcript.summary,
        };
        serde_json::to_writer_pretty(&mut *output, &syntax)?;
        writeln!(output)?;
    } else {
        writeln!(
            output,
            "{verdict} ({} advice frames, {rows} declaration rows{body_counts})",
            frames.len(),
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_olean::k3_export_syntax::{
        check_k3_base_families, check_k3_declaration_names, check_k3_fragment_classes,
        K3DeclarationKind,
    };

    const TEST_EXPORT: &str = r#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"a"}}
{"in":2,"str":{"pre":0,"str":"é"}}
{"ie":0,"bvar":0}
{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}
{"axiom":{"name":2,"levelParams":[],"type":0,"isUnsafe":false}}
"#;

    fn transcript_row<'a>(line: &'a str, kind: &'a str) -> transcript::DeclarationRow<'a> {
        transcript::DeclarationRow {
            line,
            kind,
            class: "outside",
            detail: "unsafe",
            name: "example",
            statement: None,
        }
    }

    #[test]
    fn declaration_index_checks_line_and_kind_at_equal_counts() {
        let declarations = [K3DeclarationIndexRow {
            line: 51,
            kind: K3DeclarationKind::Inductive,
        }];
        compare_declaration_index(&declarations, &[transcript_row("51", "inductive")]).unwrap();

        for (row, expected) in [
            (transcript_row("50", "inductive"), "expected export line 51"),
            (
                transcript_row("1844674407370955161600000000000", "inductive"),
                "expected export line 51",
            ),
            (transcript_row("51", "def"), "has export kind inductive"),
        ] {
            let error = compare_declaration_index(&declarations, &[row]).unwrap_err();
            assert!(error.to_string().contains(expected), "{error}");
        }
    }

    #[test]
    fn declaration_names_match_exactly_after_the_whole_roster() {
        let summary = check_k3_declaration_names(TEST_EXPORT.as_bytes()).unwrap();
        let mut rows = [transcript_row("5", "axiom"), transcript_row("6", "axiom")];
        rows[0].name = "[s1:a]";
        rows[1].name = "[s2:é]";
        compare_declaration_names(&summary, &rows).unwrap();

        rows[0].name = "[s1:b]";
        rows[1].kind = "def";
        let error = compare_declaration_names(&summary, &rows).unwrap_err();
        assert!(error
            .to_string()
            .contains("at line 6 has export kind axiom"));

        rows[1].kind = "axiom";
        let error = compare_declaration_names(&summary, &rows).unwrap_err();
        assert!(matches!(
            error,
            EvidenceCheckError::Invalid(reason)
                if reason == "K3 declaration name at export line 5 differs from the transcript"
        ));
    }

    #[test]
    fn rejects_recognition_claimed_for_a_non_inductive_row() {
        let summary = check_k3_base_families(TEST_EXPORT.as_bytes()).unwrap();
        let mut rows = [transcript_row("5", "axiom"), transcript_row("6", "axiom")];
        assert_eq!(compare_base_recognition(&summary, &rows).unwrap(), 0);

        rows[1].class = "recognised";
        let error = compare_base_recognition(&summary, &rows).unwrap_err();
        assert!(matches!(
            error,
            EvidenceCheckError::Invalid(reason)
                if reason == "K3 base recognition at export line 6 differs from the transcript"
        ));
    }

    #[test]
    fn fragment_classes_accept_refused_inside_and_reject_false_classes() {
        let export = r#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"a"}}
{"in":2,"str":{"pre":0,"str":"b"}}
{"ie":0,"sort":0}
{"def":{"name":1,"levelParams":[],"type":0,"value":0,"safety":"safe","hints":"abbrev","all":[1]}}
{"def":{"name":2,"levelParams":[],"type":0,"value":0,"safety":"unsafe","hints":"abbrev","all":[2]}}
"#;
        let summary = check_k3_fragment_classes(export.as_bytes()).unwrap();
        let mut rows = [transcript_row("5", "def"), transcript_row("6", "def")];
        for class in ["accepted", "refused"] {
            rows[0].class = class;
            assert_eq!(compare_fragment_classes(&summary, &rows).unwrap(), (1, 1));
        }

        rows[0].class = "outside";
        let error = compare_fragment_classes(&summary, &rows).unwrap_err();
        assert!(matches!(
            error,
            EvidenceCheckError::Invalid(reason)
                if reason == "K3 fragment class at export line 5 is inside, but the transcript reports outside"
        ));

        rows[0].class = "refused";
        rows[1].class = "refused";
        let error = compare_fragment_classes(&summary, &rows).unwrap_err();
        assert!(matches!(
            error,
            EvidenceCheckError::Invalid(reason)
                if reason == "K3 fragment class at export line 6 is outside, but the transcript reports refused"
        ));
    }

    #[test]
    fn dependency_refusals_compare_reported_classes_and_details() {
        let export = r#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"a"}}
{"in":2,"str":{"pre":0,"str":"b"}}
{"in":3,"str":{"pre":0,"str":"c"}}
{"ie":0,"sort":0}
{"ie":1,"const":{"name":1,"us":[]}}
{"def":{"name":1,"levelParams":[],"type":0,"value":0,"safety":"safe","hints":"abbrev","all":[1]}}
{"def":{"name":2,"levelParams":[],"type":0,"value":1,"safety":"safe","hints":"abbrev","all":[2]}}
{"axiom":{"name":3,"levelParams":[],"type":0,"isUnsafe":false}}
"#;
        let summary = check_k3_fragment_classes(export.as_bytes()).unwrap();
        let mut rows = [
            transcript_row("7", "def"),
            transcript_row("8", "def"),
            transcript_row("9", "axiom"),
        ];
        rows[0].class = "refused";
        rows[0].detail = "KCheck.Refusal.sort";
        rows[1].class = "refused";
        rows[1].detail = "dependency:[s1:a]";
        assert_eq!(compare_dependency_refusals(&summary, &rows).unwrap(), 1);

        rows[1].class = "accepted";
        assert!(matches!(
            compare_dependency_refusals(&summary, &rows),
            Err(EvidenceCheckError::Invalid(_))
        ));
    }

    #[test]
    fn declaration_index_checks_the_whole_roster() {
        let export = [K3DeclarationIndexRow {
            line: 2,
            kind: K3DeclarationKind::Def,
        }];
        compare_declaration_index(&[], &[]).unwrap();
        for (declarations, rows, expected) in [
            (&export[..], &[][..], "1 export rows for 0 transcript rows"),
            (
                &[][..],
                &[transcript_row("2", "def")][..],
                "0 export rows for 1 transcript rows",
            ),
        ] {
            let error = compare_declaration_index(declarations, rows).unwrap_err();
            assert!(error.to_string().contains(expected), "{error}");
        }
    }
}
