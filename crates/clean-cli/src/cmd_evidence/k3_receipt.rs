// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reconstruct and check the recorded K3 coverage receipt.

use super::k3_export::EXPORT;
use super::k3_inputs::{canonical_root, find_regular_file};
use super::k3_json;
use super::k3_packet::{self, Figures, ReceiptPacket, ADVICE, TRANSCRIPT};
use super::k3_sources::{
    python_whitespace, read_object, read_source_digests, validate_source_header,
    verify_source_pins, MovedSources, RunFacts, SourcePinsError, RECORD, SOURCES_MOVED,
};
use crate::EvidenceCheckError;
use serde::{de, Deserialize, Deserializer, Serialize};
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::fs;
use std::io::Write;
use std::path::Path;

pub(super) const LABELS: Labels<'static> = Labels {
    checker: Cow::Borrowed(concat!(
        "kcheck_labelled, KCheck.kcheckBytes (by definition KCheck.checker's kcheck from Advice.start of the frame); this run claims NO soundness: ",
        "whether a theorem of KCheckSpec.C3Owes KCheck.checker is in source is the scoreboard's checker-soundness line, and nothing shown ties ",
        "the executable upstream Lean compiled to the term that theorem is about",
    )),
    compiled_by: Cow::Borrowed(
        "upstream Lean (lake build under the pinned toolchain); not Clean, not Trust",
    ),
    loader: Cow::Borrowed(
        "interim, unproved; an inductive record's recursor and rules are compared with the base family by the loader, never checked by kcheck",
    ),
    site: Cow::Borrowed("none: no acceptance of clean or Trust consults this run"),
};
pub(super) const DECIDED_REASON: &str =
    "no site consults the run; steps K4b and K5 of the interim thread owe the first one";
const RECORD_ABSENT: &str = "data/kcheck_coverage.json does not exist";
const DESCRIPTION: &str = concat!(
    "Step K3 of the interim thread of docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md: the real ",
    "declarations the adopted checker accepts in one run of theories/kcheck_run, re-derived by ",
    "scripts/kcheck_coverage.py. An accepted declaration is not a proved one and decides no site.",
);

#[derive(Debug)]
pub(super) struct VerifiedCoverage {
    pub(super) accepted: usize,
    pub(super) inside_fragment: usize,
    pub(super) ordinary_declarations: usize,
    pub(super) sources: usize,
}

#[derive(Debug)]
pub(super) enum CoverageAbsence {
    MissingReceipt,
    SourcesMoved(MovedSources),
}

impl CoverageAbsence {
    pub(super) fn reason(&self) -> &'static str {
        match self {
            Self::MissingReceipt => RECORD_ABSENT,
            Self::SourcesMoved(_) => SOURCES_MOVED,
        }
    }
}

#[derive(Debug)]
pub(super) enum CoverageError {
    Absent(CoverageAbsence),
    Check(EvidenceCheckError),
}

impl From<EvidenceCheckError> for CoverageError {
    fn from(error: EvidenceCheckError) -> Self {
        Self::Check(error)
    }
}

impl From<CoverageError> for EvidenceCheckError {
    fn from(error: CoverageError) -> Self {
        match error {
            CoverageError::Absent(CoverageAbsence::MissingReceipt) => {
                Self::Unavailable(RECORD_ABSENT.to_owned())
            }
            CoverageError::Absent(CoverageAbsence::SourcesMoved(moved)) => moved.into(),
            CoverageError::Check(error) => error,
        }
    }
}

impl From<SourcePinsError> for CoverageError {
    fn from(error: SourcePinsError) -> Self {
        match error {
            SourcePinsError::Moved(moved) => Self::Absent(CoverageAbsence::SourcesMoved(moved)),
            SourcePinsError::Check(error) => Self::Check(error),
        }
    }
}

impl From<anyhow::Error> for CoverageError {
    fn from(error: anyhow::Error) -> Self {
        let check = error
            .downcast::<EvidenceCheckError>()
            .unwrap_or_else(|error| EvidenceCheckError::Invalid(format!("{error:#}")));
        Self::Check(check)
    }
}

#[derive(Deserialize)]
#[serde(transparent)]
struct ReceiptInput(#[serde(deserialize_with = "read_object")] ReceiptHeader);

// Extract the recorded metadata needed to reconstruct the receipt. The
// canonical byte comparison also checks all derived fields.
#[derive(Deserialize)]
struct ReceiptHeader {
    #[serde(deserialize_with = "read_object")]
    advice: AdviceHeader,
    #[serde(deserialize_with = "read_labels")]
    labels: Labels<'static>,
    #[serde(deserialize_with = "read_decided")]
    real_declarations_decided: u64,
    #[serde(deserialize_with = "read_object")]
    run: RunFacts,
    schema: String,
    #[serde(deserialize_with = "read_source_digests")]
    sources: BTreeMap<String, String>,
}

#[derive(Deserialize)]
struct AdviceHeader {
    origin: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct Labels<'input> {
    checker: Cow<'input, str>,
    compiled_by: Cow<'input, str>,
    loader: Cow<'input, str>,
    site: Cow<'input, str>,
}

fn read_labels<'de, D: Deserializer<'de>>(input: D) -> Result<Labels<'static>, D::Error> {
    read_object(input).map_err(|error| {
        de::Error::custom(format_args!(
            "the receipt's labels are not the ones this script writes ({error})"
        ))
    })
}

fn read_decided<'de, D: Deserializer<'de>>(input: D) -> Result<u64, D::Error> {
    u64::deserialize(input).map_err(|error| {
        de::Error::custom(format_args!(
            "real_declarations_decided must be the integer 0 ({error})"
        ))
    })
}

// Keep the fields in Python's sorted order, including the nested records.
#[derive(Serialize)]
struct CanonicalReceipt<'input> {
    advice: Advice<'input>,
    export: Export<'input>,
    figures: Figures<'input>,
    labels: Labels<'static>,
    real_declarations_decided: u64,
    real_declarations_decided_reason: &'static str,
    run: &'input RunFacts,
    schema: &'input str,
    sources: &'input BTreeMap<String, String>,
    transcript: Transcript<'input>,
    what_this_is: &'static str,
}

#[derive(Serialize)]
struct Advice<'input> {
    origin: &'input str,
    path: &'static str,
    sha256: &'input str,
}

#[derive(Serialize)]
struct Export<'input> {
    path: &'static str,
    sha256_decompressed: &'input str,
    sha256_file: &'input str,
}

#[derive(Serialize)]
struct Transcript<'input> {
    path: &'static str,
    sha256: &'input str,
}

fn parse_header(bytes: &[u8]) -> Result<ReceiptHeader, EvidenceCheckError> {
    let text = std::str::from_utf8(bytes)
        .map_err(|error| EvidenceCheckError::Invalid(format!("{RECORD} is not UTF-8: {error}")))?;
    let ReceiptInput(header) = serde_json::from_str(text)
        .map_err(|error| EvidenceCheckError::Invalid(format!("{RECORD}: {error}")))?;
    if header.real_declarations_decided != 0 {
        return Err(EvidenceCheckError::Invalid(format!(
            "{RECORD} states real_declarations_decided = {}. Only a site record can raise it above 0.",
            header.real_declarations_decided
        )));
    }
    if header.labels != LABELS {
        return Err(EvidenceCheckError::Invalid(format!(
            "{RECORD}'s labels are not the ones this script writes"
        )));
    }
    let origin = header.advice.origin.as_str();
    if origin.is_empty() || origin.trim_matches(python_whitespace) != origin {
        return Err(EvidenceCheckError::Invalid(format!(
            "{RECORD} names no producer of the advice (advice.origin)"
        )));
    }
    validate_source_header(&header.schema, &header.sources, &header.run)?;
    Ok(header)
}

fn require_canonical(actual: &[u8], expected: &[u8]) -> Result<(), EvidenceCheckError> {
    if actual == expected {
        return Ok(());
    }
    let offset = actual
        .iter()
        .zip(expected)
        .position(|(actual, expected)| actual != expected)
        .unwrap_or(actual.len().min(expected.len()));
    Err(EvidenceCheckError::Invalid(format!(
        "{RECORD} differs from a re-derivation at byte offset {offset}. Expected the canonical v1 record."
    )))
}

fn compare_receipt(
    bytes: &[u8],
    header: &ReceiptHeader,
    packet: ReceiptPacket<'_>,
) -> anyhow::Result<(usize, usize, usize)> {
    let receipt = CanonicalReceipt {
        advice: Advice {
            origin: &header.advice.origin,
            path: ADVICE,
            sha256: &packet.advice_sha256,
        },
        export: Export {
            path: EXPORT,
            sha256_decompressed: &packet.export_raw_sha256,
            sha256_file: &packet.export_gzip_sha256,
        },
        figures: packet.figures,
        labels: LABELS,
        real_declarations_decided: 0,
        real_declarations_decided_reason: DECIDED_REASON,
        run: &header.run,
        schema: &header.schema,
        sources: &header.sources,
        transcript: Transcript {
            path: TRANSCRIPT,
            sha256: &packet.transcript_sha256,
        },
        what_this_is: DESCRIPTION,
    };
    let mut canonical = Vec::new();
    k3_json::write(&mut canonical, &receipt)?;
    require_canonical(bytes, &canonical)?;
    Ok((
        receipt.figures.accepted,
        receipt.figures.inside_fragment,
        receipt.figures.ordinary_declarations,
    ))
}

fn read_receipt(root: &Path) -> Result<Vec<u8>, CoverageError> {
    let path = find_regular_file(root, RECORD)?
        .ok_or(CoverageError::Absent(CoverageAbsence::MissingReceipt))?;
    fs::read(&path).map_err(|error| {
        EvidenceCheckError::Unavailable(format!("{}: {error}", path.display())).into()
    })
}

/// Read the reported run facts for display, including on stale source pins.
pub(super) fn recorded_run(root: &Path) -> Result<RunFacts, EvidenceCheckError> {
    let root = canonical_root(root)?;
    let bytes = read_receipt(&root)?;
    Ok(parse_header(&bytes)?.run)
}

pub(super) fn verify(root: &Path) -> Result<VerifiedCoverage, CoverageError> {
    let root = canonical_root(root)?;
    let bytes = read_receipt(&root)?;
    let header = parse_header(&bytes)?;
    let (accepted, inside_fragment, ordinary_declarations) =
        k3_packet::with_receipt_packet(&root, |packet| compare_receipt(&bytes, &header, packet))?;
    let sources = verify_source_pins(&root, &header.sources, &header.run)?;
    Ok(VerifiedCoverage {
        accepted,
        inside_fragment,
        ordinary_declarations,
        sources,
    })
}

pub(super) fn run(root: &Path, output: &mut impl Write) -> anyhow::Result<()> {
    let sources = verify(root).map_err(EvidenceCheckError::from)?.sources;
    writeln!(
        output,
        "K3 coverage receipt matches the validated packet and {sources} source files"
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};

    fn header_fixture() -> Value {
        json!({
            "advice": {"origin": "test producer"},
            "labels": LABELS,
            "real_declarations_decided": 0,
            "run": {
                "command": "test executable",
                "executable_sha256": "0".repeat(64),
                "lean_toolchain": "test pin",
                "lean_version": "test version",
            },
            "schema": "clean.kcheck_coverage.v1",
            "sources": {},
        })
    }

    fn expect_invalid(record: &Value, expected: &str) {
        assert!(matches!(
            parse_header(record.to_string().as_bytes()),
            Err(EvidenceCheckError::Invalid(reason)) if reason.contains(expected)
        ));
    }

    #[test]
    fn distinguishes_absence_from_a_missing_packet_and_reads_recorded_run_facts() {
        let root = tempfile::tempdir().unwrap();
        let Err(CoverageError::Absent(absence)) = verify(root.path()) else {
            panic!("expected a missing receipt");
        };
        assert_eq!(absence.reason(), format!("{RECORD} does not exist"));
        assert!(matches!(
            EvidenceCheckError::from(CoverageError::Absent(absence)),
            EvidenceCheckError::Unavailable(reason) if reason == RECORD_ABSENT
        ));

        let path = root.path().join(RECORD);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, header_fixture().to_string()).unwrap();
        assert_eq!(
            recorded_run(root.path()).unwrap().command,
            "test executable"
        );
        assert!(matches!(
            verify(root.path()),
            Err(CoverageError::Check(EvidenceCheckError::Invalid(reason))) if reason.contains(ADVICE)
        ));
    }

    #[test]
    fn preflight_checks_integer_zero_labels_and_the_advice_origin() {
        let fixture = header_fixture();
        assert!(parse_header(fixture.to_string().as_bytes()).is_ok());
        for decided in [json!(1), json!(false), json!(0.0), json!("0")] {
            let mut changed = fixture.clone();
            changed["real_declarations_decided"] = decided;
            expect_invalid(&changed, "real_declarations_decided");
        }

        let mut changed = fixture.clone();
        changed["labels"].as_object_mut().unwrap().remove("site");
        expect_invalid(&changed, "labels are not the ones");
        changed["labels"] = json!(LABELS);
        changed["labels"]["checker"] = json!("reworded");
        expect_invalid(&changed, "labels are not the ones");

        for origin in ["", " producer", "producer\u{1c}", "\u{a0}"] {
            let mut changed = fixture.clone();
            changed["advice"]["origin"] = json!(origin);
            expect_invalid(&changed, "advice.origin");
        }
    }

    #[test]
    fn refuses_an_equivalent_record_with_noncanonical_bytes() {
        let compact = b"{\"count\":0}\n";
        let canonical = b"{\n  \"count\": 0\n}\n";
        let value = |bytes: &[u8]| serde_json::from_slice::<Value>(bytes).unwrap();
        assert_eq!(value(compact), value(canonical));
        assert!(require_canonical(canonical, canonical).is_ok());
        assert!(matches!(
            require_canonical(compact, canonical),
            Err(EvidenceCheckError::Invalid(reason))
                if reason.contains("byte offset 1") && reason.contains("canonical v1 record")
        ));
    }
}
