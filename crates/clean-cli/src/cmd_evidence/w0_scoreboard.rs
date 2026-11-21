// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Derive the full W0 v1 scoreboard from its historical source artifacts.

use super::checker_source::{self, CheckerSourceFigure, CHECKER_SOURCES};
use super::clean_p3::{self, CleanFigure};
use super::elaboration::{self, ElaborationFigure, ELABORATION_BASELINE};
use super::island_gaps::{self, GapFigure, ISLAND_GAPS};
use super::k3_scoreboard::{Accepted, Coverage, Decided};
use super::rule_families::{self, RuleFamilyFigure, RULE_INVENTORY};
use super::{derive_trust, k3_json, TrustFigure, CLEAN_PINS, SCOREBOARD, TRUST_PINS};
use crate::EvidenceCheckError;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fs;
use std::io::{self, Read, Write};
use std::path::Path;

const SCHEMA: &str = "clean.self_proof_scoreboard.v1";
// Preserve the source attribution in the v1 wire format during the shadow.
const DESCRIPTION: &str = concat!(
    "Unit W0 of docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md: the route's ",
    "headline figures, each read from the artifact that mints it by ",
    "scripts/self_proof_scoreboard.py. Every figure is as old as its source; ",
    "this file measures nothing.",
);

#[derive(Deserialize, Serialize, PartialEq, Eq)]
#[serde(untagged)]
pub(super) enum RowValue<T> {
    Present(T),
    Absent(Absent),
}

#[derive(Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct Absent {
    pub(super) absent: String,
}

impl<T: fmt::Display> fmt::Display for RowValue<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Present(row) => fmt::Display::fmt(row, f),
            Self::Absent(row) => f.write_str(&row.absent),
        }
    }
}

#[derive(Serialize)]
struct Board {
    headline: Headline,
    route: Route,
    schema: &'static str,
    what_this_is: &'static str,
}

#[derive(Serialize)]
struct Headline {
    decided_by_compiled_kcheck: RowValue<Decided>,
    planted_false_mints_clean: RowValue<CleanFigure>,
    planted_false_mints_trust: RowValue<TrustFigure>,
}

#[derive(Serialize)]
struct Route {
    accepted_by_kcheck_no_site: RowValue<Accepted>,
    checker_soundness: RowValue<CheckerSourceFigure>,
    clean_elaborates_theories: RowValue<ElaborationFigure>,
    island_gaps: RowValue<GapFigure>,
    lean_kernel_rule_families: RowValue<RuleFamilyFigure>,
}

enum SourceKind {
    File,
    Directory,
}

fn read_row<T>(
    root: &Path,
    relative: &str,
    kind: SourceKind,
    derive: impl FnOnce(&Path) -> Result<T, EvidenceCheckError>,
) -> Result<RowValue<T>, EvidenceCheckError> {
    let path = root.join(relative);
    let present = match fs::metadata(&path) {
        Ok(metadata) => match kind {
            SourceKind::File => metadata.is_file(),
            SourceKind::Directory => metadata.is_dir(),
        },
        Err(error)
            if matches!(
                error.kind(),
                io::ErrorKind::NotFound | io::ErrorKind::NotADirectory
            ) =>
        {
            false
        }
        Err(error) => {
            return Err(EvidenceCheckError::Unavailable(format!(
                "{}: {error}",
                path.display()
            )))
        }
    };
    if present {
        derive(root).map(RowValue::Present)
    } else {
        Ok(RowValue::Absent(Absent {
            absent: format!("{relative} does not exist"),
        }))
    }
}

impl Board {
    fn derive(root: &Path) -> Result<Self, EvidenceCheckError> {
        let coverage = Coverage::read(root)?;
        Ok(Self {
            headline: Headline {
                decided_by_compiled_kcheck: coverage.decided(),
                planted_false_mints_clean: read_row(
                    root,
                    CLEAN_PINS,
                    SourceKind::File,
                    clean_p3::derive,
                )?,
                planted_false_mints_trust: read_row(root, TRUST_PINS, SourceKind::File, |root| {
                    derive_trust(root).map(|(figure, _)| figure)
                })?,
            },
            route: Route {
                accepted_by_kcheck_no_site: coverage.accepted(),
                checker_soundness: read_row(
                    root,
                    CHECKER_SOURCES,
                    SourceKind::Directory,
                    checker_source::derive,
                )?,
                clean_elaborates_theories: read_row(
                    root,
                    ELABORATION_BASELINE,
                    SourceKind::File,
                    elaboration::derive,
                )?,
                island_gaps: read_row(root, ISLAND_GAPS, SourceKind::File, island_gaps::derive)?,
                lean_kernel_rule_families: read_row(
                    root,
                    RULE_INVENTORY,
                    SourceKind::File,
                    rule_families::derive,
                )?,
            },
            schema: SCHEMA,
            what_this_is: DESCRIPTION,
        })
    }

    fn write_json(&self, out: &mut impl Write) -> anyhow::Result<()> {
        let mut value = serde_json::to_value(self)?;
        value.sort_all_objects();
        k3_json::write(out, &value)
    }

    fn render(&self, out: &mut impl Write) -> io::Result<()> {
        let (headline, route) = (&self.headline, &self.route);
        writeln!(
            out,
            "SELF-PROOF SCOREBOARD (every figure is as old as its source)"
        )?;
        write_row(
            out,
            "  planted False minted, Clean : ",
            &headline.planted_false_mints_clean,
            |row| format!("{} of {} sites", row.minted_under_mutant, row.sites),
        )?;
        write_row(
            out,
            "  planted False minted, Trust : ",
            &headline.planted_false_mints_trust,
            |row| format!("{} of {} sites", row.minted_under_mutant, row.sites),
        )?;
        write_row(
            out,
            "  decided by compiled kcheck  : ",
            &headline.decided_by_compiled_kcheck,
            |row| format!("{} real declarations", row.real_declarations_decided),
        )?;
        write_row(
            out,
            "  accepted by kcheck, no site : ",
            &route.accepted_by_kcheck_no_site,
            |row| {
                format!(
                    "{} of {} in the fragment, of {} real declarations (the run claims no soundness; built by upstream Lean; interim loader)",
                    row.accepted, row.inside_fragment, row.ordinary_declarations
                )
            },
        )?;
        write_row(
            out,
            "  checker soundness headline  : ",
            &route.checker_soundness,
            |row| {
                format!(
                    "{} theorem(s) of type C3Owes KCheck.checker in source",
                    row.theorem_count()
                )
            },
        )?;
        write_row(
            out,
            "  Clean elaborates theories   : ",
            &route.clean_elaborates_theories,
            |row| format!("{} of {} modules", row.elaborated, row.modules),
        )?;
        write_row(
            out,
            "  island gaps open            : ",
            &route.island_gaps,
            |row| format!("{} of {} rows", row.open, row.rows),
        )?;
        write_row(
            out,
            "  Lean kernel rule families   : ",
            &route.lean_kernel_rule_families,
            |row| {
                format!(
                    "{} of {} specified ({} partial, {} unspecified)",
                    row.specified, row.families, row.partial, row.unspecified
                )
            },
        )
    }
}

fn write_row<T>(
    out: &mut impl Write,
    label: &str,
    row: &RowValue<T>,
    show: impl FnOnce(&T) -> String,
) -> io::Result<()> {
    match row {
        RowValue::Present(value) => writeln!(out, "{label}{}", show(value)),
        RowValue::Absent(reason) => writeln!(out, "{label}ABSENT ({})", reason.absent),
    }
}

pub(super) fn write(root: &Path, json: bool, out: &mut impl Write) -> anyhow::Result<()> {
    let board = Board::derive(root)?;
    if json {
        board.write_json(out)
    } else {
        board.render(out)?;
        Ok(())
    }
}

pub(super) fn publish(root: &Path, out: &mut impl Write) -> anyhow::Result<()> {
    let board = Board::derive(root)?;
    let path = root.join(SCOREBOARD);
    let unavailable =
        |error: io::Error| EvidenceCheckError::Unavailable(format!("{}: {error}", path.display()));
    let permissions = match fs::symlink_metadata(&path) {
        Ok(metadata) if metadata.is_file() => Some(metadata.permissions()),
        Ok(_) => {
            return Err(
                EvidenceCheckError::Invalid(format!("{SCOREBOARD} is not a regular file")).into(),
            );
        }
        Err(error) if error.kind() == io::ErrorKind::NotFound => None,
        Err(error) => return Err(unavailable(error).into()),
    };

    let mut bytes = Vec::new();
    board.write_json(&mut bytes)?;
    let mut staging = tempfile::NamedTempFile::new_in(root.join("data")).map_err(unavailable)?;
    staging.write_all(&bytes).map_err(unavailable)?;
    if let Some(permissions) = permissions {
        staging
            .as_file()
            .set_permissions(permissions)
            .map_err(unavailable)?;
    }
    staging
        .persist(&path)
        .map_err(|error| unavailable(error.error))?;

    board.render(out)?;
    writeln!(out, "wrote {SCOREBOARD}")?;
    Ok(())
}

pub(super) fn check(root: &Path, out: &mut impl Write) -> anyhow::Result<()> {
    let board = Board::derive(root)?;
    let mut expected = Vec::new();
    board.write_json(&mut expected)?;

    let path = root.join(SCOREBOARD);
    let file_error = |error: io::Error| match error.kind() {
        io::ErrorKind::NotFound | io::ErrorKind::NotADirectory => {
            EvidenceCheckError::Invalid(format!("{SCOREBOARD} does not exist"))
        }
        _ => EvidenceCheckError::Unavailable(format!("{}: {error}", path.display())),
    };
    if !fs::metadata(&path).map_err(file_error)?.is_file() {
        return Err(
            EvidenceCheckError::Invalid(format!("{SCOREBOARD} is not a regular file")).into(),
        );
    }
    let mut saved = Vec::new();
    fs::File::open(&path)
        .map_err(file_error)?
        .take(expected.len() as u64 + 1)
        .read_to_end(&mut saved)
        .map_err(file_error)?;
    if saved != expected {
        return Err(EvidenceCheckError::Invalid(format!(
            "{SCOREBOARD} differs from a re-derivation. Re-mint with scripts/self_proof_scoreboard.py --write"
        ))
        .into());
    }
    writeln!(
        out,
        "SELF_PROOF_SCOREBOARD=ok the record matches its sources"
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn refuse_board(root: &Path, expected_reason: &str) {
        let mut output = Vec::new();
        let error = check(root, &mut output).unwrap_err();
        assert!(matches!(
            error.downcast_ref::<EvidenceCheckError>(),
            Some(EvidenceCheckError::Invalid(reason)) if reason.contains(expected_reason)
        ));
        assert!(output.is_empty());
    }

    #[test]
    fn absent_sources_are_stable_across_stored_board_changes() {
        let root = tempfile::tempdir().unwrap();
        let mut absent_board = Vec::new();
        write(root.path(), true, &mut absent_board).unwrap();
        let value: serde_json::Value = serde_json::from_slice(&absent_board).unwrap();
        assert_eq!(value["schema"], SCHEMA);
        assert_eq!(
            value["headline"]["planted_false_mints_clean"]["absent"],
            format!("{CLEAN_PINS} does not exist")
        );
        assert_eq!(
            value["route"]["checker_soundness"]["absent"],
            format!("{CHECKER_SOURCES} does not exist")
        );
        assert_eq!(
            value["headline"]["decided_by_compiled_kcheck"],
            value["route"]["accepted_by_kcheck_no_site"]
        );

        let recorded = root.path().join(SCOREBOARD);
        fs::create_dir_all(recorded.parent().unwrap()).unwrap();
        fs::write(recorded, b"malformed saved board").unwrap();
        let mut same_board = Vec::new();
        write(root.path(), true, &mut same_board).unwrap();
        assert_eq!(same_board, absent_board);
    }

    #[test]
    fn invalid_source_refuses_before_writing_a_board() {
        let root = tempfile::tempdir().unwrap();
        let mut canonical = Vec::new();
        write(root.path(), true, &mut canonical).unwrap();
        let report = root.path().join(CLEAN_PINS);
        fs::create_dir_all(report.parent().unwrap()).unwrap();
        fs::write(report, b"malformed source report").unwrap();
        for json in [false, true] {
            let mut output = Vec::new();
            let err = write(root.path(), json, &mut output).unwrap_err();
            assert!(matches!(
                err.downcast_ref::<EvidenceCheckError>(),
                Some(EvidenceCheckError::Invalid(reason)) if reason.contains(CLEAN_PINS)
            ));
            assert!(output.is_empty());
        }

        refuse_board(root.path(), CLEAN_PINS);
        let recorded = root.path().join(SCOREBOARD);
        fs::create_dir_all(recorded.parent().unwrap()).unwrap();
        fs::write(&recorded, &canonical).unwrap();
        refuse_board(root.path(), CLEAN_PINS);
        let mut output = Vec::new();
        let err = publish(root.path(), &mut output).unwrap_err();
        assert!(matches!(
            err.downcast_ref::<EvidenceCheckError>(),
            Some(EvidenceCheckError::Invalid(reason)) if reason.contains(CLEAN_PINS)
        ));
        assert!(output.is_empty());
        assert_eq!(fs::read(&recorded).unwrap(), canonical);
    }

    #[test]
    fn publishes_the_same_board_as_the_renderer() {
        let root = tempfile::tempdir().unwrap();
        let recorded = root.path().join(SCOREBOARD);
        fs::create_dir(root.path().join("data")).unwrap();
        let mut canonical = Vec::new();
        write(root.path(), true, &mut canonical).unwrap();
        let mut expected_status = Vec::new();
        write(root.path(), false, &mut expected_status).unwrap();
        writeln!(expected_status, "wrote {SCOREBOARD}").unwrap();

        let mut output = Vec::new();
        publish(root.path(), &mut output).unwrap();
        assert_eq!(fs::read(&recorded).unwrap(), canonical);
        assert_eq!(output, expected_status);

        fs::write(&recorded, b"forged board").unwrap();
        publish(root.path(), &mut Vec::new()).unwrap();
        check(root.path(), &mut Vec::new()).unwrap();
        assert_eq!(fs::read(&recorded).unwrap(), canonical);
        assert_eq!(fs::read_dir(root.path().join("data")).unwrap().count(), 1);
    }

    #[test]
    fn saved_board_matches_only_exact_canonical_bytes() {
        let root = tempfile::tempdir().unwrap();
        let mut canonical = Vec::new();
        write(root.path(), true, &mut canonical).unwrap();
        refuse_board(root.path(), "does not exist");

        let recorded = root.path().join(SCOREBOARD);
        fs::create_dir_all(&recorded).unwrap();
        refuse_board(root.path(), "is not a regular file");
        fs::remove_dir(&recorded).unwrap();

        fs::write(&recorded, &canonical).unwrap();
        let mut output = Vec::new();
        check(root.path(), &mut output).unwrap();
        assert_eq!(
            output.as_slice(),
            b"SELF_PROOF_SCOREBOARD=ok the record matches its sources\n"
        );
        assert_eq!(fs::read(&recorded).unwrap(), canonical);

        let text = std::str::from_utf8(&canonical).unwrap();
        let crlf = text.replace('\n', "\r\n");
        let extra_line = format!("{text}\n");
        for variant in [
            crlf.as_bytes(),
            extra_line.as_bytes(),
            text.trim_end().as_bytes(),
        ] {
            fs::write(&recorded, variant).unwrap();
            refuse_board(root.path(), "differs from a re-derivation");
            assert_eq!(fs::read(&recorded).unwrap().as_slice(), variant);
        }
    }
}
