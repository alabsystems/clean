// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The export writer: a cone of kernel declarations as a lean4export NDJSON
//! 3.1.0 file, written by Clean with no adapter and no Lean process.
//!
//! This is unit Q1 of `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`:
//! every member of the quorum is to read the same bytes, and until now only
//! Lean could produce them (`scripts/lean_export_mint.sh` runs lean4export;
//! `MintExports.lean` runs inside Lean). The production caller is the
//! `clean_export_write` binary.
//!
//! - [`write_export`] plans the cone of the targets over an [`Environment`]
//!   from the serialized expressions and their literal support, using the
//!   closed replay's ordering algorithm (`recheck_closed::cone_order`), and
//!   writes one record per unit, in that order: every constant a record
//!   mentions is declared by an earlier record or by the record itself
//!   (`ExportWriteError::UndeclaredReference` otherwise), so a reader that
//!   checks as it reads never meets an unknown constant. A cone that reaches
//!   one quotient constant is planned again with all four (`Quot`,
//!   `Quot.mk`, `Quot.lift`, `Quot.ind`): Lean's kernel declares them by one
//!   declaration (`quotDecl`), and lean4export writes the whole package,
//!   after `Eq`, whenever its cone reaches one of them.
//! - `cone`: the kernel's records as the format's declarations, with what the
//!   kernel does not hold derived or refused.
//! - `tables`: the name, level and expression tables; indices in order of
//!   first use, a node identified by its fields and its children's indices.
//! - `records`: the declaration records.
//! - `json`: the bytes, as `Lean.Json.compress` writes them.
//!
//! The output is a function of the environment's content and the targets:
//! no address, hash order or clock reaches it.
//!
//! Names are written as the environment holds them. The export READER stores
//! some names escaped (`names.rs`, R118: a component with a `.` in it, or one
//! that reads as a number); an environment it built is written with the
//! reader's record of the names as written (`write_cone`), and
//! [`write_export`] refuses a component in the escaped form rather than write
//! a name that is not Lean's.
//!
//! [`check_export_round_trip`] reads an export back through Clean's own reader
//! (`NdjsonSource`, the front door's, with every level built node for node as
//! its record states it: `LevelBuild::AsWritten`) and writes what it read
//! again: the second writing must be the first, byte for byte. The serialization states
//! every name, level, expression node and flag of a declaration, so two
//! declaration sequences that serialize alike are structurally equal in
//! everything the writer carries. `tables` explains the omitted binder names
//! and `mdata` payloads. A reader that rebuilds a level or stores a name
//! differently from its written form fails the check.
//!
//! What this does NOT establish: that the declarations are well-typed (the
//! writer checks nothing; `clean_export_check` and
//! [`super::reference_check_export_reader`] decide an export), or that Lean's
//! own tools read the file as Clean's reader does. Lean's kernel accepting
//! the file is measured by `scripts/lean_export_replay.sh`.

mod cone;
mod error;
mod json;
mod records;
mod tables;

use std::collections::BTreeSet;
use std::io::{BufRead, Write};

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_kernel::quot::{names as quot_names, QuotKind};

use super::decl::ExportDeclaration;
use super::error::NdjsonError;
use super::source::{ExportSource, NdjsonSource};
use crate::recheck_closed::{cone_order, PlannedUnit};
use json::Json;
use tables::{Emitter, Spelling};

pub use error::ExportWriteError;

/// `meta.exporter.name` of every export this writer writes.
pub const EXPORTER_NAME: &str = "clean-export";

/// `meta.format.version`: lean4export's NDJSON format, the one the front
/// door reads.
pub const FORMAT_VERSION: &str = "3.1.0";

/// The Lean whose kernel rules the declarations are stated for: what the
/// export's `meta.lean` says. A reader selects its rule set by the version.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportWriteMeta {
    /// `meta.lean.version`, for example `4.30.0-rc2`.
    pub lean_version: String,
    /// `meta.lean.githash`.
    pub lean_githash: String,
}

/// What [`write_export`] wrote.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ExportWriteSummary {
    /// Declaration records (an inductive block is one).
    pub records: usize,
    /// Names those records declare.
    pub declarations: usize,
    /// The axioms declared, rendered unambiguously, in the order written.
    pub axioms: Vec<String>,
    /// Lines, the `meta` line included.
    pub lines: u64,
    /// Bytes.
    pub bytes: u64,
    /// SHA-256 of the bytes, lowercase hexadecimal.
    pub sha256: String,
    /// Name records.
    pub names: usize,
    /// Level records.
    pub levels: usize,
    /// Expression records.
    pub exprs: usize,
}

fn meta_record(meta: &ExportWriteMeta) -> Json {
    let text = |s: &str| Json::Str(s.to_owned());
    Json::Object(vec![(
        "meta",
        Json::Object(vec![
            (
                "exporter",
                Json::Object(vec![
                    ("name", text(EXPORTER_NAME)),
                    ("version", text(env!("CARGO_PKG_VERSION"))),
                ]),
            ),
            (
                "lean",
                Json::Object(vec![
                    ("githash", text(&meta.lean_githash)),
                    ("version", text(&meta.lean_version)),
                ]),
            ),
            (
                "format",
                Json::Object(vec![("version", text(FORMAT_VERSION))]),
            ),
        ]),
    )])
}

/// Write `declarations`, in order, after the `meta` line. `spelling` is the
/// reader's record of the names it stored otherwise than written (empty when
/// the declarations were read from no export).
pub(crate) fn write_declarations<W, I>(
    meta: &ExportWriteMeta,
    declarations: I,
    spelling: Spelling,
    out: W,
) -> Result<ExportWriteSummary, ExportWriteError>
where
    W: Write,
    I: IntoIterator<Item = Result<ExportDeclaration, ExportWriteError>>,
{
    let mut emitter = Emitter::new(out, spelling);
    emitter.record(&meta_record(meta))?;
    let mut records = 0usize;
    let mut declared = 0usize;
    let mut axioms = Vec::new();
    for declaration in declarations {
        let declaration = declaration?;
        records += 1;
        declared += declaration.declared_names().len();
        if let ExportDeclaration::Axiom { header, .. } = &declaration {
            axioms.push(header.name.to_unambiguous_string());
        }
        records::write_declaration(&mut emitter, &declaration)?;
    }
    let totals = emitter.finish()?;
    Ok(ExportWriteSummary {
        records,
        declarations: declared,
        axioms,
        lines: totals.lines,
        bytes: totals.bytes,
        sha256: totals.sha256,
        names: totals.names,
        levels: totals.levels,
        exprs: totals.exprs,
    })
}

/// Write the dependency cone of `targets` in `env` to `out` as a lean4export
/// NDJSON 3.1.0 export (module docs).
///
/// # Errors
///
/// The first thing that cannot be written as Lean's format states it, or an
/// output error. What reached `out` before an error is not an export.
pub fn write_export<W: Write>(
    env: &Environment,
    targets: &BTreeSet<Name>,
    meta: &ExportWriteMeta,
    out: W,
) -> Result<ExportWriteSummary, ExportWriteError> {
    write_cone(env, targets, meta, Spelling::new(), out)
}

/// [`write_export`] over an environment the export reader built: `spelling`
/// is that reader's record of the names it stored otherwise than written.
pub(crate) fn write_cone<W: Write>(
    env: &Environment,
    targets: &BTreeSet<Name>,
    meta: &ExportWriteMeta,
    spelling: Spelling,
    out: W,
) -> Result<ExportWriteSummary, ExportWriteError> {
    let mut plan = cone_order(env, targets);
    let reaches_quotient = plan.units.iter().any(|unit| {
        matches!(unit, PlannedUnit::Constant(name)
            if env.get_quot(name).is_some_and(|quot| quot.kind != QuotKind::Sound))
    });
    if reaches_quotient {
        // The whole quotient package (module docs).
        let mut widened = targets.clone();
        widened.extend(
            [
                &*quot_names::QUOT,
                &*quot_names::QUOT_MK,
                &*quot_names::QUOT_LIFT,
                &*quot_names::QUOT_IND,
            ]
            .into_iter()
            .cloned(),
        );
        plan = cone_order(env, &widened);
    }
    if let Some(name) = plan.absent.iter().next() {
        return Err(ExportWriteError::AbsentConstant {
            name: name.to_unambiguous_string(),
        });
    }
    if let Some(names) = plan.cycles.into_iter().next() {
        return Err(ExportWriteError::DependencyCycle { names });
    }
    let declarations = plan
        .units
        .iter()
        .map(|unit| cone::unit_declaration(env, unit));
    write_declarations(meta, declarations, spelling, out)
}

fn read_back(error: &NdjsonError) -> ExportWriteError {
    ExportWriteError::ReadBack {
        rule: error.rule(),
        message: error.to_string(),
    }
}

/// Read the export in `reader` with Clean's reader and write what was read
/// again: it must be `written`, byte for byte (module docs).
///
/// # Errors
///
/// [`ExportWriteError::ReadBack`] when the reader refuses or declines the
/// export, [`ExportWriteError::RoundTrip`] when the second writing differs
/// from the first or the reader rebuilt a level otherwise than written.
pub fn check_export_round_trip<R: BufRead>(
    reader: R,
    written: &ExportWriteSummary,
) -> Result<(), ExportWriteError> {
    let mut source = NdjsonSource::as_written(reader).map_err(|e| read_back(&e))?;
    let meta = ExportWriteMeta {
        lean_version: source.meta().lean_version.clone(),
        lean_githash: source.meta().lean_githash.clone(),
    };
    // Read everything first: the reader's record of the names it stored
    // escaped (R118) is complete only then, and the second writing spells
    // them as the first did.
    let mut declarations = Vec::new();
    while let Some((_, declaration)) = source.next_declaration().map_err(|e| read_back(&e))? {
        declarations.push(Ok(declaration));
    }
    let again = write_declarations(&meta, declarations, source.written_names(), std::io::sink())?;
    if let (Some(taint), count) = source.level_taint() {
        return Err(ExportWriteError::RoundTrip {
            problem: format!(
                "the reader built a level otherwise than written in {count} declaration(s); the \
                 first: {taint}"
            ),
        });
    }
    if again != *written {
        return Err(ExportWriteError::RoundTrip {
            problem: format!(
                "written {} record(s), {} line(s), {} byte(s), sha256 {}; read back and written \
                 again {} record(s), {} line(s), {} byte(s), sha256 {}",
                written.records,
                written.lines,
                written.bytes,
                written.sha256,
                again.records,
                again.lines,
                again.bytes,
                again.sha256
            ),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests;
