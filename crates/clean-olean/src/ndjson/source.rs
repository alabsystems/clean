// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! [`ExportSource`]: an export, one resolved declaration at a time, and its
//! NDJSON reader [`NdjsonSource`].
//!
//! The loader reads declarations through the trait, not through NDJSON, so a
//! later binary export format (the FRO's announced next step) is another
//! implementation of [`ExportSource`] and nothing downstream changes.
//!
//! [`NdjsonSource`] streams: it reads one line at a time (each at most
//! [`MAX_LINE_BYTES`]), keeps only the three internalization tables between
//! lines, and hands each declaration on as soon as its line is read. It owns
//! the reader-level rules of Lean's `LeanExport.Parse`: a line is one JSON
//! object with exactly the keys of one record, an index is bound once, a
//! reference is to a bound index, and a name is declared once
//! (`Duplicate declaration`). Two rules come from later Lean kernels and are
//! applied here as reader rules: a record other than `quot` may not declare
//! `Quot`, `Quot.mk`, `Quot.lift` or `Quot.ind` (v4.33.1 `check_name`), and a
//! `quot` record must carry the name its kind installs.

use std::io::BufRead;

use clean_kernel::name::Name;
use hashbrown::HashSet;

use super::decl::ExportDeclaration;
use super::error::NdjsonError;
use super::json::{parse_line, JsonValue};
use super::levels::LevelTaint;
use super::records::declaration;
use super::tables::{LevelBuild, Tables};
use super::world::{read_meta, ExportMeta};
use crate::module::ParsedQuotKind;

/// The longest line the reader takes (128 MiB): a 50-million-digit `natVal`
/// fits. A longer line declines the export (`LineTooLong`, exit 2).
pub const MAX_LINE_BYTES: usize = 128 * 1024 * 1024;

/// An export, read one declaration at a time.
pub(crate) trait ExportSource {
    /// The export's header.
    fn meta(&self) -> &ExportMeta;

    /// The next declaration with the 1-based line it was read from, or
    /// `Ok(None)` at the end of the export. After an `Err` the source is
    /// spent: the export is refused or declined as the error says.
    fn next_declaration(&mut self) -> Result<Option<(u64, ExportDeclaration)>, NdjsonError>;

    /// Every name the source stores otherwise than the export wrote it
    /// (`names.rs`), with the written name: what a report shows.
    fn written_names(&self) -> std::collections::HashMap<Name, Name>;

    /// The first declaration whose stored data mentions a level that keeps the
    /// export from being accepted (`levels.rs`), and how many do.
    fn level_taint(&self) -> (Option<LevelTaint>, usize);
}

/// The names `quotDecl` adds, with the kind of `quot` record that installs
/// each.
const QUOT_NAMES: [(&str, ParsedQuotKind, &str); 4] = [
    ("Quot", ParsedQuotKind::Type, "type"),
    ("Quot.mk", ParsedQuotKind::Mk, "ctor"),
    ("Quot.lift", ParsedQuotKind::Lift, "lift"),
    ("Quot.ind", ParsedQuotKind::Ind, "ind"),
];

/// A lean4export NDJSON 3.x export.
pub(crate) struct NdjsonSource<R> {
    reader: R,
    line: u64,
    buf: Vec<u8>,
    meta: ExportMeta,
    tables: Tables,
    declared: HashSet<Name>,
    taint: Option<LevelTaint>,
    tainted: usize,
}

impl<R: BufRead> NdjsonSource<R> {
    /// Read the `meta` line and select the kernel rule set.
    ///
    /// # Errors
    ///
    /// The header is missing or malformed (reject), or states a format version
    /// other than 3.1 or a Lean version with no reviewed row (decline).
    pub(crate) fn new(reader: R) -> Result<Self, NdjsonError> {
        Self::with_levels(reader, LevelBuild::Constructors)
    }

    /// [`Self::new`], with every level built node for node as its record
    /// states it ([`LevelBuild::AsWritten`]).
    ///
    /// # Errors
    ///
    /// As [`Self::new`].
    pub(crate) fn as_written(reader: R) -> Result<Self, NdjsonError> {
        Self::with_levels(reader, LevelBuild::AsWritten)
    }

    fn with_levels(mut reader: R, level_build: LevelBuild) -> Result<Self, NdjsonError> {
        let mut buf = Vec::new();
        if !read_line_capped(&mut reader, &mut buf, 1)? {
            return Err(NdjsonError::Empty);
        }
        let value = parse_line(&buf).map_err(|error| NdjsonError::Json { line: 1, error })?;
        let meta = read_meta(value)?;
        Ok(Self {
            reader,
            line: 1,
            buf,
            meta,
            tables: Tables::new(level_build),
            declared: HashSet::new(),
            taint: None,
            tainted: 0,
        })
    }

    fn item(&mut self, value: JsonValue) -> Result<Option<ExportDeclaration>, NdjsonError> {
        let line = self.line;
        let JsonValue::Object(mut entries) = value else {
            return Err(NdjsonError::ExpectedObject { line });
        };
        let unknown = |entries: &[(String, JsonValue)]| NdjsonError::UnknownRecord {
            line,
            keys: entries.iter().map(|(k, _)| k.clone()).collect(),
        };
        match entries.len() {
            1 => {
                let Some((kind, data)) = entries.pop() else {
                    return Err(unknown(&entries));
                };
                let (decl, taint) = declaration(&self.tables, line, &kind, data)?;
                self.admit_names(line, &decl)?;
                if let Some(taint) = taint {
                    self.tainted += 1;
                    self.taint.get_or_insert(taint);
                }
                Ok(Some(decl))
            }
            2 => {
                let Some(at) = entries
                    .iter()
                    .position(|(k, _)| matches!(k.as_str(), "in" | "il" | "ie"))
                else {
                    return Err(unknown(&entries));
                };
                let (table, index) = entries.swap_remove(at);
                let Some((kind, data)) = entries.pop() else {
                    return Err(unknown(&entries));
                };
                let record = match table.as_str() {
                    "in" => "Name",
                    "il" => "Level",
                    _ => "Expr",
                };
                let index = super::fields::nat_value(line, record, &table, &index)?;
                match table.as_str() {
                    "in" => self.tables.bind_name(line, index, &kind, data)?,
                    "il" => self.tables.bind_level(line, index, &kind, data)?,
                    _ => self.tables.bind_expr(line, index, &kind, data)?,
                }
                Ok(None)
            }
            _ => Err(unknown(&entries)),
        }
    }

    /// Lean's `addConst` (one declaration per name), v4.33.1's reserved
    /// quotient names, and the replay's label round trip (which the stored
    /// names make by construction, `names.rs`; this checks it).
    fn admit_names(&mut self, line: u64, decl: &ExportDeclaration) -> Result<(), NdjsonError> {
        let record_name: &'static str = match decl {
            ExportDeclaration::Axiom { .. } => "axiom",
            ExportDeclaration::Definition { .. } => "def",
            ExportDeclaration::Theorem { .. } => "thm",
            ExportDeclaration::Opaque { .. } => "opaque",
            ExportDeclaration::Quot { .. } => "quot",
            ExportDeclaration::Inductive(_) => "inductive",
        };
        for name in decl.declared_names() {
            let rendered = name.to_string();
            let reserved = QUOT_NAMES.iter().find(|(n, _, _)| *n == rendered);
            match (decl, reserved) {
                (ExportDeclaration::Quot { kind, .. }, _) => {
                    let Some(&(expected, _, kind_label)) =
                        QUOT_NAMES.iter().find(|(_, k, _)| k == kind)
                    else {
                        return Err(NdjsonError::QuotientNameMismatch {
                            line,
                            kind: "unknown",
                            name: self.tables.shown(name),
                            expected: "Quot",
                        });
                    };
                    if *name != Name::from_string(expected) {
                        return Err(NdjsonError::QuotientNameMismatch {
                            line,
                            kind: kind_label,
                            name: self.tables.shown(name),
                            expected,
                        });
                    }
                }
                (_, Some(_)) if *name == Name::from_string(&rendered) => {
                    return Err(NdjsonError::ReservedQuotientName {
                        line,
                        name: rendered,
                        record: record_name,
                    });
                }
                _ => {}
            }
            if Name::from_string(&rendered) != *name {
                return Err(NdjsonError::UnrepresentableName {
                    line,
                    name: self.tables.shown(name),
                });
            }
            if !self.declared.insert(name.clone()) {
                return Err(NdjsonError::DuplicateDeclaration {
                    line,
                    name: self.tables.shown(name),
                });
            }
        }
        Ok(())
    }
}

impl<R: BufRead> ExportSource for NdjsonSource<R> {
    fn meta(&self) -> &ExportMeta {
        &self.meta
    }

    fn written_names(&self) -> std::collections::HashMap<Name, Name> {
        self.tables.escaped_names()
    }

    fn level_taint(&self) -> (Option<LevelTaint>, usize) {
        (self.taint.clone(), self.tainted)
    }

    fn next_declaration(&mut self) -> Result<Option<(u64, ExportDeclaration)>, NdjsonError> {
        loop {
            let next = self.line + 1;
            let mut buf = std::mem::take(&mut self.buf);
            let more = read_line_capped(&mut self.reader, &mut buf, next)?;
            self.line = next;
            if !more {
                return Ok(None);
            }
            let value = parse_line(&buf).map_err(|error| NdjsonError::Json { line: next, error });
            self.buf = buf;
            if let Some(decl) = self.item(value?)? {
                return Ok(Some((next, decl)));
            }
        }
    }
}

/// Read one line into `buf` (without its `\n`), at most [`MAX_LINE_BYTES`].
/// `Ok(false)` at the end of the input.
fn read_line_capped<R: BufRead>(
    reader: &mut R,
    buf: &mut Vec<u8>,
    line: u64,
) -> Result<bool, NdjsonError> {
    buf.clear();
    let mut saw_any = false;
    loop {
        let chunk = reader
            .fill_buf()
            .map_err(|e| NdjsonError::Io(format!("line {line}: {e}")))?;
        if chunk.is_empty() {
            return Ok(saw_any);
        }
        saw_any = true;
        let (take, done) = match chunk.iter().position(|&b| b == b'\n') {
            Some(at) => (at, true),
            None => (chunk.len(), false),
        };
        if buf.len() + take > MAX_LINE_BYTES {
            return Err(NdjsonError::LineTooLong {
                line,
                limit: MAX_LINE_BYTES,
            });
        }
        buf.extend_from_slice(&chunk[..take]);
        reader.consume(if done { take + 1 } else { take });
        if done {
            return Ok(true);
        }
    }
}
