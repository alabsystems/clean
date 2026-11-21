// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The lean4export NDJSON front door: `clean olean replay --from-export
//! <file>`, exit 0 (accept), 1 (reject) or 2 (decline).
//!
//! Every place upstream admits an independent kernel hands it a lean4export
//! NDJSON 3.1.0 file: `lake check`, `lake comparator`, `--paranoid`, Lake's
//! `external_kernels` and the Kernel Arena's `$IN`
//! (<https://github.com/leanprover/lean4export/blob/master/format_ndjson.md>).
//! This module reads one, strictly, into the same structural tier as an
//! `.olean` (`crate::import`'s registration), and replays it with
//! `clean olean replay --fresh`'s engine.
//!
//! - `json`: a strict, iterative tokenizer for one line, never through
//!   `serde_json::Value`: trailing bytes, duplicate keys (compared after
//!   unescaping) and positive exponents above 100,000 are refused by name
//!   (lean4#15542/#15577, #15628, #15574).
//! - `source`: `ExportSource`, the crate-internal front end the loader
//!   reads, and `NdjsonSource`, which streams NDJSON into it. Index tables refuse
//!   rebinding (index 0 included) and accept sparse and out-of-order indices.
//! - `world`: `meta.format.version` must be 3.1 (any patch), and
//!   `meta.lean.version` must have a row in the reviewed table of kernel rule
//!   sets whose world is R81's oracle; otherwise the export is declined.
//! - `tables`: the name, level and expression tables, hash-consed on shallow
//!   keys, a level's tree bounded by `MAX_LEVEL_TREE_NODES` and its composite
//!   `max` arguments by `MAX_LEVEL_COMPOSITE_ARGS`.
//! - `names`: a name component Clean's replay labels cannot spell back is
//!   stored escaped, and two names stored alike are declined (R118).
//! - `levels`: a level the kernel's constructors build otherwise than Lean
//!   reads it is declined (R125).
//! - `records`: the declaration records; an inductive record must be one
//!   block whose stored `isRec`/`isReflexive` are the kernel's, and over no
//!   rewritten level.
//! - `load`: registration in the `.olean` structural tier; the quotient enters
//!   only through `Environment::add_quot`, after `Eq`.
//! - `replay`: the decision, including R128's decline of an export that
//!   declares a name Lean keys a literal rule on and Clean does not admit.
//! - `reference`: the same reading decided by the fenced reference entry
//!   instead (`reference_check_export_reader`), with an axiom allow-list.
//! - `advice` (feature-gated): candidate frames from a tracing-core run beside
//!   that fenced entry, never a production-checker or replay claim.
//! - `write`: the other direction. `write_export` writes a cone of kernel
//!   declarations as an export in this format, and `check_export_round_trip`
//!   reads one back through this reader (unit Q1 of the self-proof plan;
//!   the `clean_export_write` binary).
//!
//! What is not here yet: exit arm (d) of the plan item -- per-declaration
//! equality with `clean olean replay --fresh` over a v4.30.0-rc2 lean4export
//! export of an Init module -- needs an export-minting lane
//! (`checkers-export-minting-lane`) that does not exist; no installed
//! toolchain ships `leanexport`.

#[cfg(feature = "kcheck-trace")]
pub mod advice;
mod closure;
mod decl;
mod error;
mod fields;
pub(crate) mod json;
mod levels;
mod load;
pub mod meaning;
mod names;
mod natval;
mod quot;
mod records;
mod original_guard;
mod reference;
mod replay;
mod source;
mod tables;
mod world;
mod write;

use std::io::BufRead;
use std::path::Path;
use std::time::Instant;

use error::NdjsonError;
use replay::check_export;
use source::NdjsonSource;

pub use error::ExitClass;
pub use natval::MAX_NAT_LITERAL_DIGITS;
pub use original_guard::check_trust_ir_r01_source_model;
pub use reference::{
    reference_check_export_reader, reference_kernel_from_export, ExportReferenceReport,
    LEAN_FOUNDATIONAL_AXIOMS,
};
pub use replay::{
    DeclarationRecord, DeclarationVerdict, ExportCheckOptions, ExportReport, FirstRefusal,
    ReaderRefusal,
};
pub use source::MAX_LINE_BYTES;
pub use tables::MAX_LEVEL_TREE_NODES;
pub use world::{ExportMeta, KernelRuleSet, ReviewedLeanVersion, REVIEWED_LEAN_VERSIONS};
pub use write::{
    check_export_round_trip, write_export, ExportWriteError, ExportWriteMeta, ExportWriteSummary,
    EXPORTER_NAME, FORMAT_VERSION,
};

/// Read an NDJSON export from `reader`, replay it and decide.
pub fn check_export_reader<R: BufRead>(reader: R, options: ExportCheckOptions) -> ExportReport {
    let start = Instant::now();
    match NdjsonSource::new(reader) {
        Ok(source) => check_export(source, options),
        Err(error) => ExportReport::reader_failure(
            None,
            &error,
            u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX),
        ),
    }
}

/// [`check_export_reader`] over the file at `path`. A file that cannot be
/// opened is declined (exit 2): nothing was judged.
pub fn check_export_path(path: &Path, options: ExportCheckOptions) -> ExportReport {
    match std::fs::File::open(path) {
        Ok(file) => check_export_reader(std::io::BufReader::new(file), options),
        Err(e) => ExportReport::reader_failure(
            None,
            &NdjsonError::Io(format!("{}: {e}", path.display())),
            0,
        ),
    }
}

#[cfg(test)]
mod tests;
