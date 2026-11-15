// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An export decided by the fenced reference entry: the reader, then
//! `reference_base_closed` over everything the export declares.
//!
//! The front door (`replay.rs`) replays an export with `clean olean replay
//! --fresh`'s engine. The quorum of the self-proof plan asks a different
//! member: the fenced entry (`clean_kernel::ReferenceKernel`), which starts
//! empty and admits every declaration itself, in `LeanReference`, with no
//! native-reducer table. This module joins the two: the export is read and
//! registered in the structural tier as the front door reads it, except that
//! every level is built node for node as its record states it
//! (`LevelBuild::AsWritten`), and that environment is only the SOURCE the
//! closed replay re-derives from. Its production caller is
//! `clean_export_check --reference --permit <axiom>... <export.ndjson>`,
//! the export-reading quorum member that Q4 will orchestrate.
//!
//! Why the levels differ from the front door's. The front door builds a
//! `max`/`imax` record through the kernel's simplifying constructors and
//! declines an export in which Lean could tell the result from the record
//! (R125). The entry's level algebra is pinned Lean's (R150), and since R150
//! the `.olean` loader hands it stored levels node for node; an export read
//! the same way reaches the entry as the same terms. Lean's own levels are
//! not all fixed points of the constructors (`max u (imax (v+1) u)` is built
//! as `imax (v+1) u`), so the front door declines exports this entry decides.
//!
//! An export is accepted when all of these hold, and each failure is a named
//! refusal:
//!
//! - the reader read it (a malformed or unsupported export is refused);
//! - the structural tier refused no declaration, and none is `unsafe` or
//!   `partial`;
//! - no declaration is over a level the reader built otherwise than written;
//! - the closed replay through the entry refused nothing, its extension
//!   bindings were the pinned table, and every declared name was admitted;
//! - every axiom admitted is one the caller permits. The quotient's
//!   `Quot.sound` is counted as an axiom, as Lean's `#print axioms` counts it.
//!   The entry itself admits no axiom outside Ax0 and refuses one by name,
//!   with everything that reaches it; the caller's list can only be narrower.

use std::collections::BTreeSet;
use std::io::BufRead;

use clean_kernel::name::Name;
use serde::Serialize;

use super::load::load_export;
use super::replay::ReaderRefusal;
use super::source::NdjsonSource;
use super::world::ExportMeta;
use crate::recheck_closed::reference_base::reference_base_closed;
use crate::recheck_closed::ClosedRecheckOptions;

/// The axioms of Lean's foundations: what a "proved" statement may rest on.
pub const FOUNDATIONAL_AXIOMS: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];

/// The fenced entry's verdict on one export.
#[derive(Debug, Clone, Serialize)]
pub struct ExportReferenceReport {
    /// Whether the export is accepted (module docs).
    pub accepted: bool,
    /// The export's header, once read.
    pub meta: Option<ExportMeta>,
    /// Set when the reader refused or declined the export.
    pub reader_error: Option<ReaderRefusal>,
    /// Names the export declares.
    pub declarations: usize,
    /// Of them, admitted through the entry.
    pub admitted: usize,
    /// The axioms admitted through the entry.
    pub axioms: Vec<String>,
    /// Of them, those the caller did not permit.
    pub unpermitted_axioms: Vec<String>,
    /// Every other refusal, each naming its subject.
    pub refusals: Vec<String>,
}

impl ExportReferenceReport {
    fn refused(meta: Option<ExportMeta>, reader_error: ReaderRefusal) -> Self {
        Self {
            accepted: false,
            meta,
            reader_error: Some(reader_error),
            declarations: 0,
            admitted: 0,
            axioms: Vec::new(),
            unpermitted_axioms: Vec::new(),
            refusals: Vec::new(),
        }
    }
}

/// Read the export in `reader` and decide it through the fenced reference
/// entry, permitting the axioms `permitted` (compared as rendered names).
pub fn reference_check_export_reader<R: BufRead>(
    reader: R,
    permitted: &[&str],
) -> ExportReferenceReport {
    let reader_refusal = |error: &super::error::NdjsonError| ReaderRefusal {
        rule: error.rule(),
        message: error.to_string(),
    };
    let source = match NdjsonSource::as_written(reader) {
        Ok(source) => source,
        Err(error) => return ExportReferenceReport::refused(None, reader_refusal(&error)),
    };
    let loaded = match load_export(source) {
        Ok(loaded) => loaded,
        Err(error) => return ExportReferenceReport::refused(None, reader_refusal(&error)),
    };

    let mut refusals: Vec<String> = Vec::new();
    for (name, reason) in &loaded.refused {
        refusals.push(format!("{}: {reason}", loaded.shown(name)));
    }
    for (name, marker) in &loaded.not_replayable {
        refusals.push(format!(
            "{}: {marker}, outside the fragment the entry checks",
            loaded.shown(name)
        ));
    }
    if let (Some(taint), count) = &loaded.level_taint {
        refusals.push(format!(
            "{}: its {} is over a level the reader built otherwise than written ({count} such \
             declaration(s))",
            taint.member, taint.path
        ));
    }

    let targets: BTreeSet<Name> = loaded.declared.iter().map(|d| d.name.clone()).collect();
    let mut axioms: Vec<String> = Vec::new();
    let mut admitted = 0usize;
    match reference_base_closed(&loaded.env, &targets, &ClosedRecheckOptions::default()) {
        Ok(base) => {
            for refusal in &base.report.refusals {
                refusals.push(format!("{}: {refusal:?}", refusal.subject()));
            }
            for (unit, refusal) in &base.entry_refusals {
                refusals.push(format!("{unit}: reference entry: {refusal}"));
            }
            if !base.report.extension_bindings_pinned {
                refusals
                    .push("the replay's extension bindings were not the pinned table".to_owned());
            }
            // The entry's environment holds exactly what the entry admitted
            // (the quotient primitives through `add_quot_checked`, which the
            // replay compares and does not count among its admissions).
            let entry = base.kernel().environment();
            for name in &targets {
                if entry.get_const(name).is_some() {
                    admitted += 1;
                } else {
                    refusals.push(format!(
                        "{}: declared by the export and not in the entry's environment",
                        loaded.shown(name)
                    ));
                }
            }
            axioms.clone_from(&base.report.axioms_admitted);
        }
        Err(refusal) => refusals.push(format!("the reference entry could not start: {refusal}")),
    }
    let unpermitted_axioms: Vec<String> = axioms
        .iter()
        .filter(|axiom| !permitted.contains(&axiom.as_str()))
        .cloned()
        .collect();
    refusals.sort();
    refusals.dedup();
    ExportReferenceReport {
        accepted: refusals.is_empty() && unpermitted_axioms.is_empty(),
        meta: Some(loaded.meta),
        reader_error: None,
        declarations: targets.len(),
        admitted,
        axioms,
        unpermitted_axioms,
        refusals,
    }
}
