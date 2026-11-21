// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Candidate advice from an export through the feature-gated tracing core.
//!
//! This producer runs beside the fenced reference entry. It is not the
//! production checker, its bytes carry no replay claim, and `kcheck` decides
//! whether any non-empty frame is valid advice.

use std::collections::{BTreeMap, BTreeSet};
use std::io::BufRead;

use clean_kernel::name::Name;

use super::load::load_export;
use super::source::NdjsonSource;
use crate::recheck_closed::reference_base::{
    reference_base_core_tracing, AdviceCandidateObservation, TraceObservation,
};
use crate::recheck_closed::ClosedRecheckOptions;

/// Per-declaration operation budget used by the existing C4 tracing pilot.
const TRACE_OPERATIONS: u64 = 100_000;

/// Failure to read an export or run the independent tracing replay.
#[derive(Debug, thiserror::Error)]
pub enum AdviceError {
    /// The strict as-written export reader or structural loader refused input.
    #[error("candidate advice export reader: {0}")]
    Export(String),
    /// The observing replay itself could not run.
    #[error("candidate advice tracing replay: {0}")]
    Tracing(String),
}

/// Advice supplied by the observing replay for an accepted ordinary declaration.
#[derive(Clone, Copy)]
pub enum AdviceFrameSource {
    /// Preserve the original trace journal and its wire predictions.
    DiagnosticJournal,
    /// Use the separate search that follows the adopted checker's token cursor.
    ReplayCandidate,
}

/// Produce one diagnostic-journal frame per declaration record in an export.
///
/// Frames follow distinct declaration-record line numbers in ascending order.
/// Only an ordinary definition, theorem, or opaque declaration that both the
/// tracing core completed and the fenced reference entry accepted retains its
/// bytes. Every other record receives an empty frame.
pub fn export_advice_frames<R: BufRead>(reader: R) -> Result<(Vec<Vec<u8>>, usize), AdviceError> {
    export_advice_frames_from(reader, AdviceFrameSource::DiagnosticJournal)
}

/// Emit the selected native advice in export order. An unsuccessful candidate
/// search emits an empty frame. The fenced and tracing admission gates apply
/// to both sources, and only the adopted checker can judge their bytes.
pub fn export_advice_frames_from<R: BufRead>(
    reader: R,
    source: AdviceFrameSource,
) -> Result<(Vec<Vec<u8>>, usize), AdviceError> {
    let export =
        NdjsonSource::as_written(reader).map_err(|error| AdviceError::Export(error.to_string()))?;
    let loaded = load_export(export).map_err(|error| AdviceError::Export(error.to_string()))?;
    let targets: BTreeSet<Name> = loaded
        .declared
        .iter()
        .map(|entry| entry.name.clone())
        .collect();

    let mut by_name = BTreeMap::<String, Vec<u8>>::new();
    let mut observer = |row: &TraceObservation| {
        if row.kind != "ordinary" || !row.core_complete || !row.reference_accepted {
            return;
        }
        let bytes = match source {
            AdviceFrameSource::DiagnosticJournal => &row.advice_frame,
            AdviceFrameSource::ReplayCandidate => match &row.advice_candidate {
                Some(AdviceCandidateObservation::Candidate { bytes, .. }) => bytes,
                _ => return,
            },
        };
        by_name.insert(row.name.clone(), bytes.clone());
    };
    reference_base_core_tracing(
        &loaded.env,
        &targets,
        &ClosedRecheckOptions::default(),
        TRACE_OPERATIONS,
        None,
        &mut observer,
    )
    .map_err(|error| AdviceError::Tracing(error.to_string()))?;

    let mut by_line = BTreeMap::new();
    for entry in &loaded.declared {
        by_line.entry(entry.line).or_insert(entry);
    }
    let frames: Vec<Vec<u8>> = by_line
        .into_values()
        .map(|entry| match entry.kind {
            "def" | "thm" | "opaque" => by_name
                .remove(&entry.name.to_unambiguous_string())
                .unwrap_or_default(),
            _ => Vec::new(),
        })
        .collect();
    let count = frames.len();
    Ok((frames, count))
}
