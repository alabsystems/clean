// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase and per-declaration timing for `clean check --json`.
//!
//! WHY. The performance audit (`reports/lean4-replacement-audit-2026-09-24/
//! performance.json`) measured the five-file source-elab slice at about 1,100x
//! the pinned Lean, found that slice time roughly TRIPLED between 2026-08-31
//! and 2026-09-21 (a per-module `env.clone()` in the importer, then one wave's
//! unbudgeted `grind` fallback) and that no gate noticed, because nothing
//! recorded where a check's time went. It had to split import from
//! elaboration by the timestamp of the last "Loaded module" log line. This
//! module is the report's own answer, in the shape Lean's `-Dprofiler` gives:
//!
//! * `setup_s`  standing up the environment (prelude, native registrars);
//! * `parse_s`  parsing the entry file;
//! * `import_s` the entry file's `import` commands (loading and converting the
//!   `.olean` closure) plus any intra-project imports elaborated from source;
//! * `elab_s`   every other top-level command, kernel checks included;
//! * `per_declaration` each declaration the user wrote, with its line and
//!   wall time (see `clean_elab::DeclTiming` for what one record covers).
//!
//! `scripts/source_elab_gate.sh` ratchets `import_s` and `elab_s` per pinned
//! file, with a tolerance, so a regression of that shape turns the gate red.
//! Peak RSS is not here: reading it needs `getrusage`, i.e. `unsafe` FFI, so
//! the gate reads it from `/usr/bin/time` instead.

use serde::Serialize;
use std::time::Duration;

/// Accumulated while a check runs; turned into [`CheckTimingReport`] once.
#[derive(Debug, Default, Clone)]
pub(crate) struct CheckPhaseTiming {
    pub(crate) setup: Duration,
    pub(crate) parse: Duration,
    pub(crate) import: Duration,
    pub(crate) elab: Duration,
    pub(crate) per_declaration: Vec<PerDeclTiming>,
}

/// One declaration's elapsed wall time.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct PerDeclTiming {
    pub(crate) name: String,
    /// 1-based line of the declaration's first token in the entry file.
    pub(crate) line: u32,
    pub(crate) elapsed_ms: f64,
    /// Automation work units the declaration spent against
    /// `--automation-budget` (`0` when the budget is off). Deterministic,
    /// unlike `elapsed_ms`: it is what the budget's default is calibrated from.
    pub(crate) automation_work: u64,
}

/// The `timing` object of `Clean-check-report-v2` (an additive field since v1).
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct CheckTimingReport {
    pub(crate) total_s: f64,
    pub(crate) setup_s: f64,
    pub(crate) parse_s: f64,
    pub(crate) import_s: f64,
    pub(crate) elab_s: f64,
    pub(crate) per_declaration: Vec<PerDeclTiming>,
}

/// Seconds, rounded to the millisecond so a report does not carry nanosecond
/// noise that no consumer can use.
fn secs(d: Duration) -> f64 {
    (d.as_secs_f64() * 1000.0).round() / 1000.0
}

/// 1-based line of `offset` in `source` (an offset past the end is the last
/// line).
fn line_of(source: &str, offset: usize) -> u32 {
    let end = offset.min(source.len());
    let newlines = source.as_bytes()[..end]
        .iter()
        .filter(|b| **b == b'\n')
        .count();
    u32::try_from(newlines)
        .unwrap_or(u32::MAX)
        .saturating_add(1)
}

/// Keep the records of declarations the user wrote, in source order, with
/// their byte offsets turned into lines of `source`.
pub(crate) fn per_declaration(
    records: Vec<clean_elab::DeclTiming>,
    source: &str,
) -> Vec<PerDeclTiming> {
    records
        .into_iter()
        .filter(|r| r.kind == clean_elab::DeclTimingKind::Declaration)
        .map(|r| PerDeclTiming {
            line: line_of(source, r.byte_start),
            elapsed_ms: (r.elapsed.as_secs_f64() * 1_000_000.0).round() / 1000.0,
            automation_work: r.automation_work,
            name: r.name,
        })
        .collect()
}

pub(crate) fn report(phases: CheckPhaseTiming, total: Duration) -> CheckTimingReport {
    CheckTimingReport {
        total_s: secs(total),
        setup_s: secs(phases.setup),
        parse_s: secs(phases.parse),
        import_s: secs(phases.import),
        elab_s: secs(phases.elab),
        per_declaration: phases.per_declaration,
    }
}

/// Arms per-declaration recording for the entry file's main loop and disarms
/// it even if that loop is left early, so a failed check cannot leave the
/// thread recording.
pub(crate) struct RecordingScope {
    taken: bool,
}

impl RecordingScope {
    pub(crate) fn begin() -> Self {
        clean_elab::begin_decl_timing();
        Self { taken: false }
    }

    pub(crate) fn finish(mut self) -> Vec<clean_elab::DeclTiming> {
        self.taken = true;
        clean_elab::take_decl_timings()
    }
}

impl Drop for RecordingScope {
    fn drop(&mut self) {
        if !self.taken {
            let _ = clean_elab::take_decl_timings();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_line_of_counts_newlines_before_the_offset() {
        let src = "a\nbb\nccc\n";
        assert_eq!(line_of(src, 0), 1);
        assert_eq!(line_of(src, 2), 2);
        assert_eq!(line_of(src, 5), 3);
        assert_eq!(
            line_of(src, 999),
            4,
            "an offset past the end is the last line"
        );
    }

    #[test]
    fn test_report_rounds_to_milliseconds() {
        let phases = CheckPhaseTiming {
            import: Duration::from_micros(1_234_567),
            ..CheckPhaseTiming::default()
        };
        let r = report(phases, Duration::from_millis(2_000));
        assert!((r.import_s - 1.235).abs() < 1e-9, "{r:?}");
        assert!((r.total_s - 2.0).abs() < 1e-9, "{r:?}");
    }
}
