// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CSV/TSV output helpers for `mathverse graph` subcommands. Extracted from
//! `graph.rs` to keep that file under the per-file line budget.

use crate::cross_system_index::{CrossSystemReport, EquivalenceMatch};
use crate::types::SourceSystem;

use crate::mathverse_bin_cmds::fmt::{emit_delimited_row, source_system_display, OutputFormat};

/// Long-format graph search output: one row per record with a `kind` column
/// distinguishing direct graph equivalents from canonical-name matches.
pub(super) fn print_search_delimited(
    filtered: &[&EquivalenceMatch],
    equivalents: &[(String, SourceSystem)],
    fmt: OutputFormat,
) {
    emit_delimited_row(
        &[
            "kind",
            "canonical_name",
            "system_count",
            "ref_count",
            "confidence",
        ],
        fmt,
    );
    for (name, source) in equivalents {
        emit_delimited_row(
            &[
                "equivalent",
                name,
                source_system_display(*source as u8),
                "",
                "",
            ],
            fmt,
        );
    }
    for m in filtered {
        let sys_count = m.system_count.to_string();
        let ref_count = m.refs.len().to_string();
        let conf = format!("{:.2}", m.confidence);
        emit_delimited_row(
            &["match", &m.canonical_name, &sys_count, &ref_count, &conf],
            fmt,
        );
    }
}

/// Long-format graph stats output: one row per record, with a `category`
/// column separating summary totals, top-cross-referenced matches, and
/// overlap pairs.
pub(super) fn print_stats_delimited(report: &CrossSystemReport, fmt: OutputFormat) {
    emit_delimited_row(&["category", "key_a", "key_b", "value"], fmt);
    let total = report.total_constants.to_string();
    let systems = report.total_systems.to_string();
    let multi = report.multi_system_count.to_string();
    emit_delimited_row(&["total", "total_constants", "", &total], fmt);
    emit_delimited_row(&["total", "total_systems", "", &systems], fmt);
    emit_delimited_row(&["total", "multi_system", "", &multi], fmt);

    for m in &report.top_cross_referenced {
        let refs = m.refs.len().to_string();
        emit_delimited_row(&["top_match", &m.canonical_name, "", &refs], fmt);
    }

    for o in report.overlap_matrix.iter().filter(|o| o.shared_names > 0) {
        let shared = o.shared_names.to_string();
        emit_delimited_row(
            &[
                "overlap",
                source_system_display(o.system_a as u8),
                source_system_display(o.system_b as u8),
                &shared,
            ],
            fmt,
        );
    }
}
