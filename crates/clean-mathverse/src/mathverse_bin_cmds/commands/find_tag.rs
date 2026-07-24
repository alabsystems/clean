// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tag-search helpers for `mathverse find`. Extracted from `find.rs` to keep
//! that module under the per-file line budget.

use crate::library::MathverseLibrary;
use crate::tag_index::TagIndex;

use crate::mathverse_bin_cmds::fmt::{
    domain_display, emit_delimited_row, source_system_display, OutputFormat,
};
use crate::mathverse_bin_cmds::load_library;

use super::truncate;

/// Handle `mathverse find --tag <t> [--tag <t2>]` — AND-search over auto-tags.
pub(super) fn run_tag_search(
    lib: &MathverseLibrary,
    tags: &[String],
    limit: usize,
    format: OutputFormat,
) {
    let tag_index = auto_tag_library(lib);
    let tag_refs: Vec<&str> = tags.iter().map(|s| s.as_str()).collect();
    let indices = if tags.len() > 1 {
        tag_index.search_tags_all(&tag_refs)
    } else {
        tag_index.search_tag(tag_refs[0]).to_vec()
    };
    let limited: Vec<u32> = indices.into_iter().take(limit).collect();

    match format {
        OutputFormat::Table => print_tag_table(lib, &tag_index, &limited, tags),
        OutputFormat::Json => print_tag_json(lib, &tag_index, &limited),
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
            print_tag_delimited(lib, &tag_index, &limited, fmt)
        }
    }
}

/// Handle `mathverse find --tags` — enumerate all known tags with counts.
pub(super) fn run_list_tags(limit: usize, format: OutputFormat) {
    let lib = load_library();
    let tag_index = auto_tag_library(&lib);
    let all_tags = tag_index.all_tags();

    match format {
        OutputFormat::Table => {
            println!("{:<30} {:<10}", "TAG", "COUNT");
            println!("{}", "-".repeat(42));
            for (tag, count) in all_tags.iter().take(limit) {
                println!("{:<30} {:<10}", tag, count);
            }
            println!("\n{} tag(s) total", all_tags.len());
        }
        OutputFormat::Json => {
            let entries: Vec<serde_json::Value> = all_tags
                .iter()
                .take(limit)
                .map(|(tag, count)| serde_json::json!({"tag": tag, "count": count}))
                .collect();
            println!(
                "{}",
                serde_json::to_string_pretty(&entries).expect("invariant: json serialization")
            );
        }
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
            emit_delimited_row(&["tag", "count"], fmt);
            for (tag, count) in all_tags.iter().take(limit) {
                let count_s = count.to_string();
                emit_delimited_row(&[tag, &count_s], fmt);
            }
        }
    }
}

fn print_tag_table(lib: &MathverseLibrary, tag_index: &TagIndex, limited: &[u32], tags: &[String]) {
    if limited.is_empty() {
        println!("No results found for tags: {}", tags.join(", "));
        return;
    }
    println!(
        "{:<8} {:<50} {:<15} {:<30}",
        "IDX", "NAME", "SYSTEM", "TAGS"
    );
    println!("{}", "-".repeat(105));
    for idx in limited {
        let name = lib.get_name(*idx).unwrap_or("?");
        let sys = lib
            .get_constant(*idx)
            .map(|h| source_system_display(h.source_system))
            .unwrap_or("Unknown");
        let tag_str = tag_index.tags_for(*idx).join(", ");
        println!(
            "{:<8} {:<50} {:<15} {:<30}",
            idx,
            truncate(name, 50),
            sys,
            truncate(&tag_str, 30),
        );
    }
    println!("\n{} result(s)", limited.len());
}

fn print_tag_json(lib: &MathverseLibrary, tag_index: &TagIndex, limited: &[u32]) {
    let entries: Vec<serde_json::Value> = limited
        .iter()
        .filter_map(|idx| {
            let name = lib.get_name(*idx)?;
            let h = lib.get_constant(*idx)?;
            Some(serde_json::json!({
                "idx": idx,
                "name": name,
                "source_system": source_system_display(h.source_system),
                "tags": tag_index.tags_for(*idx),
            }))
        })
        .collect();
    println!(
        "{}",
        serde_json::to_string_pretty(&entries).expect("invariant: json serialization")
    );
}

fn print_tag_delimited(
    lib: &MathverseLibrary,
    tag_index: &TagIndex,
    limited: &[u32],
    fmt: OutputFormat,
) {
    emit_delimited_row(&["idx", "name", "source_system", "tags"], fmt);
    for idx in limited {
        if let (Some(name), Some(h)) = (lib.get_name(*idx), lib.get_constant(*idx)) {
            let idx_s = idx.to_string();
            // Tags joined with `;` avoid colliding with CSV's comma.
            let tags = tag_index.tags_for(*idx).join(";");
            emit_delimited_row(
                &[&idx_s, name, source_system_display(h.source_system), &tags],
                fmt,
            );
        }
    }
}

/// Auto-generate tags from library constant names by tokenizing on `.` and `_`.
pub(super) fn auto_tag_library(lib: &MathverseLibrary) -> TagIndex {
    let mut index = TagIndex::new();
    let count = lib.constant_count();
    for idx in 0..count as u32 {
        if let Some(name) = lib.get_name(idx) {
            for token in name.split(['.', '_']) {
                if token.len() >= 2 {
                    index.add_tag(idx, token);
                }
            }
            if let Some(h) = lib.get_constant(idx) {
                let domain = domain_display(h.content_domain).to_lowercase();
                if domain != "unknown" {
                    index.add_tag(idx, &domain);
                }
            }
        }
    }
    index
}
