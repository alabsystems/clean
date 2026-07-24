// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse stats` and `mathverse systems` — aggregate library statistics.

use std::collections::HashMap;

use crate::mathverse_bin_cmds::fmt::{
    confidence_display, domain_display, emit_delimited_row, source_system_display, OutputFormat,
};
use crate::mathverse_bin_cmds::load_library;

use super::parse_format_arg;

// -----------------------------------------------------------------------
// stats
// -----------------------------------------------------------------------

pub fn cmd_stats(args: &[String]) {
    let format = parse_format_arg(args);
    let lib = load_library();
    let count = lib.constant_count();

    let mut by_system: HashMap<u8, usize> = HashMap::new();
    let mut by_trust: HashMap<u8, usize> = HashMap::new();
    let mut by_domain: HashMap<u8, usize> = HashMap::new();
    let mut with_value = 0usize;
    let mut trust_gated = 0usize;

    for idx in 0..count as u32 {
        if let Some(h) = lib.get_constant(idx) {
            *by_system.entry(h.source_system).or_default() += 1;
            *by_trust.entry(h.import_confidence).or_default() += 1;
            *by_domain.entry(h.content_domain).or_default() += 1;
            if h.has_value() {
                with_value += 1;
            }
            if h.is_trust_gated() {
                trust_gated += 1;
            }
        }
    }

    match format {
        OutputFormat::Table => {
            print_stats_table(
                count,
                with_value,
                trust_gated,
                &by_system,
                &by_trust,
                &by_domain,
            );
        }
        OutputFormat::Json => {
            print_stats_json(
                count,
                with_value,
                trust_gated,
                &by_system,
                &by_trust,
                &by_domain,
            );
        }
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
            print_stats_delimited(
                count,
                with_value,
                trust_gated,
                &by_system,
                &by_trust,
                &by_domain,
                fmt,
            );
        }
    }
}

fn print_stats_table(
    count: usize,
    with_value: usize,
    trust_gated: usize,
    by_system: &HashMap<u8, usize>,
    by_trust: &HashMap<u8, usize>,
    by_domain: &HashMap<u8, usize>,
) {
    println!("Mathverse Library Statistics");
    println!("========================");
    println!("Total constants:  {count}");
    println!("With proof term:  {with_value}");
    println!("Trust-gated:      {trust_gated}");

    println!("\nBy trust level:");
    let mut trust_sorted: Vec<_> = by_trust.iter().collect();
    trust_sorted.sort_by_key(|&(k, _)| *k);
    for (&id, &n) in &trust_sorted {
        println!("  {:<20} {n}", confidence_display(id));
    }

    println!("\nBy domain:");
    let mut domain_sorted: Vec<_> = by_domain.iter().collect();
    domain_sorted.sort_by_key(|&(_, n)| std::cmp::Reverse(*n));
    for (&id, &n) in &domain_sorted {
        println!("  {:<20} {n}", domain_display(id));
    }

    println!("\nTop systems (by count):");
    let mut sys_sorted: Vec<_> = by_system.iter().collect();
    sys_sorted.sort_by_key(|&(_, n)| std::cmp::Reverse(*n));
    for (&id, &n) in sys_sorted.iter().take(15) {
        println!("  {:<20} {n}", source_system_display(id));
    }
}

fn print_stats_json(
    count: usize,
    with_value: usize,
    trust_gated: usize,
    by_system: &HashMap<u8, usize>,
    by_trust: &HashMap<u8, usize>,
    by_domain: &HashMap<u8, usize>,
) {
    let sys_map: serde_json::Map<String, serde_json::Value> = by_system
        .iter()
        .map(|(&id, &n)| (source_system_display(id).to_string(), serde_json::json!(n)))
        .collect();
    let trust_map: serde_json::Map<String, serde_json::Value> = by_trust
        .iter()
        .map(|(&id, &n)| (confidence_display(id).to_string(), serde_json::json!(n)))
        .collect();
    let domain_map: serde_json::Map<String, serde_json::Value> = by_domain
        .iter()
        .map(|(&id, &n)| (domain_display(id).to_string(), serde_json::json!(n)))
        .collect();

    let obj = serde_json::json!({
        "total_constants": count,
        "with_value": with_value,
        "trust_gated": trust_gated,
        "by_system": sys_map,
        "by_trust": trust_map,
        "by_domain": domain_map,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&obj).expect("invariant: json serialization")
    );
}

/// Emit stats as long-format rows (category, key, value). Long-format keeps
/// a consistent schema across heterogeneous breakdowns (system/trust/domain).
fn print_stats_delimited(
    count: usize,
    with_value: usize,
    trust_gated: usize,
    by_system: &HashMap<u8, usize>,
    by_trust: &HashMap<u8, usize>,
    by_domain: &HashMap<u8, usize>,
    fmt: OutputFormat,
) {
    emit_delimited_row(&["category", "key", "count"], fmt);
    let total = count.to_string();
    let wv = with_value.to_string();
    let tg = trust_gated.to_string();
    emit_delimited_row(&["total", "total_constants", &total], fmt);
    emit_delimited_row(&["total", "with_value", &wv], fmt);
    emit_delimited_row(&["total", "trust_gated", &tg], fmt);

    let mut trust_sorted: Vec<_> = by_trust.iter().collect();
    trust_sorted.sort_by_key(|&(k, _)| *k);
    for (&id, &n) in &trust_sorted {
        let n_s = n.to_string();
        emit_delimited_row(&["trust", confidence_display(id), &n_s], fmt);
    }

    let mut domain_sorted: Vec<_> = by_domain.iter().collect();
    domain_sorted.sort_by_key(|&(_, n)| std::cmp::Reverse(*n));
    for (&id, &n) in &domain_sorted {
        let n_s = n.to_string();
        emit_delimited_row(&["domain", domain_display(id), &n_s], fmt);
    }

    let mut sys_sorted: Vec<_> = by_system.iter().collect();
    sys_sorted.sort_by_key(|&(_, n)| std::cmp::Reverse(*n));
    for (&id, &n) in &sys_sorted {
        let n_s = n.to_string();
        emit_delimited_row(&["system", source_system_display(id), &n_s], fmt);
    }
}

// -----------------------------------------------------------------------
// systems
// -----------------------------------------------------------------------

pub fn cmd_systems(args: &[String]) {
    let format = parse_format_arg(args);
    let lib = load_library();
    let count = lib.constant_count();

    let mut by_system: HashMap<u8, usize> = HashMap::new();
    for idx in 0..count as u32 {
        if let Some(h) = lib.get_constant(idx) {
            *by_system.entry(h.source_system).or_default() += 1;
        }
    }

    let mut sorted: Vec<_> = by_system.into_iter().collect();
    sorted.sort_by_key(|&(_, n)| std::cmp::Reverse(n));

    match format {
        OutputFormat::Table => {
            println!("{:<6} {:<20} {:<10}", "ID", "SYSTEM", "COUNT");
            println!("{}", "-".repeat(38));
            for (id, n) in &sorted {
                println!("{:<6} {:<20} {:<10}", id, source_system_display(*id), n);
            }
            println!("\n{} source system(s)", sorted.len());
        }
        OutputFormat::Json => {
            let arr: Vec<serde_json::Value> = sorted
                .iter()
                .map(|&(id, n)| {
                    serde_json::json!({
                        "id": id,
                        "name": source_system_display(id),
                        "count": n,
                    })
                })
                .collect();
            println!(
                "{}",
                serde_json::to_string_pretty(&arr).expect("invariant: json serialization")
            );
        }
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
            emit_delimited_row(&["id", "name", "count"], fmt);
            for &(id, n) in &sorted {
                let id_s = id.to_string();
                let n_s = n.to_string();
                emit_delimited_row(&[&id_s, source_system_display(id), &n_s], fmt);
            }
        }
    }
}
