// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse sample` — draw N declarations matching optional filters.
//!
//! Uses a deterministic stride walk over the library (not true random — good
//! enough for exploratory browsing, repeatable across runs with the same seed).

use crate::library::MathverseLibrary;
use crate::types::ConstantIdx;

use crate::mathverse_bin_cmds::fmt::{
    confidence_display, domain_display, emit_delimited_row, parse_source_system, parse_trust_level,
    source_system_display, OutputFormat,
};
use crate::mathverse_bin_cmds::load_library;

use super::{parse_format_arg, truncate};

pub fn cmd_sample(args: &[String]) {
    let opts = SampleOpts::parse(args);
    let format = parse_format_arg(args);
    let lib = load_library();

    let sample = collect_sample(&lib, &opts);
    match format {
        OutputFormat::Table => print_table(&lib, &sample),
        OutputFormat::Json => print_json(&lib, &sample),
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => print_delimited(&lib, &sample, fmt),
    }
}

struct SampleOpts {
    n: usize,
    domain_filter: Option<u8>,
    system_filter: Option<u8>,
    trust_filter: Option<u8>,
    seed: u64,
}

impl SampleOpts {
    fn parse(args: &[String]) -> Self {
        let mut opts = Self {
            n: 10,
            domain_filter: None,
            system_filter: None,
            trust_filter: None,
            seed: 0,
        };
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "--n" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.n = val.parse().unwrap_or(10);
                    }
                }
                "--domain" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.domain_filter = parse_domain(val);
                        if opts.domain_filter.is_none() {
                            eprintln!("Unknown domain: {val}");
                            std::process::exit(1);
                        }
                    }
                }
                "--system" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.system_filter = parse_source_system(val);
                        if opts.system_filter.is_none() {
                            eprintln!("Unknown system: {val}");
                            std::process::exit(1);
                        }
                    }
                }
                "--trust" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.trust_filter = parse_trust_level(val);
                        if opts.trust_filter.is_none() {
                            eprintln!("Unknown trust level: {val}");
                            std::process::exit(1);
                        }
                    }
                }
                "--seed" => {
                    i += 1;
                    if let Some(val) = args.get(i) {
                        opts.seed = val.parse().unwrap_or(0);
                    }
                }
                _ => {}
            }
            i += 1;
        }
        opts
    }
}

fn parse_domain(name: &str) -> Option<u8> {
    let lower = name.to_lowercase();
    if let Ok(n) = lower.parse::<u8>() {
        return Some(n);
    }
    match lower.as_str() {
        "puremath" | "pure" | "math" => Some(0),
        "software" => Some(1),
        "complexity" => Some(2),
        "nnverification" | "nn" | "nnverify" => Some(3),
        "physics" => Some(4),
        "logic" => Some(5),
        "cryptography" | "crypto" => Some(6),
        _ => None,
    }
}

/// Sample by stride-walking the library, using `seed` to offset the start.
/// This is deterministic — same seed on same library returns same sample.
fn collect_sample(lib: &MathverseLibrary, opts: &SampleOpts) -> Vec<ConstantIdx> {
    let total = lib.constant_count();
    if total == 0 || opts.n == 0 {
        return Vec::new();
    }

    // Count matching constants first to pick an appropriate stride.
    let mut matching: Vec<ConstantIdx> = Vec::new();
    for idx in 0..total as u32 {
        if matches_filters(lib, idx, opts) {
            matching.push(idx);
        }
    }
    if matching.is_empty() {
        return Vec::new();
    }

    // Pick `n` using linear congruential walk through matching indices.
    let mut seed = opts.seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut out = Vec::with_capacity(opts.n);
    let mut seen = hashbrown::HashSet::with_capacity(opts.n);
    let mut attempts = 0;
    let max_attempts = opts.n.saturating_mul(10).max(matching.len());
    while out.len() < opts.n && attempts < max_attempts {
        attempts += 1;
        seed = seed
            .wrapping_mul(0x5851_F42D_4C95_7F2D)
            .wrapping_add(0x1405_7B7E_F767_814F);
        let pos = (seed % matching.len() as u64) as usize;
        let pick = matching[pos];
        if seen.insert(pick) {
            out.push(pick);
        }
    }
    out
}

fn matches_filters(lib: &MathverseLibrary, idx: ConstantIdx, opts: &SampleOpts) -> bool {
    let Some(h) = lib.get_constant(idx) else {
        return false;
    };
    if let Some(d) = opts.domain_filter {
        if h.content_domain != d {
            return false;
        }
    }
    if let Some(s) = opts.system_filter {
        if h.source_system != s {
            return false;
        }
    }
    if let Some(t) = opts.trust_filter {
        if h.import_confidence != t {
            return false;
        }
    }
    true
}

fn print_table(lib: &MathverseLibrary, sample: &[ConstantIdx]) {
    if sample.is_empty() {
        println!("No declarations match the requested filters.");
        return;
    }
    println!(
        "{:<8} {:<50} {:<15} {:<16} {:<14}",
        "IDX", "NAME", "SYSTEM", "TRUST", "DOMAIN"
    );
    println!("{}", "-".repeat(105));
    for &idx in sample {
        let name = lib.get_name(idx).unwrap_or("?");
        let Some(h) = lib.get_constant(idx) else {
            continue;
        };
        println!(
            "{:<8} {:<50} {:<15} {:<16} {:<14}",
            idx,
            truncate(name, 50),
            source_system_display(h.source_system),
            confidence_display(h.import_confidence),
            domain_display(h.content_domain),
        );
    }
    println!("\n{} sampled declaration(s)", sample.len());
}

fn print_json(lib: &MathverseLibrary, sample: &[ConstantIdx]) {
    let entries: Vec<serde_json::Value> = sample
        .iter()
        .filter_map(|&idx| {
            let h = lib.get_constant(idx)?;
            let name = lib.get_name(idx)?;
            Some(serde_json::json!({
                "idx": idx,
                "name": name,
                "source_system": source_system_display(h.source_system),
                "trust": confidence_display(h.import_confidence),
                "domain": domain_display(h.content_domain),
            }))
        })
        .collect();
    println!(
        "{}",
        serde_json::to_string_pretty(&entries).expect("invariant: json serialization")
    );
}

fn print_delimited(lib: &MathverseLibrary, sample: &[ConstantIdx], fmt: OutputFormat) {
    emit_delimited_row(&["idx", "name", "source_system", "trust", "domain"], fmt);
    for &idx in sample {
        let Some(h) = lib.get_constant(idx) else {
            continue;
        };
        let Some(name) = lib.get_name(idx) else {
            continue;
        };
        let idx_s = idx.to_string();
        emit_delimited_row(
            &[
                &idx_s,
                name,
                source_system_display(h.source_system),
                confidence_display(h.import_confidence),
                domain_display(h.content_domain),
            ],
            fmt,
        );
    }
}
