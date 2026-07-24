// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse inspect` — show full metadata for a single declaration.

use crate::library::MathverseLibrary;

use crate::mathverse_bin_cmds::fmt::{
    confidence_display, domain_display, emit_delimited_row, source_system_display, OutputFormat,
};
use crate::mathverse_bin_cmds::load_library;

use super::parse_format_arg;

pub fn cmd_inspect(args: &[String]) {
    if args.is_empty() {
        eprintln!("Usage: mathverse inspect <name> [--format table|json|csv|tsv]");
        std::process::exit(1);
    }
    let target = &args[0];
    let format = parse_format_arg(&args[1..]);
    let lib = load_library();
    let count = lib.constant_count();

    let mut found_idx: Option<u32> = None;
    for idx in 0..count as u32 {
        if let Some(name) = lib.get_name(idx) {
            if name == target.as_str() {
                found_idx = Some(idx);
                break;
            }
        }
    }

    let idx = match found_idx {
        Some(i) => i,
        None => {
            eprintln!("Declaration not found: {target}");
            std::process::exit(1);
        }
    };

    match format {
        OutputFormat::Table => print_table(&lib, idx, target),
        OutputFormat::Json => print_json(&lib, idx, target),
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => print_delimited(&lib, idx, target, fmt),
    }
}

fn print_table(lib: &MathverseLibrary, idx: u32, name: &str) {
    let header = match lib.get_constant(idx) {
        Some(h) => h,
        None => return,
    };
    println!("Name:             {name}");
    println!("Index:            {idx}");
    println!(
        "Source system:    {}",
        source_system_display(header.source_system)
    );
    println!(
        "Trust level:      {}",
        confidence_display(header.import_confidence)
    );
    println!(
        "Content domain:   {}",
        domain_display(header.content_domain)
    );
    println!("Has value:        {}", header.has_value());
    println!("Trust-gated:      {}", header.is_trust_gated());
    println!("Axiom count:      {}", header.axiom_profile.axiom_count());

    let prov = lib.provenance();
    if let Some(record) = prov.get(header.provenance_idx) {
        println!("\n--- Provenance ---");
        println!("Original name:    {}", record.original_name);
        if let Some(ref f) = record.source_file {
            println!("Source file:      {f}");
        }
        if let Some(line) = record.source_line {
            println!("Source line:      {line}");
        }
        if let Some(ref v) = record.source_version {
            println!("Source version:   {v}");
        }
        if let Some(ref m) = record.module_path {
            println!("Module path:      {m}");
        }
        println!("Pipeline version: {}", record.pipeline_version);
        if !record.notes.is_empty() {
            println!("Notes:            {}", record.notes.join("; "));
        }
    }
}

fn print_json(lib: &MathverseLibrary, idx: u32, name: &str) {
    let header = match lib.get_constant(idx) {
        Some(h) => h,
        None => return,
    };
    let mut obj = serde_json::json!({
        "idx": idx,
        "name": name,
        "source_system": source_system_display(header.source_system),
        "trust": confidence_display(header.import_confidence),
        "domain": domain_display(header.content_domain),
        "has_value": header.has_value(),
        "trust_gated": header.is_trust_gated(),
        "axiom_count": header.axiom_profile.axiom_count(),
    });

    let prov = lib.provenance();
    if let Some(record) = prov.get(header.provenance_idx) {
        obj["provenance"] = serde_json::json!({
            "original_name": record.original_name,
            "source_file": record.source_file,
            "source_line": record.source_line,
            "source_version": record.source_version,
            "module_path": record.module_path,
            "pipeline_version": record.pipeline_version,
            "notes": record.notes,
        });
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&obj).expect("invariant: json serialization")
    );
}

fn print_delimited(lib: &MathverseLibrary, idx: u32, name: &str, fmt: OutputFormat) {
    let header = match lib.get_constant(idx) {
        Some(h) => h,
        None => return,
    };
    // Inspect is a single-record view; emit a flat header + one row with the
    // core metadata, plus provenance columns when available.
    emit_delimited_row(
        &[
            "idx",
            "name",
            "source_system",
            "trust",
            "domain",
            "has_value",
            "trust_gated",
            "axiom_count",
            "original_name",
            "source_file",
            "source_line",
            "source_version",
            "module_path",
            "pipeline_version",
            "notes",
        ],
        fmt,
    );
    let idx_s = idx.to_string();
    let has_val = header.has_value().to_string();
    let gated = header.is_trust_gated().to_string();
    let axioms = header.axiom_profile.axiom_count().to_string();

    let prov = lib.provenance();
    let record = prov.get(header.provenance_idx);
    let original_name = record.map(|r| r.original_name.as_str()).unwrap_or("");
    let source_file = record.and_then(|r| r.source_file.as_deref()).unwrap_or("");
    let source_line = record
        .and_then(|r| r.source_line)
        .map(|n| n.to_string())
        .unwrap_or_default();
    let source_version = record
        .and_then(|r| r.source_version.as_deref())
        .unwrap_or("");
    let module_path = record.and_then(|r| r.module_path.as_deref()).unwrap_or("");
    let pipeline_version = record
        .map(|r| r.pipeline_version.to_string())
        .unwrap_or_default();
    let notes = record.map(|r| r.notes.join("; ")).unwrap_or_default();

    emit_delimited_row(
        &[
            &idx_s,
            name,
            source_system_display(header.source_system),
            confidence_display(header.import_confidence),
            domain_display(header.content_domain),
            &has_val,
            &gated,
            &axioms,
            original_name,
            source_file,
            &source_line,
            source_version,
            module_path,
            &pipeline_version,
            &notes,
        ],
        fmt,
    );
}
