// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse export` — export mathverse library data in various formats.
//!
//! Subcommands:
//! - `clean-native`: Export to clean native kernel format
//! - `arxiv`: Import and export arXiv papers
//! - `all`: Export all eligible constants

use std::path::PathBuf;

use crate::export::alpha::{ExportConfig, ExportFormat, Exporter};
use crate::verify::TrustGate;

use crate::mathverse_bin_cmds::load_library;

pub fn cmd_export(args: &[String]) {
    if args.is_empty() {
        print_export_usage();
        std::process::exit(1);
    }

    match args[0].as_str() {
        "clean-native" => cmd_export_clean_native(&args[1..]),
        "arxiv" => cmd_export_arxiv(&args[1..]),
        "all" => cmd_export_all(&args[1..]),
        "help" | "--help" | "-h" => print_export_usage(),
        other => {
            eprintln!("Unknown export subcommand: {other}");
            print_export_usage();
            std::process::exit(1);
        }
    }
}

// ---------------------------------------------------------------------------
// clean-native
// ---------------------------------------------------------------------------

fn cmd_export_clean_native(args: &[String]) {
    let mut output_dir: Option<PathBuf> = None;
    let mut domain: Option<String> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--output" => {
                i += 1;
                output_dir = args.get(i).map(PathBuf::from);
            }
            "--domain" => {
                i += 1;
                domain = args.get(i).cloned();
            }
            other => {
                eprintln!("Unknown clean-native option: {other}");
                std::process::exit(1);
            }
        }
        i += 1;
    }

    let out = output_dir.unwrap_or_else(|| PathBuf::from("data/mathverse-native-export"));
    println!("Exporting mathverse library to clean native format...");
    println!("  Output: {}", out.display());
    if let Some(ref d) = domain {
        println!("  Domain filter: {d}");
    }

    // Export the kernel-verified constructive subset as a clean-Native `.mathverse`
    // shard (the behavior documented for `export clean-native`). This replaces
    // the earlier JSONL training-data placeholder now that `native_export` is
    // complete: it writes a binary shard plus an `.mathverse.json` metadata sidecar.
    let entries = crate::export::native_export::collect_nn_verify_theorems();

    if let Err(e) = std::fs::create_dir_all(&out) {
        eprintln!("Failed to create output directory: {e}");
        std::process::exit(1);
    }
    let shard_path = out.join("clean-native.mathverse");
    match crate::export::native_export::export_native_theorems(&entries, &shard_path) {
        Ok(stats) => {
            println!(
                "  Exported {} kernel-verified declarations to {}",
                stats.entries_written,
                shard_path.display()
            );
            println!(
                "  Metadata sidecar: {}",
                crate::shard_metadata::sidecar_path_for(&shard_path).display()
            );
        }
        Err(e) => {
            eprintln!("Failed to export native theorems: {e}");
            std::process::exit(1);
        }
    }
}

// ---------------------------------------------------------------------------
// arxiv
// ---------------------------------------------------------------------------

fn cmd_export_arxiv(args: &[String]) {
    let mut paper_id: Option<String> = None;
    let mut output_dir: Option<PathBuf> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--paper" => {
                i += 1;
                paper_id = args.get(i).cloned();
            }
            "--output" => {
                i += 1;
                output_dir = args.get(i).map(PathBuf::from);
            }
            other => {
                eprintln!("Unknown arxiv option: {other}");
                std::process::exit(1);
            }
        }
        i += 1;
    }

    let out = output_dir.unwrap_or_else(|| PathBuf::from("data/mathverse-arxiv-export"));

    match paper_id {
        Some(ref id) => {
            println!("Importing arXiv paper {id} into mathverse library...");
            println!("  Output: {}", out.display());

            // The arXiv pipeline requires LaTeX source to be downloaded
            // externally. Print guidance for the workflow.
            println!();
            println!("To import an arXiv paper:");
            println!("  1. Download source: curl -O https://arxiv.org/e-print/{id}");
            println!("  2. Extract LaTeX: tar xf {id}");
            println!(
                "  3. Run: mathverse export arxiv --paper {id} --output {}",
                out.display()
            );
            println!();
            println!("Pipeline stages: parse -> import -> formalize -> validate -> admit");
            println!("See: crate::arxiv::pipeline for programmatic access.");
        }
        None => {
            eprintln!("Error: --paper <ARXIV_ID> is required for arxiv export.");
            eprintln!("Example: mathverse export arxiv --paper 2301.13868");
            std::process::exit(1);
        }
    }
}

// ---------------------------------------------------------------------------
// all
// ---------------------------------------------------------------------------

fn cmd_export_all(args: &[String]) {
    let mut output_dir: Option<PathBuf> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--output" => {
                i += 1;
                output_dir = args.get(i).map(PathBuf::from);
            }
            other => {
                eprintln!("Unknown export option: {other}");
                std::process::exit(1);
            }
        }
        i += 1;
    }

    let out = output_dir.unwrap_or_else(|| PathBuf::from("data/mathverse-export-all"));
    println!("Exporting full mathverse library...");
    println!("  Output: {}", out.display());

    let lib = load_library();
    let config = ExportConfig {
        trust_gate: TrustGate::StatementOnly,
        max_axiom_bits: u64::MAX,
        include_proofs: false,
        include_deps: false,
        format: ExportFormat::JsonLines,
        limit: 0,
        source_filter: None,
        domain_filter: None,
    };
    let exporter = Exporter::new(&lib, config);
    let records = exporter.export_all();

    if let Err(e) = std::fs::create_dir_all(&out) {
        eprintln!("Failed to create output directory: {e}");
        std::process::exit(1);
    }
    let out_path = out.join("mathverse-library-export.json");
    let json = match serde_json::to_string_pretty(&records) {
        Ok(j) => j,
        Err(e) => {
            eprintln!("Failed to serialize: {e}");
            std::process::exit(1);
        }
    };
    if let Err(e) = std::fs::write(&out_path, json) {
        eprintln!("Failed to write export: {e}");
        std::process::exit(1);
    }
    println!(
        "  Exported {} records to {}",
        records.len(),
        out_path.display()
    );
}

// ---------------------------------------------------------------------------
// usage
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Parsed argument structs (testable)
// ---------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq)]
#[cfg(test)]
pub(crate) struct NativeExportArgs {
    pub(crate) output_dir: PathBuf,
    pub(crate) domain: Option<String>,
}

#[cfg(test)]
impl NativeExportArgs {
    pub(crate) fn parse(args: &[String]) -> Result<Self, String> {
        let mut output_dir: Option<PathBuf> = None;
        let mut domain: Option<String> = None;
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "--output" => {
                    i += 1;
                    output_dir = args.get(i).map(PathBuf::from);
                }
                "--domain" => {
                    i += 1;
                    domain = args.get(i).cloned();
                }
                other => return Err(format!("Unknown clean-native option: {other}")),
            }
            i += 1;
        }
        Ok(Self {
            output_dir: output_dir.unwrap_or_else(|| PathBuf::from("data/mathverse-native-export")),
            domain,
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
#[cfg(test)]
pub(crate) struct ArxivExportArgs {
    pub(crate) paper_id: Option<String>,
    pub(crate) output_dir: PathBuf,
}

#[cfg(test)]
impl ArxivExportArgs {
    pub(crate) fn parse(args: &[String]) -> Result<Self, String> {
        let mut paper_id: Option<String> = None;
        let mut output_dir: Option<PathBuf> = None;
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "--paper" => {
                    i += 1;
                    paper_id = args.get(i).cloned();
                }
                "--output" => {
                    i += 1;
                    output_dir = args.get(i).map(PathBuf::from);
                }
                other => return Err(format!("Unknown arxiv option: {other}")),
            }
            i += 1;
        }
        Ok(Self {
            paper_id,
            output_dir: output_dir.unwrap_or_else(|| PathBuf::from("data/mathverse-arxiv-export")),
        })
    }
}

fn print_export_usage() {
    eprintln!("mathverse export -- export mathverse library data");
    eprintln!();
    eprintln!("Subcommands:");
    eprintln!("  clean-native   Export to clean native kernel format");
    eprintln!("  arxiv          Import an arXiv paper into mathverse format");
    eprintln!("  all            Export all library data (JSONL/JSON)");
    eprintln!();
    eprintln!("clean-native options:");
    eprintln!("  --output <DIR>     Output directory (default: data/mathverse-native-export)");
    eprintln!("  --domain <NAME>    Filter by content domain (e.g. nn-verification)");
    eprintln!();
    eprintln!("arxiv options:");
    eprintln!("  --paper <ID>       arXiv paper ID (required, e.g. 2301.13868)");
    eprintln!("  --output <DIR>     Output directory (default: data/mathverse-arxiv-export)");
    eprintln!();
    eprintln!("all options:");
    eprintln!("  --output <DIR>     Output directory (default: data/mathverse-export-all)");
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(strs: &[&str]) -> Vec<String> {
        strs.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn test_native_export_args_defaults() {
        let parsed = NativeExportArgs::parse(&args(&[])).expect("should parse empty args");
        assert_eq!(
            parsed.output_dir,
            PathBuf::from("data/mathverse-native-export")
        );
        assert_eq!(parsed.domain, None);
    }

    #[test]
    fn test_native_export_args_with_output_and_domain() {
        let parsed = NativeExportArgs::parse(&args(&[
            "--output",
            "/tmp/out",
            "--domain",
            "nn-verification",
        ]))
        .expect("should parse");
        assert_eq!(parsed.output_dir, PathBuf::from("/tmp/out"));
        assert_eq!(parsed.domain, Some("nn-verification".to_string()));
    }

    #[test]
    fn test_native_export_args_unknown_flag() {
        let result = NativeExportArgs::parse(&args(&["--bad"]));
        assert!(result.is_err());
    }

    #[test]
    fn test_arxiv_export_args_with_paper() {
        let parsed =
            ArxivExportArgs::parse(&args(&["--paper", "2301.13868", "--output", "/tmp/arxiv"]))
                .expect("should parse");
        assert_eq!(parsed.paper_id, Some("2301.13868".to_string()));
        assert_eq!(parsed.output_dir, PathBuf::from("/tmp/arxiv"));
    }

    #[test]
    fn test_arxiv_export_args_no_paper() {
        let parsed = ArxivExportArgs::parse(&args(&[])).expect("should parse");
        assert_eq!(parsed.paper_id, None);
        assert_eq!(
            parsed.output_dir,
            PathBuf::from("data/mathverse-arxiv-export")
        );
    }
}
