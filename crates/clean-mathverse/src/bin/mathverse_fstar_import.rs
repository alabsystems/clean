// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Full F* / Project-Everest corpus importer with coverage measurement.
//!
//! Walks one or more directories for `.fst` / `.fsti` files, parses every
//! top-level declaration via `clean_mathverse::fstar_source`, writes the
//! imported declarations to a single `.mathverse` shard, and reports honest
//! coverage: declarations *recognised* (val/let/type/constructor heads) vs
//! *imported* (those that lower to a real `FlatExpr` tree, never a stub).
//!
//! Skipped declarations (recognised but not importable) are written to
//! `<output>/fstar_skipped.txt` so the importer can be hardened against the
//! real corpus.
//!
//! Usage:
//!   mathverse_fstar_import <output-dir> <input-dir> [<input-dir> ...]

use std::collections::BTreeMap;
use std::env;
use std::path::{Path, PathBuf};
use std::process::exit;
use std::time::Instant;

use clean_mathverse::fstar_source::{parse_fstar_file, write_fstar_shard};
use clean_mathverse::shard::ShardWriter;

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = std::fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                // Skip VCS metadata.
                if path.file_name().is_some_and(|n| n == ".git") {
                    continue;
                }
                collect(&path, out);
            } else if path.extension().is_some_and(|e| e == "fst" || e == "fsti") {
                out.push(path);
            }
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: mathverse_fstar_import <output-dir> <input-dir> [<input-dir> ...]");
        exit(2);
    }
    let output = PathBuf::from(&args[1]);
    if let Err(e) = std::fs::create_dir_all(&output) {
        eprintln!("failed to create output dir {}: {e}", output.display());
        exit(2);
    }

    let mut files = Vec::new();
    for d in &args[2..] {
        collect(Path::new(d), &mut files);
    }
    files.sort();
    files.dedup();
    eprintln!("scanning {} .fst/.fsti files…", files.len());

    let start = Instant::now();
    let mut shard = ShardWriter::new();
    // A separate shard holding only the inductive-family decls (bedrock
    // candidates) so they can be kernel-replayed without the full-corpus scan.
    let mut ind_shard = ShardWriter::new();
    let mut files_ok = 0usize;
    let mut read_errors = 0usize;
    let mut recognised = 0usize;
    let mut imported = 0usize;
    // Per-source-repo accounting (first path component under the corpus root).
    let mut per_repo: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    // Skipped declarations: name + type_repr, capped for the dump file.
    let mut skipped: Vec<String> = Vec::new();
    const SKIP_DUMP_CAP: usize = 100_000;

    for path in &files {
        let filename = path.file_name().unwrap_or_default().to_string_lossy();
        // The repo is the path component immediately under `everest-corpus`.
        let comps: Vec<String> = path
            .components()
            .map(|c| c.as_os_str().to_string_lossy().to_string())
            .collect();
        let repo = comps
            .iter()
            .position(|s| s == "everest-corpus")
            .and_then(|i| comps.get(i + 1))
            .cloned()
            .unwrap_or_else(|| "?".into());
        let content = match std::fs::read_to_string(path) {
            Ok(c) => c,
            Err(_) => {
                read_errors += 1;
                continue;
            }
        };
        files_ok += 1;
        let decls = parse_fstar_file(&content, &filename);
        let entry = per_repo.entry(repo).or_insert((0, 0));
        for d in &decls {
            recognised += 1;
            entry.0 += 1;
            let before = shard.constant_count();
            write_fstar_shard(std::slice::from_ref(d), &mut shard);
            let wrote = shard.constant_count() > before;
            if wrote {
                imported += 1;
                entry.1 += 1;
                // Mirror inductive-family decls into a separate, small shard so
                // the kernel re-verifier can replay just the bedrock candidates
                // (Inductive/Constructor) without scanning all ~80k constants.
                if matches!(
                    d.kind,
                    clean_mathverse::fstar_source::FStarDeclKind::Inductive { .. }
                        | clean_mathverse::fstar_source::FStarDeclKind::Constructor
                ) {
                    write_fstar_shard(std::slice::from_ref(d), &mut ind_shard);
                }
            } else if skipped.len() < SKIP_DUMP_CAP {
                skipped.push(format!("{} :: {} : {}", filename, d.name, d.type_repr));
            }
        }
    }

    let shard_path = output.join("fstar.mathverse");
    if let Err(e) = shard.write_to_file(&shard_path) {
        eprintln!("failed to write shard {}: {e}", shard_path.display());
        exit(1);
    }
    let ind_dir = output.join("inductives");
    let _ = std::fs::create_dir_all(&ind_dir);
    let ind_path = ind_dir.join("fstar_inductives.mathverse");
    if ind_shard.constant_count() > 0 {
        if let Err(e) = ind_shard.write_to_file(&ind_path) {
            eprintln!(
                "failed to write inductive shard {}: {e}",
                ind_path.display()
            );
        } else {
            eprintln!(
                "wrote {} inductive-family constants to {}",
                ind_shard.constant_count(),
                ind_path.display()
            );
        }
    }
    let skip_path = output.join("fstar_skipped.txt");
    let _ = std::fs::write(&skip_path, skipped.join("\n"));

    let elapsed = start.elapsed();
    let rate = imported as f64 / recognised.max(1) as f64 * 100.0;

    println!("=== F* / Project-Everest corpus import ===");
    println!("files scanned (.fst/.fsti): {}", files.len());
    println!("files read OK / read errors: {files_ok} / {read_errors}");
    println!("declarations recognised:    {recognised}");
    println!("declarations imported:      {imported}  ({rate:.1}%)");
    println!(
        "shard exprs / constants:    {} / {}",
        shard.expr_count(),
        shard.constant_count()
    );
    println!("elapsed: {:.2}s", elapsed.as_secs_f64());
    println!("shard:   {}", shard_path.display());
    println!(
        "skips:   {} (sample dumped to {})",
        recognised - imported,
        skip_path.display()
    );
    println!("--- per-repo (recognised / imported) ---");
    for (repo, (rec, imp)) in &per_repo {
        let r = *imp as f64 / (*rec).max(1) as f64 * 100.0;
        println!("  {repo:<14} {rec:>8} / {imp:<8} ({r:.1}%)");
    }
}
