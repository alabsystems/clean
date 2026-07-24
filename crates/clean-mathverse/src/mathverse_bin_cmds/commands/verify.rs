// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `mathverse verify` — verify a shard directory or release against its manifest.
//!
//! Checks blake3 hashes in `mathverse-manifest.json` if present, otherwise
//! walks every `.mathverse` file and validates each one opens cleanly
//! (header + checksum + structural bounds).

use std::path::{Path, PathBuf};

use crate::release::verify_release;
use crate::shard::ShardReader;

use crate::mathverse_bin_cmds::fmt::{emit_delimited_row, OutputFormat};

use super::parse_format_arg;

pub fn cmd_verify(args: &[String]) {
    let mut target: Option<PathBuf> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--format" => {
                i += 1; // consumed by parse_format_arg
            }
            other if !other.starts_with("--") && target.is_none() => {
                target = Some(PathBuf::from(other));
            }
            _ => {}
        }
        i += 1;
    }
    let format = parse_format_arg(args);

    let dir = target.unwrap_or_else(|| PathBuf::from("data/mathverse-shards"));
    if !dir.exists() {
        eprintln!("Verify target not found: {}", dir.display());
        std::process::exit(1);
    }

    let manifest_path = dir.join("mathverse-manifest.json");
    if manifest_path.exists() {
        run_manifest_verify(&dir, format);
    } else {
        run_walk_verify(&dir, format);
    }
}

fn run_manifest_verify(dir: &Path, format: OutputFormat) {
    match verify_release(dir) {
        Ok(result) => match format {
            OutputFormat::Table => {
                println!("Manifest verification of {}:", dir.display());
                println!("  Checked: {}", result.checked);
                println!("  Passed:  {}", result.passed);
                println!("  Missing: {}", result.missing.len());
                println!("  Failed:  {}", result.failures.len());
                for f in &result.failures {
                    println!(
                        "    - {}: expected {} got {}",
                        f.path,
                        &f.expected[..16],
                        &f.actual[..16]
                    );
                }
                for m in &result.missing {
                    println!("    - {m}: missing");
                }
                if !result.failures.is_empty() || !result.missing.is_empty() {
                    std::process::exit(1);
                }
            }
            OutputFormat::Json => {
                let obj = serde_json::json!({
                    "target": dir.display().to_string(),
                    "mode": "manifest",
                    "checked": result.checked,
                    "passed": result.passed,
                    "missing": result.missing,
                    "failures": result.failures.iter().map(|f| serde_json::json!({
                        "path": f.path,
                        "expected": f.expected,
                        "actual": f.actual,
                    })).collect::<Vec<_>>(),
                });
                println!(
                    "{}",
                    serde_json::to_string_pretty(&obj).expect("invariant: json")
                );
                if !result.failures.is_empty() || !result.missing.is_empty() {
                    std::process::exit(1);
                }
            }
            fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
                emit_delimited_row(&["status", "path", "detail"], fmt);
                for f in &result.failures {
                    let detail = format!("expected {} got {}", f.expected, f.actual);
                    emit_delimited_row(&["failed", &f.path, &detail], fmt);
                }
                for m in &result.missing {
                    emit_delimited_row(&["missing", m, ""], fmt);
                }
                let checked = result.checked.to_string();
                let passed = result.passed.to_string();
                emit_delimited_row(&["summary", "checked", &checked], fmt);
                emit_delimited_row(&["summary", "passed", &passed], fmt);
                if !result.failures.is_empty() || !result.missing.is_empty() {
                    std::process::exit(1);
                }
            }
        },
        Err(e) => {
            eprintln!("Manifest verify failed: {e}");
            std::process::exit(1);
        }
    }
}

fn run_walk_verify(dir: &Path, format: OutputFormat) {
    let mut checked = 0usize;
    let mut passed = 0usize;
    let mut failures: Vec<(PathBuf, String)> = Vec::new();
    walk_mathverse_files(dir, &mut |path| {
        checked += 1;
        match ShardReader::from_file(path) {
            Ok(_) => passed += 1,
            Err(e) => failures.push((path.to_path_buf(), e.to_string())),
        }
    });

    match format {
        OutputFormat::Table => {
            println!("Shard verification of {} (no manifest):", dir.display());
            println!("  Checked: {checked}");
            println!("  Passed:  {passed}");
            println!("  Failed:  {}", failures.len());
            for (p, err) in &failures {
                println!("    - {}: {err}", p.display());
            }
            if !failures.is_empty() {
                std::process::exit(1);
            }
        }
        OutputFormat::Json => {
            let obj = serde_json::json!({
                "target": dir.display().to_string(),
                "mode": "walk",
                "checked": checked,
                "passed": passed,
                "failures": failures.iter().map(|(p, e)| serde_json::json!({
                    "path": p.display().to_string(),
                    "error": e,
                })).collect::<Vec<_>>(),
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&obj).expect("invariant: json")
            );
            if !failures.is_empty() {
                std::process::exit(1);
            }
        }
        fmt @ (OutputFormat::Csv | OutputFormat::Tsv) => {
            emit_delimited_row(&["status", "path", "detail"], fmt);
            for (p, err) in &failures {
                emit_delimited_row(&["failed", &p.display().to_string(), err], fmt);
            }
            let checked_s = checked.to_string();
            let passed_s = passed.to_string();
            emit_delimited_row(&["summary", "checked", &checked_s], fmt);
            emit_delimited_row(&["summary", "passed", &passed_s], fmt);
            if !failures.is_empty() {
                std::process::exit(1);
            }
        }
    }
}

fn walk_mathverse_files(dir: &Path, f: &mut dyn FnMut(&Path)) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().collect();
    entries.sort_by_key(|entry| entry.path());
    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            walk_mathverse_files(&path, f);
        } else if path.extension().and_then(|s| s.to_str()) == Some("mathverse") {
            f(&path);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::walk_mathverse_files;
    use tempfile::tempdir;

    #[test]
    fn test_walk_mathverse_files_visits_paths_in_stable_order() {
        let dir = tempdir().expect("tempdir");
        let root = dir.path();
        std::fs::create_dir(root.join("b")).expect("mkdir b");
        std::fs::create_dir(root.join("a")).expect("mkdir a");
        std::fs::write(root.join("z.mathverse"), b"z").expect("write z");
        std::fs::write(root.join("a").join("c.mathverse"), b"c").expect("write c");
        std::fs::write(root.join("a").join("b.txt"), b"ignore").expect("write txt");
        std::fs::write(root.join("b").join("a.mathverse"), b"a").expect("write a");

        let mut visited = Vec::new();
        walk_mathverse_files(root, &mut |path| {
            visited.push(
                path.strip_prefix(root)
                    .expect("relative path")
                    .to_string_lossy()
                    .replace('\\', "/"),
            );
        });

        assert_eq!(
            visited,
            vec!["a/c.mathverse", "b/a.mathverse", "z.mathverse"]
        );
    }
}
