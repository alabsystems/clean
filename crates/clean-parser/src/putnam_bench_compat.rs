// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PutnamBench parser compatibility tests.

use crate::{ParseError, Parser};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Once;

const MIN_PUTNAMBENCH_PARSE_PCT: f64 = 98.0;

fn init_test_logging() {
    static INIT: Once = Once::new();

    INIT.call_once(|| {
        let _ = tracing_subscriber::fmt()
            .with_test_writer()
            .without_time()
            .with_target(false)
            .try_init();
    });
}

fn resolve_putnam_bench_corpus_dir() -> Option<PathBuf> {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let candidates = [
        std::env::var_os("CLEAN_PUTNAMBENCH_DIR").map(PathBuf::from),
        Some(manifest_dir.join("../../../PutnamBench-ref")),
        Some(manifest_dir.join("../../research/axiom/code/PutnamBench")),
    ];

    candidates
        .into_iter()
        .flatten()
        .find_map(normalize_corpus_dir)
}

fn normalize_corpus_dir(candidate: PathBuf) -> Option<PathBuf> {
    let corpus_dir = if candidate.join("lean4/src").is_dir() {
        candidate.join("lean4/src")
    } else if candidate.join("src").is_dir() {
        candidate.join("src")
    } else if candidate.is_dir() {
        candidate
    } else {
        return None;
    };

    corpus_dir
        .join("putnam_1962_a1.lean")
        .is_file()
        .then_some(corpus_dir)
}

fn collect_lean_files(dir: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_lean_files(&path, files)?;
        } else if path.extension().is_some_and(|ext| ext == "lean") {
            files.push(path);
        }
    }
    Ok(())
}

fn parse_with_small_stack(source: String) -> Result<(), ParseError> {
    std::thread::Builder::new()
        .stack_size(clean_kernel::test_utils::SMALL_STACK)
        .spawn(move || Parser::parse_file(&source).map(|_| ()))
        .expect("should spawn parser thread")
        .join()
        .unwrap_or_else(|_| {
            Err(ParseError::UnexpectedToken {
                line: 0,
                col: 0,
                message: "parser thread panicked or overflowed".to_string(),
            })
        })
}

fn collect_failures(corpus_dir: &Path, files: &[PathBuf]) -> (usize, Vec<(String, String)>) {
    let mut passed = 0usize;
    let mut failures = Vec::new();

    for path in files {
        let content = fs::read_to_string(path).expect("PutnamBench corpus file should be readable");
        match parse_with_small_stack(content) {
            Ok(()) => passed += 1,
            Err(err) => {
                let relative = path
                    .strip_prefix(corpus_dir)
                    .unwrap_or(path)
                    .display()
                    .to_string();
                failures.push((relative, err.to_string()));
            }
        }
    }

    (passed, failures)
}

fn print_report(corpus_dir: &Path, passed: usize, total: usize, failures: &[(String, String)]) {
    let failed = failures.len();
    let percentage = 100.0 * passed as f64 / total as f64;

    tracing::info!("");
    tracing::info!("========================================");
    tracing::info!("PutnamBench Parser Compatibility Report");
    tracing::info!("========================================");
    tracing::info!("Corpus: {}", corpus_dir.display());
    tracing::info!("Passed: {passed}");
    tracing::info!("Failed: {failed}");
    tracing::info!("Total:  {total}");
    tracing::info!("Compatibility: {percentage:.1}% ({passed}/{total})");
    tracing::info!("========================================");

    if !failures.is_empty() {
        tracing::info!("");
        tracing::info!("First {} failures:", failures.len().min(25));
        for (path, err) in failures.iter().take(25) {
            let short_err = err.lines().next().unwrap_or(err);
            tracing::info!("  {path} - {short_err}");
        }
    }
}

/// Parse the full local PutnamBench Lean 4 corpus when it is available.
///
/// This is an opt-in local baseline test: it exits cleanly when no checkout is
/// present, and otherwise reports file-level parser compatibility over the
/// upstream `lean4/src` corpus.
#[test]
fn putnam_bench_full_corpus_parse_baseline() {
    init_test_logging();

    let Some(corpus_dir) = resolve_putnam_bench_corpus_dir() else {
        tracing::info!(
            "PutnamBench checkout not found. Set CLEAN_PUTNAMBENCH_DIR or clone to ~/PutnamBench-ref."
        );
        return;
    };

    let mut files = Vec::new();
    collect_lean_files(&corpus_dir, &mut files).expect("should collect PutnamBench files");
    files.sort();
    assert!(
        !files.is_empty(),
        "PutnamBench corpus at {} should contain .lean files",
        corpus_dir.display()
    );

    let total = files.len();
    let (passed, failures) = collect_failures(&corpus_dir, &files);
    let percentage = 100.0 * passed as f64 / total as f64;

    print_report(&corpus_dir, passed, total, &failures);

    assert_eq!(
        passed + failures.len(),
        total,
        "every PutnamBench file should be counted exactly once"
    );
    // Baseline on 2026-03-12 against the current PutnamBench checkout:
    // 98.7% (663/672) after adding postfix ! (factorial/get-or-panic),
    // neighborhood filter 𝓝[op] notation, inner product ⟪x, y⟫, letI/haveI
    // keywords, anonymous instance let, named instance brackets [n : T],
    // let-tuple body retry, ≃ₗᵢ typed equiv subscript, and expanded
    // implicit body starters (∃, ∀, ¬, if, NatLit).
    // Remaining 9 failures: nested ⟨⟨⟩⟩, nested lambda tuples, layout
    // sensitivity, |x| pipe ambiguity, conditional measures, ⨅ set builders.
    assert!(
        percentage >= MIN_PUTNAMBENCH_PARSE_PCT,
        "PutnamBench parser regression: {:.1}% < {:.1}% threshold (passed {}/{})",
        percentage,
        MIN_PUTNAMBENCH_PARSE_PCT,
        passed,
        total
    );
}
