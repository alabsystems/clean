// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Isabelle corpus assembly** — the raw-export → replay-ready-corpus stage of
//! the standing import pipeline (P3 of
//! `designs/2026-07-07-isabelle-100pct-industrial-import.md`), replacing the
//! ad-hoc `assemble.py` + external `sort -n` chain with a bounded-memory,
//! deterministic, checked Rust implementation.
//!
//! Input: a directory of per-theory `<Theory.Name>.jsonl` files as written by
//! `scripts/isabelle/zproof_capture_hook.ML` (one JSON object per line, each
//! with a leading `{"serial":<n>,...` key).
//!
//! Output: ONE corpus file, lines strictly ascending by serial, duplicates
//! dropped (first occurrence in lexicographic-filename order wins — the same
//! first-wins semantics the historical `assemble.py` used), plus a
//! [`AssembleReport`] with the closure sanity stats the old `closure_check.py`
//! gated on (line/duplicate counts, `nop` proof roots, legacy `:null` holes,
//! missing referenced serials).
//!
//! Memory is bounded by two-pass serial-range bucketing: pass 1 histograms
//! serials, pass 2 distributes lines into ≤ `mem_budget`-sized bucket files,
//! pass 3 sorts each bucket in memory and appends in range order. The result
//! is byte-deterministic for a given input directory.

use std::collections::{BTreeMap, HashSet};
use std::io::{BufRead as _, Write as _};
use std::path::{Path, PathBuf};

/// Errors from corpus assembly. Typed so the CLI can distinguish input
/// problems from I/O failures.
#[derive(Debug, thiserror::Error)]
pub enum IsabelleImportError {
    /// Filesystem failure.
    #[error("isabelle-import I/O on {path}: {source}")]
    Io {
        /// Path involved.
        path: PathBuf,
        /// Underlying error.
        source: std::io::Error,
    },
    /// The raw directory contained no `.jsonl` theory files.
    #[error("no .jsonl theory files found under {0}")]
    NoInputs(PathBuf),
}

fn io_err(path: &Path) -> impl FnOnce(std::io::Error) -> IsabelleImportError + '_ {
    move |source| IsabelleImportError::Io {
        path: path.to_path_buf(),
        source,
    }
}

/// What [`assemble_corpus`] did and what the corpus looks like — the
/// machine-checkable half of the old `closure_check.py` gates.
#[derive(Debug, Clone, Default)]
pub struct AssembleReport {
    /// Theory files consumed, in the deterministic (sorted) order used.
    pub files: usize,
    /// Total non-empty input lines.
    pub lines_in: usize,
    /// Duplicate-serial lines dropped (first occurrence kept).
    pub duplicates_dropped: usize,
    /// Lines with no parseable leading serial (kept out of the corpus,
    /// reported here — an export bug if nonzero).
    pub unparseable: usize,
    /// Lines written to the corpus.
    pub lines_out: usize,
    /// Corpus bytes written.
    pub bytes_out: u64,
    /// Lines whose proof root is the `nop` hole (`"proof":{"k":"nop"}`).
    pub nop_lines: usize,
    /// Occurrences of a legacy `:null` hole anywhere (must be 0 for zproof
    /// exports — the %NONE elimination invariant).
    pub null_holes: usize,
    /// Distinct referenced serials (`"k":"thm","id":N`) absent from the
    /// corpus — the unresolved-dep floor of any replay.
    pub missing_refs: usize,
}

/// Parse the leading serial of a corpus line (`{"serial":<digits>`).
#[must_use]
pub fn leading_serial(line: &str) -> Option<i64> {
    let rest = line.strip_prefix("{\"serial\":")?;
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

/// Every `"k":"thm","id":<n>` reference on the line — the same conservative
/// byte-level superset of `IsaProof::thm_deps` the parallel driver schedules
/// with. Shared with the slice extractor.
pub(crate) fn thm_refs_public(line: &str, out: &mut Vec<i64>) {
    let needle = "\"k\":\"thm\",\"id\":";
    let mut start = 0usize;
    while let Some(pos) = line[start..].find(needle) {
        let at = start + pos + needle.len();
        let digits: String = line[at..]
            .chars()
            .take_while(|c| c.is_ascii_digit() || *c == '-')
            .collect();
        if let Ok(id) = digits.parse::<i64>() {
            out.push(id);
        }
        start = at;
    }
}

/// The sorted `.jsonl` inputs under `raw_dir` (deterministic order).
fn theory_files(raw_dir: &Path) -> Result<Vec<PathBuf>, IsabelleImportError> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(raw_dir)
        .map_err(io_err(raw_dir))?
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|e| e == "jsonl"))
        .collect();
    files.sort();
    if files.is_empty() {
        return Err(IsabelleImportError::NoInputs(raw_dir.to_path_buf()));
    }
    Ok(files)
}

/// Assemble the per-theory exports under `raw_dir` into ONE serial-sorted,
/// deduplicated corpus at `out_corpus`, using at most ~`mem_budget` bytes of
/// line data in memory at a time. Returns the [`AssembleReport`].
///
/// # Errors
/// [`IsabelleImportError`] on I/O failure or an empty input directory.
pub fn assemble_corpus(
    raw_dir: &Path,
    out_corpus: &Path,
    mem_budget: usize,
) -> Result<AssembleReport, IsabelleImportError> {
    let files = theory_files(raw_dir)?;
    let mut report = AssembleReport {
        files: files.len(),
        ..AssembleReport::default()
    };

    // PASS 1 — serial histogram (16k-wide ranges) + closure-stat collection.
    let mut histogram: BTreeMap<i64, u64> = BTreeMap::new(); // range_key -> bytes
    let mut serials: HashSet<i64> = HashSet::new();
    let mut refs: HashSet<i64> = HashSet::new();
    let mut ref_buf: Vec<i64> = Vec::new();
    for f in &files {
        let reader = std::io::BufReader::new(std::fs::File::open(f).map_err(io_err(f))?);
        for line in reader.lines() {
            let line = line.map_err(io_err(f))?;
            if line.trim().is_empty() {
                continue;
            }
            report.lines_in += 1;
            let Some(serial) = leading_serial(&line) else {
                report.unparseable += 1;
                continue;
            };
            serials.insert(serial);
            *histogram.entry(serial >> 14).or_insert(0) += line.len() as u64 + 1;
            ref_buf.clear();
            thm_refs_public(&line, &mut ref_buf);
            refs.extend(ref_buf.iter().copied());
            if line.contains("\"proof\":{\"k\":\"nop\"}") {
                report.nop_lines += 1;
            }
            report.null_holes += line.matches(":null").count();
        }
    }
    report.missing_refs = refs.difference(&serials).count();
    drop(refs);

    // Choose contiguous range-key buckets whose byte sums stay under budget
    // (a single overweight range still becomes its own bucket — sorted alone).
    let mut buckets: Vec<(i64, i64)> = Vec::new(); // inclusive range-key spans
    {
        let mut span_start: Option<i64> = None;
        let mut span_bytes: u64 = 0;
        let mut last_key = 0i64;
        for (&key, &bytes) in &histogram {
            match span_start {
                None => {
                    span_start = Some(key);
                    span_bytes = bytes;
                }
                Some(start) => {
                    if span_bytes + bytes > mem_budget as u64 {
                        buckets.push((start, last_key));
                        span_start = Some(key);
                        span_bytes = bytes;
                    } else {
                        span_bytes += bytes;
                    }
                }
            }
            last_key = key;
        }
        if let Some(start) = span_start {
            buckets.push((start, last_key));
        }
    }

    // PASS 2 — distribute lines into per-bucket temp files (input order
    // preserved within each bucket = the dedup-first-wins order).
    let tmp_dir = out_corpus.with_extension("assemble.tmp");
    let _ = std::fs::remove_dir_all(&tmp_dir);
    std::fs::create_dir_all(&tmp_dir).map_err(io_err(&tmp_dir))?;
    let bucket_of = |serial: i64| -> usize {
        let key = serial >> 14;
        buckets
            .iter()
            .position(|&(a, b)| key >= a && key <= b)
            .unwrap_or(buckets.len().saturating_sub(1))
    };
    {
        let mut writers: Vec<std::io::BufWriter<std::fs::File>> = buckets
            .iter()
            .enumerate()
            .map(|(i, _)| {
                let p = tmp_dir.join(format!("bucket{i:05}.jsonl"));
                std::fs::File::create(&p)
                    .map(std::io::BufWriter::new)
                    .map_err(io_err(&p))
            })
            .collect::<Result<_, _>>()?;
        for f in &files {
            let reader = std::io::BufReader::new(std::fs::File::open(f).map_err(io_err(f))?);
            for line in reader.lines() {
                let line = line.map_err(io_err(f))?;
                if line.trim().is_empty() {
                    continue;
                }
                let Some(serial) = leading_serial(&line) else {
                    continue;
                };
                let w = &mut writers[bucket_of(serial)];
                w.write_all(line.as_bytes()).map_err(io_err(&tmp_dir))?;
                w.write_all(b"\n").map_err(io_err(&tmp_dir))?;
            }
        }
        for w in &mut writers {
            w.flush().map_err(io_err(&tmp_dir))?;
        }
    }

    // PASS 3 — per bucket: stable sort by serial, dedup keep-first, append.
    let mut out =
        std::io::BufWriter::new(std::fs::File::create(out_corpus).map_err(io_err(out_corpus))?);
    let mut seen: HashSet<i64> = HashSet::new();
    for i in 0..buckets.len() {
        let p = tmp_dir.join(format!("bucket{i:05}.jsonl"));
        let reader = std::io::BufReader::new(std::fs::File::open(&p).map_err(io_err(&p))?);
        let mut entries: Vec<(i64, String)> = Vec::new();
        for line in reader.lines() {
            let line = line.map_err(io_err(&p))?;
            if let Some(serial) = leading_serial(&line) {
                entries.push((serial, line));
            }
        }
        entries.sort_by_key(|(s, _)| *s); // stable: preserves first-wins order
        for (serial, line) in entries {
            if !seen.insert(serial) {
                report.duplicates_dropped += 1;
                continue;
            }
            out.write_all(line.as_bytes()).map_err(io_err(out_corpus))?;
            out.write_all(b"\n").map_err(io_err(out_corpus))?;
            report.lines_out += 1;
            report.bytes_out += line.len() as u64 + 1;
        }
    }
    out.flush().map_err(io_err(out_corpus))?;
    let _ = std::fs::remove_dir_all(&tmp_dir);
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;

    const FIXTURE: &str =
        include_str!("../../tests/fixtures/isabelle/hol_foundational_closure.jsonl");

    /// Assembling shuffled multi-file input with cross-file duplicates must
    /// yield the serial-sorted, deduplicated corpus — byte-equal to sorting
    /// the fixture directly — and report accurate stats.
    #[test]
    fn test_assemble_corpus_sorted_dedup_matches_reference() {
        let dir = std::env::temp_dir().join(format!("isa_assemble_{}", std::process::id()));
        let raw = dir.join("raw");
        std::fs::create_dir_all(&raw).expect("mk raw dir");

        let mut lines: Vec<&str> = FIXTURE.lines().filter(|l| !l.trim().is_empty()).collect();
        // Three "theory files": interleave thirds, and duplicate a slice of
        // file A's lines into file C (first-wins must keep A's copies).
        let split_lines = lines.clone();
        let (a, rest) = split_lines.split_at(split_lines.len() / 3);
        let (b, c) = rest.split_at(rest.len() / 2);
        for (name, chunk, dup) in [
            ("HOL.A.jsonl", a, None),
            ("HOL.B.jsonl", b, None),
            ("HOL.C.jsonl", c, Some(&a[..a.len() / 2])),
        ] {
            let mut f = std::fs::File::create(raw.join(name)).expect("create theory file");
            for l in chunk {
                writeln!(f, "{l}").expect("write");
            }
            if let Some(d) = dup {
                for l in d.iter() {
                    writeln!(f, "{l}").expect("write dup");
                }
            }
        }

        let corpus = dir.join("corpus.jsonl");
        // Tiny budget to force multiple buckets (exercises the range split).
        let report = assemble_corpus(&raw, &corpus, 4096).expect("assemble");

        // Reference: sort the fixture lines by serial.
        lines.sort_by_key(|l| leading_serial(l).expect("fixture serials parse"));
        let expect: String = lines.iter().map(|l| format!("{l}\n")).collect();
        let got = std::fs::read_to_string(&corpus).expect("read corpus");
        assert_eq!(got, expect, "corpus must equal serial-sorted fixture");

        assert_eq!(report.files, 3, "three theory files");
        assert_eq!(report.lines_out, lines.len(), "all unique lines kept");
        assert_eq!(
            report.duplicates_dropped,
            a[..a.len() / 2].len(),
            "cross-file duplicates dropped"
        );
        assert_eq!(report.unparseable, 0, "fixture parses fully");
        // The committed fixture predates the zproof exporter, so legacy
        // `:null` holes exist — the stat must equal a direct recount over the
        // UNIQUE lines (the report counts pass-1 input, which includes the
        // duplicated slice; recount accordingly).
        let direct: usize = lines
            .iter()
            .chain(a[..a.len() / 2].iter())
            .map(|l| l.matches(":null").count())
            .sum();
        assert_eq!(
            report.null_holes, direct,
            "null-hole stat must match recount"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }
}
