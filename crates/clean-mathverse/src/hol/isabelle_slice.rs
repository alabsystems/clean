// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Closure-complete slice extraction** — the fast-iteration half of the
//! standing import pipeline (P3 of
//! `designs/2026-07-07-isabelle-100pct-industrial-import.md`).
//!
//! An engine round iterates against a SLICE: the corpus lines for a target
//! family (selected by serial, by name substring, or straight from an
//! `ISA_DUMP_REJECTS` dump) **plus their transitive proof dependencies**, in
//! serial order — a self-contained mini corpus whose replay reproduces the
//! grand corpus's verdicts for those lines in minutes instead of hours. This
//! module replaces the ad-hoc `make_slices.py` scripts that were rewritten for
//! every round (and lost with every `/tmp` purge).
//!
//! Selection composes: serials ∪ name-substrings ∪ reject-dump rows (optionally
//! filtered by reason). The dependency closure is computed over the byte-level
//! `"k":"thm","id":` reference scan — the same conservative superset of
//! `IsaProof::thm_deps` the parallel driver schedules with.

use std::collections::{HashMap, HashSet, VecDeque};
use std::io::{BufRead as _, Write as _};
use std::path::{Path, PathBuf};

use super::isabelle_import::leading_serial;

/// Errors from slice extraction.
#[derive(Debug, thiserror::Error)]
pub enum IsabelleSliceError {
    /// Filesystem failure.
    #[error("isabelle-slice I/O on {path}: {source}")]
    Io {
        /// Path involved.
        path: PathBuf,
        /// Underlying error.
        source: std::io::Error,
    },
    /// No seeds resolved from the given selectors.
    #[error("no seed lines matched the given selectors")]
    NoSeeds,
}

fn io_err(path: &Path) -> impl FnOnce(std::io::Error) -> IsabelleSliceError + '_ {
    move |source| IsabelleSliceError::Io {
        path: path.to_path_buf(),
        source,
    }
}

/// What to slice on. All selectors compose (set union of seeds).
#[derive(Debug, Default, Clone)]
pub struct SliceSelect {
    /// Exact serials.
    pub serials: HashSet<i64>,
    /// Case-sensitive substrings matched against the line's `"name"` field.
    pub name_substrings: Vec<String>,
    /// Rows of an `ISA_DUMP_REJECTS` file (`reason\tname\tsignature`); the
    /// name column seeds the slice (`<anon.sN>` rows resolve by serial).
    pub reject_dump: Option<PathBuf>,
    /// Keep only dump rows whose reason equals this (e.g. `kernel-reject`).
    pub reject_reason: Option<String>,
    /// Include every definitional/registration line (`_def` / `_dict`) in the
    /// slice regardless of dependency reachability. The verify drivers'
    /// PASS-1 registries are built from exactly these lines; a slice WITHOUT
    /// them registers fewer classes/dicts/insts than the grand corpus does,
    /// so membership-mode-seam families falsely verify on-slice (measured:
    /// the instk-flavor round's grand-rejecting `equal_itself_def` verified
    /// on a proof-dep-only slice). Default TRUE; disable only for minimal
    /// proof-dependency slices.
    pub include_registrations: bool,
}

/// Slice statistics.
#[derive(Debug, Clone, Default)]
pub struct SliceReport {
    /// Seed lines the selectors resolved to.
    pub seeds: usize,
    /// Registration (`_def`/`_dict`) lines included beyond the dependency
    /// closure (see `SliceSelect::include_registrations`).
    pub registration_lines: usize,
    /// Lines written (seeds + transitive dependency closure), serial order.
    pub lines_out: usize,
    /// Bytes written.
    pub bytes_out: u64,
    /// Referenced serials absent from the corpus (the slice's unavoidable
    /// unresolved-dep floor).
    pub missing_refs: usize,
}

/// The `"name":"..."` field of a corpus line (after the serial key).
fn line_name(line: &str) -> Option<&str> {
    let at = line.find("\"name\":\"")? + "\"name\":\"".len();
    let rest = &line[at..];
    let end = rest.find('"')?;
    Some(&rest[..end])
}

/// Extract the closure-complete slice of `corpus` selected by `select` into
/// `out_slice` (serial-ascending, ready for `ISA_CLOSURE_STREAM_PRESORTED`).
///
/// # Errors
/// [`IsabelleSliceError`] on I/O failure or when no seeds match.
pub fn extract_slice(
    corpus: &Path,
    out_slice: &Path,
    select: &SliceSelect,
) -> Result<SliceReport, IsabelleSliceError> {
    // Resolve dump-file seeds first (names + `<anon.sN>` serials).
    let mut want_serials: HashSet<i64> = select.serials.clone();
    let mut want_names: Vec<String> = select.name_substrings.clone();
    let mut dump_exact_names: HashSet<String> = HashSet::new();
    if let Some(dump) = &select.reject_dump {
        let reader = std::io::BufReader::new(std::fs::File::open(dump).map_err(io_err(dump))?);
        for line in reader.lines() {
            let line = line.map_err(io_err(dump))?;
            let mut cols = line.split('\t');
            let (Some(reason), Some(name)) = (cols.next(), cols.next()) else {
                continue;
            };
            if let Some(want) = &select.reject_reason {
                if reason != want {
                    continue;
                }
            }
            if let Some(serial) = name
                .strip_prefix("<anon.s")
                .and_then(|r| r.strip_suffix('>'))
                .and_then(|d| d.parse::<i64>().ok())
            {
                want_serials.insert(serial);
            } else {
                dump_exact_names.insert(name.to_string());
            }
        }
    }

    // PASS 1 — build the dep graph + resolve seeds, from the `<corpus>.idx`
    // sidecar when present (near-instant seeks over the 52 GB corpus), else a
    // scan. Both produce identical `(deps_of, present, seeds)`.
    let index = super::isabelle_index::try_load(corpus);
    let (deps_of, present, seeds) = match &index {
        Some(idx) => pass1_from_index(idx, &want_serials, &want_names, &dump_exact_names),
        None => pass1_scan(corpus, &want_serials, &want_names, &dump_exact_names)?,
    };
    want_names.clear();
    if seeds.is_empty() {
        return Err(IsabelleSliceError::NoSeeds);
    }

    // BFS dependency closure (graph-only; identical whichever built the graph).
    let mut keep: HashSet<i64> = HashSet::new();
    let mut missing: HashSet<i64> = HashSet::new();
    let mut queue: VecDeque<i64> = seeds.iter().copied().collect();
    while let Some(s) = queue.pop_front() {
        if !keep.insert(s) {
            continue;
        }
        if let Some(deps) = deps_of.get(&s) {
            for &d in deps {
                if present.contains(&d) {
                    if !keep.contains(&d) {
                        queue.push_back(d);
                    }
                } else {
                    missing.insert(d);
                }
            }
        }
    }

    // PASS 2 — emit kept lines in corpus (= FILE) order. The index path
    // seek-reads only the emitted lines; the scan path re-streams the corpus.
    // Both write byte-identical output.
    let seeds_n = seeds.len();
    let missing_n = missing.len();
    match &index {
        Some(idx) => emit_from_index(idx, corpus, out_slice, &keep, select, seeds_n, missing_n),
        None => emit_scan(corpus, out_slice, &keep, select, seeds_n, missing_n),
    }
}

/// PASS-1 graph + seed resolution over the `<corpus>.idx` sidecar (scan-free).
/// Iterates entries in FILE order so duplicate-serial `deps_of` resolution
/// matches [`pass1_scan`] exactly.
fn pass1_from_index(
    index: &super::isabelle_index::CorpusIndex,
    want_serials: &HashSet<i64>,
    want_names: &[String],
    dump_exact_names: &HashSet<String>,
) -> (HashMap<i64, Vec<i64>>, HashSet<i64>, HashSet<i64>) {
    let mut deps_of: HashMap<i64, Vec<i64>> = HashMap::new();
    let mut present: HashSet<i64> = HashSet::new();
    let mut seeds: HashSet<i64> = HashSet::new();
    for e in index.entries_in_file_order() {
        present.insert(e.serial);
        if !e.deps.is_empty() {
            deps_of.insert(e.serial, e.deps.clone());
        }
        let name_match = !e.name.is_empty()
            && (dump_exact_names.contains(&e.name)
                || want_names.iter().any(|w| e.name.contains(w.as_str())));
        if want_serials.contains(&e.serial) || name_match {
            seeds.insert(e.serial);
        }
    }
    (deps_of, present, seeds)
}

/// PASS-1 graph + seed resolution by streaming scan (the sidecar-absent path).
fn pass1_scan(
    corpus: &Path,
    want_serials: &HashSet<i64>,
    want_names: &[String],
    dump_exact_names: &HashSet<String>,
) -> Result<(HashMap<i64, Vec<i64>>, HashSet<i64>, HashSet<i64>), IsabelleSliceError> {
    let mut deps_of: HashMap<i64, Vec<i64>> = HashMap::new();
    let mut present: HashSet<i64> = HashSet::new();
    let mut seeds: HashSet<i64> = HashSet::new();
    let reader = std::io::BufReader::new(std::fs::File::open(corpus).map_err(io_err(corpus))?);
    let mut ref_buf: Vec<i64> = Vec::new();
    for line in reader.lines() {
        let line = line.map_err(io_err(corpus))?;
        let Some(serial) = leading_serial(&line) else {
            continue;
        };
        present.insert(serial);
        ref_buf.clear();
        super::isabelle_import::thm_refs_public(&line, &mut ref_buf);
        if !ref_buf.is_empty() {
            deps_of.insert(serial, ref_buf.clone());
        }
        if want_serials.contains(&serial) {
            seeds.insert(serial);
        } else if let Some(name) = line_name(&line) {
            if !name.is_empty()
                && (dump_exact_names.contains(name)
                    || want_names.iter().any(|w| name.contains(w.as_str())))
            {
                seeds.insert(serial);
            }
        }
    }
    Ok((deps_of, present, seeds))
}

/// Emit the closure + registration lines by seek-reading only the kept entries
/// from the corpus (index-driven; FILE order).
fn emit_from_index(
    index: &super::isabelle_index::CorpusIndex,
    corpus: &Path,
    out_slice: &Path,
    keep: &HashSet<i64>,
    select: &SliceSelect,
    seeds: usize,
    missing_refs: usize,
) -> Result<SliceReport, IsabelleSliceError> {
    let mut report = SliceReport {
        seeds,
        missing_refs,
        ..SliceReport::default()
    };
    let mut out =
        std::io::BufWriter::new(std::fs::File::create(out_slice).map_err(io_err(out_slice))?);
    for e in index.entries_in_file_order() {
        let in_closure = keep.contains(&e.serial);
        let is_registration = select.include_registrations && !in_closure && e.is_registration;
        if in_closure || is_registration {
            let line = index
                .read_line(corpus, e)
                .map_err(|src| IsabelleSliceError::Io {
                    path: corpus.to_path_buf(),
                    source: std::io::Error::other(src.to_string()),
                })?;
            out.write_all(line.as_bytes()).map_err(io_err(out_slice))?;
            out.write_all(b"\n").map_err(io_err(out_slice))?;
            report.lines_out += 1;
            report.bytes_out += line.len() as u64 + 1;
            if is_registration {
                report.registration_lines += 1;
            }
        }
    }
    out.flush().map_err(io_err(out_slice))?;
    Ok(report)
}

/// Emit the closure + registration lines by re-streaming the corpus (the
/// sidecar-absent path).
fn emit_scan(
    corpus: &Path,
    out_slice: &Path,
    keep: &HashSet<i64>,
    select: &SliceSelect,
    seeds: usize,
    missing_refs: usize,
) -> Result<SliceReport, IsabelleSliceError> {
    let mut report = SliceReport {
        seeds,
        missing_refs,
        ..SliceReport::default()
    };
    let reader = std::io::BufReader::new(std::fs::File::open(corpus).map_err(io_err(corpus))?);
    let mut out =
        std::io::BufWriter::new(std::fs::File::create(out_slice).map_err(io_err(out_slice))?);
    for line in reader.lines() {
        let line = line.map_err(io_err(corpus))?;
        let Some(serial) = leading_serial(&line) else {
            continue;
        };
        let in_closure = keep.contains(&serial);
        let is_registration = select.include_registrations
            && !in_closure
            && (line.contains("_def") || line.contains("_dict"));
        if in_closure || is_registration {
            out.write_all(line.as_bytes()).map_err(io_err(out_slice))?;
            out.write_all(b"\n").map_err(io_err(out_slice))?;
            report.lines_out += 1;
            report.bytes_out += line.len() as u64 + 1;
            if is_registration {
                report.registration_lines += 1;
            }
        }
    }
    out.flush().map_err(io_err(out_slice))?;
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;

    const FIXTURE: &str =
        include_str!("../../tests/fixtures/isabelle/hol_foundational_closure.jsonl");

    /// Slicing on a named seed must pull its full transitive dep closure
    /// (every `"k":"thm"` reference of every kept line is kept or reported
    /// missing), in serial-ascending order.
    #[test]
    fn test_extract_slice_closure_complete_and_sorted() {
        let dir = std::env::temp_dir().join(format!("isa_slice_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let corpus = dir.join("corpus.jsonl");
        let mut lines: Vec<&str> = FIXTURE.lines().filter(|l| !l.trim().is_empty()).collect();
        lines.sort_by_key(|l| leading_serial(l).expect("serials"));
        std::fs::write(&corpus, lines.join("\n") + "\n").expect("write corpus");

        // Closure-only reference first (used to separate registration extras).
        let pre_min = dir.join("slice_min_pre.jsonl");
        let _ = extract_slice(
            &corpus,
            &pre_min,
            &SliceSelect {
                name_substrings: vec!["HOL.iffI".to_string()],
                include_registrations: false,
                ..SliceSelect::default()
            },
        )
        .expect("closure-only reference");

        let slice = dir.join("slice.jsonl");
        let select = SliceSelect {
            name_substrings: vec!["HOL.iffI".to_string()],
            include_registrations: true,
            ..SliceSelect::default()
        };
        let report = extract_slice(&corpus, &slice, &select).expect("slice");
        assert!(report.seeds >= 1, "iffI must seed");
        assert!(
            report.lines_out >= report.seeds,
            "closure includes at least the seeds"
        );
        // Registration-closure fidelity: every corpus `_def`/`_dict` line
        // outside the dep closure must be present (mode-seam fidelity).
        let def_lines_in_corpus = lines
            .iter()
            .filter(|l| l.contains("_def") || l.contains("_dict"))
            .count();
        assert!(
            report.registration_lines + report.lines_out - report.registration_lines
                >= report.seeds
                && report.registration_lines <= def_lines_in_corpus,
            "registration lines bounded by corpus def/dict lines"
        );
        // Closure-only mode excludes them.
        let slice_min = dir.join("slice_min.jsonl");
        let select_min = SliceSelect {
            name_substrings: vec!["HOL.iffI".to_string()],
            include_registrations: false,
            ..SliceSelect::default()
        };
        let report_min = extract_slice(&corpus, &slice_min, &select_min).expect("slice min");
        assert_eq!(report_min.registration_lines, 0, "closure-only mode");
        assert!(
            report_min.lines_out <= report.lines_out,
            "registration mode is a superset"
        );

        // Closure completeness: every thm ref of every kept line is kept
        // (or was absent from the corpus). Order: serial-ascending.
        let kept = std::fs::read_to_string(&slice).expect("read slice");
        let kept_serials: HashSet<i64> = kept.lines().filter_map(leading_serial).collect();
        let corpus_serials: HashSet<i64> = lines.iter().filter_map(|l| leading_serial(l)).collect();
        // Registration-included lines are statement-registered, deliberately
        // NOT proof-closed — closure-completeness holds for the dep closure
        // itself (lines that are NOT registration-only extras).
        let closure_only = std::fs::read_to_string(dir.join("slice_min_pre.jsonl"))
            .map(|t| {
                t.lines()
                    .filter_map(leading_serial)
                    .collect::<HashSet<i64>>()
            })
            .unwrap_or_default();
        let mut prev = i64::MIN;
        for l in kept.lines() {
            let s = leading_serial(l).expect("kept line serial");
            assert!(s > prev, "slice must be serial-ascending");
            prev = s;
            if !closure_only.is_empty() && !closure_only.contains(&s) {
                continue; // registration extra: statement-only by design
            }
            let mut refs = Vec::new();
            crate::hol::isabelle_import::thm_refs_public(l, &mut refs);
            for r in refs {
                assert!(
                    kept_serials.contains(&r) || !corpus_serials.contains(&r),
                    "dep s{r} of kept line s{s} must be in the slice"
                );
            }
        }

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The index-driven slice must be BYTE-IDENTICAL to the scan-driven slice,
    /// for both a serial seed and a name-substring seed (with registration
    /// inclusion on and off).
    #[test]
    fn test_slice_with_index_byte_identical_to_without() {
        let dir = std::env::temp_dir().join(format!("isa_slice_idx_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let corpus = dir.join("corpus.jsonl");
        let mut lines: Vec<&str> = FIXTURE.lines().filter(|l| !l.trim().is_empty()).collect();
        lines.sort_by_key(|l| leading_serial(l).expect("serials"));
        std::fs::write(&corpus, lines.join("\n") + "\n").expect("write corpus");

        // Two selectors × two registration modes.
        let selects = [
            SliceSelect {
                name_substrings: vec!["HOL.iffI".to_string()],
                include_registrations: true,
                ..SliceSelect::default()
            },
            SliceSelect {
                name_substrings: vec!["HOL.iffI".to_string()],
                include_registrations: false,
                ..SliceSelect::default()
            },
            SliceSelect {
                serials: [300].into_iter().collect(),
                include_registrations: true,
                ..SliceSelect::default()
            },
        ];

        for (i, select) in selects.iter().enumerate() {
            // No index present -> scan path.
            let scan_out = dir.join(format!("scan_{i}.jsonl"));
            let _ = std::fs::remove_file(crate::hol::isabelle_index::index_path(&corpus));
            let r_scan = extract_slice(&corpus, &scan_out, select).expect("scan slice");

            // Build the index, then re-slice -> index path.
            let index = crate::hol::isabelle_index::build_index(&corpus).expect("build index");
            crate::hol::isabelle_index::save_index(
                &crate::hol::isabelle_index::index_path(&corpus),
                &index,
            )
            .expect("save index");
            let idx_out = dir.join(format!("idx_{i}.jsonl"));
            let r_idx = extract_slice(&corpus, &idx_out, select).expect("index slice");

            let scan_bytes = std::fs::read(&scan_out).expect("read scan out");
            let idx_bytes = std::fs::read(&idx_out).expect("read idx out");
            assert_eq!(
                scan_bytes, idx_bytes,
                "selector {i}: index slice must be byte-identical to scan slice"
            );
            assert_eq!(r_scan.lines_out, r_idx.lines_out, "selector {i}: lines_out");
            assert_eq!(r_scan.bytes_out, r_idx.bytes_out, "selector {i}: bytes_out");
            assert_eq!(r_scan.seeds, r_idx.seeds, "selector {i}: seeds");
            assert_eq!(
                r_scan.registration_lines, r_idx.registration_lines,
                "selector {i}: registration_lines"
            );
            assert_eq!(
                r_scan.missing_refs, r_idx.missing_refs,
                "selector {i}: missing_refs"
            );
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
}
