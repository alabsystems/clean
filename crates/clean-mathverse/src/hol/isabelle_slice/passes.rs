// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The two corpus passes behind [`super::extract_slice`].
//!
//! PASS 1 builds the dependency graph and resolves the seed set; PASS 2 emits
//! the kept lines in corpus (= FILE) order. Each pass has an index-backed
//! variant (seek-reads through the `<corpus>.idx` sidecar) and a streaming
//! scan variant (the sidecar-absent path). The two variants of a pass are
//! required to produce identical results — `pass1_from_index` iterates in FILE
//! order precisely so its duplicate-serial `deps_of` resolution matches
//! `pass1_scan`, and `emit_from_index` / `emit_scan` write byte-identical
//! output. Keeping the four together makes that pairwise obligation local.

use std::collections::{HashMap, HashSet};
use std::io::{BufRead as _, Write as _};
use std::path::Path;

use super::{io_err, IsabelleSliceError, SliceReport, SliceSelect};
use crate::hol::isabelle_import::leading_serial;

/// The `"name":"..."` field of a corpus line (after the serial key).
fn line_name(line: &str) -> Option<&str> {
    let at = line.find("\"name\":\"")? + "\"name\":\"".len();
    let rest = &line[at..];
    let end = rest.find('"')?;
    Some(&rest[..end])
}

/// PASS-1 graph + seed resolution over the `<corpus>.idx` sidecar (scan-free).
/// Iterates entries in FILE order so duplicate-serial `deps_of` resolution
/// matches [`pass1_scan`] exactly.
pub(super) fn pass1_from_index(
    index: &crate::hol::isabelle_index::CorpusIndex,
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
pub(super) fn pass1_scan(
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
        crate::hol::isabelle_import::thm_refs_public(&line, &mut ref_buf);
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
pub(super) fn emit_from_index(
    index: &crate::hol::isabelle_index::CorpusIndex,
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
pub(super) fn emit_scan(
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
