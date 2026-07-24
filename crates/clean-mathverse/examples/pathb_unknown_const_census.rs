// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Path-B harness frequency census** (NOT a production path): run the
//! `isabelle-lean-goal` translation harness over a candidate serial pool and emit
//! the ranked **unknown-const backlog** — the specific Isabelle constants the
//! pattern library does not yet render, ordered by decline frequency. This turns
//! the opaque "68% unknown-const" taxonomy bucket
//! ([`docs/analysis/zproof-pathb-batch5.md`] §3b) into a concrete, prioritized
//! fragment backlog.
//!
//! Reads only via the corpus `.idx` seek-read (pure reads; no verify lock, no
//! kernel, no replay); parses ONLY each candidate line's `name` + `prop` (a
//! bounded prefix — serde skips the heavy proof), then drives the exact same
//! [`clean_mathverse::hol::isabelle_lean_goal::translate_prop`] path the batch-prep
//! CLI uses, so the census matches the CLI's emitted `census.json` byte-for-byte.
//!
//! Usage:
//!   cargo run -q --release --example pathb_unknown_const_census -p clean-mathverse -- \
//!     <corpus.jsonl> <serials.txt> [census_out.json]
//!
//! `serials.txt`: one integer serial per line (a leading `s` is tolerated).
//! Prints the census JSON to stdout (or to `census_out.json` when given) and a
//! human-readable summary table to stderr.

use std::collections::BTreeSet;
use std::io::{Read as _, Seek as _};
use std::path::Path;

use clean_mathverse::hol::isabelle_index::{index_path, load_index, CorpusIndex, IndexEntry};
use clean_mathverse::hol::isabelle_lean_goal::batch::{prepare, PreparedGoal};
use clean_mathverse::hol::isabelle_lean_goal::census::Census;
use clean_mathverse::hol::isabelle_pure::IsaTerm;
use serde::Deserialize as _;

/// Bounded per-line read: `name` and `prop` are early in the line, so a prefix
/// suffices and bounds memory even for multi-MB proof trees we never parse.
const PREFIX_CAP: usize = 8 * 1024 * 1024;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if !(3..=4).contains(&args.len()) {
        eprintln!(
            "usage: pathb_unknown_const_census <corpus.jsonl> <serials.txt> [census_out.json]"
        );
        std::process::exit(2);
    }
    let corpus = Path::new(&args[1]);
    let serials: BTreeSet<i64> = std::fs::read_to_string(&args[2])
        .expect("read serials file")
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .filter_map(|l| l.strip_prefix('s').unwrap_or(l).parse::<i64>().ok())
        .collect();

    let index: CorpusIndex = load_index(&index_path(corpus)).expect("load .idx");
    let mut f = std::fs::File::open(corpus).expect("open corpus");

    let mut goals: Vec<PreparedGoal> = Vec::with_capacity(serials.len());
    let mut n_missing = 0usize;
    for e in &index.entries {
        if !serials.contains(&e.serial) {
            continue;
        }
        match read_name_prop(&mut f, e) {
            Some((name, prop)) => goals.push(prepare(
                format!("s{}", e.serial),
                Some(e.serial),
                &name,
                &prop,
            )),
            None => n_missing += 1,
        }
    }

    // Optional faithfulness spot-check dump: `PATHB_SUPPORTED_TSV=<path>` writes
    // one `serial \t isabelle-name \t signature` row per supported goal, for
    // statement-for-statement comparison against the Isabelle `prop`.
    if let Ok(path) = std::env::var("PATHB_SUPPORTED_TSV") {
        use clean_mathverse::hol::isabelle_lean_goal::types::LeanGoal;
        let mut out = String::new();
        for g in &goals {
            if let LeanGoal::Supported(sg) = &g.goal {
                let sig = sg.signature.replace('\n', " ");
                out.push_str(&format!("{}\t{}\t{}\n", g.id, g.isabelle, sig));
            }
        }
        std::fs::write(&path, out).expect("write supported tsv");
        eprintln!("supported goals dumped to {path}");
    }

    let census = Census::from_goals(&goals);

    // Human-readable summary to stderr.
    eprintln!(
        "PATH-B CENSUS: {} candidates -> {} supported, {} unsupported ({:.2}% coverage); prop-extract-failures={}",
        census.total, census.supported, census.unsupported, census.coverage_pct, n_missing
    );
    eprintln!("--- decline taxonomy (by kind) ---");
    for (kind, count) in &census.reason_histogram {
        eprintln!("  {count:>6}  {kind}");
    }
    eprintln!("--- top 40 unknown-const backlog (rank by frequency) ---");
    for (i, e) in census.unknown_const_rank.iter().take(40).enumerate() {
        eprintln!(
            "  {:>3}. {:>5}  {}  (e.g. s{})",
            i + 1,
            e.count,
            e.name,
            e.example_serial.unwrap_or(-1)
        );
    }
    eprintln!("--- per-family support ---");
    for (fam, s) in &census.per_family {
        let pct = if s.total == 0 {
            0.0
        } else {
            100.0 * s.supported as f64 / s.total as f64
        };
        eprintln!("  {:>5}/{:<5} {:>5.1}%  {fam}", s.supported, s.total, pct);
    }

    // Machine-readable census JSON to stdout or the given file.
    let json = serde_json::to_string_pretty(&census).expect("serialize census");
    if let Some(out) = args.get(3) {
        std::fs::write(out, json + "\n").expect("write census json");
        eprintln!("census written to {out}");
    } else {
        println!("{json}");
    }
}

/// Seek to the line, read a bounded prefix, and parse just the `name` + `prop`.
fn read_name_prop(f: &mut std::fs::File, e: &IndexEntry) -> Option<(String, IsaTerm)> {
    f.seek(std::io::SeekFrom::Start(e.offset)).ok()?;
    let cap = (e.len as usize).min(PREFIX_CAP);
    let mut buf = vec![0u8; cap];
    let n = read_full(f, &mut buf)?;
    buf.truncate(n);
    let s = String::from_utf8_lossy(&buf);
    let name = extract_name(&s)?;
    let sub = extract_prop_object(&s)?;
    let mut de = serde_json::Deserializer::from_str(sub);
    de.disable_recursion_limit();
    let prop = IsaTerm::deserialize(&mut de).ok()?;
    Some((name, prop))
}

fn read_full(f: &mut std::fs::File, buf: &mut [u8]) -> Option<usize> {
    let mut total = 0;
    while total < buf.len() {
        match f.read(&mut buf[total..]) {
            Ok(0) => break,
            Ok(k) => total += k,
            Err(_) => return None,
        }
    }
    Some(total)
}

/// Extract the (JSON-unescaped-enough) value of `"name":"…"`. The Isabelle names
/// in this corpus carry no escaped characters, so a plain scan to the closing
/// unescaped quote is exact.
fn extract_name(line: &str) -> Option<String> {
    let key = "\"name\":\"";
    let at = line.find(key)? + key.len();
    let rest = &line[at..];
    let mut out = String::new();
    let mut esc = false;
    for c in rest.chars() {
        if esc {
            out.push(c);
            esc = false;
        } else if c == '\\' {
            esc = true;
        } else if c == '"' {
            return Some(out);
        } else {
            out.push(c);
        }
    }
    None
}

/// Extract the substring of the JSON `"prop":{...}` value by brace-matching
/// (quote/escape aware). Returns `None` if the prop object is not closed inside
/// the prefix (pathologically large statement — reported, not silently dropped).
fn extract_prop_object(line: &str) -> Option<&str> {
    let key = "\"prop\":";
    let at = line.find(key)? + key.len();
    let rest = &line[at..];
    let start = rest.find('{')?;
    let bytes = rest.as_bytes();
    let mut depth = 0i32;
    let mut in_str = false;
    let mut esc = false;
    for (i, &b) in bytes.iter().enumerate().skip(start) {
        if in_str {
            if esc {
                esc = false;
            } else if b == b'\\' {
                esc = true;
            } else if b == b'"' {
                in_str = false;
            }
        } else if b == b'"' {
            in_str = true;
        } else if b == b'{' {
            depth += 1;
        } else if b == b'}' {
            depth -= 1;
            if depth == 0 {
                return Some(&rest[start..=i]);
            }
        }
    }
    None
}
