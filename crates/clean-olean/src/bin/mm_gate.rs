// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DEPENDENCY-CLOSURE GATE for the two-pass parallel Metamath verifier.
//!
//! The two-pass verifier (`mm_verify_range`) checks each proof against a PASS-1
//! environment in which EVERY theorem's type is registered as an axiom. So if a
//! theorem `D` is skipped (its own proof did not verify), a dependent `T` that
//! cites `D` can still type-check against `D`'s pass-1 AXIOM type — `T` would be
//! reported verified even though it rests on an unproven `D`. The sequential
//! verifier never does this (it only registers `D` after `D` verified).
//!
//! This gate restores byte-for-byte equality with the sequential result: it
//! removes any verified theorem whose transitive `$p`-theorem dependency closure
//! is not fully verified. A theorem survives iff EVERY `$p` theorem it cites is
//! also verified (`$a` axioms and `$f`/`$e` hypotheses are the trusted/local base
//! and are not dependencies in this sense). Iterated to a fixpoint, the surviving
//! set equals exactly the set the sequential verifier would accept — so the
//! two-pass parallel output carries the SAME KernelVerified trust as sequential.
//!
//! Usage: `mm_gate <path.mm> [verified-labels-file]`
//!   Verified labels are read from the file (or stdin if omitted); lines may be
//!   bare labels or the `V <label>` form emitted by `mm_verify_range`. Prints the
//!   gated (closure) label set, one per line, sorted.

use std::collections::{HashMap, HashSet};
use std::io::Read;
use std::process::ExitCode;

use clean_olean::metamath::{parse_database_file, resolve_database, Proof, ResolvedStatement};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: mm_gate <path.mm> [verified-labels-file]  (else stdin)");
        return ExitCode::FAILURE;
    }
    let db = match parse_database_file(std::path::Path::new(&args[1])) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("parse error: {e}");
            return ExitCode::FAILURE;
        }
    };
    let resolved = match resolve_database(&db) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("resolve error: {e}");
            return ExitCode::FAILURE;
        }
    };

    // All `$p` (provable) theorem labels, and each provable's `$p`-theorem deps
    // (the cited labels that are themselves provable theorems).
    let mut provable: HashSet<String> = HashSet::new();
    let mut proof_labels: HashMap<String, Vec<String>> = HashMap::new();
    for stmt in &resolved.statements {
        if let ResolvedStatement::Assertion(a) = stmt {
            if a.kind == "provable" {
                provable.insert(a.label.clone());
                let labels: Vec<String> = match &a.proof {
                    Some(Proof::Uncompressed(ls)) => ls.clone(),
                    Some(Proof::Compressed(c)) => c.labels.clone(),
                    None => Vec::new(),
                };
                proof_labels.insert(a.label.clone(), labels);
            }
        }
    }
    let deps: HashMap<String, Vec<String>> = proof_labels
        .iter()
        .map(|(t, ls)| {
            let d: Vec<String> = ls
                .iter()
                .filter(|l| provable.contains(*l))
                .cloned()
                .collect();
            (t.clone(), d)
        })
        .collect();

    // Read the verified set (file arg or stdin); accept bare labels or `V <label>`.
    let raw = if args.len() >= 3 {
        match std::fs::read_to_string(&args[2]) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("read error {}: {e}", args[2]);
                return ExitCode::FAILURE;
            }
        }
    } else {
        let mut s = String::new();
        if std::io::stdin().read_to_string(&mut s).is_err() {
            eprintln!("stdin read error");
            return ExitCode::FAILURE;
        }
        s
    };
    let mut verified: HashSet<String> = raw
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with("VERIFIED_COUNT"))
        .map(|l| l.strip_prefix("V ").unwrap_or(l).trim().to_string())
        .filter(|l| !l.is_empty())
        .collect();
    let before = verified.len();

    // Fixpoint dependency-closure: drop any verified theorem with an unverified
    // `$p`-dependency; a removal may cascade to its dependents.
    loop {
        let removed: Vec<String> = verified
            .iter()
            .filter(|t| {
                deps.get(*t)
                    .map(|ds| ds.iter().any(|d| !verified.contains(d)))
                    .unwrap_or(false)
            })
            .cloned()
            .collect();
        if removed.is_empty() {
            break;
        }
        for r in removed {
            verified.remove(&r);
        }
    }

    eprintln!(
        "=== gate: {before} verified -> {} after dependency-closure ({} removed as resting on unverified $p-deps) ===",
        verified.len(),
        before - verified.len()
    );
    let mut out: Vec<&String> = verified.iter().collect();
    out.sort();
    for l in out {
        println!("{l}");
    }
    ExitCode::SUCCESS
}
