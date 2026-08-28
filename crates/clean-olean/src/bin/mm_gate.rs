// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DEPENDENCY-CLOSURE GATE for the two-pass parallel Metamath verifier.
//!
//! The two-pass verifier (`mm_verify_range`) checks each proof against a PASS-1
//! environment in which EVERY theorem's type is registered as an axiom. That makes
//! the raw union of the workers' verified labels a STRICT SUPERSET of what the
//! sequential verifier accepts, in two ways, and this gate removes both:
//!
//! 1. A theorem `D` that never verified still has a pass-1 AXIOM type, so a
//!    dependent `T` type-checks against it and is reported verified. Removed
//!    because `D` is not in the verified set.
//! 2. A theorem `D` that verified only on the GROUND fallback is verified but NOT
//!    reusable — the sequential verifier leaves it out of its reuse cache and skips
//!    every dependent. Two-pass instead leaves `D`'s cheap pass-1 *schematic* type
//!    standing in every worker that does not own `D`, and `T` type-checks against
//!    that. Removed because `D` is marked `G` (ground-only) in the input stream.
//!    This is issue R1-MM; rule 2 is what makes the surviving set EQUAL the
//!    sequential set rather than a superset of it.
//!
//! A theorem survives iff EVERY `$p` theorem it cites is verified AND citable
//! (`$a` axioms and `$f`/`$e` hypotheses are the trusted/local base and are not
//! dependencies in this sense), iterated to a fixpoint.
//!
//! The gate logic itself lives in
//! [`clean_olean::metamath::dependency_closure_gate`] so it is exercised by the
//! R1-MM property/differential suite (`tests/mm_two_pass_theorem.rs`) rather than
//! only by this binary. Read that module's docs for the precise statement of what
//! the gate does and does NOT establish, and
//! `docs/issues/2026-08-23-r1-mm-two-pass-theorem.md` for the history.
//!
//! Usage: `mm_gate [--allow-unmarked] <path.mm> [verified-labels-file]`
//!   Verified labels are read from the file (or stdin if omitted). The stream MUST
//!   carry the `VERIFIED_FORMAT 2` stamp that `mm_verify_range` writes; without it
//!   the reusability of every label is UNKNOWN and the gate REFUSES the file rather
//!   than guess (guessing "all reusable" is exactly the R1-MM gap). `--allow-unmarked`
//!   proceeds anyway, treating every unmarked label as NON-citable — fail-closed, so
//!   the result under-approximates. Prints the gated (closure) label set, one BARE
//!   label per line, sorted (the format `mm_export_verified` consumes). A label that
//!   is not a `$p` theorem of the given database is dropped, not passed through.

use std::io::Read;
use std::process::ExitCode;

use clean_olean::metamath::{
    dependency_closure_gate, parse_database_file, parse_verified_labels, resolve_database,
    VERIFIED_FORMAT_HEADER,
};

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().collect();
    let allow_unmarked = argv.iter().any(|a| a == "--allow-unmarked");
    let args: Vec<&String> = argv
        .iter()
        .enumerate()
        .filter(|(i, a)| *i == 0 || !a.starts_with("--"))
        .map(|(_, a)| a)
        .collect();
    if args.len() < 2 {
        eprintln!(
            "usage: mm_gate [--allow-unmarked] <path.mm> [verified-labels-file]  (else stdin)"
        );
        return ExitCode::FAILURE;
    }
    let db = match parse_database_file(std::path::Path::new(args[1])) {
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

    // Read the verified set (file arg or stdin).
    let raw = if args.len() >= 3 {
        match std::fs::read_to_string(args[2]) {
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
    let verified = parse_verified_labels(&raw);
    let before = verified.len();
    let unmarked = verified.unmarked_count();
    let ground_only = verified.ground_only().len();

    // FAIL CLOSED on a pre-R1-MM labels file. Reading it as "everything reusable"
    // is the exact defect this gate was fixed for, so refuse rather than guess.
    if unmarked > 0 && !allow_unmarked {
        eprintln!(
            "REFUSED: {unmarked} of {before} verified labels carry no reusability marking \
             (the stream has no `{VERIFIED_FORMAT_HEADER}` stamp)."
        );
        eprintln!(
            "  The gate cannot tell a schematically-verified dependency from a GROUND-ONLY one \
             without it, and assuming `reusable` re-opens issue R1-MM \
             (docs/issues/2026-08-23-r1-mm-two-pass-theorem.md)."
        );
        eprintln!(
            "  FIX: regenerate the labels with a current `mm_verify_range` (via \
             scripts/mm_two_pass.sh), or pass --allow-unmarked to treat every unmarked label \
             as NON-citable (fail-closed: the result under-approximates)."
        );
        return ExitCode::FAILURE;
    }
    if unmarked > 0 {
        eprintln!(
            "warn: --allow-unmarked — {unmarked} label(s) have unknown reusability and are \
             treated as NON-citable; every dependent of one is dropped."
        );
    }

    let gated = dependency_closure_gate(&resolved, &verified);

    eprintln!(
        "=== gate: {before} verified ({ground_only} ground-only, {unmarked} unmarked) -> {} after \
         dependency-closure ({} removed as resting on an unverified or non-citable $p-dep, or as \
         not a $p of this database) ===",
        gated.len(),
        before - gated.len()
    );
    // `BTreeSet` iteration is already sorted.
    for l in &gated {
        println!("{l}");
    }
    ExitCode::SUCCESS
}
