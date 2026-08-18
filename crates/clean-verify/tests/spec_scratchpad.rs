// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The scratchpad — validate a CHAIN of candidate declarations in ONE spec build.
//!
//! # Why this exists
//!
//! Registering a declaration in `core_spec` and running `axiom_ratchet` costs
//! ~26 minutes and tells you about **one** declaration. Across the def-eq
//! completeness program that has been the dominant cost by a wide margin: every
//! rejection so far has been in term *assembly* — recursor arity, binder
//! precedence, variable capture, universe level, paren balance, registration
//! order — and not one has been in the mathematics. Half-hour feedback on
//! syntax-level mistakes is the wrong trade.
//!
//! `Specification::add_recursive_def` and friends are `pub` and return
//! `Result`, so the spec can be built **once** and then used as a target for many
//! candidates. Each success is registered, so later candidates may depend on
//! earlier ones: a whole chain of bricks validates per build instead of one.
//!
//! # What this CANNOT see — read before trusting a PASS
//!
//! Candidates are appended to an **already-built** spec, so every dependency is
//! trivially in scope. **Registration order is invisible here.** A candidate can
//! pass the scratchpad and still break the spec build when moved into
//! `core_spec`, if it is placed before something it depends on — sequential
//! registration fails at the first such declaration and leaves everything after
//! it unchecked.
//!
//! That is not hypothetical: it happened, it reached a commit, and it broke
//! `main` (`a95c1106a`, repaired in `cb72aed9c`). Fast iteration and registration
//! order are ORTHOGONAL checks.
//!
//! **`axiom_ratchet` green before push. No exceptions, however good this tool is
//! at its own job.**
//!
//! # Use
//!
//! Put candidates in `data/spec_scratch.json` as `[{"kind","name","source"}]`,
//! with `kind` one of `def` / `inductive`, then:
//!
//! ```sh
//! cargo test --offline -p clean-verify --test spec_scratchpad -- --nocapture
//! ```
//!
//! Every candidate is reported PASS or FAIL **with its elaboration error**, and
//! the run does not stop at the first failure — so one build diagnoses the whole
//! chain. When a candidate is right, move it into `core_spec` for real.
//!
//! An absent or empty scratch file passes trivially: this is a development tool,
//! not a gate, and it must never fail a clean tree.

use std::path::PathBuf;

use clean_verify::test_utils::build_spec_with_stack;

fn scratch_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../data/spec_scratch.json")
}

/// Try every candidate against one spec build; report each independently.
#[test]
fn scratchpad_candidates_elaborate() {
    let path = scratch_path();
    let raw = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(_) => {
            eprintln!("scratchpad: no {} — nothing to check", path.display());
            return;
        }
    };
    let items: Vec<serde_json::Value> = match serde_json::from_str(&raw) {
        Ok(v) => v,
        Err(e) => panic!("scratchpad: {} is not valid JSON: {e}", path.display()),
    };
    if items.is_empty() {
        eprintln!("scratchpad: empty — nothing to check");
        return;
    }

    let mut spec = build_spec_with_stack();
    let mut failures: Vec<String> = Vec::new();
    let mut passed = 0usize;

    for (idx, item) in items.iter().enumerate() {
        let name = item["name"].as_str().unwrap_or("<unnamed>");
        let kind = item["kind"].as_str().unwrap_or("def");
        let source = match item["source"].as_str() {
            Some(s) => s,
            None => {
                failures.push(format!("[{idx}] {name}: missing `source`"));
                continue;
            }
        };
        let desc = "scratchpad candidate — not a registered spec declaration";
        // Per-candidate wall clock, printed with the verdict — the same field
        // `evalir_scratchpad` has carried since 2026-08-13, and for the same
        // reason: a run that prints only PASS/FAIL cannot tell "slow" from
        // "hung" from "cheap", and the three want different responses. Without
        // it, a 2026-08-15 run reported thirteen passes over 273 s and could
        // say nothing about which declaration spent them.
        let started = std::time::Instant::now();
        let result = match kind {
            "inductive" => spec.add_inductive(source, desc),
            _ => spec.add_recursive_def(source, desc),
        };
        let secs = started.elapsed().as_secs_f64();
        match result {
            Ok(()) => {
                passed += 1;
                eprintln!("scratchpad PASS  [{idx}] {secs:8.3}s {name}");
            }
            Err(e) => {
                eprintln!("scratchpad FAIL  [{idx}] {secs:8.3}s {name}\n    {e}");
                failures.push(format!("[{idx}] {name}: {e}"));
            }
        }
    }

    eprintln!("scratchpad: {passed}/{} candidates elaborated", items.len());
    assert!(
        failures.is_empty(),
        "scratchpad: {} candidate(s) failed to elaborate:\n  {}\n\n\
         Each is reported above with its own error, and the run did NOT stop at the first \
         failure — so this one build diagnoses the whole chain. Fix them here, where the only \
         cost is a rerun, rather than one per 26-minute axiom_ratchet cycle.",
        failures.len(),
        failures.join("\n  ")
    );
}
