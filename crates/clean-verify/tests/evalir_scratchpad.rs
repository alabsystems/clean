// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **A fast scratchpad, scoped to the EvalIR bundle.**
//!
//! Same contract as `spec_scratchpad`: candidates in a JSON file are elaborated
//! and kernel-checked one at a time against one spec build, each reported
//! independently so a single run diagnoses the whole chain.
//!
//! The difference is the spec it builds. `spec_scratchpad` uses the FULL
//! specification, which costs roughly half an hour per cycle. This one uses
//! `CoreSpecBundle::EvalIr` — foundation types plus the EvalIR stages — which
//! is a fraction of that.
//!
//! ## Why a second one is worth having
//!
//! Crystal A4's remaining work is machine-shape reasoning: what configuration
//! the IR machine is in after *k* steps, what the caller's frame looks like once
//! a callee has been pushed, which instruction bound which SSA id. That work is
//! iterative — an off-by-one in a frame or a step count is discovered by trying
//! it — and at full-spec cost each attempt is a half-hour. None of it needs
//! `KExpr`, the reduction substrate, or anything else the full spec carries.
//!
//! What is NOT available here: `Level`, and therefore `EncodesLevelArc`
//! (`add_eval_ir_repr`) and `ir_lz_cost` (`add_eval_ir_cost`, which needs
//! `level_is_zero`). Candidates mentioning those must go through the full
//! `spec_scratchpad`. Everything reachable from `ir_steps`, `ir_step`,
//! `ir_lz_module` and the activation leaves is fair game.
//!
//! This is a development tool, not a gate. An absent or empty scratch file
//! passes trivially and must never fail a clean tree.
//!
//! ```text
//! cargo test --offline -p clean-verify --test evalir_scratchpad -- --nocapture
//! ```

use std::path::PathBuf;

use clean_verify::test_utils::build_eval_ir_spec_with_stack;

fn scratch_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../data/spec_scratch_evalir.json")
}

/// Try every candidate against one EvalIR spec build; report each independently.
#[test]
fn evalir_scratchpad_candidates_elaborate() {
    let path = scratch_path();
    let raw = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(_) => {
            eprintln!(
                "evalir scratchpad: no {} — nothing to check",
                path.display()
            );
            return;
        }
    };
    let items: Vec<serde_json::Value> = match serde_json::from_str(&raw) {
        Ok(v) => v,
        Err(e) => panic!(
            "evalir scratchpad: {} is not valid JSON: {e}",
            path.display()
        ),
    };
    if items.is_empty() {
        eprintln!("evalir scratchpad: empty — nothing to check");
        return;
    }

    let mut spec = build_eval_ir_spec_with_stack();
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
        let desc = "evalir scratchpad candidate — not a registered spec declaration";
        let result = match kind {
            "inductive" => spec.add_inductive(source, desc),
            _ => spec.add_recursive_def(source, desc),
        };
        match result {
            Ok(()) => {
                passed += 1;
                eprintln!("evalir scratchpad PASS  [{idx}] {name}");
            }
            Err(e) => {
                eprintln!("evalir scratchpad FAIL  [{idx}] {name}\n    {e}");
                failures.push(format!("[{idx}] {name}: {e}"));
            }
        }
    }

    eprintln!(
        "evalir scratchpad: {passed}/{} candidates elaborated",
        items.len()
    );
    assert!(
        failures.is_empty(),
        "evalir scratchpad: {} candidate(s) failed to elaborate:\n  {}\n\n\
         Each is reported above with its own error, and the run did NOT stop at the first \
         failure. If a candidate fails with an unknown identifier for `Level`, `level_is_zero`, \
         `EncodesLevelArc` or `ir_lz_cost`, that is expected — this bundle does not carry them; \
         move that candidate to the full `spec_scratchpad`.",
        failures.len(),
        failures.join("\n  ")
    );
}
