// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scratch elaboration for the six remaining backward laws at `RedWStep`.

use super::*;
use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};

/// `redLet` and the four `redRec*` at `RedWStep (sort 0)`. SCRATCH.
///
/// Four dependency vecs register first, and they are also the CONTROL: all five
/// arms here are one-line lifts, so if the type-blind sources or
/// `redw_acc_to_sort` fail to register, nothing below is a statement about
/// `RedW` at all.
#[test]
fn candmodel_whnf_backward_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for (name, src) in Specification::redrecgen_probe_sources() {
            spec.add_recursive_def(&src, "redRec* type-blind probe")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::redlet_blind_probe_sources() {
            spec.add_recursive_def(&src, "redLet type-blind probe")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::candmodel_whnf_indexed_sources() {
            spec.add_recursive_def(&src, "CandModel whnf-indexed candidate")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        for (name, src) in Specification::candmodel_whnf_typestep_quantified_sources() {
            spec.add_recursive_def(&src, "CandModel whnf quantified transports")
                .unwrap_or_else(|e| panic!("dependency {name} must register first: {e}"));
        }
        let mut passed: Vec<String> = Vec::new();
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::candmodel_whnf_backward_sources() {
            parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "CandModel whnf backward laws") {
                Ok(()) => {
                    eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64());
                    passed.push(name);
                }
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s: {e}", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        eprintln!("BACKWARD-VERDICT: {} passed {:?}", passed.len(), passed);
        assert!(
            failures.is_empty(),
            "whnf-indexed backward-law failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}
