// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scratch elaboration for the step-transfer arm lemmas.

use super::*;
use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};

#[test]
fn wh3_to_wh_arm_sources_parse() {
    for (src, _) in Specification::wh3_to_wh_arm_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("arm source does not parse: {e}\n{src}"));
    }
}

/// ITERATION TOOL. Appends every arm to an already-built spec and reports each
/// failure with its own message — so a rejection names the ARM, which is the
/// whole reason this induction is being built arm by arm.
#[test]
fn wh3_to_wh_arms_elaborate() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        // Wired-state guard: once the stage lands in `bundles.rs` the spec
        // already carries these, and re-registering would fail on the duplicate
        // name rather than on anything about the terms.
        if spec
            .env()
            .get_const(&clean_kernel::Name::from_string(
                "wh3_const_stuck_gives_none",
            ))
            .is_some()
        {
            return;
        }
        let mut failures: Vec<String> = Vec::new();
        for (src, _desc) in Specification::wh3_to_wh_arm_sources() {
            let name = src
                .split_whitespace()
                .nth(1)
                .unwrap_or("<unnamed>")
                .to_string();
            // Printed BEFORE the attempt and BEFORE its own result, under
            // --nocapture, so a run that is killed or that hangs still says
            // which constant it was on. A row buffered to the end is a row lost
            // the first time a probe stalls; that has already cost one run here.
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            let outcome = spec.add_recursive_def(&src, "wh3-to-wh arm scratch");
            let secs = t0.elapsed().as_secs_f64();
            match outcome {
                Ok(()) => eprintln!("  ok   {name} {secs:.1}s"),
                Err(e) => {
                    eprintln!("  FAIL {name} {secs:.1}s");
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "step-transfer arm failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}
