// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scratch elaboration for the generic-recursor spine probe.

use super::*;
use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};

#[test]
fn redrecgen_probe_sources_parse() {
    for (name, src) in Specification::redrecgen_probe_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
    }
}

/// The probe is NOT wired and must not be, so there is no wired-state guard
/// here: this test always registers, and a green always means it reached its
/// assertion.
#[test]
fn redrecgen_probe_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::redrecgen_probe_sources() {
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "redRecGen type-blind probe") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "redRecGen probe failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}
