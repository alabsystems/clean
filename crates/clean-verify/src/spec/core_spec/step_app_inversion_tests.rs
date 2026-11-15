// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scratch elaboration for the application step inversion.

use super::*;
use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};

#[test]
fn step_app_inversion_sources_parse() {
    for (name, src) in Specification::step_app_inversion_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
    }
}

/// ITERATION TOOL. The guard names a constant from the set this test registers.
#[test]
fn step_app_inversion_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        // WIRED-STATE BRANCH, and deliberately not an early `return`.
        // A bare return is a SELF-SKIP: this test would report ok forever if the
        // stage were removed from `bundles.rs`, which is the one regression the
        // wiring is supposed to protect. So assert the invariant instead -- when
        // the spec carries them, it must carry ALL of them.
        let wired = Specification::step_app_inversion_sources()
            .iter()
            .any(|(n, _)| {
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(n))
                    .is_some()
            });
        if wired {
            for (name, _) in Specification::step_app_inversion_sources() {
                assert!(
                    spec.env()
                        .get_const(&clean_kernel::Name::from_string(&name))
                        .is_some(),
                    "{name} is missing while its siblings are wired -- the stage is \
                     registering only part of its table"
                );
            }
        } else {
            let mut failures: Vec<String> = Vec::new();
            for (name, src) in Specification::step_app_inversion_sources() {
                eprintln!("REGISTERING {name}");
                let t0 = std::time::Instant::now();
                match spec.add_recursive_def(&src, "application step inversion") {
                    Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                    Err(e) => {
                        eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                        failures.push(format!("{name}: {e}"));
                    }
                }
            }
            assert!(
                failures.is_empty(),
                "application step inversion failures ({}):\n{}",
                failures.len(),
                failures.join("\n")
            );
        }
    });
}
