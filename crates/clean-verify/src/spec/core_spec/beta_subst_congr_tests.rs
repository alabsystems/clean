// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scratch elaboration for step substitutivity.

use super::*;
use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};

#[test]
fn beta_subst_congr_sources_parse() {
    let sources = Specification::beta_subst_congr_sources()
        .into_iter()
        .chain(Specification::redlet_blind_probe_sources());
    for (name, src) in sources {
        parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
    }
}

/// Registers the three constants against a built spec, printing each verdict
/// before its result so a killed run still says where it was.
///
/// This also settles the open identification recorded in
/// `designs/2026-09-18-is-candmodel-uninhabited.md`: the two `forall_congr_*`
/// arms are written exactly as the `pi` arms, so they elaborate iff
/// `KExpr.forall_` is a `pi` alias rather than a tenth constructor.
#[test]
fn beta_subst_congr_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        if spec
            .env()
            // The PROBE's own name, not a wired one. This guard used to name
            // `beta_reduces_psubst_congr`; the moment that lemma was wired the
            // guard began returning early and this test silently elaborated
            // NOTHING while still reporting ok — a test passing by never
            // reaching its assertion, which is the failure this repo has a
            // standing rule about.
            .get_const(&clean_kernel::Name::from_string("redlet_blind"))
            .is_some()
        {
            return;
        }
        // The general lemmas are WIRED now, so the spec already carries them and
        // the guard above returns early. What this still elaborates is the
        // type-blind candidate probe, which is not wired and must not be.
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in Specification::redlet_blind_probe_sources() {
            eprintln!("REGISTERING {name}");
            let t0 = std::time::Instant::now();
            match spec.add_recursive_def(&src, "step substitutivity") {
                Ok(()) => eprintln!("  ok   {name} {:.1}s", t0.elapsed().as_secs_f64()),
                Err(e) => {
                    eprintln!("  FAIL {name} {:.1}s", t0.elapsed().as_secs_f64());
                    failures.push(format!("{name}: {e}"));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "step substitutivity failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}
