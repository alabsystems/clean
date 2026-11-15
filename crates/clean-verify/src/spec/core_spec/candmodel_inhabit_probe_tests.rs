// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The type-blind `CandModel` probe: a MAP of which laws hold, not a gate.

use super::*;
use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};

#[test]
fn candmodel_blind_probe_sources_parse() {
    for (name, src) in Specification::candmodel_blind_probe_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("{name} does not parse: {e}\n{src}"));
    }
}

/// Registers each law separately and PRINTS the verdict per law. It does not
/// assert that they all hold — most of the value is in the ones that do not,
/// and `pi_elim` is expected to fail (Ω refutes it at a type-blind candidate).
///
/// What it DOES assert is the control: if `pi_elim` ever elaborates here, the
/// probe is measuring nothing and the reader must be told loudly rather than
/// shown a green tick.
#[test]
fn candmodel_blind_probe_maps_which_laws_hold() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        if spec
            .env()
            .get_const(&clean_kernel::Name::from_string("probe_blind_cr1"))
            .is_some()
        {
            return;
        }
        let mut held: Vec<String> = Vec::new();
        let mut refused: Vec<(String, String)> = Vec::new();
        for (name, src) in Specification::candmodel_blind_probe_sources() {
            eprintln!("PROBING {name}");
            match spec.add_recursive_def(&src, "candmodel type-blind probe") {
                Ok(()) => {
                    eprintln!("  HOLDS   {name}");
                    held.push(name);
                }
                Err(e) => {
                    let msg = format!("{e}");
                    eprintln!(
                        "  REFUSED {name}: {}",
                        msg.chars().take(160).collect::<String>()
                    );
                    refused.push((name, msg));
                }
            }
        }
        eprintln!(
            "\nTYPE-BLIND CANDMODEL MAP: {} hold, {} refused",
            held.len(),
            refused.len()
        );
        eprintln!("  hold:    {held:?}");
        eprintln!(
            "  refused: {:?}",
            refused.iter().map(|(n, _)| n).collect::<Vec<_>>()
        );

        assert!(
            refused.iter().any(|(n, _)| n == "probe_blind_pi_elim"),
            "CONTROL FAILED: pi_elim must NOT hold at a type-blind candidate — \
             Omega refutes `whnf_acc f -> whnf_acc a -> whnf_acc (app f a)`. \
             If it elaborated, this probe is measuring nothing."
        );
    });
}
