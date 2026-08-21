// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Falsification for the COST half of GAP 2.**
//!
//! The existing `crystal_a3_mutation_cost_floor_is_real` asserts that `fuel_out`
//! is rejected at a **hardcoded** probe (`fuel=6`, `tag=2`). That shows the
//! kernel executes the obligation; it does not show that the *gate* responds to
//! the cost it measures — and until 2026-08-20 it could not have, because
//! `is_green()` never consulted cost and `cost_is_uniform()` was called once in
//! the whole repository, inside an `eprintln!`.
//!
//! The two mutations here perturb the MEASURED quantity and require the verdict
//! to move:
//!
//! * a wrong harness overhead — the constant subtracted from trust-ir's step
//!   count — shifts every row equally, stays perfectly *uniform*, and must still
//!   go RED against the declared offset;
//! * a single row whose Clean fuel threshold moves must go RED as a divergence.
//!
//! Between them they cover the two ways a cost correspondence can be wrong, and
//! the first is the one uniformity alone cannot see.

use clean_verify::ir_semdiff::{summarize, ChainReport, CostVerdict};
use clean_verify::spec::Specification;
use clean_verify::test_utils::build_eval_ir_spec_with_stack;

use super::chains::{chains, Chain};
use super::measure_with;

/// The cheapest chain to measure twice: six inputs, `Exact` enum model, E3 present.
fn subject() -> Chain {
    chains()
        .into_iter()
        .find(|c| c.name == "has_cubical_layer")
        .expect("the has_cubical_layer chain is registered")
}

fn measure(prefix: &str, bias: i64, chain: &Chain) -> ChainReport {
    // A fresh specification per measurement: `register_module` would refuse to
    // register the same module twice into one. The builder is cached per
    // process, so this is a clone rather than a rebuild.
    let mut spec: Specification = build_eval_ir_spec_with_stack();
    measure_with(&mut spec, chain, prefix, bias)
}

/// **Mutation — a wrong harness overhead must turn the gate RED.**
///
/// This is the mutation the panel asked for and the one the old battery lacked:
/// it perturbs the measurement, not a probe. `harness_steps` is subtracted from
/// trust-ir's step count, so a wrong value shifts every row by the same amount.
/// The offsets stay *uniform* — which is exactly why uniformity alone was never
/// a gate — and only the comparison against the chain's declared
/// `expected_cost_offset` refuses it.
#[test]
fn crystal_a3_mutation_a_wrong_harness_overhead_turns_the_gate_red() {
    let chain = subject();

    let truth = measure("a3ct", 0, &chain);
    assert_eq!(
        truth.cost_verdict(),
        CostVerdict::Uniform(chain.expected_cost_offset),
        "the unperturbed chain must measure its declared offset: {}",
        truth.summary()
    );
    assert!(truth.is_green(), "{}", truth.summary());

    // Subtract one step too many. Nothing else changes.
    let mutated = measure("a3cm", 1, &chain);
    assert_eq!(
        mutated.agreed, truth.agreed,
        "the perturbation must not touch the VALUE half — otherwise this mutation would be \
         falsifying value agreement again rather than cost"
    );
    assert_eq!(
        mutated.disagreed, 0,
        "every value still agrees; only the cost moved"
    );
    assert!(
        mutated.cost_is_uniform(),
        "THE MUTATION IS NOT THE INTERESTING ONE: a constant overhead error must remain \
         UNIFORM. If it is not uniform, uniformity alone would have caught it and this test \
         proves less than it claims. Got {:?}",
        mutated.cost_verdict()
    );
    assert_eq!(
        mutated.cost_verdict(),
        CostVerdict::Uniform(chain.expected_cost_offset + 1),
        "one step less subtracted from trust-ir's count raises clean-minus-trust by exactly one"
    );
    assert!(
        !mutated.is_green(),
        "THE COST HALF IS STILL TELEMETRY: a wrong harness overhead shifted the measured offset \
         off its pin and the chain stayed green. {}",
        mutated.summary()
    );
    eprintln!(
        "cost mutation 1 (wrong harness overhead) correctly RED: {:?} vs pinned {:+}",
        mutated.cost_verdict(),
        chain.expected_cost_offset
    );
}

/// **Mutation — one row's cost moving must turn the gate RED.**
///
/// The other failure direction: a body that reaches the right answer by a
/// different route on *one* input. Applied to the rows the gate really measured,
/// so it cannot pass by measuring something else.
#[test]
fn crystal_a3_mutation_a_single_divergent_row_turns_the_gate_red() {
    let chain = subject();
    let truth = measure("a3cd", 0, &chain);
    assert!(truth.is_green(), "{}", truth.summary());

    let mut rows = truth.rows.clone();
    let first = rows
        .first_mut()
        .expect("the chain measured at least one row");
    let (value, fuel) = first
        .clean
        .clone()
        .expect("the Clean leg answered on every row");
    let bumped = fuel.expect("the Clean leg pinned a threshold") + 1;
    first.clean = Some((value, Some(bumped)));

    let mutated = summarize(
        chain.name,
        chain.enum_model,
        chain.total_domain,
        chain.expected_cost_offset,
        rows,
    );
    assert_eq!(
        mutated.disagreed, 0,
        "the values are untouched: this is a pure cost divergence"
    );
    assert_eq!(
        mutated.cost_verdict(),
        CostVerdict::Divergent,
        "two different offsets in one chain is a divergence, not a uniform cost"
    );
    assert!(
        !mutated.is_green(),
        "THE COST HALF IS STILL TELEMETRY: one row took a different number of steps and the \
         chain stayed green. {}",
        mutated.summary()
    );
    eprintln!(
        "cost mutation 2 (one divergent row) correctly RED: {:?}",
        mutated.cost_verdict()
    );
}
