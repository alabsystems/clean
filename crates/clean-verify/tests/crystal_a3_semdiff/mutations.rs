// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Falsification for the GAP-2 differential. A gate that cannot go red is not
//! evidence.**
//!
//! Every mutation here asserts a REJECTION. Together they establish that the
//! `Eq.refl` obligations the gate submits are genuinely executed by the Clean
//! kernel rather than accepted structurally, that the module under test does not
//! ignore its argument, that the cost measurement is not vacuous, that the
//! payload-elision guard refuses, and that the default edge is pinned.

use clean_verify::ir_semdiff::{
    fuel_out_obligation, payload_is_unread, value_obligation, ArgShape, RunResult,
};
use clean_verify::test_utils::build_eval_ir_spec_with_stack;

use super::chains::chains;
use super::{fixture, register_module};

/// **Mutation 1 — a wrong VALUE must be rejected by the Clean kernel.**
///
/// The single most important negative control: it shows the `Eq.refl`
/// obligations are genuinely executed rather than accepted structurally.
#[test]
fn crystal_a3_mutation_wrong_value_is_rejected() {
    let mut spec = build_eval_ir_spec_with_stack();
    let chain = &chains()[0];
    register_module(&mut spec, chain);

    // Tag 2 is Cubical: the true answer is `true`.
    let good = value_obligation(
        "a3_mut_good",
        chain.clean_module,
        ArgShape::PointerCell,
        6,
        2,
        &RunResult::Bool(true),
    )
    .expect("encodable");
    spec.add_recursive_def(&good, "mutation battery: the correct value")
        .expect("the kernel must accept the value trust-ir measured");

    let bad = value_obligation(
        "a3_mut_bad",
        chain.clean_module,
        ArgShape::PointerCell,
        6,
        2,
        &RunResult::Bool(false),
    )
    .expect("encodable");
    let err = spec
        .add_recursive_def(&bad, "mutation battery: a deliberately wrong value")
        .expect_err(
            "THE GATE IS VACUOUS: the Clean kernel accepted `has_cubical_layer(Cubical) = false`",
        );
    eprintln!("mutation 1 (wrong value) correctly REJECTED: {err}");
}

/// **Mutation 2 — a wrong INPUT TAG must change the answer.**
///
/// Guards against a module that ignores its argument: if the switch were
/// mis-encoded to a constant, every tag would answer alike and the whole
/// differential would agree vacuously.
#[test]
fn crystal_a3_mutation_tag_must_matter() {
    let mut spec = build_eval_ir_spec_with_stack();
    let chain = &chains()[0];
    register_module(&mut spec, chain);

    // Tag 0 (Constructive) is false; asserting `true` there must be rejected.
    let bad = value_obligation(
        "a3_mut_tag",
        chain.clean_module,
        ArgShape::PointerCell,
        6,
        0,
        &RunResult::Bool(true),
    )
    .expect("encodable");
    let err = spec
        .add_recursive_def(&bad, "mutation battery: right value, wrong tag")
        .expect_err(
            "THE MODULE IGNORES ITS ARGUMENT: tag 0 and tag 2 gave the same answer, so the \
             switch is not being executed",
        );
    eprintln!("mutation 2 (tag must matter) correctly REJECTED: {err}");
}

/// **Mutation 3 — the cost floor must be real.**
///
/// One step below the measured threshold the machine must still be RUNNING.
/// If `fuel_out` were accepted at the threshold itself, the "cost" would be
/// meaningless and the sharper half of this gate would be decoration.
#[test]
fn crystal_a3_mutation_cost_floor_is_real() {
    let mut spec = build_eval_ir_spec_with_stack();
    let chain = &chains()[0];
    register_module(&mut spec, chain);

    // At the measured threshold the machine has FINISHED, so `fuel_out` is false.
    let bad = fuel_out_obligation(
        "a3_mut_cost",
        chain.clean_module,
        ArgShape::PointerCell,
        6,
        2,
    )
    .expect("encodable");
    let err = spec
        .add_recursive_def(&bad, "mutation battery: fuel_out at the threshold")
        .expect_err(
            "THE COST MEASUREMENT IS VACUOUS: the machine reports fuel_out at the same fuel \
             at which it returns a value",
        );
    eprintln!("mutation 3 (cost floor) correctly REJECTED: {err}");
}

/// **The default edge is genuinely exercised, and stays that way.**
///
/// `from_source_system`'s emitted switch lists cases 0..9 and 11. There is **no
/// case 10**: `PVS` reaches the DEFAULT edge. That hole is what makes this chain
/// the sharpest available test of the one thing GAP 2 names by name — whether
/// Clean's `switch` encoding routes like trust-ir's — because a contiguous table
/// can be got right by a mechanism that merely indexes, while a hole cannot.
///
/// This test fails if the hole ever closes. Without it, a future producer that
/// emitted a dense 0..11 table would silently remove the teeth from the
/// differential while leaving every row green.
#[test]
fn crystal_a3_default_edge_is_actually_reached() {
    let text = fixture("from_source_system.trust-ir.txt");
    let switch = text
        .lines()
        .find(|l| l.trim_start().starts_with("switch "))
        .expect("the body must contain a switch");
    let cases = switch.split(';').next().unwrap_or(switch);

    assert!(
        cases.contains("default:"),
        "the switch must have a default edge: {cases}"
    );
    assert!(
        !cases.contains(" 10: "),
        "case 10 has appeared in the emitted switch. The differential's sharpest \
         input (tag 10, routed through the DEFAULT edge) is no longer a default-edge \
         test. Re-point it at whichever discriminant now falls through, or record \
         that this chain no longer exercises a non-contiguous switch: {cases}"
    );
    assert!(
        cases.contains(" 9: ") && cases.contains(" 11: "),
        "cases 9 and 11 must both be present for 10 to be a HOLE rather than a \
         truncation: {cases}"
    );
    eprintln!(
        "default-edge check: switch is non-contiguous (…9, 11, default), tag 10 falls through"
    );
}

/// **Mutation 5 — the default edge must not be a black hole.**
///
/// Guards the opposite failure from mutation 2: if the default edge answered
/// whatever the last explicit case answered, the hole at 10 would be
/// indistinguishable from a case. Tag 10 (`PVS`) answers `Classical` (tag 4),
/// and asserting anything else must be rejected.
#[test]
fn crystal_a3_mutation_default_edge_answer_is_pinned() {
    let mut spec = build_eval_ir_spec_with_stack();
    let chain = chains()
        .into_iter()
        .find(|c| c.name == "from_source_system")
        .expect("the from_source_system chain is registered");
    register_module(&mut spec, &chain);

    let good = value_obligation(
        "a3_mut_dflt_good",
        chain.clean_module,
        chain.arg_shape,
        5,
        10,
        &RunResult::EnumTag(4),
    )
    .expect("encodable");
    spec.add_recursive_def(&good, "mutation battery: the default edge's real answer")
        .expect("tag 10 must reach the default edge and answer Classical (4)");

    let bad = value_obligation(
        "a3_mut_dflt_bad",
        chain.clean_module,
        chain.arg_shape,
        5,
        10,
        &RunResult::EnumTag(5),
    )
    .expect("encodable");
    let err = spec
        .add_recursive_def(&bad, "mutation battery: a wrong default-edge answer")
        .expect_err("THE DEFAULT EDGE IS UNCONSTRAINED: any answer was accepted at tag 10");
    eprintln!("mutation 5 (default edge pinned) correctly REJECTED: {err}");
}

/// **Mutation 4 — the payload guard must actually refuse.**
#[test]
fn crystal_a3_mutation_payload_guard_refuses_a_payload_read() {
    let text = fixture("level_kind_ord.trust-ir.txt");
    payload_is_unread("level_kind_ord", &text, "%2").expect("the real body projects only field 0");

    let mutated = text.replace("extractfield u8 %2, 0", "extractfield ptr %2, 1");
    assert!(
        payload_is_unread("level_kind_ord", &mutated, "%2").is_err(),
        "the payload guard must refuse a body that reads the elided payload"
    );
}

/// **The harness's enum declarations are pinned against an INDEPENDENT artifact.**
///
/// The trust-ir side of this differential has exactly one modelling parameter a
/// human chose: the enum declaration reconstituted for each chain, because the
/// crate-level dump references `enum.13` without carrying an enum table. If that
/// mapping were wrong, E2 would be executing a different function from E1 and E3.
///
/// It is not a free parameter. `data/crystal_enum_tag_pin.json` was produced by a
/// different lane (`77e42993e`), from the Rust source, for a different purpose —
/// pinning the discriminants the *proofs* depend on. This test asserts the two
/// agree variant-for-variant. Two independent derivations of the same mapping is
/// worth considerably more than either alone, and a future divergence in either
/// direction fails here.
#[test]
fn crystal_a3_enum_declarations_match_the_independent_tag_pin() {
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../data/crystal_enum_tag_pin.json");
    let raw = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "the enum tag pin must be readable at {}: {e}",
            path.display()
        )
    });
    let pin: serde_json::Value =
        serde_json::from_str(&raw).expect("crystal_enum_tag_pin.json must be valid JSON");
    let enums = pin["enums"].as_array().expect("`enums` must be an array");

    let mut checked = 0usize;
    for chain in chains() {
        for decl in chain
            .enum_decls
            .split("enum @")
            .filter(|d| !d.trim().is_empty())
        {
            let ident = decl
                .split_whitespace()
                .next()
                .expect("a declaration names its enum");
            let open = decl.find('{').expect("a declaration has a variant list");
            let close = decl
                .find('}')
                .expect("a declaration closes its variant list");
            let mine: Vec<String> = decl[open + 1..close]
                .split(',')
                .map(|v| v.trim().to_owned())
                .filter(|v| !v.is_empty())
                .collect();

            let Some(entry) = enums.iter().find(|e| e["ident"] == ident) else {
                continue; // not every declared enum is pinned; those are unchecked here.
            };
            let pinned: Vec<(String, u64)> = entry["variants"]
                .as_array()
                .expect("`variants` must be an array")
                .iter()
                .map(|v| {
                    (
                        v[0].as_str().expect("variant name").to_owned(),
                        v[1].as_u64().expect("variant tag"),
                    )
                })
                .collect();

            assert_eq!(
                mine.len(),
                pinned.len(),
                "chain `{}` declares {} variants of `{ident}` but the independent pin \
                 records {}. The harness would execute a different function from the \
                 Clean and shipped legs.",
                chain.name,
                mine.len(),
                pinned.len()
            );
            for (idx, (name, tag)) in pinned.iter().enumerate() {
                assert_eq!(
                    u64::try_from(idx).expect("index fits"),
                    *tag,
                    "`{ident}` is pinned with a non-positional discriminant at {name}; \
                     the harness's implicit 0..N declaration no longer models it"
                );
                assert_eq!(
                    &mine[idx], name,
                    "chain `{}`: `{ident}` variant {idx} is `{}` in the harness but `{name}` \
                     in data/crystal_enum_tag_pin.json",
                    chain.name, mine[idx]
                );
            }
            checked += 1;
        }
    }
    assert!(
        checked >= 3,
        "expected at least three enum declarations to be covered by the pin, checked {checked}"
    );
    eprintln!("enum tag pin cross-check: {checked} declaration(s) agree variant-for-variant");
}

/// **The harness's step overhead is DERIVED, not tuned.**
///
/// The cost half of this differential subtracts the harness's own instructions
/// from trust-ir's step count. If that constant were chosen to make the numbers
/// line up, the `+0` offset would be an artefact of the instrument rather than a
/// finding. It is not chosen: it must equal the number of nodes the harness
/// actually emits, and this test counts them.
#[test]
fn crystal_a3_harness_step_overhead_is_derived_not_tuned() {
    for chain in chains() {
        let text = fixture(chain.fixture);
        let (mut module, _) = super::trust_exec::build_module(
            &text,
            chain.original_name,
            chain.enum_decls,
            chain.ret_ty.clone(),
            chain.arg_shape,
            chain.arg_enum,
        )
        .unwrap_or_else(|e| panic!("chain `{}`: {e}", chain.name));
        let harness =
            super::trust_exec::attach_harness(&mut module, chain.arg_shape, chain.arg_enum)
                .unwrap_or_else(|e| panic!("chain `{}`: {e}", chain.name));

        let emitted = harness.blocks.iter().map(|b| b.body.len()).sum::<usize>();
        let declared = super::trust_exec::harness_steps(chain.arg_shape) as usize;
        assert_eq!(
            emitted, declared,
            "chain `{}`: the harness emits {emitted} instructions but {declared} are \
             subtracted from trust-ir's step count. The reported cost offset would be \
             an artefact of the instrument.",
            chain.name
        );
    }
    eprintln!("harness overhead check: subtracted steps equal emitted instructions on every chain");
}
