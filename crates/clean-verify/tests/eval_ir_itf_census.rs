// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! The assume-guarantee activation's census — the acceptance gate for the
//! A4-SHAPED statement about `infer_type`.
//!
//! What this file exists to stop is one specific way of being wrong: a
//! theorem whose NAME says more than its statement. `ir_it_ag_correct`
//! concludes about `ir_eval` at function 0 of an ABSTRACT module, under two
//! callee contracts it does not discharge, and the value it returns is the
//! second contract's own payload carried through. Every one of those clauses
//! is asserted here against the registered statement, so the day one of them
//! is dropped the census goes red rather than the claim quietly widening.

use clean_kernel::name::Name;
use clean_verify::test_utils::build_spec_with_stack;

/// Every declaration of the stage registers, and the load-bearing ones carry
/// an EMPTY axiom closure.
#[test]
fn the_assume_guarantee_stage_registers_axiom_free() {
    let spec = build_spec_with_stack();
    let mut missing: Vec<&str> = Vec::new();
    for name in clean_verify::spec::ITF_NAMES {
        if !spec.definitions().contains_key(*name) {
            missing.push(name);
        }
    }
    assert!(
        missing.is_empty(),
        "the full spec must register every declaration of the assume-guarantee \
         stage; missing: {missing:?}"
    );
    assert_eq!(
        clean_verify::spec::ITF_NAMES.len(),
        80,
        "the stage is 80 declarations: 61 for the theorem (five general \
         helpers, the two seams' abstract-module transports, the prologue, \
         both call steps, the arbitrary-slot transport, the ret step, and the \
         two headline theorems) plus 19 for the NON-VACUITY WITNESS below"
    );
    for name in [
        "ir_mem_lookup_update_hit",
        "ir_it_hf_of_h0",
        "ir_it_hg_nil",
        "ir_it_dispatch_seg_ext",
        "ir_it_transport3_at",
        "ir_it_ag_prologue",
        "ir_it_ag_call2",
        "ir_it_ag_ret",
        "ir_it_ag_activation",
        "ir_it_ag_init",
        "ir_it_ag_correct",
    ] {
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY transitive axiom closure — the callee \
             contracts are PREMISES of a statement, never axioms of the \
             environment, and that distinction is the whole point of this \
             stage. Found: {deps:?}"
        );
    }
}

/// **The premises are simultaneously satisfiable — the theorem is not vacuous.**
///
/// Six premises, two of them universally-quantified callee contracts, is
/// exactly the shape that can be true for the wrong reason. So the theorem is
/// instantiated at a CONCRETE module — `ir_itd_module`, whose two callees are
/// the authored two-node models the `ir_itd` chain already runs — where every
/// premise is discharged by computation, and the conclusion it then yields is
/// checked against `ir_itd_transports_the_inference_result`, a fact the tree
/// proves independently and by a different route.
#[test]
fn the_assume_guarantee_premises_are_all_discharged_at_a_concrete_module() {
    let spec = build_spec_with_stack();
    for name in [
        // every premise, proved rather than assumed
        "ir_it_ag_h0_at_itd",
        "ir_it_ag_h1_at_itd",
        "ir_it_ag_h2_at_itd",
        "ir_it_ag_hc1_at_itd",
        "ir_it_ag_hc2_at_itd",
        "ir_it_ag_hslot_at_itd",
        // the theorem applied to them, and the agreement with ir_itd
        "ir_it_ag_witness",
        "ir_it_ag_witness_agrees",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} must be registered: without it the A4-shaped theorem is \
             well-typed but never shown SATISFIABLE, which is the one way six \
             premises can be true for the wrong reason"
        );
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must be axiom-free. Found: {deps:?}"
        );
    }

    // THE TWO CONTRACTS ARE FRAME-GENERIC HERE TOO. A witness that discharged
    // hc1/hc2 at one `d`/`r` would not be a witness for the theorem, which
    // consumes them at two DIFFERENT frame stacks.
    for name in ["ir_it_ag_hc1_at_itd", "ir_it_ag_hc2_at_itd"] {
        let src = spec
            .definitions()
            .get(name)
            .map(|d| d.type_src.clone())
            .unwrap_or_default();
        assert!(
            src.contains("(d : IRList Nat)") && src.contains("(r : IRList IRFrame)"),
            "{name} must quantify the return-destination list and the caller \
             stack: {src}"
        );
    }
}

/// **The claim cannot outrun the statement.**
///
/// Read off the registered type, not off the description: the module is
/// quantified, both callee contracts appear as premises, each contract is
/// about its own function (`ir_func_params g1` / `g2`, so a premise cannot be
/// vacuously about some other body), the conclusion is about `ir_eval`, and
/// the returned value is the SECOND contract's payload — the same `spv` that
/// appears inside `hc2`.
#[test]
fn the_a4_shaped_theorem_states_its_premises_and_its_transported_value() {
    let spec = build_spec_with_stack();
    let src = spec
        .definitions()
        .get("ir_it_ag_correct")
        .map(|d| d.type_src.clone())
        .expect("ir_it_ag_correct must be registered");

    for needle in [
        // the module is ABSTRACT
        "(fs : IRList IRFunc)",
        "(gs : IRList IRGlobal)",
        "IRModule.mk fs gs",
        // function 0 is the minted body, 1 and 2 are the contracts' functions
        "(ir_func_find fs ir_d0) (IROption.some IRFunc ir_it_func)",
        "(hc1 :",
        "(hc2 :",
        "ir_func_params g1",
        "ir_func_params g2",
        // the heap hypothesis and the fuel bound are premises too
        "(hslot :",
        "(hle : Le",
        // and the conclusion is about the evaluator
        "Eq IROutcome (ir_eval fuel (IRModule.mk fs gs) ir_d0",
    ] {
        assert!(
            src.contains(needle),
            "ir_it_ag_correct must carry `{needle}` in its STATEMENT: {src}"
        );
    }

    // THE VALUE IS TRANSPORTED, NOT COMPUTED. `spv` is bound by the theorem and
    // appears inside `hc2`'s own conclusion; the theorem returns it. If a later
    // edit made the conclusion name something the premises do not supply, this
    // is where that shows up.
    assert!(
        src.contains("(ir_ret_to d r mem2 na2 (ir_vl1 (IRScalar.aggv spv)))"),
        "hc2 must be the thing that supplies the returned payload: {src}"
    );
    assert!(
        src.contains("(IROutcome.ret (ir_vl1 (IRScalar.aggv spv)))"),
        "the conclusion must return hc2's own payload: {src}"
    );

    // A5 IS NOT CLAIMED. The A4-shaped half is stated; nothing here asserts
    // machine soundness, and a name that did would have to be added to the
    // `ir_it_` guard in eval_ir_its_census.rs deliberately.
    let names: Vec<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_it_ag"))
        .collect();
    assert!(
        !names.iter().any(|n| n.contains("machine_sound")),
        "no A5-shaped name is claimed for the assume-guarantee stage: {names:?}"
    );
}
