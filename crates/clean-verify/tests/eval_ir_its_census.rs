// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `ir_its` chain's census — **A4 and A5 for a body of
//! `TypeChecker::infer_type`'s DERIVED CLOSURE.**
//!
//! `ir_its` is minted from function index 102 of the callee sidecar's partial
//! bundle for `<impl tc::TypeChecker<'env>>::infer_type`
//! (`dump-infertype-O3-part`, 2,388 functions), not from the crate module every
//! earlier chain is cut from. The body is
//! `<[level::Level; 2] as smallvec::Array>::size`: `const usize 2`, `copy`,
//! `ret`.
//!
//! This test pays the FULL spec build rather than the EvalIr bundle's half
//! minute, because `ir_its_correct` names `ir_run_le_ret` and
//! `ir_its_machine_sound` names `ir_ret_int_inj`, neither of which is in the
//! narrow EvalIr bundle — the same line `ir_mt` sits on.
//!
//! What it pins is the pair of theorems and their axiom closures. What it does
//! NOT pin, and what `eval_ir_its.rs`'s header states at length, is the
//! three-reader A2 mint gate: this chain has reader A's projection and a HAND
//! reading of the emitted text, and a hand reading is not a gate.

use clean_kernel::name::Name;
use clean_verify::test_utils::build_spec_with_stack;

#[test]
fn a4_and_a5_hold_for_a_body_of_infer_types_derived_closure() {
    let spec = build_spec_with_stack();
    let names: Vec<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_its") || *n == "smallvec_level2_array_size")
        .collect();

    for required in [
        // the minted module, replayed line for line from the artifact projection
        "ir_its_b0",
        "ir_its_func",
        "ir_its_module",
        // the machine ir_init actually builds, pinned by computation
        "ir_its_mach0",
        "ir_its_init_is_mach0",
        // the kernel RUNNING the emitted body
        "ir_its_exact",
        // A4, A5, and the no-fault corollary
        "ir_its_correct",
        "ir_its_never_faults",
        "ir_its_machine_sound",
        // the reflected answer, named rather than written as a literal
        "smallvec_level2_array_size",
    ] {
        assert!(
            names.contains(&required),
            "the full spec must register {required}; it has {names:?}"
        );
    }

    // The whole point: these are DerivedProved with EMPTY axiom closures. A
    // chain that reached A4 by assuming something would show it here.
    for name in ["ir_its_exact", "ir_its_correct", "ir_its_machine_sound"] {
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY transitive axiom closure -- it is a computation, not an \
             assumption. Found: {deps:?}"
        );
    }
}

/// **The DESIGNATED TARGET is in the spec, and the kernel stops it at its first
/// callee.** `ir_it` is `TypeChecker::infer_type` itself — function index 0 of
/// the callee sidecar's partial bundle, six blocks, 36 nodes, minted by reader A.
///
/// A4 is deliberately NOT among these names: the module calls two functions it
/// does not define, so it halts `stuck no_func`. What is pinned is that the body
/// is registered, that the machine `ir_init` builds for it is the one computed,
/// and that the halt is STUCK rather than out of fuel.
#[test]
fn the_designated_target_is_registered_and_halts_at_its_first_callee() {
    let spec = build_spec_with_stack();
    let names: Vec<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_it_"))
        .collect();

    for required in [
        // the five interned type aliases -- five, and every one a flat
        // __tag/__v rendering or an opaque datatype
        "ir_it_tresult",
        "ir_it_ttyerr_opaque",
        "ir_it_ttyerr_flat",
        "ir_it_tresult2",
        "ir_it_tcflow",
        // the six blocks of the emitted control-flow graph
        "ir_it_b0",
        "ir_it_b1",
        "ir_it_b2",
        "ir_it_b3",
        "ir_it_b4",
        "ir_it_b5",
        // the function and the module
        "ir_it_func",
        "ir_it_module",
        // the machine, and the two execution facts
        "ir_it_mach0",
        "ir_it_init_is_mach0",
        "ir_it_halts_at_the_heartbeat",
        "ir_it_more_fuel_does_not_help",
    ] {
        assert!(
            names.contains(&required),
            "the full spec must register {required}; it has {names:?}"
        );
    }

    // ONE A4-SHAPED NAME IS ADMITTED, AS METATHEORY, AND ONLY UNDER ITS PREMISES.
    // (Relabelled 2026-09-24, decision memo D5(d) and section 11: `ir_it_ag_correct`
    // is metatheory over an abstract module whose function 0 is the body minted
    // from a 2026-09-16 dump, which is not the object that ships today. It is
    // never to be cited as A4 for the deployed infer_type.)
    //
    // This assertion used to refuse every A4/A5-shaped name in the `ir_it_`
    // family outright, and it was right to: `ir_it_module` halts STUCK at an
    // undefined callee, so anything called `correct` there would have been a
    // correctness claim about a module that cannot run. `ir_it_ag_correct` is a
    // different statement -- it quantifies the module (`fs`/`gs`) and carries
    // the two callee contracts as PREMISES rather than as authored bodies -- so
    // the guard is not deleted, it is narrowed to the thing that makes that
    // statement honest. Outgrowing it quietly is exactly what must stay
    // impossible: a second A4-shaped name, or this one losing a premise, fails
    // here.
    //
    // E2's second instance (2026-09-24) adds ONE more, and it is admitted for
    // the same reason and under the same premise check: `ir_it_pc_a4_crosscheck`
    // has EXACTLY `ir_it_ag_correct`'s statement (`eval_ir_ctr_census` compares
    // the two elaborated types), re-derived through the step-indexed device. Its
    // name does not contain `correct`, so the filter also catches `_a4`: a
    // guard that a rename could walk past would enforce nothing.
    const AG_ADMITTED: &[&str] = &["ir_it_ag_correct", "ir_it_pc_a4_crosscheck"];
    let a4_shaped: Vec<&str> = names
        .iter()
        .copied()
        .filter(|n| n.contains("correct") || n.contains("machine_sound") || n.contains("_a4"))
        .collect();
    for name in &a4_shaped {
        assert!(
            AG_ADMITTED.contains(name),
            "{name} carries an A4/A5-shaped name in the `ir_it_` family. Only \
             {AG_ADMITTED:?} is admitted, and only because it is stated over an \
             ABSTRACT module with both callee contracts as premises. If this is \
             a new assume-guarantee theorem, add it here WITH its premise check \
             below; if it is a claim about `ir_it_module`, it is false -- that \
             module halts stuck at an undefined callee."
        );
    }
    for name in AG_ADMITTED {
        assert!(
            names.contains(name),
            "{name} must be registered: it is the assume-guarantee METATHEORY for \
             link 4 of this target (memo D5(d)), not A4 for the deployed body"
        );
        let src = spec
            .definitions()
            .get(*name)
            .map(|d| d.type_src.clone())
            .unwrap_or_default();
        // THE PREMISES THAT MAKE THE NAME HONEST, checked in the statement
        // itself rather than trusted. `hc1` is tick_heartbeat's contract and
        // `hc2` is infer_type_fast's; the module is quantified, so this is not a
        // theorem about the minted `ir_it_module`; and the callee frames are
        // built from the contracts' own functions (`ir_func_params g1`/`g2`),
        // which is what stops a premise being vacuously about some other body.
        for needle in [
            "(fs : IRList IRFunc)",
            "(gs : IRList IRGlobal)",
            "(hc1 :",
            "(hc2 :",
            "ir_func_params g1",
            "ir_func_params g2",
            "IRModule.mk fs gs",
        ] {
            assert!(
                src.contains(needle),
                "{name} must carry `{needle}` in its STATEMENT -- without it the \
                 A4-shaped name outruns what was proved: {src}"
            );
        }
        // And it must be a statement about `ir_eval`, not about a step count.
        assert!(
            src.contains("Eq IROutcome (ir_eval fuel (IRModule.mk fs gs) ir_d0"),
            "{name} must conclude about `ir_eval` at function 0 of the abstract \
             module: {src}"
        );
    }

    for name in [
        "ir_it_halts_at_the_heartbeat",
        "ir_it_more_fuel_does_not_help",
        "ir_it_init_is_mach0",
    ] {
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY transitive axiom closure -- it is the kernel running \
             the emitted body, not an assumption about it. Found: {deps:?}"
        );
    }
}

/// **The size-one cut, EXERCISED.** `ir_itc` is the designated target together
/// with `tick_heartbeat` — the callee whose absence makes `infer_type`'s
/// transitive closure cyclic (396 functions / 12 back edges -> 113 / 0).
///
/// The pair of facts is the content: at three steps the machine is still RUNNING
/// where `ir_it_module` has already halted at that very instruction, which is the
/// call resolving; and it then stops inside the heartbeat at `LocalKey::with`.
#[test]
fn the_size_one_cut_is_exercised_and_the_machine_goes_one_frame_deeper() {
    let spec = build_spec_with_stack();
    let names: Vec<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_itc_") || n.starts_with("ir_th_"))
        .collect();

    for required in [
        "ir_itc_module",
        "ir_itc_func",
        // tick_heartbeat's own twenty blocks and its function
        "ir_th_func",
        "ir_th_b0",
        "ir_th_b19",
        // the machine, and the two facts
        "ir_itc_mach0",
        "ir_itc_init_is_mach0",
        "ir_itc_enters_the_heartbeat",
        "ir_itc_halts_inside_the_heartbeat",
    ] {
        assert!(
            names.contains(&required),
            "the full spec must register {required}; it has {names:?}"
        );
    }

    // A4 IS STILL NOT CLAIMED -- four called functions remain declarations.
    // Same guard as ir_it's: a later lane adding one must delete this line on
    // purpose rather than outgrow it quietly.
    assert!(
        !names
            .iter()
            .any(|n| n.contains("correct") || n.contains("machine_sound")),
        "ir_itc must NOT carry an A4/A5-shaped name while its module still halts \
         stuck at an undefined callee: {names:?}"
    );

    for name in [
        "ir_itc_enters_the_heartbeat",
        "ir_itc_halts_inside_the_heartbeat",
    ] {
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY transitive axiom closure -- it is the kernel walking \
             the emitted bodies, not an assumption about them. Found: {deps:?}"
        );
    }
}

/// **The designated target runs its WHOLE DISPATCH.** `ir_itb` is the `ir_lzb`
/// posture applied to `infer_type`: the module NAMES the minted `ir_it_func` and
/// supplies an authored two-node heartbeat model beside it.
///
/// The halting progression across three chains is the content:
///   `ir_it`  halts at the first call (tick_heartbeat absent)
///   `ir_itc` halts one frame INTO the real tick_heartbeat
///   `ir_itb` halts PAST the heartbeat, on the ok branch, at `infer_type_fast`
#[test]
fn the_target_runs_its_whole_dispatch_over_an_authored_heartbeat() {
    let spec = build_spec_with_stack();
    let names: Vec<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_itb"))
        .collect();

    for required in [
        "ir_itb_hb_b0",
        "ir_itb_hb",
        "ir_itb_module",
        "ir_itb_mach0",
        "ir_itb_init_is_mach0",
        "ir_itb_takes_the_switch",
        "ir_itb_reaches_the_inference_call",
    ] {
        assert!(
            names.contains(&required),
            "the full spec must register {required}; it has {names:?}"
        );
    }

    // A4 IS NOT CLAIMED HERE EITHER, and for a second reason on top of the
    // undefined callee: the heartbeat is AUTHORED. Same deliberate guard.
    assert!(
        !names
            .iter()
            .any(|n| n.contains("correct") || n.contains("machine_sound")),
        "ir_itb must NOT carry an A4/A5-shaped name: its heartbeat is a MODEL and \
         its inference callee is undefined: {names:?}"
    );

    for name in [
        "ir_itb_takes_the_switch",
        "ir_itb_reaches_the_inference_call",
    ] {
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY transitive axiom closure -- the model is a MODULE \
             MEMBER the kernel executes, not an assumption it carries. Found: {deps:?}"
        );
    }
}

/// **The designated target RUNS TO COMPLETION and TRANSPORTS its callee's
/// payload.** `ir_itd` supplies the second authored model, and `infer_type`
/// returns — for EVERY payload the inference could have handed back.
///
/// The progression across four chains is the content:
///   `ir_it`  halts at `call 1`      (no heartbeat)
///   `ir_itc` one frame INTO the real heartbeat
///   `ir_itb` halts at `call 2`, step 8   (past the switch, on the ok branch)
///   `ir_itd` RETURNS, step 14            (both callees modelled)
#[test]
fn the_target_returns_and_transports_whatever_its_inference_callee_gave_it() {
    let spec = build_spec_with_stack();
    let names: Vec<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_itd"))
        .collect();

    for required in [
        "ir_itd_cval",
        "ir_itd_fast_b0",
        "ir_itd_fast",
        "ir_itd_module",
        "ir_itd_answer",
        // the cost PIN: still running at 13, returned at 14
        "ir_itd_is_still_running_at_thirteen",
        "ir_itd_transports_the_inference_result",
        "ir_itd_more_fuel_does_not_change_it",
    ] {
        assert!(
            names.contains(&required),
            "the full spec must register {required}; it has {names:?}"
        );
    }

    // A4 IS STILL NOT CLAIMED, and now for the strongest reason yet: BOTH
    // callees are authored. A chain that RETURNS is the one most likely to be
    // read as a correctness result, so the guard matters most here.
    assert!(
        !names
            .iter()
            .any(|n| n.contains("correct") || n.contains("machine_sound")),
        "ir_itd must NOT carry an A4/A5-shaped name: both of its callees are \
         AUTHORED models, so this is the caller's half of a compositional \
         argument and not a correctness theorem about infer_type: {names:?}"
    );

    for name in [
        "ir_itd_is_still_running_at_thirteen",
        "ir_itd_transports_the_inference_result",
        "ir_itd_more_fuel_does_not_change_it",
    ] {
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY transitive axiom closure -- the models are MODULE \
             MEMBERS the kernel executes, not assumptions it carries. Found: {deps:?}"
        );
    }

    // The transport theorem must QUANTIFY over the payload. A version with the
    // payload baked in would be one execution witness and would pass every
    // assertion above, so the binder is checked against the registered source.
    //
    // This guard replaces an earlier one that asserted the rendered definition
    // merely CONTAINED "w" -- which was vacuous, because `ir_itd_answer`
    // contains that letter and the type names it either way. A guard that
    // cannot fail is worse than no guard, because it reads as coverage.
    for name in [
        "ir_itd_cval",
        "ir_itd_module",
        "ir_itd_transports_the_inference_result",
    ] {
        let src = spec
            .definitions()
            .get(name)
            .map(|d| d.type_src.clone())
            .unwrap_or_default();
        assert!(
            src.contains("(sp : IRConst)"),
            "{name} must bind the payload spine as `(sp : IRConst)` -- that binder is the \
             whole difference between the TRANSPORT property and one execution witness. \
             Registered source: {src}"
        );
    }

    // The discriminant is deliberately NOT quantified: it is the selector the
    // target's own switch reads. Pinning that here keeps the scope of the
    // claim honest if someone later tries to generalise it.
    let cval = spec
        .definitions()
        .get("ir_itd_cval")
        .map(|d| d.type_src.clone())
        .unwrap_or_default();
    assert!(
        cval.contains("IRConst.int_ ir_d0"),
        "ir_itd_cval must PIN the discriminant to zero -- it is the switch selector, and a \
         quantified tag would make the branch undecidable. Registered source: {cval}"
    );
}

/// **The transport tail, as a SEAM — over the TARGET ALONE, at an arbitrary
/// heap, with NO callee named in the statement.**
///
/// `ir_itd` proves transport by RUNNING the module, so its statement mentions
/// two authored models and pins the heap to `ir_mem0`. `ir_it_transport_seg`
/// starts from the configuration the instant `call 2` returns and runs only the
/// four nodes that remain, over `ir_it_module` — `infer_type` and nothing else.
///
/// This test's real content is the NEGATIVE guard: that no authored callee
/// appears in the registered statement. That is the whole difference between
/// the two forms, and it is the thing a later edit would silently undo.
#[test]
fn the_transport_tail_holds_over_the_target_alone_with_no_callee_named() {
    let spec = build_spec_with_stack();
    let names: Vec<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_ite_") || *n == "ir_it_transport_seg")
        .collect();

    for required in [
        "ir_ite_loc",
        "ir_ite_smach",
        "ir_ite_bmach",
        "ir_ite_after_store_lookup",
        "ir_ite_after_store_update",
        "ir_ite_after_load",
        "ir_ite_step_store",
        "ir_it_transport_seg",
    ] {
        assert!(
            names.contains(&required),
            "the full spec must register {required}; it has {names:?}"
        );
    }

    for name in ["ir_ite_step_store", "ir_it_transport_seg"] {
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY transitive axiom closure. Found: {deps:?}"
        );
    }

    let src = spec
        .definitions()
        .get("ir_it_transport_seg")
        .map(|d| d.type_src.clone())
        .unwrap_or_default();

    // THE POINT. Neither authored model may appear anywhere in the statement.
    for model in ["ir_itb_hb", "ir_itd_fast", "ir_itd_module", "ir_itb_module"] {
        assert!(
            !src.contains(model),
            "ir_it_transport_seg must not name {model} -- the seam form exists precisely \
             because ir_itd's statement does. Registered source: {src}"
        );
    }
    assert!(
        src.contains("ir_it_module"),
        "ir_it_transport_seg must run over ir_it_module -- the target ALONE. Source: {src}"
    );

    // ...and the heap, counter, caller and bindings must all be QUANTIFIED,
    // which is the other half of what the seam form buys over ir_itd.
    for binder in [
        "(mem : IRList IRMemSlot)",
        "(na : Nat)",
        "(rest : IRList IRFrame)",
        "(ds : IRList Nat)",
        "(loc : IRList IRBinding)",
        "(spv : IRScalar)",
        "(v0 : IRScalar)",
    ] {
        assert!(
            src.contains(binder),
            "ir_it_transport_seg must quantify {binder} -- ir_itd pins the heap to ir_mem0 and \
             this lemma exists to remove that. Registered source: {src}"
        );
    }

    // It is a SEGMENT, not a run, and must not be read as A4.
    assert!(
        !names
            .iter()
            .any(|n| n.contains("correct") || n.contains("machine_sound")),
        "the seam lemma must NOT carry an A4/A5-shaped name: it closes one segment of the \
         body, and composing it end to end still needs the dispatch seam: {names:?}"
    );
}

/// **The DISPATCH seam — the other half of the ok path, over the target alone.**
///
/// `ir_it_transport_seg` covers `call 2` returns → `ret`. This covers `call 1`
/// returns → `call 2`: the `br`, the `extractfield` that reads the tag, and the
/// `switch` that takes the ok branch. Together they cover every instruction of
/// `infer_type`'s ok path EXCEPT the two calls, with no callee named in either.
///
/// It is strictly MORE general than the transport seam: this segment performs no
/// memory operation at all, so the heap and the allocation counter are
/// quantified outright rather than constrained to a live slot at the head.
#[test]
fn the_dispatch_seam_holds_over_the_target_alone_at_an_arbitrary_heap() {
    let spec = build_spec_with_stack();
    let names: Vec<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_it_d") || n.starts_with("ir_it_hb_answer"))
        .collect();

    for required in [
        "ir_it_dframe",
        "ir_it_hb_answer",
        "ir_it_dispatch_end",
        "ir_it_dispatch_seg",
        "ir_it_dispatch_ends_at_the_call",
    ] {
        assert!(
            names.contains(&required),
            "the full spec must register {required}; it has {names:?}"
        );
    }

    for name in ["ir_it_dispatch_seg", "ir_it_dispatch_ends_at_the_call"] {
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY transitive axiom closure. Found: {deps:?}"
        );
    }

    let src = spec
        .definitions()
        .get("ir_it_dispatch_seg")
        .map(|d| d.type_src.clone())
        .unwrap_or_default();

    // No authored model may appear -- the whole point of a seam.
    for model in ["ir_itb_hb", "ir_itd_fast", "ir_itb_module", "ir_itd_module"] {
        assert!(
            !src.contains(model),
            "ir_it_dispatch_seg must not name {model}; it runs over the target alone: {src}"
        );
    }
    assert!(
        src.contains("ir_it_module"),
        "ir_it_dispatch_seg must run over ir_it_module: {src}"
    );

    // THE HEAP AND COUNTER ARE FREE HERE, unlike in the transport seam. That
    // difference is the claim, so it is asserted rather than described.
    for binder in [
        "(mem : IRList IRMemSlot)",
        "(na : Nat)",
        "(rest : IRList IRFrame)",
        "(ds : IRList Nat)",
        "(loc : IRList IRBinding)",
        "(sp : IRScalar)",
    ] {
        assert!(
            src.contains(binder),
            "ir_it_dispatch_seg must quantify {binder}: {src}"
        );
    }
    assert!(
        !src.contains("IRMemSlot.mk"),
        "ir_it_dispatch_seg must NOT constrain the heap's shape -- it touches no \
         memory, so unlike ir_it_transport_seg it needs no live-slot hypothesis: {src}"
    );

    // Still a segment, still not A4.
    assert!(
        !names
            .iter()
            .any(|n| n.contains("correct") || n.contains("machine_sound")),
        "the dispatch seam must NOT carry an A4/A5-shaped name -- it closes one \
         segment and stops at the callee boundary: {names:?}"
    );
}
