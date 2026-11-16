// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `ir_stk` frame-stacking family's census — its acceptance gate.
//!
//! Builds the EvalIr BUNDLE (not the full spec), so an elaboration failure in
//! `add_eval_ir_stack` surfaces here in ~40 s with the failing definition's
//! name, rather than after a 13-minute full build. The first thing this pins is
//! `ir_step_cons_fetch`: an `Eq.refl` at an ABSTRACT module and frame. Its
//! registration is the measurement the whole family was front-loaded on — if
//! the elaborator unfolds `ir_step` there, every later convoy is syntactic.

use clean_kernel::name::Name;
use clean_verify::spec::{ProofStatus, Specification};
use clean_verify::test_utils::build_eval_ir_spec_with_stack;

/// Every name in `names` is registered as a kernel-CHECKED definition with a
/// value (never an axiom), RE-CHECKED here (`verify_definition` infers the
/// elaborated value's type and holds it definitionally equal to the declared
/// one), with an EMPTY transitive axiom closure -- "proved" in this tree's sense
/// (closure within the foundational set, here empty).
///
/// The in-memory `proof_status` LABEL is deliberately not asserted: every
/// `add_recursive_def` registration carries `DerivedPending` until the legacy
/// ProofLibrary promote pipeline runs (declaration_registration.rs), which it
/// never does for this family -- the 103 earlier stack terms, `ir_stk_activation`
/// and `ir_it_ag_correct` included. The kernel closure is the evidence; the
/// label is bookkeeping.
fn assert_kernel_checked_axiom_free(spec: &Specification, names: &[&str]) {
    for name in names {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("{name} must be registered"));
        assert!(
            !def.is_axiom && def.value_src.is_some() && def.elaborated_value.is_some(),
            "{name} must carry a checked value, not be an axiom"
        );
        assert_ne!(
            def.proof_status,
            ProofStatus::Axiom,
            "{name} must not be an axiom-status lemma"
        );
        spec.verify_definition(name)
            .unwrap_or_else(|e| panic!("{name} must re-check against its declared type: {e:?}"));
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY axiom closure. Found: {deps:?}"
        );
    }
}

#[test]
fn the_stacking_definitions_and_shape_witness_register_in_the_evalir_bundle() {
    let spec = build_eval_ir_spec_with_stack();
    let names: Vec<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| {
            n.starts_with("ir_frames_app")
                || n.starts_with("ir_mach_stack")
                || n.starts_with("ir_config_stack")
                || n.starts_with("ir_stk_")
                || n.starts_with("ir_ret_to_nil")
                || n.starts_with("ir_step_cons")
        })
        .collect();
    for required in [
        "ir_frames_app",
        "ir_mach_stack",
        "ir_config_stack",
        "ir_stk_running",
        "ir_frames_app_nil",
        "ir_frames_app_cons",
        "ir_mach_stack_mk",
        "ir_config_stack_running",
        "ir_config_stack_halted",
        "ir_ret_to_nil_halts",
        // THE MEASUREMENT
        "ir_step_cons_fetch",
        // S2, S4 -- hand-authored, foundation-only dependencies
        "ir_stk_running_back",
        "ir_stk_ret_step",
    ] {
        assert!(
            names.contains(&required),
            "the EvalIr bundle must register {required}; it has {names:?}"
        );
    }
    for name in [
        "ir_ret_to_nil_halts",
        "ir_step_cons_fetch",
        "ir_stk_running_back",
        "ir_stk_ret_step",
    ] {
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY axiom closure. Found: {deps:?}"
        );
    }
    // The shape witness must be stated at an ABSTRACT module -- that is the
    // whole point; a version over a concrete ir_*_module would measure nothing.
    let src = spec
        .definitions()
        .get("ir_step_cons_fetch")
        .map(|d| d.type_src.clone())
        .unwrap_or_default();
    assert!(
        src.contains("(m : IRModule)"),
        "ir_step_cons_fetch must quantify the module: {src}"
    );
    assert!(
        src.contains("(f : IRFrame)"),
        "ir_step_cons_fetch must quantify the frame: {src}"
    );
}

/// The MINTED family (64 `ir_stk_*` + 43 `ir_mext_*` + the 49-term node-keyed
/// classifier and twin, scripts/gen_stack_lemmas.py)
/// and the hand-authored theorems above it (S3 `ir_stk_steps`, S5
/// `ir_stk_activation`, `ir_mext_run`) all register, and the load-bearing ones
/// have EMPTY axiom closures. The kernel is the judge of every minted term; this
/// test only asserts that it judged them all and that nothing was assumed.
#[test]
fn the_minted_families_and_the_theorems_above_them_register_axiom_free() {
    let spec = build_eval_ir_spec_with_stack();
    let mut missing: Vec<&str> = Vec::new();
    for name in clean_verify::spec::STACK_MINTED_NAMES
        .iter()
        .chain(clean_verify::spec::STACK_THEOREM_NAMES.iter())
    {
        if !spec.definitions().contains_key(*name) {
            missing.push(name);
        }
    }
    assert!(
        missing.is_empty(),
        "the EvalIr bundle must register every minted stacking / module-extension \
         declaration and every theorem above them; missing: {missing:?}"
    );
    assert_eq!(
        clean_verify::spec::STACK_MINTED_NAMES.len(),
        203,
        "the minted family is 64 ir_stk_* + 43 ir_mext_* declarations (explicit legacy refusal arms \
         for both atomics and Release included) + 49 node-keyed ones: 7 classifier \
         definitions, 6 vacuity pins, ir_stkn_ret_to, 33 ir_stkn_arm_*, ir_stkn_step, \
         ir_stk_botret_false_of_running; then the mkv module axis (crystal link 4 M0 W3): 3 \
         encodings-agreement lemmas, the 43 ir_mextv_* twins and ir_mextv_run"
    );
    for name in [
        "ir_stk_step",
        "ir_mext_step",
        "ir_mext_steps",
        "ir_stk_steps",
        "ir_stk_activation",
        "ir_mext_run",
        "ir_stkn_step",
        "ir_stk_botret_false_of_running",
    ] {
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY axiom closure. Found: {deps:?}"
        );
    }
    // The compositional call rule is stated at an ABSTRACT module and an
    // ABSTRACT caller stack -- a version over a concrete module or a nil rest
    // would restate what the tree already proves by computation.
    let src = spec
        .definitions()
        .get("ir_stk_activation")
        .map(|d| d.type_src.clone())
        .unwrap_or_default();
    for needle in [
        "(m : IRModule)",
        "(rest : IRList IRFrame)",
        "(fk : IRFrame)",
    ] {
        assert!(
            src.contains(needle),
            "ir_stk_activation must quantify {needle}: {src}"
        );
    }
    let src = spec
        .definitions()
        .get("ir_mext_run")
        .map(|d| d.type_src.clone())
        .unwrap_or_default();
    assert!(
        src.contains("(fs0 : IRList IRFunc)") && src.contains("(fs : IRList IRFunc)"),
        "ir_mext_run must quantify BOTH modules' function lists: {src}"
    );
}

/// **E1: the stacking split keyed on the FETCHED NODE** (eval_ir_stack_split.rs,
/// designs/2026-09-24-e1-stk-split.md). Every declaration registers in the
/// EvalIr bundle; the split, its three cases, the dests contract form, the
/// generic call step and the two witnesses carry EMPTY axiom closures; and the
/// statements quantify what they claim to -- an abstract module, an abstract
/// caller stack, the classifier as a premise, never the step's outcome.
#[test]
fn the_fetched_node_split_registers_axiom_free_in_the_evalir_bundle() {
    let spec = build_eval_ir_spec_with_stack();
    let missing: Vec<&str> = clean_verify::spec::STACK_SPLIT_NAMES
        .iter()
        .copied()
        .filter(|name| !spec.definitions().contains_key(*name))
        .collect();
    assert!(
        missing.is_empty(),
        "the EvalIr bundle must register every split declaration; missing: {missing:?}"
    );
    assert_eq!(clean_verify::spec::STACK_SPLIT_NAMES.len(), 32);
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::STACK_SPLIT_NAMES);
    // The 49 node-keyed MINTED declarations (classifier, pins, twin) too: they
    // sit in STACK_MINTED_NAMES after ir_mext_steps and before the mkv module
    // family (W3), which opens at its first encodings-agreement lemma.
    let minted = clean_verify::spec::STACK_MINTED_NAMES;
    let tail = minted
        .iter()
        .position(|n| *n == "ir_mext_steps")
        .expect("ir_mext_steps is minted");
    let mkv = minted
        .iter()
        .position(|n| *n == "ir_enc_agree_view_word")
        .expect("ir_enc_agree_view_word is minted");
    let node_keyed = &minted[tail + 1..mkv];
    assert_eq!(node_keyed.len(), 49);
    assert_eq!(node_keyed.first(), Some(&"ir_frames_is_nil"));
    assert_eq!(node_keyed.last(), Some(&"ir_stk_botret_false_of_running"));
    assert_kernel_checked_axiom_free(&spec, node_keyed);
    // The registry's `type_src` is the whole declaration; the STATEMENT is the
    // header before the first ` := ` (no binder or type here contains one).
    let ty = |name: &str| -> String {
        spec.definitions()
            .get(name)
            .and_then(|d| d.type_src.split(" := ").next().map(str::to_string))
            .unwrap_or_default()
    };
    // The node-keyed step: abstract module and stack; the premises are the
    // nonempty frame list and the CLASSIFIER, never the step's outcome.
    let step = ty("ir_stkn_step");
    for needle in [
        "(m : IRModule)",
        "(rest : IRList IRFrame)",
        "ir_frames_is_nil (ir_mach_frames s)",
        "ir_stk_botret m s",
    ] {
        assert!(
            step.contains(needle),
            "ir_stkn_step must carry {needle}: {step}"
        );
    }
    assert!(
        !step.contains("ir_stk_running"),
        "ir_stkn_step must NOT take a running premise -- that is the whole point: {step}"
    );
    // The split: abstract module, abstract caller stack, the clear predicate.
    let split = ty("ir_stk_split");
    for needle in [
        "(m : IRModule)",
        "(rest : IRList IRFrame)",
        "ir_stk_clear n m c",
    ] {
        assert!(
            split.contains(needle),
            "ir_stk_split must carry {needle}: {split}"
        );
    }
    // F: a HALTED outcome transports -- the case the running family cannot state.
    let f = ty("ir_stk_split_halted");
    assert!(
        f.contains("(o : IROutcome)") && f.contains("(IRConfig.halted o)"),
        "ir_stk_split_halted must conclude at an arbitrary halted outcome: {f}"
    );
    // The dests contract form is `forall d r` with d on the ENTRY frame.
    let dests = ty("ir_stk_activation_dests");
    assert!(
        dests.contains("forall (d : IRList Nat) (r : IRList IRFrame)")
            && dests.contains("ir_ret_to d r"),
        "ir_stk_activation_dests must conclude the forall-d-r contract form: {dests}"
    );
    // The generic call step: abstract module and frame, callee resolved by id.
    let call = ty("ir_call_push");
    for needle in [
        "(m : IRModule)",
        "(f : IRFrame)",
        "(IRInst.call fid args)",
        "ir_func_find (ir_mod_funcs m) fid",
        "ir_push",
    ] {
        assert!(
            call.contains(needle),
            "ir_call_push must carry {needle}: {call}"
        );
    }
    // The witnesses are at the ir_lzc run and quantify the caller stack.
    for name in ["ir_stk_split_witness_r", "ir_stk_split_witness_f"] {
        let w = ty(name);
        assert!(
            w.contains("(rest : IRList IRFrame)") && w.contains("ir_lzc_module"),
            "{name} must be stated over every caller stack at the ir_lzc run: {w}"
        );
    }
}

/// **E1's T witness** (eval_ir_stk_witness.rs, Full-only): the split's T case
/// applied at the authored heartbeat model yields EXACTLY the statement of
/// `ir_it_ag_hc1_at_itd` -- the frame-generic contract `ir_it_ag_correct`
/// consumes -- and every declaration is axiom-free. The equality of the two
/// statements is checked on the REGISTERED types, not on the sources.
#[test]
fn the_split_t_witness_reproduces_the_heartbeat_contract() {
    let spec = clean_verify::test_utils::build_spec_with_stack();
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::STK_WITNESS_NAMES);
    // The split family is in the full spec too, not only in the EvalIr bundle.
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::STACK_SPLIT_NAMES);
    // The two STATEMENTS are compared as elaborated kernel types (the registry's
    // `type_src` is the whole declaration source, name and proof included).
    let elab_ty = |name: &str| {
        spec.definitions()
            .get(name)
            .and_then(|d| d.elaborated_type.clone())
            .unwrap_or_else(|| panic!("{name} must carry an elaborated type"))
    };
    assert!(
        elab_ty("ir_stk_split_witness_t") == elab_ty("ir_it_ag_hc1_at_itd"),
        "the T witness must state exactly the heartbeat contract the A4-shaped theorem consumes"
    );
    // The two re-derived call steps still register axiom-free under their
    // unchanged statements, now proved through the generic ir_call_push.
    for name in ["ir_it_ag_step_call", "ir_hlb_call_step"] {
        let d = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} must be registered"));
        assert!(
            d.value_src
                .as_deref()
                .unwrap_or_default()
                .contains("ir_call_push"),
            "{name} must be proved THROUGH ir_call_push"
        );
    }
    assert_kernel_checked_axiom_free(&spec, &["ir_it_ag_step_call", "ir_hlb_call_step"]);
}

/// The STATEMENT of a registered declaration: its source up to the first
/// top-level ` := ` (the registry's `type_src` is the whole declaration).
fn statement_of(spec: &Specification, name: &str) -> String {
    let src = spec
        .definitions()
        .get(name)
        .map(|d| d.type_src.clone())
        .unwrap_or_else(|| panic!("{name} must be registered"));
    let mut depth = 0i32;
    for (i, ch) in src.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ':' if depth == 0 && src[i..].starts_with(":= ") => return src[..i].to_string(),
            _ => {}
        }
    }
    src
}

/// **The two axes E1 left open** (eval_ir_stack_axes_minted.rs, minted by
/// scripts/gen_stack_axes.py, and eval_ir_stack_axes.rs;
/// designs/2026-09-25-e1-axes.md). Every declaration registers in the EvalIr
/// bundle kernel-checked with an EMPTY axiom closure, and the load-bearing ones
/// say what they claim: the dests theorems quantify the module and take NO
/// premise about the body; the general T case takes ONE run; the module axis is
/// keyed on `ir_mext_ok`, never on the running predicate.
#[test]
fn the_two_axes_register_axiom_free_in_the_evalir_bundle() {
    let spec = build_eval_ir_spec_with_stack();
    let minted = clean_verify::spec::STACK_AXES_MINTED_NAMES;
    let theorems = clean_verify::spec::STACK_AXES_NAMES;
    assert_eq!(
        minted.len(),
        191,
        "the minted axes are 11 definitions and pins, ir_resolve_bdst, 9 writers, 18 \
         branching helpers, 33 single-frame arms, ir_bdst_step1, 6 tail lemmas, \
         ir_bdst_step_cons, 3 + 7 + 3 module-premise definitions, pins and support, the 43 \
         outcome-keyed twins, 3 + 7 + 1 for the classifier converse, and the mkv module \
         axis keyed on the outcome (crystal link 4 M0 W3): the 43 ir_mextvo_* twins and \
         ir_mextvo_run"
    );
    assert_eq!(theorems.len(), 16);
    let missing: Vec<&str> = minted
        .iter()
        .chain(theorems.iter())
        .copied()
        .filter(|n| !spec.definitions().contains_key(*n))
        .collect();
    assert!(missing.is_empty(), "unregistered: {missing:?}");
    assert_kernel_checked_axiom_free(&spec, minted);
    assert_kernel_checked_axiom_free(&spec, theorems);
    // One twin per running-keyed module term, and one single-frame arm per
    // IRInst constructor -- counted against the families they mirror.
    let mext = clean_verify::spec::STACK_MINTED_NAMES
        .iter()
        .filter(|n| n.starts_with("ir_mext_"))
        .count();
    let mexto = minted.iter().filter(|n| n.starts_with("ir_mexto_")).count();
    assert_eq!(mexto, mext, "one outcome-keyed twin per ir_mext_ term");
    let stk_arms = clean_verify::spec::STACK_MINTED_NAMES
        .iter()
        .filter(|n| n.starts_with("ir_stk_arm_"))
        .count();
    let bdst_arms = minted
        .iter()
        .filter(|n| n.starts_with("ir_bdst_arm_"))
        .count();
    assert_eq!(
        bdst_arms, stk_arms,
        "one single-frame arm per IRInst constructor"
    );

    // Axis 1: parametricity at EVERY module and machine, with no hypothesis.
    let step = statement_of(&spec, "ir_bdst_step");
    assert!(
        step.contains("(m : IRModule) (s : IRMachine) (d : IRList Nat)")
            && !step.contains("(h")
            && step.contains("ir_config_set_bot (ir_step m s) d"),
        "ir_bdst_step must be premise-free over every module and machine: {step}"
    );
    let inv = statement_of(&spec, "ir_stk_bot_dests_inv");
    assert!(
        inv.contains("(m : IRModule)") && !inv.contains("(h"),
        "the dests invariant must take NO premise about the body: {inv}"
    );
    let general = statement_of(&spec, "ir_stk_activation_dests_gen");
    assert!(
        general.contains("(m : IRModule)")
            && !general.contains("(hrun : forall")
            && general.contains("forall (d : IRList Nat) (r : IRList IRFrame)")
            && general.contains("ir_ret_to d r"),
        "the general T case must take ONE run and conclude the forall-d-r contract form: {general}"
    );
    // Axis 2: the twin is keyed on ir_mext_ok, and F crosses both axes.
    let mstep = statement_of(&spec, "ir_mexto_step");
    assert!(
        mstep.contains("ir_mext_ok") && !mstep.contains("ir_stk_running"),
        "the outcome-keyed step must not take the running premise: {mstep}"
    );
    let f = statement_of(&spec, "ir_stk_split_halted_mext");
    for needle in [
        "(rest : IRList IRFrame)",
        "(o : IROutcome)",
        "ir_mext_ok (IRConfig.halted o)",
        "(ir_steps n (IRModule.mk fs gs) (ir_config_stack c rest))",
    ] {
        assert!(
            f.contains(needle),
            "ir_stk_split_halted_mext must carry {needle}: {f}"
        );
    }
    // The classifier's converse, at an abstract module and machine.
    let conv = statement_of(&spec, "ir_stk_botret_ret");
    assert!(
        conv.contains("(m : IRModule) (s : IRMachine)")
            && conv.contains("ir_is_ret_halt (ir_step m s)"),
        "ir_stk_botret_ret: {conv}"
    );
    // The dests witness CITES the 107-step run.
    let w = spec
        .definitions()
        .get("ir_bdst_lzd_maxzz_out")
        .and_then(|d| d.value_src.clone())
        .unwrap_or_default();
    assert!(w.contains("ir_lzd_max_zz_returns_true_at_107"));
}

/// **The two axes' Full-only witnesses and necessity refutations**
/// (eval_ir_stack_axes_witness.rs): the T witness through the GENERAL theorem
/// from ONE run states exactly `ir_it_ag_hc1_at_itd` (compared as elaborated
/// types); F crosses both axes at the meta-tag OOB run; and each exclusion of
/// `ir_mext_ok` is refuted as unnecessary-to-drop by a kernel-checked
/// contradiction from the unguarded statement.
#[test]
fn the_axes_witnesses_and_refutations_hold_in_the_full_spec() {
    let spec = clean_verify::test_utils::build_spec_with_stack();
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::STACK_AXES_WITNESS_NAMES);
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::STACK_AXES_MINTED_NAMES);
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::STACK_AXES_NAMES);
    let elab_ty = |name: &str| {
        spec.definitions()
            .get(name)
            .and_then(|d| d.elaborated_type.clone())
            .unwrap_or_else(|| panic!("{name} must carry an elaborated type"))
    };
    assert!(
        elab_ty("ir_stk_split_witness_t_gen") == elab_ty("ir_it_ag_hc1_at_itd"),
        "the T witness through ir_stk_activation_dests_gen must state exactly the heartbeat \
         contract ir_it_ag_correct consumes"
    );
    let via = spec
        .definitions()
        .get("ir_stk_split_witness_t_gen")
        .and_then(|d| d.value_src.clone())
        .unwrap_or_default();
    assert!(
        via.contains("ir_stk_activation_dests_gen") && via.contains("(@IRList.nil Nat))"),
        "the T witness must go through the general theorem from ONE run at the empty dests"
    );
    // The three-way reading and its exact return case, witnessed at the
    // heartbeat contract with NO side premise beyond the budget split.
    let tri = statement_of(&spec, "ir_ctr_tri_stack_hb");
    assert!(
        tri.contains("(r : IRList IRFrame)") && !tri.contains("(hc") && !tri.contains("(hE"),
        "the heartbeat reading must discharge the contract and entry premises itself: {tri}"
    );
    let post = statement_of(&spec, "ir_ctr_ret_post_stack_hb");
    assert!(
        post.starts_with("def ir_ctr_ret_post_stack_hb (spc : IRConst) (p : Nat) (mem : IRList IRMemSlot) (na : Nat) (d : IRList Nat) :"),
        "every premise of the exact return case must be discharged at the heartbeat: {post}"
    );
    for name in ["ir_mexto_needs_no_func", "ir_mexto_needs_no_global"] {
        let st = statement_of(&spec, name);
        assert!(
            st.contains("(C : Prop)")
                && st.contains("Eq IRConfig (ir_step (IRModule.mk fs gs) s) (IRConfig.halted o)")
                && !st.contains("ir_mext_ok"),
            "{name} must refute the UNGUARDED one-step transport: {st}"
        );
    }
}

/// **The module axis over BOTH module forms** (crystal link 4, M0 work item W3;
/// scripts/gen_stack_lemmas.py and scripts/gen_stack_axes.py, the mkv sections).
/// A pre-Phase-B module is `IRModule.mk fs gs`; every DERIVED module is
/// `IRModule.mkv fs gs es`, whose loads read the encodings table `es`. The mk
/// family (`ir_mext_*`, `ir_mexto_*`, `ir_mext_run`, `ir_mexto_run`) says nothing
/// about an mkv module, so the axis is minted twice: one mkv twin per mk module
/// term, running-keyed and outcome-keyed, plus the two run forms. The census
/// holds the two families to each other by COUNT, holds every load-bearing
/// declaration to a kernel-checked, axiom-free registration, and holds the
/// statements to what they claim: the mkv forms quantify BOTH encodings tables
/// and take the encodings premise -- every row found alike (`henc`) and the same
/// length (`hlen`, the view's fuel) -- and the `load` arm is the ONLY arm that takes
/// it. Dropping that premise is refused by the kernel (the RED record in
/// reports/crystal-lane/2026-09-30-link4-m0/w3/).
#[test]
fn the_module_axis_covers_both_module_forms() {
    let spec = build_eval_ir_spec_with_stack();
    let minted = clean_verify::spec::STACK_MINTED_NAMES;
    let axes = clean_verify::spec::STACK_AXES_MINTED_NAMES;
    let count =
        |names: &[&str], prefix: &str| names.iter().filter(|n| n.starts_with(prefix)).count();
    let mk = count(minted, "ir_mext_");
    assert_eq!(mk, 43, "the running-keyed mk module family");
    assert_eq!(
        count(minted, "ir_mextv_"),
        mk + 1,
        "one mkv twin per mk module term, plus ir_mextv_run"
    );
    assert_eq!(
        count(minted, "ir_mextv_arm_"),
        count(minted, "ir_mext_arm_"),
        "one mkv arm per mk arm, i.e. per IRInst constructor"
    );
    assert_eq!(count(axes, "ir_mexto_"), mk, "the outcome-keyed mk twins");
    assert_eq!(
        count(axes, "ir_mextvo_"),
        mk + 1,
        "one outcome-keyed mkv twin per mk module term, plus ir_mextvo_run"
    );
    assert_kernel_checked_axiom_free(
        &spec,
        &[
            "ir_enc_agree_view_word",
            "ir_enc_agree_view_ty",
            "ir_enc_agree_load_view",
            "ir_mext_step",
            "ir_mext_steps",
            "ir_mext_run",
            "ir_mexto_run",
            "ir_mextv_arm_load",
            "ir_mextv_step",
            "ir_mextv_steps",
            "ir_mextv_run",
            "ir_mextvo_step",
            "ir_mextvo_steps",
            "ir_mextvo_run",
        ],
    );
    let he =
        "(henc : forall (te : IRTy), @Eq (IROption IREnc) (ir_enc_find es0 te) (ir_enc_find es te))";
    let hl = "(hlen : @Eq Nat (ir_enc_len es0) (ir_enc_len es))";
    for name in [
        "ir_mextv_run",
        "ir_mextvo_run",
        "ir_mextv_step",
        "ir_mextv_steps",
    ] {
        let src = statement_of(&spec, name);
        for needle in [
            "(IRModule.mkv fs0 gs0 es0)",
            "(IRModule.mkv fs gs es)",
            he,
            hl,
        ] {
            assert!(src.contains(needle), "{name} must carry {needle}: {src}");
        }
    }
    for name in ["ir_mext_run", "ir_mexto_run"] {
        let src = statement_of(&spec, name);
        assert!(
            src.contains("(IRModule.mk fs0 gs0)")
                && src.contains("(IRModule.mk fs gs)")
                && !src.contains("(henc :"),
            "{name} is the mk form and takes no encodings premise: {src}"
        );
    }
    for name in minted.iter().filter(|n| n.starts_with("ir_mextv_arm_")) {
        let src = statement_of(&spec, name);
        assert_eq!(
            src.contains("(henc :"),
            *name == "ir_mextv_arm_load",
            "only the load arm reads the encodings table, so only it takes henc / hlen: {name}"
        );
    }
}
