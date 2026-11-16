// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **E2's census** -- the step-indexed contract device (`eval_ir_ctr.rs`), the
//! `Level::is_zero` local obligations in step-indexed form
//! (`eval_ir_lzd_sctr.rs`, minted by `scripts/gen_lzd_sctr.py`), and the
//! Full-bundle assembly (`eval_ir_lzd_pc.rs`); and the SECOND instance,
//! `TypeChecker::infer_type` in a three-member mutual group
//! (`eval_ir_it_sctr.rs`, `eval_ir_it_pc.rs`, minted by `scripts/gen_it_sctr.py`).
//! Statements settled in `designs/2026-09-24-e2-contract-soundness.md`.
//!
//! "Proved" here means what the tree means by it: kernel-checked on
//! registration, re-checked by `verify_definition`, transitive axiom closure
//! EMPTY. The in-memory `proof_status` label of every `add_recursive_def`
//! registration is `DerivedPending` (declaration_registration.rs), for this
//! family exactly as for the stack family and the structural A4; the census
//! asserts the kernel facts, not the label.

use clean_kernel::name::Name;
use clean_verify::spec::{ProofStatus, Specification};
use clean_verify::test_utils::build_eval_ir_spec_with_stack;

/// The counts this census mints -- the E2 half of the cost model. Quote them;
/// do not type them somewhere else.
///
/// 16 -> 32 and 12 -> 14 (2026-09-25, D5's re-decided remedy): the body
/// obligations are minted ONE LEMMA PER CALL, so each gains one resume segment
/// per call it makes -- `ir_lzd_imax_sseg` and `ir_lzd_max_false_sseg` two each,
/// `ir_lzd_max_true_sseg` four, `ir_it_top_sseg` two -- and each `is_zero`
/// obligation one NAMED frame stack per call as well (`_st<i>`: spelled out,
/// the stack carries the execution history, which kept the chain superlinear).
/// `infer_type`'s frames are written out and do not grow, so it gains none. The
/// obligations' own statements are unchanged; this is the minted SHAPE moving.
///
/// 44 -> 46 (2026-09-25, decision memo §18): the two `unreachable`-arm pins, the image of an
/// undefined-behaviour halt.
const CTR_DECLS: usize = 46;
const LZD_SCTR_DECLS: usize = 32;
const LZD_PC_DECLS: usize = 15;
/// E2's SECOND instance (`eval_ir_it_sctr.rs`, `eval_ir_it_pc.rs`): infer_type.
const IT_SCTR_DECLS: usize = 14;
const IT_PC_DECLS: usize = 20;

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
        assert_ne!(def.proof_status, ProofStatus::Axiom, "{name}");
        spec.verify_definition(name)
            .unwrap_or_else(|e| panic!("{name} must re-check against its declared type: {e:?}"));
        let mut deps: Vec<String> = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default()
            .into_iter()
            .map(|n| n.to_string())
            .collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY axiom closure. Found: {deps:?}"
        );
    }
}

/// The STATEMENT of a registered declaration: its source up to the first
/// top-level ` := ` (the registry's `type_src` is the whole declaration).
fn statement(spec: &Specification, name: &str) -> String {
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

/// The device and the instance's local obligations register in the EvalIr
/// bundle, kernel-checked with empty axiom closures, and say what they claim:
/// the sanctioned-halt predicate admits exactly `ub assert_failed`; the contract
/// is stated on the POST-RETURN configuration for every caller; soundness is a
/// plain `Nat.rec` whose local obligation consumes the group at the strictly
/// smaller budget; every local obligation proves `Nat.succ n` from `n`.
#[test]
fn the_contract_device_and_the_lzd_obligations_register_axiom_free_in_the_evalir_bundle() {
    let spec = build_eval_ir_spec_with_stack();
    assert_eq!(clean_verify::spec::CTR_NAMES.len(), CTR_DECLS);
    assert_eq!(clean_verify::spec::LZD_SCTR_NAMES.len(), LZD_SCTR_DECLS);
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::CTR_NAMES);
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::LZD_SCTR_NAMES);

    // The sanctioned-halt predicate: one true minor, at assert_failed, and the
    // pins the kernel checked by computation.
    for pin in [
        "ir_sanctioned_assert_failed",
        "ir_sanctioned_unreachable",
        "ir_sanctioned_atomic_arm",
        "ir_bad_halt_atomic_arm",
        "ir_sanctioned_unreachable_arm",
        "ir_bad_halt_unreachable_arm",
        "ir_bad_halt_type_error",
        "ir_bad_halt_unmodelled",
        "ir_bad_halt_stuck",
    ] {
        assert!(spec.definitions().contains_key(pin), "{pin}");
    }
    assert!(
        statement(&spec, "ir_sanctioned_atomic_arm")
            .contains("IRInst.atomic_fetch_add_relaxed_u64_seq p v"),
        "the atomic pin must be stated at the 31st IRInst arm"
    );
    // Memo §18: the UB-halt image is the `unreachable` ARM, refused at every module and machine.
    assert!(
        statement(&spec, "ir_sanctioned_unreachable_arm")
            .contains("ir_sanctioned (ir_config_outcome (ir_exec m IRInst.unreachable rs s))"),
        "the UB-halt pin must be stated at the unreachable IRInst arm"
    );

    // The contract: every G, every caller (d, r); the post on the POST-RETURN
    // configuration; safety at the entry.
    let ctr = spec
        .definitions()
        .get("ir_ctr_at")
        .map(|d| d.type_src.clone())
        .unwrap_or_default();
    for needle in [
        "forall (G : IROutcome -> Prop) (d : IRList Nat) (r : IRList IRFrame)",
        "Q mem2 na2 vs -> ir_safe G m n (ir_ret_to d r mem2 na2 vs)",
        "ir_safe G m n (IRConfig.running (E d r))",
    ] {
        assert!(ctr.contains(needle), "ir_ctr_at must carry {needle}: {ctr}");
    }

    // Soundness: Nat.rec, the local obligation from n to succ n, a table of
    // any index type -- and no strong induction anywhere in the device.
    let sound = statement(&spec, "ir_ctr_group_sound");
    assert!(
        sound.contains(
            "(hloc : forall (n : Nat), (forall (a : A), P a -> ir_ctr_at m (E a) (Q a) n) -> \
             forall (a : A), P a -> ir_ctr_at m (E a) (Q a) (Nat.succ n))"
        ),
        "ir_ctr_group_sound must take the local obligation from n to succ n: {sound}"
    );
    for name in clean_verify::spec::CTR_NAMES
        .iter()
        .chain(clean_verify::spec::LZD_SCTR_NAMES)
    {
        let src = &spec.definitions()[*name].type_src;
        assert!(
            !src.contains("nat_strong_rec") && !src.contains("Le.rec"),
            "{name}: the device must not need strong induction"
        );
    }

    // The adapter: an exact run in the hc1 shape, for every caller.
    let adapter = statement(&spec, "ir_ctr_of_exact");
    assert!(
        adapter.contains(
            "(hex : forall (d : IRList Nat) (r : IRList IRFrame), @Eq IRConfig \
             (ir_steps c m (IRConfig.running (E d r))) (ir_ret_to d r mX nX vX))"
        ),
        "the adapter must consume the hc1 shape: {adapter}"
    );
    assert!(spec.definitions()["ir_lzd_deref_ctr"]
        .type_src
        .contains("ir_lzd_deref_activation mem p b na d r hlt h hcb"));

    // Every local obligation proves the body at succ n from the group at n.
    for (name, ih) in [
        ("ir_lzd_imax_sseg", "(ih2 : ir_ctr_at ir_lzd_module"),
        ("ir_lzd_max_false_sseg", "(ih1 : ir_ctr_at ir_lzd_module"),
        ("ir_lzd_max_true_sseg", "(ih1 : ir_ctr_at ir_lzd_module"),
    ] {
        let st = statement(&spec, name);
        assert!(
            st.contains(ih),
            "{name} must take the group hypothesis: {st}"
        );
        assert!(
            st.ends_with("(ir_lzd_zpost mem na Bool.false) (Nat.succ n) ")
                || st.ends_with("(ir_lzd_zpost mem na ans2) (Nat.succ n) "),
            "{name} must conclude the body's contract at succ n: {st}"
        );
    }
}

/// **The first instance, end to end, in the Full bundle.** The table's
/// declarations are kernel-checked with empty axiom closures; the acceptance
/// theorem is partial correctness plus safety at EVERY fuel (no cost premise);
/// and the cross-check's elaborated TYPE is EXACTLY the structural A4
/// `ir_lzd_correct`'s -- the same statement, reached with the answer from the
/// device and only termination from the structural chain.
#[test]
fn the_is_zero_instance_reproduces_the_structural_a4_through_the_device() {
    let spec = clean_verify::test_utils::build_spec_with_stack();
    assert_eq!(clean_verify::spec::LZD_PC_NAMES.len(), LZD_PC_DECLS);
    assert_eq!(clean_verify::spec::LZD_PC_NAMES[0], "IRLzdIn");
    assert!(
        spec.env()
            .get_inductive(&Name::from_string("IRLzdIn"))
            .is_some(),
        "the table's index type must be registered"
    );
    assert_kernel_checked_axiom_free(&spec, &clean_verify::spec::LZD_PC_NAMES[1..]);
    // The device and the EvalIr half are in the Full spec too.
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::CTR_NAMES);
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::LZD_SCTR_NAMES);

    let elab_ty = |name: &str| {
        spec.definitions()
            .get(name)
            .and_then(|d| d.elaborated_type.clone())
            .unwrap_or_else(|| panic!("{name} must carry an elaborated type"))
    };
    assert!(
        elab_ty("ir_lzd_pc_a4_crosscheck") == elab_ty("ir_lzd_correct"),
        "the cross-check must state EXACTLY the structural A4"
    );

    // The acceptance theorem: every fuel, no cost premise, the premise
    // ir_lzd_correct takes, the three-way outcome predicate.
    let pc = statement(&spec, "ir_lzd_pc");
    assert!(
        pc.contains("(fuel : Nat)")
            && pc.contains("(href : EncodesLiveLevelRefD (ir_lzd_init_mem mem) na r l)")
            && pc.contains(
                ": ir_lzd_pc_ok (level_is_zero l) (ir_eval fuel ir_lzd_module ir_d0 (ir_vl1 r) mem na)"
            )
            && !pc.contains("Le "),
        "ir_lzd_pc must be partial correctness plus safety at every fuel: {pc}"
    );
    // The contract at every budget comes from the soundness theorem, and the
    // cross-check takes only TERMINATION from the structural chain.
    let ctr_src = &spec.definitions()["ir_lzd_ctr"].type_src;
    assert!(ctr_src.contains("ir_ctr_group_sound ir_lzd_module IRLzdIn"));
    let cc = &spec.definitions()["ir_lzd_pc_a4_crosscheck"].type_src;
    assert!(cc.contains("(ir_lzd_pc mem fuel na r l href)"));
    assert!(cc.contains("ir_lzd_never_faults") && !cc.contains("(ir_lzd_correct "));
    // Non-vacuity: the premise is witnessed and the ret arm is exercised.
    for w in [
        "ir_lzd_in_pre_witness",
        "ir_lzd_pc_witness_maxzz",
        "ir_lzd_pc_crosscheck_maxzz",
    ] {
        assert!(
            spec.definitions()[w].type_src.contains("encodes_"),
            "{w} must rest on the inhabited premise"
        );
    }
}

/// **E2's open item: the three-way reading at an ARBITRARY caller stack**
/// (eval_ir_ctr_stack.rs). Every declaration registers in the EvalIr bundle
/// axiom-free; the reading quantifies the caller stack and is proved FROM the
/// contract; its witness instantiates the deref contract.
#[test]
fn the_three_way_reading_at_an_arbitrary_caller_stack_registers_axiom_free() {
    let spec = build_eval_ir_spec_with_stack();
    let names = clean_verify::spec::CTR_STACK_NAMES;
    assert_eq!(names.len(), 11);
    assert_kernel_checked_axiom_free(&spec, names);
    let tri = statement(&spec, "ir_ctr_tri_stack");
    for needle in [
        "(hc : ir_ctr_at m E Q n)",
        "(r : IRList IRFrame)",
        "ir_stk_tri Q r",
        "(IRConfig.running (E d r))",
    ] {
        assert!(
            tri.contains(needle),
            "ir_ctr_tri_stack must carry {needle}: {tri}"
        );
    }
    let w = statement(&spec, "ir_ctr_tri_stack_lzd_deref");
    assert!(
        w.contains("(r : IRList IRFrame)") && w.contains("ir_lzd_dmach mem p na d r"),
        "the witness must read the deref contract at an arbitrary caller stack: {w}"
    );
    let clear = statement(&spec, "ir_stk_clear_of_mid");
    assert!(clear.contains("ir_halt_mid (ir_steps n m c)") && clear.contains("ir_stk_clear n m c"));
}

/// **The second instance, end to end, in the Full bundle: `infer_type`.** A
/// body that calls two OTHER functions and itself not at all, over an ABSTRACT
/// module, in a three-member MUTUAL recursion group whose two callee members'
/// local obligations are premises. Every declaration is kernel-checked with an
/// empty axiom closure; the contract at every budget comes from
/// `ir_ctr_group_sound`; the acceptance theorem is partial correctness plus
/// safety at every fuel; the cross-check's elaborated TYPE is EXACTLY the
/// structural A4-shaped `ir_it_ag_correct`'s; and both the table's precondition
/// and the theorem's premises are inhabited, with the `ret` arm exercised.
#[test]
fn the_infer_type_instance_reproduces_the_structural_a4_shape_through_the_device() {
    let spec = clean_verify::test_utils::build_spec_with_stack();
    assert_eq!(clean_verify::spec::IT_SCTR_NAMES.len(), IT_SCTR_DECLS);
    assert_eq!(clean_verify::spec::IT_PC_NAMES.len(), IT_PC_DECLS);
    assert_eq!(clean_verify::spec::IT_PC_NAMES[0], "IRItIn");
    assert!(
        spec.env()
            .get_inductive(&Name::from_string("IRItIn"))
            .is_some(),
        "the table's index type must be registered"
    );
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::IT_SCTR_NAMES);
    assert_kernel_checked_axiom_free(&spec, &clean_verify::spec::IT_PC_NAMES[1..]);
    for name in clean_verify::spec::IT_SCTR_NAMES
        .iter()
        .chain(&clean_verify::spec::IT_PC_NAMES[1..])
    {
        let src = &spec.definitions()[*name].type_src;
        assert!(
            !src.contains("nat_strong_rec") && !src.contains("Le.rec"),
            "{name}: the device must not need strong induction"
        );
    }

    let elab_ty = |name: &str| {
        spec.definitions()
            .get(name)
            .and_then(|d| d.elaborated_type.clone())
            .unwrap_or_else(|| panic!("{name} must carry an elaborated type"))
    };
    assert!(
        elab_ty("ir_it_pc_a4_crosscheck") == elab_ty("ir_it_ag_correct"),
        "the cross-check must state EXACTLY the structural A4-shaped theorem"
    );

    // The body's local obligation: both callees through CONTRACTS at n, the
    // body's contract at succ n, over the abstract module.
    let sseg = statement(&spec, "ir_it_top_sseg");
    for needle in [
        "(ihh : ir_ctr_at (IRModule.mk fs gs) (ir_it_hb_entry g1 p",
        "-> ir_ctr_at (IRModule.mk fs gs) (ir_it_fast_entry g2 p q mem1 na1) (QF p q mem1 na1) n)",
        ": ir_ctr_at (IRModule.mk fs gs) (ir_it_ag_entry p q mem na) (ir_it_tpost QH QF p q mem na) (Nat.succ n) ",
    ] {
        assert!(
            sseg.contains(needle),
            "ir_it_top_sseg must carry `{needle}`: {sseg}"
        );
    }
    // The table is a MUTUAL group: the callee members' local obligations are
    // premises that may consume the whole group at n.
    let local = statement(&spec, "ir_it_local");
    for needle in [
        "(hloc_hb : forall (n : Nat), (forall (a : IRItIn), ir_it_in_pre PT PH PF a ->",
        "(hloc_fast : forall (n : Nat), (forall (a : IRItIn), ir_it_in_pre PT PH PF a ->",
    ] {
        assert!(
            local.contains(needle),
            "the callee members' local obligations must be group-relative premises: {local}"
        );
    }
    assert!(spec.definitions()["ir_it_ctr"]
        .type_src
        .contains("ir_ctr_group_sound (IRModule.mk fs gs) IRItIn"));

    // The acceptance theorem: every fuel, no cost premise, the transport post.
    let pc = statement(&spec, "ir_it_pc");
    assert!(
        pc.contains("(fuel : Nat)")
            && pc.contains(
                ": ir_it_pc_ok (ir_it_tpost QH QF p q (ir_mem_concat (ir_globals_mem gs) mem0) na) \
                 (ir_eval fuel (IRModule.mk fs gs) ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) mem0 na)"
            )
            && !pc.contains("Le "),
        "ir_it_pc must be partial correctness plus safety at every fuel: {pc}"
    );
    // The cross-check takes only TERMINATION from the structural chain.
    let cc = &spec.definitions()["ir_it_pc_a4_crosscheck"].type_src;
    assert!(cc.contains("ir_it_ag_returns") && !cc.contains("(ir_it_ag_correct "));
    assert!(cc.contains("(ir_it_pc_of_exact "));

    // The refusals: the switch default and the Err arm meet no contract.
    assert!(statement(&spec, "ir_it_unreachable_refutes")
        .contains("(IRFrame.mk ir_d0 ir_d2 Nat.zero loc d)"));
    let err = statement(&spec, "ir_it_err_arm_refutes");
    assert!(
        err.contains("(IRScalar.vcons (IRScalar.int_ ir_d1)")
            && err.contains(" Q ir_d9) (C : Prop) "),
        "the Err-arm refusal must be stated at an Err answer (tag 1) and budget nine: {err}"
    );

    // Non-vacuity: the precondition and the premises are inhabited, and the
    // ret arm is exercised at the cost.
    assert!(spec.definitions()["ir_it_in_pre_witness"]
        .type_src
        .contains("(ir_it_in_itd p q)"));
    for (w, needle) in [
        ("ir_it_pc_witness_itd", "(ir_it_ag_hc1_at_itd spc p"),
        ("ir_it_pc_crosscheck_itd", "(Le.refl ir_d14)"),
    ] {
        assert!(
            spec.definitions()[w].type_src.contains(needle),
            "{w} must rest on the structural chain's own witnesses: missing `{needle}`"
        );
    }
}
