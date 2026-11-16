// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked real fetch/step endpoints. These hand-built module fixtures do not
//! establish source translation or native/provider fidelity.

use super::*;
use clean_kernel::Name;

fn checked(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).unwrap();
    assert!(!definition.is_axiom);
    assert!(definition.elaborated_value.is_some());
    spec.verify_definition(name).unwrap();
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(source, "Actual byte fetch/step consumer")
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    checked(spec, name);
}

fn reject(spec: &mut Specification, source: &str) {
    let error = spec
        .add_recursive_def(source, "Invalid fetched-step claim")
        .expect_err("invalid endpoint must fail admission");
    crate::test_utils::assert_type_mismatch_rejection(&error, "fetched-step claim");
}

fn list(ty: &str, values: &[String]) -> String {
    values
        .iter()
        .rev()
        .fold(format!("(@IRList.nil {ty})"), |tail, value| {
            format!("(@IRList.cons {ty} {value} {tail})")
        })
}

const TY: &str = "(IRTy.array_ (IRTy.uint_ 8) 16)";
const PTR_TYPES: &str = "(@IRList.cons IRTy IRTy.ptr_ (@IRList.nil IRTy))";
const RESULTS: &str = "(@IRList.cons Nat 99 (@IRList.nil Nat))";
const LOCALS: &str =
    "(@IRList.cons IRBinding (IRBinding.mk 40 (IRScalar.bool_ Bool.true)) (@IRList.nil IRBinding))";
const CURRENT: &str = "(IRFrame.mk 9 7 2 (@IRList.cons IRBinding (IRBinding.mk 40 (IRScalar.bool_ Bool.true)) (@IRList.nil IRBinding)) (@IRList.nil Nat))";
const TAIL: &str = "(@IRList.cons IRFrame (IRFrame.mk 3 4 5 (@IRList.nil IRBinding) (@IRList.nil Nat)) (@IRList.nil IRFrame))";
const LEGACY: &str = "(@IRList.nil IRMemSlot)";
const OWNERS: &str = "(@IRList.cons Nat 1 (@IRList.nil Nat))";
const ROWS: &str = "(@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 8 1 Bool.true)
  (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 48 8 3 Bool.false)
    (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 32 8 0 Bool.true) (@IRList.nil IRByteAllocationV1))))";

fn frame(fid: u64, block: u64, pc: u64) -> String {
    format!("(IRFrame.mk {fid} {block} {pc} {LOCALS} (@IRList.nil Nat))")
}

fn machine(frame: &str) -> String {
    format!("(IRMachine.mk (@IRList.cons IRFrame {frame} {TAIL}) {LEGACY} 1)")
}

fn world() -> String {
    format!("(@IRByteWorldV1.mk Nat (IRByteMemoryV1.mk {ROWS} bytes 65) host (@IRList.cons Nat 2 {OWNERS}) 5)")
}

fn node() -> String {
    format!("(IRNode.mk (IRInst.alloca {TY} (@IROption.none Nat)) {RESULTS})")
}

fn block(node: &str) -> String {
    let nodes = list("IRNode", &[
        "(IRNode.mk (IRInst.const_ IRTy.bool_ (IRConst.bool_ Bool.true)) (@IRList.cons Nat 11 (@IRList.nil Nat)))".into(),
        "(IRNode.mk (IRInst.const_ (IRTy.int_ 64) (IRConst.int_ 1)) (@IRList.cons Nat 12 (@IRList.nil Nat)))".into(),
        node.into(),
        format!("(IRNode.mk (IRInst.ret {RESULTS}) (@IRList.nil Nat))"),
    ]);
    format!("(IRBlock.mk 7 (@IRList.nil Nat) {nodes})")
}

fn function(block: &str) -> String {
    format!("(IRFunc.mk 9 (@IRList.cons Nat 40 (@IRList.nil Nat)) 7 (@IRList.cons IRBlock {block} (@IRList.nil IRBlock)))")
}

fn site(fid: u64, block: u64, pc: u64, results: &str) -> String {
    format!("(IRByteSiteV1.mk {fid} {block} {pc} 8 1 {results})")
}

fn context(function: &str, site: &str) -> String {
    format!("(IRByteContextV1.mk
      (IRModule.mk (@IRList.cons IRFunc {function} (@IRList.nil IRFunc)) (@IRList.nil IRGlobal))
      (@IRList.cons IRByteLayoutV1 (IRByteLayoutV1.mk {TY} 16 1 (@IRList.nil IRTy) (@IRList.nil Nat)) (@IRList.nil IRByteLayoutV1))
      (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1)
      (@IRList.cons IRByteSiteV1 {site} (@IRList.nil IRByteSiteV1)))")
}

fn fixture(spec: &mut Specification) {
    for (name, ty, value) in [
        ("fetch_node", "IRNode", node()),
        ("fetch_block", "IRBlock", block("fetch_node")),
        ("fetch_function", "IRFunc", function("fetch_block")),
        ("fetch_site", "IRByteSiteV1", site(9, 7, 2, PTR_TYPES)),
        (
            "fetch_context",
            "IRByteContextV1",
            context("fetch_function", "fetch_site"),
        ),
    ] {
        add(spec, name, &format!("def {name} : {ty} := {value}"));
    }
    for (name, ty, actual, value) in [
        (
            "fetch_function_found",
            "IRFunc",
            "ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 fetch_context)) 9".into(),
            "fetch_function".into(),
        ),
        (
            "fetch_block_found",
            "IRBlock",
            "ir_block_find (ir_func_blocks fetch_function) 7".into(),
            "fetch_block".into(),
        ),
        (
            "fetch_node_found",
            "IRNode",
            "ir_nodes_get (ir_block_nodes fetch_block) 2".into(),
            "fetch_node".into(),
        ),
        (
            "fetch_site_found",
            "IRByteSiteV1",
            "ir_byte_site_v1 fetch_context 9 7 2".into(),
            "fetch_site".into(),
        ),
        (
            "fetch_layout_found",
            "IRByteLayoutV1",
            format!("ir_byte_layout_v1 fetch_context {TY}"),
            format!("(IRByteLayoutV1.mk {TY} 16 1 (@IRList.nil IRTy) (@IRList.nil Nat))"),
        ),
    ] {
        add(
            spec,
            name,
            &format!(
                "def {name} : @Eq (IROption {ty}) ({actual}) (@IROption.some {ty} {value}) :=
          @Eq.refl (IROption {ty}) (@IROption.some {ty} {value})"
            ),
        );
    }
}

fn expected() -> String {
    let values = "(@IRList.cons IRScalar (IRScalar.ptr_ 72) (@IRList.nil IRScalar))";
    format!("(@IRByteConfigV1.running Nat
      (IRMachine.mk (@IRList.cons IRFrame (ir_frame_advance (ir_frame_set_many {CURRENT} {RESULTS} {values})) {TAIL}) {LEGACY} 1)
      (ir_byte_with_memory_v1 Nat {} (ir_byte_fresh_memory_v1 {ROWS} bytes 72 16 2)))", world())
}

fn step(ctx: &str, current: &str) -> String {
    format!(
        "(ir_byte_step_v1 Nat {ctx} providers (@IRByteConfigV1.running Nat {} {}))",
        machine(current),
        world()
    )
}

#[test]
fn byte_fetched_step_roots_are_public_checked_and_axiom_free() {
    crate::test_utils::run_with_stack(|| {
        let spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
        for (name, _) in laws() {
            checked(&spec, name);
        }
    });
}

fn arithmetic_frame(left: &str, right: &str) -> String {
    format!("(IRFrame.mk 9 7 2 (@IRList.cons IRBinding (IRBinding.mk 40 ({left}))
      (@IRList.cons IRBinding (IRBinding.mk 78 ({right})) (@IRList.nil IRBinding))) (@IRList.nil Nat))")
}

fn arithmetic_context(instruction: &str, results: &str, result_types: &str) -> String {
    let node = format!("(IRNode.mk ({instruction}) {results})");
    let body = block(&node);
    let function = format!("(IRFunc.mk 9 (@IRList.cons Nat 40 (@IRList.cons Nat 78 (@IRList.nil Nat))) 7 (@IRList.cons IRBlock {body} (@IRList.nil IRBlock)))");
    context(&function, &site(9, 7, 2, result_types))
}

#[test]
fn byte_binop_fetched_faults_and_float_profile_refusals_preserve_world() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
        let integers = "(@IRList.cons IRTy (IRTy.int_ 4) (@IRList.nil IRTy))";
        for (case, (op, left, right, fault)) in [
            ("udiv", 3, 0, "div_zero"),
            ("sdiv", 3, 0, "div_zero"),
            ("urem", 3, 0, "div_zero"),
            ("srem", 3, 0, "div_zero"),
            ("sdiv", 8, 15, "div_overflow"),
            ("srem", 8, 15, "div_overflow"),
            ("shl", 1, 4, "shift_oob"),
            ("lshr", 1, 4, "shift_oob"),
            ("ashr", 1, 4, "shift_oob"),
        ]
        .into_iter()
        .enumerate()
        {
            let ctx = arithmetic_context(
                &format!("IRInst.binop IRBinOp.{op} (IRTy.int_ 4) 40 78"),
                RESULTS,
                integers,
            );
            let actual = step(
                &ctx,
                &arithmetic_frame(
                    &format!("IRScalar.int_ {left}"),
                    &format!("IRScalar.int_ {right}"),
                ),
            );
            let expected = format!(
                "(@IRByteConfigV1.halted Nat (IROutcome.ub IRFault.{fault}) {})",
                world()
            );
            add(&mut spec, &format!("fetch_binop_fault_{case}"), &format!(
                "def fetch_binop_fault_{case} (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {actual} {expected} := @Eq.refl (IRByteConfigV1 Nat) {expected}"));
        }
        for op in ["fadd", "fsub", "fmul", "fdiv", "frem", "fmin", "fmax"] {
            let ctx = arithmetic_context(
                &format!("IRInst.binop IRBinOp.{op} (IRTy.float_ 64) 40 78"),
                RESULTS,
                "(@IRList.cons IRTy (IRTy.float_ 64) (@IRList.nil IRTy))",
            );
            let actual = step(
                &ctx,
                &arithmetic_frame("IRScalar.float_ 0", "IRScalar.float_ 0"),
            );
            let expected = format!(
                "(@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) {})",
                world()
            );
            add(&mut spec, &format!("fetch_binop_float_refuses_{op}"), &format!(
                "def fetch_binop_float_refuses_{op} (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {actual} {expected} := @Eq.refl (IRByteConfigV1 Nat) {expected}"));
        }
    });
}

#[test]
fn byte_binop_fault_precedence_is_carrier_then_evaluator_then_result() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
        let one_type = "(@IRList.cons IRTy (IRTy.int_ 4) (@IRList.nil IRTy))";
        let two_types =
            "(@IRList.cons IRTy (IRTy.int_ 4) (@IRList.cons IRTy (IRTy.int_ 4) (@IRList.nil IRTy)))";
        let two_results = "(@IRList.cons Nat 99 (@IRList.cons Nat 100 (@IRList.nil Nat)))";
        for (case, (op, left, right, results, types, outcome)) in [
            (
                "udiv",
                16,
                0,
                RESULTS,
                one_type,
                "IROutcome.type_error IRFault.bad_field",
            ),
            (
                "shl",
                1,
                16,
                RESULTS,
                one_type,
                "IROutcome.type_error IRFault.bad_field",
            ),
            (
                "udiv",
                3,
                0,
                two_results,
                two_types,
                "IROutcome.ub IRFault.div_zero",
            ),
            (
                "shl",
                1,
                4,
                two_results,
                two_types,
                "IROutcome.ub IRFault.shift_oob",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let ctx = arithmetic_context(
                &format!("IRInst.binop IRBinOp.{op} (IRTy.int_ 4) 40 78"),
                results,
                types,
            );
            let actual = step(
                &ctx,
                &arithmetic_frame(
                    &format!("IRScalar.int_ {left}"),
                    &format!("IRScalar.int_ {right}"),
                ),
            );
            let expected = format!("(@IRByteConfigV1.halted Nat ({outcome}) {})", world());
            add(&mut spec, &format!("fetch_binop_precedence_{case}"), &format!(
                "def fetch_binop_precedence_{case} (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {actual} {expected} := @Eq.refl (IRByteConfigV1 Nat) {expected}"));
        }
    });
}

#[test]
fn byte_add_sub_fetched_steps_reject_carriers_widths_and_result_lanes() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
        let integers = "(@IRList.cons IRTy (IRTy.uint_ 64) (@IRList.nil IRTy))";
        for op in ["add", "sub"] {
            for (case, (ty, left, right, rhs, results, result_types)) in [
                ("IRTy.uint_ 64", "IRScalar.bool_ Bool.true", "IRScalar.int_ 1", 78, RESULTS, integers),
                ("IRTy.uint_ 64", "IRScalar.int_ 1", "IRScalar.bool_ Bool.false", 78, RESULTS, integers),
                ("IRTy.uint_ 8", "IRScalar.int_ 256", "IRScalar.int_ 0", 78, RESULTS, integers),
                ("IRTy.uint_ 8", "IRScalar.int_ 0", "IRScalar.int_ 256", 78, RESULTS, integers),
                ("IRTy.uint_ 64", "IRScalar.int_ 1", "IRScalar.int_ 0", 999, RESULTS, integers),
                ("IRTy.uint_ 0", "IRScalar.int_ 0", "IRScalar.int_ 0", 78, RESULTS, integers),
                ("IRTy.int_ 129", "IRScalar.int_ 0", "IRScalar.int_ 0", 78, RESULTS, integers),
                ("IRTy.bool_", "IRScalar.int_ 0", "IRScalar.int_ 0", 78, RESULTS, integers),
                ("IRTy.uint_ 64", "IRScalar.int_ 1", "IRScalar.int_ 0", 78, RESULTS, "(@IRList.cons IRTy IRTy.bool_ (@IRList.nil IRTy))"),
                ("IRTy.uint_ 64", "IRScalar.int_ 1", "IRScalar.int_ 0", 78, "(@IRList.nil Nat)", "(@IRList.nil IRTy)"),
                ("IRTy.uint_ 64", "IRScalar.int_ 1", "IRScalar.int_ 0", 78, "(@IRList.cons Nat 99 (@IRList.cons Nat 100 (@IRList.nil Nat)))", "(@IRList.cons IRTy (IRTy.uint_ 64) (@IRList.cons IRTy (IRTy.uint_ 64) (@IRList.nil IRTy)))"),
            ].into_iter().enumerate() {
                let instruction = format!("IRInst.binop IRBinOp.{op} ({ty}) 40 {rhs}");
                let ctx = arithmetic_context(&instruction, results, result_types);
                let actual = step(&ctx, &arithmetic_frame(left, right));
                let expected = format!("(@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) {})", world());
                add(&mut spec, &format!("fetch_arithmetic_refuses_{op}_{case}"), &format!(
                    "def fetch_arithmetic_refuses_{op}_{case} (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {actual} {expected} := @Eq.refl (IRByteConfigV1 Nat) {expected}"));
            }
        }
        // Byte-native two-result Overflow is a distinct instruction. These
        // unchanged malformed fixtures reject the Boolean input, not a
        // successfully executed arithmetic result with its flag erased.
        for (case, instruction) in [
            "IRInst.overflow IROverflowOp.addoverflow (IRTy.uint_ 64) 40 78",
            "IRInst.overflow IROverflowOp.suboverflow (IRTy.uint_ 64) 40 78",
        ]
        .into_iter()
        .enumerate()
        {
            let ctx = arithmetic_context(instruction, RESULTS, integers);
            let actual = step(
                &ctx,
                &arithmetic_frame("IRScalar.bool_ Bool.true", "IRScalar.int_ 0"),
            );
            let expected = format!(
                "(@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.not_int) {})",
                world()
            );
            add(&mut spec, &format!("fetch_overflow_not_int_{case}"), &format!(
                "def fetch_overflow_not_int_{case} (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {actual} {expected} := @Eq.refl (IRByteConfigV1 Nat) {expected}"));
        }
    });
}

#[test]
fn byte_add_sub_fetched_step_proof_is_bound_to_actual_instruction_and_world() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
        let integers = "(@IRList.cons IRTy (IRTy.uint_ 64) (@IRList.nil IRTy))";
        let current = arithmetic_frame("IRScalar.int_ 250", "IRScalar.int_ 10");
        let ctx = arithmetic_context(
            "IRInst.binop IRBinOp.add (IRTy.uint_ 64) 40 78",
            RESULTS,
            integers,
        );
        let actual = step(&ctx, &current);
        let expected = format!("(@IRByteConfigV1.running Nat
          (IRMachine.mk (@IRList.cons IRFrame (ir_frame_advance (ir_frame_set_many {current} {RESULTS}
            (@IRList.cons IRScalar (IRScalar.int_ 260) (@IRList.nil IRScalar)))) {TAIL}) {LEGACY} 1) {})", world());
        add(&mut spec, "fetch_arithmetic_exact", &format!(
            "def fetch_arithmetic_exact (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {actual} {expected} := @Eq.refl (IRByteConfigV1 Nat) {expected}"));
        for (case, instruction, results) in [
            (
                "opcode",
                "IRInst.binop IRBinOp.sub (IRTy.uint_ 64) 40 78",
                RESULTS,
            ),
            (
                "operand",
                "IRInst.binop IRBinOp.add (IRTy.uint_ 64) 40 40",
                RESULTS,
            ),
            (
                "type",
                "IRInst.binop IRBinOp.add (IRTy.uint_ 8) 40 78",
                RESULTS,
            ),
            (
                "destination",
                "IRInst.binop IRBinOp.add (IRTy.uint_ 64) 40 78",
                "(@IRList.cons Nat 100 (@IRList.nil Nat))",
            ),
        ] {
            let changed = step(
                &arithmetic_context(instruction, results, integers),
                &current,
            );
            reject(&mut spec, &format!(
                "def fetch_arithmetic_wrong_{case} (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {changed} {expected} := fetch_arithmetic_exact providers bytes host"));
        }
        let changed = step(
            &ctx,
            &arithmetic_frame("IRScalar.int_ 249", "IRScalar.int_ 10"),
        );
        reject(&mut spec, &format!(
            "def fetch_arithmetic_wrong_input (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {changed} {expected} := fetch_arithmetic_exact providers bytes host"));
        let changed_world = expected.replace("bytes 65", "bytes 66");
        assert_ne!(changed_world, expected);
        reject(&mut spec, &format!(
            "def fetch_arithmetic_wrong_world (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {actual} {changed_world} := fetch_arithmetic_exact providers bytes host"));
    });
}

#[test]
fn byte_fetched_alloca_uses_real_sparse_ids_pc_and_preserves_world() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
        fixture(&mut spec);
        let high = "(@And.intro (Nat.lt 24 65)
          (ir_byte_high_water_v1 (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 48 8 3 Bool.false)
            (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 32 8 0 Bool.true) (@IRList.nil IRByteAllocationV1))) 65)
          (Nat.le_add_right 25 40)
          (@And.intro (Nat.lt 56 65)
            (ir_byte_high_water_v1 (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 32 8 0 Bool.true) (@IRList.nil IRByteAllocationV1)) 65)
            (Nat.le_add_right 57 8)
            (@And.intro (Nat.lt 40 65) True (Nat.le_add_right 41 24) True.intro)))".to_string();
        let args = format!("Nat {ROWS} bytes 65 host 2 {OWNERS} 5 {CURRENT} {TAIL} {LEGACY} 1
          fetch_context providers 99 1 fetch_function fetch_block (Nat.zero_lt_succ 64)
          (Nat.le_add_right 89 18446744073709551527) {high} fetch_layout_found (@Eq.refl Bool Bool.true)
          fetch_function_found fetch_block_found fetch_node_found fetch_site_found");
        let actual = step("fetch_context", CURRENT);
        let result = expected();
        add(
            &mut spec,
            "fetch_actual_exact",
            &format!(
                "def fetch_actual_exact
          (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) :
          @Eq (IRByteConfigV1 Nat) {actual} {result} := ir_byte_step_frame16_exact_v1 {args}"
            ),
        );
        let predicate = "(fun (c : IRByteConfigV1 Nat) => @IRByteConfigV1.rec Nat (fun (_ : IRByteConfigV1 Nat) => Prop)
          (fun (s : IRMachine) (w : IRByteWorldV1 Nat) => @Eq Bool (ir_byte_world_valid_v1 Nat s w) Bool.true)
          (fun (_ : IROutcome) (_ : IRByteWorldV1 Nat) => False) c)";
        add(
            &mut spec,
            "fetch_actual_valid",
            &format!(
                "def fetch_actual_valid
          (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) :
          {predicate} {actual} := ir_byte_step_frame16_world_v1 {args}"
            ),
        );
        // A wrong owner can still pass the bookkeeping invariant; the exact
        // fetched execution theorem must reject it nevertheless.
        let wrong = result.replace(
            &format!("(ir_byte_fresh_memory_v1 {ROWS} bytes 72 16 2)"),
            &format!("(ir_byte_fresh_memory_v1 {ROWS} bytes 72 16 1)"),
        );
        reject(
            &mut spec,
            &format!(
                "def fetch_wrong_owner
          (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) :
          @Eq (IRByteConfigV1 Nat) {actual} {wrong} := fetch_actual_exact providers bytes host"
            ),
        );
    });
}

#[test]
fn byte_fetched_step_mutations_follow_actual_faults_not_shadow_metadata() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
        fixture(&mut spec);
        let scenarios = [
            (
                "wrong_function",
                "fetch_context".into(),
                frame(10, 7, 2),
                "IROutcome.stuck IRFault.no_func",
            ),
            (
                "wrong_block",
                "fetch_context".into(),
                frame(9, 8, 2),
                "IROutcome.stuck IRFault.no_block",
            ),
            (
                "wrong_pc",
                "fetch_context".into(),
                frame(9, 7, 8),
                "IROutcome.stuck IRFault.fetch_past_end",
            ),
            (
                "wrong_site_function",
                context("fetch_function", &site(10, 7, 2, PTR_TYPES)),
                CURRENT.into(),
                "IROutcome.stuck IRFault.fetch_past_end",
            ),
            (
                "wrong_site_block",
                context("fetch_function", &site(9, 8, 2, PTR_TYPES)),
                CURRENT.into(),
                "IROutcome.stuck IRFault.fetch_past_end",
            ),
            (
                "wrong_site_pc",
                context("fetch_function", &site(9, 7, 3, PTR_TYPES)),
                CURRENT.into(),
                "IROutcome.stuck IRFault.fetch_past_end",
            ),
            (
                "wrong_arity",
                context("fetch_function", &site(9, 7, 2, "(@IRList.nil IRTy)")),
                CURRENT.into(),
                "IROutcome.type_error IRFault.bad_field",
            ),
        ];
        for (label, ctx, current, outcome) in scenarios {
            let actual = step(&ctx, &current);
            let failed = format!("(@IRByteConfigV1.halted Nat ({outcome}) {})", world());
            add(
                &mut spec,
                &format!("fetch_observed_{label}"),
                &format!(
                    "def fetch_observed_{label}
              (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) :
              @Eq (IRByteConfigV1 Nat) {actual} {failed} := @Eq.refl (IRByteConfigV1 Nat) {failed}"
                ),
            );
            reject(
                &mut spec,
                &format!(
                    "def fetch_bad_{label}
              (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) :
              @Eq (IRByteConfigV1 Nat) {actual} {} := @Eq.refl (IRByteConfigV1 Nat) {}",
                    expected(),
                    expected()
                ),
            );
        }
        // Mutate the actual instruction, retaining the same metadata. It now
        // produces a null pointer without allocating; the old result must fail.
        let changed_node = format!("(IRNode.mk (IRInst.const_ IRTy.ptr_ IRConst.null_) {RESULTS})");
        let changed_ctx = context(&function(&block(&changed_node)), "fetch_site");
        let actual = step(&changed_ctx, CURRENT);
        let null_values = "(@IRList.cons IRScalar IRScalar.nullptr_ (@IRList.nil IRScalar))";
        let changed = format!("(@IRByteConfigV1.running Nat
          (IRMachine.mk (@IRList.cons IRFrame (ir_frame_advance (ir_frame_set_many {CURRENT} {RESULTS} {null_values})) {TAIL}) {LEGACY} 1) {})", world());
        add(
            &mut spec,
            "fetch_changed_instruction_observed",
            &format!(
                "def fetch_changed_instruction_observed
          (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) :
          @Eq (IRByteConfigV1 Nat) {actual} {changed} := @Eq.refl (IRByteConfigV1 Nat) {changed}"
            ),
        );
        reject(
            &mut spec,
            &format!(
                "def fetch_changed_instruction_bad
          (providers : IRByteProvidersV1 Nat) (bytes : Nat -> IROption Nat) (host : Nat) :
          @Eq (IRByteConfigV1 Nat) {actual} {} := @Eq.refl (IRByteConfigV1 Nat) {}",
                expected(),
                expected()
            ),
        );
    });
}
