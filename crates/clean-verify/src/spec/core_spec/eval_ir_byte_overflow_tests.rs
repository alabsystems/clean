// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public-constructor and real fetched-step controls. These are operational
//! kernel fixtures, not Rust extraction, native execution or panic proofs.

use crate::spec::Specification;
use clean_kernel::Name;

const CONFIG: &str = "IRByteConfigV1 Nat";
const RESULTS: &str = "(IRList.cons Nat 99 (IRList.cons Nat 100 (IRList.nil Nat)))";
const ROOTS: &[&str] = &[
    "ir_byte_overflow_ints_v1",
    "ir_byte_overflow_vals_v1",
    "ir_byte_overflow_exec_v1",
    "ir_byte_overflow_uint_transfer_v1",
    "ir_byte_overflow_int_transfer_v1",
    "ir_byte_step_overflow_uint_v1",
    "ir_byte_step_overflow_int_v1",
];

fn checked(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).expect("registered definition");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(name)
        .expect("strict kernel acceptance");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn register(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Checked-arithmetic operational fixture")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
}

fn check(spec: &mut Specification, name: &str, actual: &str, expected: &str) {
    register(
        spec,
        &format!(
            "def {name} : Eq ({CONFIG}) ({actual}) ({expected}) := Eq.refl ({CONFIG}) ({expected})"
        ),
    );
    checked(spec, name);
}

fn reject_source(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Deliberately forged arithmetic endpoint")
        .expect_err("forged proof must fail");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn reject(spec: &mut Specification, name: &str, actual: &str, wrong: &str) {
    reject_source(
        spec,
        name,
        &format!("def {name} : Eq ({CONFIG}) ({actual}) ({wrong}) := Eq.refl ({CONFIG}) ({wrong})"),
    );
}

fn types(ty: &str) -> String {
    format!("(IRList.cons IRTy ({ty}) (IRList.cons IRTy IRTy.bool_ (IRList.nil IRTy)))")
}

fn instruction(op: &str, ty: &str) -> String {
    format!("IRInst.overflow IROverflowOp.{op} ({ty}) 40 78")
}

fn block(inst: &str, results: &str) -> String {
    format!(
        "(IRBlock.mk 7 (IRList.nil Nat)
  (IRList.cons IRNode (IRNode.mk IRInst.unreachable (IRList.nil Nat))
    (IRList.cons IRNode (IRNode.mk IRInst.unreachable (IRList.nil Nat))
      (IRList.cons IRNode (IRNode.mk ({inst}) {results}) (IRList.nil IRNode)))))"
    )
}

fn function(block: &str) -> String {
    format!(
        "(IRFunc.mk 9 (IRList.cons Nat 40 (IRList.cons Nat 78 (IRList.nil Nat))) 7
  (IRList.cons IRBlock {block} (IRList.nil IRBlock)))"
    )
}

fn site(types: &str, pc: u64) -> String {
    format!("(IRByteSiteV1.mk 9 7 {pc} 0 1 {types})")
}

fn context(inst: &str, results: &str, types: &str, pc: u64) -> String {
    format!(
        "(IRByteContextV1.mk (IRModule.mk
  (IRList.cons IRFunc {} (IRList.nil IRFunc)) (IRList.nil IRGlobal))
  (IRList.nil IRByteLayoutV1) (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1)
  (IRList.cons IRByteSiteV1 {} (IRList.nil IRByteSiteV1)))",
        function(&block(inst, results)),
        site(types, pc)
    )
}

fn frame(a: &str, b: &str) -> String {
    format!("(ov_frame ({a}) ({b}))")
}

fn actual(ctx: &str, frame: &str) -> String {
    format!(
        "ir_byte_step_v1 Nat ({ctx}) ov_providers
  (IRByteConfigV1.running Nat (ov_machine {frame}) ov_world)"
    )
}

fn expected(frame: &str, results: &str, word: u128, flag: bool) -> String {
    format!(
        "IRByteConfigV1.running Nat (ov_machine
  (ir_frame_advance (ir_frame_set_many {frame} {results}
    (IRList.cons IRScalar (IRScalar.int_ {word})
      (IRList.cons IRScalar (IRScalar.bool_ Bool.{flag}) (IRList.nil IRScalar)))))) ov_world"
    )
}

fn fault(kind: &str) -> String {
    format!("IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.{kind}) ov_world")
}

fn fixture() -> Specification {
    let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1()
        .expect("actual public ByteV1 constructor");
    for source in [
        r"def ov_tail : IRList IRFrame := IRList.cons IRFrame
  (IRFrame.mk 3 4 5 (IRList.cons IRBinding (IRBinding.mk 777 (IRScalar.int_ 88)) (IRList.nil IRBinding))
    (IRList.cons Nat 55 (IRList.nil Nat))) (IRList.nil IRFrame)",
        r"def ov_frame (a b : IRScalar) : IRFrame := IRFrame.mk 9 7 2
  (IRList.cons IRBinding (IRBinding.mk 40 a)
    (IRList.cons IRBinding (IRBinding.mk 78 b)
      (IRList.cons IRBinding (IRBinding.mk 99 (IRScalar.int_ 77))
        (IRList.cons IRBinding (IRBinding.mk 100 (IRScalar.bool_ Bool.true)) (IRList.nil IRBinding)))))
  (IRList.cons Nat 123 (IRList.nil Nat))",
        r"def ov_machine (frame : IRFrame) : IRMachine := IRMachine.mk
  (IRList.cons IRFrame frame ov_tail) (IRList.nil IRMemSlot) 17",
        r"def ov_allocs : IRList IRByteAllocationV1 :=
IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 8 7 Bool.true)
  (IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 32 8 0 Bool.true)
    (IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 48 8 5 Bool.false) (IRList.nil IRByteAllocationV1)))",
        r"def ov_memory : IRByteMemoryV1 := IRByteMemoryV1.mk ov_allocs
  (ir_byte_write_word_v1 (fun (_ : Nat) => IROption.none Nat) 32 8 173) 128",
        r"def ov_owners : IRList Nat := IRList.cons Nat 7 (IRList.cons Nat 1 (IRList.nil Nat))",
        r"def ov_world : IRByteWorldV1 Nat := IRByteWorldV1.mk Nat ov_memory 123 ov_owners 9",
        r"def ov_providers : IRByteProvidersV1 Nat :=
fun (_ : Nat) (_ : IRList IRScalar) (mem : IRByteMemoryV1) (host : Nat) =>
  IRByteImportResultV1.mk Nat (IROutcome.stuck IRFault.no_func) mem host",
    ] {
        register(&mut spec, source);
    }
    spec
}

fn arguments(op: &str, kind: &str, width: u64, a: u128, b: u128) -> String {
    let ty = format!("IRTy.{kind}_ {width}");
    let inst = instruction(op, &ty);
    let types = types(&ty);
    let block = block(&inst, RESULTS);
    let function = function(&block);
    let site = site(&types, 2);
    let frame = frame(&format!("IRScalar.int_ {a}"), &format!("IRScalar.int_ {b}"));
    format!(
        "Nat {} ov_providers {frame} ov_tail (IRList.nil IRMemSlot) 17 ov_world
  40 78 {RESULTS} {site} {function} {block} IROverflowOp.{op} {width} {a} {b}
  (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)
  (Eq.refl Bool Bool.true)
  (Eq.refl IRScalar (IRScalar.int_ {a})) (Eq.refl IRScalar (IRScalar.int_ {b}))
  (Eq.refl (IROption IRFunc) (IROption.some IRFunc {function}))
  (Eq.refl (IROption IRBlock) (IROption.some IRBlock {block}))
  (Eq.refl (IROption IRNode) (IROption.some IRNode (IRNode.mk ({inst}) {RESULTS})))
  (Eq.refl (IROption IRByteSiteV1) (IROption.some IRByteSiteV1 {site}))
  (Eq.refl Bool Bool.true)",
        context(&inst, RESULTS, &types, 2)
    )
}

#[test]
fn byte_overflow_fetched_arithmetic_binds_both_lanes_and_generic_laws() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for name in ROOTS {
            checked(&spec, name);
        }
        for (index, (op, kind, width, a, b, word, flag)) in [
            ("addoverflow", "uint", 8, 255, 1, 0, true),
            ("addoverflow", "uint", 8, 3, 5, 8, false),
            ("suboverflow", "uint", 8, 0, 1, 255, true),
            ("suboverflow", "uint", 8, 3, 1, 2, false),
            ("muloverflow", "uint", 8, 16, 16, 0, true),
            ("muloverflow", "uint", 8, 3, 5, 15, false),
            ("addoverflow", "int", 8, 127, 1, 128, true),
            ("addoverflow", "int", 8, 128, 255, 127, true),
            ("addoverflow", "int", 8, 128, 1, 129, false),
            ("suboverflow", "int", 8, 128, 1, 127, true),
            ("suboverflow", "int", 8, 128, 255, 129, false),
            ("muloverflow", "int", 8, 128, 255, 128, true),
            ("muloverflow", "int", 8, 128, 1, 128, false),
            ("suboverflow", "uint", 64, 3, 1, 2, false),
            ("addoverflow", "uint", 128, u128::MAX, 1, 0, true),
        ]
        .into_iter()
        .enumerate()
        {
            let ty = format!("IRTy.{kind}_ {width}");
            let frame = frame(&format!("IRScalar.int_ {a}"), &format!("IRScalar.int_ {b}"));
            let ctx = context(&instruction(op, &ty), RESULTS, &types(&ty), 2);
            let actual = actual(&ctx, &frame);
            let after = expected(&frame, RESULTS, word, flag);
            check(&mut spec, &format!("ov_vector_{index}"), &actual, &after);
            let name = format!("ov_fetched_law_{index}");
            register(
                &mut spec,
                &format!(
                    "def {name} : Eq ({CONFIG}) ({actual}) ({after}) :=
ir_byte_step_overflow_{kind}_v1 {}",
                    arguments(op, kind, width, a, b)
                ),
            );
            checked(&spec, &name);
        }
    });
}

#[test]
fn byte_overflow_nominal_width_and_signedness_are_semantic_inputs() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for width in [1, 4, 8, 16, 32, 64, 128] {
            let mask = if width == 128 {
                u128::MAX
            } else {
                (1u128 << width) - 1
            };
            // At signed width one, bit pattern 1 is -1: 0 - (-1) is +1,
            // outside I1's [-1, 0]. Wider signed words interpret 1 as +1.
            for (kind, flag) in [("uint", true), ("int", width == 1)] {
                let ty = format!("IRTy.{kind}_ {width}");
                let frame = frame("IRScalar.int_ 0", "IRScalar.int_ 1");
                let ctx = context(&instruction("suboverflow", &ty), RESULTS, &types(&ty), 2);
                check(
                    &mut spec,
                    &format!("ov_width_{width}_{kind}"),
                    &actual(&ctx, &frame),
                    &expected(&frame, RESULTS, mask, flag),
                );
            }
        }
        let frame = frame("IRScalar.int_ 127", "IRScalar.int_ 1");
        let ctx = context(
            &instruction("addoverflow", "IRTy.uint_ 8"),
            RESULTS,
            &types("IRTy.uint_ 8"),
            2,
        );
        reject(
            &mut spec,
            "ov_unsigned_not_signed",
            &actual(&ctx, &frame),
            &expected(&frame, RESULTS, 128, true),
        );
    });
}

#[test]
fn byte_overflow_bad_types_widths_and_noncanonical_operands_fail_closed() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        let good = frame("IRScalar.int_ 3", "IRScalar.int_ 1");
        for (index, ty) in [
            "IRTy.bool_",
            "IRTy.ptr_",
            "IRTy.usize_ 64",
            "IRTy.float_ 64",
        ]
        .into_iter()
        .enumerate()
        {
            let ctx = context(&instruction("suboverflow", ty), RESULTS, &types(ty), 2);
            check(
                &mut spec,
                &format!("ov_type_{index}"),
                &actual(&ctx, &good),
                &fault("not_int"),
            );
        }
        for width in [0, 129] {
            let ty = format!("IRTy.uint_ {width}");
            let ctx = context(&instruction("suboverflow", &ty), RESULTS, &types(&ty), 2);
            check(
                &mut spec,
                &format!("ov_bad_width_{width}"),
                &actual(&ctx, &good),
                &fault("bad_field"),
            );
        }
        let ctx = context(
            &instruction("suboverflow", "IRTy.uint_ 8"),
            RESULTS,
            &types("IRTy.uint_ 8"),
            2,
        );
        for (index, value, error) in [
            (0, "IRScalar.ptr_ 16", "not_int"),
            (1, "IRScalar.bool_ Bool.true", "not_int"),
            (2, "IRScalar.int_ 256", "bad_field"),
            (3, "IRScalar.undef_", "not_int"),
        ] {
            for (side, frame) in [
                ("left", frame(value, "IRScalar.int_ 1")),
                ("right", frame("IRScalar.int_ 3", value)),
            ] {
                check(
                    &mut spec,
                    &format!("ov_bad_{side}_{index}"),
                    &actual(&ctx, &frame),
                    &fault(error),
                );
            }
        }
    });
}

#[test]
fn byte_overflow_exact_site_result_arity_order_and_ssa_ids_are_checked() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        let ty = "IRTy.uint_ 8";
        let inst = instruction("suboverflow", ty);
        let frame = frame("IRScalar.int_ 3", "IRScalar.int_ 1");
        let pair = types(ty);
        let one = "(IRList.cons Nat 99 (IRList.nil Nat))";
        let three =
            "(IRList.cons Nat 99 (IRList.cons Nat 100 (IRList.cons Nat 101 (IRList.nil Nat))))";
        for (index, results, types) in [
            (0, one, pair.clone()),
            (1, three, pair.clone()),
            (
                2,
                RESULTS,
                "(IRList.cons IRTy IRTy.bool_ (IRList.cons IRTy (IRTy.uint_ 8) (IRList.nil IRTy)))"
                    .into(),
            ),
            (3, RESULTS, types("IRTy.int_ 8")),
            (
                4,
                RESULTS,
                "(IRList.cons IRTy (IRTy.uint_ 8) (IRList.nil IRTy))".into(),
            ),
        ] {
            check(
                &mut spec,
                &format!("ov_bad_results_{index}"),
                &actual(&context(&inst, results, &types, 2), &frame),
                &fault("bad_field"),
            );
        }
        let swapped = "(IRList.cons Nat 100 (IRList.cons Nat 99 (IRList.nil Nat)))";
        let changed = actual(&context(&inst, swapped, &pair, 2), &frame);
        check(
            &mut spec,
            "ov_swapped_destinations_live",
            &changed,
            &expected(&frame, swapped, 2, false),
        );
        reject(
            &mut spec,
            "ov_swapped_destinations_not_original",
            &changed,
            &expected(&frame, RESULTS, 2, false),
        );
        check(
            &mut spec,
            "ov_missing_site",
            &actual(&context(&inst, RESULTS, &pair, 3), &frame),
            "IRByteConfigV1.halted Nat (IROutcome.stuck IRFault.fetch_past_end) ov_world",
        );
        let changed = inst.replace(" 40 78", " 78 40");
        reject(
            &mut spec,
            "ov_changed_operands",
            &actual(&context(&changed, RESULTS, &pair, 2), &frame),
            &expected(&frame, RESULTS, 2, false),
        );
    });
}

#[test]
fn byte_overflow_forged_value_flag_frame_and_world_endpoints_are_refuted() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        let frame = frame("IRScalar.int_ 0", "IRScalar.int_ 1");
        let ctx = context(
            &instruction("suboverflow", "IRTy.uint_ 8"),
            RESULTS,
            &types("IRTy.uint_ 8"),
            2,
        );
        let actual = actual(&ctx, &frame);
        let correct = expected(&frame, RESULTS, 255, true);
        for (name, source) in [
            (
                "ov_machine_wrong",
                "def ov_machine_wrong (frame : IRFrame) : IRMachine := IRMachine.mk (IRList.cons IRFrame frame ov_tail) (IRList.nil IRMemSlot) 18",
            ),
            (
                "ov_machine_lost_tail",
                "def ov_machine_lost_tail (frame : IRFrame) : IRMachine := IRMachine.mk (IRList.cons IRFrame frame (IRList.nil IRFrame)) (IRList.nil IRMemSlot) 17",
            ),
            (
                "ov_frame_no_advance",
                "def ov_frame_no_advance (frame : IRFrame) : IRFrame := frame",
            ),
        ] {
            register(&mut spec, source);
            checked(&spec, name);
        }
        for (name, wrong) in [
            ("value", expected(&frame, RESULTS, 0, true)),
            ("flag", expected(&frame, RESULTS, 255, false)),
            ("pc", correct.replace("ir_frame_advance", "ov_frame_no_advance")),
            ("cursor", correct.replace("ov_machine", "ov_machine_wrong")),
            ("tail", correct.replace("ov_machine", "ov_machine_lost_tail")),
            ("host", correct.replace("ov_world", "(IRByteWorldV1.mk Nat ov_memory 124 ov_owners 9)")),
            ("owners", correct.replace("ov_world", "(IRByteWorldV1.mk Nat ov_memory 123 (IRList.nil Nat) 9)")),
            ("next", correct.replace("ov_world", "(IRByteWorldV1.mk Nat ov_memory 123 ov_owners 10)")),
            ("memory", correct.replace("ov_world", "(IRByteWorldV1.mk Nat (IRByteMemoryV1.mk ov_allocs (fun (_ : Nat) => IROption.none Nat) 128) 123 ov_owners 9)")),
        ] { reject(&mut spec, &format!("ov_forged_{name}"), &actual, &wrong); }
    });
}

#[test]
fn byte_overflow_false_transfer_premises_and_assert_semantics_remain_refused() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        let ty = "IRTy.uint_ 8";
        let inst = instruction("suboverflow", ty);
        let pair = types(ty);
        let frame = frame("IRScalar.int_ 256", "IRScalar.int_ 1");
        let site = site(&pair, 2);
        let ctx = context(&inst, RESULTS, &pair, 2);
        let actual = format!(
            "ir_byte_overflow_exec_v1 Nat {ctx} (ov_machine {frame}) ov_world {RESULTS} {site}
  IROverflowOp.suboverflow ({ty}) (IRScalar.int_ 256) (IRScalar.int_ 1)"
        );
        let wrong = format!("ir_byte_bind_values_v1 Nat {ctx} (ov_machine {frame}) ov_world {RESULTS} {pair}
  (IRList.cons IRScalar (IRScalar.int_ (ir_overflow_value IROverflowOp.suboverflow 8 256 1))
    (IRList.cons IRScalar (IRScalar.bool_ (ir_overflow_flag IROverflowOp.suboverflow Bool.false 8 256 1)) (IRList.nil IRScalar)))");
        reject_source(&mut spec, "ov_false_input_premise", &format!("def ov_false_input_premise : Eq ({CONFIG}) ({actual}) ({wrong}) :=
ir_byte_overflow_uint_transfer_v1 Nat {ctx} (ov_machine {frame}) ov_world {RESULTS} {site}
  IROverflowOp.suboverflow 8 256 1 (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)"));
        for flag in [false, true] {
            let frame = self::frame(&format!("IRScalar.bool_ Bool.{flag}"), "IRScalar.int_ 1");
            check(
                &mut spec,
                &format!("ov_assert_still_unmodelled_{flag}"),
                &self::actual(
                    &context(
                        "IRInst.assert 40",
                        "(IRList.nil Nat)",
                        "(IRList.nil IRTy)",
                        2,
                    ),
                    &frame,
                ),
                "IRByteConfigV1.halted Nat (IROutcome.unmodelled IRFault.width_bounded) ov_world",
            );
        }
    });
}
