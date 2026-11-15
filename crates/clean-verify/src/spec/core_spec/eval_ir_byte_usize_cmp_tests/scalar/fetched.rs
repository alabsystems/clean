// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const CONFIG: &str = "IRByteConfigV1 Nat";

fn fixture() -> Specification {
    let mut spec = super::super::fixture();
    for source in [
        r"def scalar_cmp_block (op : IRICmpOp) (ty : IRTy) (left right dest : Nat) : IRBlock :=
IRBlock.mk 7 (IRList.nil Nat)
  (IRList.cons IRNode (IRNode.mk (IRInst.icmp op ty left right)
    (IRList.cons Nat dest (IRList.nil Nat)))
    (IRList.cons IRNode (IRNode.mk (IRInst.ret (IRList.cons Nat 99 (IRList.nil Nat)))
      (IRList.nil Nat)) (IRList.nil IRNode)))",
        r"def scalar_cmp_context (op : IRICmpOp) (ty : IRTy)
  (left right dest sitePc : Nat) (resultTy : IRTy) : IRByteContextV1 :=
IRByteContextV1.mk
  (IRModule.mk (IRList.cons IRFunc
    (IRFunc.mk 9 (IRList.cons Nat 40 (IRList.cons Nat 78 (IRList.nil Nat))) 7
      (IRList.cons IRBlock (scalar_cmp_block op ty left right dest) (IRList.nil IRBlock)))
    (IRList.nil IRFunc)) (IRList.nil IRGlobal))
  (IRList.nil IRByteLayoutV1)
  (IRList.cons IRByteSignatureV1 (IRByteSignatureV1.mk 0
    (IRList.cons IRTy ty (IRList.cons IRTy ty (IRList.nil IRTy)))
    (IRList.cons IRTy IRTy.bool_ (IRList.nil IRTy)) Bool.false)
    (IRList.nil IRByteSignatureV1))
  (IRList.cons IRByteFunctionV1 (IRByteFunctionV1.mk 9 0 4096 1 Bool.false)
    (IRList.nil IRByteFunctionV1))
  (IRList.cons IRByteSiteV1 (IRByteSiteV1.mk 9 7 sitePc 1 1
    (IRList.cons IRTy resultTy (IRList.nil IRTy)))
    (IRList.cons IRByteSiteV1 (IRByteSiteV1.mk 9 7 1 1 1 (IRList.nil IRTy))
      (IRList.nil IRByteSiteV1)))",
        r"def scalar_cmp_frame (left right : IRScalar) : IRFrame :=
IRFrame.mk 9 7 0 (IRList.cons IRBinding (IRBinding.mk 40 left)
  (IRList.cons IRBinding (IRBinding.mk 78 right) (IRList.nil IRBinding))) (IRList.nil Nat)",
        r"def scalar_cmp_machine (frame : IRFrame) : IRMachine :=
IRMachine.mk (IRList.cons IRFrame frame (IRList.nil IRFrame)) (IRList.nil IRMemSlot) 0",
        r"def scalar_cmp_memory : IRByteMemoryV1 := IRByteMemoryV1.mk
(IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 8 0 Bool.true)
  (IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 8 7 Bool.false)
    (IRList.nil IRByteAllocationV1)))
(fun (_ : Nat) => IROption.some Nat 173) 128",
        r"def scalar_cmp_world : IRByteWorldV1 Nat := IRByteWorldV1.mk Nat
scalar_cmp_memory 123 (IRList.cons Nat 8 (IRList.nil Nat)) 9",
        r"def scalar_cmp_done : IRByteWorldV1 Nat := IRByteWorldV1.mk Nat
scalar_cmp_memory 123 (IRList.nil Nat) 9",
        r"def scalar_cmp_providers : IRByteProvidersV1 Nat :=
fun (_ : Nat) (_ : IRList IRScalar) (memory : IRByteMemoryV1) (host : Nat) =>
IRByteImportResultV1.mk Nat (IROutcome.stuck IRFault.no_func) memory host",
    ] {
        register(&mut spec, source);
    }
    spec
}

fn context(op: &str, ty: &str) -> String {
    format!("scalar_cmp_context IRICmpOp.{op} ({ty}) 40 78 99 0 IRTy.bool_")
}

fn step(ctx: &str, left: &str, right: &str) -> String {
    format!("ir_byte_step_v1 Nat ({ctx}) scalar_cmp_providers
(IRByteConfigV1.running Nat (scalar_cmp_machine (scalar_cmp_frame ({left}) ({right}))) scalar_cmp_world)")
}

fn stepped(left: &str, right: &str, value: bool) -> String {
    format!(
        "IRByteConfigV1.running Nat (scalar_cmp_machine
(ir_frame_advance (ir_frame_set_many (scalar_cmp_frame ({left}) ({right}))
  (IRList.cons Nat 99 (IRList.nil Nat))
  (IRList.cons IRScalar ({}) (IRList.nil IRScalar))))) scalar_cmp_world",
        boolean(value)
    )
}

fn run(ctx: &str, left: &str, right: &str) -> String {
    format!(
        "ir_byte_run_v1 Nat ({ctx}) scalar_cmp_providers 2
(ir_byte_init_v1 Nat ({ctx}) 9
  (IRList.cons IRScalar ({left}) (IRList.cons IRScalar ({right}) (IRList.nil IRScalar)))
  scalar_cmp_memory 123)"
    )
}

fn returned(value: bool) -> String {
    format!(
        "IRByteConfigV1.halted Nat
(IROutcome.ret (IRList.cons IRScalar ({}) (IRList.nil IRScalar))) scalar_cmp_done",
        boolean(value)
    )
}

fn cell(
    spec: &mut Specification,
    name: &str,
    op: &str,
    ty: &str,
    left: &str,
    right: &str,
    value: bool,
) {
    let ctx = context(op, ty);
    check(
        spec,
        &format!("{name}_primitive"),
        "IRStepResult",
        &comparison(op, ty, left, right),
        &result(value),
    );
    check(
        spec,
        &format!("{name}_step"),
        CONFIG,
        &step(&ctx, left, right),
        &stepped(left, right, value),
    );
    let actual = run(&ctx, left, right);
    check(
        spec,
        &format!("{name}_run"),
        CONFIG,
        &actual,
        &returned(value),
    );
    reject(
        spec,
        &format!("{name}_wrong"),
        CONFIG,
        &actual,
        &returned(!value),
    );
}

#[test]
fn byte_scalar_icmp_fetched_bool_comparisons_preserve_entire_run() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for op in OPS {
            for left in [false, true] {
                for right in [false, true] {
                    cell(
                        &mut spec,
                        &format!("bool_{op}_{left}_{right}"),
                        op,
                        "IRTy.bool_",
                        &boolean(left),
                        &boolean(right),
                        expected(op, 1, u64::from(left), u64::from(right)),
                    );
                }
            }
        }
    });
}

#[test]
fn byte_scalar_icmp_fetched_usize_comparisons_preserve_entire_run() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for op in OPS {
            for (index, (left, right)) in [
                (0, 0),
                (0, 1),
                (1, 0),
                (8, 7),
                (1 << 63, 0),
                (u64::MAX, 0),
                (1 << 63, u64::MAX),
            ]
            .into_iter()
            .enumerate()
            {
                cell(
                    &mut spec,
                    &format!("usize_{op}_{index}"),
                    op,
                    "IRTy.usize_ 64",
                    &integer(left),
                    &integer(right),
                    expected(op, 64, left, right),
                );
            }
        }
    });
}

#[test]
fn byte_scalar_icmp_fetched_mutations_and_typed_refusals_are_observable() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = fixture();
        for (label, ty, op, changed_op, left, right) in [
            (
                "bool",
                "IRTy.bool_",
                "slt",
                "ult",
                boolean(true),
                boolean(false),
            ),
            (
                "usize",
                "IRTy.usize_ 64",
                "ne_",
                "eq_",
                integer(8),
                integer(7),
            ),
        ] {
            let original = context(op, ty);
            let actual = run(&original, &left, &right);
            let correct = returned(true);
            check(
                &mut spec,
                &format!("scalar_mutation_{label}_positive"),
                CONFIG,
                &actual,
                &correct,
            );
            for (suffix, changed) in [
                ("opcode", context(changed_op, ty)),
                (
                    "operand",
                    format!("scalar_cmp_context IRICmpOp.{op} ({ty}) 78 78 99 0 IRTy.bool_"),
                ),
                (
                    "destination",
                    format!("scalar_cmp_context IRICmpOp.{op} ({ty}) 40 78 100 0 IRTy.bool_"),
                ),
                (
                    "site",
                    format!("scalar_cmp_context IRICmpOp.{op} ({ty}) 40 78 99 2 IRTy.bool_"),
                ),
                (
                    "result_type",
                    format!("scalar_cmp_context IRICmpOp.{op} ({ty}) 40 78 99 0 (IRTy.uint_ 64)"),
                ),
            ] {
                reject(
                    &mut spec,
                    &format!("scalar_mutation_{label}_{suffix}"),
                    CONFIG,
                    &run(&changed, &left, &right),
                    &correct,
                );
            }
            reject(
                &mut spec,
                &format!("scalar_mutation_{label}_input"),
                CONFIG,
                &run(&original, &left, &left),
                &correct,
            );
            for (suffix, world) in [
                (
                    "host",
                    "IRByteWorldV1.mk Nat scalar_cmp_memory 124 (IRList.nil Nat) 9",
                ),
                (
                    "owners",
                    "IRByteWorldV1.mk Nat scalar_cmp_memory 123 (IRList.cons Nat 8 (IRList.nil Nat)) 9",
                ),
                (
                    "next_owner",
                    "IRByteWorldV1.mk Nat scalar_cmp_memory 123 (IRList.nil Nat) 10",
                ),
                (
                    "cursor",
                    "IRByteWorldV1.mk Nat (IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 scalar_cmp_memory) (fun (_ : Nat) => IROption.some Nat 173) 129) 123 (IRList.nil Nat) 9",
                ),
                (
                    "bytes",
                    "IRByteWorldV1.mk Nat (IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 scalar_cmp_memory) (fun (_ : Nat) => IROption.none Nat) 128) 123 (IRList.nil Nat) 9",
                ),
            ] {
                reject(
                    &mut spec,
                    &format!("scalar_mutation_{label}_{suffix}"),
                    CONFIG,
                    &actual,
                    &correct.replace("scalar_cmp_done", &format!("({world})")),
                );
            }
            for (index, malformed) in [
                "IRScalar.undef_",
                "IRScalar.ptr_ 16",
                "IRScalar.int_ 18446744073709551616",
            ]
            .into_iter()
            .enumerate()
            {
                for (side, a, b) in [
                    ("left", malformed, right.as_str()),
                    ("right", left.as_str(), malformed),
                ] {
                    check(
                        &mut spec,
                        &format!("scalar_machine_refusal_{label}_{index}_{side}"),
                        CONFIG,
                        &step(&original, a, b),
                        "IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) scalar_cmp_world",
                    );
                }
            }
        }
    });
}
