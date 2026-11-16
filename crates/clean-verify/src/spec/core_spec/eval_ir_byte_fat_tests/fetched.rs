// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const NIL: &str = "(@IRList.nil Nat)";
const RESULTS: &str = "(@IRList.cons Nat 99 (@IRList.nil Nat))";
const MEMORY: &str = "(IRByteMemoryV1.mk
  (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 8 2 Bool.true)
    (@IRList.nil IRByteAllocationV1))
  (fun (_ : Nat) => @IROption.some Nat 77) 128)";
const TAIL: &str = "(@IRList.cons IRFrame (IRFrame.mk 3 4 5 (@IRList.nil IRBinding)
  (@IRList.cons Nat 55 (@IRList.nil Nat))) (@IRList.nil IRFrame))";

fn world() -> String {
    format!(
        "(@IRByteWorldV1.mk Nat {MEMORY} host
  (@IRList.cons Nat 2 (@IRList.cons Nat 1 (@IRList.nil Nat))) 3)"
    )
}

fn frame(meta: &str) -> String {
    format!(
        "(IRFrame.mk 9 7 1
  (@IRList.cons IRBinding (IRBinding.mk 40 (IRScalar.fat_ 16 5))
   (@IRList.cons IRBinding (IRBinding.mk 41 (IRScalar.ptr_ 16))
    (@IRList.cons IRBinding (IRBinding.mk 42 ({meta}))
     (@IRList.cons IRBinding (IRBinding.mk 88 (IRScalar.int_ 55)) (@IRList.nil IRBinding)))))
  (@IRList.cons Nat 123 {NIL}))"
    )
}

fn machine(frame: &str) -> String {
    format!("(IRMachine.mk (@IRList.cons IRFrame {frame} {TAIL}) (@IRList.nil IRMemSlot) 77)")
}

fn context(instruction: &str, result_ty: &str) -> String {
    format!(
        "(IRByteContextV1.mk
 (IRModule.mk
  (@IRList.cons IRFunc (IRFunc.mk 9 {NIL} 7
   (@IRList.cons IRBlock (IRBlock.mk 7 {NIL}
    (@IRList.cons IRNode (IRNode.mk IRInst.unreachable {NIL})
     (@IRList.cons IRNode (IRNode.mk ({instruction}) {RESULTS}) (@IRList.nil IRNode))))
    (@IRList.nil IRBlock))) (@IRList.nil IRFunc)) (@IRList.nil IRGlobal))
 (@IRList.nil IRByteLayoutV1) (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1)
 (@IRList.cons IRByteSiteV1 (IRByteSiteV1.mk 9 7 1 0 1
  (@IRList.cons IRTy ({result_ty}) (@IRList.nil IRTy))) (@IRList.nil IRByteSiteV1)))"
    )
}

fn fetched(instruction: &str, result_ty: &str, frame: &str) -> String {
    let world = world();
    format!(
        "ir_byte_step_v1 Nat {} providers (@IRByteConfigV1.running Nat {} {world})",
        context(instruction, result_ty),
        machine(frame)
    )
}

#[test]
fn byte_fat_actual_fetched_operators_bind_once_and_preserve_the_entire_world() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let params = "(providers : IRByteProvidersV1 Nat) (host : Nat)";
        let world = world();
        for (i, (ty, mt)) in KINDS.iter().enumerate() {
            let meta = metadata(mt, "5");
            let frame = frame(&meta);
            for (j, (instruction, result_ty, value)) in [
                (
                    format!("IRInst.ptrdata ({ty}) 40"),
                    "IRTy.ptr_",
                    "IRScalar.ptr_ 16".to_owned(),
                ),
                (format!("IRInst.ptrmetadata ({ty}) ({mt}) 40"), *mt, meta),
                (
                    format!("IRInst.ptrfromparts ({ty}) ({mt}) 41 42"),
                    *ty,
                    "IRScalar.fat_ 16 5".to_owned(),
                ),
            ]
            .into_iter()
            .enumerate()
            {
                let run = fetched(&instruction, result_ty, &frame);
                let after = format!(
                    "(ir_frame_advance (ir_frame_set_many {frame} {RESULTS}
  (@IRList.cons IRScalar ({value}) (@IRList.nil IRScalar))))"
                );
                let expected = format!("@IRByteConfigV1.running Nat {} {world}", machine(&after));
                let name = format!("byte_fat_fetched_{i}_{j}");
                add(
                    &mut spec,
                    &format!(
                        "def {name} {params} : @Eq (IRByteConfigV1 Nat)
  ({run}) ({expected}) := @Eq.refl (IRByteConfigV1 Nat) ({expected})"
                    ),
                );
                let failed = format!(
                    "@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) {world}"
                );
                add(
                    &mut spec,
                    &format!(
                        "def byte_fat_bad_site_{i}_{j} {params} : @Eq (IRByteConfigV1 Nat)
  ({}) ({failed}) := @Eq.refl (IRByteConfigV1 Nat) ({failed})",
                        fetched(&instruction, "IRTy.bool_", &frame)
                    ),
                );
                // Detect host changes, extra advancement and erasure of real
                // byte/allocation state. Legacy cell memory stays empty because
                // that is an explicit precondition of ir_byte_world_valid_v1.
                for (k, changed) in [
                    expected.replace("host", "(Nat.succ host)"),
                    expected.replace(&after, &format!("(ir_frame_advance {after})")),
                    expected.replace(MEMORY, "(ir_byte_memory_empty_v1 128)"),
                ]
                .into_iter()
                .enumerate()
                {
                    let bad = format!("byte_fat_fetched_mutation_{i}_{j}_{k}");
                    refuse_claim(
                        &mut spec,
                        &bad,
                        &format!(
                            "def {bad} {params} :
  @Eq (IRByteConfigV1 Nat) ({run}) ({changed}) := {name} providers host"
                        ),
                    );
                }
            }
        }
        let frame = frame("IRScalar.int_ 5");
        let good = fetched(
            "IRInst.ptrmetadata IRTy.containerlen_ (IRTy.uint_ 64) 40",
            "IRTy.uint_ 64",
            &frame,
        );
        for (i, instruction) in [
            "IRInst.ptrdata IRTy.containerlen_ 40",
            "IRInst.ptrmetadata IRTy.containerlen_ (IRTy.uint_ 64) 88",
        ]
        .into_iter()
        .enumerate()
        {
            let bad = format!("byte_fat_changed_operator_or_ssa_{i}");
            refuse_claim(
                &mut spec,
                &bad,
                &format!(
                    "def {bad} {params} : @Eq (IRByteConfigV1 Nat)
  ({}) ({good}) := @Eq.refl (IRByteConfigV1 Nat) ({good})",
                    fetched(instruction, "IRTy.uint_ 64", &frame)
                ),
            );
        }
    });
}
