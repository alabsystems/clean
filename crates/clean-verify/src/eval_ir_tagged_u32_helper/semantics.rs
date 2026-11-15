// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use crate::spec::{SpecError, Specification};

pub(super) fn install(spec: &mut Specification) -> Result<(), SpecError> {
    spec.add_inductive(
        "inductive IRCleanTag32HelperRunV1 (W : Type) : Type\n| mk : IRCleanTag32PrefixV1 W -> Nat -> IRCleanTag32HelperRunV1 W",
        "Complete helper endpoint and exact remaining node budget, distinct from prefix run.",
    )?;
    for source in DEFINITIONS {
        let name = source
            .split_whitespace()
            .nth(1)
            .ok_or_else(|| SpecError::TypeError("missing fixed helper declaration name".into()))?;
        spec.add_recursive_def(
            source,
            "Explicit complete tagged helper; no default ByteV1 change.",
        )?;
        spec.verify_definition(name)?;
    }
    Ok(())
}

const DEFINITIONS: &[&str] = &[
    r"def ir_clean_tag32_helper_provider_v1 (W : Type) (unbox : Nat) (boxer : Nat) (fid : Nat) (args : IRList IRScalar) (mem : IRByteMemoryV1) (host : W) : IRByteImportResultV1 W :=
let bad : IRByteImportResultV1 W := IRByteImportResultV1.mk W (IROutcome.type_error IRFault.bad_field) mem host;
Bool.rec (fun (_ : Bool) => IRByteImportResultV1 W)
  (ir_clean_tag32_provider_v1 W unbox fid args mem host)
  (match args with
   | IRList.nil => bad
   | IRList.cons value rest =>
     match rest with
     | IRList.cons head tail => bad
     | IRList.nil =>
       match value with
       | IRScalar.int_ n =>
         Bool.rec (fun (_ : Bool) => IRByteImportResultV1 W) bad
           (IRByteImportResultV1.mk W (IROutcome.ret (IRList.cons IRScalar (IRScalar.ptr_ (ir_clean_tag32_encode_v1 n)) (IRList.nil IRScalar))) mem host)
           (ir_nat_ltb n 4294967296)
       | _ => bad)
  (ir_nat_eqb fid boxer)",
    r"def ir_clean_tag32_helper_prefix_v1 (wrapper : Nat) (block : Nat) (machine : IRMachine) : Bool :=
match ir_mach_frames machine with
| IRList.nil => Bool.false
| IRList.cons frame rest =>
  Bool.and (ir_nat_eqb (ir_frame_func frame) wrapper)
    (Bool.and (ir_nat_eqb (ir_frame_block frame) block) (ir_nat_ltb (ir_frame_pc frame) 4))",
    r"def ir_clean_tag32_helper_tail_v1 (W : Type) (ctx : IRByteContextV1) (unbox : Nat) (boxer : Nat) (machine : IRMachine) (world : IRByteWorldV1 W) (left : Bool) (right : Bool) : IRCleanTag32PrefixV1 W :=
Bool.rec (fun (_ : Bool) => IRCleanTag32PrefixV1 W)
  (ir_clean_tag32_fault_v1 W world left right)
  (IRCleanTag32PrefixV1.mk W (ir_byte_step_machine_v1 W ctx (ir_clean_tag32_helper_provider_v1 W unbox boxer) machine world) Bool.false Bool.false)
  (Bool.and (Bool.not left) (Bool.not right))",
    r"def ir_clean_tag32_helper_step_v1 (W : Type) (ctx : IRByteContextV1) (wrapper : Nat) (block : Nat) (unbox : Nat) (boxer : Nat) (p0 : Nat) (p1 : Nat) (state : IRCleanTag32PrefixV1 W) : IRCleanTag32PrefixV1 W :=
match state with
| IRCleanTag32PrefixV1.mk config left right =>
  match config with
  | IRByteConfigV1.halted outcome world => state
  | IRByteConfigV1.running machine world =>
    Bool.rec (fun (_ : Bool) => IRCleanTag32PrefixV1 W)
      (Bool.rec (fun (_ : Bool) => IRCleanTag32PrefixV1 W)
        (IRCleanTag32PrefixV1.mk W (IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_addr) world) left right)
        (ir_clean_tag32_helper_tail_v1 W ctx unbox boxer machine world left right)
        (ir_byte_world_valid_v1 W machine world))
      (ir_clean_tag32_step_v1 W ctx wrapper block unbox p0 p1 state)
      (ir_clean_tag32_helper_prefix_v1 wrapper block machine)",
    r"def ir_clean_tag32_helper_init_v1 (W : Type) (ctx : IRByteContextV1) (wrapper : Nat) (args : IRList IRScalar) (mem : IRByteMemoryV1) (host : W) : IRCleanTag32PrefixV1 W :=
ir_clean_tag32_init_v1 W ctx wrapper args mem host",
    r"def ir_clean_tag32_helper_run_v1 (W : Type) (ctx : IRByteContextV1) (wrapper : Nat) (block : Nat) (unbox : Nat) (boxer : Nat) (p0 : Nat) (p1 : Nat) (fuel : Nat) (state : IRCleanTag32PrefixV1 W) : IRCleanTag32HelperRunV1 W :=
Nat.rec (fun (_ : Nat) => IRCleanTag32PrefixV1 W -> IRCleanTag32HelperRunV1 W)
  (fun (p : IRCleanTag32PrefixV1 W) => IRCleanTag32HelperRunV1.mk W p 0)
  (fun (remaining : Nat) (again : IRCleanTag32PrefixV1 W -> IRCleanTag32HelperRunV1 W) =>
    fun (p : IRCleanTag32PrefixV1 W) =>
      Bool.rec (fun (_ : Bool) => IRCleanTag32HelperRunV1 W)
        (again (ir_clean_tag32_helper_step_v1 W ctx wrapper block unbox boxer p0 p1 p))
        (IRCleanTag32HelperRunV1.mk W p (Nat.succ remaining))
        (ir_byte_halted_v1 W (ir_clean_tag32_config_v1 W p))) fuel state",
];
