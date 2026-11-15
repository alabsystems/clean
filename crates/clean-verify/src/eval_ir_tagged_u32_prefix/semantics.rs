// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use crate::spec::{SpecError, Specification};

/// A separate model extension. It neither replaces nor edits the ByteV1 driver.
pub(super) fn install(spec: &mut Specification) -> Result<(), SpecError> {
    spec.add_inductive(
        "inductive IRCleanTag32PrefixV1 (W : Type) : Type\n| mk : IRByteConfigV1 W -> Bool -> Bool -> IRCleanTag32PrefixV1 W",
        "Complete Byte configuration and two occurrence slots; no allocation/ARC abstraction.",
    )?;
    spec.add_inductive(
        "inductive IRCleanTag32RunV1 (W : Type) : Type\n| mk : IRCleanTag32PrefixV1 W -> Nat -> IRCleanTag32RunV1 W",
        "Prefix endpoint including exact unconsumed node budget.",
    )?;
    for source in DEFINITIONS {
        let name = source.split_whitespace().nth(1).ok_or_else(|| {
            SpecError::TypeError("missing fixed tagged-prefix declaration name".into())
        })?;
        spec.add_recursive_def(
            source,
            "Explicit tagged-UInt32 prefix model; full world and occurrence slots retained.",
        )?;
        spec.verify_definition(name)?;
    }
    Ok(())
}

const DEFINITIONS: &[&str] = &[
    r"def ir_clean_tag32_word_v1 (word : Nat) : Bool :=
Bool.and (ir_nat_eqb (Nat.mod word 2) 1) (ir_nat_ltb (Nat.div word 2) 4294967296)",
    r"def ir_clean_tag32_provider_v1 (W : Type) (unbox : Nat) (fid : Nat) (args : IRList IRScalar) (mem : IRByteMemoryV1) (host : W) : IRByteImportResultV1 W :=
let bad : IRByteImportResultV1 W := IRByteImportResultV1.mk W (IROutcome.type_error IRFault.bad_field) mem host;
Bool.rec (fun (_ : Bool) => IRByteImportResultV1 W) bad
  (match args with
   | IRList.nil => bad
   | IRList.cons value rest =>
     match rest with
     | IRList.cons head tail => bad
     | IRList.nil =>
       match value with
       | IRScalar.ptr_ word =>
         Bool.rec (fun (_ : Bool) => IRByteImportResultV1 W) bad
           (IRByteImportResultV1.mk W (IROutcome.ret (IRList.cons IRScalar (IRScalar.int_ (Nat.div word 2)) (IRList.nil IRScalar))) mem host)
           (ir_clean_tag32_word_v1 word)
       | _ => bad)
  (ir_nat_eqb fid unbox)",
    r"def ir_clean_tag32_config_v1 (W : Type) (p : IRCleanTag32PrefixV1 W) : IRByteConfigV1 W :=
match p with
| IRCleanTag32PrefixV1.mk config left right => config",
    r"def ir_clean_tag32_fault_v1 (W : Type) (w : IRByteWorldV1 W) (left : Bool) (right : Bool) : IRCleanTag32PrefixV1 W :=
IRCleanTag32PrefixV1.mk W (IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) w) left right",
    r"def ir_clean_tag32_wrapper_v1 (ctx : IRByteContextV1) (wrapper : Nat) (block : Nat) (p0 : Nat) (p1 : Nat) : Bool :=
match ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx)) wrapper with
| IROption.none => Bool.false
| IROption.some function =>
  match ir_func_params function with
  | IRList.nil => Bool.false
  | IRList.cons a tail =>
    match tail with
    | IRList.nil => Bool.false
    | IRList.cons b rest =>
      match rest with
      | IRList.cons head last => Bool.false
      | IRList.nil =>
        match ir_byte_function_v1 ctx wrapper with
        | IROption.none => Bool.false
        | IROption.some binding =>
          match ir_byte_signature_v1 ctx (ir_byte_binding_sig_v1 binding) with
          | IROption.none => Bool.false
          | IROption.some signature =>
            Bool.and (Bool.not (ir_nat_eqb p0 p1))
              (Bool.and (ir_nat_eqb a p0) (Bool.and (ir_nat_eqb b p1)
                (Bool.and (ir_nat_eqb (ir_func_entry function) block)
                  (Bool.and (Bool.not (ir_byte_binding_import_v1 binding))
                    (Bool.and (ir_nat_eqb (ir_byte_binding_cc_v1 binding) 0)
                      (Bool.and (Bool.not (ir_byte_signature_vararg_v1 signature))
                        (Bool.and (ir_byte_ty_list_eq_v1 (ir_byte_signature_params_v1 signature) (IRList.cons IRTy IRTy.ptr_ (IRList.cons IRTy IRTy.ptr_ (IRList.nil IRTy))))
                          (ir_byte_ty_list_eq_v1 (ir_byte_signature_returns_v1 signature) (IRList.cons IRTy IRTy.ptr_ (IRList.nil IRTy))))))))))",
    r"def ir_clean_tag32_site_ptr_v1 (site : IRByteSiteV1) (pointer : Nat) : Bool :=
match ir_byte_site_operands_v1 site with
| IROption.none => Bool.true
| IROption.some rows =>
  Bool.and (ir_byte_operands_unique_v1 rows)
    (match rows with
     | IRList.nil => Bool.false
     | IRList.cons operand rest =>
       match rest with
       | IRList.cons head tail => Bool.false
       | IRList.nil => Bool.and (ir_nat_eqb (ir_byte_operand_id_v1 operand) pointer) (ir_byte_ty_eq_v1 (ir_byte_operand_ty_v1 operand) IRTy.ptr_))",
    r"def ir_clean_tag32_release_v1 (W : Type) (ctx : IRByteContextV1) (wrapper : Nat) (block : Nat) (s : IRMachine) (w : IRByteWorldV1 W) (f : IRFrame) (pointer : Nat) (rs : IRList Nat) (site : IRByteSiteV1) (p0 : Nat) (p1 : Nat) (left : Bool) (right : Bool) : IRCleanTag32PrefixV1 W :=
let bad : IRCleanTag32PrefixV1 W := ir_clean_tag32_fault_v1 W w left right;
let empty : Bool := Bool.and (ir_clean_tag32_wrapper_v1 ctx wrapper block p0 p1)
  (Bool.and (ir_clean_tag32_site_ptr_v1 site pointer)
    (Bool.and (ir_nat_eqb (ir_byte_site_fid_v1 site) (ir_frame_func f))
      (Bool.and (ir_nat_eqb (ir_byte_site_block_v1 site) (ir_frame_block f))
        (Bool.and (ir_nat_eqb (ir_byte_site_pc_v1 site) (ir_frame_pc f))
          (Bool.and (ir_nat_eqb (ir_byte_length_v1 Nat rs) 0) (ir_nat_eqb (ir_byte_length_v1 IRTy (ir_byte_site_results_v1 site)) 0))))));
match ir_frame_get f pointer with
| IRScalar.ptr_ word =>
  Bool.rec (fun (_ : Bool) => IRCleanTag32PrefixV1 W) bad
    (Bool.rec (fun (_ : Bool) => IRCleanTag32PrefixV1 W)
      (Bool.rec (fun (_ : Bool) => IRCleanTag32PrefixV1 W) bad
        (IRCleanTag32PrefixV1.mk W (ir_byte_lift_v1 W w (ir_advance s)) left Bool.false)
        (Bool.and (ir_nat_eqb (ir_frame_pc f) 3) (Bool.and (ir_nat_eqb pointer p1) right)))
      (IRCleanTag32PrefixV1.mk W (ir_byte_lift_v1 W w (ir_advance s)) Bool.false right)
      (Bool.and (ir_nat_eqb (ir_frame_pc f) 2) (Bool.and (ir_nat_eqb pointer p0) left)))
    (Bool.and empty (ir_clean_tag32_word_v1 word))
| _ => bad",
    r"def ir_clean_tag32_node_v1 (W : Type) (ctx : IRByteContextV1) (wrapper : Nat) (block : Nat) (unbox : Nat) (p0 : Nat) (p1 : Nat) (s : IRMachine) (w : IRByteWorldV1 W) (f : IRFrame) (node : IRNode) (left : Bool) (right : Bool) : IRCleanTag32PrefixV1 W :=
match ir_byte_site_v1 ctx (ir_frame_func f) (ir_frame_block f) (ir_frame_pc f) with
| IROption.none => ir_clean_tag32_fault_v1 W w left right
| IROption.some site =>
  match node with
  | IRNode.mk instruction rs =>
    match instruction with
    | IRInst.release pointer => ir_clean_tag32_release_v1 W ctx wrapper block s w f pointer rs site p0 p1 left right
    | _ => IRCleanTag32PrefixV1.mk W (ir_byte_step_node_v1 W ctx (ir_clean_tag32_provider_v1 W unbox) s w f node) left right",
    r"def ir_clean_tag32_fetch_v1 (W : Type) (ctx : IRByteContextV1) (wrapper : Nat) (block : Nat) (unbox : Nat) (p0 : Nat) (p1 : Nat) (s : IRMachine) (w : IRByteWorldV1 W) (left : Bool) (right : Bool) : IRCleanTag32PrefixV1 W :=
match ir_mach_frames s with
| IRList.nil => ir_clean_tag32_fault_v1 W w left right
| IRList.cons f rest =>
  Bool.rec (fun (_ : Bool) => IRCleanTag32PrefixV1 W)
    (ir_clean_tag32_fault_v1 W w left right)
    (match ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx)) (ir_frame_func f) with
     | IROption.none => ir_clean_tag32_fault_v1 W w left right
     | IROption.some function =>
       match ir_block_find (ir_func_blocks function) (ir_frame_block f) with
       | IROption.none => ir_clean_tag32_fault_v1 W w left right
       | IROption.some body =>
         match ir_nodes_get (ir_block_nodes body) (ir_frame_pc f) with
         | IROption.none => ir_clean_tag32_fault_v1 W w left right
         | IROption.some node => ir_clean_tag32_node_v1 W ctx wrapper block unbox p0 p1 s w f node left right)
    (Bool.and (ir_nat_eqb (ir_frame_func f) wrapper)
      (Bool.and (ir_nat_eqb (ir_frame_block f) block) (ir_nat_ltb (ir_frame_pc f) 4)))",
    r"def ir_clean_tag32_step_v1 (W : Type) (ctx : IRByteContextV1) (wrapper : Nat) (block : Nat) (unbox : Nat) (p0 : Nat) (p1 : Nat) (p : IRCleanTag32PrefixV1 W) : IRCleanTag32PrefixV1 W :=
match p with
| IRCleanTag32PrefixV1.mk config left right =>
  match config with
  | IRByteConfigV1.halted outcome w => p
  | IRByteConfigV1.running s w =>
    Bool.rec (fun (_ : Bool) => IRCleanTag32PrefixV1 W)
      (IRCleanTag32PrefixV1.mk W (IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_addr) w) left right)
      (ir_clean_tag32_fetch_v1 W ctx wrapper block unbox p0 p1 s w left right)
      (ir_byte_world_valid_v1 W s w)",
    r"def ir_clean_tag32_stopped_v1 (W : Type) (p : IRCleanTag32PrefixV1 W) : Bool :=
match ir_clean_tag32_config_v1 W p with
| IRByteConfigV1.halted outcome w => Bool.true
| IRByteConfigV1.running s w =>
  match ir_mach_frames s with
  | IRList.nil => Bool.true
  | IRList.cons f rest => ir_nat_leb 4 (ir_frame_pc f)",
    r"def ir_clean_tag32_run_v1 (W : Type) (ctx : IRByteContextV1) (wrapper : Nat) (block : Nat) (unbox : Nat) (p0 : Nat) (p1 : Nat) (fuel : Nat) (p : IRCleanTag32PrefixV1 W) : IRCleanTag32RunV1 W :=
Nat.rec (fun (_ : Nat) => IRCleanTag32PrefixV1 W -> IRCleanTag32RunV1 W)
  (fun (state : IRCleanTag32PrefixV1 W) => IRCleanTag32RunV1.mk W state 0)
  (fun (remaining : Nat) (again : IRCleanTag32PrefixV1 W -> IRCleanTag32RunV1 W) =>
    fun (state : IRCleanTag32PrefixV1 W) =>
      Bool.rec (fun (_ : Bool) => IRCleanTag32RunV1 W)
        (again (ir_clean_tag32_step_v1 W ctx wrapper block unbox p0 p1 state))
        (IRCleanTag32RunV1.mk W state (Nat.succ remaining))
        (ir_clean_tag32_stopped_v1 W state)) fuel p",
    r"def ir_clean_tag32_init_v1 (W : Type) (ctx : IRByteContextV1) (wrapper : Nat) (args : IRList IRScalar) (mem : IRByteMemoryV1) (host : W) : IRCleanTag32PrefixV1 W :=
IRCleanTag32PrefixV1.mk W (ir_byte_init_v1 W ctx wrapper args mem host) Bool.true Bool.true",
    r"def ir_clean_tag32_run_zero_v1 (W : Type) (ctx : IRByteContextV1) (wrapper : Nat) (block : Nat) (unbox : Nat) (p0 : Nat) (p1 : Nat) (p : IRCleanTag32PrefixV1 W) : Eq (IRCleanTag32RunV1 W) (ir_clean_tag32_run_v1 W ctx wrapper block unbox p0 p1 0 p) (IRCleanTag32RunV1.mk W p 0) :=
Eq.refl (IRCleanTag32RunV1 W) (IRCleanTag32RunV1.mk W p 0)",
];
