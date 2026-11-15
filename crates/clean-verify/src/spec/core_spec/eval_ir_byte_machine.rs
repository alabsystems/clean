// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Byte/world execution using the existing EvalIR syntax, SSA frames and pure
//! operations. Memory, imports and activation lifetime never use the legacy
//! cell-memory dispatcher. Context well-formedness is supplied by actual-module
//! reflection; code/data separation and provider fidelity remain explicit
//! representation obligations, not facts established by this evaluator.
//! BinOp delegates to the existing canonical operator semantics after byte
//! carrier checks; execution coverage does not imply proof-builder coverage.
//! Floating carriers remain outside the byte profile's value representation.

use crate::spec::{SpecError, Specification};

impl Specification {
    pub(super) fn add_eval_ir_byte_machine(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_byte_world_helpers()?;
        self.add_eval_ir_byte_overflow_v1()?;
        self.add_eval_ir_byte_call_helpers()?;
        self.add_eval_ir_byte_dispatch()?;
        self.add_recursive_def(
            "def ir_byte_release_unmodelled_v1 (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W) (s : IRMachine) (w : IRByteWorldV1 W) (site : IRByteSiteV1) (pointer : Nat) (rs : IRList Nat) : @Eq (IRByteConfigV1 W) (ir_byte_exec_v1 W ctx providers s w site (IRInst.release pointer) rs) (@IRByteConfigV1.halted W (IROutcome.unmodelled IRFault.width_bounded) w) := @Eq.refl (IRByteConfigV1 W) (@IRByteConfigV1.halted W (IROutcome.unmodelled IRFault.width_bounded) w)",
            "Release syntax retention: exact unmodelled dispatch and unchanged world for all inputs. Fetch/site/world preflights remain outside this dispatch equality; no ARC semantics.",
        )?;
        self.add_eval_ir_byte_initialization()
    }

    fn add_eval_ir_byte_world_helpers(&mut self) -> Result<(), SpecError> {
        for source in [
            r"def ir_byte_with_memory_v1 (W : Type) (w : IRByteWorldV1 W) (mem : IRByteMemoryV1) : IRByteWorldV1 W :=
match w with
| IRByteWorldV1.mk old host owners next => @IRByteWorldV1.mk W mem host owners next",
            r"def ir_byte_lift_v1 (W : Type) (w : IRByteWorldV1 W) (c : IRConfig) : IRByteConfigV1 W :=
match c with
| IRConfig.running s => @IRByteConfigV1.running W s w
| IRConfig.halted o => @IRByteConfigV1.halted W o w",
            r"def ir_byte_owner_member_v1 (owner : Nat) (owners : IRList Nat) : Bool :=
@IRList.rec Nat (fun (_ : IRList Nat) => Bool) Bool.false
  (fun (x : Nat) (_ : IRList Nat) (ih : Bool) => Bool.or (ir_nat_eqb x owner) ih) owners",
            r"def ir_byte_owners_valid_v1 (owners : IRList Nat) (next : Nat) : Bool :=
@IRList.rec Nat (fun (_ : IRList Nat) => Bool) (ir_nat_pos next)
  (fun (x : Nat) (rest : IRList Nat) (ih : Bool) =>
    Bool.and ih (Bool.and (ir_nat_pos x)
      (Bool.and (ir_nat_ltb x next) (Bool.not (ir_byte_owner_member_v1 x rest))))) owners",
            r"def ir_byte_memory_owners_v1 (mem : IRByteMemoryV1) (owners : IRList Nat) (next : Nat) : Bool :=
@IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => Bool) Bool.true
  (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (ih : Bool) =>
    Bool.and ih (Bool.and (ir_byte_alloc_valid_v1 a)
      (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 a) next)
        (Bool.or (Bool.not (ir_byte_alloc_live_v1 a))
          (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0)
            (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners)))))) (ir_byte_mem_allocs_v1 mem)",
            r"def ir_byte_fresh_owner_v1 (mem : IRByteMemoryV1) : Nat :=
@IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => Nat) 1
  (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (ih : Nat) =>
    let candidate : Nat := Nat.succ (ir_byte_alloc_owner_v1 a);
    @Bool.rec (fun (_ : Bool) => Nat) ih candidate (ir_nat_ltb ih candidate)) (ir_byte_mem_allocs_v1 mem)",
            r"def ir_byte_world_valid_v1 (W : Type) (s : IRMachine) (w : IRByteWorldV1 W) : Bool :=
Bool.and (ir_nat_eqb (ir_byte_length_v1 IRMemSlot (ir_mach_mem s)) 0)
  (Bool.and (ir_nat_eqb (ir_byte_length_v1 IRFrame (ir_mach_frames s)) (ir_byte_length_v1 Nat (ir_byte_world_owners_v1 W w)))
    (Bool.and (ir_byte_owners_valid_v1 (ir_byte_world_owners_v1 W w) (ir_byte_world_next_v1 W w))
      (ir_byte_memory_owners_v1 (ir_byte_world_memory_v1 W w) (ir_byte_world_owners_v1 W w) (ir_byte_world_next_v1 W w))))",
            r"def ir_byte_push_owner_v1 (W : Type) (w : IRByteWorldV1 W) : IRByteWorldV1 W :=
match w with
| IRByteWorldV1.mk mem host owners next => @IRByteWorldV1.mk W mem host (@IRList.cons Nat next owners) (Nat.succ next)",
            r"def ir_byte_pop_owner_v1 (W : Type) (w : IRByteWorldV1 W) : IRByteWorldV1 W :=
match w with
| IRByteWorldV1.mk mem host owners next =>
  match owners with
  | IRList.nil => w
  | IRList.cons owner rest => @IRByteWorldV1.mk W (ir_byte_retire_v1 owner mem) host rest next",
            r"def ir_byte_bind_values_v1 (W : Type) (ctx : IRByteContextV1) (s : IRMachine) (w : IRByteWorldV1 W) (rs : IRList Nat) (tys : IRList IRTy) (vs : IRList IRScalar) : IRByteConfigV1 W :=
@Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
  (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) w)
  (match s with
   | IRMachine.mk fs mem na =>
     match fs with
     | IRList.nil => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_frame) w
     | IRList.cons f rest => @IRByteConfigV1.running W
         (IRMachine.mk (@IRList.cons IRFrame (ir_frame_advance (ir_frame_set_many f rs vs)) rest) mem na) w)
  (Bool.and (ir_nat_eqb (ir_byte_length_v1 Nat rs) (ir_byte_length_v1 IRScalar vs))
    (ir_byte_values_match_v1 ctx tys vs))",
            r"def ir_byte_scalar_result_v1 (W : Type) (ctx : IRByteContextV1) (s : IRMachine) (w : IRByteWorldV1 W) (rs : IRList Nat) (tys : IRList IRTy) (r : IRStepResult) : IRByteConfigV1 W :=
match r with
| IRStepResult.value v => ir_byte_bind_values_v1 W ctx s w rs tys (@IRList.cons IRScalar v (@IRList.nil IRScalar))
| IRStepResult.fault o => @IRByteConfigV1.halted W o w",
            r"def ir_byte_memory_result_v1 (W : Type) (ctx : IRByteContextV1) (s : IRMachine) (w : IRByteWorldV1 W) (rs : IRList Nat) (tys : IRList IRTy) (store : Bool) (r : IRByteMemoryResultV1) : IRByteConfigV1 W :=
match r with
| IRByteMemoryResultV1.value v mem =>
  ir_byte_bind_values_v1 W ctx s (ir_byte_with_memory_v1 W w mem) rs tys
    (@Bool.rec (fun (_ : Bool) => IRList IRScalar)
      (@IRList.cons IRScalar v (@IRList.nil IRScalar)) (@IRList.nil IRScalar) store)
| IRByteMemoryResultV1.fault o mem => @IRByteConfigV1.halted W o (ir_byte_with_memory_v1 W w mem)",
            r"def ir_byte_jump_v1 (W : Type) (ctx : IRByteContextV1) (s : IRMachine) (w : IRByteWorldV1 W) (target : Nat) (args : IRList Nat) : IRByteConfigV1 W :=
match ir_cur_func (ir_byte_context_module_v1 ctx) s with
| IROption.none => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_func) w
| IROption.some f =>
  match ir_block_find (ir_func_blocks f) target with
  | IROption.none => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_block) w
  | IROption.some b =>
    @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
      (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) w)
      (ir_byte_lift_v1 W w (ir_jump (ir_byte_context_module_v1 ctx) s target args))
      (ir_nat_eqb (ir_byte_length_v1 Nat (ir_block_params b)) (ir_byte_length_v1 Nat args))",
        ] {
            self.add_recursive_def(source, "Versioned byte/world operational helper; checked value term, no representation or provider fidelity assumption.")?;
        }
        Ok(())
    }

    fn add_eval_ir_byte_call_helpers(&mut self) -> Result<(), SpecError> {
        for source in [
            r"def ir_byte_import_result_v1 (W : Type) (ctx : IRByteContextV1) (s : IRMachine) (w : IRByteWorldV1 W) (rs : IRList Nat) (tys : IRList IRTy) (r : IRByteImportResultV1 W) : IRByteConfigV1 W :=
match r with
| IRByteImportResultV1.mk outcome mem host =>
  let updated : IRByteWorldV1 W := @IRByteWorldV1.mk W mem host (ir_byte_world_owners_v1 W w) (ir_byte_world_next_v1 W w);
  @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
    (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_addr) updated)
    (match outcome with
     | IROutcome.ret vs => ir_byte_bind_values_v1 W ctx s updated rs tys vs
     | _ => @IRByteConfigV1.halted W outcome updated)
    (ir_byte_memory_owners_v1 mem (ir_byte_world_owners_v1 W w) (ir_byte_world_next_v1 W w))",
            r"def ir_byte_call_known_v1 (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W) (s : IRMachine) (w : IRByteWorldV1 W) (rs : IRList Nat) (site : IRByteSiteV1) (binding : IRByteFunctionV1) (sig : IRByteSignatureV1) (args : IRList IRScalar) : IRByteConfigV1 W :=
@Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
  (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_fnptr) w)
  (@Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
    (match ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx)) (ir_byte_binding_fid_v1 binding) with
     | IROption.none => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_func) w
     | IROption.some f =>
       @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
         (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) w)
         (ir_byte_lift_v1 W (ir_byte_push_owner_v1 W w) (ir_push s rs f args))
         (ir_nat_eqb (ir_byte_length_v1 Nat (ir_func_params f)) (ir_byte_length_v1 IRScalar args)))
    (ir_byte_import_result_v1 W ctx s w rs (ir_byte_signature_returns_v1 sig)
      (providers (ir_byte_binding_fid_v1 binding) args (ir_byte_world_memory_v1 W w) (ir_byte_world_host_v1 W w)))
    (ir_byte_binding_import_v1 binding))
  (Bool.and (Bool.not (ir_byte_signature_vararg_v1 sig))
    (Bool.and (ir_nat_leb (ir_byte_binding_cc_v1 binding) 1)
      (Bool.and (ir_nat_eqb (ir_byte_site_cc_v1 site) (ir_byte_binding_cc_v1 binding))
        (Bool.and (ir_nat_eqb (ir_byte_length_v1 Nat rs) (ir_byte_length_v1 IRTy (ir_byte_signature_returns_v1 sig)))
          (Bool.and (ir_byte_ty_list_eq_v1 (ir_byte_site_results_v1 site) (ir_byte_signature_returns_v1 sig))
            (ir_byte_values_match_v1 ctx (ir_byte_signature_params_v1 sig) args))))))",
            r"def ir_byte_call_v1 (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W) (s : IRMachine) (w : IRByteWorldV1 W) (rs : IRList Nat) (site : IRByteSiteV1) (fid : Nat) (args : IRList Nat) : IRByteConfigV1 W :=
match ir_byte_function_v1 ctx fid with
| IROption.none => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_func) w
| IROption.some binding =>
  match ir_byte_signature_v1 ctx (ir_byte_binding_sig_v1 binding) with
  | IROption.none => @IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_fnptr) w
  | IROption.some sig => ir_byte_call_known_v1 W ctx providers s w rs site binding sig (ir_resolve s args)",
            r"def ir_byte_call_indirect_v1 (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W) (s : IRMachine) (w : IRByteWorldV1 W) (rs : IRList Nat) (site : IRByteSiteV1) (callee : IRScalar) (sig : Nat) (args : IRList Nat) (cc : Nat) : IRByteConfigV1 W :=
match callee with
| IRScalar.fnptr_ fid =>
  match ir_byte_function_v1 ctx fid with
  | IROption.none => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_func) w
  | IROption.some binding =>
    @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
      (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_fnptr) w)
      (ir_byte_call_v1 W ctx providers s w rs site fid args)
      (Bool.and (ir_nat_eqb sig (ir_byte_binding_sig_v1 binding)) (ir_nat_eqb cc (ir_byte_site_cc_v1 site)))
| IRScalar.nullptr_ => @IRByteConfigV1.halted W (IROutcome.ub IRFault.null_deref) w
| _ => @IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_fnptr) w",
            r"def ir_byte_return_v1 (W : Type) (ctx : IRByteContextV1) (s : IRMachine) (w : IRByteWorldV1 W) (args : IRList Nat) : IRByteConfigV1 W :=
match ir_mach_frames s with
| IRList.nil => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_frame) w
| IRList.cons f rest =>
  match ir_byte_function_v1 ctx (ir_frame_func f) with
  | IROption.none => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_func) w
  | IROption.some binding =>
    match ir_byte_signature_v1 ctx (ir_byte_binding_sig_v1 binding) with
    | IROption.none => @IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_fnptr) w
    | IROption.some sig =>
      @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
        (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) w)
        (ir_byte_lift_v1 W (ir_byte_pop_owner_v1 W w) (ir_ret_vals s (ir_resolve s args)))
        (Bool.and (ir_byte_values_match_v1 ctx (ir_byte_signature_returns_v1 sig) (ir_resolve s args))
          (match rest with
           | IRList.nil => ir_nat_eqb (ir_byte_length_v1 Nat (ir_frame_dests f)) 0
           | IRList.cons caller tail => ir_nat_eqb (ir_byte_length_v1 Nat (ir_frame_dests f)) (ir_byte_length_v1 Nat args)))",
        ] {
            self.add_recursive_def(source, "Exact-signature byte/world call semantics; shared SSA push/return rules with fresh activation ownership and explicit provider results.")?;
        }
        Ok(())
    }

    fn add_eval_ir_byte_dispatch(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(r"def ir_byte_copy_eval_v1 (ctx : IRByteContextV1) (ty : IRTy) (value : IRScalar) : IRStepResult :=
@Bool.rec (fun (_ : Bool) => IRStepResult)
  (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))
  (IRStepResult.value value)
  (ir_byte_value_matches_v1 ctx ty value)",
            "Typed byte-profile Copy preserves the exact carrier after the actual context's width, pointer/function and aggregate checks. Unlike legacy ir_copy_eval this is not merely a shape-class check. Static source type agreement still belongs to module validation; copying a pointer establishes no allocation, lifetime or access authority.")?;
        self.add_recursive_def(r"def ir_byte_alloca_exec_v1 (W : Type) (ctx : IRByteContextV1) (s : IRMachine) (w : IRByteWorldV1 W) (rs : IRList Nat) (site : IRByteSiteV1) (ty : IRTy) (count : IROption Nat) : IRByteConfigV1 W :=
match ir_byte_world_owners_v1 W w with
| IRList.nil => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_frame) w
| IRList.cons owner rest =>
  let value : IRScalar := @IROption.rec Nat (fun (_ : IROption Nat) => IRScalar) (IRScalar.int_ 1) (fun (id : Nat) => ir_getd s id) count;
  match value with
  | IRScalar.int_ n =>
    @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
      (@IRByteConfigV1.halted W (IROutcome.unmodelled IRFault.width_bounded) w)
      (ir_byte_memory_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) Bool.false
        (ir_byte_alloc_v1 ctx ty n (ir_byte_site_align_v1 site) owner (ir_byte_world_memory_v1 W w)))
      (ir_nat_ltb n 9223372036854775808)
  | _ => @IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_int) w",
            "Typed layout/count allocation; canonical nonnegative signed64 counts are this profile's explicit domain.")?;
        self.add_recursive_def(r"def ir_byte_exec_v1 (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W) (s : IRMachine) (w : IRByteWorldV1 W) (site : IRByteSiteV1) (i : IRInst) (rs : IRList Nat) : IRByteConfigV1 W :=
match i with
| IRInst.const_ ty c => @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
    (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) w)
    (ir_byte_scalar_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) (ir_byte_const_context_eval_v1 ctx ty c))
    (ir_byte_ty_list_eq_v1 (ir_byte_site_results_v1 site) (@IRList.cons IRTy ty (@IRList.nil IRTy)))
| IRInst.copy ty value => ir_byte_scalar_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) (ir_byte_copy_eval_v1 ctx ty (ir_getd s value))
| IRInst.cast op src dst value => ir_byte_scalar_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) (ir_byte_cast_eval_v1 ctx op src dst (ir_getd s value))
| IRInst.ptrdata ty value => ir_byte_scalar_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) (ir_byte_ptrdata_eval_v1 ctx ty (ir_getd s value))
| IRInst.ptrmetadata ty metadataTy value => ir_byte_scalar_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) (ir_byte_ptrmetadata_eval_v1 ctx ty metadataTy (ir_getd s value))
| IRInst.ptrfromparts ty metadataTy data metadata => ir_byte_scalar_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) (ir_byte_ptrfromparts_eval_v1 ctx ty metadataTy (ir_getd s data) (ir_getd s metadata))
| IRInst.binop op ty a b =>
  @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
    (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) w)
    (ir_byte_scalar_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) (ir_binop_eval op ty (ir_getd s a) (ir_getd s b)))
    (Bool.and (ir_byte_value_matches_v1 ctx ty (ir_getd s a)) (ir_byte_value_matches_v1 ctx ty (ir_getd s b)))
| IRInst.overflow op ty a b => ir_byte_overflow_exec_v1 W ctx s w rs site op ty (ir_getd s a) (ir_getd s b)
| IRInst.icmp op ty a b =>
  @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
    (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) w)
    (ir_byte_scalar_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) (ir_byte_icmp_eval_v1 op ty (ir_getd s a) (ir_getd s b)))
    (Bool.and (ir_byte_value_matches_v1 ctx ty (ir_getd s a)) (ir_byte_value_matches_v1 ctx ty (ir_getd s b)))
| IRInst.select ty c a b =>
  @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
    (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) w)
    (ir_byte_scalar_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) (ir_select_eval (ir_getd s c) (ir_getd s a) (ir_getd s b)))
    (Bool.and (ir_byte_value_matches_v1 ctx ty (ir_getd s a)) (ir_byte_value_matches_v1 ctx ty (ir_getd s b)))
| IRInst.extractfield ty a field => ir_byte_scalar_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) (ir_byte_extract_field_v1 ctx site ty a (ir_getd s a) field)
| IRInst.insertfield ty a field value => ir_byte_scalar_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) (ir_byte_insert_field_v1 ctx site ty a (ir_getd s a) field value (ir_getd s value))
| IRInst.load ty p vol => ir_byte_memory_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) Bool.false (ir_byte_load_v1 ctx ty (ir_getd s p) (ir_byte_site_align_v1 site) vol (ir_byte_world_memory_v1 W w))
| IRInst.store ty p v vol => ir_byte_memory_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) Bool.true (ir_byte_store_v1 ctx ty (ir_getd s p) (ir_getd s v) (ir_byte_site_align_v1 site) vol (ir_byte_world_memory_v1 W w))
| IRInst.atomic_fetch_add_relaxed_u64_seq p v => ir_byte_memory_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) Bool.false (ir_byte_fetch_add_relaxed_u64_seq_v1 ctx (ir_getd s p) (ir_getd s v) (ir_byte_world_memory_v1 W w))
| IRInst.atomic_fetch_add_relaxed_usize_seq bits p v => ir_byte_memory_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) Bool.false (ir_byte_fetch_add_relaxed_usize_seq_v1 bits ctx (ir_getd s p) (ir_getd s v) (ir_byte_world_memory_v1 W w))
| IRInst.alloca ty count => ir_byte_alloca_exec_v1 W ctx s w rs site ty count
| IRInst.gep ty base indices inbounds => ir_byte_memory_result_v1 W ctx s w rs (ir_byte_site_results_v1 site) Bool.false (ir_byte_gep_site_v1 ctx site ty s base indices inbounds (ir_byte_world_memory_v1 W w))
| IRInst.br target args => ir_byte_jump_v1 W ctx s w target args
| IRInst.condbr c tt ta et ea =>
  match ir_getd s c with
  | IRScalar.bool_ b => @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W) (ir_byte_jump_v1 W ctx s w et ea) (ir_byte_jump_v1 W ctx s w tt ta) b
  | _ => @IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_bool) w
| IRInst.call fid args => ir_byte_call_v1 W ctx providers s w rs site fid args
| IRInst.callindirect callee sig args cc => ir_byte_call_indirect_v1 W ctx providers s w rs site (ir_getd s callee) sig args cc
| IRInst.ret args => ir_byte_return_v1 W ctx s w args
| IRInst.release pointer => @IRByteConfigV1.halted W (IROutcome.unmodelled IRFault.width_bounded) w
| _ => @IRByteConfigV1.halted W (IROutcome.unmodelled IRFault.width_bounded) w",
            "Versioned dispatch over actual IRInst: only the reflected scalar/control/byte/call profile executes; unsupported operations never enter legacy memory or call semantics.")?;
        for source in [
            r"def ir_byte_step_node_v1 (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W) (s : IRMachine) (w : IRByteWorldV1 W) (f : IRFrame) (node : IRNode) : IRByteConfigV1 W :=
match ir_byte_site_v1 ctx (ir_frame_func f) (ir_frame_block f) (ir_frame_pc f) with
| IROption.none => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.fetch_past_end) w
| IROption.some site =>
  match node with
  | IRNode.mk i rs =>
    @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
      (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) w)
      (ir_byte_exec_v1 W ctx providers s w site i rs)
      (ir_nat_eqb (ir_byte_length_v1 Nat rs) (ir_byte_length_v1 IRTy (ir_byte_site_results_v1 site)))",
            r"def ir_byte_step_machine_v1 (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W) (s : IRMachine) (w : IRByteWorldV1 W) : IRByteConfigV1 W :=
match ir_mach_frames s with
| IRList.nil => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_frame) w
| IRList.cons frame rest =>
  match ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx)) (ir_frame_func frame) with
  | IROption.none => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_func) w
  | IROption.some f =>
    match ir_block_find (ir_func_blocks f) (ir_frame_block frame) with
    | IROption.none => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_block) w
    | IROption.some b =>
      match ir_nodes_get (ir_block_nodes b) (ir_frame_pc frame) with
      | IROption.none => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.fetch_past_end) w
      | IROption.some node => ir_byte_step_node_v1 W ctx providers s w frame node",
            r"def ir_byte_step_v1 (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W) (c : IRByteConfigV1 W) : IRByteConfigV1 W :=
match c with
| IRByteConfigV1.halted outcome w => c
| IRByteConfigV1.running s w =>
  @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
    (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_addr) w)
    (ir_byte_step_machine_v1 W ctx providers s w)
    (ir_byte_world_valid_v1 W s w)",
        ] {
            self.add_recursive_def(source, "Byte-profile fetch/step preserving actual final world, checking exact site metadata and activation bookkeeping.")?;
        }
        Ok(())
    }

    fn add_eval_ir_byte_initialization(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(r"def ir_byte_init_v1 (W : Type) (ctx : IRByteContextV1) (fid : Nat) (args : IRList IRScalar) (mem : IRByteMemoryV1) (host : W) : IRByteConfigV1 W :=
let owner : Nat := ir_byte_fresh_owner_v1 mem;
let w : IRByteWorldV1 W := @IRByteWorldV1.mk W mem host (@IRList.cons Nat owner (@IRList.nil Nat)) (Nat.succ owner);
@Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
  (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_addr) w)
  (match ir_byte_function_v1 ctx fid with
   | IROption.none => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_func) w
   | IROption.some binding =>
     match ir_byte_signature_v1 ctx (ir_byte_binding_sig_v1 binding) with
     | IROption.none => @IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_fnptr) w
     | IROption.some sig =>
       match ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx)) fid with
       | IROption.none => @IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_func) w
       | IROption.some f =>
         @Bool.rec (fun (_ : Bool) => IRByteConfigV1 W)
           (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) w)
           (ir_byte_lift_v1 W w (ir_init (ir_byte_context_module_v1 ctx) fid args (@IRList.nil IRMemSlot) 0))
           (Bool.and (Bool.not (ir_byte_binding_import_v1 binding))
             (Bool.and (Bool.not (ir_byte_signature_vararg_v1 sig))
               (Bool.and (ir_nat_leb (ir_byte_binding_cc_v1 binding) 1)
                 (Bool.and (ir_nat_eqb (ir_byte_length_v1 Nat (ir_func_params f)) (ir_byte_length_v1 IRScalar args))
                   (ir_byte_values_match_v1 ctx (ir_byte_signature_params_v1 sig) args))))))
  (Bool.and (ir_nat_eqb (ir_byte_length_v1 IRGlobal (ir_mod_globals (ir_byte_context_module_v1 ctx))) 0)
    (ir_byte_memory_owners_v1 mem (@IRList.nil Nat) owner))",
            "Actual local entry with exact signature and caller-owned live memory. Fresh owner is greater than every historical allocation owner, permitting repeated top-level runs with retained retired memory. No globals or legacy cell memory; code-address injection and code/data separation remain explicit representation premises.")?;
        Ok(())
    }
}
