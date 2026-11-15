// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Operational rules for the actual byte evaluator's imported calls.
//!
//! Returned memory and host state are explicit and may differ from their inputs.
//! The real owner check establishes bookkeeping, not byte preservation, allocation
//! disjointness, high-water preservation, or fidelity to a native provider. Results
//! are arbitrary typed lists: a C aggregate occupies one SSA result, not one result
//! per field. Import return advances the current frame once and does not push or
//! pop an activation owner. These equations do not provide publication authority.

use crate::spec::{SpecError, Specification};

const RESULT: &str = "(IRByteConfigV1 W)";
const MACHINE: &str = "(IRMachine.mk (@IRList.cons IRFrame current tail) legacy cursor)";
const UPDATED: &str = "(ir_frame_advance (ir_frame_set_many current destinations values))";
const WORLD: &str = "(@IRByteWorldV1.mk W returnedMemory returnedHost
    (ir_byte_world_owners_v1 W world) (ir_byte_world_next_v1 W world))";
const MEMORY_GUARD: &str = "(ir_byte_memory_owners_v1 returnedMemory
    (ir_byte_world_owners_v1 W world) (ir_byte_world_next_v1 W world))";
const ARITY: &str = "(ir_nat_eqb (ir_byte_length_v1 Nat destinations)
    (ir_byte_length_v1 IRScalar values))";
const TYPED: &str = "(ir_byte_values_match_v1 ctx types values)";

fn imported_call_source() -> String {
    let no_func = "(@IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_func) world)";
    let bad_field = "(@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) world)";
    let not_function = "(@IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_fnptr) world)";
    let local_success = "(ir_byte_lift_v1 W (ir_byte_push_owner_v1 W world)
        (ir_push machine destinations callee arguments))";
    let local_shape = "(ir_nat_eqb (ir_byte_length_v1 Nat (ir_func_params callee))
        (ir_byte_length_v1 IRScalar arguments))";
    let local = format!(
        "(@IROption.rec IRFunc (fun (_ : IROption IRFunc) => {RESULT}) {no_func}
        (fun (callee : IRFunc) => @Bool.rec (fun (_ : Bool) => {RESULT})
          {bad_field} {local_success} {local_shape})
        (ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx))
          (ir_byte_binding_fid_v1 binding)))"
    );
    let imported = "(ir_byte_import_result_v1 W ctx machine world destinations
        (ir_byte_signature_returns_v1 signature)
        (providers (ir_byte_binding_fid_v1 binding) arguments
          (ir_byte_world_memory_v1 W world) (ir_byte_world_host_v1 W world)))";
    let guard = "(Bool.and (Bool.not (ir_byte_signature_vararg_v1 signature))
      (Bool.and (ir_nat_leb (ir_byte_binding_cc_v1 binding) 1)
        (Bool.and (ir_nat_eqb (ir_byte_site_cc_v1 site) (ir_byte_binding_cc_v1 binding))
          (Bool.and (ir_nat_eqb (ir_byte_length_v1 Nat destinations) (ir_byte_length_v1 IRTy (ir_byte_signature_returns_v1 signature)))
            (Bool.and (ir_byte_ty_list_eq_v1 (ir_byte_site_results_v1 site) (ir_byte_signature_returns_v1 signature))
              (ir_byte_values_match_v1 ctx (ir_byte_signature_params_v1 signature) arguments))))))";
    let import_flag = "(ir_byte_binding_import_v1 binding)";
    format!("def ir_byte_import_call_rule_v1
      (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W)
      (machine : IRMachine) (world : IRByteWorldV1 W) (destinations : IRList Nat)
      (site : IRByteSiteV1) (binding : IRByteFunctionV1) (signature : IRByteSignatureV1)
      (arguments : IRList IRScalar)
      (imported : @Eq Bool {import_flag} Bool.true)
      (admitted : @Eq Bool {guard} Bool.true) :
    @Eq {RESULT}
      (ir_byte_call_known_v1 W ctx providers machine world destinations site binding signature arguments)
      {imported} :=
    ir_byte_case_true_v1 {RESULT} {guard} {not_function}
      (@Bool.rec (fun (_ : Bool) => {RESULT}) {local} {imported} {import_flag})
      {imported} admitted
      (ir_byte_case_true_v1 {RESULT} {import_flag} {local} {imported} {imported}
        imported (@Eq.refl {RESULT} {imported}))")
}

fn return_telescope() -> String {
    format!(
        "(W : Type) (ctx : IRByteContextV1)
      (current : IRFrame) (tail : IRList IRFrame) (legacy : IRList IRMemSlot) (cursor : Nat)
      (world : IRByteWorldV1 W) (destinations : IRList Nat) (types : IRList IRTy)
      (values : IRList IRScalar) (returnedMemory : IRByteMemoryV1) (returnedHost : W)
      (owners : @Eq Bool {MEMORY_GUARD} Bool.true)
      (arity : @Eq Bool {ARITY} Bool.true)
      (typed : @Eq Bool {TYPED} Bool.true)"
    )
}

fn returned() -> String {
    format!(
        "(ir_byte_import_result_v1 W ctx {MACHINE} world destinations types
      (@IRByteImportResultV1.mk W (IROutcome.ret values) returnedMemory returnedHost))"
    )
}

fn expected() -> String {
    format!(
        "(@IRByteConfigV1.running W
      (IRMachine.mk (@IRList.cons IRFrame {UPDATED} tail) legacy cursor) {WORLD})"
    )
}

fn import_return_source() -> String {
    let expected = expected();
    let bad_memory =
        format!("(@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_addr) {WORLD})");
    let bad_values =
        format!("(@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) {WORLD})");
    let bind =
        format!("(ir_byte_bind_values_v1 W ctx {MACHINE} {WORLD} destinations types values)");
    let guard = format!("(Bool.and {ARITY} {TYPED})");
    format!(
        "def ir_byte_import_return_rule_v1 {} :
      @Eq {RESULT} {} {expected} :=
    ir_byte_case_true_v1 {RESULT} {MEMORY_GUARD} {bad_memory} {bind} {expected} owners
      (ir_byte_case_true_v1 {RESULT} {guard} {bad_values} {expected} {expected}
        (ir_byte_world_and_intro_v1 {ARITY} {TYPED} arity typed)
        (@Eq.refl {RESULT} {expected}))",
        return_telescope(),
        returned()
    )
}

fn and(a: &str, b: &str) -> String {
    format!("(Bool.and {a} {b})")
}

fn left(a: &str, b: &str, proof: &str) -> String {
    format!("(ir_byte_world_and_left_v1 {a} {b} {proof})")
}

fn right(a: &str, b: &str, proof: &str) -> String {
    format!("(ir_byte_world_and_right_v1 {a} {b} {proof})")
}

fn join(a: &str, b: &str, pa: &str, pb: &str) -> String {
    format!("(ir_byte_world_and_intro_v1 {a} {b} {pa} {pb})")
}

fn world_shape_source() -> String {
    // Frame contents do not occur in the world guard, only stack length. The
    // memory premise is precisely the production import check, not a claim that
    // the provider preserved the previous allocation or byte maps.
    let empty = "(ir_nat_eqb (ir_byte_length_v1 IRMemSlot legacy) 0)";
    let count = "(ir_nat_eqb (ir_byte_length_v1 IRFrame (@IRList.cons IRFrame current tail))
        (ir_byte_length_v1 Nat (ir_byte_world_owners_v1 W world)))";
    let owners = "(ir_byte_owners_valid_v1 (ir_byte_world_owners_v1 W world)
        (ir_byte_world_next_v1 W world))";
    let old_memory = "(ir_byte_memory_owners_v1 (ir_byte_world_memory_v1 W world)
        (ir_byte_world_owners_v1 W world) (ir_byte_world_next_v1 W world))";
    let tail_guard = and(count, &and(owners, old_memory));
    let empty_proof = left(empty, &tail_guard, "before");
    let tail_proof = right(empty, &tail_guard, "before");
    let count_proof = left(count, &and(owners, old_memory), &tail_proof);
    let owners_proof = left(
        owners,
        old_memory,
        &right(count, &and(owners, old_memory), &tail_proof),
    );
    let proof = join(
        empty,
        &and(count, &and(owners, MEMORY_GUARD)),
        &empty_proof,
        &join(
            count,
            &and(owners, MEMORY_GUARD),
            &count_proof,
            &join(owners, MEMORY_GUARD, &owners_proof, "memoryOwners"),
        ),
    );
    format!(
        "def ir_byte_import_world_shape_v1
      (W : Type) (world : IRByteWorldV1 W) (current updated : IRFrame)
      (tail : IRList IRFrame) (legacy : IRList IRMemSlot) (cursor : Nat)
      (returnedMemory : IRByteMemoryV1) (returnedHost : W)
      (before : @Eq Bool (ir_byte_world_valid_v1 W {MACHINE} world) Bool.true)
      (memoryOwners : @Eq Bool {MEMORY_GUARD} Bool.true) :
    @Eq Bool (ir_byte_world_valid_v1 W
      (IRMachine.mk (@IRList.cons IRFrame updated tail) legacy cursor) {WORLD}) Bool.true :=
    {proof}"
    )
}

fn import_return_world_source() -> String {
    let predicate = "(fun (c : IRByteConfigV1 W) =>
      @IRByteConfigV1.rec W (fun (_ : IRByteConfigV1 W) => Prop)
        (fun (machine : IRMachine) (world : IRByteWorldV1 W) =>
          @Eq Bool (ir_byte_world_valid_v1 W machine world) Bool.true)
        (fun (_ : IROutcome) (_ : IRByteWorldV1 W) => False) c)";
    let actual = returned();
    let expected = expected();
    format!(
        "def ir_byte_import_return_world_v1 {}
      (before : @Eq Bool (ir_byte_world_valid_v1 W {MACHINE} world) Bool.true) :
    {predicate} {actual} :=
    @Eq.subst {RESULT} {predicate} {expected} {actual}
      (@Eq.symm {RESULT} {actual} {expected}
        (ir_byte_import_return_rule_v1 W ctx current tail legacy cursor world destinations types
          values returnedMemory returnedHost owners arity typed))
      (ir_byte_import_world_shape_v1 W world current {UPDATED} tail legacy cursor
        returnedMemory returnedHost before owners)",
        return_telescope()
    )
}

fn laws() -> [(&'static str, String); 4] {
    [
        ("ir_byte_import_call_rule_v1", imported_call_source()),
        ("ir_byte_import_return_rule_v1", import_return_source()),
        ("ir_byte_import_world_shape_v1", world_shape_source()),
        (
            "ir_byte_import_return_world_v1",
            import_return_world_source(),
        ),
    ]
}

impl Specification {
    /// Install checked import rules after the byte machine, access and world laws.
    /// No provider implementation or external memory preservation is certified.
    pub(super) fn add_eval_ir_byte_import_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(&source,
                "Actual imported-call result/host/memory rule; no provider fidelity or native authority.")
                .map_err(|error| SpecError::TypeError(format!("{name}: {error}")))?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_import_tests.rs"]
mod tests;
