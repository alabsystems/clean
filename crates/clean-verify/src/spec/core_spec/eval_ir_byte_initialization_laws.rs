// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked local-entry initialization of the actual byte/world evaluator.
//!
//! Catalog and pre-memory premises are the real entry checks, not assumed
//! execution or post-validity. The activation owner is computed from every
//! historical allocation, including retired ones. These laws introduce no
//! provider, source-language, allocation-success, or native-fidelity premise.

use crate::spec::{SpecError, Specification};

const CHOOSE_POSITIVE: &str = r"def ir_byte_init_choose_positive_v1
  (a b : Nat) (ha : @Eq Bool (ir_nat_pos a) Bool.true)
  (hb : @Eq Bool (ir_nat_pos b) Bool.true) (flag : Bool) :
@Eq Bool (ir_nat_pos (@Bool.rec (fun (_ : Bool) => Nat) a b flag)) Bool.true :=
@Bool.rec
  (fun (x : Bool) => @Eq Bool (ir_nat_pos (@Bool.rec (fun (_ : Bool) => Nat) a b x)) Bool.true)
  ha hb flag";

const FRESH_POSITIVE: &str = r"def ir_byte_fresh_owner_positive_v1 (mem : IRByteMemoryV1) :
@Eq Bool (ir_nat_pos (ir_byte_fresh_owner_v1 mem)) Bool.true :=
@IRByteMemoryV1.rec
  (fun (m : IRByteMemoryV1) => @Eq Bool (ir_nat_pos (ir_byte_fresh_owner_v1 m)) Bool.true)
  (fun (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat) (cursor : Nat) =>
    @IRList.rec IRByteAllocationV1
      (fun (xs : IRList IRByteAllocationV1) =>
        @Eq Bool (ir_nat_pos (ir_byte_fresh_owner_v1 (IRByteMemoryV1.mk xs bytes cursor))) Bool.true)
      (@Eq.refl Bool Bool.true)
      (fun (a : IRByteAllocationV1) (rest : IRList IRByteAllocationV1)
        (ih : @Eq Bool (ir_nat_pos (ir_byte_fresh_owner_v1 (IRByteMemoryV1.mk rest bytes cursor))) Bool.true) =>
        ir_byte_init_choose_positive_v1
          (ir_byte_fresh_owner_v1 (IRByteMemoryV1.mk rest bytes cursor))
          (Nat.succ (ir_byte_alloc_owner_v1 a)) ih (@Eq.refl Bool Bool.true)
          (ir_nat_ltb (ir_byte_fresh_owner_v1 (IRByteMemoryV1.mk rest bytes cursor))
            (Nat.succ (ir_byte_alloc_owner_v1 a)))) allocs) mem";

const INITIAL_VALID: &str = r"def ir_byte_init_current_valid_v1
  (W : Type) (mem : IRByteMemoryV1) (host : W) (frame : IRFrame)
  (initialMemory : @Eq Bool
    (ir_byte_memory_owners_v1 mem (@IRList.nil Nat) (ir_byte_fresh_owner_v1 mem)) Bool.true) :
@Eq Bool (ir_byte_world_valid_v1 W
  (IRMachine.mk (@IRList.cons IRFrame frame (@IRList.nil IRFrame)) (@IRList.nil IRMemSlot) 0)
  (@IRByteWorldV1.mk W mem host
    (@IRList.cons Nat (ir_byte_fresh_owner_v1 mem) (@IRList.nil Nat))
    (Nat.succ (ir_byte_fresh_owner_v1 mem)))) Bool.true :=
ir_byte_world_and_intro_v1
  (ir_byte_owners_valid_v1
    (@IRList.cons Nat (ir_byte_fresh_owner_v1 mem) (@IRList.nil Nat))
    (Nat.succ (ir_byte_fresh_owner_v1 mem)))
  (ir_byte_memory_owners_v1 mem
    (@IRList.cons Nat (ir_byte_fresh_owner_v1 mem) (@IRList.nil Nat))
    (Nat.succ (ir_byte_fresh_owner_v1 mem)))
  (ir_byte_owners_push_v1 (@IRList.nil Nat) (ir_byte_fresh_owner_v1 mem)
    (ir_byte_fresh_owner_positive_v1 mem))
  (ir_byte_memory_owners_push_v1 mem (@IRList.nil Nat) (ir_byte_fresh_owner_v1 mem) initialMemory)";

const NO_GLOBALS: &str = r"def ir_byte_init_no_globals_v1 (m : IRModule)
  (noGlobals : @Eq (IRList IRGlobal) (ir_mod_globals m) (@IRList.nil IRGlobal)) :
@Eq Bool (ir_nat_eqb (ir_byte_length_v1 IRGlobal (ir_mod_globals m)) 0) Bool.true :=
ir_eq_cong (IRList IRGlobal) Bool
  (fun (globals : IRList IRGlobal) => ir_nat_eqb (ir_byte_length_v1 IRGlobal globals) 0)
  (ir_mod_globals m) (@IRList.nil IRGlobal) noGlobals";

fn frame() -> &'static str {
    "(IRFrame.mk (ir_func_id f) (ir_func_entry f) 0 (ir_bind_params (ir_func_params f) args (@IRList.nil IRBinding)) (@IRList.nil Nat))"
}

fn machine(globals: &str) -> String {
    format!(
        "(IRMachine.mk (@IRList.cons IRFrame {} (@IRList.nil IRFrame)) (ir_mem_concat (ir_globals_mem {globals}) (@IRList.nil IRMemSlot)) 0)",
        frame()
    )
}

fn legacy_source() -> String {
    let lookup = "(ir_func_find (ir_mod_funcs m) fid)";
    let actual = machine("(ir_mod_globals m)");
    let expected = machine("(@IRList.nil IRGlobal)");
    let body = machine("globals");
    format!(
        "def ir_byte_init_legacy_current_v1 (m : IRModule) (fid : Nat) (args : IRList IRScalar) (f : IRFunc)\n\
         (noGlobals : @Eq (IRList IRGlobal) (ir_mod_globals m) (@IRList.nil IRGlobal))\n\
         (found : @Eq (IROption IRFunc) {lookup} (@IROption.some IRFunc f)) :\n\
         @Eq IRConfig (ir_init m fid args (@IRList.nil IRMemSlot) 0) (IRConfig.running {expected}) :=\n\
         ir_byte_case_some_v1 IRFunc IRConfig {lookup} f\n\
           (IRConfig.halted (IROutcome.stuck IRFault.no_func))\n\
           (fun (f : IRFunc) => IRConfig.running {actual}) (IRConfig.running {expected}) found\n\
           (ir_eq_cong (IRList IRGlobal) IRConfig (fun (globals : IRList IRGlobal) => IRConfig.running {body})\n\
             (ir_mod_globals m) (@IRList.nil IRGlobal) noGlobals)"
    )
}

fn init_source() -> String {
    let module = "(ir_byte_context_module_v1 ctx)";
    let owner = "(ir_byte_fresh_owner_v1 mem)";
    let world = format!(
        "(@IRByteWorldV1.mk W mem host (@IRList.cons Nat {owner} (@IRList.nil Nat)) (Nat.succ {owner}))"
    );
    let result = "(IRByteConfigV1 W)";
    let expected = format!(
        "(@IRByteConfigV1.running W {} {world})",
        machine("(@IRList.nil IRGlobal)")
    );
    let raw = format!(
        "(ir_byte_lift_v1 W {world} (ir_init {module} fid args (@IRList.nil IRMemSlot) 0))"
    );
    let failure = |fault| format!("(@IRByteConfigV1.halted W ({fault}) {world})");
    let no_func = failure("IROutcome.stuck IRFault.no_func");
    let no_signature = failure("IROutcome.type_error IRFault.not_fnptr");
    let bad_field = failure("IROutcome.type_error IRFault.bad_field");
    let bad_memory = failure("IROutcome.type_error IRFault.bad_addr");
    let functions = format!("(ir_func_find (ir_mod_funcs {module}) fid)");
    let signatures = "(ir_byte_signature_v1 ctx (ir_byte_binding_sig_v1 binding))";
    let bindings = "(ir_byte_function_v1 ctx fid)";
    let admission = "(Bool.and (Bool.not (ir_byte_binding_import_v1 binding)) (Bool.and (Bool.not (ir_byte_signature_vararg_v1 signature)) (Bool.and (ir_nat_leb (ir_byte_binding_cc_v1 binding) 1) (Bool.and (ir_nat_eqb (ir_byte_length_v1 Nat (ir_func_params f)) (ir_byte_length_v1 IRScalar args)) (ir_byte_values_match_v1 ctx (ir_byte_signature_params_v1 signature) args)))))";
    let globals = format!("(ir_nat_eqb (ir_byte_length_v1 IRGlobal (ir_mod_globals {module})) 0)");
    let memory = format!("(ir_byte_memory_owners_v1 mem (@IRList.nil Nat) {owner})");
    let initial = format!("(Bool.and {globals} {memory})");
    let admitted_case =
        format!("(@Bool.rec (fun (_ : Bool) => {result}) {bad_field} {raw} {admission})");
    let function_case = format!(
        "(@IROption.rec IRFunc (fun (_ : IROption IRFunc) => {result}) {no_func} (fun (f : IRFunc) => {admitted_case}) {functions})"
    );
    let signature_case = format!(
        "(@IROption.rec IRByteSignatureV1 (fun (_ : IROption IRByteSignatureV1) => {result}) {no_signature} (fun (signature : IRByteSignatureV1) => {function_case}) {signatures})"
    );
    let binding_case = format!(
        "(@IROption.rec IRByteFunctionV1 (fun (_ : IROption IRByteFunctionV1) => {result}) {no_func} (fun (binding : IRByteFunctionV1) => {signature_case}) {bindings})"
    );
    format!(
        "def ir_byte_init_current_v1\n\
         (W : Type) (ctx : IRByteContextV1) (fid : Nat) (args : IRList IRScalar) (mem : IRByteMemoryV1) (host : W)\n\
         (binding : IRByteFunctionV1) (signature : IRByteSignatureV1) (f : IRFunc)\n\
         (noGlobals : @Eq (IRList IRGlobal) (ir_mod_globals {module}) (@IRList.nil IRGlobal))\n\
         (found : @Eq (IROption IRByteFunctionV1) {bindings} (@IROption.some IRByteFunctionV1 binding))\n\
         (signatureFound : @Eq (IROption IRByteSignatureV1) {signatures} (@IROption.some IRByteSignatureV1 signature))\n\
         (functionFound : @Eq (IROption IRFunc) {functions} (@IROption.some IRFunc f))\n\
         (initialMemory : @Eq Bool {memory} Bool.true)\n\
         (admitted : @Eq Bool {admission} Bool.true) :\n\
         @Eq {result} (ir_byte_init_v1 W ctx fid args mem host) {expected} :=\n\
         @Eq.trans {result} (ir_byte_init_v1 W ctx fid args mem host) {raw} {expected}\n\
           (ir_byte_case_true_v1 {result} {initial} {bad_memory} {binding_case} {raw}\n\
             (ir_byte_world_and_intro_v1 {globals} {memory} (ir_byte_init_no_globals_v1 {module} noGlobals) initialMemory)\n\
             (ir_byte_case_some_v1 IRByteFunctionV1 {result} {bindings} binding {no_func}\n\
               (fun (binding : IRByteFunctionV1) => {signature_case}) {raw} found\n\
               (ir_byte_case_some_v1 IRByteSignatureV1 {result} {signatures} signature {no_signature}\n\
                 (fun (signature : IRByteSignatureV1) => {function_case}) {raw} signatureFound\n\
                 (ir_byte_case_some_v1 IRFunc {result} {functions} f {no_func}\n\
                   (fun (f : IRFunc) => {admitted_case}) {raw} functionFound\n\
                   (ir_byte_case_true_v1 {result} {admission} {bad_field} {raw} {raw} admitted (@Eq.refl {result} {raw}))))))\n\
           (ir_eq_cong IRConfig {result} (fun (config : IRConfig) => ir_byte_lift_v1 W {world} config)\n\
             (ir_init {module} fid args (@IRList.nil IRMemSlot) 0) (IRConfig.running {})\n\
             (ir_byte_init_legacy_current_v1 {module} fid args f noGlobals functionFound))",
        machine("(@IRList.nil IRGlobal)")
    )
}

fn laws() -> [(&'static str, String); 6] {
    [
        ("ir_byte_init_choose_positive_v1", CHOOSE_POSITIVE.into()),
        ("ir_byte_fresh_owner_positive_v1", FRESH_POSITIVE.into()),
        ("ir_byte_init_current_valid_v1", INITIAL_VALID.into()),
        ("ir_byte_init_no_globals_v1", NO_GLOBALS.into()),
        ("ir_byte_init_legacy_current_v1", legacy_source()),
        ("ir_byte_init_current_v1", init_source()),
    ]
}

impl Specification {
    pub(super) fn add_eval_ir_byte_initialization_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(&source, "Checked actual local-entry initialization and derived fresh world validity; no assumed postcondition.")
                .map_err(|error| match error {
                    SpecError::ParseError(detail) => SpecError::ParseError(format!("{name}: {detail}")),
                    SpecError::ElabError(detail) => SpecError::ElabError(format!("{name}: {detail}")),
                    SpecError::TypeError(detail) => SpecError::TypeError(format!("{name}: {detail}")),
                    other => other,
                })?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_initialization_tests.rs"]
mod tests;
