// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Separate LOGICAL Rust U64 entry; no physical calling-convention theorem.
//! Old ByteV1 C/Fast definitions, constructors and admissibility remain unchanged.
use crate::spec::{SpecError, Specification};

const INITIALIZE: &str = r#"def ir_rust_u64_init_v1 (W : Type) (ctx : IRByteContextV1) (fid : Nat) (args : IRList IRScalar) (mem : IRByteMemoryV1) (host : W) : IRByteConfigV1 W :=
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
           (Bool.and (ir_byte_ty_list_eq_v1 (ir_byte_signature_params_v1 sig) (@IRList.cons IRTy (IRTy.uint_ 64) (@IRList.nil IRTy)))
            (Bool.and (ir_byte_ty_list_eq_v1 (ir_byte_signature_returns_v1 sig) (@IRList.cons IRTy (IRTy.uint_ 64) (@IRList.nil IRTy)))
              (Bool.and (Bool.not (ir_byte_binding_import_v1 binding))
                (Bool.and (Bool.not (ir_byte_signature_vararg_v1 sig))
                  (Bool.and (ir_nat_eqb (ir_byte_binding_cc_v1 binding) 3)
                    (Bool.and (ir_nat_eqb (ir_byte_length_v1 Nat (ir_func_params f)) (ir_byte_length_v1 IRScalar args))
                      (ir_byte_values_match_v1 ctx (ir_byte_signature_params_v1 sig) args))))))))
  (Bool.and (ir_nat_eqb (ir_byte_length_v1 IRGlobal (ir_mod_globals (ir_byte_context_module_v1 ctx))) 0)
    (ir_byte_memory_owners_v1 mem (@IRList.nil Nat) owner))"#;

fn frame() -> &'static str {
    "(IRFrame.mk (ir_func_id f) (ir_func_entry f) 0 (ir_bind_params (ir_func_params f) args (@IRList.nil IRBinding)) (@IRList.nil Nat))"
}

fn machine(globals: &str) -> String {
    format!(
        "(IRMachine.mk (@IRList.cons IRFrame {} (@IRList.nil IRFrame)) (ir_mem_concat (ir_globals_mem {globals}) (@IRList.nil IRMemSlot)) 0)",
        frame()
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
    let admission = "(Bool.and (ir_byte_ty_list_eq_v1 (ir_byte_signature_params_v1 signature) (@IRList.cons IRTy (IRTy.uint_ 64) (@IRList.nil IRTy))) (Bool.and (ir_byte_ty_list_eq_v1 (ir_byte_signature_returns_v1 signature) (@IRList.cons IRTy (IRTy.uint_ 64) (@IRList.nil IRTy))) (Bool.and (Bool.not (ir_byte_binding_import_v1 binding)) (Bool.and (Bool.not (ir_byte_signature_vararg_v1 signature)) (Bool.and (ir_nat_eqb (ir_byte_binding_cc_v1 binding) 3) (Bool.and (ir_nat_eqb (ir_byte_length_v1 Nat (ir_func_params f)) (ir_byte_length_v1 IRScalar args)) (ir_byte_values_match_v1 ctx (ir_byte_signature_params_v1 signature) args)))))))";
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
        "def ir_rust_u64_init_current_v1\n\
         (W : Type) (ctx : IRByteContextV1) (fid : Nat) (args : IRList IRScalar) (mem : IRByteMemoryV1) (host : W)\n\
         (binding : IRByteFunctionV1) (signature : IRByteSignatureV1) (f : IRFunc)\n\
         (noGlobals : @Eq (IRList IRGlobal) (ir_mod_globals {module}) (@IRList.nil IRGlobal))\n\
         (found : @Eq (IROption IRByteFunctionV1) {bindings} (@IROption.some IRByteFunctionV1 binding))\n\
         (signatureFound : @Eq (IROption IRByteSignatureV1) {signatures} (@IROption.some IRByteSignatureV1 signature))\n\
         (functionFound : @Eq (IROption IRFunc) {functions} (@IROption.some IRFunc f))\n\
         (initialMemory : @Eq Bool {memory} Bool.true)\n\
         (admitted : @Eq Bool {admission} Bool.true) :\n\
         @Eq {result} (ir_rust_u64_init_v1 W ctx fid args mem host) {expected} :=\n\
         @Eq.trans {result} (ir_rust_u64_init_v1 W ctx fid args mem host) {raw} {expected}\n\
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

impl Specification {
    /// Extend a canonical ByteV1 environment with a separately named logical
    /// Rust U64 entry and its universally checked initialization law. This is
    /// mathematical vocabulary, never a native/source/ABI admission certificate.
    pub fn into_rust_u64_logical_entry_v1(mut self) -> Result<Self, SpecError> {
        let previous = self.definitions().keys().cloned().collect();
        self.add_recursive_def(INITIALIZE, "Explicit Rust wire convention3, exact U64 logical signature; all original memory/catalog/value checks retained")?;
        self.verify_definition("ir_rust_u64_init_v1")?;
        self.add_recursive_def(&init_source(), "Actual ir_init positional parameter/entry binding under the exact Rust logical entry checks; arbitrary initial memory and host")?;
        self.verify_definition("ir_rust_u64_init_current_v1")?;
        self.verify_eval_ir_byte_additions_v1(&previous)?;
        Ok(self)
    }
}
