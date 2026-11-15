// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compositional call/return rules for the actual byte/world evaluator.
//!
//! Catalog and guard premises refer to the real module and dispatch checks.
//! They do not assume a callee's answer. Return preserves the *current* host
//! state and memory, retires exactly the returning activation, and binds all
//! result lanes without advancing the already-advanced caller a second time.
//! Callee execution, world validity, provider fidelity and native refinement
//! remain consuming obligations, not consequences of these operational rules.

use crate::spec::{SpecError, Specification};

const PUSH_FRAME: &str = r"def ir_byte_push_frame_v1
  (W : Type) (mem : IRByteMemoryV1) (host : W) (owners : IRList Nat) (next : Nat)
  (caller : IRFrame) (tail : IRList IRFrame) (legacy : IRList IRMemSlot) (cursor : Nat)
  (destinations : IRList Nat) (callee : IRFunc) (values : IRList IRScalar) :
@Eq (IRByteConfigV1 W)
  (ir_byte_lift_v1 W
    (ir_byte_push_owner_v1 W (@IRByteWorldV1.mk W mem host owners next))
    (ir_push (IRMachine.mk (@IRList.cons IRFrame caller tail) legacy cursor) destinations callee values))
  (@IRByteConfigV1.running W
    (IRMachine.mk
      (@IRList.cons IRFrame
        (IRFrame.mk (ir_func_id callee) (ir_func_entry callee) 0
          (ir_bind_params (ir_func_params callee) values (@IRList.nil IRBinding)) destinations)
        (@IRList.cons IRFrame (ir_frame_advance caller) tail)) legacy cursor)
    (@IRByteWorldV1.mk W mem host (@IRList.cons Nat next owners) (Nat.succ next))) :=
@Eq.refl (IRByteConfigV1 W)
  (@IRByteConfigV1.running W
    (IRMachine.mk
      (@IRList.cons IRFrame
        (IRFrame.mk (ir_func_id callee) (ir_func_entry callee) 0
          (ir_bind_params (ir_func_params callee) values (@IRList.nil IRBinding)) destinations)
        (@IRList.cons IRFrame (ir_frame_advance caller) tail)) legacy cursor)
    (@IRByteWorldV1.mk W mem host (@IRList.cons Nat next owners) (Nat.succ next)))";

fn internal_call_source() -> String {
    let result = "(IRByteConfigV1 W)";
    let failure = |fault: &str| format!("(@IRByteConfigV1.halted W ({fault}) world)");
    let no_func = failure("IROutcome.stuck IRFault.no_func");
    let bad_field = failure("IROutcome.type_error IRFault.bad_field");
    let not_function = failure("IROutcome.type_error IRFault.not_fnptr");
    let expected = "(ir_byte_lift_v1 W (ir_byte_push_owner_v1 W world) (ir_push machine destinations callee values))";
    let shape = "(ir_nat_eqb (ir_byte_length_v1 Nat (ir_func_params callee)) (ir_byte_length_v1 IRScalar values))";
    let local = format!(
        "(@IROption.rec IRFunc (fun (_ : IROption IRFunc) => {result}) {no_func}\n\
         (fun (callee : IRFunc) => @Bool.rec (fun (_ : Bool) => {result})\n\
           {bad_field} {expected} {shape})\n\
         (ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx)) (ir_byte_binding_fid_v1 binding)))"
    );
    let imported = "(ir_byte_import_result_v1 W ctx machine world destinations (ir_byte_signature_returns_v1 signature) (providers (ir_byte_binding_fid_v1 binding) values (ir_byte_world_memory_v1 W world) (ir_byte_world_host_v1 W world)))";
    let guard = "(Bool.and (Bool.not (ir_byte_signature_vararg_v1 signature))
      (Bool.and (ir_nat_leb (ir_byte_binding_cc_v1 binding) 1)
        (Bool.and (ir_nat_eqb (ir_byte_site_cc_v1 site) (ir_byte_binding_cc_v1 binding))
          (Bool.and (ir_nat_eqb (ir_byte_length_v1 Nat destinations) (ir_byte_length_v1 IRTy (ir_byte_signature_returns_v1 signature)))
            (Bool.and (ir_byte_ty_list_eq_v1 (ir_byte_site_results_v1 site) (ir_byte_signature_returns_v1 signature))
              (ir_byte_values_match_v1 ctx (ir_byte_signature_params_v1 signature) values))))))";
    format!(
        "def ir_byte_internal_call_rule_v1\n\
         (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W)\n\
         (machine : IRMachine) (world : IRByteWorldV1 W) (destinations : IRList Nat)\n\
         (site : IRByteSiteV1) (binding : IRByteFunctionV1) (signature : IRByteSignatureV1)\n\
         (values : IRList IRScalar) (callee : IRFunc)\n\
         (localBinding : @Eq Bool (ir_byte_binding_import_v1 binding) Bool.false)\n\
         (bodyLookup : @Eq (IROption IRFunc)\n\
           (ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx)) (ir_byte_binding_fid_v1 binding))\n\
           (@IROption.some IRFunc callee))\n\
         (arity : @Eq Bool {shape} Bool.true)\n\
         (admitted : @Eq Bool {guard} Bool.true) :\n\
         @Eq {result} (ir_byte_call_known_v1 W ctx providers machine world destinations site binding signature values)\n\
           {expected} :=\n\
         ir_byte_case_true_v1 {result} {guard} {not_function}\n\
           (@Bool.rec (fun (_ : Bool) => {result}) {local} {imported} (ir_byte_binding_import_v1 binding))\n\
           {expected} admitted\n\
           (@Eq.subst Bool\n\
             (fun (isImport : Bool) => @Eq {result}\n\
               (@Bool.rec (fun (_ : Bool) => {result}) {local} {imported} isImport) {expected})\n\
             Bool.false (ir_byte_binding_import_v1 binding)\n\
             (@Eq.symm Bool (ir_byte_binding_import_v1 binding) Bool.false localBinding)\n\
             (ir_byte_case_some_v1 IRFunc {result}\n\
               (ir_func_find (ir_mod_funcs (ir_byte_context_module_v1 ctx)) (ir_byte_binding_fid_v1 binding))\n\
               callee {no_func}\n\
               (fun (callee : IRFunc) => @Bool.rec (fun (_ : Bool) => {result}) {bad_field} {expected} {shape})\n\
               {expected} bodyLookup\n\
               (ir_byte_case_true_v1 {result} {shape} {bad_field} {expected} {expected} arity\n\
                 (@Eq.refl {result} {expected}))))"
    )
}

fn indirect_call_source() -> String {
    let result = "(IRByteConfigV1 W)";
    let expected =
        "(ir_byte_call_v1 W ctx providers machine world destinations site fid arguments)";
    let guard = "(Bool.and (ir_nat_eqb signature (ir_byte_binding_sig_v1 binding)) (ir_nat_eqb convention (ir_byte_site_cc_v1 site)))";
    let failure = "(@IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_fnptr) world)";
    format!(
        "def ir_byte_indirect_call_exact_v1\n\
         (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W)\n\
         (machine : IRMachine) (world : IRByteWorldV1 W) (destinations : IRList Nat)\n\
         (site : IRByteSiteV1) (fid : Nat) (signature : Nat) (arguments : IRList Nat)\n\
         (convention : Nat) (binding : IRByteFunctionV1)\n\
         (found : @Eq (IROption IRByteFunctionV1) (ir_byte_function_v1 ctx fid) (@IROption.some IRByteFunctionV1 binding))\n\
         (exact : @Eq Bool {guard} Bool.true) :\n\
         @Eq {result}\n\
           (ir_byte_call_indirect_v1 W ctx providers machine world destinations site (IRScalar.fnptr_ fid) signature arguments convention)\n\
           {expected} :=\n\
         ir_byte_case_some_v1 IRByteFunctionV1 {result} (ir_byte_function_v1 ctx fid) binding\n\
           (@IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_func) world)\n\
           (fun (binding : IRByteFunctionV1) => @Bool.rec (fun (_ : Bool) => {result}) {failure} {expected} {guard})\n\
           {expected} found\n\
           (ir_byte_case_true_v1 {result} {guard} {failure} {expected} {expected} exact\n\
             (@Eq.refl {result} {expected}))"
    )
}

fn direct_call_source() -> String {
    let result = "(IRByteConfigV1 W)";
    let expected = "(ir_byte_call_known_v1 W ctx providers machine world destinations site binding signature (ir_resolve machine arguments))";
    let signature_lookup = "(ir_byte_signature_v1 ctx (ir_byte_binding_sig_v1 binding))";
    let signature_failure =
        "(@IRByteConfigV1.halted W (IROutcome.type_error IRFault.not_fnptr) world)";
    let signature_case = format!(
        "(@IROption.rec IRByteSignatureV1 (fun (_ : IROption IRByteSignatureV1) => {result}) {signature_failure}\n\
         (fun (signature : IRByteSignatureV1) => {expected}) {signature_lookup})"
    );
    format!(
        "def ir_byte_call_of_catalog_v1\n\
         (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W)\n\
         (machine : IRMachine) (world : IRByteWorldV1 W) (destinations : IRList Nat)\n\
         (site : IRByteSiteV1) (fid : Nat) (arguments : IRList Nat)\n\
         (binding : IRByteFunctionV1) (signature : IRByteSignatureV1)\n\
         (found : @Eq (IROption IRByteFunctionV1) (ir_byte_function_v1 ctx fid) (@IROption.some IRByteFunctionV1 binding))\n\
         (signatureFound : @Eq (IROption IRByteSignatureV1) {signature_lookup} (@IROption.some IRByteSignatureV1 signature)) :\n\
         @Eq {result} (ir_byte_call_v1 W ctx providers machine world destinations site fid arguments) {expected} :=\n\
         ir_byte_case_some_v1 IRByteFunctionV1 {result} (ir_byte_function_v1 ctx fid) binding\n\
           (@IRByteConfigV1.halted W (IROutcome.stuck IRFault.no_func) world)\n\
           (fun (binding : IRByteFunctionV1) => {signature_case}) {expected} found\n\
           (ir_byte_case_some_v1 IRByteSignatureV1 {result} {signature_lookup} signature {signature_failure}\n\
             (fun (signature : IRByteSignatureV1) => {expected}) {expected} signatureFound\n\
             (@Eq.refl {result} {expected}))"
    )
}

fn return_to_caller_source() -> String {
    let result = "(IRByteConfigV1 W)";
    let machine = "(IRMachine.mk (@IRList.cons IRFrame returning (@IRList.cons IRFrame caller tail)) legacy cursor)";
    let world = "(@IRByteWorldV1.mk W memory host (@IRList.cons Nat owner owners) next)";
    let resolved = format!("(ir_resolve {machine} arguments)");
    let failure = |fault: &str| format!("(@IRByteConfigV1.halted W ({fault}) {world})");
    let no_function = failure("IROutcome.stuck IRFault.no_func");
    let not_function = failure("IROutcome.type_error IRFault.not_fnptr");
    let bad_field = failure("IROutcome.type_error IRFault.bad_field");
    let expected = format!(
        "(@IRByteConfigV1.running W\n\
           (IRMachine.mk (@IRList.cons IRFrame (ir_frame_set_many caller (ir_frame_dests returning) {resolved}) tail) legacy cursor)\n\
           (@IRByteWorldV1.mk W (ir_byte_retire_v1 owner memory) host owners next))"
    );
    let success = format!(
        "(ir_byte_lift_v1 W (ir_byte_pop_owner_v1 W {world}) (ir_ret_vals {machine} {resolved}))"
    );
    let guard = format!(
        "(Bool.and (ir_byte_values_match_v1 ctx (ir_byte_signature_returns_v1 signature) {resolved})\n\
           (ir_nat_eqb (ir_byte_length_v1 Nat (ir_frame_dests returning)) (ir_byte_length_v1 Nat arguments)))"
    );
    let lookup_signature = "(ir_byte_signature_v1 ctx (ir_byte_binding_sig_v1 binding))";
    let signature_case = format!(
        "(@IROption.rec IRByteSignatureV1 (fun (_ : IROption IRByteSignatureV1) => {result}) {not_function}\n\
           (fun (signature : IRByteSignatureV1) => @Bool.rec (fun (_ : Bool) => {result}) {bad_field} {success} {guard})\n\
           {lookup_signature})"
    );
    format!(
        "def ir_byte_return_to_caller_v1\n\
         (W : Type) (ctx : IRByteContextV1) (returning : IRFrame) (caller : IRFrame) (tail : IRList IRFrame)\n\
         (legacy : IRList IRMemSlot) (cursor : Nat) (memory : IRByteMemoryV1) (host : W)\n\
         (owner : Nat) (owners : IRList Nat) (next : Nat) (arguments : IRList Nat)\n\
         (binding : IRByteFunctionV1) (signature : IRByteSignatureV1)\n\
         (found : @Eq (IROption IRByteFunctionV1) (ir_byte_function_v1 ctx (ir_frame_func returning)) (@IROption.some IRByteFunctionV1 binding))\n\
         (signatureFound : @Eq (IROption IRByteSignatureV1) {lookup_signature} (@IROption.some IRByteSignatureV1 signature))\n\
         (admitted : @Eq Bool {guard} Bool.true) :\n\
         @Eq {result} (ir_byte_return_v1 W ctx {machine} {world} arguments) {expected} :=\n\
         ir_byte_case_some_v1 IRByteFunctionV1 {result}\n\
           (ir_byte_function_v1 ctx (ir_frame_func returning)) binding {no_function}\n\
           (fun (binding : IRByteFunctionV1) => {signature_case}) {expected} found\n\
           (ir_byte_case_some_v1 IRByteSignatureV1 {result} {lookup_signature} signature {not_function}\n\
             (fun (signature : IRByteSignatureV1) => @Bool.rec (fun (_ : Bool) => {result}) {bad_field} {success} {guard})\n\
             {expected} signatureFound\n\
             (ir_byte_case_true_v1 {result} {guard} {bad_field} {success} {expected} admitted\n\
               (@Eq.refl {result} {expected})))"
    )
}

fn laws() -> [(&'static str, String); 5] {
    [
        ("ir_byte_push_frame_v1", PUSH_FRAME.to_owned()),
        ("ir_byte_internal_call_rule_v1", internal_call_source()),
        ("ir_byte_call_of_catalog_v1", direct_call_source()),
        ("ir_byte_indirect_call_exact_v1", indirect_call_source()),
        ("ir_byte_return_to_caller_v1", return_to_caller_source()),
    ]
}

impl Specification {
    pub(super) fn add_eval_ir_byte_call_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(
                &source,
                "Checked actual byte/world call or return rule; catalog/type premises do not assume callee execution or native fidelity.",
            )
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
#[path = "eval_ir_byte_call_tests.rs"]
mod consumers;

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    fn spec() -> Specification {
        Specification::new_eval_ir_byte_prelude_spec_v1().unwrap()
    }

    fn checked(spec: &Specification, name: &str) {
        let definition = spec.get_definition(name).expect("registered call law");
        assert!(!definition.is_axiom);
        assert!(definition.elaborated_value.is_some());
        spec.verify_definition(name)
            .expect("independent kernel replay");
        let name = Name::from_string(name);
        assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
        assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
    }

    #[test]
    fn quantified_call_return_rules_are_kernel_checked() {
        crate::test_utils::run_with_stack(|| {
            let spec = spec();
            for (name, _) in laws() {
                checked(&spec, name);
            }
        });
    }

    #[test]
    fn call_return_rules_reject_lost_frames_and_wrong_continuations() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            for (name, original, before, after) in [
                (
                    "bad_call_unadvanced",
                    PUSH_FRAME.to_owned(),
                    "(ir_frame_advance caller)",
                    "caller",
                ),
                (
                    "bad_call_no_owner",
                    PUSH_FRAME.to_owned(),
                    "(@IRList.cons Nat next owners)",
                    "owners",
                ),
                (
                    "bad_return_live",
                    return_to_caller_source(),
                    "(ir_byte_retire_v1 owner memory)",
                    "memory",
                ),
                (
                    "bad_return_owner",
                    return_to_caller_source(),
                    "(ir_byte_retire_v1 owner memory)",
                    "(ir_byte_retire_v1 next memory)",
                ),
                (
                    "bad_return_double_advance",
                    return_to_caller_source(),
                    "ir_frame_set_many caller",
                    "ir_frame_set_many (ir_frame_advance caller)",
                ),
                (
                    "bad_indirect_guard",
                    indirect_call_source(),
                    "(exact : @Eq Bool",
                    "(exact : @Eq Bool",
                ),
            ] {
                let (header, proof) = original.split_once(":=").unwrap();
                let old_name = header.split_whitespace().nth(1).unwrap();
                let changed = if name == "bad_indirect_guard" {
                    header.replace("Bool.true)", "Bool.false)")
                } else {
                    assert!(header.contains(before), "mutation must act on conclusion");
                    header.replace(before, after)
                };
                let source = format!("{} := {proof}", changed.replacen(old_name, name, 1));
                let error = spec
                    .add_recursive_def(
                        &source,
                        "Adversarial mutation of actual call/return conclusion",
                    )
                    .expect_err(name);
                crate::test_utils::assert_type_mismatch_rejection(&error, name);
                assert!(spec.get_definition(name).is_none());
            }
        });
    }
}
