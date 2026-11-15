// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Kernel replay of actual parameter/current-frame binding, not source refinement.

use super::*;
use clean_kernel::Name;

fn checked(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).expect("installed binding law");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(name).unwrap();
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

#[test]
fn byte_binding_public_constructor_rechecks_all_roots() {
    let spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
    for (name, _) in laws() {
        checked(&spec, name);
    }
}

fn add_checked(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(source, "Actual positional binding consumer")
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    checked(spec, name);
}

fn reject(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Invalid binding or lookup claim")
        .expect_err(name);
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn list(ty: &str, values: &[String]) -> String {
    values
        .iter()
        .rev()
        .fold(format!("(IRList.nil {ty})"), |tail, value| {
            format!("(IRList.cons {ty} ({value}) {tail})")
        })
}

fn ids(values: &[u64]) -> String {
    list(
        "Nat",
        &values.iter().map(u64::to_string).collect::<Vec<_>>(),
    )
}

fn first(ids_in: &[u64], index: usize) -> String {
    let key = ids_in[index];
    let mut proof = format!("(Eq.refl Nat {key})");
    for offset in (0..index).rev() {
        let id = ids_in[offset];
        proof = format!(
            "(@And.intro (Eq Bool (ir_nat_eqb {id} {key}) Bool.false)
              (ir_byte_first_param_v1 {} {} {key}) (Eq.refl Bool Bool.false) {proof})",
            ids(&ids_in[offset + 1..]),
            index - offset - 1,
        );
    }
    proof
}

fn avoid(ids_in: &[u64], key: u64) -> String {
    let mut proof = "True.intro".to_owned();
    for offset in (0..ids_in.len()).rev() {
        let id = ids_in[offset];
        proof = format!(
            "(@And.intro (Eq Bool (ir_nat_eqb {id} {key}) Bool.false)
              (ir_byte_ids_avoid_v1 {} {key}) (Eq.refl Bool Bool.false) {proof})",
            ids(&ids_in[offset + 1..]),
        );
    }
    proof
}

const FORMALS: [u64; 5] = [101, 7, 43, 211, 89];

fn arguments(context: &str, state: &str, helper: &str, capture: &str) -> Vec<String> {
    vec![
        format!("IRScalar.ptr_ {context}"),
        format!("IRScalar.ptr_ {state}"),
        "IRScalar.nullptr_".into(),
        format!("IRScalar.fnptr_ {helper}"),
        format!("IRScalar.ptr_ {capture}"),
    ]
}

fn frame(arguments: &[String], locals: &str) -> String {
    format!(
        "(IRFrame.mk 301 91 0 (ir_bind_params {} {} {locals}) {})",
        ids(&FORMALS),
        list("IRScalar", arguments),
        ids(&[601, 17, 77, 98, 320]),
    )
}

fn machine(frame: &str, tail: &str) -> String {
    format!("(IRMachine.mk (IRList.cons IRFrame {frame} {tail}) (IRList.nil IRMemSlot) 0)")
}

#[test]
fn byte_binding_five_arguments_and_fresh_results_preserve_exact_values() {
    let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
    let values = arguments("context", "state", "helper", "capture");
    let value_list = list("IRScalar", &values);
    let current = frame(&values, "locals");
    // These are the physical five incoming lanes. Declaration environment is
    // null; the last lane is a distinct captured environment. Arbitrary caller
    // frames and previous locals cannot replace any freshly bound parameter.
    for (index, value) in values.iter().enumerate() {
        let key = FORMALS[index];
        let name = format!("binding_five_{index}");
        add_checked(&mut spec, &name, &format!(
            "def {name} (context state helper capture : Nat)
              (locals : IRList IRBinding) (tail : IRList IRFrame) :
            Eq IRScalar (ir_getd {} {key}) ({value}) :=
            ir_byte_getd_param_at_v1 301 91 0 {} tail (IRList.nil IRMemSlot) 0
              {} {value_list} {index} locals {key} ({value}) {} (Eq.refl (IROption IRScalar) (IROption.some IRScalar ({value})))",
            machine(&current, "tail"), ids(&[601, 17, 77, 98, 320]), ids(&FORMALS), first(&FORMALS, index),
        ));
    }
    // The real byte-result helper advances frame_set_many. Three successive
    // fresh bindings model a pair-valued import result and its two extracts;
    // no claim is made here about the import's semantics or actual SSA code.
    let pair = "IRScalar.aggv (IRScalar.vcons (IRScalar.int_ 0) (IRScalar.vcons (IRScalar.int_ 17) IRScalar.vnil))";
    let steps = [
        (1001, pair),
        (1002, "IRScalar.int_ 0"),
        (1003, "IRScalar.int_ 17"),
    ];
    let mut frames = vec![current.clone()];
    for (id, value) in steps {
        frames.push(format!(
            "(ir_frame_advance (ir_frame_set_many {} {} {}))",
            frames.last().unwrap(),
            ids(&[id]),
            list("IRScalar", &[value.to_owned()])
        ));
    }
    for index in [3, 4] {
        let key = FORMALS[index];
        let value = &values[index];
        let mut proof = format!("binding_five_{index} context state helper capture locals tail");
        for (step, (id, result)) in steps.iter().enumerate() {
            proof = format!(
                "Eq.trans IRScalar (ir_frame_get {} {key}) (ir_frame_get {} {key}) ({value})
                  (ir_byte_frame_advance_set_preserves_v1 {} {} {} {key} {}) ({proof})",
                frames[step + 1],
                frames[step],
                frames[step],
                ids(&[*id]),
                list("IRScalar", &[(*result).to_owned()]),
                avoid(&[*id], key),
            );
        }
        let name = format!("binding_guard_preserves_{index}");
        add_checked(
            &mut spec,
            &name,
            &format!(
                "def {name} (context state helper capture : Nat)
              (locals : IRList IRBinding) (tail : IRList IRFrame) :
            Eq IRScalar (ir_getd {} {key}) ({value}) := {proof}",
                machine(frames.last().unwrap(), "tail"),
            ),
        );
    }
}

#[test]
fn byte_binding_head_first_truncation_and_current_frame_are_exact() {
    let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
    let duplicate_ids = ids(&[11, 11]);
    let pair = list(
        "IRScalar",
        &["IRScalar.fnptr_ 41".into(), "IRScalar.fnptr_ 42".into()],
    );
    add_checked(&mut spec, "binding_duplicate_head_wins", &format!(
        "def binding_duplicate_head_wins (locals : IRList IRBinding) :
        Eq (IROption IRScalar) (ir_binding_lookup (ir_bind_params {duplicate_ids} {pair} locals) 11)
          (IROption.some IRScalar (IRScalar.fnptr_ 41)) :=
        ir_byte_bind_params_at_v1 {duplicate_ids} {pair} 0 locals 11 (IRScalar.fnptr_ 41)
          (Eq.refl Nat 11) (Eq.refl (IROption IRScalar) (IROption.some IRScalar (IRScalar.fnptr_ 41)))"
    ));
    let short = list("IRScalar", &["IRScalar.ptr_ 16".into()]);
    let old = list("IRBinding", &["IRBinding.mk 22 (IRScalar.ptr_ 99)".into()]);
    add_checked(
        &mut spec,
        "binding_short_prefix_leaves_old_tail",
        &format!(
            "def binding_short_prefix_leaves_old_tail :
        Eq (IROption IRScalar) (ir_binding_lookup (ir_bind_params {} {short} {old}) 22)
          (IROption.some IRScalar (IRScalar.ptr_ 99)) :=
        Eq.refl (IROption IRScalar) (IROption.some IRScalar (IRScalar.ptr_ 99))",
            ids(&[11, 22])
        ),
    );
    add_checked(&mut spec, "binding_short_prefix_keeps_first", &format!(
        "def binding_short_prefix_keeps_first (locals : IRList IRBinding) :
        Eq (IROption IRScalar) (ir_binding_lookup (ir_bind_params {} {short} locals) 11)
          (IROption.some IRScalar (IRScalar.ptr_ 16)) :=
        ir_byte_bind_params_at_v1 {} {short} 0 locals 11 (IRScalar.ptr_ 16)
          (Eq.refl Nat 11) (Eq.refl (IROption IRScalar) (IROption.some IRScalar (IRScalar.ptr_ 16)))",
        ids(&[11, 22]), ids(&[11, 22]),
    ));
    let caller = format!("(IRFrame.mk 301 91 18 {old} (IRList.nil Nat))");
    let callee = "(IRFrame.mk 407 13 0 (IRList.nil IRBinding) (IRList.nil Nat))";
    let state = machine(callee, &list("IRFrame", &[caller]));
    add_checked(
        &mut spec,
        "binding_no_caller_fallback",
        &format!(
            "def binding_no_caller_fallback : Eq IRScalar (ir_getd {state} 22) IRScalar.undef_ :=
          Eq.refl IRScalar IRScalar.undef_"
        ),
    );
    reject(&mut spec, "binding_caller_fallback_is_wrong", &format!(
        "def binding_caller_fallback_is_wrong : Eq IRScalar (ir_getd {state} 22) (IRScalar.ptr_ 99) :=
          binding_no_caller_fallback"
    ));
    // Fresh additions also preserve *absence*, not only initialized values.
    add_checked(&mut spec, "binding_unbound_stays_unbound", &format!(
        "def binding_unbound_stays_unbound :
        Eq (IROption IRScalar) (ir_binding_lookup (ir_bind_params {} {short} (IRList.nil IRBinding)) 22)
          (IROption.none IRScalar) :=
        ir_byte_bind_params_preserves_v1 {} {short} (IRList.nil IRBinding) 22 {}",
        ids(&[11]), ids(&[11]), avoid(&[11], 22),
    ));
}

#[test]
fn byte_binding_rejects_swaps_alias_helpers_stale_and_missing_arguments() {
    let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
    let values = arguments("16", "32", "41", "80");
    let value_list = list("IRScalar", &values);
    let bindings = format!(
        "(ir_bind_params {} {value_list} (IRList.nil IRBinding))",
        ids(&FORMALS)
    );
    // Both function identities satisfy the same function type in an actual
    // two-entry catalog. Type compatibility does not prove identity equality.
    let catalog = list(
        "IRByteFunctionV1",
        &[
            "IRByteFunctionV1.mk 41 17 4096 1 Bool.false".into(),
            "IRByteFunctionV1.mk 42 17 8192 1 Bool.false".into(),
        ],
    );
    add_checked(&mut spec, "binding_same_signature_context", &format!(
        "def binding_same_signature_context : IRByteContextV1 :=
        IRByteContextV1.mk (IRModule.mk (IRList.nil IRFunc) (IRList.nil IRGlobal))
          (IRList.nil IRByteLayoutV1) (IRList.nil IRByteSignatureV1) {catalog} (IRList.nil IRByteSiteV1)"
    ));
    for helper in [41, 42] {
        let name = format!("binding_helper_{helper}_fits");
        add_checked(&mut spec, &name, &format!(
            "def {name} : Eq Bool
              (ir_byte_value_matches_v1 binding_same_signature_context (IRTy.func_ 17) (IRScalar.fnptr_ {helper})) Bool.true :=
              Eq.refl Bool Bool.true"
        ));
    }
    for (name, index, claimed) in [
        (
            "binding_wrong_same_signature_helper",
            3,
            "IRScalar.fnptr_ 42",
        ),
        ("binding_declaration_is_not_capture", 2, "IRScalar.ptr_ 80"),
        ("binding_capture_is_not_declaration", 4, "IRScalar.nullptr_"),
        ("binding_context_is_not_state", 0, "IRScalar.ptr_ 32"),
    ] {
        let key = FORMALS[index];
        let actual = &values[index];
        reject(&mut spec, name, &format!(
            "def {name} : Eq (IROption IRScalar) (ir_binding_lookup {bindings} {key}) (IROption.some IRScalar ({claimed})) :=
            ir_byte_bind_params_at_v1 {} {value_list} {index} (IRList.nil IRBinding) {key} ({actual}) {}
              (Eq.refl (IROption IRScalar) (IROption.some IRScalar ({actual})))",
            ids(&FORMALS), first(&FORMALS, index),
        ));
    }
    let mut swapped = values.clone();
    swapped.swap(2, 4);
    reject(
        &mut spec,
        "binding_swapped_actual_arguments",
        &format!(
            "def binding_swapped_actual_arguments : Eq (IROption IRScalar)
          (ir_binding_lookup (ir_bind_params {} {} (IRList.nil IRBinding)) 89)
          (IROption.some IRScalar (IRScalar.ptr_ 80)) :=
        ir_byte_bind_params_at_v1 {} {value_list} 4 (IRList.nil IRBinding) 89 (IRScalar.ptr_ 80) {}
          (Eq.refl (IROption IRScalar) (IROption.some IRScalar (IRScalar.ptr_ 80)))",
            ids(&FORMALS),
            list("IRScalar", &swapped),
            ids(&FORMALS),
            first(&FORMALS, 4),
        ),
    );
    let overwritten = list("IRScalar", &["IRScalar.ptr_ 96".into()]);
    reject(
        &mut spec,
        "binding_stale_lookup_after_overwrite",
        &format!(
            "def binding_stale_lookup_after_overwrite : Eq (IROption IRScalar)
          (ir_binding_lookup (ir_bind_params {} {overwritten} {bindings}) 89)
          (ir_binding_lookup {bindings} 89) :=
        ir_byte_bind_params_preserves_v1 {} {overwritten} {bindings} 89 {}",
            ids(&[89]),
            ids(&[89]),
            avoid(&[89], 89),
        ),
    );
    reject(
        &mut spec,
        "binding_duplicate_before_selected_id",
        &format!(
            "def binding_duplicate_before_selected_id : Eq (IROption IRScalar)
          (ir_binding_lookup (ir_bind_params {} {} (IRList.nil IRBinding)) 11)
          (IROption.some IRScalar (IRScalar.fnptr_ 42)) :=
        ir_byte_bind_params_at_v1 {} {} 1 (IRList.nil IRBinding) 11 (IRScalar.fnptr_ 42) {}
          (Eq.refl (IROption IRScalar) (IROption.some IRScalar (IRScalar.fnptr_ 42)))",
            ids(&[11, 11]),
            list(
                "IRScalar",
                &["IRScalar.fnptr_ 41".into(), "IRScalar.fnptr_ 42".into()]
            ),
            ids(&[11, 11]),
            list(
                "IRScalar",
                &["IRScalar.fnptr_ 41".into(), "IRScalar.fnptr_ 42".into()]
            ),
            first(&[11, 11], 1),
        ),
    );
    let missing = list("IRScalar", &values[..4]);
    reject(
        &mut spec,
        "binding_missing_capture_argument",
        &format!(
            "def binding_missing_capture_argument : Eq (IROption IRScalar)
          (ir_binding_lookup (ir_bind_params {} {missing} (IRList.nil IRBinding)) 89)
          (IROption.some IRScalar (IRScalar.ptr_ 80)) :=
        ir_byte_bind_params_at_v1 {} {missing} 4 (IRList.nil IRBinding) 89 (IRScalar.ptr_ 80) {}
          (Eq.refl (IROption IRScalar) (IROption.some IRScalar (IRScalar.ptr_ 80)))",
            ids(&FORMALS),
            ids(&FORMALS),
            first(&FORMALS, 4),
        ),
    );
}
