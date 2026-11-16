// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Hand-built import-helper witnesses, not a reflected-module validation,
//! provider-fidelity proof, or native execution certificate.

use super::*;
use clean_kernel::Name;

fn checked(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).expect("installed import law");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(name).unwrap();
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(source, "Actual imported-call consumer")
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    checked(spec, name);
}

fn reject(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Invalid imported-call conclusion")
        .expect_err(name);
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn specification() -> Specification {
    Specification::new_eval_ir_byte_prelude_spec_v1().unwrap()
}

fn list(ty: &str, values: &[&str]) -> String {
    values
        .iter()
        .rev()
        .fold(format!("(@IRList.nil {ty})"), |tail, value| {
            format!("(@IRList.cons {ty} {value} {tail})")
        })
}

const PAIR: &str = "(IRScalar.aggv (IRScalar.vcons (IRScalar.int_ 7)
    (IRScalar.vcons (IRScalar.int_ 0) IRScalar.vnil)))";
const CURRENT: &str = "(IRFrame.mk 9 7 2
    (@IRList.cons IRBinding (IRBinding.mk 40 (IRScalar.ptr_ 64)) (@IRList.nil IRBinding))
    (@IRList.nil Nat))";
const TAIL: &str = "(@IRList.cons IRFrame
    (IRFrame.mk 3 5 12 (@IRList.cons IRBinding (IRBinding.mk 88 (IRScalar.bool_ Bool.false))
      (@IRList.nil IRBinding)) (@IRList.nil Nat)) (@IRList.nil IRFrame))";
const LEGACY: &str = "(@IRList.nil IRMemSlot)";
const OWNERS: &str = "(@IRList.cons Nat 2 (@IRList.cons Nat 1 (@IRList.nil Nat)))";
const ROWS: &str = "(@IRList.cons IRByteAllocationV1
    (IRByteAllocationV1.mk 16 8 1 Bool.true) (@IRList.nil IRByteAllocationV1))";
const BINDING: &str = "(IRByteFunctionV1.mk 55 4 4096 0 Bool.true)";
const SIGNATURE: &str = "(IRByteSignatureV1.mk 4
    (@IRList.cons IRTy IRTy.ptr_ (@IRList.nil IRTy))
    (@IRList.cons IRTy (IRTy.struct_ 9) (@IRList.nil IRTy)) Bool.false)";
const TRUE: &str = "(@Eq.refl Bool Bool.true)";

fn install_context(spec: &mut Specification) {
    let layout = "(IRByteLayoutV1.mk (IRTy.struct_ 9) 16 8
      (@IRList.cons IRTy (IRTy.uint_ 64) (@IRList.cons IRTy (IRTy.int_ 64) (@IRList.nil IRTy)))
      (@IRList.cons Nat 0 (@IRList.cons Nat 8 (@IRList.nil Nat))))";
    // Only helper/call catalogs are exercised: the current frame is not fetched
    // from this empty module, and no global module-validity claim is made.
    add(
        spec,
        "import_test_context",
        &format!(
            "def import_test_context : IRByteContextV1 :=
      IRByteContextV1.mk (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal))
        {} {} {} (@IRList.nil IRByteSiteV1)",
            list("IRByteLayoutV1", &[layout]),
            list("IRByteSignatureV1", &[SIGNATURE]),
            list("IRByteFunctionV1", &[BINDING])
        ),
    );
}

fn memory(bytes: &str) -> String {
    format!("(IRByteMemoryV1.mk {ROWS} {bytes} 64)")
}

fn changed_memory(bytes: &str) -> String {
    memory(&format!("(ir_byte_write_word_v1 {bytes} 16 8 99)"))
}

fn world(mem: &str, host: &str) -> String {
    format!("(@IRByteWorldV1.mk Nat {mem} {host} {OWNERS} 5)")
}

fn machine() -> String {
    format!("(IRMachine.mk (@IRList.cons IRFrame {CURRENT} {TAIL}) {LEGACY} 1)")
}

fn next_machine(destinations: &str, values: &str, advance: usize) -> String {
    let mut current = format!("(ir_frame_set_many {CURRENT} {destinations} {values})");
    for _ in 0..advance {
        current = format!("(ir_frame_advance {current})");
    }
    format!("(IRMachine.mk (@IRList.cons IRFrame {current} {TAIL}) {LEGACY} 1)")
}

fn import_actual(destinations: &str, types: &str, values: &str, returned_memory: &str) -> String {
    format!(
        "(ir_byte_import_result_v1 Nat import_test_context {} {} {destinations} {types}
      (@IRByteImportResultV1.mk Nat (IROutcome.ret {values}) {returned_memory} (Nat.succ host)))",
        machine(),
        world(&memory("bytes"), "host")
    )
}

fn return_proof(destinations: &str, types: &str, values: &str, returned_memory: &str) -> String {
    format!(
        "(ir_byte_import_return_rule_v1 Nat import_test_context {CURRENT} {TAIL} {LEGACY} 1
      {} {destinations} {types} {values} {returned_memory} (Nat.succ host) {TRUE} {TRUE} {TRUE})",
        world(&memory("bytes"), "host")
    )
}

fn direct_call_claim(
    name: &str,
    unchanged_memory: bool,
    unchanged_host: bool,
    advance: usize,
) -> String {
    let results = list("Nat", &["99"]);
    let types = list("IRTy", &["(IRTy.struct_ 9)"]);
    let values = list("IRScalar", &[PAIR]);
    let site = format!("(IRByteSiteV1.mk 9 7 2 0 0 {types})");
    let args = list("Nat", &["40"]);
    let old = world(&memory("bytes"), "host");
    let new_memory = changed_memory("bytes");
    let provider = format!(
        "(fun (_ : Nat) (_ : IRList IRScalar) (mem : IRByteMemoryV1) (host : Nat) =>
      @IRByteImportResultV1.mk Nat (IROutcome.ret {values})
        (IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 mem)
          (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) 16 8 99) (ir_byte_mem_next_v1 mem))
        (Nat.succ host))"
    );
    let actual = format!(
        "(ir_byte_call_v1 Nat import_test_context {provider} {} {old} {results} {site} 55 {args})",
        machine()
    );
    let middle = format!(
        "(ir_byte_call_known_v1 Nat import_test_context {provider} {} {old} {results}
      {site} {BINDING} {SIGNATURE} (ir_resolve {} {args}))",
        machine(),
        machine()
    );
    let imported = import_actual(&results, &types, &values, &new_memory);
    let actual_expected = format!(
        "(@IRByteConfigV1.running Nat {} {})",
        next_machine(&results, &values, 1),
        world(&new_memory, "(Nat.succ host)")
    );
    let claimed = format!(
        "(@IRByteConfigV1.running Nat {} {})",
        next_machine(&results, &values, advance),
        world(
            &if unchanged_memory {
                memory("bytes")
            } else {
                new_memory.clone()
            },
            if unchanged_host {
                "host"
            } else {
                "(Nat.succ host)"
            }
        )
    );
    format!(
        "def {name} (bytes : Nat -> IROption Nat) (host : Nat) :
      @Eq (IRByteConfigV1 Nat) {actual} {claimed} :=
      @Eq.trans (IRByteConfigV1 Nat) {actual} {middle} {actual_expected}
        (ir_byte_call_of_catalog_v1 Nat import_test_context {provider} {} {old} {results}
          {site} 55 {args} {BINDING} {SIGNATURE}
          (@Eq.refl (IROption IRByteFunctionV1) (@IROption.some IRByteFunctionV1 {BINDING}))
          (@Eq.refl (IROption IRByteSignatureV1) (@IROption.some IRByteSignatureV1 {SIGNATURE})))
        (@Eq.trans (IRByteConfigV1 Nat) {middle} {imported} {actual_expected}
          (ir_byte_import_call_rule_v1 Nat import_test_context {provider} {} {old} {results}
            {site} {BINDING} {SIGNATURE} (ir_resolve {} {args}) {TRUE} {TRUE})
          {})",
        machine(),
        machine(),
        machine(),
        return_proof(&results, &types, &values, &new_memory)
    )
}

#[test]
fn byte_import_all_quantified_roots_replay_without_axioms_or_trust() {
    let spec = specification();
    for (name, _) in laws() {
        checked(&spec, name);
    }
}

#[test]
fn byte_import_aggregate_is_one_result_and_retains_changed_bytes_and_host() {
    let mut spec = specification();
    install_context(&mut spec);
    add(
        &mut spec,
        "import_pair_changed",
        &direct_call_claim("import_pair_changed", false, false, 1),
    );
    let results = list("Nat", &["99"]);
    let types = list("IRTy", &["(IRTy.struct_ 9)"]);
    let values = list("IRScalar", &[PAIR]);
    let returned_memory = changed_memory("bytes");
    let actual = import_actual(&results, &types, &values, &returned_memory);
    let predicate = "(fun (c : IRByteConfigV1 Nat) => @IRByteConfigV1.rec Nat
      (fun (_ : IRByteConfigV1 Nat) => Prop)
      (fun (s : IRMachine) (w : IRByteWorldV1 Nat) => @Eq Bool (ir_byte_world_valid_v1 Nat s w) Bool.true)
      (fun (_ : IROutcome) (_ : IRByteWorldV1 Nat) => False) c)";
    add(&mut spec, "import_pair_world", &format!("def import_pair_world
      (bytes : Nat -> IROption Nat) (host : Nat) : {predicate} {actual} :=
      ir_byte_import_return_world_v1 Nat import_test_context {CURRENT} {TAIL} {LEGACY} 1
        {} {results} {types} {values} {returned_memory} (Nat.succ host) {TRUE} {TRUE} {TRUE} {TRUE}",
        world(&memory("bytes"), "host")));
    // The write is observable at an admitted byte address, independently of
    // whole-map equality; arbitrary initial bytes need not already contain 99.
    add(
        &mut spec,
        "import_changed_byte",
        &format!(
            "def import_changed_byte
      (bytes : Nat -> IROption Nat) :
      @Eq (IROption Nat) (ir_byte_mem_bytes_v1 {returned_memory} 16) (@IROption.some Nat 99) :=
      @Eq.refl (IROption Nat) (@IROption.some Nat 99)"
        ),
    );
}

#[test]
fn byte_import_actual_arity_type_owner_and_fault_checks_keep_returned_world() {
    let mut spec = specification();
    install_context(&mut spec);
    let results = list("Nat", &["99"]);
    let pair_types = list("IRTy", &["(IRTy.struct_ 9)"]);
    let pair_values = list("IRScalar", &[PAIR]);
    let changed = changed_memory("bytes");
    let orphan = format!(
        "(IRByteMemoryV1.mk {} (ir_byte_mem_bytes_v1 {changed}) 64)",
        list(
            "IRByteAllocationV1",
            &["(IRByteAllocationV1.mk 16 8 3 Bool.true)"]
        )
    );
    let bad_dead = orphan.replace("3 Bool.true", "5 Bool.false");
    let admitted_dead = orphan.replace("3 Bool.true", "3 Bool.false");
    for (name, rs, ts, mem, fault) in [
        (
            "import_wrong_arity",
            list("Nat", &["99", "100"]),
            pair_types.clone(),
            changed.clone(),
            "IRFault.bad_field",
        ),
        (
            "import_wrong_type",
            results.clone(),
            list("IRTy", &["(IRTy.uint_ 64)"]),
            changed.clone(),
            "IRFault.bad_field",
        ),
        (
            "import_live_orphan",
            results.clone(),
            pair_types.clone(),
            orphan,
            "IRFault.bad_addr",
        ),
        (
            "import_dead_future_owner",
            results.clone(),
            pair_types.clone(),
            bad_dead,
            "IRFault.bad_addr",
        ),
    ] {
        let actual = import_actual(&rs, &ts, &pair_values, &mem);
        let expected = format!(
            "(@IRByteConfigV1.halted Nat (IROutcome.type_error {fault}) {})",
            world(&mem, "(Nat.succ host)")
        );
        add(
            &mut spec,
            name,
            &format!(
                "def {name} (bytes : Nat -> IROption Nat) (host : Nat) :
          @Eq (IRByteConfigV1 Nat) {actual} {expected} := @Eq.refl (IRByteConfigV1 Nat) {expected}"
            ),
        );
    }
    // Retired historical owners below next are admitted; rejecting every dead
    // row would incorrectly strengthen the actual provider check.
    for (name, rs, ts, vs, mem) in [
        (
            "import_old_dead_owner",
            results,
            pair_types,
            pair_values,
            admitted_dead,
        ),
        (
            "import_empty_results",
            list("Nat", &[]),
            list("IRTy", &[]),
            list("IRScalar", &[]),
            changed.clone(),
        ),
        (
            "import_multiple_results",
            list("Nat", &["99", "100"]),
            list("IRTy", &["(IRTy.uint_ 64)", "IRTy.bool_"]),
            list(
                "IRScalar",
                &["(IRScalar.int_ 7)", "(IRScalar.bool_ Bool.true)"],
            ),
            changed.clone(),
        ),
    ] {
        let actual = import_actual(&rs, &ts, &vs, &mem);
        let expected = format!(
            "(@IRByteConfigV1.running Nat {} {})",
            next_machine(&rs, &vs, 1),
            world(&mem, "(Nat.succ host)")
        );
        add(
            &mut spec,
            name,
            &format!(
                "def {name} (bytes : Nat -> IROption Nat) (host : Nat) :
          @Eq (IRByteConfigV1 Nat) {actual} {expected} := {}",
                return_proof(&rs, &ts, &vs, &mem)
            ),
        );
    }
    let fault = "(IROutcome.ub IRFault.null_deref)";
    let expected = format!(
        "(@IRByteConfigV1.halted Nat {fault} {})",
        world(&changed, "(Nat.succ host)")
    );
    add(
        &mut spec,
        "import_fault_world",
        &format!(
            "def import_fault_world
      (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat)
      (ir_byte_import_result_v1 Nat import_test_context {} {} (@IRList.nil Nat) (@IRList.nil IRTy)
        (@IRByteImportResultV1.mk Nat {fault} {changed} (Nat.succ host))) {expected} :=
      @Eq.refl (IRByteConfigV1 Nat) {expected}",
            machine(),
            world(&memory("bytes"), "host")
        ),
    );
}

#[test]
fn byte_import_rejects_lost_effects_and_wrong_advancement() {
    let mut spec = specification();
    install_context(&mut spec);
    for (name, old_memory, old_host, advance) in [
        ("import_bad_old_memory", true, false, 1),
        ("import_bad_old_host", false, true, 1),
        ("import_bad_no_advance", false, false, 0),
        ("import_bad_double_advance", false, false, 2),
    ] {
        reject(
            &mut spec,
            name,
            &direct_call_claim(name, old_memory, old_host, advance),
        );
    }
    let rs = list("Nat", &["99", "100"]);
    let types = list("IRTy", &["(IRTy.struct_ 9)"]);
    let values = list("IRScalar", &[PAIR]);
    let mem = changed_memory("bytes");
    let actual = import_actual(&rs, &types, &values, &mem);
    let expected = format!(
        "(@IRByteConfigV1.running Nat {} {})",
        next_machine(&rs, &values, 1),
        world(&mem, "(Nat.succ host)")
    );
    reject(
        &mut spec,
        "import_bad_pair_as_two_results",
        &format!(
            "def import_bad_pair_as_two_results
      (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {actual} {expected} :=
      {}",
            return_proof(&rs, &types, &values, &mem)
        ),
    );
}
