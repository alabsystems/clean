// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual public initialization-law kernel replay; not a whole source proof.

use super::*;
use clean_kernel::Name;

fn checked(spec: &Specification, name: &str) {
    let definition = spec
        .get_definition(name)
        .expect("installed initialization law");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(name).unwrap();
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

#[test]
fn byte_initialization_public_constructor_rechecks_all_roots() {
    let spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
    for (name, _) in laws() {
        checked(&spec, name);
    }
}

fn add(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(source, "Actual generic byte initialization consumer")
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    checked(spec, name);
}

fn reject(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Invalid initialization claim")
        .expect_err(name);
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn list(ty: &str, values: &[&str]) -> String {
    values
        .iter()
        .rev()
        .fold(format!("(@IRList.nil {ty})"), |tail, value| {
            format!("(@IRList.cons {ty} {value} {tail})")
        })
}

const ARGS: &str = "(@IRList.cons IRScalar (IRScalar.ptr_ 16) (@IRList.cons IRScalar (IRScalar.ptr_ 48) (@IRList.nil IRScalar)))";
const BINDINGS: &str = "(@IRList.cons IRBinding (IRBinding.mk 31 (IRScalar.ptr_ 16)) (@IRList.cons IRBinding (IRBinding.mk 7 (IRScalar.ptr_ 48)) (@IRList.nil IRBinding)))";
const INITIAL_FRAME: &str = "(IRFrame.mk 41 17 0 init_test_bindings (@IRList.nil Nat))";
const TRUE: &str = "(@Eq.refl Bool Bool.true)";

fn context_source(name: &str, imported: bool, vararg: bool, cc: u64, globals: &str) -> String {
    let params = list("Nat", &["31", "7"]);
    let parameter_types = list("IRTy", &["IRTy.ptr_", "IRTy.ptr_"]);
    let nodes = list(
        "IRNode",
        &["(IRNode.mk (IRInst.ret (@IRList.nil Nat)) (@IRList.nil Nat))"],
    );
    let blocks = list("IRBlock", &[&format!("(IRBlock.mk 17 {params} {nodes})")]);
    let function = format!("(IRFunc.mk 41 {params} 17 {blocks})");
    let signature =
        format!("(IRByteSignatureV1.mk 79 {parameter_types} (@IRList.nil IRTy) Bool.{vararg})");
    let binding = format!("(IRByteFunctionV1.mk 41 79 4096 {cc} Bool.{imported})");
    let site = "(IRByteSiteV1.mk 41 17 0 0 0 (@IRList.nil IRTy))";
    format!(
        "def {name} : IRByteContextV1 := IRByteContextV1.mk
      (IRModule.mk {} {globals})
      {} {} {} {}",
        list("IRFunc", &[&function]),
        list(
            "IRByteLayoutV1",
            &["(IRByteLayoutV1.mk IRTy.ptr_ 8 8 (@IRList.nil IRTy) (@IRList.nil Nat))"]
        ),
        list("IRByteSignatureV1", &[&signature]),
        list("IRByteFunctionV1", &[&binding]),
        list("IRByteSiteV1", &[site])
    )
}

fn specification() -> Specification {
    let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
    add(
        &mut spec,
        "init_test_context",
        &context_source(
            "init_test_context",
            false,
            false,
            0,
            "(@IRList.nil IRGlobal)",
        ),
    );
    let params = list("Nat", &["31", "7"]);
    let nodes = list(
        "IRNode",
        &["(IRNode.mk (IRInst.ret (@IRList.nil Nat)) (@IRList.nil Nat))"],
    );
    let blocks = list("IRBlock", &[&format!("(IRBlock.mk 17 {params} {nodes})")]);
    add(
        &mut spec,
        "init_test_function",
        &format!("def init_test_function : IRFunc := IRFunc.mk 41 {params} 17 {blocks}"),
    );
    add(
        &mut spec,
        "init_test_signature",
        &format!(
            "def init_test_signature : IRByteSignatureV1 := IRByteSignatureV1.mk 79 {} (@IRList.nil IRTy) Bool.false",
            list("IRTy", &["IRTy.ptr_", "IRTy.ptr_"])
        ),
    );
    add(
        &mut spec,
        "init_test_binding",
        "def init_test_binding : IRByteFunctionV1 := IRByteFunctionV1.mk 41 79 4096 0 Bool.false",
    );
    add(
        &mut spec,
        "init_test_args",
        &format!("def init_test_args : IRList IRScalar := {ARGS}"),
    );
    add(
        &mut spec,
        "init_test_bindings",
        &format!("def init_test_bindings : IRList IRBinding := {BINDINGS}"),
    );
    // Two live external (owner0) allocations, and two retired activations in
    // non-monotone list order. Arbitrary bytes may be initialized or undefined.
    let rows = list(
        "IRByteAllocationV1",
        &[
            "(IRByteAllocationV1.mk 16 16 0 Bool.true)",
            "(IRByteAllocationV1.mk 80 8 7 Bool.false)",
            "(IRByteAllocationV1.mk 48 16 0 Bool.true)",
            "(IRByteAllocationV1.mk 96 8 3 Bool.false)",
        ],
    );
    add(
        &mut spec,
        "init_test_memory",
        &format!(
            "def init_test_memory (bytes : Nat -> IROption Nat) : IRByteMemoryV1 := IRByteMemoryV1.mk {rows} bytes 128"
        ),
    );
    spec
}

fn world(memory: &str, host: &str, owner: &str, next: &str) -> String {
    format!(
        "(@IRByteWorldV1.mk Nat {memory} {host} (@IRList.cons Nat {owner} (@IRList.nil Nat)) {next})"
    )
}

fn current(frame: &str, world: &str) -> String {
    format!(
        "(@IRByteConfigV1.running Nat (IRMachine.mk (@IRList.cons IRFrame {frame} (@IRList.nil IRFrame)) (@IRList.nil IRMemSlot) 0) {world})"
    )
}

fn application() -> String {
    format!("ir_byte_init_current_v1 Nat init_test_context 41 init_test_args (init_test_memory bytes) host
      init_test_binding init_test_signature init_test_function
      (@Eq.refl (IRList IRGlobal) (@IRList.nil IRGlobal))
      (@Eq.refl (IROption IRByteFunctionV1) (@IROption.some IRByteFunctionV1 init_test_binding))
      (@Eq.refl (IROption IRByteSignatureV1) (@IROption.some IRByteSignatureV1 init_test_signature))
      (@Eq.refl (IROption IRFunc) (@IROption.some IRFunc init_test_function)) {TRUE} {TRUE}")
}

fn consumer(name: &str, expected: &str, proof: &str) -> String {
    format!(
        "def {name} (bytes : Nat -> IROption Nat) (host : Nat) :
      @Eq (IRByteConfigV1 Nat)
        (ir_byte_init_v1 Nat init_test_context 41 init_test_args (init_test_memory bytes) host)
        {expected} := {proof}"
    )
}

#[test]
fn byte_initialization_preserves_nonempty_history_bytes_host_and_positional_inputs() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let w = world("(init_test_memory bytes)", "host", "8", "9");
        add(
            &mut spec,
            "init_test_success",
            &consumer(
                "init_test_success",
                &current(INITIAL_FRAME, &w),
                &application(),
            ),
        );
        add(&mut spec, "init_test_valid", &format!("def init_test_valid
          (bytes : Nat -> IROption Nat) (host : Nat) :
          @Eq Bool (ir_byte_world_valid_v1 Nat
            (IRMachine.mk (@IRList.cons IRFrame {INITIAL_FRAME} (@IRList.nil IRFrame)) (@IRList.nil IRMemSlot) 0) {w}) Bool.true :=
          ir_byte_init_current_valid_v1 Nat (init_test_memory bytes) host {INITIAL_FRAME} {TRUE}"));
        for (id, address) in [(31, 16), (7, 48)] {
            let name = format!("init_test_parameter_{id}");
            add(&mut spec, &name, &format!("def {name} (bytes : Nat -> IROption Nat) (host : Nat) :
              @IRByteConfigV1.rec Nat (fun (_ : IRByteConfigV1 Nat) => Prop)
                (fun (machine : IRMachine) (_ : IRByteWorldV1 Nat) => @Eq IRScalar (ir_getd machine {id}) (IRScalar.ptr_ {address}))
                (fun (_ : IROutcome) (_ : IRByteWorldV1 Nat) => False)
                (ir_byte_init_v1 Nat init_test_context 41 init_test_args (init_test_memory bytes) host) :=
              @Eq.subst (IRByteConfigV1 Nat)
                (fun (config : IRByteConfigV1 Nat) => @IRByteConfigV1.rec Nat (fun (_ : IRByteConfigV1 Nat) => Prop)
                  (fun (machine : IRMachine) (_ : IRByteWorldV1 Nat) => @Eq IRScalar (ir_getd machine {id}) (IRScalar.ptr_ {address}))
                  (fun (_ : IROutcome) (_ : IRByteWorldV1 Nat) => False) config)
                {} (ir_byte_init_v1 Nat init_test_context 41 init_test_args (init_test_memory bytes) host)
                (@Eq.symm (IRByteConfigV1 Nat)
                  (ir_byte_init_v1 Nat init_test_context 41 init_test_args (init_test_memory bytes) host) {}
                  (init_test_success bytes host)) (@Eq.refl IRScalar (IRScalar.ptr_ {address}))",
                current(INITIAL_FRAME, &w), current(INITIAL_FRAME, &w)));
        }
    });
}

#[test]
fn byte_initialization_rejects_changed_bindings_history_and_entry_endpoint() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let w = world("(init_test_memory bytes)", "host", "8", "9");
        let positive = current(INITIAL_FRAME, &w);
        add(
            &mut spec,
            "init_test_success",
            &consumer("init_test_success", &positive, &application()),
        );
        let swapped = INITIAL_FRAME.replace("init_test_bindings", "(ir_bind_params (ir_func_params init_test_function) (@IRList.cons IRScalar (IRScalar.ptr_ 48) (@IRList.cons IRScalar (IRScalar.ptr_ 16) (@IRList.nil IRScalar))) (@IRList.nil IRBinding))");
        for (name, expected) in [
            ("init_wrong_arguments", current(&swapped, &w)),
            (
                "init_skipped_entry",
                current(&INITIAL_FRAME.replace("41 17 0", "41 17 1"), &w),
            ),
            (
                "init_wrong_function",
                current(&INITIAL_FRAME.replace("41 17 0", "42 17 0"), &w),
            ),
            (
                "init_reused_retired_owner",
                current(
                    INITIAL_FRAME,
                    &world("(init_test_memory bytes)", "host", "7", "9"),
                ),
            ),
            (
                "init_wrong_next_owner",
                current(
                    INITIAL_FRAME,
                    &world("(init_test_memory bytes)", "host", "8", "8"),
                ),
            ),
            (
                "init_changed_host",
                current(
                    INITIAL_FRAME,
                    &world("(init_test_memory bytes)", "(Nat.succ host)", "8", "9"),
                ),
            ),
            (
                "init_discarded_bytes",
                current(
                    INITIAL_FRAME,
                    &world(
                        "(init_test_memory (fun (_ : Nat) => @IROption.none Nat))",
                        "host",
                        "8",
                        "9",
                    ),
                ),
            ),
        ] {
            reject(
                &mut spec,
                name,
                &consumer(name, &expected, "init_test_success bytes host"),
            );
        }
        let wrong_lookup = application().replace(
            "init_test_binding init_test_signature",
            "(IRByteFunctionV1.mk 42 79 4096 0 Bool.false) init_test_signature",
        );
        reject(
            &mut spec,
            "init_wrong_catalog",
            &consumer("init_wrong_catalog", &positive, &wrong_lookup),
        );
    });
}

#[test]
fn byte_initialization_actual_entry_checks_fail_with_retained_world() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let globals = list("IRGlobal", &["(IRGlobal.mk 900 (IRConst.int_ 0))"]);
        for (name, imported, vararg, cc, gs, args, memory, fault) in [
            (
                "init_imported",
                true,
                false,
                0,
                "(@IRList.nil IRGlobal)",
                ARGS,
                "(init_test_memory bytes)",
                "bad_field",
            ),
            (
                "init_vararg",
                false,
                true,
                0,
                "(@IRList.nil IRGlobal)",
                ARGS,
                "(init_test_memory bytes)",
                "bad_field",
            ),
            (
                "init_unknown_cc",
                false,
                false,
                2,
                "(@IRList.nil IRGlobal)",
                ARGS,
                "(init_test_memory bytes)",
                "bad_field",
            ),
            (
                "init_has_globals",
                false,
                false,
                0,
                globals.as_str(),
                ARGS,
                "(init_test_memory bytes)",
                "bad_addr",
            ),
            (
                "init_wrong_arity",
                false,
                false,
                0,
                "(@IRList.nil IRGlobal)",
                "(@IRList.cons IRScalar (IRScalar.ptr_ 16) (@IRList.nil IRScalar))",
                "(init_test_memory bytes)",
                "bad_field",
            ),
            (
                "init_wrong_type",
                false,
                false,
                0,
                "(@IRList.nil IRGlobal)",
                "(@IRList.cons IRScalar (IRScalar.int_ 16) (@IRList.cons IRScalar (IRScalar.ptr_ 48) (@IRList.nil IRScalar)))",
                "(init_test_memory bytes)",
                "bad_field",
            ),
            (
                "init_live_foreign_owner",
                false,
                false,
                0,
                "(@IRList.nil IRGlobal)",
                ARGS,
                "(IRByteMemoryV1.mk (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 16 7 Bool.true) (@IRList.nil IRByteAllocationV1)) bytes 128)",
                "bad_addr",
            ),
        ] {
            let ctx = format!("{name}_ctx");
            add(
                &mut spec,
                &ctx,
                &context_source(&ctx, imported, vararg, cc, gs),
            );
            let w = world(memory, "host", "8", "9");
            let expected =
                format!("(@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.{fault}) {w})");
            add(&mut spec, name, &format!("def {name} (bytes : Nat -> IROption Nat) (host : Nat) :
              @Eq (IRByteConfigV1 Nat) (ir_byte_init_v1 Nat {ctx} 41 {args} {memory} host) {expected} :=
              @Eq.refl (IRByteConfigV1 Nat) {expected}"));
            let refused = format!("{name}_cannot_succeed");
            reject(
                &mut spec,
                &refused,
                &format!(
                    "def {refused} (bytes : Nat -> IROption Nat) (host : Nat) :
              @Eq (IRByteConfigV1 Nat) (ir_byte_init_v1 Nat {ctx} 41 {args} {memory} host) {} :=
              {name} bytes host",
                    current(INITIAL_FRAME, &w)
                ),
            );
        }
    });
}
