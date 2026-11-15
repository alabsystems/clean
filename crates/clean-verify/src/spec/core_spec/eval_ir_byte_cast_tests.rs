// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact opaque-pointer Bitcast controls. These are checked model terms, not
//! compiler/source authority, allocation validity or concurrent-memory proofs.

use crate::spec::Specification;
use clean_kernel::Name;

fn specification() -> Specification {
    crate::eval_ir::build_byte_prelude_spec_v1_with_stack().expect("public ByteV1 vocabulary")
}

fn add(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Opaque pointer Bitcast regression")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
    let name = source.split_whitespace().nth(1).unwrap();
    spec.verify_definition(name).expect("kernel-checked value");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn equality(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
    add(
        spec,
        &format!(
            "def {name} (ctx : IRByteContextV1) : Eq ({ty}) ({actual}) ({expected}) := Eq.refl ({ty}) ({expected})"
        ),
    );
}

fn refuse_claim(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Deliberately false Bitcast claim")
        .expect_err("wrong value must be rejected");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

#[test]
fn byte_bitcast_ptr_identity_is_general_checked_and_inhabited() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let root = "ir_byte_bitcast_ptr_identity_v1";
        let definition = spec
            .get_definition(root)
            .expect("registered identity theorem");
        assert!(!definition.is_axiom && definition.elaborated_value.is_some());
        spec.verify_definition(root).unwrap();
        let name = Name::from_string(root);
        assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
        assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
        for (index, value) in [
            "IRScalar.nullptr_",
            "IRScalar.ptr_ 1",
            "IRScalar.ptr_ 16",
            "IRScalar.ptr_ 18446744073709551615",
        ]
        .into_iter()
        .enumerate()
        {
            add(
                &mut spec,
                &format!(
                    "def byte_bitcast_ptr_by_law_{index} (ctx : IRByteContextV1) :
  Eq IRStepResult (ir_byte_cast_eval_v1 ctx IRCastOp.bitcast IRTy.ptr_ IRTy.ptr_ ({value}))
    (IRStepResult.value ({value})) :=
  ir_byte_bitcast_ptr_identity_v1 ctx ({value}) (Eq.refl Bool Bool.true)"
                ),
            );
        }
        refuse_claim(
            &mut spec,
            "byte_bitcast_ptr_changed_value",
            "def byte_bitcast_ptr_changed_value (ctx : IRByteContextV1) :
  Eq IRStepResult (ir_byte_cast_eval_v1 ctx IRCastOp.bitcast IRTy.ptr_ IRTy.ptr_ (IRScalar.ptr_ 16))
    (IRStepResult.value (IRScalar.ptr_ 17)) :=
  ir_byte_bitcast_ptr_identity_v1 ctx (IRScalar.ptr_ 16) (Eq.refl Bool Bool.true)",
        );
    });
}

#[test]
fn byte_bitcast_ptr_refuses_mixed_types_and_retains_integer_and_legacy_meanings() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (index, (src, dst)) in [
            ("IRTy.ptr_", "IRTy.uint_ 64"),
            ("IRTy.uint_ 64", "IRTy.ptr_"),
            ("IRTy.ptr_", "IRTy.float_ 64"),
            ("IRTy.float_ 64", "IRTy.ptr_"),
            ("IRTy.fatptr_ (IRTy.uint_ 8)", "IRTy.ptr_"),
            ("IRTy.ptr_", "IRTy.fatptr_ (IRTy.uint_ 8)"),
            ("IRTy.ref_ (IRTy.uint_ 8)", "IRTy.ptr_"),
            ("IRTy.ptr_", "IRTy.rawmut_ (IRTy.uint_ 8)"),
            ("IRTy.rc_ (IRTy.uint_ 8)", "IRTy.rc_ (IRTy.uint_ 8)"),
            ("IRTy.func_ 0", "IRTy.func_ 0"),
            ("IRTy.bool_", "IRTy.bool_"),
            ("IRTy.uint_ 8", "IRTy.uint_ 16"),
            ("IRTy.float_ 64", "IRTy.uint_ 64"),
        ]
        .into_iter()
        .enumerate()
        {
            // Every carrier, including a well-formed pointer, must fail this
            // unsupported type pair before the operand's representation check.
            add(&mut spec, &format!("def byte_bitcast_ptr_unsupported_{index} (ctx : IRByteContextV1) (value : IRScalar) :
  Eq IRStepResult (ir_byte_cast_eval_v1 ctx IRCastOp.bitcast ({src}) ({dst}) value)
    ir_width_fault := Eq.refl IRStepResult ir_width_fault"));
        }
        equality(
            &mut spec,
            "byte_bitcast_ptr_integer_unchanged",
            "IRStepResult",
            "ir_byte_cast_eval_v1 ctx IRCastOp.bitcast (IRTy.int_ 8) (IRTy.uint_ 8) (IRScalar.int_ 255)",
            "IRStepResult.value (IRScalar.int_ 255)",
        );
        equality(
            &mut spec,
            "byte_bitcast_ptr_legacy_refusal",
            "IRStepResult",
            "ir_cast_eval IRCastOp.bitcast IRTy.ptr_ IRTy.ptr_ (IRScalar.ptr_ 16)",
            "ir_width_fault",
        );
    });
}

#[test]
fn byte_bitcast_ptr_rejects_noncanonical_and_wrong_carriers() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (index, value) in [
            "IRScalar.ptr_ 0",
            "IRScalar.ptr_ 18446744073709551616",
            "IRScalar.int_ 16",
            "IRScalar.bool_ Bool.true",
            "IRScalar.undef_",
            "IRScalar.fat_ 16 1",
            "IRScalar.fnptr_ 0",
        ]
        .into_iter()
        .enumerate()
        {
            equality(
                &mut spec,
                &format!("byte_bitcast_ptr_bad_{index}"),
                "IRStepResult",
                &format!("ir_byte_cast_eval_v1 ctx IRCastOp.bitcast IRTy.ptr_ IRTy.ptr_ ({value})"),
                "IRStepResult.fault (IROutcome.type_error IRFault.bad_field)",
            );
        }
        refuse_claim(
            &mut spec,
            "byte_bitcast_ptr_zero_representation",
            "def byte_bitcast_ptr_zero_representation (ctx : IRByteContextV1) :
  Eq IRStepResult (ir_byte_cast_eval_v1 ctx IRCastOp.bitcast IRTy.ptr_ IRTy.ptr_ (IRScalar.ptr_ 0))
    (IRStepResult.value (IRScalar.ptr_ 0)) :=
  ir_byte_bitcast_ptr_identity_v1 ctx (IRScalar.ptr_ 0) (Eq.refl Bool Bool.true)",
        );
    });
}

const EMPTY_NAT: &str = "(IRList.nil Nat)";
const RESULTS: &str = "(IRList.cons Nat 99 (IRList.nil Nat))";
const WORLD: &str = "(IRByteWorldV1.mk Nat (ir_byte_memory_empty_v1 128) host
  (IRList.cons Nat 2 (IRList.cons Nat 1 (IRList.nil Nat))) 3)";
const FRAME: &str = "(IRFrame.mk 9 7 1
  (IRList.cons IRBinding (IRBinding.mk 40 (IRScalar.ptr_ 16))
    (IRList.cons IRBinding (IRBinding.mk 88 (IRScalar.int_ 55)) (IRList.nil IRBinding)))
  (IRList.cons Nat 123 (IRList.nil Nat)))";
const TAIL: &str = "(IRList.cons IRFrame (IRFrame.mk 3 4 5 (IRList.nil IRBinding)
  (IRList.cons Nat 55 (IRList.nil Nat))) (IRList.nil IRFrame))";

fn machine(frame: &str) -> String {
    format!("(IRMachine.mk (IRList.cons IRFrame {frame} {TAIL}) (IRList.nil IRMemSlot) 77)")
}
fn context(result_ty: &str) -> String {
    format!(
        "(IRByteContextV1.mk
 (IRModule.mk
  (IRList.cons IRFunc (IRFunc.mk 9 (IRList.cons Nat 40 {EMPTY_NAT}) 7
   (IRList.cons IRBlock (IRBlock.mk 7 {EMPTY_NAT}
    (IRList.cons IRNode (IRNode.mk IRInst.unreachable {EMPTY_NAT})
     (IRList.cons IRNode (IRNode.mk (IRInst.cast IRCastOp.bitcast IRTy.ptr_ IRTy.ptr_ 40) {RESULTS})
      (IRList.nil IRNode)))) (IRList.nil IRBlock))) (IRList.nil IRFunc)) (IRList.nil IRGlobal))
 (IRList.nil IRByteLayoutV1) (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1)
 (IRList.cons IRByteSiteV1 (IRByteSiteV1.mk 9 7 1 0 1
  (IRList.cons IRTy ({result_ty}) (IRList.nil IRTy))) (IRList.nil IRByteSiteV1)))"
    )
}

#[test]
fn byte_bitcast_ptr_actual_fetched_step_binds_once_and_preserves_world_without_access() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let params = "(providers : IRByteProvidersV1 Nat) (host : Nat)";
        let run = |result_ty: &str| {
            format!(
                "ir_byte_step_v1 Nat {} providers
  (IRByteConfigV1.running Nat {} {WORLD})",
                context(result_ty),
                machine(FRAME)
            )
        };
        let frame = format!(
            "(ir_frame_advance (ir_frame_set_many {FRAME} {RESULTS}
  (IRList.cons IRScalar (IRScalar.ptr_ 16) (IRList.nil IRScalar))))"
        );
        let expected = format!("IRByteConfigV1.running Nat {} {WORLD}", machine(&frame));
        add(
            &mut spec,
            &format!(
                "def byte_bitcast_ptr_fetched {params} :
  Eq (IRByteConfigV1 Nat) ({}) ({expected}) := Eq.refl (IRByteConfigV1 Nat) ({expected})",
                run("IRTy.ptr_")
            ),
        );
        // The complete unchanged world includes empty memory: transporting the
        // pointer grants no allocation/access right. A bad result lane faults
        // at this fetched instruction without changing any bytes or host state.
        let failed =
            format!("IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) {WORLD}");
        add(
            &mut spec,
            &format!(
                "def byte_bitcast_ptr_bad_site {params} :
  Eq (IRByteConfigV1 Nat) ({}) ({failed}) := Eq.refl (IRByteConfigV1 Nat) ({failed})",
                run("IRTy.uint_ 64")
            ),
        );
        refuse_claim(
            &mut spec,
            "byte_bitcast_ptr_changed_world",
            &format!(
                "def byte_bitcast_ptr_changed_world {params} :
  Eq (IRByteConfigV1 Nat) ({}) ({}) := byte_bitcast_ptr_fetched providers host",
                run("IRTy.ptr_"),
                expected.replace("host", "(Nat.succ host)")
            ),
        );
        let load_context = "(IRByteContextV1.mk
  (IRModule.mk (IRList.nil IRFunc) (IRList.nil IRGlobal))
  (IRList.cons IRByteLayoutV1
    (IRByteLayoutV1.mk (IRTy.uint_ 64) 8 8 (IRList.nil IRTy) (IRList.nil Nat))
    (IRList.nil IRByteLayoutV1))
  (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1) (IRList.nil IRByteSiteV1))";
        equality(
            &mut spec,
            "byte_bitcast_ptr_no_dereference_right",
            "IRByteMemoryResultV1",
            &format!(
                "ir_byte_load_v1 {load_context} (IRTy.uint_ 64) (IRScalar.ptr_ 16) 8 Bool.false (ir_byte_memory_empty_v1 128)"
            ),
            "IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr) (ir_byte_memory_empty_v1 128)",
        );
        equality(
            &mut spec,
            "byte_bitcast_ptr_empty_allocation_inaccessible",
            "Bool",
            "ir_byte_accessible_v1 (IRList.nil IRByteAllocationV1) 16 8 8",
            "Bool.false",
        );
    });
}
