// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real kernel replay of range-local framing, not native execution evidence.

use super::*;
use clean_kernel::Name;

fn checked(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).expect("installed range law");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(name).unwrap();
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add_checked(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(source, "Actual range-framing consumer")
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    checked(spec, name);
}

fn reject(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Invalid range-framing claim")
        .expect_err(name);
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

#[test]
fn byte_range_laws_public_constructor_rechecks_every_root() {
    let spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
    for (name, _) in laws() {
        checked(&spec, name);
    }
}

#[test]
fn byte_range_disjoint_writes_preserve_undefined_and_invalid_bytes() {
    let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
    for (name, operation, args) in [
        ("range_write_touching", "write_word", "99"),
        ("range_clear_touching", "clear", ""),
    ] {
        let law = if operation == "clear" {
            "ir_byte_read_clear_disjoint_v1"
        } else {
            "ir_byte_read_write_disjoint_v1"
        };
        let source = format!(
            "def {name} (bytes : Nat -> IROption Nat) (base : Nat) :
          @Eq (IROption Nat)
            (ir_byte_read_word_v1 (ir_byte_{operation}_v1 bytes (Nat.add base 8) 8 {args}) 8 base)
            (ir_byte_read_word_v1 bytes 8 base) :=
          {law} bytes base 8 (Nat.add base 8) 8 {args}
            (@Or.inl (Nat.le (Nat.add base 8) (Nat.add base 8))
              (Nat.le (Nat.add (Nat.add base 8) 8) base) (Nat.le_refl (Nat.add base 8)))"
        );
        add_checked(&mut spec, name, &source);
    }
    add_checked(
        &mut spec,
        "range_write_before",
        r"def range_write_before
      (bytes : Nat -> IROption Nat) (base word : Nat) :
      @Eq (IROption Nat)
        (ir_byte_read_word_v1 (ir_byte_write_word_v1 bytes base 8 word) 8 (Nat.add base 8))
        (ir_byte_read_word_v1 bytes 8 (Nat.add base 8)) :=
      ir_byte_read_write_disjoint_v1 bytes (Nat.add base 8) 8 base 8 word
        (@Or.inr (Nat.le (Nat.add (Nat.add base 8) 8) base)
          (Nat.le (Nat.add base 8) (Nat.add base 8)) (Nat.le_refl (Nat.add base 8)))",
    );
    // The actual reader must preserve failure from an interior missing byte or
    // byte >=256, not merely agree on all-successful concrete arrays.
    for (name, interior) in [
        ("range_none_interior", "@IROption.none Nat"),
        ("range_invalid_interior", "@IROption.some Nat 256"),
    ] {
        let bytes = format!(
            "(fun (address : Nat) => @Bool.rec (fun (_ : Bool) => IROption Nat)
          (@IROption.some Nat 1) ({interior}) (ir_nat_eqb address 3))"
        );
        add_checked(
            &mut spec,
            name,
            &format!(
                "def {name} : @Eq (IROption Nat)
          (ir_byte_read_word_v1 (ir_byte_write_word_v1 {bytes} 8 8 99) 8 0) (@IROption.none Nat) :=
          @Eq.trans (IROption Nat)
            (ir_byte_read_word_v1 (ir_byte_write_word_v1 {bytes} 8 8 99) 8 0)
            (ir_byte_read_word_v1 {bytes} 8 0) (@IROption.none Nat)
            (range_write_touching {bytes} 0) (@Eq.refl (IROption Nat) (@IROption.none Nat))"
            ),
        );
    }
    add_checked(
        &mut spec,
        "range_zero_width",
        r"def range_zero_width (left right : Nat -> IROption Nat) (base : Nat) :
      @Eq (IROption Nat) (ir_byte_read_word_v1 left 0 base) (ir_byte_read_word_v1 right 0 base) :=
      ir_byte_read_range_congr_v1 left right 0 base
        (fun (offset : Nat) (bad : Nat.lt offset 0) =>
          @False.elim (@Eq (IROption Nat) (left (Nat.add base offset)) (right (Nat.add base offset)))
            (Nat.not_succ_le_zero offset bad))",
    );
}

#[test]
fn byte_range_rejects_overlap_changed_values_and_missing_bytes() {
    let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
    let bytes = "(fun (_ : Nat) => @IROption.some Nat 0)";
    reject(
        &mut spec,
        "range_overlap",
        &format!(
            "def range_overlap :
      @Eq (IROption Nat) (ir_byte_read_word_v1 (ir_byte_write_word_v1 {bytes} 7 8 1) 8 0)
        (ir_byte_read_word_v1 {bytes} 8 0) :=
      ir_byte_read_write_disjoint_v1 {bytes} 0 8 7 8 1
        (@Or.inl (Nat.le 8 7) (Nat.le 15 0) (Nat.le_refl 8))"
        ),
    );
    reject(
        &mut spec,
        "range_changed_read",
        &format!(
            "def range_changed_read :
      @Eq (IROption Nat) (ir_byte_read_word_v1 (ir_byte_write_word_v1 {bytes} 8 8 1) 8 0)
        (@IROption.some Nat 1) :=
      ir_byte_read_write_disjoint_v1 {bytes} 0 8 8 8 1
        (@Or.inl (Nat.le 8 8) (Nat.le 16 0) (Nat.le_refl 8))"
        ),
    );
    reject(
        &mut spec,
        "range_missing_is_not_zero",
        r"def range_missing_is_not_zero :
      @Eq (IROption Nat) (ir_byte_read_word_v1 (fun (_ : Nat) => @IROption.none Nat) 8 0)
        (@IROption.some Nat 0) := @Eq.refl (IROption Nat) (@IROption.some Nat 0)",
    );
}

fn layout(ty: &str) -> String {
    format!("(IRByteLayoutV1.mk ({ty}) 8 8 (@IRList.nil IRTy) (@IRList.nil Nat))")
}

/// Independent endpoints: four public operations, with both observations of
/// the exact same final memory. The code address is not a native address claim.
fn capture_claim(
    ctx: &str,
    mem: &str,
    base: &str,
    fid: &str,
    sig: &str,
    code: &str,
    capture: &str,
) -> String {
    let second_address = format!("(Nat.add {base} 8)");
    let first = written(mem, base, code);
    let final_mem = written(&first, &second_address, capture);
    let mut claims = Vec::new();
    for (ty, address, value, before, after) in [
        (
            format!("IRTy.func_ {sig}"),
            base.to_owned(),
            format!("IRScalar.fnptr_ {fid}"),
            mem.to_owned(),
            first.clone(),
        ),
        (
            "IRTy.ptr_".to_owned(),
            second_address.clone(),
            format!("IRScalar.ptr_ {capture}"),
            first,
            final_mem.clone(),
        ),
    ] {
        claims.push(equality("IRByteMemoryResultV1",
            &format!("ir_byte_store_v1 {ctx} ({ty}) (IRScalar.ptr_ {address}) ({value}) 0 Bool.false {before}"),
            &format!("IRByteMemoryResultV1.value IRScalar.unit_ {after}")));
    }
    for (ty, address, value) in [
        (
            format!("IRTy.func_ {sig}"),
            base.to_owned(),
            format!("IRScalar.fnptr_ {fid}"),
        ),
        (
            "IRTy.ptr_".to_owned(),
            second_address,
            format!("IRScalar.ptr_ {capture}"),
        ),
    ] {
        claims.push(equality(
            "IRByteMemoryResultV1",
            &format!(
                "ir_byte_load_v1 {ctx} ({ty}) (IRScalar.ptr_ {address}) 0 Bool.false {final_mem}"
            ),
            &format!("IRByteMemoryResultV1.value ({value}) {final_mem}"),
        ));
    }
    format!(
        "And {} (And {} (And {} {}))",
        claims[0], claims[1], claims[2], claims[3]
    )
}

#[test]
fn byte_range_typed_callback_and_capture_share_final_memory() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
        let fl = layout("IRTy.func_ sig");
        let pl = layout("IRTy.ptr_");
        let binding = "(IRByteFunctionV1.mk fid sig codeAddress cc imported)";
        let claim = capture_claim(
            "ctx",
            "mem",
            "base",
            "fid",
            "sig",
            "codeAddress",
            "(Nat.succ predecessor)",
        );
        add_checked(&mut spec, "range_capture_generic", &format!(
            "def range_capture_generic (ctx : IRByteContextV1) (mem : IRByteMemoryV1)
          (base fid sig codeAddress predecessor cc : Nat) (imported : Bool)
          (baseBound : Nat.lt base ir_byte_limit_v1)
          (secondBound : Nat.lt (Nat.add base 8) ir_byte_limit_v1)
          (forward : @Eq (IROption IRByteFunctionV1) (ir_byte_function_v1 ctx fid) (@IROption.some IRByteFunctionV1 {binding}))
          (reverse : @Eq (IROption IRByteFunctionV1) (ir_byte_function_address_v1 ctx codeAddress) (@IROption.some IRByteFunctionV1 {binding}))
          (positive : Nat.lt 0 codeAddress) (codeBound : Nat.lt codeAddress ir_byte_limit_v1)
          (captureBound : Nat.lt (Nat.succ predecessor) ir_byte_limit_v1)
          (functionLayout : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx (IRTy.func_ sig)) (@IROption.some IRByteLayoutV1 {fl}))
          (pointerLayout : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx IRTy.ptr_) (@IROption.some IRByteLayoutV1 {pl}))
          (firstAccess : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) base 8
            (ir_byte_effective_align_v1 0 (ir_byte_layout_align_v1 {fl}))) Bool.true)
          (secondAccess : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) (Nat.add base 8) 8
            (ir_byte_effective_align_v1 0 (ir_byte_layout_align_v1 {pl}))) Bool.true) :
          {claim} :=
          ir_byte_store_pair_eight_v1 ctx (IRTy.func_ sig) IRTy.ptr_
            (IRScalar.ptr_ base) (IRScalar.ptr_ (Nat.add base 8))
            (IRScalar.fnptr_ fid) (IRScalar.ptr_ (Nat.succ predecessor)) 0 0 mem
            {fl} {pl} base (Nat.add base 8) codeAddress (Nat.succ predecessor)
            (ir_byte_function_lane_eight_v1 sig) functionLayout (ir_byte_canonical_layout_eight_v1 (IRTy.func_ sig))
            (ir_byte_pointer_address_bounded_v1 base baseBound) firstAccess
            (ir_byte_function_value_matches_of_catalog_v1 ctx fid sig codeAddress cc imported forward positive codeBound)
            (ir_byte_function_scalar_word_of_catalog_v1 ctx fid sig codeAddress cc imported forward reverse positive codeBound)
            (ir_byte_function_decode_word_of_catalog_v1 ctx fid sig codeAddress cc imported forward reverse positive codeBound) codeBound
            ir_byte_ptr_lane_eight_v1 pointerLayout (ir_byte_canonical_layout_eight_v1 IRTy.ptr_)
            (ir_byte_pointer_address_bounded_v1 (Nat.add base 8) secondBound) secondAccess
            (ir_byte_pointer_value_fits_v1 ctx predecessor captureBound)
            (ir_byte_pointer_scalar_word_v1 ctx predecessor captureBound)
            (ir_byte_pointer_decode_word_v1 ctx predecessor) captureBound
            (@Or.inl (Nat.le (Nat.add base 8) (Nat.add base 8))
              (Nat.le (Nat.add (Nat.add base 8) 8) base) (Nat.le_refl (Nat.add base 8)))"));

        // Inhabited exact catalog/access premises with arbitrary initial bytes.
        // The empty IRModule is only a memory-catalog fixture, not a callable.
        let layouts = format!(
            "(@IRList.cons IRByteLayoutV1 {} (@IRList.cons IRByteLayoutV1 {} (@IRList.cons IRByteLayoutV1 {} (@IRList.nil IRByteLayoutV1))))",
            layout("IRTy.func_ 17"),
            layout("IRTy.ptr_"),
            layout("IRTy.func_ 18")
        );
        add_checked(&mut spec, "range_capture_ctx", &format!(
            "def range_capture_ctx : IRByteContextV1 := IRByteContextV1.mk
          (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal)) {layouts}
          (@IRList.nil IRByteSignatureV1)
          (@IRList.cons IRByteFunctionV1 (IRByteFunctionV1.mk 41 17 4096 1 Bool.false) (@IRList.nil IRByteFunctionV1))
          (@IRList.nil IRByteSiteV1)"));
        let mem = "(IRByteMemoryV1.mk (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 16 7 Bool.true) (@IRList.nil IRByteAllocationV1)) bytes 33)";
        let claim = capture_claim("range_capture_ctx", mem, "16", "41", "17", "4096", "80");
        let proof = format!("range_capture_generic range_capture_ctx {mem} 16 41 17 4096 79 1 Bool.false
          (Nat.le_add_right 17 18446744073709551599) (Nat.le_add_right 25 18446744073709551591)
          (@Eq.refl (IROption IRByteFunctionV1) (@IROption.some IRByteFunctionV1 (IRByteFunctionV1.mk 41 17 4096 1 Bool.false)))
          (@Eq.refl (IROption IRByteFunctionV1) (@IROption.some IRByteFunctionV1 (IRByteFunctionV1.mk 41 17 4096 1 Bool.false)))
          (Nat.zero_lt_succ 4095) (Nat.le_add_right 4097 18446744073709547519)
          (Nat.le_add_right 81 18446744073709551535)
          (@Eq.refl (IROption IRByteLayoutV1) (@IROption.some IRByteLayoutV1 {}))
          (@Eq.refl (IROption IRByteLayoutV1) (@IROption.some IRByteLayoutV1 {}))
          (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)", layout("IRTy.func_ 17"), layout("IRTy.ptr_"));
        add_checked(
            &mut spec,
            "range_capture_inhabited",
            &format!(
                "def range_capture_inhabited (bytes : Nat -> IROption Nat) : {claim} := {proof}"
            ),
        );

        let first = written(mem, "16", "4096");
        let final_mem = written(&first, "(Nat.add 16 8)", "80");
        let wrong_load = format!(
            "ir_byte_load_v1 range_capture_ctx (IRTy.func_ 18) (IRScalar.ptr_ 16) 0 Bool.false {final_mem}"
        );
        let fault =
            format!("IRByteMemoryResultV1.fault (IROutcome.ub IRFault.width_bounded) {final_mem}");
        add_checked(
            &mut spec,
            "range_capture_wrong_signature_fault",
            &format!(
                "def range_capture_wrong_signature_fault (bytes : Nat -> IROption Nat) : {} :=
              @Eq.refl IRByteMemoryResultV1 ({fault})",
                equality("IRByteMemoryResultV1", &wrong_load, &fault)
            ),
        );
        reject(
            &mut spec,
            "range_capture_wrong_signature_success",
            &format!(
                "def range_capture_wrong_signature_success (bytes : Nat -> IROption Nat) : {} :=
              @Eq.refl IRByteMemoryResultV1 ({fault})",
                equality(
                    "IRByteMemoryResultV1",
                    &wrong_load,
                    &format!("IRByteMemoryResultV1.value (IRScalar.fnptr_ 41) {final_mem}")
                )
            ),
        );
        // Changing either expected value or the observed memory must not admit
        // the same pair proof. This prevents proving each field only before the
        // second store, the exact composition error this law is intended to fix.
        for (name, corrupted) in [
            (
                "range_capture_wrong_callback",
                claim.replacen(
                    "IRByteMemoryResultV1.value (IRScalar.fnptr_ 41)",
                    "IRByteMemoryResultV1.value (IRScalar.fnptr_ 7)",
                    1,
                ),
            ),
            (
                "range_capture_wrong_capture",
                claim.replacen(
                    "IRByteMemoryResultV1.value (IRScalar.ptr_ 80)",
                    "IRByteMemoryResultV1.value (IRScalar.ptr_ 88)",
                    1,
                ),
            ),
            (
                "range_capture_stale_memory",
                claim.replacen(
                    &format!("(IRScalar.ptr_ 16) 0 Bool.false {final_mem}"),
                    &format!("(IRScalar.ptr_ 16) 0 Bool.false {mem}"),
                    1,
                ),
            ),
        ] {
            assert_ne!(corrupted, claim, "mutation must change actual endpoint");
            reject(
                &mut spec,
                name,
                &format!("def {name} (bytes : Nat -> IROption Nat) : {corrupted} := {proof}"),
            );
        }
    });
}
