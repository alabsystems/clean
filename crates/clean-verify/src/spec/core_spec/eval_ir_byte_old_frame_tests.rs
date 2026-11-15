// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel replay of actual memory operations, not a native-address or
//! source-reachability claim. Catalog fixtures are not callable modules.

use super::*;
use clean_kernel::Name;

fn checked(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).expect("installed old-frame law");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(name).unwrap();
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add_checked(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(source, "Actual old-frame allocation consumer")
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    checked(spec, name);
}

fn reject(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Malformed old-frame claim")
        .expect_err(name);
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn observe_bool(spec: &mut Specification, name: &str, decision: &str, value: bool) {
    let value = if value { "Bool.true" } else { "Bool.false" };
    add_checked(
        spec,
        name,
        &format!("def {name} : Eq Bool ({decision}) {value} := Eq.refl Bool {value}"),
    );
}

fn layout(ty: &str) -> String {
    format!("(IRByteLayoutV1.mk ({ty}) 8 8 (IRList.nil IRTy) (IRList.nil Nat))")
}

fn frame_layout() -> &'static str {
    "(IRByteLayoutV1.mk (IRTy.array_ (IRTy.uint_ 8) 16) 16 1 (IRList.nil IRTy) (IRList.nil Nat))"
}

/// Caller is deliberately below both a retired and a global allocation.
fn history() -> &'static str {
    "(IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 48 8 3 Bool.false)
      (IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 8 4 0 Bool.true)
        (IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 16 1 Bool.true)
          (IRList.nil IRByteAllocationV1))))"
}

fn high_water() -> &'static str {
    "(@And.intro (Nat.lt 56 65) (And (Nat.lt 12 65) (And (Nat.lt 32 65) True))
      (Nat.le_add_right 57 8)
      (@And.intro (Nat.lt 12 65) (And (Nat.lt 32 65) True) (Nat.le_add_right 13 52)
        (@And.intro (Nat.lt 32 65) True (Nat.le_add_right 33 32) True.intro)))"
}

// Independent expected operation endpoints: both stores, real typed allocation,
// and both loads of exactly the final allocated memory. We do not obtain the
// expected claim by looking up or reusing a law's generated declaration text.
fn capture_claim(
    ctx: &str,
    allocs: &str,
    bytes: &str,
    cursor: &str,
    owner: &str,
    base: &str,
    fid: &str,
    sig: &str,
    code: &str,
    capture: &str,
) -> (String, String, String) {
    let second = format!("(Nat.add {base} 8)");
    let mem = format!("(IRByteMemoryV1.mk {allocs} {bytes} {cursor})");
    let first_bytes = format!("(ir_byte_write_word_v1 {bytes} {base} 8 {code})");
    let init_bytes = format!("(ir_byte_write_word_v1 {first_bytes} {second} 8 {capture})");
    let first = format!("(IRByteMemoryV1.mk {allocs} {first_bytes} {cursor})");
    let init = format!("(IRByteMemoryV1.mk {allocs} {init_bytes} {cursor})");
    let fresh_base = format!("(ir_byte_aligned_base_v1 {cursor} 8)");
    let fresh = format!("(IRByteMemoryV1.mk
      (IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk {fresh_base} 16 {owner} Bool.true) {allocs})
      (ir_byte_clear_v1 {init_bytes} {fresh_base} 16) (Nat.succ (Nat.add {fresh_base} 16)))");
    let mut claims = Vec::new();
    for (ty, address, value, before, after) in [
        (
            format!("IRTy.func_ {sig}"),
            base.to_owned(),
            format!("IRScalar.fnptr_ {fid}"),
            mem,
            first.clone(),
        ),
        (
            "IRTy.ptr_".into(),
            second.clone(),
            format!("IRScalar.ptr_ {capture}"),
            first,
            init.clone(),
        ),
    ] {
        claims.push(format!(
            "(Eq IRByteMemoryResultV1
          (ir_byte_store_v1 {ctx} ({ty}) (IRScalar.ptr_ {address}) ({value}) 0 Bool.false {before})
          (IRByteMemoryResultV1.value IRScalar.unit_ {after}))"
        ));
    }
    claims.push(format!(
        "(Eq IRByteMemoryResultV1
      (ir_byte_alloc_v1 {ctx} (IRTy.array_ (IRTy.uint_ 8) 16) 1 8 {owner} {init})
      (IRByteMemoryResultV1.value (IRScalar.ptr_ {fresh_base}) {fresh}))"
    ));
    for (ty, address, value) in [
        (
            format!("IRTy.func_ {sig}"),
            base.to_owned(),
            format!("IRScalar.fnptr_ {fid}"),
        ),
        (
            "IRTy.ptr_".into(),
            second,
            format!("IRScalar.ptr_ {capture}"),
        ),
    ] {
        claims.push(format!(
            "(Eq IRByteMemoryResultV1
          (ir_byte_load_v1 {ctx} ({ty}) (IRScalar.ptr_ {address}) 0 Bool.false {fresh})
          (IRByteMemoryResultV1.value ({value}) {fresh}))"
        ));
    }
    (
        format!(
            "And {} (And {} (And {} (And {} {})))",
            claims[0], claims[1], claims[2], claims[3], claims[4]
        ),
        init,
        fresh,
    )
}

#[test]
fn byte_old_frame_public_constructor_rechecks_every_root() {
    let spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
    for (name, _) in laws() {
        checked(&spec, name);
    }
}

#[test]
fn byte_old_frame_real_stores_allocate_and_reload_both_values() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
        let fl = layout("IRTy.func_ sig");
        let pl = layout("IRTy.ptr_");
        let binding = "(IRByteFunctionV1.mk fid sig codeAddress cc imported)";
        let (claim, _, _) = capture_claim(
            "ctx",
            "allocs",
            "bytes",
            "cursor",
            "owner",
            "base",
            "fid",
            "sig",
            "codeAddress",
            "(Nat.succ predecessor)",
        );
        add_checked(&mut spec, "old_frame_capture_generic", &format!(
            "def old_frame_capture_generic (ctx : IRByteContextV1)
          (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
          (cursor owner base fid sig codeAddress predecessor cc : Nat) (imported : Bool)
          (cursorPositive : Nat.lt 0 cursor)
          (room : Nat.lt (Nat.add (ir_byte_aligned_base_v1 cursor 8) 16) ir_byte_limit_v1)
          (highWater : ir_byte_high_water_v1 allocs cursor)
          (frameLayout : Eq (IROption IRByteLayoutV1)
            (ir_byte_layout_v1 ctx (IRTy.array_ (IRTy.uint_ 8) 16)) (IROption.some IRByteLayoutV1 {}))
          (baseBound : Nat.lt base ir_byte_limit_v1)
          (secondBound : Nat.lt (Nat.add base 8) ir_byte_limit_v1)
          (forward : Eq (IROption IRByteFunctionV1) (ir_byte_function_v1 ctx fid) (IROption.some IRByteFunctionV1 {binding}))
          (reverse : Eq (IROption IRByteFunctionV1) (ir_byte_function_address_v1 ctx codeAddress) (IROption.some IRByteFunctionV1 {binding}))
          (positive : Nat.lt 0 codeAddress) (codeBound : Nat.lt codeAddress ir_byte_limit_v1)
          (captureBound : Nat.lt (Nat.succ predecessor) ir_byte_limit_v1)
          (functionLayout : Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx (IRTy.func_ sig)) (IROption.some IRByteLayoutV1 {fl}))
          (pointerLayout : Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx IRTy.ptr_) (IROption.some IRByteLayoutV1 {pl}))
          (firstAccess : Eq Bool (ir_byte_accessible_v1 allocs base 8 8) Bool.true)
          (secondAccess : Eq Bool (ir_byte_accessible_v1 allocs (Nat.add base 8) 8 8) Bool.true) :
          {claim} := ir_byte_store_pair_fresh_frame16_v1 ctx (IRTy.func_ sig) IRTy.ptr_
            (IRScalar.ptr_ base) (IRScalar.ptr_ (Nat.add base 8))
            (IRScalar.fnptr_ fid) (IRScalar.ptr_ (Nat.succ predecessor)) 0 0 allocs bytes cursor owner
            {fl} {pl} base (Nat.add base 8) codeAddress (Nat.succ predecessor)
            cursorPositive room highWater frameLayout
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
              (Nat.le (Nat.add (Nat.add base 8) 8) base) (Nat.le_refl (Nat.add base 8)))", frame_layout()));

        let layouts = format!("(IRList.cons IRByteLayoutV1 {} (IRList.cons IRByteLayoutV1 {} (IRList.cons IRByteLayoutV1 {} (IRList.cons IRByteLayoutV1 {} (IRList.nil IRByteLayoutV1)))))",
            layout("IRTy.func_ 17"), layout("IRTy.ptr_"), frame_layout(), layout("IRTy.func_ 18"));
        add_checked(&mut spec, "old_frame_capture_ctx", &format!(
            "def old_frame_capture_ctx : IRByteContextV1 := IRByteContextV1.mk
          (IRModule.mk (IRList.nil IRFunc) (IRList.nil IRGlobal)) {layouts}
          (IRList.nil IRByteSignatureV1)
          (IRList.cons IRByteFunctionV1 (IRByteFunctionV1.mk 41 17 4096 1 Bool.false) (IRList.nil IRByteFunctionV1))
          (IRList.nil IRByteSiteV1)"));
        let (claim, initialized, fresh) = capture_claim(
            "old_frame_capture_ctx",
            history(),
            "bytes",
            "65",
            "2",
            "16",
            "41",
            "17",
            "4096",
            "16",
        );
        // The captured pointer names the old live caller's allocation, not a
        // future fresh address; neither this fixture nor the law dereferences it.
        let proof = format!("old_frame_capture_generic old_frame_capture_ctx {} bytes 65 2 16 41 17 4096 15 1 Bool.false
          (Nat.zero_lt_succ 64) (Nat.le_add_right 89 18446744073709551527) {} 
          (Eq.refl (IROption IRByteLayoutV1) (IROption.some IRByteLayoutV1 {}))
          (Nat.le_add_right 17 18446744073709551599) (Nat.le_add_right 25 18446744073709551591)
          (Eq.refl (IROption IRByteFunctionV1) (IROption.some IRByteFunctionV1 (IRByteFunctionV1.mk 41 17 4096 1 Bool.false)))
          (Eq.refl (IROption IRByteFunctionV1) (IROption.some IRByteFunctionV1 (IRByteFunctionV1.mk 41 17 4096 1 Bool.false)))
          (Nat.zero_lt_succ 4095) (Nat.le_add_right 4097 18446744073709547519)
          (Nat.le_add_right 17 18446744073709551599)
          (Eq.refl (IROption IRByteLayoutV1) (IROption.some IRByteLayoutV1 {}))
          (Eq.refl (IROption IRByteLayoutV1) (IROption.some IRByteLayoutV1 {}))
          (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)", history(), high_water(), frame_layout(), layout("IRTy.func_ 17"), layout("IRTy.ptr_"));
        add_checked(
            &mut spec,
            "old_frame_capture_inhabited",
            &format!(
            "def old_frame_capture_inhabited (bytes : Nat -> IROption Nat) : {claim} := {proof}"),
        );

        // The fresh extent really is cleared, independent of arbitrary input
        // bytes. Returning the initialized-but-not-allocated memory is wrong.
        add_checked(
            &mut spec,
            "old_frame_fresh_extent_cleared",
            &format!(
                "def old_frame_fresh_extent_cleared (bytes : Nat -> IROption Nat) :
          Eq (IROption Nat) (ir_byte_mem_bytes_v1 {fresh} 72) (IROption.none Nat) :=
          Eq.refl (IROption Nat) (IROption.none Nat)"
            ),
        );
        for (name, corrupted) in [
            (
                "old_frame_wrong_callback",
                claim.replacen(
                    "IRByteMemoryResultV1.value (IRScalar.fnptr_ 41)",
                    "IRByteMemoryResultV1.value (IRScalar.fnptr_ 7)",
                    1,
                ),
            ),
            (
                "old_frame_wrong_capture",
                claim.replacen(
                    "IRByteMemoryResultV1.value (IRScalar.ptr_ 16)",
                    "IRByteMemoryResultV1.value (IRScalar.ptr_ 88)",
                    1,
                ),
            ),
            (
                "old_frame_returns_stale_memory",
                claim.replacen(
                    &format!("IRByteMemoryResultV1.value (IRScalar.fnptr_ 41) {fresh}"),
                    &format!("IRByteMemoryResultV1.value (IRScalar.fnptr_ 41) {initialized}"),
                    1,
                ),
            ),
            (
                "old_frame_observes_stale_memory",
                claim.replacen(
                    &format!("(IRScalar.ptr_ 16) 0 Bool.false {fresh}"),
                    &format!("(IRScalar.ptr_ 16) 0 Bool.false {initialized}"),
                    1,
                ),
            ),
        ] {
            assert_ne!(corrupted, claim, "mutation must change an actual endpoint");
            reject(
                &mut spec,
                name,
                &format!("def {name} (bytes : Nat -> IROption Nat) : {corrupted} := {proof}"),
            );
        }
        let actual = format!("ir_byte_load_v1 old_frame_capture_ctx (IRTy.func_ 18) (IRScalar.ptr_ 16) 0 Bool.false {fresh}");
        let fault =
            format!("IRByteMemoryResultV1.fault (IROutcome.ub IRFault.width_bounded) {fresh}");
        add_checked(&mut spec, "old_frame_wrong_signature_fault", &format!(
            "def old_frame_wrong_signature_fault (bytes : Nat -> IROption Nat) : Eq IRByteMemoryResultV1 ({actual}) ({fault}) := Eq.refl IRByteMemoryResultV1 ({fault})"));
        reject(&mut spec, "old_frame_wrong_signature_success", &format!(
            "def old_frame_wrong_signature_success (bytes : Nat -> IROption Nat) : Eq IRByteMemoryResultV1 ({actual})
              (IRByteMemoryResultV1.value (IRScalar.fnptr_ 41) {fresh}) := Eq.refl IRByteMemoryResultV1 ({fault})"));
    });
}

#[test]
fn byte_old_frame_history_access_and_fault_premises_are_not_assumed() {
    let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
    add_checked(
        &mut spec,
        "old_frame_buried_cover_bound",
        &format!(
            "def old_frame_buried_cover_bound : Nat.lt (Nat.add 24 8) 65 :=
      ir_byte_high_water_covered_end_v1 {} 65 24 8 {} (Eq.refl Bool Bool.true)",
            history(),
            high_water()
        ),
    );
    add_checked(&mut spec, "old_frame_buried_access_preserved", &format!(
        "def old_frame_buried_access_preserved : Eq Bool (ir_byte_accessible_v1
        (IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 72 16 2 Bool.true) {}) 24 8 8) Bool.true :=
      ir_byte_old_frame_accessible_fresh_v1 {} 65 72 16 2 24 8 8 (Nat.le_add_right 65 7) {} (Eq.refl Bool Bool.true)", history(), history(), high_water()));

    let caller = "(IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 16 1 Bool.true) (IRList.nil IRByteAllocationV1))";
    let retired = "(IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 16 1 Bool.false) (IRList.nil IRByteAllocationV1))";
    let overlapping = format!(
        "(IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 23 8 2 Bool.true) {caller})"
    );
    for (name, allocs, address, align) in [
        ("old_frame_overlapping_access", overlapping.as_str(), 16, 8),
        ("old_frame_retired_access", retired, 16, 8),
        ("old_frame_misaligned_access", caller, 24, 16),
        ("old_frame_invalid_alignment", caller, 16, 3),
    ] {
        let decision = format!("ir_byte_accessible_v1 {allocs} {address} 8 {align}");
        observe_bool(&mut spec, name, &decision, false);
        reject(
            &mut spec,
            &format!("{name}_success"),
            &format!(
                "def {name}_success : Eq Bool ({decision}) Bool.true := Eq.refl Bool Bool.false"
            ),
        );
        // A real load-at checks access before reading or decoding; bytes remain
        // arbitrary, so no successful post-read is smuggled into this control.
        let mem = format!("(IRByteMemoryV1.mk {allocs} bytes 65)");
        let fault = format!("(IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr) {mem})");
        add_checked(&mut spec, &format!("{name}_fault"), &format!(
            "def {name}_fault (ctx : IRByteContextV1) (bytes : Nat -> IROption Nat) :
          Eq IRByteMemoryResultV1 (ir_byte_load_at_v1 ctx IRTy.ptr_ {address} 8 {align} {mem}) {fault} :=
          Eq.refl IRByteMemoryResultV1 {fault}"));
    }
    let before_retirement = format!("(IRByteMemoryV1.mk {} bytes 65)", history());
    let after_retirement = format!("(ir_byte_retire_v1 1 {before_retirement})");
    let retired_fault =
        format!("(IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr) {after_retirement})");
    add_checked(&mut spec, "old_frame_actual_owner_retirement_fault", &format!(
        "def old_frame_actual_owner_retirement_fault (ctx : IRByteContextV1) (bytes : Nat -> IROption Nat) :
      Eq IRByteMemoryResultV1 (ir_byte_load_at_v1 ctx IRTy.ptr_ 16 8 8 {after_retirement}) {retired_fault} :=
      Eq.refl IRByteMemoryResultV1 {retired_fault}"));
    reject(&mut spec, "old_frame_actual_owner_retirement_success", &format!(
        "def old_frame_actual_owner_retirement_success (ctx : IRByteContextV1) (bytes : Nat -> IROption Nat) :
      Eq IRByteMemoryResultV1 (ir_byte_load_at_v1 ctx IRTy.ptr_ 16 8 8 {after_retirement})
        (IRByteMemoryResultV1.value (IRScalar.ptr_ 80) {after_retirement}) :=
      Eq.refl IRByteMemoryResultV1 {retired_fault}"));
    // Retired history still reserves address space for overlap/high-water.
    // The actual fresh allocator must reject reuse of that historical extent.
    let stale_retired = "(IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 72 8 3 Bool.false) (IRList.nil IRByteAllocationV1))";
    for (name, allocs, cursor) in [
        ("old_frame_stale_cursor", caller, 24),
        ("old_frame_stale_retired", stale_retired, 65),
    ] {
        let mem = format!("(IRByteMemoryV1.mk {allocs} bytes {cursor})");
        let fault = format!("(IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr) {mem})");
        let actual = format!("(ir_byte_allocate_range_v1 16 8 2 {mem})");
        add_checked(&mut spec, &format!("{name}_fault"), &format!(
            "def {name}_fault (bytes : Nat -> IROption Nat) : Eq IRByteMemoryResultV1 {actual} {fault} := Eq.refl IRByteMemoryResultV1 {fault}"));
        reject(
            &mut spec,
            &format!("{name}_success"),
            &format!(
            "def {name}_success (bytes : Nat -> IROption Nat) : Eq IRByteMemoryResultV1 {actual}
          (IRByteMemoryResultV1.value (IRScalar.ptr_ (ir_byte_aligned_base_v1 {cursor} 8)) {mem}) :=
          Eq.refl IRByteMemoryResultV1 {fault}"),
        );
    }
    reject(&mut spec, "old_frame_false_overlap_premise", &format!(
        "def old_frame_false_overlap_premise : Eq Bool
      (ir_byte_accessible_v1 {overlapping} 16 8 8) Bool.true :=
      ir_byte_accessible_prepend_nonoverlap_v1 {caller} (IRByteAllocationV1.mk 23 8 2 Bool.true) 16 8 8
        (Eq.refl Bool Bool.false) (Eq.refl Bool Bool.true)"));
    reject(
        &mut spec,
        "old_frame_false_high_water",
        &format!(
            "def old_frame_false_high_water : ir_byte_high_water_v1 {caller} 32 :=
      @And.intro (Nat.lt 32 32) True (Nat.le_refl 32) True.intro"
        ),
    );
}

#[test]
fn byte_old_frame_closed_endpoint_is_stricter_than_byte_nonoverlap() {
    let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
    let caller = "(IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 16 1 Bool.true) (IRList.nil IRByteAllocationV1))";
    let adjacent = "(IRByteAllocationV1.mk 32 16 2 Bool.true)";
    let added = format!("(IRList.cons IRByteAllocationV1 {adjacent} {caller})");
    observe_bool(
        &mut spec,
        "old_frame_adjacent_byte_overlap",
        &format!("ir_byte_overlaps_v1 {adjacent} 24 8"),
        false,
    );
    add_checked(&mut spec, "old_frame_adjacent_byte_access", &format!(
        "def old_frame_adjacent_byte_access : Eq Bool (ir_byte_accessible_v1 {added} 24 8 8) Bool.true :=
      ir_byte_accessible_prepend_nonoverlap_v1 {caller} {adjacent} 24 8 8 (Eq.refl Bool Bool.false) (Eq.refl Bool Bool.true)"));
    for (name, allocs, count) in [
        ("old_frame_point_before", caller, 1),
        ("old_frame_point_after", added.as_str(), 2),
    ] {
        add_checked(&mut spec, name, &format!("def {name} : Eq Nat (ir_byte_point_count_v1 {allocs} 32) {count} := Eq.refl Nat {count}"));
    }
    observe_bool(
        &mut spec,
        "old_frame_onepast_before",
        &format!("ir_byte_same_allocation_v1 {caller} 16 32"),
        true,
    );
    observe_bool(
        &mut spec,
        "old_frame_onepast_after",
        &format!("ir_byte_same_allocation_v1 {added} 16 32"),
        false,
    );
    reject(
        &mut spec,
        "old_frame_adjacent_not_strict",
        &format!(
            "def old_frame_adjacent_not_strict : Eq Bool (ir_byte_same_allocation_v1 {added} 16 32)
      (ir_byte_same_allocation_v1 {caller} 16 32) :=
      ir_byte_same_allocation_prepend_before_v1 {caller} {adjacent} 16 32
        (Nat.le_add_right 17 15) (Nat.le_refl 32)"
        ),
    );
    // An actual fresh high-water allocation leaves a strict gap. The same
    // one-past endpoint is then preserved, including buried history.
    add_checked(
        &mut spec,
        "old_frame_onepast_fresh_gap",
        &format!(
            "def old_frame_onepast_fresh_gap : Eq Bool (ir_byte_same_allocation_v1
        (IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 72 16 2 Bool.true) {}) 16 32)
      (ir_byte_same_allocation_v1 {} 16 32) :=
      ir_byte_same_allocation_prepend_before_v1 {} (IRByteAllocationV1.mk 72 16 2 Bool.true) 16 32
        (Nat.le_add_right 17 55) (Nat.le_add_right 33 39)",
            history(),
            history(),
            history()
        ),
    );
}
