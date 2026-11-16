// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nonvacuity and adversarial consumers of actual allocation/freshness laws.
//! This is byte-profile semantics, not a proof of TLA lowering or native memory.

use super::*;
use clean_kernel::Name;

fn spec() -> Specification {
    Specification::new_eval_ir_byte_prelude_spec_v1()
        .expect("actual public byte-profile prelude with checked allocation laws")
}

fn checked(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).unwrap();
    assert!(!definition.is_axiom);
    assert!(definition.elaborated_value.is_some());
    spec.verify_definition(name).unwrap();
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add_checked(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(source, "Actual byte allocation consumer")
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    checked(spec, name);
}

fn reject(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Invalid allocator claim")
        .expect_err("invalid allocation/access must fail kernel admission");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
}

#[test]
fn arbitrary_allocation_lists_have_checked_freshness_rules() {
    crate::test_utils::run_with_stack(|| {
        let spec = spec();
        for (name, _) in laws() {
            checked(&spec, name);
        }
    });
}

const NIL: &str = "(@IRList.nil IRByteAllocationV1)";

fn rows(data: &[(u64, u64, u64, bool)]) -> String {
    data.iter().rev().fold(NIL.to_owned(), |tail, (base, size, owner, live)| {
        format!("(@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk {base} {size} {owner} Bool.{live}) {tail})")
    })
}

fn high_water(data: &[(u64, u64, u64, bool)], cursor: u64) -> String {
    data.iter().enumerate().rev().fold(
        "True.intro".to_owned(),
        |tail_proof, (i, (base, size, _, _))| {
            let end = base + size;
            assert!(end < cursor, "test fixture must have strict high water");
            let tail = rows(&data[i + 1..]);
            format!(
                "(@And.intro (Nat.lt {end} {cursor}) (ir_byte_high_water_v1 {tail} {cursor})\n\
          (Nat.le_add_right {} {}) ({tail_proof}))",
                end + 1,
                cursor - end - 1
            )
        },
    )
}

#[test]
fn typed_frame_allocation_rounds_cursor_and_admits_both_real_slots() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        // Nonempty arbitrary-order history, including global and retired rows.
        // Byte contents and the new activation owner remain quantified.
        let data = [(16, 8, 7, true), (48, 8, 4, false), (32, 8, 0, true)];
        let allocs = rows(&data);
        let before = high_water(&data, 65);
        let fresh = format!("(ir_byte_fresh_memory_v1 {allocs} bytes 72 16 owner)");
        let ty = "(IRTy.array_ (IRTy.uint_ 8) 16)";
        let layout = format!("(IRByteLayoutV1.mk {ty} 16 1 (@IRList.nil IRTy) (@IRList.nil Nat))");
        let room = "(Nat.le_add_right 89 18446744073709551527)";
        let args = format!("{allocs} bytes 65 owner (Nat.zero_lt_succ 64) {room} {before}");
        add_checked(
            &mut spec,
            "allocation_array16_context",
            &format!(
                "def allocation_array16_context : IRByteContextV1 :=\n\
          IRByteContextV1.mk (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal))\n\
            (@IRList.cons IRByteLayoutV1 {layout} (@IRList.nil IRByteLayoutV1))\n\
            (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1) (@IRList.nil IRByteSiteV1)"
            ),
        );
        add_checked(
            &mut spec,
            "allocation_array16_layout",
            &format!(
                "def allocation_array16_layout :\n\
          @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 allocation_array16_context {ty})\n\
            (@IROption.some IRByteLayoutV1 {layout}) := @Eq.refl (IROption IRByteLayoutV1) (@IROption.some IRByteLayoutV1 {layout})"
            ),
        );
        add_checked(
            &mut spec,
            "allocation_real_array16",
            &format!(
                "def allocation_real_array16\n\
          (ctx : IRByteContextV1) (bytes : Nat -> IROption Nat) (owner : Nat)\n\
          (layout : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx {ty}) (@IROption.some IRByteLayoutV1 {layout})) :\n\
          @Eq IRByteMemoryResultV1 (ir_byte_alloc_v1 ctx {ty} 1 8 owner (IRByteMemoryV1.mk {allocs} bytes 65))\n\
            (IRByteMemoryResultV1.value (IRScalar.ptr_ 72) {fresh}) :=\n\
          ir_byte_frame16_typed_allocate_v1 ctx {args} layout"
            ),
        );
        // Instantiate the actual table lookup, not merely a conditional catalog
        // premise. This tiny memory context is not an actual-TY module claim.
        add_checked(
            &mut spec,
            "allocation_inhabited_array16",
            &format!(
                "def allocation_inhabited_array16\n\
          (bytes : Nat -> IROption Nat) (owner : Nat) :\n\
          @Eq IRByteMemoryResultV1\n\
            (ir_byte_alloc_v1 allocation_array16_context {ty} 1 8 owner (IRByteMemoryV1.mk {allocs} bytes 65))\n\
            (IRByteMemoryResultV1.value (IRScalar.ptr_ 72) {fresh}) :=\n\
          allocation_real_array16 allocation_array16_context bytes owner allocation_array16_layout"
            ),
        );
        for (address, access_rule, gep_rule, offset) in [
            (
                72,
                "ir_byte_frame16_first_accessible_v1",
                "ir_byte_frame16_first_gep_v1",
                0,
            ),
            (
                80,
                "ir_byte_frame16_second_accessible_v1",
                "ir_byte_frame16_second_gep_v1",
                8,
            ),
        ] {
            let access_name = format!("allocation_real_slot{offset}");
            add_checked(
                &mut spec,
                &access_name,
                &format!(
                    "def {access_name} (bytes : Nat -> IROption Nat) (owner : Nat) :\n\
              @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 {fresh}) {address} 8 8) Bool.true := {access_rule} {args}"
                ),
            );
            let gep_name = format!("allocation_real_gep{offset}");
            add_checked(
                &mut spec,
                &gep_name,
                &format!(
                    "def {gep_name} (bytes : Nat -> IROption Nat) (owner : Nat) :\n\
              @Eq IRByteMemoryResultV1 (ir_byte_gep_at_v1 72 1 {offset} Bool.true {fresh})\n\
                (IRByteMemoryResultV1.value (IRScalar.ptr_ {address}) {fresh}) := {gep_rule} {args}"
                ),
            );
        }
        add_checked(
            &mut spec,
            "allocation_real_cursor",
            &format!(
                "def allocation_real_cursor (bytes : Nat -> IROption Nat) (owner : Nat) :\n\
          ir_byte_high_water_v1 (ir_byte_mem_allocs_v1 {fresh}) 89 := ir_byte_frame16_high_water_v1 {args}"
            ),
        );
    });
}

#[test]
fn adjacent_closed_endpoint_is_not_inbounds_despite_readable_slots() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        let old = rows(&[(8, 8, 1, true)]);
        let mem = format!(
            "(ir_byte_fresh_memory_v1 {old} (fun (_ : Nat) => @IROption.none Nat) 16 16 2)"
        );
        // The underlying allocator permits adjacency for malformed incoming
        // cursor discipline. Half-open access is fine; inbounds is not.
        add_checked(
            &mut spec,
            "allocation_adjacent_succeeds",
            &format!(
                "def allocation_adjacent_succeeds :\n\
          @Eq IRByteMemoryResultV1 (ir_byte_allocate_range_v1 16 8 2 (IRByteMemoryV1.mk {old} (fun (_ : Nat) => @IROption.none Nat) 16))\n\
            (IRByteMemoryResultV1.value (IRScalar.ptr_ 16) {mem}) :=\n\
          @Eq.refl IRByteMemoryResultV1 (IRByteMemoryResultV1.value (IRScalar.ptr_ 16) {mem})"
            ),
        );
        add_checked(
            &mut spec,
            "allocation_adjacent_access",
            &format!(
                "def allocation_adjacent_access : @Eq Bool\n\
          (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 {mem}) 16 8 8) Bool.true := @Eq.refl Bool Bool.true"
            ),
        );
        let fault = format!("(IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr) {mem})");
        add_checked(
            &mut spec,
            "allocation_adjacent_gep_fault",
            &format!(
                "def allocation_adjacent_gep_fault :\n\
          @Eq IRByteMemoryResultV1 (ir_byte_gep_at_v1 16 1 0 Bool.true {mem}) {fault} := @Eq.refl IRByteMemoryResultV1 {fault}"
            ),
        );
        let false_success = format!("(IRByteMemoryResultV1.value (IRScalar.ptr_ 16) {mem})");
        reject(
            &mut spec,
            "allocation_bad_adjacent_gep",
            &format!(
                "def allocation_bad_adjacent_gep :\n\
          @Eq IRByteMemoryResultV1 (ir_byte_gep_at_v1 16 1 0 Bool.true {mem}) {false_success} :=\n\
          @Eq.refl IRByteMemoryResultV1 {false_success}"
            ),
        );
    });
}

#[test]
fn retired_overlap_stale_cursor_and_exclusive_limit_reject_false_success() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        for (name, old, cursor, base) in [
            (
                "allocation_bad_retired_overlap",
                rows(&[(16, 16, 3, false)]),
                16_u64,
                16_u64,
            ),
            (
                "allocation_bad_stale_cursor",
                rows(&[(16, 16, 3, true)]),
                17,
                24,
            ),
            ("allocation_bad_zero_cursor", NIL.to_owned(), 0, 0),
            (
                "allocation_bad_exclusive_limit",
                NIL.to_owned(),
                18446744073709551600,
                18446744073709551600,
            ),
        ] {
            let bytes = "(fun (_ : Nat) => @IROption.none Nat)";
            let mem = format!("(IRByteMemoryV1.mk {old} {bytes} {cursor})");
            let actual = format!("(ir_byte_allocate_range_v1 16 8 9 {mem})");
            let fault =
                format!("(IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr) {mem})");
            let fault_name = format!("{name}_fault");
            add_checked(
                &mut spec,
                &fault_name,
                &format!(
                    "def {fault_name} :\n\
              @Eq IRByteMemoryResultV1 {actual} {fault} := @Eq.refl IRByteMemoryResultV1 {fault}"
                ),
            );
            let success = format!(
                "(IRByteMemoryResultV1.value (IRScalar.ptr_ {base}) (ir_byte_fresh_memory_v1 {old} {bytes} {base} 16 9))"
            );
            reject(
                &mut spec,
                name,
                &format!(
                    "def {name} : @Eq IRByteMemoryResultV1\n\
              {actual} {success} :=\n\
              @Eq.refl IRByteMemoryResultV1 {success}"
                ),
            );
        }
    });
}
