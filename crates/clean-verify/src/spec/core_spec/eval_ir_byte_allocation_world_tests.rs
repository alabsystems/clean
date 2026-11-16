// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Actual operational endpoints and strict counterexamples, not native evidence.

use super::*;
use clean_kernel::Name;

fn spec() -> Specification {
    Specification::new_eval_ir_byte_prelude_spec_v1()
        .expect("public byte profile with allocation-world laws")
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

fn add(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(source, "Actual byte-world consumer")
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    checked(spec, name);
}

fn reject(spec: &mut Specification, source: &str) {
    let error = spec
        .add_recursive_def(source, "Invalid allocation-world claim")
        .expect_err("false claim must be rejected");
    crate::test_utils::assert_type_mismatch_rejection(&error, "allocation-world claim");
}

#[test]
fn allocation_world_quantified_roots_replay_without_axioms_or_trust() {
    crate::test_utils::run_with_stack(|| {
        let spec = spec();
        for (name, _) in laws() {
            checked(&spec, name);
        }
    });
}

const NIL: &str = "(@IRList.nil IRByteAllocationV1)";
const OWNER_TAIL: &str = "(@IRList.cons Nat 1 (@IRList.nil Nat))";
const OWNER_LIST: &str = "(@IRList.cons Nat 2 (@IRList.cons Nat 1 (@IRList.nil Nat)))";
const CURRENT: &str = "(IRFrame.mk 9 0 7 (@IRList.cons IRBinding (IRBinding.mk 40 (IRScalar.bool_ Bool.true)) (@IRList.nil IRBinding)) (@IRList.nil Nat))";
const TAIL: &str = "(@IRList.cons IRFrame (IRFrame.mk 8 0 3 (@IRList.nil IRBinding) (@IRList.nil Nat)) (@IRList.nil IRFrame))";
const LEGACY: &str = "(@IRList.nil IRMemSlot)";

fn rows(data: &[(u64, u64, u64, bool)]) -> String {
    data.iter().rev().fold(NIL.into(), |tail, (base, size, owner, live)| {
        format!("(@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk {base} {size} {owner} Bool.{live}) {tail})")
    })
}

fn high_water(data: &[(u64, u64, u64, bool)], cursor: u64) -> String {
    data.iter()
        .enumerate()
        .rev()
        .fold("True.intro".into(), |proof, (i, (base, size, _, _))| {
            let end = base + size;
            assert!(end < cursor);
            format!(
                "(@And.intro (Nat.lt {end} {cursor}) (ir_byte_high_water_v1 {} {cursor})
          (Nat.le_add_right {} {}) ({proof}))",
                rows(&data[i + 1..]),
                end + 1,
                cursor - end - 1
            )
        })
}

#[test]
fn allocation_world_actual_alloca_binds_pointer_and_retains_arbitrary_host_bytes() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        let data = [(16, 8, 1, true), (48, 8, 3, false), (32, 8, 0, true)];
        let allocs = rows(&data);
        let high = high_water(&data, 65);
        let ty = "(IRTy.array_ (IRTy.uint_ 8) 16)";
        let layout = format!("(IRByteLayoutV1.mk {ty} 16 1 (@IRList.nil IRTy) (@IRList.nil Nat))");
        add(
            &mut spec,
            "allocation_world_context",
            &format!(
                "def allocation_world_context : IRByteContextV1 :=
          IRByteContextV1.mk (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal))
          (@IRList.cons IRByteLayoutV1 {layout} (@IRList.nil IRByteLayoutV1))
          (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1) (@IRList.nil IRByteSiteV1)"
            ),
        );
        add(&mut spec, "allocation_world_lookup", &format!("def allocation_world_lookup :
          @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 allocation_world_context {ty})
          (@IROption.some IRByteLayoutV1 {layout}) := @Eq.refl (IROption IRByteLayoutV1) (@IROption.some IRByteLayoutV1 {layout})"));
        let mem = format!("(IRByteMemoryV1.mk {allocs} bytes 65)");
        let world = format!("(@IRByteWorldV1.mk Nat {mem} host {OWNER_LIST} 5)");
        let machine = format!("(IRMachine.mk (@IRList.cons IRFrame {CURRENT} {TAIL}) {LEGACY} 1)");
        let dests = "(@IRList.cons Nat 99 (@IRList.nil Nat))";
        let values = "(@IRList.cons IRScalar (IRScalar.ptr_ 72) (@IRList.nil IRScalar))";
        let site = format!("(IRByteSiteV1.mk 9 0 7 8 1 {PTR_TYPES})");
        let actual = format!("(ir_byte_alloca_exec_v1 Nat allocation_world_context {machine} {world} {dests} {site} {ty} (@IROption.none Nat))");
        let fresh = format!("(ir_byte_fresh_memory_v1 {allocs} bytes 72 16 2)");
        let expected = format!("(@IRByteConfigV1.running Nat
          (IRMachine.mk (@IRList.cons IRFrame (ir_frame_advance (ir_frame_set_many {CURRENT} {dests} {values})) {TAIL}) {LEGACY} 1)
          (ir_byte_with_memory_v1 Nat {world} {fresh}))");
        let arguments = format!(
            "Nat {allocs} bytes 65 host 2 {OWNER_TAIL} 5 {CURRENT} {TAIL} {LEGACY} 1
          allocation_world_context 99 9 0 7 1 (Nat.zero_lt_succ 64)
          (Nat.le_add_right 89 18446744073709551527) {high} allocation_world_lookup"
        );
        add(&mut spec, "allocation_world_actual_exact", &format!("def allocation_world_actual_exact
          (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {actual} {expected} :=
          ir_byte_alloca_frame16_exact_v1 {arguments}"));
        let predicate = "(fun (c : IRByteConfigV1 Nat) => @IRByteConfigV1.rec Nat (fun (_ : IRByteConfigV1 Nat) => Prop)
          (fun (s : IRMachine) (w : IRByteWorldV1 Nat) => @Eq Bool (ir_byte_world_valid_v1 Nat s w) Bool.true)
          (fun (_ : IROutcome) (_ : IRByteWorldV1 Nat) => False) c)";
        add(
            &mut spec,
            "allocation_world_actual_valid",
            &format!(
                "def allocation_world_actual_valid
          (bytes : Nat -> IROption Nat) (host : Nat) : {predicate} {actual} :=
          ir_byte_alloca_frame16_world_v1 {arguments} (@Eq.refl Bool Bool.true)"
            ),
        );
        // Actual TY sites use Fast=1. Alloca itself ignores the calling
        // convention field; check C=0 through the same generic theorem too.
        // This is not a claim that calls can ignore their convention.
        let c_site = format!("(IRByteSiteV1.mk 9 0 7 8 0 {PTR_TYPES})");
        let c_actual = format!("(ir_byte_alloca_exec_v1 Nat allocation_world_context {machine} {world} {dests} {c_site} {ty} (@IROption.none Nat))");
        let c_arguments = format!(
            "Nat {allocs} bytes 65 host 2 {OWNER_TAIL} 5 {CURRENT} {TAIL} {LEGACY} 1
          allocation_world_context 99 9 0 7 0 (Nat.zero_lt_succ 64)
          (Nat.le_add_right 89 18446744073709551527) {high} allocation_world_lookup"
        );
        add(&mut spec, "allocation_world_c_exact", &format!("def allocation_world_c_exact
          (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {c_actual} {expected} :=
          ir_byte_alloca_frame16_exact_v1 {c_arguments}"));
        add(&mut spec, "allocation_world_c_fast_same_alloca", &format!("def allocation_world_c_fast_same_alloca
          (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {c_actual} {actual} :=
          @Eq.trans (IRByteConfigV1 Nat) {c_actual} {expected} {actual}
            (allocation_world_c_exact bytes host)
            (@Eq.symm (IRByteConfigV1 Nat) {actual} {expected} (allocation_world_actual_exact bytes host))"));
        // Independent pointer observation, in addition to the exact complete
        // frame/world endpoint above (SSA update, one advance and retained tail).
        let observe = "(fun (c : IRByteConfigV1 Nat) => @IRByteConfigV1.rec Nat (fun (_ : IRByteConfigV1 Nat) => IRScalar)
          (fun (s : IRMachine) (_ : IRByteWorldV1 Nat) => ir_getd s 99)
          (fun (_ : IROutcome) (_ : IRByteWorldV1 Nat) => IRScalar.undef_) c)";
        add(&mut spec, "allocation_world_pointer_observation", &format!("def allocation_world_pointer_observation
          (bytes : Nat -> IROption Nat) (host : Nat) : @Eq IRScalar ({observe} {actual}) (IRScalar.ptr_ 72) :=
          ir_eq_cong (IRByteConfigV1 Nat) IRScalar {observe} {actual} {expected}
            (allocation_world_actual_exact bytes host)"));
        // A caller-owned slab would satisfy the owner-support invariant too,
        // but is not what this Alloca does. Check the exact endpoint separately
        // so world validity cannot conceal an incorrect activation owner.
        let wrong_fresh = format!("(ir_byte_fresh_memory_v1 {allocs} bytes 72 16 1)");
        let wrong_world = format!("(ir_byte_with_memory_v1 Nat {world} {wrong_fresh})");
        let wrong_expected = expected.replace(&fresh, &wrong_fresh);
        add(&mut spec, "allocation_world_other_active_owner_valid", &format!("def allocation_world_other_active_owner_valid
          (bytes : Nat -> IROption Nat) (host : Nat) :
          @Eq Bool (ir_byte_world_valid_v1 Nat {machine} {wrong_world}) Bool.true := @Eq.refl Bool Bool.true"));
        reject(&mut spec, &format!("def allocation_world_wrong_owner_execution
          (bytes : Nat -> IROption Nat) (host : Nat) : @Eq (IRByteConfigV1 Nat) {actual} {wrong_expected} :=
          allocation_world_actual_exact bytes host"));
    });
}

#[test]
fn allocation_world_invalid_owners_extents_and_history_are_not_preserved() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        let good = [(16, 8, 1, true), (48, 8, 3, false), (32, 8, 0, true)];
        // Successful ordinary owner insertion is not permission to invent a
        // different live owner or make an invalid range/history well formed.
        let cases = [
            ("orphan", rows(&good), 72, 16, 3, OWNER_LIST.to_owned(), 5),
            (
                "not_fresh_owner",
                rows(&good),
                72,
                16,
                5,
                OWNER_LIST.to_owned(),
                5,
            ),
            (
                "null_extent",
                rows(&good),
                0,
                16,
                2,
                OWNER_LIST.to_owned(),
                5,
            ),
            (
                "empty_extent",
                rows(&good),
                72,
                0,
                2,
                OWNER_LIST.to_owned(),
                5,
            ),
            (
                "live_orphan_history",
                rows(&[(16, 8, 3, true)]),
                72,
                16,
                2,
                OWNER_LIST.to_owned(),
                5,
            ),
            (
                "invalid_retired_history",
                rows(&[(0, 8, 3, false)]),
                72,
                16,
                2,
                OWNER_LIST.to_owned(),
                5,
            ),
            (
                "duplicate_active",
                rows(&[(32, 8, 0, true), (48, 8, 3, false)]),
                72,
                16,
                2,
                "(@IRList.cons Nat 2 (@IRList.cons Nat 2 (@IRList.nil Nat)))".into(),
                5,
            ),
            (
                "stale_owner_cursor",
                rows(&[]),
                72,
                16,
                2,
                OWNER_LIST.to_owned(),
                2,
            ),
            (
                "zero_active_owner",
                rows(&[]),
                72,
                16,
                0,
                "(@IRList.cons Nat 0 (@IRList.cons Nat 1 (@IRList.nil Nat)))".into(),
                5,
            ),
        ];
        for (label, allocs, base, size, owner, owners, next) in cases {
            let fresh = format!("(ir_byte_fresh_memory_v1 {allocs} bytes {base} {size} {owner})");
            let target = format!(
                "(ir_byte_world_valid_v1 Nat
              (IRMachine.mk (@IRList.cons IRFrame {CURRENT} {TAIL}) {LEGACY} 1)
              (@IRByteWorldV1.mk Nat {fresh} host {owners} {next}))"
            );
            add(&mut spec, &format!("allocation_world_observed_{label}"), &format!("def allocation_world_observed_{label}
              (bytes : Nat -> IROption Nat) (host : Nat) : @Eq Bool {target} Bool.false := @Eq.refl Bool Bool.false"));
            reject(&mut spec, &format!("def allocation_world_bad_{label}
              (bytes : Nat -> IROption Nat) (host : Nat) : @Eq Bool {target} Bool.true := @Eq.refl Bool Bool.true"));
        }
        // The world predicate does not assert separation: even overlapping
        // old live/retired records and a zero allocation cursor can be valid.
        // This positive observation prevents silently inferring high-water.
        let overlap = rows(&[(16, 16, 1, true), (24, 8, 3, false)]);
        let target = format!(
            "(ir_byte_world_valid_v1 Nat
          (IRMachine.mk (@IRList.cons IRFrame {CURRENT} {TAIL}) {LEGACY} 1)
          (@IRByteWorldV1.mk Nat (IRByteMemoryV1.mk {overlap} bytes 0) host {OWNER_LIST} 5))"
        );
        add(&mut spec, "allocation_world_not_high_water", &format!("def allocation_world_not_high_water
          (bytes : Nat -> IROption Nat) (host : Nat) : @Eq Bool {target} Bool.true := @Eq.refl Bool Bool.true"));
    });
}
