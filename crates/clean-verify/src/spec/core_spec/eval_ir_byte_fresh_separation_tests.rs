// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::Name;

fn spec() -> Specification {
    Specification::new_eval_ir_byte_prelude_spec_v1().expect("actual byte prelude and checked laws")
}

fn checked(spec: &Specification, name: &str) {
    let declaration = spec.get_definition(name).unwrap();
    assert!(!declaration.is_axiom);
    assert!(declaration.elaborated_value.is_some());
    spec.verify_definition(name).unwrap();
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(
        source,
        "Actual caller-access and arbitrary fresh-range consumer",
    )
    .unwrap_or_else(|error| panic!("{name}: {error}"));
    checked(spec, name);
}

fn reject(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Invalid caller-memory contract")
        .expect_err("forged freshness/access/result must fail kernel checking");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
}

fn rows(data: &[(u64, u64, u64, bool)]) -> String {
    data.iter().rev().fold("(IRList.nil IRByteAllocationV1)".into(), |tail, (base, size, owner, live)| {
        format!("(IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk {base} {size} {owner} Bool.{live}) {tail})")
    })
}

fn access(allocs: &str, base: u64, address: u64, width: u64, align: u64) -> String {
    format!(
        "(ir_byte_accessible_v1 (IRList.cons IRByteAllocationV1
      (IRByteAllocationV1.mk {base} 16 owner Bool.true) {allocs}) {address} {width} {align})"
    )
}

fn rule(allocs: &str, base: u64, address: u64, width: u64, align: u64) -> String {
    format!(
        "ir_byte_accessible_fresh_range_v1 {allocs} {base} 16 owner {address} {width} {align}
      (Eq.refl Nat 0) (Eq.refl Bool Bool.true)"
    )
}

#[test]
fn fresh_separation_universal_laws_replay_without_axioms_or_trust_markers() {
    crate::test_utils::run_with_stack(|| {
        let spec = spec();
        assert_eq!(laws().len(), 13);
        for (name, _) in laws() {
            checked(&spec, name);
        }
    });
}

#[test]
fn fresh_separation_frames_before_after_and_between_preserve_actual_caller_access() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        // Deliberately unsorted, including retired history. Both boundary
        // adjacency directions are legal for these half-open access ranges.
        let allocs = rows(&[(224, 32, 0, true), (40, 8, 7, false), (128, 40, 0, true)]);
        for (index, base) in [16, 80, 112, 168, 192, 256].into_iter().enumerate() {
            let name = format!("fresh_access_case_{index}");
            add(
                &mut spec,
                &name,
                &format!(
                    "def {name} (owner : Nat) : Eq Bool {} Bool.true := {}",
                    access(&allocs, base, 128, 40, 8),
                    rule(&allocs, base, 128, 40, 8)
                ),
            );
            let name = format!("fresh_separated_case_{index}");
            add(
                &mut spec,
                &name,
                &format!(
                    "def {name} (owner : Nat) :
              Or (Nat.le (Nat.add {base} 16) 128) (Nat.le 168 {base}) :=
              ir_byte_fresh_range_disjoint_v1 {allocs} {base} 16 owner 128 40 8
                (Nat.zero_lt_succ 15) (Eq.refl Nat 0) (Eq.refl Bool Bool.true)"
                ),
            );
            let name = format!("fresh_read_preserved_case_{index}");
            add(
                &mut spec,
                &name,
                &format!(
                    "def {name} (bytes : Nat -> IROption Nat) (owner word : Nat) :
              Eq (IROption Nat)
                (ir_byte_read_word_v1 (ir_byte_write_word_v1 bytes 128 40 word) 16 {base})
                (ir_byte_read_word_v1 bytes 16 {base}) :=
              ir_byte_fresh_range_read_preserved_v1 bytes {allocs} {base} 16 owner 128 40 8 word
                (Nat.zero_lt_succ 15) (Eq.refl Nat 0) (Eq.refl Bool Bool.true)"
                ),
            );
        }
    });
}

#[test]
fn fresh_separation_refuses_overlap_retirement_partial_ranges_alignment_and_result_swaps() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = spec();
        let normal = rows(&[(128, 40, 0, true), (40, 8, 7, false), (224, 32, 0, true)]);
        let retired = rows(&[(128, 40, 0, false)]);
        let adjacent = rows(&[(128, 16, 0, true), (144, 24, 0, true)]);
        let overlapping = rows(&[(128, 40, 0, true), (144, 8, 9, false)]);
        let empty = rows(&[]);
        for (index, (allocs, base, address, width, align)) in [
            (&normal, 128, 128, 40, 8), // frame covers caller output
            (&normal, 120, 128, 40, 8), // only frame tail overlaps
            (&normal, 160, 128, 40, 8), // only frame head overlaps
            (&normal, 40, 128, 40, 8),  // fresh frame overlaps retired history
            (&normal, 224, 128, 40, 8), // overlaps another live allocation
            (&retired, 80, 128, 40, 8),
            (&adjacent, 80, 128, 40, 8),
            (&overlapping, 80, 128, 40, 8),
            (&normal, 80, 136, 40, 8), // caller range escapes allocation
            (&normal, 80, 129, 8, 8),  // misaligned caller
            (&normal, 80, 128, 0, 8),  // empty caller range
            (&normal, 80, 128, 40, 3), // unsupported alignment
            (&empty, 80, 128, 40, 8),
        ]
        .into_iter()
        .enumerate()
        {
            let name = format!("fresh_bad_access_{index}");
            reject(
                &mut spec,
                &name,
                &format!(
                    "def {name} (owner : Nat) : Eq Bool {} Bool.true := {}",
                    access(allocs, base, address, width, align),
                    rule(allocs, base, address, width, align)
                ),
            );
        }
        reject(
            &mut spec,
            "fresh_bad_result",
            &format!(
                "def fresh_bad_result (owner : Nat) :
          Eq Bool {} Bool.false := {}",
                access(&normal, 80, 128, 40, 8),
                rule(&normal, 80, 128, 40, 8)
            ),
        );
        reject(
            &mut spec,
            "fresh_bad_read_address",
            &format!(
                "def fresh_bad_read_address
          (bytes : Nat -> IROption Nat) (owner word : Nat) :
          Eq (IROption Nat) (ir_byte_read_word_v1 (ir_byte_write_word_v1 bytes 128 40 word) 16 80)
            (ir_byte_read_word_v1 bytes 16 96) :=
          ir_byte_fresh_range_read_preserved_v1 bytes {normal} 80 16 owner 128 40 8 word
            (Nat.zero_lt_succ 15) (Eq.refl Nat 0) (Eq.refl Bool Bool.true)"
            ),
        );
    });
}
