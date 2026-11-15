// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Byte-observer model tests, not execution or layout evidence for Rust Name/Arc.
//! A supplied str view is not a ContainerLen header or an authenticated Name field.

use crate::spec::Specification;
use clean_kernel::Name;

const RESULT: &str = "IROption IRBuiltinNameAtomV1";
const NONE: &str = "IROption.none IRBuiltinNameAtomV1";
const LIMIT: u128 = 1_u128 << 64;
const WORDS: [(&str, &[u16]); 2] = [
    ("nat_", &[78, 97, 116]),
    ("string_", &[83, 116, 114, 105, 110, 103]),
];

fn specification() -> Specification {
    crate::eval_ir::build_byte_prelude_spec_v1_with_stack().expect("public ByteV1 vocabulary")
}

fn audit(spec: &mut Specification, name: &str) {
    let definition = spec.get_definition(name).expect("registered definition");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(name)
        .expect("independent kernel check");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Exact builtin-name byte-observer regression")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
    audit(spec, source.split_whitespace().nth(1).unwrap());
}

fn equality(spec: &mut Specification, name: &str, actual: &str, expected: &str) {
    add(
        spec,
        &format!(
            "def {name} : Eq ({RESULT}) ({actual}) ({expected}) :=
             Eq.refl ({RESULT}) ({expected})"
        ),
    );
}

fn some(atom: &str) -> String {
    format!("IROption.some IRBuiltinNameAtomV1 IRBuiltinNameAtomV1.{atom}")
}

fn allocations(rows: &[(u128, u128, u128, bool)]) -> String {
    rows.iter().rev().fold(
        "IRList.nil IRByteAllocationV1".to_string(),
        |tail, (base, size, owner, live)| {
            let live = if *live { "Bool.true" } else { "Bool.false" };
            format!(
                "IRList.cons IRByteAllocationV1
                 (IRByteAllocationV1.mk {base} {size} {owner} {live}) ({tail})"
            )
        },
    )
}

fn memory(rows: &[(u128, u128, u128, bool)], bytes: &[(u128, u16)], next: u128) -> String {
    let bytes =
        bytes
            .iter()
            .rev()
            .fold("IROption.none Nat".to_string(), |tail, (address, byte)| {
                format!(
                    "Bool.rec (fun (_ : Bool) => IROption Nat) ({tail})
                 (IROption.some Nat {byte}) (ir_nat_eqb address {address})"
                )
            });
    format!(
        "IRByteMemoryV1.mk ({}) (fun (address : Nat) => {bytes}) {next}",
        allocations(rows)
    )
}

fn at(base: u128, word: &[u16]) -> Vec<(u128, u16)> {
    word.iter()
        .enumerate()
        .map(|(index, byte)| (base + index as u128, *byte))
        .collect()
}

fn fixture(spec: &mut Specification, name: &str, word: &[u16]) {
    // The data address is intentionally not 8-aligned. str bytes need alignment1.
    let mut bytes = at(65, word);
    bytes.push((257, 201));
    add(
        spec,
        &format!(
            "def {name} : IRByteMemoryV1 := {}",
            memory(&[(64, 16, 7, true), (256, 8, 9, true)], &bytes, 1024)
        ),
    );
}

fn decode(mem: &str, ty: &str, value: &str) -> String {
    format!("ir_byte_builtin_name_atom_v1 ({mem}) ({ty}) ({value})")
}

fn view(mem: &str, address: u128, length: u128) -> String {
    decode(
        mem,
        "IRTy.fatstr_",
        &format!("IRScalar.fat_ {address} {length}"),
    )
}

#[test]
fn byte_builtin_name_exact_live_heap_views_check_and_have_empty_closures() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        audit(&mut spec, "ir_byte_builtin_name_atom_v1");
        for (index, (atom, word)) in WORDS.iter().enumerate() {
            let mem = format!("builtin_exact_memory_{index}");
            fixture(&mut spec, &mem, word);
            equality(
                &mut spec,
                &format!("builtin_exact_{index}"),
                &view(&mem, 65, word.len() as u128),
                &some(atom),
            );
        }
    });
}

#[test]
fn byte_builtin_name_every_byte_is_exact_initialized_and_canonical() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (kind, (_, word)) in WORDS.iter().enumerate() {
            for position in 0..word.len() {
                for mode in 0..3 {
                    let mut bytes = at(65, word);
                    match mode {
                        0 => bytes[position].1 += 1,
                        1 => {
                            bytes.remove(position);
                        }
                        2 => bytes[position].1 = 256,
                        _ => unreachable!(),
                    }
                    let mem = memory(&[(64, 16, 7, true)], &bytes, 1024);
                    equality(
                        &mut spec,
                        &format!("builtin_bad_byte_{kind}_{position}_{mode}"),
                        &view(&mem, 65, word.len() as u128),
                        NONE,
                    );
                }
            }
        }
    });
}

#[test]
fn byte_builtin_name_declared_kind_carrier_length_and_word_bounds_are_checked() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (kind, (_, word)) in WORDS.iter().enumerate() {
            let mem = format!("builtin_wrong_sort_memory_{kind}");
            fixture(&mut spec, &mem, word);
            let length = word.len() as u128;
            for (index, ty) in [
                "IRTy.fatslice_ (IRTy.uint_ 8)",
                "IRTy.containerlen_",
                "IRTy.containervtable_",
                "IRTy.fatdyn_ 7",
                "IRTy.fatptr_ (IRTy.uint_ 8)",
                "IRTy.ptr_",
                "IRTy.ref_ (IRTy.uint_ 8)",
                "IRTy.uint_ 64",
                "IRTy.usize_ 64",
                "IRTy.unit_",
            ]
            .iter()
            .enumerate()
            {
                equality(
                    &mut spec,
                    &format!("builtin_wrong_kind_{kind}_{index}"),
                    &decode(&mem, ty, &format!("IRScalar.fat_ 65 {length}")),
                    NONE,
                );
            }
            for (index, value) in [
                "IRScalar.undef_",
                "IRScalar.unit_",
                "IRScalar.bool_ Bool.true",
                "IRScalar.int_ 65",
                "IRScalar.float_ 65",
                "IRScalar.ptr_ 65",
                "IRScalar.nullptr_",
                "IRScalar.fnptr_ 65",
                "IRScalar.aggv IRScalar.vnil",
            ]
            .iter()
            .enumerate()
            {
                equality(
                    &mut spec,
                    &format!("builtin_wrong_carrier_{kind}_{index}"),
                    &decode(&mem, "IRTy.fatstr_", value),
                    NONE,
                );
            }
            for (index, bad_length) in [0, 1, 2, 3, 4, 5, 6, 7, LIMIT - 1, LIMIT]
                .into_iter()
                .filter(|n| *n != length)
                .enumerate()
            {
                equality(
                    &mut spec,
                    &format!("builtin_wrong_length_{kind}_{index}"),
                    &view(&mem, 65, bad_length),
                    NONE,
                );
            }
            for (index, address) in [0, LIMIT - 1, LIMIT].into_iter().enumerate() {
                equality(
                    &mut spec,
                    &format!("builtin_wrong_address_{kind}_{index}"),
                    &view(&mem, address, length),
                    NONE,
                );
            }
        }
    });
}

#[test]
fn byte_builtin_name_requires_one_live_covering_allocation() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let word = WORDS[1].1;
        let bytes = at(65, word);
        let cases = [
            vec![],
            vec![(64, 16, 7, false)],
            vec![(64, 0, 7, true)],
            vec![(64, 6, 7, true)],
            vec![(66, 16, 7, true)],
            vec![(128, 16, 7, true)],
            vec![(64, 4, 7, true), (68, 12, 8, true)],
            vec![(64, 16, 7, true), (64, 16, 8, true)],
            vec![(64, 16, 7, true), (67, 2, 8, false)],
            vec![(64, LIMIT, 7, true)],
        ];
        for (index, rows) in cases.iter().enumerate() {
            equality(
                &mut spec,
                &format!("builtin_bad_allocation_{index}"),
                &view(&memory(rows, &bytes, 1024), 65, 6),
                NONE,
            );
        }
        // Fully initialized bytes do not excuse a noncanonical end address.
        let address = LIMIT - 2;
        equality(
            &mut spec,
            "builtin_past_address_space",
            &view(
                &memory(&[(address, 6, 7, true)], &at(address, word), LIMIT),
                address,
                6,
            ),
            NONE,
        );
    });
}

#[test]
fn byte_builtin_name_ignores_disjoint_bytes_owners_and_allocation_cursor() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (kind, (atom, word)) in WORDS.iter().enumerate() {
            let original = memory(&[(64, 16, 7, true)], &at(65, word), 1024);
            let mut changed_bytes = at(65, word);
            changed_bytes.extend([(64, 255), (80, 256), (257, 99)]);
            let changed = memory(
                &[(256, 8, 91, false), (64, 16, 72, true)],
                &changed_bytes,
                4096,
            );
            // Distinct concrete inputs, not a reflexive memory-preservation claim.
            assert_ne!(original, changed);
            for (index, mem) in [original, changed].iter().enumerate() {
                equality(
                    &mut spec,
                    &format!("builtin_disjoint_change_{kind}_{index}"),
                    &view(mem, 65, word.len() as u128),
                    &some(atom),
                );
            }
        }
    });
}

#[test]
fn byte_builtin_name_swapped_atoms_are_semantic_proof_failures() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (index, (_, word)) in WORDS.iter().enumerate() {
            let mem = format!("builtin_swapped_memory_{index}");
            fixture(&mut spec, &mem, word);
            let name = format!("builtin_swapped_atom_{index}");
            let wrong = some(WORDS[1 - index].0);
            let actual = view(&mem, 65, word.len() as u128);
            let source = format!(
                "def {name} : Eq ({RESULT}) ({actual}) ({wrong}) :=
                 Eq.refl ({RESULT}) ({wrong})"
            );
            let error = spec
                .add_recursive_def(&source, "Deliberately false builtin-name decoding")
                .expect_err("Nat and String cannot exchange decoded atoms");
            crate::test_utils::assert_type_mismatch_rejection(&error, &name);
            assert!(spec.get_definition(&name).is_none());
        }
    });
}

#[test]
fn byte_builtin_name_general_input_and_frame_laws_have_inhabited_applications() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (index, (atom, word)) in WORDS.iter().enumerate() {
            let kind = if index == 0 { "nat" } else { "string" };
            let length = word.len();
            for suffix in ["read", "input", "range_frame", "write_frame", "clear_frame"] {
                audit(&mut spec, &format!("ir_byte_builtin_{kind}_{suffix}_v1"));
            }
            let mut address = "data".to_string();
            let mut premises = String::new();
            let mut arguments = String::new();
            for (position, byte) in word.iter().enumerate() {
                premises.push_str(&format!(
                    " (byte{position} : Eq (IROption Nat) (bytes ({address}))
                      (IROption.some Nat {byte}))"
                ));
                arguments.push_str(&format!(" byte{position}"));
                address = format!("Nat.succ ({address})");
            }
            let expected = some(atom);
            add(
                &mut spec,
                &format!(
                    "def builtin_general_input_{kind}
                      (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
                      (next data : Nat) (bounded : Nat.lt data ir_byte_limit_v1)
                      (access : Eq Bool (ir_byte_accessible_v1 allocs data {length} 1)
                        Bool.true) {premises} :
                      Eq ({RESULT}) (ir_byte_builtin_name_atom_v1
                        (IRByteMemoryV1.mk allocs bytes next)
                        IRTy.fatstr_ (IRScalar.fat_ data {length})) ({expected}) :=
                      ir_byte_builtin_{kind}_input_v1 allocs bytes next data bounded access
                        {arguments}"
                ),
            );
            add(
                &mut spec,
                &format!(
                    "def builtin_general_range_{kind}
                      (allocs : IRList IRByteAllocationV1)
                      (left right : Nat -> IROption Nat) (leftNext rightNext data : Nat)
                      (same : forall (offset : Nat), Nat.lt offset {length} ->
                        Eq (IROption Nat) (left (Nat.add data offset))
                          (right (Nat.add data offset))) :
                      Eq ({RESULT}) (ir_byte_builtin_name_atom_v1
                        (IRByteMemoryV1.mk allocs left leftNext)
                        IRTy.fatstr_ (IRScalar.fat_ data {length}))
                        (ir_byte_builtin_name_atom_v1
                          (IRByteMemoryV1.mk allocs right rightNext)
                          IRTy.fatstr_ (IRScalar.fat_ data {length})) :=
                      ir_byte_builtin_{kind}_range_frame_v1
                        allocs left right leftNext rightNext data same"
                ),
            );
            let mem = format!("builtin_law_memory_{kind}");
            fixture(&mut spec, &mem, word);
            let allocs = format!("(ir_byte_mem_allocs_v1 {mem})");
            let bytes = format!("(ir_byte_mem_bytes_v1 {mem})");
            let byte_proofs = word
                .iter()
                .map(|byte| format!(" (Eq.refl (IROption Nat) (IROption.some Nat {byte}))"))
                .collect::<String>();
            let encoded = word
                .iter()
                .rev()
                .fold(0_u64, |tail, byte| u64::from(*byte) + 256 * tail);
            add(
                &mut spec,
                &format!(
                    "def builtin_read_inhabited_{kind} :
                      Eq (IROption Nat) (ir_byte_read_word_v1 {bytes} {length} 65)
                        (IROption.some Nat {encoded}) :=
                      ir_byte_builtin_{kind}_read_v1 {bytes} 65 {byte_proofs}"
                ),
            );
            add(
                &mut spec,
                &format!(
                    "def builtin_input_inhabited_{kind} :
                      Eq ({RESULT}) ({}) ({expected}) :=
                      ir_byte_builtin_{kind}_input_v1 {allocs} {bytes} 1024 65
                        (Nat.le_add_right 66 {}) (Eq.refl Bool Bool.true) {byte_proofs}",
                    view(&mem, 65, length as u128),
                    LIMIT - 66
                ),
            );
            for (side, write_base) in [("left", 16), ("right", 256)] {
                let end = 65 + length;
                let apart = if write_base == 16 {
                    format!(
                        "@Or.inr (Nat.le {end} 16) (Nat.le 24 65)
                          (Nat.le_add_right 24 41)"
                    )
                } else {
                    format!(
                        "@Or.inl (Nat.le {end} 256) (Nat.le 264 65)
                          (Nat.le_add_right {end} {})",
                        256 - end
                    )
                };
                for operation in ["write", "clear"] {
                    let extra = if operation == "write" { "42" } else { "" };
                    let modified = format!(
                        "IRByteMemoryV1.mk {allocs}
                          (ir_byte_{operation}{}_v1 {bytes} {write_base} 8 {extra}) 1024",
                        if operation == "write" { "_word" } else { "" }
                    );
                    add(
                        &mut spec,
                        &format!(
                            "def builtin_{operation}_inhabited_{kind}_{side} :
                              Eq ({RESULT}) ({}) ({expected}) :=
                              ir_byte_builtin_{kind}_{operation}_frame_v1
                                {allocs} {bytes} 1024 65 {write_base} 8 {extra} ({apart})",
                            view(&modified, 65, length as u128)
                        ),
                    );
                }
            }
        }
    });
}
