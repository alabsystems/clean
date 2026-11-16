// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Synthetic heap witnesses for conditional representation elimination only.
//! The offsets below deliberately vary. They are NOT Rust ABI facts, compiler
//! layout captures, Arc provenance evidence, or Name tag/parent/hash evidence.

use crate::spec::Specification;
use clean_kernel::Name;

const LIMIT: u128 = 1_u128 << 64;
const NONE: &str = "@IROption.none IRBuiltinNameAtomV1";
const ROOTS: [&str; 8] = [
    "ir_byte_arc_tail_pointer_load_v1",
    "ir_byte_arc_tail_length_load_v1",
    "ir_byte_arc_tail_gep_v1",
    "ir_byte_arc_tail_project_v1",
    "ir_byte_arc_tail_project_input_v1",
    "ir_byte_arc_tail_observe_v1",
    "ir_byte_arc_tail_nat_input_v1",
    "ir_byte_arc_tail_string_input_v1",
];

fn audit(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).expect("registered definition");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(name)
        .expect("independent kernel check");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Conditional Arc-tail byte-model regression")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
    audit(spec, source.split_whitespace().nth(1).unwrap());
}

fn equality(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
    add(
        spec,
        &format!("def {name} : @Eq ({ty}) ({actual}) ({expected}) := @Eq.refl ({ty}) ({expected})"),
    );
}

fn reject(spec: &mut Specification, source: &str) {
    let name = source.split_whitespace().nth(1).unwrap();
    let error = spec
        .add_recursive_def(source, "Type-only false Arc-tail endpoint")
        .expect_err("unchanged proof must not establish the mutated conclusion");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn context(pointer: bool, metadata_ty: &str) -> String {
    let mut rows = vec![super::layout(metadata_ty, 8), super::layout(super::U8, 1)];
    if pointer {
        rows.push(super::layout("IRTy.ptr_", 8));
    }
    let layouts = rows
        .iter()
        .rev()
        .fold("@IRList.nil IRByteLayoutV1".to_owned(), |tail, row| {
            format!("@IRList.cons IRByteLayoutV1 ({row}) ({tail})")
        });
    format!("IRByteContextV1.mk (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal))
  ({layouts}) (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1) (@IRList.nil IRByteSiteV1)")
}

fn specification() -> Specification {
    let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .expect("public ByteV1 registration, including Arc-tail laws");
    add(
        &mut spec,
        &format!(
            "def arc_tail_test_ctx : IRByteContextV1 := {}",
            context(true, super::U64)
        ),
    );
    spec
}

fn allocations(rows: &[(u128, u128, bool)]) -> String {
    rows.iter().enumerate().rev().fold("@IRList.nil IRByteAllocationV1".to_owned(), |tail, (owner, (base, size, live))| {
        let live = if *live { "Bool.true" } else { "Bool.false" };
        format!("@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk {base} {size} {owner} {live}) ({tail})")
    })
}

fn byte_map(bytes: &[(u128, u16)]) -> String {
    let body = bytes.iter().rev().fold("@IROption.none Nat".to_owned(), |tail, (address, byte)| {
        format!("@Bool.rec (fun (_ : Bool) => IROption Nat) ({tail}) (@IROption.some Nat {byte}) (ir_nat_eqb address {address})")
    });
    format!("fun (address : Nat) => {body}")
}

fn memory(rows: &[(u128, u128, bool)], bytes: &[(u128, u16)]) -> String {
    format!(
        "IRByteMemoryV1.mk ({}) ({}) 1024",
        allocations(rows),
        byte_map(bytes)
    )
}

fn word_at(bytes: &mut Vec<(u128, u16)>, address: u128, word: u64) {
    bytes.extend(
        word.to_le_bytes()
            .iter()
            .enumerate()
            .map(|(i, byte)| (address + i as u128, u16::from(*byte))),
    );
}

fn storage(
    pointer_offset: u128,
    metadata_offset: u128,
    data_offset: u128,
    text: &[u8],
) -> Vec<(u128, u16)> {
    let mut bytes = Vec::new();
    word_at(&mut bytes, 64 + pointer_offset, 256);
    word_at(&mut bytes, 64 + metadata_offset, text.len() as u64);
    bytes.extend(
        text.iter()
            .enumerate()
            .map(|(i, byte)| (256 + data_offset + i as u128, u16::from(*byte))),
    );
    bytes
}

fn observe(
    ctx: &str,
    mem: &str,
    pointer_offset: u128,
    metadata_offset: u128,
    data_offset: u128,
) -> String {
    format!("ir_byte_arc_tail_observe_v1 ({ctx}) ({mem}) 64 {pointer_offset} {metadata_offset} {data_offset}")
}

fn atom(name: &str) -> String {
    format!("@IROption.some IRBuiltinNameAtomV1 IRBuiltinNameAtomV1.{name}_")
}

#[test]
fn arc_tail_public_input_laws_have_checked_empty_closures() {
    crate::test_utils::run_with_stack(|| {
        let spec = specification();
        for root in ROOTS {
            audit(&spec, root);
        }
    });
}

#[test]
fn arc_tail_distinct_field_orders_and_data_offsets_reach_exact_atoms() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        // Both arrangements are model witnesses, NOT an asserted Rust field order.
        for (layout, (pointer, metadata, offset)) in
            [(0, 8, 5), (16, 0, 11)].into_iter().enumerate()
        {
            for (kind, bytes) in [("nat", b"Nat".as_slice()), ("string", b"String".as_slice())] {
                let mem = format!("arc_tail_exact_{layout}_{kind}_memory");
                add(
                    &mut spec,
                    &format!(
                        "def {mem} : IRByteMemoryV1 := {}",
                        memory(
                            &[(64, 32, true), (256, 40, true)],
                            &storage(pointer, metadata, offset, bytes)
                        )
                    ),
                );
                equality(
                    &mut spec,
                    &format!("arc_tail_exact_{layout}_{kind}"),
                    super::OPTION,
                    &observe("arc_tail_test_ctx", &mem, pointer, metadata, offset),
                    &atom(kind),
                );
                equality(&mut spec, &format!("arc_tail_projected_{layout}_{kind}"), super::STEP,
                    &format!("ir_byte_arc_tail_project_v1 arc_tail_test_ctx {mem} 64 {pointer} {metadata} {offset}"),
                    &format!("IRStepResult.value (IRScalar.fat_ {} {})", 256 + offset, bytes.len()));
                equality(&mut spec, &format!("arc_tail_header_load_{layout}_{kind}"), super::MEMORY_RESULT,
                    &format!("ir_byte_load_v1 arc_tail_test_ctx IRTy.ptr_ (IRScalar.ptr_ {}) 8 Bool.false {mem}", 64 + pointer),
                    &format!("IRByteMemoryResultV1.value (IRScalar.ptr_ 256) {mem}"));
                equality(&mut spec, &format!("arc_tail_container_is_not_str_{layout}_{kind}"), super::OPTION,
                    &format!("ir_byte_builtin_name_atom_v1 {mem} IRTy.containerlen_ (IRScalar.fat_ {} {})", 256 + offset, bytes.len()), NONE);
            }
        }
    });
}

#[test]
fn arc_tail_raw_slot_corruption_and_missing_layouts_are_refused() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (index, (address, replacement)) in [
            (64, None),
            (72, None),
            (64, Some(256)),
            (72, Some(256)),
            (72, Some(4)),
            (64, Some(1)),
        ]
        .into_iter()
        .enumerate()
        {
            let mut bytes = storage(0, 8, 5, b"Nat");
            bytes.retain(|(at, _)| *at != address);
            if let Some(byte) = replacement {
                bytes.push((address, byte));
            }
            equality(
                &mut spec,
                &format!("arc_tail_bad_slot_{index}"),
                super::OPTION,
                &observe(
                    "arc_tail_test_ctx",
                    &memory(&[(64, 32, true), (256, 40, true)], &bytes),
                    0,
                    8,
                    5,
                ),
                NONE,
            );
        }
        let mem = memory(
            &[(64, 32, true), (256, 40, true)],
            &storage(0, 8, 5, b"Nat"),
        );
        for (index, ctx) in [context(false, super::U64), context(true, "IRTy.usize_ 64")]
            .into_iter()
            .enumerate()
        {
            equality(
                &mut spec,
                &format!("arc_tail_missing_layout_{index}"),
                super::OPTION,
                &observe(&ctx, &mem, 0, 8, 5),
                NONE,
            );
        }
        for (index, (pointer, metadata)) in
            [(8, 0), (1, 8), (0, 9), (32, 8)].into_iter().enumerate()
        {
            equality(
                &mut spec,
                &format!("arc_tail_wrong_field_{index}"),
                super::OPTION,
                &observe("arc_tail_test_ctx", &mem, pointer, metadata, 5),
                NONE,
            );
        }
        // Check the operation fault, not merely the observer's erased None.
        let mut incomplete = storage(0, 8, 5, b"Nat");
        incomplete.retain(|(address, _)| *address != 72);
        let missing_metadata = memory(&[(64, 32, true), (256, 40, true)], &incomplete);
        for (name, actual, outcome) in [
            (
                "arc_tail_missing_metadata_is_uninit",
                format!(
                    "ir_byte_arc_tail_project_v1 arc_tail_test_ctx ({missing_metadata}) 64 0 8 5"
                ),
                "IROutcome.ub IRFault.uninit",
            ),
            (
                "arc_tail_misalignment_is_bad_addr",
                format!("ir_byte_arc_tail_project_v1 arc_tail_test_ctx ({mem}) 64 1 8 5"),
                "IROutcome.ub IRFault.bad_addr",
            ),
            (
                "arc_tail_missing_layout_is_unmodelled",
                format!(
                    "ir_byte_arc_tail_project_v1 ({}) ({mem}) 64 0 8 5",
                    context(false, super::U64)
                ),
                "IROutcome.unmodelled IRFault.width_bounded",
            ),
        ] {
            equality(
                &mut spec,
                name,
                super::STEP,
                &actual,
                &format!("IRStepResult.fault ({outcome})"),
            );
        }
    });
}

#[test]
fn arc_tail_requires_live_unique_inbounds_tail_and_exact_tail_bytes() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let bytes = storage(0, 8, 5, b"Nat");
        for (index, rows) in [
            vec![(64, 32, false), (256, 40, true)],
            vec![(64, 32, true), (256, 40, false)],
            vec![(64, 32, true), (256, 40, true), (256, 40, true)],
            vec![(64, 32, true), (256, 6, true)],
            vec![(64, 32, true), (261, 8, true)],
        ]
        .iter()
        .enumerate()
        {
            equality(
                &mut spec,
                &format!("arc_tail_bad_allocation_{index}"),
                super::OPTION,
                &observe("arc_tail_test_ctx", &memory(rows, &bytes), 0, 8, 5),
                NONE,
            );
        }
        let mem = memory(&[(64, 32, true), (256, 40, true)], &bytes);
        for (index, offset) in [0, 4, 6, 40, 1_u128 << 63, LIMIT - 1, LIMIT]
            .into_iter()
            .enumerate()
        {
            equality(
                &mut spec,
                &format!("arc_tail_bad_data_offset_{index}"),
                super::OPTION,
                &observe("arc_tail_test_ctx", &mem, 0, 8, offset),
                NONE,
            );
        }
        // Correct bytes at the allocation header cannot justify an offset tail.
        let wrong_place = memory(
            &[(64, 32, true), (256, 40, true)],
            &storage(0, 8, 0, b"Nat"),
        );
        equality(
            &mut spec,
            "arc_tail_header_bytes_are_not_tail_bytes",
            super::OPTION,
            &observe("arc_tail_test_ctx", &wrong_place, 0, 8, 5),
            NONE,
        );
    });
}

fn numeric_bound(n: u128, limit: u128) -> String {
    format!("Nat.le_add_right {} {}", n + 1, limit - n - 1)
}

#[test]
fn arc_tail_input_theorem_has_a_constructed_raw_storage_witness() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        add(
            &mut spec,
            &format!(
                "def arc_tail_witness_allocs : IRList IRByteAllocationV1 := {}",
                allocations(&[(64, 32, true), (256, 40, true)])
            ),
        );
        // Both are synthetic storage witnesses, not compiler layout evidence.
        // Apply each public input theorem; no projected-result premise is used.
        for (kind, text) in [("nat", b"Nat".as_slice()), ("string", b"String".as_slice())] {
            let length = text.len() as u128;
            let prefix = format!("arc_tail_witness_{kind}");
            let bytes = text
                .iter()
                .enumerate()
                .map(|(i, byte)| (261 + i as u128, u16::from(*byte)))
                .collect::<Vec<_>>();
            add(
                &mut spec,
                &format!(
                    "def {prefix}_bytes : Nat -> IROption Nat := {}",
                    byte_map(&bytes)
                ),
            );
            add(
                &mut spec,
                &format!(
                    "def {prefix}_memory : IRByteMemoryV1 :=
IRByteMemoryV1.mk arc_tail_witness_allocs
  (ir_byte_write_word_v1 (ir_byte_write_word_v1 {prefix}_bytes 72 8 {length}) 64 8 256) 1024"
                ),
            );
            add(
                &mut spec,
                &format!(
                    "def {prefix}_pointer_rep : ir_byte_u64_rep_v1 {prefix}_memory 64 256 :=
ir_byte_u64_rep_write_v1 (IRByteMemoryV1.mk arc_tail_witness_allocs
  (ir_byte_write_word_v1 {prefix}_bytes 72 8 {length}) 1024) 64 256"
                ),
            );
            add(
                &mut spec,
                &format!("def {prefix}_length_rep : ir_byte_u64_rep_v1 {prefix}_memory 72 {length} :=
fun (i : Nat) (inside : Nat.lt i 8) =>
  @Eq.trans (IROption Nat)
    (ir_byte_mem_bytes_v1 {prefix}_memory (Nat.add 72 i))
    (ir_byte_write_word_v1 {prefix}_bytes 72 8 {length} (Nat.add 72 i))
    (@IROption.some Nat (Nat.mod (Nat.div {length} (ir_nat_pow2 (Nat.mul 8 i))) 256))
    (ir_byte_write_outside_v1 (ir_byte_write_word_v1 {prefix}_bytes 72 8 {length}) 64 8 256 (Nat.add 72 i)
      (ir_byte_range_after_v1 64 8 (Nat.add 72 i) (Nat.le_add_right 72 i)))
    (ir_byte_write_digit_v1 {prefix}_bytes 72 8 {length} i inside)"),
            );
            let bounds = [
                (64, LIMIT),
                (72, LIMIT),
                (256, LIMIT),
                (length, LIMIT),
                (5, 1_u128 << 63),
                (5, LIMIT),
                (261, LIMIT),
            ]
            .iter()
            .map(|(n, limit)| format!("\n  ({})", numeric_bound(*n, *limit)))
            .collect::<String>();
            let layouts = [("IRTy.ptr_", 8), (super::U64, 8), (super::U8, 1)]
                .iter()
                .map(|(ty, size)| {
                    format!(
                        "\n  (@Eq.refl (IROption IRByteLayoutV1) (@IROption.some IRByteLayoutV1 ({})))",
                        super::layout(ty, *size)
                    )
                })
                .collect::<String>();
            let byte_proofs = text
                .iter()
                .map(|byte| format!("\n  (@Eq.refl (IROption Nat) (@IROption.some Nat {byte}))"))
                .collect::<String>();
            add(
                &mut spec,
                &format!(
                    "def {prefix} : @Eq ({})
  (ir_byte_arc_tail_observe_v1 arc_tail_test_ctx {prefix}_memory 64 0 8 5) ({}) :=
ir_byte_arc_tail_{kind}_input_v1 arc_tail_test_ctx {prefix}_memory 64 0 8 255 5
  {bounds} {layouts}
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  {prefix}_pointer_rep {prefix}_length_rep
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  {byte_proofs}",
                    super::OPTION,
                    atom(kind)
                ),
            );
        }
    });
}

#[test]
fn arc_tail_unchanged_proofs_reject_header_as_tail_and_wrong_atom() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let project = super::project_source();
        let (head, body) = project.split_once(" :=").expect("generated definition");
        let correct = format!("IRScalar.fat_ ({}) length", super::TAIL);
        assert_eq!(head.matches(&correct).count(), 1);
        let bad_head = head
            .replace(
                "ir_byte_arc_tail_project_input_v1",
                "arc_tail_bad_header_endpoint",
            )
            .replace(
                &correct,
                &format!("IRScalar.fat_ ({}) length", super::HEADER),
            );
        reject(&mut spec, &format!("{bad_head} :={body}"));
        let observed = super::observer_source("nat", b"Nat");
        let (head, body) = observed.split_once(" :=").expect("generated definition");
        assert_eq!(head.matches("IRBuiltinNameAtomV1.nat_").count(), 1);
        let bad_head = head
            .replace(
                "ir_byte_arc_tail_nat_input_v1",
                "arc_tail_bad_atom_endpoint",
            )
            .replace("IRBuiltinNameAtomV1.nat_", "IRBuiltinNameAtomV1.string_");
        reject(&mut spec, &format!("{bad_head} :={body}"));
    });
}
