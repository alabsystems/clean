// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Synthetic MODEL applications, not captured Rust layouts or live Arc/Name.
//! Counter addresses 16/32 and sparse slots 48..104 are intentionally fixture
//! descriptors. Nothing authenticates these as production offsets or tags.
//! In particular count zero remains a mathematical fetch-add input, not Arc.

use crate::spec::Specification;
use clean_kernel::Name;

#[path = "eval_ir_byte_arc_frame_tests/cases.rs"]
mod cases;

const MAX: u128 = (1_u128 << 63) - 1;
const LIMIT: u128 = 1_u128 << 64;
const RESULT: &str = "IRByteMemoryResultV1";
const OPTION: &str = "IROption Nat";

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
    spec.add_recursive_def(source, "Two-counter sparse-frame MODEL application")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
    audit(spec, source.split_whitespace().nth(1).unwrap());
}

fn equation(name: &str, ty: &str, actual: &str, expected: &str, proof: &str) -> String {
    format!("def {name} : Eq ({ty}) ({actual}) ({expected}) :=\n{proof}")
}

fn compute(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
    add(
        spec,
        &equation(
            name,
            ty,
            actual,
            expected,
            &format!("Eq.refl ({ty}) ({expected})"),
        ),
    );
}

fn conclusion_control(spec: &mut Specification, positive: &str, name: &str, from: &str, to: &str) {
    // Qualify the exact positive first. Alter only its conclusion/name, never
    // its proof or premises. A parser/resource refusal cannot count as success.
    add(spec, positive);
    let (header, proof) = positive
        .split_once(":=")
        .expect("declaration proof separator");
    assert_eq!(
        header.matches(from).count(),
        1,
        "unique intended conclusion"
    );
    let original_name = positive.split_whitespace().nth(1).unwrap();
    let changed_header = header
        .replacen(original_name, name, 1)
        .replacen(from, to, 1);
    let negative = format!("{changed_header}:={proof}");
    assert_eq!(negative.split_once(":=").unwrap().1, proof);
    let error = spec
        .add_recursive_def(
            &negative,
            "Conclusion-only unchanged-proof semantic control",
        )
        .expect_err("wrong conclusion must not check");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn specification() -> Specification {
    let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .expect("public ByteV1 constructor including pair-frame registration");
    // No conditional rescue registration: this test requires the PUBLIC
    // constructor to install the new module once the parent integrates it.
    audit(&spec, "ir_byte_arc_count_pair_distinct_v1");
    for source in [
        format!("def arc_pair_ctx : IRByteContextV1 :=\nIRByteContextV1.mk (IRModule.mk (IRList.nil IRFunc) (IRList.nil IRGlobal))\n  (IRList.cons IRByteLayoutV1 ({}) (IRList.nil IRByteLayoutV1))\n  (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1) (IRList.nil IRByteSiteV1)", super::LAYOUT),
        "def arc_pair_allocs : IRList IRByteAllocationV1 := IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 160 7 Bool.true) (IRList.nil IRByteAllocationV1)".to_owned(),
        "def arc_pair_blank : Nat -> IROption Nat := fun (_ : Nat) => IROption.none Nat".to_owned(),
        "def arc_pair_empty : IRByteMemoryV1 := IRByteMemoryV1.mk arc_pair_allocs arc_pair_blank 512".to_owned(),
        format!("def arc_pair_seed : IRByteMemoryV1 := {}", seed(b"Nat")),
        format!("def arc_pair_string_seed : IRByteMemoryV1 := {}", seed(b"String")),
        format!("def arc_pair_memory (seed : IRByteMemoryV1) (n m : Nat) : IRByteMemoryV1 := {}",
            super::written(&super::written("seed", "32", "m"), "16", "n")),
    ] {
        add(&mut spec, &source);
    }
    spec
}

fn seed(text: &[u8]) -> String {
    // Synthetic observed tag/pointer/length/cache words, NOT representation
    // validity for Name. Address104 stays undef: no wholeheap initialization.
    let mut bytes = "arc_pair_blank".to_owned();
    for (address, word) in [
        (48, 1),
        (56, 144),
        (64, 200),
        (72, text.len() as u64),
        (80, 77),
    ] {
        bytes = format!("ir_byte_write_word_v1 ({bytes}) {address} 8 {word}");
    }
    for (index, byte) in text.iter().enumerate() {
        bytes = format!("ir_byte_write_word_v1 ({bytes}) {} 1 {byte}", 96 + index);
    }
    format!("IRByteMemoryV1.mk arc_pair_allocs ({bytes}) 512")
}

fn memory(seed: &str, n: u128, m: u128) -> String {
    format!("arc_pair_memory {seed} {n} {m}")
}

fn operation(alias: bool, seed: &str, n: u128, m: u128) -> String {
    let second = if alias { 16 } else { 32 };
    format!(
        "ir_byte_arc_count_pair_seq_v1 arc_pair_ctx ({}) 16 {second}",
        memory(seed, n, m)
    )
}

fn expected(alias: bool, seed: &str, n: u128, m: u128) -> String {
    let initial = memory(seed, n, m);
    let first = super::written(&initial, "16", &(n + 1).to_string());
    let (address, old) = if alias { (16, n + 1) } else { (32, m) };
    let final_memory = super::written(&first, &address.to_string(), &(old + 1).to_string());
    format!(
        "{RESULT}.value ({}) ({final_memory})",
        super::pair(&n.to_string(), &old.to_string())
    )
}

fn le(a: u128, b: u128) -> String {
    assert!(a <= b);
    format!("Nat.le_add_right {a} {}", b - a)
}

fn apart(read: u128, size: u128, write: u128) -> String {
    let left = format!("Nat.le (Nat.add {read} {size}) {write}");
    let right = format!("Nat.le (Nat.add {write} 8) {read}");
    if read + size <= write {
        format!("@Or.inl ({left}) ({right}) ({})", le(read + size, write))
    } else {
        assert!(write + 8 <= read);
        format!("@Or.inr ({left}) ({right}) ({})", le(write + 8, read))
    }
}

fn arguments(alias: bool, seed: &str, n: u128, m: u128) -> String {
    let initial = memory(seed, n, m);
    let with_second = super::written(seed, "32", &m.to_string());
    let layout = format!(
        "Eq.refl (IROption IRByteLayoutV1) (IROption.some IRByteLayoutV1 ({}))",
        super::LAYOUT
    );
    let common = format!("arc_pair_ctx ({initial}) 16 {n} ({}) ({layout})\n  (Eq.refl Bool Bool.true) (ir_byte_usize64_rep_write_v1 ({with_second}) 16 {n})", le(17, LIMIT));
    if alias {
        format!("{common} ({})", le(n + 1, MAX))
    } else {
        let disjoint = apart(32, 8, 16);
        format!("{common} 32 {m} ({}) (Eq.refl Bool Bool.true)\n  (ir_byte_usize64_rep_disjoint_write_v1 ({with_second}) 32 16 {n} {m}\n    ({disjoint}) (ir_byte_usize64_rep_write_v1 {seed} 32 {m}))\n  ({}) ({}) ({disjoint})", le(33, LIMIT), le(n, MAX), le(m, MAX))
    }
}

fn law(alias: bool, suffix: &str, seed: &str, n: u128, m: u128) -> String {
    let case = super::suffix(alias);
    let middle = if suffix.is_empty() {
        String::new()
    } else {
        format!("_{suffix}")
    };
    format!(
        "ir_byte_arc_count_pair_{case}{middle}_v1 {}",
        arguments(alias, seed, n, m)
    )
}

fn read(alias: bool, seed: &str, n: u128, m: u128, address: u128, size: u128) -> String {
    format!("ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 (ir_byte_fetch_add_memory_v1 ({}))) {size} {address}", operation(alias, seed, n, m))
}

#[test]
fn byte_arc_count_pair_registered_laws_have_empty_closures() {
    crate::test_utils::run_with_stack(|| {
        let spec = specification();
        let declarations = super::declarations();
        assert_eq!(declarations.len(), 32);
        let mut names = std::collections::BTreeSet::new();
        for (name, _) in declarations {
            assert!(names.insert(name.clone()), "unique declaration {name}");
            audit(&spec, &name);
        }
    });
}

fn execution_observations(alias: bool) {
    let mut spec = specification();
    let case = super::suffix(alias);
    let (n, m) = (41, 7);
    let seed = "arc_pair_seed";
    add(
        &mut spec,
        &equation(
            &format!("arc_pair_{case}_execution"),
            RESULT,
            &operation(alias, seed, n, m),
            &expected(alias, seed, n, m),
            &law(alias, "", seed, n, m),
        ),
    );
    for (suffix, index, old) in [
        ("first_old", 0, n),
        ("second_old", 1, if alias { n + 1 } else { m }),
    ] {
        add(
            &mut spec,
            &equation(
                &format!("arc_pair_{case}_{suffix}"),
                "IROption IRScalar",
                &format!(
                    "ir_byte_arc_count_pair_old_at_v1 ({}) {index}",
                    operation(alias, seed, n, m)
                ),
                &format!("IROption.some IRScalar (IRScalar.int_ {old})"),
                &law(alias, suffix, seed, n, m),
            ),
        );
    }
    for (suffix, address, new) in [
        ("first_new", 16, if alias { n + 2 } else { n + 1 }),
        (
            "second_new",
            if alias { 16 } else { 32 },
            if alias { n + 2 } else { m + 1 },
        ),
    ] {
        add(
            &mut spec,
            &equation(
                &format!("arc_pair_{case}_{suffix}"),
                OPTION,
                &read(alias, seed, n, m, address, 8),
                &format!("IROption.some Nat {new}"),
                &law(alias, suffix, seed, n, m),
            ),
        );
    }
    for (suffix, ty, accessor, endpoint) in [
        (
            "allocations",
            "IRList IRByteAllocationV1",
            "ir_byte_mem_allocs_v1",
            "arc_pair_allocs",
        ),
        ("cursor", "Nat", "ir_byte_mem_next_v1", "512"),
    ] {
        add(
            &mut spec,
            &equation(
                &format!("arc_pair_{case}_{suffix}"),
                ty,
                &format!(
                    "{accessor} (ir_byte_fetch_add_memory_v1 ({}))",
                    operation(alias, seed, n, m)
                ),
                endpoint,
                &law(alias, suffix, seed, n, m),
            ),
        );
    }
}

#[test]
fn byte_arc_count_pair_distinct_derives_both_updates_and_exact_old_observations() {
    crate::test_utils::run_with_stack(|| execution_observations(false));
}

#[test]
fn byte_arc_count_pair_alias_derives_second_old_and_final_plus_two() {
    crate::test_utils::run_with_stack(|| execution_observations(true));
}
