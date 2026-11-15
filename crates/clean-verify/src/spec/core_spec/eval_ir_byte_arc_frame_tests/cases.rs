// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Inhabited frame, boundary and semantic-control applications. All addresses
//! and valid-cache predicates are explicit synthetic inputs, not Rust ABI facts.

use super::*;

fn frame(alias: bool, address: u128, size: u128) -> String {
    let second = if alias { 16 } else { 32 };
    format!(
        "{} {address} {size} ({}) ({})",
        law(alias, "range_frame", "arc_pair_seed", 41, 7),
        apart(address, size, 16),
        apart(address, size, second)
    )
}

fn sparse(alias: bool, address: u128, size: u128) -> String {
    let apart_function = |counter: u128| {
        format!(
            "fun (base size : Nat) (selected : Nat.le 40 base) =>
  @Or.inr (Nat.le (Nat.add base size) {counter}) (Nat.le (Nat.add {counter} 8) base)
    (@Nat.le_trans (Nat.add {counter} 8) 40 base ({}) selected)",
            le(counter + 8, 40)
        )
    };
    format!(
        "{} (fun (base size : Nat) => Nat.le 40 base)
  ({}) ({}) {address} {size} ({})",
        law(alias, "sparse_frame", "arc_pair_seed", 41, 7),
        apart_function(16),
        apart_function(if alias { 16 } else { 32 }),
        le(40, address)
    )
}

fn cached(alias: bool) -> String {
    format!(
        "{} 77 (fun (word : Nat) => Eq Nat word 77)
  (Eq.refl Nat 77) (Eq.refl (IROption Nat) (IROption.some Nat 77))",
        frame(alias, 80, 8).replacen("range_frame", "cached_word", 1)
    )
}

fn cache_equation(alias: bool, name: &str) -> String {
    format!(
        "def {name} : And (Eq Nat 77 77)
  (Eq (IROption Nat) ({}) (IROption.some Nat 77)) :=\n{}",
        read(alias, "arc_pair_seed", 41, 7, 80, 8),
        cached(alias)
    )
}

#[test]
fn byte_arc_count_pair_sparse_slots_cache_and_undefined_padding_are_framed() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for alias in [false, true] {
            let case = super::super::suffix(alias);
            for (address, size, endpoint) in [
                (48, 8, "IROption.some Nat 1"),
                (56, 8, "IROption.some Nat 144"),
                (64, 8, "IROption.some Nat 200"),
                (72, 8, "IROption.some Nat 3"),
                (80, 8, "IROption.some Nat 77"),
                // Unobserved/padding initialization is never an input premise.
                // This selected padding read happens to be NONE, and stays so.
                (104, 1, "IROption.none Nat"),
            ] {
                let initial = format!(
                    "ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 ({})) {size} {address}",
                    memory("arc_pair_seed", 41, 7)
                );
                let actual = read(alias, "arc_pair_seed", 41, 7, address, size);
                let proof = super::super::trans(
                    OPTION,
                    &actual,
                    &initial,
                    endpoint,
                    &sparse(alias, address, size),
                    &format!("Eq.refl ({OPTION}) ({endpoint})"),
                );
                add(
                    &mut spec,
                    &equation(
                        &format!("arc_pair_{case}_sparse_{address}"),
                        OPTION,
                        &actual,
                        endpoint,
                        &proof,
                    ),
                );
            }
            add(
                &mut spec,
                &cache_equation(alias, &format!("arc_pair_{case}_cache_validity_carried")),
            );
        }
    });
}

fn builtin(alias: bool, text: &str, name: &str) -> String {
    let (seed, length, atom) = match text {
        "nat" => ("arc_pair_seed", 3, "nat_"),
        "string" => ("arc_pair_string_seed", 6, "string_"),
        _ => panic!("fixture text"),
    };
    let ty = "IROption IRBuiltinNameAtomV1";
    let actual = format!(
        "ir_byte_builtin_name_atom_v1
  (ir_byte_fetch_add_memory_v1 ({})) IRTy.fatstr_ (IRScalar.fat_ 96 {length})",
        operation(alias, seed, 41, 7)
    );
    let initial = format!(
        "ir_byte_builtin_name_atom_v1 ({}) IRTy.fatstr_ (IRScalar.fat_ 96 {length})",
        memory(seed, 41, 7)
    );
    let endpoint = format!("IROption.some IRBuiltinNameAtomV1 IRBuiltinNameAtomV1.{atom}");
    let second = if alias { 16 } else { 32 };
    let proof = format!(
        "{} 96 ({}) ({})",
        law(alias, &format!("{text}_frame"), seed, 41, 7),
        apart(96, length, 16),
        apart(96, length, second)
    );
    // Keep the String input proof in the checked byte-witness lane: direct
    // reflected 256 * packed-tail reduction is enormous in external Lean.
    // This is the same input lemma composition checked in the separate R2
    // replay; no decoder result is assumed and the statement is unchanged.
    let initial_observer_proof = if text == "string" {
        let initial_memory = memory(seed, 41, 7);
        let byte_proofs = b"String"
            .iter()
            .map(|byte| format!(" (Eq.refl (IROption Nat) (IROption.some Nat {byte}))"))
            .collect::<String>();
        format!(
            "ir_byte_builtin_string_input_v1 (ir_byte_mem_allocs_v1 ({initial_memory})) \
             (ir_byte_mem_bytes_v1 ({initial_memory})) (ir_byte_mem_next_v1 ({initial_memory})) \
             96 ({}) (Eq.refl Bool Bool.true){byte_proofs}",
            le(97, LIMIT)
        )
    } else {
        format!("Eq.refl ({ty}) ({endpoint})")
    };
    equation(
        name,
        ty,
        &actual,
        &endpoint,
        &super::super::trans(
            ty,
            &actual,
            &initial,
            &endpoint,
            &proof,
            &initial_observer_proof,
        ),
    )
}

#[test]
fn byte_arc_count_pair_both_builtin_atoms_follow_the_actual_observer_frames() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for alias in [false, true] {
            for text in ["nat", "string"] {
                add(
                    &mut spec,
                    &builtin(
                        alias,
                        text,
                        &format!("arc_pair_{}_builtin_{text}", super::super::suffix(alias)),
                    ),
                );
            }
        }
    });
}

#[test]
fn byte_arc_count_pair_clone_bound_allows_equality_and_separately_bounds_alias_second_old() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (name, old) in [("zero_not_live_arc", 0), ("equality", MAX)] {
            add(
                &mut spec,
                &equation(
                    &format!("arc_pair_bound_{name}"),
                    "Bool",
                    &format!("ir_nat_ltb {MAX} {old}"),
                    "Bool.false",
                    &format!("ir_byte_arc_clone_old_guard_v1 {old} ({})", le(old, MAX)),
                ),
            );
        }
        // The alias case n=MAX is NOT qualified: its second old would be MAX+1.
        // n=MAX-1 really reaches second old=MAX and final stored word=MAX+1.
        for (alias, n, m) in [(false, MAX, 7), (true, MAX - 1, 7)] {
            let case = super::super::suffix(alias);
            add(
                &mut spec,
                &equation(
                    &format!("arc_pair_{case}_at_boundary"),
                    RESULT,
                    &operation(alias, "arc_pair_seed", n, m),
                    &expected(alias, "arc_pair_seed", n, m),
                    &law(alias, "", "arc_pair_seed", n, m),
                ),
            );
            let (suffix, address, new) = if alias {
                ("second_new", 16, MAX + 1)
            } else {
                ("first_new", 16, MAX + 1)
            };
            add(
                &mut spec,
                &equation(
                    &format!("arc_pair_{case}_boundary_new"),
                    OPTION,
                    &read(alias, "arc_pair_seed", n, m, address, 8),
                    &format!("IROption.some Nat {new}"),
                    &law(alias, suffix, "arc_pair_seed", n, m),
                ),
            );
        }
        compute(
            &mut spec,
            "arc_pair_above_max_guard_true",
            "Bool",
            &format!("ir_nat_ltb {MAX} {}", MAX + 1),
            "Bool.true",
        );

        // This is ONLY the underlying fetch-add model at an above-MAX old.
        // Rust checks/aborts AFTER that write. No source clone/pair execution,
        // no abort model, and no atomic nonmutation-on-abort claim follows.
        let old = MAX + 1;
        let initial = memory("arc_pair_seed", old, 7);
        let before_second = super::super::written("arc_pair_seed", "32", "7");
        let actual = format!("ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 (ir_byte_fetch_add_memory_v1
  (ir_byte_fetch_add_relaxed_usize_seq_v1 64 arc_pair_ctx (IRScalar.ptr_ 16) (IRScalar.int_ 1) ({initial})))) 8 16");
        let proof = format!(
            "ir_byte_fetch_add_relaxed_usize64_seq_new_v1 arc_pair_ctx ({initial}) 16 {old} 1
  ({}) (Eq.refl (IROption IRByteLayoutV1) (IROption.some IRByteLayoutV1 ({})))
  (Eq.refl Bool Bool.true) (ir_byte_usize64_rep_write_v1 ({before_second}) 16 {old}) ({})",
            le(17, LIMIT),
            super::super::LAYOUT,
            le(old + 2, LIMIT)
        );
        add(
            &mut spec,
            &equation(
                "arc_pair_above_max_single_model_still_writes",
                OPTION,
                &actual,
                &format!("IROption.some Nat {}", old + 1),
                &proof,
            ),
        );
    });
}

#[test]
fn byte_arc_count_pair_faults_preserve_exact_first_or_intermediate_memory() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let initial = super::super::written("arc_pair_seed", "16", "41");
        let after_first = super::super::written(&initial, "16", "42");
        for (name, memory, second, outcome, endpoint_memory) in [
            (
                "first_uninit",
                "arc_pair_seed".to_owned(),
                32,
                "IROutcome.ub IRFault.uninit",
                "arc_pair_seed".to_owned(),
            ),
            (
                "second_uninit",
                initial.clone(),
                32,
                "IROutcome.ub IRFault.uninit",
                after_first.clone(),
            ),
            (
                "second_misaligned",
                initial.clone(),
                33,
                "IROutcome.ub IRFault.bad_addr",
                after_first.clone(),
            ),
            (
                "first_retired",
                format!("ir_byte_retire_v1 7 ({initial})"),
                32,
                "IROutcome.ub IRFault.bad_addr",
                format!("ir_byte_retire_v1 7 ({initial})"),
            ),
        ] {
            let operation =
                format!("ir_byte_arc_count_pair_seq_v1 arc_pair_ctx ({memory}) 16 {second}");
            compute(
                &mut spec,
                &format!("arc_pair_fault_{name}"),
                RESULT,
                &operation,
                &format!("{RESULT}.fault ({outcome}) ({endpoint_memory})"),
            );
            compute(
                &mut spec,
                &format!("arc_pair_fault_{name}_old_none"),
                "IROption IRScalar",
                &format!("ir_byte_arc_count_pair_old_at_v1 ({operation}) 0"),
                "IROption.none IRScalar",
            );
        }
        let u64_context = "IRByteContextV1.mk (IRModule.mk (IRList.nil IRFunc) (IRList.nil IRGlobal))
  (IRList.cons IRByteLayoutV1 (IRByteLayoutV1.mk (IRTy.uint_ 64) 8 8 (IRList.nil IRTy) (IRList.nil Nat)) (IRList.nil IRByteLayoutV1))
  (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1) (IRList.nil IRByteSiteV1)";
        let memory = memory("arc_pair_seed", 41, 7);
        compute(
            &mut spec,
            "arc_pair_wrong_nominal_layout_refuses",
            RESULT,
            &format!("ir_byte_arc_count_pair_seq_v1 ({u64_context}) ({memory}) 16 32"),
            &format!("{RESULT}.fault (IROutcome.unmodelled IRFault.width_bounded) ({memory})"),
        );
    });
}

#[test]
fn byte_arc_count_pair_wrong_conclusions_fail_with_unchanged_proofs() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (alias, from, to) in [
            (false, "IRScalar.int_ (7)", "IRScalar.int_ (8)"),
            (true, "IRScalar.int_ (42)", "IRScalar.int_ (41)"),
        ] {
            let case = super::super::suffix(alias);
            let source = equation(
                &format!("arc_pair_control_{case}_positive"),
                RESULT,
                &operation(alias, "arc_pair_seed", 41, 7),
                &expected(alias, "arc_pair_seed", 41, 7),
                &law(alias, "", "arc_pair_seed", 41, 7),
            );
            conclusion_control(
                &mut spec,
                &source,
                &format!("arc_pair_control_{case}_wrong_old"),
                from,
                to,
            );
        }
        for (alias, correct, stale) in [(false, 42, 41), (true, 43, 42)] {
            let case = super::super::suffix(alias);
            let source = equation(
                &format!("arc_pair_control_{case}_new_positive"),
                OPTION,
                &read(alias, "arc_pair_seed", 41, 7, 16, 8),
                &format!("IROption.some Nat {correct}"),
                &law(alias, "first_new", "arc_pair_seed", 41, 7),
            );
            conclusion_control(
                &mut spec,
                &source,
                &format!("arc_pair_control_{case}_stale_new"),
                &format!("IROption.some Nat {correct}"),
                &format!("IROption.some Nat {stale}"),
            );
        }
        let cache = cache_equation(false, "arc_pair_control_cache_positive");
        conclusion_control(
            &mut spec,
            &cache,
            "arc_pair_control_cache_changed",
            "IROption.some Nat 77",
            "IROption.some Nat 78",
        );
        let atom = builtin(false, "nat", "arc_pair_control_atom_positive");
        conclusion_control(
            &mut spec,
            &atom,
            "arc_pair_control_atom_changed",
            "IROption.some IRBuiltinNameAtomV1 IRBuiltinNameAtomV1.nat_",
            "IROption.some IRBuiltinNameAtomV1 IRBuiltinNameAtomV1.string_",
        );

        let initial = super::super::written("arc_pair_seed", "16", "41");
        let after_first = super::super::written(&initial, "16", "42");
        let actual = format!("ir_byte_arc_count_pair_seq_v1 arc_pair_ctx ({initial}) 16 32");
        let endpoint = format!("{RESULT}.fault (IROutcome.ub IRFault.uninit) ({after_first})");
        let source = equation(
            "arc_pair_control_second_fault_positive",
            RESULT,
            &actual,
            &endpoint,
            &format!("Eq.refl ({RESULT}) ({endpoint})"),
        );
        conclusion_control(
            &mut spec,
            &source,
            "arc_pair_control_fault_rollback",
            &endpoint,
            &format!("{RESULT}.fault (IROutcome.ub IRFault.uninit) ({initial})"),
        );
    });
}
