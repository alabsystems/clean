// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ByteV1's census (crystal link 4, D20; `designs/2026-10-01-evalir-bytev1-memory.md`).
//!
//! S1a: the ladder trie with full-key buckets and the Nat-keyed function fetch. Every
//! declaration registers in the EvalIr BUNDLE as a kernel-checked definition with an EMPTY
//! axiom closure, and the fetch law states what the device relies on: a fetch through the
//! function trie IS `ir_func_find`, the list walk `ir_step` performs.

use clean_kernel::name::Name;
use clean_verify::spec::{ProofStatus, Specification};
use clean_verify::test_utils::build_eval_ir_spec_with_stack;

fn assert_kernel_checked_axiom_free(spec: &Specification, names: &[&str]) {
    for name in names {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("{name} must be registered"));
        if def.elaborated_value.is_none() {
            // An inductive registers its type, not a value; its recursor carries the content.
            continue;
        }
        assert!(
            !def.is_axiom && def.value_src.is_some(),
            "{name} must carry a checked value, not be an axiom"
        );
        assert_ne!(def.proof_status, ProofStatus::Axiom, "{name}");
        spec.verify_definition(name)
            .unwrap_or_else(|e| panic!("{name} must re-check against its declared type: {e:?}"));
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY axiom closure. Found: {deps:?}"
        );
    }
}

#[test]
fn the_nat_keyed_store_and_function_fetch_register_axiom_free() {
    let spec = build_eval_ir_spec_with_stack();
    let names = clean_verify::spec::BMEM_TRIE_NAMES;
    assert_eq!(names.len(), 21, "the S1a library");
    assert_kernel_checked_axiom_free(&spec, names);
    let ty = |name: &str| -> String {
        spec.definitions()
            .get(name)
            .map(|d| d.type_src.split(" := ").next().unwrap_or("").to_string())
            .unwrap_or_default()
    };
    // The fetch law relates the trie to the step's own fetch, not to a copy of it.
    let fetch = ty("ir_func_trie_find");
    assert!(
        fetch.contains("(ir_func_tfind (ir_func_trie fs) k)")
            && fetch.contains("(ir_func_find fs k)"),
        "ir_func_trie_find must equate the trie fetch with ir_func_find: {fetch}"
    );
    // The client rewrite is the Bool.rec form, quantified over every trie and both keys.
    let law = ty("ir_bt_get_set");
    assert!(
        law.contains("(t : (IRBmTrie A))") && law.contains("(ir_nat_eqb k1 k2)"),
        "ir_bt_get_set must quantify the trie and branch on the key comparison: {law}"
    );
}

#[test]
fn the_byte_memory_core_registers_axiom_free() {
    let spec = build_eval_ir_spec_with_stack();
    let names = clean_verify::spec::BMEM_CORE_NAMES;
    assert_eq!(
        names.len(),
        153,
        "ByteV1 core plus the explicit Release refusal law"
    );
    assert_kernel_checked_axiom_free(&spec, names);
    let ty = |name: &str| -> String {
        spec.definitions()
            .get(name)
            .map(|d| d.type_src.split(" := ").next().unwrap_or("").to_string())
            .unwrap_or_default()
    };
    // The refinement's load arm relates the CELL machine's own load arm to the byte one.
    let arm = ty("ir_rf_load_arm");
    assert!(
        arm.contains("(ir_load_eval s (IRScalar.ptr_ a))")
            && arm.contains("(ir_bm_load (ir_rf_enc g (ir_mach_mem s)) k a)"),
        "ir_rf_load_arm must equate the cell load arm with the byte load arm: {arm}"
    );
    // W4's swap constraint: one resume function applied to one lookup, per memory arm. Since
    // S3.1 the lookup is the interior-address resolution, so a field address resolves too.
    for (name, resume) in [
        ("ir_bm_exec_load_factor", "ir_bm_r_load"),
        ("ir_bm_exec_store_factor", "ir_bm_r_store"),
        ("ir_bm_exec_borrow_factor", "ir_bm_r_borrow"),
    ] {
        let t = ty(name);
        assert!(
            t.contains(resume)
                && t.contains("(ir_bm_resolve (ir_bm_allocs M) a)")
                && t.contains("(cx : IRBmCtx)"),
            "{name} must factor through {resume} applied to one resolution, under the context: {t}"
        );
    }
    // The load and store resume functions walk S1b's field path by the context's layout rows.
    let value = |name: &str| -> String {
        spec.definitions()
            .get(name)
            .and_then(|d| d.value_src.clone())
            .unwrap_or_default()
    };
    for (name, path) in [
        ("ir_bm_r_load", "ir_bm_load_from (ir_bm_ctx_rows c)"),
        ("ir_bm_r_store", "ir_bm_store_from (ir_bm_ctx_rows c)"),
    ] {
        let v = value(name);
        assert!(v.contains(path), "{name} must walk the field path: {v}");
    }
    // Return is the cell return plus one memory function.
    let ret = ty("ir_bm_exec_ret_shape");
    assert!(
        ret.contains("(ir_bm_after_ret (ir_exec m (IRInst.ret ids) rs s) M)"),
        "{ret}"
    );
    // 20 arms are the cell arm, lifted VERBATIM; cast, call, callindirect and ret go through a
    // wrapper, and the eight memory / unmodelled-yet arms (load, store, alloca, gep, globaladdr,
    // borrow, the two atomics) are ByteV1's own.
    let arms = names.iter().filter(|n| n.starts_with("ir_bm_arm_")).count();
    assert_eq!(
        arms, 20,
        "one delegation lemma per non-memory IRInst constructor"
    );
    // The witnesses the scratch falsifiers ran are part of every spec build.
    for w in [
        "ir_bm_run_roundtrip",
        "ir_bm_byte_dangling_faults",
        "ir_bm_cell_dangling_reads_42",
        "ir_bm_tc_tick_then_whole_load",
        "ir_bm_tc_tick_leaves_limit",
        "ir_bm_group_load_packed",
        "ir_d20_cell_whole_load_is_stale",
        "ir_d20_byte_whole_load_sees_field",
        "ir_bm_run_heartbeat_read",
        "ir_bm_run_tick_then_whole",
        "ir_bm_gep_u64_stride",
        "ir_bm_cell_gep_u64_stride",
    ] {
        assert!(names.contains(&w), "{w} must be landed");
    }
}

/// The same declarations register in the FULL specification (`STAGES`), not only in the EvalIr
/// bundle: both stage lists carry `add_eval_ir_bmem_trie` and `add_eval_ir_bmem_core`.
#[test]
fn the_byte_memory_registers_in_the_full_spec() {
    let spec = clean_verify::test_utils::build_spec_with_stack();
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::BMEM_TRIE_NAMES);
    assert_kernel_checked_axiom_free(&spec, clean_verify::spec::BMEM_CORE_NAMES);
}
