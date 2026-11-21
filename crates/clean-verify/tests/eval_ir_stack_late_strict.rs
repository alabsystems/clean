// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strict replay of the 46 actual EvalIR declarations containing the fixed late80 heads.

use clean_kernel::{ConstantKind, DeclarationVerification, Expr, ExprKind, Name, TypeChecker};
use clean_verify::spec::{ProofStatus, Specification};
use clean_verify::spec_axiom_closure::computed_axiom_closure;
use clean_verify::test_utils::{build_eval_ir_spec_with_stack, run_with_stack};
use std::collections::BTreeSet;

// Exact definition-name union of canonical review 1e91055d's 80 fixed sites.
// This list does not expand to every EvalIR root or infer coverage from spelling.
const SELECTED: [&str; 46] = [
    "ir_stk_steps",
    "ir_stk_activation",
    "ir_mext_run",
    "ir_bool_guard_false",
    "ir_stk_clear_zero",
    "ir_stk_clear_succ",
    "ir_stk_clear_halted",
    "ir_stk_nonnil_of_running",
    "ir_stk_clear_of_running",
    "ir_stk_split",
    "ir_config_outcome_stack",
    "ir_stk_botret_hit",
    "ir_frame_dests_bind",
    "ir_frame_dests_bind2",
    "ir_frame_dests_advance",
    "ir_frame_dests_goto",
    "ir_frame_dests_set_many",
    "ir_push_cons",
    "ir_call_push",
    "ir_stk_clear_lzc_maxzz_8",
    "ir_stk_clear_lzc_maxzz_9",
    "ir_stk_botret_lz_b6",
    "ir_frames_set_bot_nil",
    "ir_frames_set_bot_one",
    "ir_frames_set_bot_two",
    "ir_frame_set_dests_mk",
    "ir_frame_dests_set_dests",
    "ir_frame_func_set_dests",
    "ir_config_set_bot_halted",
    "ir_resolve_bdst",
    "ir_bind_bdst",
    "ir_bind_result_bdst",
    "ir_bind2_bdst",
    "ir_advance_bdst",
    "ir_advance_set_mem_bdst",
    "ir_alloca_k_bdst",
    "ir_goto_bdst",
    "ir_push_bdst",
    "ir_ret_vals_bdst",
    "ir_store_live_bdst",
    "ir_store_checked_bdst",
    "ir_store_exec_bdst",
    "ir_jump_block_bdst",
    "ir_jump_func_bdst",
    "ir_condbr_exec_bdst",
    "ir_switch_exec_bdst",
];

fn require_closed(expression: &Expr, name: &str) {
    assert!(
        !expression.has_fvar_quick(),
        "{name}: unexpected free variable"
    );
    assert!(
        !expression.has_loose_bvars(),
        "{name}: loose bound variable"
    );
    assert!(
        !expression.has_expr_mvar_quick(),
        "{name}: unresolved term meta"
    );
    assert!(
        !expression.has_level_mvar_quick(),
        "{name}: unresolved universe meta"
    );
}

fn require_checked_root(spec: &Specification, name: &str) {
    let record = spec
        .get_definition(name)
        .unwrap_or_else(|| panic!("{name}: actual source record"));
    assert_eq!(record.name, name, "{name}: exact stored name");
    assert!(
        !record.is_axiom,
        "{name}: source record must not be an axiom"
    );
    assert_ne!(
        record.proof_status,
        ProofStatus::Axiom,
        "{name}: axiom status"
    );
    assert!(
        record
            .value_src
            .as_ref()
            .is_some_and(|source| !source.is_empty()),
        "{name}: actual authored value"
    );
    let type_ = record
        .elaborated_type
        .as_ref()
        .unwrap_or_else(|| panic!("{name}: stored type"));
    let value = record
        .elaborated_value
        .as_ref()
        .unwrap_or_else(|| panic!("{name}: stored value"));
    let kernel_name = Name::from_string(name);
    let root = spec
        .env()
        .get_const(&kernel_name)
        .unwrap_or_else(|| panic!("{name}: actual kernel root"));
    assert_eq!(root.name, kernel_name, "{name}: exact live kernel name");
    assert_ne!(root.kind, ConstantKind::Axiom, "{name}: kernel axiom");
    assert_eq!(&root.type_, type_, "{name}: source/kernel type identity");
    assert_eq!(
        root.value.as_ref(),
        Some(value),
        "{name}: source/kernel value identity"
    );
    assert_eq!(
        spec.env().declaration_verification(&kernel_name),
        Some(DeclarationVerification::FullKernelCheck),
        "{name}: full checked provenance"
    );
    require_closed(type_, name);
    require_closed(value, name);
    assert!(
        !value.collect_constants().contains(&kernel_name),
        "{name}: value must not cite its own root"
    );

    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let sort = checker
        .infer_type_full(type_)
        .unwrap_or_else(|error| panic!("{name}: full declared-type check: {error:?}"));
    assert!(
        matches!(checker.whnf(&sort).kind(), ExprKind::Sort(_)),
        "{name}: declared type must inhabit a sort"
    );
    assert!(
        !checker.heartbeat_spent(),
        "{name}: declared-type check must finish"
    );
    checker
        .check_type(value, type_)
        .unwrap_or_else(|error| panic!("{name}: public full value check: {error:?}"));
    assert!(
        !checker.heartbeat_spent(),
        "{name}: value check must finish"
    );
    spec.verify_definition(name).unwrap_or_else(|error| {
        panic!("{name}: original verification must also succeed: {error:?}")
    });

    require_empty_closures(spec, &kernel_name, name);
}

fn require_empty_closures(spec: &Specification, kernel_name: &Name, name: &str) {
    // Require actual answers before using the legacy computed API, whose own
    // absent-root behavior is an empty set. Missing data cannot pass this test.
    let domain = spec
        .env()
        .axiom_deps(kernel_name)
        .unwrap_or_else(|| panic!("{name}: missing domain closure"));
    let foundational = spec
        .env()
        .foundational_axiom_deps(kernel_name)
        .unwrap_or_else(|| panic!("{name}: missing foundational closure"));
    let computed = computed_axiom_closure(spec, name);
    let rendered: BTreeSet<String> = domain.iter().map(Name::to_unambiguous_string).collect();
    assert_eq!(
        computed, rendered,
        "{name}: computed/live domain closure agreement"
    );
    assert!(domain.is_empty(), "{name}: domain axioms {domain:?}");
    assert!(
        foundational.is_empty(),
        "{name}: foundational axioms {foundational:?}"
    );
    assert!(computed.is_empty(), "{name}: computed axioms {computed:?}");
}

// Compare the actual substituted source terms against the existing run
// witnesses. This inspects fixed source assembly, never recursor/arity policy.
fn actual_init(source: &str) -> &str {
    let needle = "(ir_init ir_lzc_module ";
    assert_eq!(
        source.matches(needle).count(),
        1,
        "one actual Max(Zero,Zero) initial state"
    );
    let start = source.find(needle).expect("actual ir_init source");
    let mut depth = 0usize;
    for (offset, character) in source[start..].char_indices() {
        match character {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return &source[start..start + offset + 1];
                }
            }
            _ => {}
        }
    }
    panic!("balanced actual initial state")
}

#[test]
fn selected_late46_values_recheck_strictly_in_evalir_without_axioms() {
    run_with_stack(|| {
        let expected: BTreeSet<&str> = SELECTED.into_iter().collect();
        assert_eq!(
            expected.len(),
            46,
            "exact distinct selected declaration names"
        );
        // This is the real production EvalIR bundle; construction failure fails.
        let spec = build_eval_ir_spec_with_stack();
        let mut checked = BTreeSet::new();
        for name in SELECTED {
            assert!(checked.insert(name), "{name}: duplicate replay");
            require_checked_root(&spec, name);
        }
        assert_eq!(
            checked, expected,
            "all and only the 46 selected roots replayed"
        );

        for (positive, run) in [
            ("ir_stk_clear_lzc_maxzz_8", "ir_lzc_max_running_at_8"),
            ("ir_stk_clear_lzc_maxzz_9", "ir_lzc_max_stuck_at_9"),
        ] {
            assert!(
                checked.contains(positive),
                "the concrete positive must be replayed"
            );
            let source = &spec
                .get_definition(positive)
                .expect("actual substituted positive")
                .type_src;
            let existing_run = &spec
                .get_definition(run)
                .expect("actual existing run witness")
                .type_src;
            assert!(
                !source.contains("{INIT}"),
                "{positive}: normal substitution must execute"
            );
            assert_eq!(
                actual_init(source),
                actual_init(existing_run),
                "{positive}: normal initial state must match its run witness"
            );
        }
        assert!(
            checked.contains("ir_stk_botret_lz_b6"),
            "the actual bottom-ret positive must replay"
        );
    });
}
