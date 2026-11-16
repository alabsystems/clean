// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Computations over actual captured model records and real checked callers.
//! These tests do not turn a final stored block into pre-restoration admission.

use super::checks;
use crate::test_utils::{run_with_stack, shared_spec};

const ONE: &str = "(Nat.succ Nat.zero)";
const TWO: &str = "(Nat.succ (Nat.succ Nat.zero))";
const THREE: &str = "(Nat.succ (Nat.succ (Nat.succ Nat.zero)))";
const P: &str = "(kind_num_params kcre_eq_ind_meta)";
const NI: &str = "(kind_num_indices kcre_eq_ind_meta)";
const DEPTH: &str = "(count_pi nig_eq_ctor)";
const FACTS: &str = "NamedStrictAppFacts nig_eq_block nig_eq_levels nig_eq_family (count_pi nig_eq_ctor) (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta) nig_eq_return";

#[test]
fn named_indexed_guard_actual_eq_records_and_counts() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (source, expected) in [
            (
                "kind_for (red_ind_ctor the_red_env) kcre_eq_type_name",
                "@OptionType.some KIndMeta kcre_eq_ind_meta",
            ),
            (
                "kctor_for (red_ind_ctor the_red_env) kcre_eq_refl_name",
                "@OptionType.some KCtorMeta kcre_eq_refl_meta",
            ),
            (
                "kcre_ind_ctor_tenv kcre_eq_type_name",
                "@OptionType.some KConstSig kcre_eq_type_signature",
            ),
            (
                "kcre_ind_ctor_tenv kcre_eq_refl_name",
                "@OptionType.some KConstSig kcre_eq_refl_signature",
            ),
            ("kind_sig kcre_eq_ind_meta", "kcre_eq_type_signature"),
            ("kctor_sig kcre_eq_refl_meta", "kcre_eq_refl_signature"),
            ("kctor_parent kcre_eq_refl_meta", "kcre_eq_type_name"),
            (
                "kind_all_names kcre_eq_ind_meta",
                "@ListType.cons Name kcre_eq_type_name (@ListType.nil Name)",
            ),
            (
                "kind_ctor_names kcre_eq_ind_meta",
                "@ListType.cons Name kcre_eq_refl_name (@ListType.nil Name)",
            ),
            ("kctor_index kcre_eq_refl_meta", "Nat.zero"),
            ("kind_num_params kcre_eq_ind_meta", TWO),
            ("kctor_num_params kcre_eq_refl_meta", TWO),
            ("kind_num_indices kcre_eq_ind_meta", ONE),
            ("kctor_num_fields kcre_eq_refl_meta", "Nat.zero"),
            ("count_pi nig_eq_former", THREE),
            ("count_pi nig_eq_ctor", TWO),
            ("list_length (nig_pi_domains nig_eq_former)", THREE),
            ("list_length nig_eq_domains", TWO),
            (
                "kconst_params kcre_eq_refl_signature",
                "kconst_params kcre_eq_type_signature",
            ),
            ("nig_eq_block", "kind_all_names kcre_eq_ind_meta"),
        ] {
            checks::computes(spec, source, expected);
        }
        checks::not_def_eq(spec, "kcre_eq_type_name", "kcre_eq_refl_name");
        checks::not_def_eq(
            spec,
            "kctor_num_fields kcre_eq_refl_meta",
            "kind_num_indices kcre_eq_ind_meta",
        );
        checks::computes(spec, "nig_eq_return", &format!(
            "KExpr.app (KExpr.app (KExpr.app (KExpr.const kcre_eq_type_name nig_eq_levels) (KExpr.bvar {ONE})) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)"));
        checks::computes(spec, &format!("nig_slots {DEPTH} {P} Nat.zero"), &format!(
            "@ListType.cons KExpr (KExpr.bvar {ONE}) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))"));
        checks::computes(
            spec,
            &format!("list_drop {P} (kapp_args nig_eq_return)"),
            "@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)",
        );
        checks::computes(
            spec,
            "nig_pi_prefix_b nig_eq_domains nig_eq_ctor",
            "Bool.true",
        );
        checks::computes(spec, &format!("nig_strict_app_b nig_eq_block nig_eq_levels nig_eq_family {DEPTH} {P} {NI} nig_eq_return"), "Bool.true");
    });
}

#[test]
fn named_indexed_guard_generic_facts_and_computed_suffix() {
    run_with_stack(|| {
        let spec = shared_spec();
        // Constructor parameters become implicit in Clean's environment. The
        // fully applied lambda keeps KExpr as the element type when the
        // constructor is passed as a higher-order congruence argument.
        checks::caller(
            spec,
            "universe_bridge_congr2 KExpr (ListType KExpr) (ListType KExpr) (fun (element : KExpr) (elements : ListType KExpr) => @ListType.cons KExpr element elements) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) (@ListType.nil KExpr) (@ListType.nil KExpr) (@Eq.refl KExpr (KExpr.bvar Nat.zero)) (@Eq.refl (ListType KExpr) (@ListType.nil KExpr))",
            "@Eq (ListType KExpr) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr)) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))",
        );
        let args =
            format!("nig_eq_block nig_eq_levels nig_eq_family {DEPTH} {P} {NI} nig_eq_return");
        checks::caller(
            spec,
            &format!("nig_strict_sound {args} nig_eq_actual_guard"),
            FACTS,
        );
        checks::caller(
            spec,
            &format!("nig_strict_complete {args} nig_eq_actual_facts"),
            &format!("@Eq Bool (nig_strict_app_b {args}) Bool.true"),
        );
        checks::caller(
            spec,
            &format!("nig_strict_arity {args} nig_eq_actual_facts"),
            &format!("@Eq Nat (list_length (kapp_args nig_eq_return)) (Nat.add {P} {NI})"),
        );
        checks::caller(spec, &format!("nig_strict_computed_suffix {args} nig_eq_actual_facts"),
            &format!("@Eq Bool (nig_indices_free_b nig_eq_block (list_drop {P} (kapp_args nig_eq_return))) Bool.true"));
        checks::caller(
            spec,
            "nig_eq_actual_member_exclusion",
            "@Eq Bool (const_occurs nig_eq_family (KExpr.bvar Nat.zero)) Bool.false",
        );
        checks::caller(spec, "nig_eq_caller_bound", &format!("Le {P} {DEPTH}"));
        let selected = "@ListType.cons KExpr nig_eq_former (@ListType.nil KExpr)";
        checks::caller(spec, &format!(
            "nig_selected_member_count {P} {NI} Nat.zero ({selected}) nig_eq_former (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr nig_eq_former)) (@Eq.refl (OptionType Nat) (@OptionType.some Nat {NI}))"),
            &format!("@Eq Nat (count_pi nig_eq_former) (Nat.add {P} {NI})"));
        let continuation = format!(
            "fun (ix : ListType KExpr) (_spine : @Eq KExpr nig_eq_return (apply_spine (list_append (nig_slots {DEPTH} {P} Nat.zero) ix) (KExpr.const nig_eq_family nig_eq_levels))) (_length : @Eq Nat (list_length ix) {NI}) (_free : @Eq Bool (nig_indices_free_b nig_eq_block ix) Bool.true) => ix");
        // Opaque proof data is consumed by its actual Type-valued eliminator.
        // No claim is made that kernel reduction unfolds this opaque proof.
        checks::caller(
            spec,
            &format!("nig_eq_actual_decomposition (ListType KExpr) ({continuation})"),
            "ListType KExpr",
        );
    });
}

#[test]
fn named_indexed_guard_connected_eq_continuation() {
    run_with_stack(|| {
        let spec = shared_spec();
        let bindings = [
            ("_former_lookup", "@Eq (OptionType KIndMeta) (kind_for (red_ind_ctor the_red_env) kcre_eq_type_name) (@OptionType.some KIndMeta kcre_eq_ind_meta)"),
            ("_ctor_lookup", "@Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor the_red_env) kcre_eq_refl_name) (@OptionType.some KCtorMeta kcre_eq_refl_meta)"),
            ("_former_sig", "@Eq KConstSig (kind_sig kcre_eq_ind_meta) kcre_eq_type_signature"),
            ("_ctor_sig", "@Eq KConstSig (kctor_sig kcre_eq_refl_meta) kcre_eq_refl_signature"),
            ("_former_tenv", "@Eq (OptionType KConstSig) (kcre_ind_ctor_tenv kcre_eq_type_name) (@OptionType.some KConstSig kcre_eq_type_signature)"),
            ("_ctor_tenv", "@Eq (OptionType KConstSig) (kcre_ind_ctor_tenv kcre_eq_refl_name) (@OptionType.some KConstSig kcre_eq_refl_signature)"),
            ("_parent", "@Eq Name (kctor_parent kcre_eq_refl_meta) kcre_eq_type_name"),
            ("_block_member", "@Eq Bool (name_list_mem (kind_all_names kcre_eq_ind_meta) kcre_eq_type_name) Bool.true"),
            ("_ctor_member", "@Eq Bool (name_list_mem (kind_ctor_names kcre_eq_ind_meta) kcre_eq_refl_name) Bool.true"),
            ("_block", "@Eq (ListType Name) (kind_all_names kcre_eq_ind_meta) (@ListType.cons Name kcre_eq_type_name (@ListType.nil Name))"),
            ("_index", "@Eq Nat (kctor_index kcre_eq_refl_meta) Nat.zero"),
            ("_params", "@Eq Nat (kctor_num_params kcre_eq_refl_meta) (kind_num_params kcre_eq_ind_meta)"),
            ("_universes", "@Eq (ListType Name) (kconst_params kcre_eq_refl_signature) (kconst_params kcre_eq_type_signature)"),
            ("_ctor_count", "@Eq Nat (count_pi (kconst_type kcre_eq_refl_signature)) (Nat.add (kctor_num_params kcre_eq_refl_meta) (kctor_num_fields kcre_eq_refl_meta))"),
            ("_former_count", "@Eq Nat (list_length (nig_pi_domains (kconst_type kcre_eq_type_signature))) (Nat.add (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta))"),
            ("_domain_count", "@Eq Nat (list_length nig_eq_domains) (kind_num_params kcre_eq_ind_meta)"),
            ("_domains", "@Eq (ListType KExpr) nig_eq_domains (list_take (kind_num_params kcre_eq_ind_meta) (nig_pi_domains (kconst_type kcre_eq_type_signature)))"),
            ("_prefix", "@Eq Bool (nig_pi_prefix_b nig_eq_domains nig_eq_ctor) Bool.true"),
            ("_bound", "Le (kind_num_params kcre_eq_ind_meta) (count_pi nig_eq_ctor)"),
            ("facts", FACTS),
            ("_suffix", "@Eq Bool (nig_indices_free_b nig_eq_block (list_drop (kind_num_params kcre_eq_ind_meta) (kapp_args nig_eq_return))) Bool.true"),
        ];
        assert_eq!(bindings.len(), 21);
        let binders = bindings
            .iter()
            .map(|(name, ty)| format!("({name} : {ty})"))
            .collect::<Vec<_>>()
            .join(" ");
        checks::caller(
            spec,
            &format!("nig_eq_connected_stored_context ({FACTS}) (fun {binders} => facts)"),
            FACTS,
        );
    });
}

#[test]
fn named_indexed_guard_pi_domain_extraction_covers_nine_arms() {
    run_with_stack(|| {
        let spec = shared_spec();
        let pi = "KExpr.pi (KExpr.sort Level.zero) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))";
        checks::computes(spec, &format!("nig_pi_domains ({pi})"),
            "@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.cons KExpr (KExpr.bvar Nat.zero) (@ListType.nil KExpr))");
        let non_pi = [
            "KExpr.sort Level.zero".to_owned(),
            "KExpr.bvar Nat.zero".to_owned(),
            format!("KExpr.app ({pi}) ({pi})"),
            format!("KExpr.lam ({pi}) ({pi})"),
            "KExpr.const Name.anonymous (@ListType.nil Level)".to_owned(),
            format!("KExpr.let_ ({pi}) ({pi}) ({pi})"),
            format!("KExpr.proj Name.anonymous Nat.zero ({pi})"),
            "KExpr.lit Nat.zero".to_owned(),
        ];
        for source in non_pi {
            checks::computes(
                spec,
                &format!("nig_pi_domains ({source})"),
                "@ListType.nil KExpr",
            );
            checks::caller(
                spec,
                &format!("nig_pi_domains_length ({source})"),
                &format!("@Eq Nat (list_length (nig_pi_domains ({source}))) (count_pi ({source}))"),
            );
        }
        checks::caller(
            spec,
            &format!("nig_pi_domains_length ({pi})"),
            &format!("@Eq Nat (list_length (nig_pi_domains ({pi}))) {TWO}"),
        );
    });
}

#[test]
fn named_indexed_guard_mutual_occurrence_and_raw_level_boundaries() {
    run_with_stack(|| {
        let spec = shared_spec();
        let sibling = format!("(Name.str Name.anonymous {ONE})");
        let block = format!("(@ListType.cons Name Name.anonymous (@ListType.cons Name {sibling} (@ListType.nil Name)))");
        let c = format!("(KExpr.const {sibling} (@ListType.nil Level))");
        let s = "(KExpr.sort Level.zero)";
        let occurrences = [
            format!("KExpr.app {c} {s}"),
            format!("KExpr.app {s} {c}"),
            format!("KExpr.lam {c} {s}"),
            format!("KExpr.lam {s} {c}"),
            format!("KExpr.pi {c} {s}"),
            format!("KExpr.pi {s} {c}"),
            format!("KExpr.let_ {c} {s} {s}"),
            format!("KExpr.let_ {s} {c} {s}"),
            format!("KExpr.let_ {s} {s} {c}"),
            format!("KExpr.proj Name.anonymous Nat.zero {c}"),
        ];
        for source in occurrences {
            checks::computes(
                spec,
                &format!("nig_block_free_b {block} ({source})"),
                "Bool.false",
            );
        }
        checks::computes(
            spec,
            &format!("nig_block_free_b {block} (KExpr.proj {sibling} Nat.zero {s})"),
            "Bool.true",
        );
        checks::computes(
            spec,
            &format!("nig_block_free_b {block} (KExpr.sort (Level.param {sibling}))"),
            "Bool.true",
        );
        let levels = "(@ListType.cons Level (Level.param Name.anonymous) (@ListType.nil Level))";
        checks::computes(spec, &format!("nig_head_b Name.anonymous {levels} (KExpr.const Name.anonymous (@ListType.cons Level (Level.param {sibling}) (@ListType.nil Level)))"), "Bool.false");
        // Raw model syntax, NOT a negative produced by Rust's smart Level::max.
        checks::computes(spec, &format!("nig_head_b Name.anonymous {levels} (KExpr.const Name.anonymous (@ListType.cons Level (Level.max (Level.param Name.anonymous) Level.zero) (@ListType.nil Level)))"), "Bool.false");
    });
}

#[test]
fn named_indexed_guard_caller_guards_refuse_underflow() {
    run_with_stack(|| {
        let spec = shared_spec();
        let block = "(@ListType.cons Name Name.anonymous (@ListType.nil Name))";
        checks::computes(spec, &format!("nig_strict_app_b {block} (@ListType.nil Level) Name.anonymous Nat.zero {ONE} Nat.zero (KExpr.app (KExpr.const Name.anonymous (@ListType.nil Level)) (KExpr.bvar Nat.zero))"), "Bool.true");
        checks::computes(spec, "nig_pi_prefix_b (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) (KExpr.sort Level.zero)", "Bool.false");
        checks::computes(
            spec,
            &format!("nig_checked_indices {ONE} (KExpr.sort Level.zero)"),
            "@OptionType.none Nat",
        );
        checks::computes(
            spec,
            "nig_member_indices Nat.zero (@ListType.nil KExpr) Nat.zero",
            "@OptionType.none Nat",
        );
        checks::computes(
            spec,
            &format!("nig_checked_indices {P} nig_eq_former"),
            &format!("@OptionType.some Nat {NI}"),
        );
        checks::caller(
            spec,
            "nig_eq_prefix_guard",
            "@Eq Bool (nig_pi_prefix_b nig_eq_domains nig_eq_ctor) Bool.true",
        );
        checks::caller(spec, "nig_eq_caller_bound", &format!("Le {P} {DEPTH}"));
    });
}
