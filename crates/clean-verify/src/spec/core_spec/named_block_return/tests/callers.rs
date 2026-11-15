// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real captured Eq callers; mutations are explicit new model records.
//! Synthetic F/G tests separately exercise a nonzero member position.

use super::checks;
use crate::test_utils::{run_with_stack, shared_spec};

const ENV: &str = "(red_ind_ctor the_red_env)";
const BLOCK: &str = "(kind_all_names kcre_eq_ind_meta)";
const FAMILY: &str = "kcre_eq_type_name";
const IM: &str = "kcre_eq_ind_meta";
const CN: &str = "kcre_eq_refl_name";
const CM: &str = "kcre_eq_refl_meta";
const ONE: &str = "(Nat.succ Nat.zero)";
const TWO: &str = "(Nat.succ (Nat.succ Nat.zero))";
const THREE: &str = "(Nat.succ (Nat.succ (Nat.succ Nat.zero)))";
const FACTS: &str = "NamedStrictAppFacts (kind_all_names kcre_eq_ind_meta) (nig_param_levels (kconst_params (kind_sig kcre_eq_ind_meta))) kcre_eq_type_name (count_pi (kconst_type (kctor_sig kcre_eq_refl_meta))) (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta) (return_type (kconst_type (kctor_sig kcre_eq_refl_meta)))";

fn whole(env: &str) -> String {
    format!("nrb_block_return_b {env} {BLOCK}")
}

fn selected_eq_body() -> String {
    // Exact sixteen outputs of nrb_selected_constructor, specialized to the
    // actual captured records. All are produced by that theorem; none is an
    // input oracle, and C is the Type-valued facts carrier, not a proposition.
    let bindings = [
        ("_reference_length", "Eq Nat (list_length (nrb_reference kcre_eq_ind_meta)) (kind_num_params kcre_eq_ind_meta)"),
        ("_unique_block", "Eq Bool (nrb_names_unique_b (kind_all_names kcre_eq_ind_meta)) Bool.true"),
        ("_block", "Eq (ListType Name) (kind_all_names kcre_eq_ind_meta) (kind_all_names kcre_eq_ind_meta)"),
        ("_parameters", "Eq Nat (kind_num_params kcre_eq_ind_meta) (kind_num_params kcre_eq_ind_meta)"),
        ("_member_levels", "Eq (ListType Name) (kconst_params (kind_sig kcre_eq_ind_meta)) (kconst_params (kind_sig kcre_eq_ind_meta))"),
        ("_member_prefix", "Eq Bool (nig_pi_prefix_b (nrb_reference kcre_eq_ind_meta) (kconst_type (kind_sig kcre_eq_ind_meta))) Bool.true"),
        ("_checked_indices", "Eq (OptionType Nat) (nig_checked_indices (kind_num_params kcre_eq_ind_meta) (kconst_type (kind_sig kcre_eq_ind_meta))) (OptionType.some Nat (kind_num_indices kcre_eq_ind_meta))"),
        ("_former_count", "Eq Nat (count_pi (kconst_type (kind_sig kcre_eq_ind_meta))) (Nat.add (kind_num_params kcre_eq_ind_meta) (kind_num_indices kcre_eq_ind_meta))"),
        ("_parent", "Eq Name (kctor_parent kcre_eq_refl_meta) kcre_eq_type_name"),
        ("_ctor_parameters", "Eq Nat (kctor_num_params kcre_eq_refl_meta) (kind_num_params kcre_eq_ind_meta)"),
        ("_ctor_levels", "Eq (ListType Name) (kconst_params (kctor_sig kcre_eq_refl_meta)) (kconst_params (kind_sig kcre_eq_ind_meta))"),
        ("_ctor_index", "Eq Nat (kctor_index kcre_eq_refl_meta) Nat.zero"),
        ("_ctor_count", "Eq Nat (count_pi (kconst_type (kctor_sig kcre_eq_refl_meta))) (Nat.add (kind_num_params kcre_eq_ind_meta) (kctor_num_fields kcre_eq_refl_meta))"),
        ("_ctor_prefix", "Eq Bool (nig_pi_prefix_b (nrb_reference kcre_eq_ind_meta) (kconst_type (kctor_sig kcre_eq_refl_meta))) Bool.true"),
        ("_parameter_bound", "Le (kind_num_params kcre_eq_ind_meta) (count_pi (kconst_type (kctor_sig kcre_eq_refl_meta)))"),
        ("facts", FACTS),
    ];
    assert_eq!(bindings.len(), 16);
    let continuation = bindings
        .iter()
        .map(|(n, t)| format!("({n} : {t})"))
        .collect::<Vec<_>>()
        .join(" ");
    let first_at = format!("(Eq.refl (OptionType Name) (OptionType.some Name {FAMILY}))");
    let first_lookup = format!("(Eq.refl (OptionType KIndMeta) (OptionType.some KIndMeta {IM}))");
    let ctor_at = format!("(Eq.refl (OptionType Name) (OptionType.some Name {CN}))");
    let ctor_lookup = format!("(Eq.refl (OptionType KCtorMeta) (OptionType.some KCtorMeta {CM}))");
    format!("nrb_selected_constructor {ENV} {BLOCK} {FAMILY} {IM} Nat.zero {FAMILY} {IM} Nat.zero {CN} {CM}
        (Eq.refl Bool Bool.true) {first_at} {first_lookup} {first_at} {first_lookup}
        {ctor_at} {ctor_lookup} ({FACTS}) (fun {continuation} => facts)")
}

#[test]
fn named_block_return_actual_eq_whole_computes() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (term, expected) in [
            (
                format!("kind_for {ENV} {FAMILY}"),
                format!("OptionType.some KIndMeta {IM}"),
            ),
            (
                format!("kctor_for {ENV} {CN}"),
                format!("OptionType.some KCtorMeta {CM}"),
            ),
            (
                format!("kcre_ind_ctor_tenv {FAMILY}"),
                "OptionType.some KConstSig kcre_eq_type_signature".to_owned(),
            ),
            (
                format!("kcre_ind_ctor_tenv {CN}"),
                "OptionType.some KConstSig kcre_eq_refl_signature".to_owned(),
            ),
            (
                format!("kind_sig {IM}"),
                "kcre_eq_type_signature".to_owned(),
            ),
            (
                format!("kctor_sig {CM}"),
                "kcre_eq_refl_signature".to_owned(),
            ),
            (format!("kctor_parent {CM}"), FAMILY.to_owned()),
            (
                format!("kind_all_names {IM}"),
                format!("ListType.cons Name {FAMILY} (ListType.nil Name)"),
            ),
            (
                format!("kind_ctor_names {IM}"),
                format!("ListType.cons Name {CN} (ListType.nil Name)"),
            ),
            (format!("kind_num_params {IM}"), TWO.to_owned()),
            (format!("kind_num_indices {IM}"), ONE.to_owned()),
            (format!("kctor_num_fields {CM}"), "Nat.zero".to_owned()),
            (
                format!("count_pi (kconst_type (kind_sig {IM}))"),
                THREE.to_owned(),
            ),
            (
                format!("count_pi (kconst_type (kctor_sig {CM}))"),
                TWO.to_owned(),
            ),
            (format!("nrb_reference {IM}"), "nig_eq_domains".to_owned()),
            (whole(ENV), "Bool.true".to_owned()),
        ] {
            checks::computes(spec, &term, &expected);
        }
        checks::not_def_eq(spec, FAMILY, CN);
        checks::not_def_eq(
            spec,
            &format!("kind_num_indices {IM}"),
            &format!("kctor_num_fields {CM}"),
        );
    });
}

#[test]
fn named_block_return_actual_eq_selected_registration_and_closures() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        let whole_type = format!("Eq Bool ({}) Bool.true", whole(ENV));
        let whole_body = "Eq.refl Bool Bool.true";
        super::super::theorem(
            &mut spec,
            "nrb_test_actual_eq_whole",
            &whole_type,
            whole_body,
            "Test-only actual captured Eq whole check",
        )
        .expect("whole reflected checker accepts in actual Clean");
        checks::record(
            &spec,
            "nrb_test_actual_eq_whole",
            &whole_type,
            whole_body,
            Some(true),
        );
        let body = selected_eq_body();
        super::super::theorem(
            &mut spec,
            "nrb_test_actual_eq_selected",
            FACTS,
            &body,
            "Test-only whole-check-to-selected captured Eq caller",
        )
        .expect("actual selected-constructor continuation checks");
        checks::record(
            &spec,
            "nrb_test_actual_eq_selected",
            FACTS,
            &body,
            Some(false),
        );
        // The supplied whole success and six positional/table equations are
        // actual computations over the real table, not an authored replacement.
        checks::caller(&spec, &format!("nig_strict_computed_suffix {BLOCK} (nig_param_levels (kconst_params (kind_sig {IM}))) {FAMILY} (count_pi (kconst_type (kctor_sig {CM}))) (kind_num_params {IM}) (kind_num_indices {IM}) (return_type (kconst_type (kctor_sig {CM}))) nrb_test_actual_eq_selected"),
            &format!("Eq Bool (nig_indices_free_b {BLOCK} (list_drop (kind_num_params {IM}) (kapp_args (return_type (kconst_type (kctor_sig {CM})))))) Bool.true"));
    });
}

const IND_FIELDS: [&str; 5] = [
    "(kind_sig kcre_eq_ind_meta)",
    "(kind_num_params kcre_eq_ind_meta)",
    "(kind_num_indices kcre_eq_ind_meta)",
    "(kind_ctor_names kcre_eq_ind_meta)",
    "(kind_all_names kcre_eq_ind_meta)",
];
const CTOR_FIELDS: [&str; 5] = [
    "(kctor_sig kcre_eq_refl_meta)",
    "(kctor_parent kcre_eq_refl_meta)",
    "(kctor_num_params kcre_eq_refl_meta)",
    "(kctor_num_fields kcre_eq_refl_meta)",
    "(kctor_index kcre_eq_refl_meta)",
];

fn record_expression(head: &str, fields: &[&str; 5]) -> String {
    format!("{head} {}", fields.join(" "))
}

fn mutated_record(head: &str, original: &[&str; 5], index: usize, replacement: &str) -> String {
    let mut fields = *original;
    fields[index] = replacement;
    record_expression(head, &fields)
}

fn assert_single_field(
    spec: &crate::spec::Specification,
    record: &str,
    projectors: &[&str; 5],
    fields: &[&str; 5],
    changed: usize,
    replacement: &str,
) {
    for (index, projector) in projectors.iter().enumerate() {
        checks::computes(
            spec,
            &format!("{projector} ({record})"),
            if index == changed {
                replacement
            } else {
                fields[index]
            },
        );
    }
}

#[test]
fn named_block_return_actual_eq_inductive_metadata_mutations() {
    run_with_stack(|| {
        let spec = shared_spec();
        let reconstructed = record_expression("KIndMeta.mk", &IND_FIELDS);
        checks::computes(spec, &reconstructed, IM);
        checks::computes(
            spec,
            &whole(&format!(
                "(IndCtorEnv.addInd {ENV} {FAMILY} ({reconstructed}))"
            )),
            "Bool.true",
        );
        let projectors = [
            "kind_sig",
            "kind_num_params",
            "kind_num_indices",
            "kind_ctor_names",
            "kind_all_names",
        ];
        let changes = [
            (0, "(KConstSig.mk (ListType.nil Name) (kconst_type (kind_sig kcre_eq_ind_meta)))"),
            (0, "(KConstSig.mk (kconst_params (kind_sig kcre_eq_ind_meta)) (KExpr.sort Level.zero))"),
            (1, "Nat.zero"),
            (2, "Nat.zero"),
            (3, "(ListType.cons Name kcre_eq_type_name (ListType.nil Name))"),
            (3, "(ListType.cons Name kcre_eq_refl_name (ListType.cons Name kcre_eq_refl_name (ListType.nil Name)))"),
            (4, "(ListType.nil Name)"),
        ];
        for (field, replacement) in changes {
            let record = mutated_record("KIndMeta.mk", &IND_FIELDS, field, replacement);
            assert_single_field(spec, &record, &projectors, &IND_FIELDS, field, replacement);
            checks::not_def_eq(spec, &record, IM);
            checks::computes(
                spec,
                &whole(&format!("(IndCtorEnv.addInd {ENV} {FAMILY} ({record}))")),
                "Bool.false",
            );
        }
        // Load-bearing limit: no source completeness premise is present.
        // The checker checks ALL LISTED constructors, not an external list.
        let empty_ctors = mutated_record("KIndMeta.mk", &IND_FIELDS, 3, "(ListType.nil Name)");
        assert_single_field(
            spec,
            &empty_ctors,
            &projectors,
            &IND_FIELDS,
            3,
            "(ListType.nil Name)",
        );
        checks::computes(
            spec,
            &whole(&format!(
                "(IndCtorEnv.addInd {ENV} {FAMILY} ({empty_ctors}))"
            )),
            "Bool.true",
        );
    });
}

#[test]
fn named_block_return_actual_eq_constructor_metadata_mutations() {
    run_with_stack(|| {
        let spec = shared_spec();
        let reconstructed = record_expression("KCtorMeta.mk", &CTOR_FIELDS);
        checks::computes(spec, &reconstructed, CM);
        checks::computes(
            spec,
            &whole(&format!(
                "(IndCtorEnv.addCtor {ENV} {CN} ({reconstructed}))"
            )),
            "Bool.true",
        );
        let projectors = [
            "kctor_sig",
            "kctor_parent",
            "kctor_num_params",
            "kctor_num_fields",
            "kctor_index",
        ];
        let changes = [
            (0, "(KConstSig.mk (ListType.nil Name) (kconst_type (kctor_sig kcre_eq_refl_meta)))"),
            (0, "(KConstSig.mk (kconst_params (kctor_sig kcre_eq_refl_meta)) (KExpr.sort Level.zero))"),
            (1, "kcre_eq_refl_name"),
            (2, "Nat.zero"),
            (3, ONE),
            (4, ONE),
        ];
        for (field, replacement) in changes {
            let record = mutated_record("KCtorMeta.mk", &CTOR_FIELDS, field, replacement);
            assert_single_field(spec, &record, &projectors, &CTOR_FIELDS, field, replacement);
            checks::not_def_eq(spec, &record, CM);
            checks::computes(
                spec,
                &whole(&format!("(IndCtorEnv.addCtor {ENV} {CN} ({record}))")),
                "Bool.false",
            );
        }
        // Wrong-kind shadows use the actual tagged lookup, not two namespaces.
        checks::computes(
            spec,
            &whole(&format!("(IndCtorEnv.addCtor {ENV} {FAMILY} {CM})")),
            "Bool.false",
        );
        checks::computes(
            spec,
            &whole(&format!("(IndCtorEnv.addInd {ENV} {CN} {IM})")),
            "Bool.false",
        );
    });
}

#[test]
fn named_block_return_positions_and_other_member_controls() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (term, expected) in [
            ("nrb_name_at nrb_demo_block Nat.zero", "OptionType.some Name nrb_demo_f"),
            ("nrb_name_at nrb_demo_block (Nat.succ Nat.zero)", "OptionType.some Name nrb_demo_g"),
            ("nrb_name_at nrb_demo_block (Nat.succ (Nat.succ Nat.zero))", "OptionType.none Name"),
            ("nrb_block_return_b nrb_demo_env nrb_demo_block", "Bool.true"),
            ("nrb_block_return_b nrb_demo_bad_other_parent nrb_demo_block", "Bool.false"),
            ("nrb_ctor_at_b nrb_demo_bad_other_parent nrb_demo_block nrb_demo_f_meta nrb_demo_g nrb_demo_g_meta Nat.zero nrb_demo_cg", "Bool.true"),
            ("nrb_block_return_b nrb_demo_bad_other_index nrb_demo_block", "Bool.false"),
            ("nrb_block_return_b nrb_demo_bad_g_arity nrb_demo_block", "Bool.false"),
            ("nrb_block_return_b IndCtorEnv.empty nrb_demo_block", "Bool.false"),
            ("nrb_block_return_b (IndCtorEnv.addCtor nrb_demo_env nrb_demo_f nrb_demo_cf_meta) nrb_demo_block", "Bool.false"),
            ("nrb_block_return_b nrb_demo_env (ListType.cons Name nrb_demo_g (ListType.cons Name nrb_demo_f (ListType.nil Name)))", "Bool.false"),
            ("nrb_nat_some_b (Nat.succ Nat.zero) (OptionType.some Nat (Nat.succ Nat.zero))", "Bool.true"),
            ("nrb_nat_some_b (Nat.succ Nat.zero) (OptionType.some Nat Nat.zero)", "Bool.false"),
            ("nrb_nat_some_b (Nat.succ Nat.zero) (OptionType.none Nat)", "Bool.false"),
        ] {
            checks::computes(spec, term, expected);
        }
        let predicate = "(fun (j : Nat) (n : Name) => nrb_option_b Name (fun (m : Name) => name_eqb n m) (nrb_name_at nrb_demo_block j))";
        checks::computes(
            spec,
            &format!("nrb_all_index_b {predicate} nrb_demo_block"),
            "Bool.true",
        );
        checks::caller(spec, &format!("nrb_all_index_at nrb_demo_block {predicate} {ONE} nrb_demo_g (Eq.refl Bool Bool.true) (Eq.refl (OptionType Name) (OptionType.some Name nrb_demo_g))"),
            &format!("Eq Bool ({predicate} {ONE} nrb_demo_g) Bool.true"));
        checks::caller(
            spec,
            &format!(
                "nrb_nat_some_sound {ONE} (OptionType.some Nat {ONE}) (Eq.refl Bool Bool.true)"
            ),
            &format!("Eq (OptionType Nat) (OptionType.some Nat {ONE}) (OptionType.some Nat {ONE})"),
        );
        let (ty, body) = super::super::records::DECLARATIONS
            .iter()
            .find_map(|d| match d {
                super::super::DeclarationInput::Proof(name, ty, body)
                    if *name == "nrb_demo_selected_g" =>
                {
                    Some((*ty, *body))
                }
                _ => None,
            })
            .expect("actual registered nonzero-position selector caller");
        checks::caller(spec, body, ty);
    });
}
