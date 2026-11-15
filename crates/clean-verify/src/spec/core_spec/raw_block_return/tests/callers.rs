// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Input-only symbolic callers and finite synthetic whole-block controls.
//! Independent captured Eq/Prod source reconstruction belongs to fidelity tests.

use super::checks;
use crate::test_utils::{run_with_stack, shared_spec};

const ONE: &str = "(Nat.succ Nat.zero)";
const TWO: &str = "(Nat.succ (Nat.succ Nat.zero))";
const BLOCK: &str = "(nsi_names NamedMemberSource nsi_member_name nsi_demo_sources)";
const RAW_BLOCK: &str = "(nsi_names NamedMemberSource nsi_member_name ms)";
const DEMO_IM: &str = "(nsi_member_meta nrb_demo_levels (Nat.succ Nat.zero) (nsi_names NamedMemberSource nsi_member_name nsi_demo_sources) nsi_demo_g)";
const DEMO_CM: &str = "(nsi_ctor_meta nrb_demo_levels (Nat.succ Nat.zero) nrb_demo_g (Nat.succ Nat.zero) nsi_demo_cg2)";
const DEMO_FACTS: &str = "NamedStrictAppFacts (nsi_names NamedMemberSource nsi_member_name nsi_demo_sources) (nig_param_levels nrb_demo_levels) nrb_demo_g (count_pi (nsi_ctor_type nsi_demo_cg2)) (Nat.succ Nat.zero) (kind_num_indices (nsi_member_meta nrb_demo_levels (Nat.succ Nat.zero) (nsi_names NamedMemberSource nsi_member_name nsi_demo_sources) nsi_demo_g)) (return_type (nsi_ctor_type nsi_demo_cg2))";

#[test]
fn raw_block_return_symbolic_input_only_lookup_callers() {
    run_with_stack(|| {
        let spec = shared_spec();
        // These quantified premises concern raw input names and two raw input
        // positions only. No desired table lookup or NRB success is assumed.
        checks::caller(
            spec,
            "nsi_raw_ctor_lookup_installed",
            r"forall
 (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv)
 (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource),
 Eq Bool (nrb_names_unique_b (nsi_all_names ms)) Bool.true ->
 Eq (OptionType NamedMemberSource) (nsi_at NamedMemberSource ms mi) (OptionType.some NamedMemberSource m) ->
 Eq (OptionType NamedCtorSource) (nsi_at NamedCtorSource (nsi_member_ctors m) j) (OptionType.some NamedCtorSource c) ->
 Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install us p ms base) (nsi_ctor_name c))
  (OptionType.some KCtorMeta (nsi_ctor_meta us p (nsi_member_name m) j c))",
        );
        checks::caller(
            spec,
            "nsi_raw_kind_lookup_installed",
            r"forall
 (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv)
 (mi : Nat) (m : NamedMemberSource),
 Eq Bool (nrb_names_unique_b (nsi_all_names ms)) Bool.true ->
 Eq (OptionType NamedMemberSource) (nsi_at NamedMemberSource ms mi) (OptionType.some NamedMemberSource m) ->
 Eq (OptionType KIndMeta) (kind_for (nsi_raw_install us p ms base) (nsi_member_name m))
  (OptionType.some KIndMeta (nsi_member_meta us p (nsi_names NamedMemberSource nsi_member_name ms) m))",
        );
        checks::caller(
            spec,
            "nsi_raw_member_name_at",
            r"forall
 (ms : ListType NamedMemberSource) (mi : Nat) (m : NamedMemberSource),
 Eq (OptionType NamedMemberSource) (nsi_at NamedMemberSource ms mi) (OptionType.some NamedMemberSource m) ->
 Eq (OptionType Name) (nrb_name_at (nsi_names NamedMemberSource nsi_member_name ms) mi)
  (OptionType.some Name (nsi_member_name m))",
        );
        checks::caller(
            spec,
            "nsi_member_ctor_name_at",
            r"forall
 (us : ListType Name) (p : Nat) (block : ListType Name) (m : NamedMemberSource)
 (j : Nat) (c : NamedCtorSource),
 Eq (OptionType NamedCtorSource) (nsi_at NamedCtorSource (nsi_member_ctors m) j) (OptionType.some NamedCtorSource c) ->
 Eq (OptionType Name) (nrb_name_at (kind_ctor_names (nsi_member_meta us p block m)) j)
  (OptionType.some Name (nsi_ctor_name c))",
        );
    });
}

const SELECTED_BINDERS: &str = r"(us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource)
 (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource)
 (run : Eq Bool (nwr_raw_return_b us p ms) Bool.true)
 (member_at : Eq (OptionType NamedMemberSource) (nsi_at NamedMemberSource ms mi) (OptionType.some NamedMemberSource m))
 (ctor_at : Eq (OptionType NamedCtorSource) (nsi_at NamedCtorSource (nsi_member_ctors m) j) (OptionType.some NamedCtorSource c))";

fn selected16_consumer() -> (String, String) {
    let first = format!("(nsi_member_meta us p {RAW_BLOCK} first_source)");
    let member = format!("(nsi_member_meta us p {RAW_BLOCK} m)");
    let ctor = "(nsi_ctor_meta us p (nsi_member_name m) j c)";
    let facts = format!("NamedStrictAppFacts {RAW_BLOCK} (nig_param_levels us) (nsi_member_name m) (count_pi (nsi_ctor_type c)) p (kind_num_indices {member}) (return_type (nsi_ctor_type c))");
    // Consume the exact sixteen outputs, including the Type-valued final
    // carrier. The raw whole guard, not selected-leaf success, is the premise.
    let fields = [
        ("_reference_length", format!("Eq Nat (list_length (nrb_reference {first})) (kind_num_params {first})")),
        ("_unique_block", format!("Eq Bool (nrb_names_unique_b {RAW_BLOCK}) Bool.true")),
        ("_block", format!("Eq (ListType Name) (kind_all_names {member}) {RAW_BLOCK}")),
        ("_parameters", format!("Eq Nat (kind_num_params {member}) (kind_num_params {first})")),
        ("_member_levels", format!("Eq (ListType Name) (kconst_params (kind_sig {member})) (kconst_params (kind_sig {first}))")),
        ("_member_prefix", format!("Eq Bool (nig_pi_prefix_b (nrb_reference {first}) (kconst_type (kind_sig {member}))) Bool.true")),
        ("_checked_indices", format!("Eq (OptionType Nat) (nig_checked_indices (kind_num_params {first}) (kconst_type (kind_sig {member}))) (OptionType.some Nat (kind_num_indices {member}))")),
        ("_former_count", format!("Eq Nat (count_pi (kconst_type (kind_sig {member}))) (Nat.add (kind_num_params {first}) (kind_num_indices {member}))")),
        ("_parent", format!("Eq Name (kctor_parent {ctor}) (nsi_member_name m)")),
        ("_ctor_parameters", format!("Eq Nat (kctor_num_params {ctor}) (kind_num_params {first})")),
        ("_ctor_levels", format!("Eq (ListType Name) (kconst_params (kctor_sig {ctor})) (kconst_params (kind_sig {first}))")),
        ("_ctor_index", format!("Eq Nat (kctor_index {ctor}) j")),
        ("_ctor_count", format!("Eq Nat (count_pi (kconst_type (kctor_sig {ctor}))) (Nat.add (kind_num_params {first}) (kctor_num_fields {ctor}))")),
        ("_ctor_prefix", format!("Eq Bool (nig_pi_prefix_b (nrb_reference {first}) (kconst_type (kctor_sig {ctor}))) Bool.true")),
        ("_parameter_bound", format!("Le (kind_num_params {first}) (count_pi (kconst_type (kctor_sig {ctor})))")),
        ("facts", format!("NamedStrictAppFacts {RAW_BLOCK} (nig_param_levels (kconst_params (kind_sig {first}))) (nsi_member_name m) (count_pi (kconst_type (kctor_sig {ctor}))) (kind_num_params {first}) (kind_num_indices {member}) (return_type (kconst_type (kctor_sig {ctor})))")),
    ];
    assert_eq!(fields.len(), 16);
    let continuation = fields
        .iter()
        .map(|(name, ty)| format!("({name} : {ty})"))
        .collect::<Vec<_>>()
        .join(" ");
    (
        format!("forall {SELECTED_BINDERS}, {facts}"),
        format!("fun {SELECTED_BINDERS} => nwr_selected_constructor_from_raw us p ms base mi m j c run member_at ctor_at ({facts}) (fun (first_source : NamedMemberSource) {continuation} => facts)"),
    )
}

#[test]
fn raw_block_return_whole_success_and_selected16_consumer() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        checks::caller(
            &spec,
            "nwr_installed_return_of_raw",
            r"forall
 (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv),
 Eq Bool (nwr_raw_return_b us p ms) Bool.true ->
 Eq Bool (nrb_block_return_b (nsi_raw_install us p ms base) (nsi_names NamedMemberSource nsi_member_name ms)) Bool.true",
        );
        let (ty, body) = selected16_consumer();
        checks::tuple_ast("nwr_test_raw_selected16", &ty, &body);
        super::super::theorem(
            &mut spec,
            "nwr_test_raw_selected16",
            &ty,
            &body,
            "Test-only symbolic raw-whole to exact selected16 consumer",
        )
        .expect("actual sixteen-output consumer registers");
        checks::record(&spec, "nwr_test_raw_selected16", &ty, &body, Some(false));
        let selected = format!("nwr_test_raw_selected16 nrb_demo_levels {ONE} nsi_demo_sources IndCtorEnv.empty {ONE} nsi_demo_g {ONE} nsi_demo_cg2 nwr_demo_raw_success (Eq.refl (OptionType NamedMemberSource) (OptionType.some NamedMemberSource nsi_demo_g)) (Eq.refl (OptionType NamedCtorSource) (OptionType.some NamedCtorSource nsi_demo_cg2))");
        checks::caller(&spec, &selected, DEMO_FACTS);
        checks::caller(&spec, &format!("nig_strict_arity {BLOCK} (nig_param_levels nrb_demo_levels) nrb_demo_g (count_pi (nsi_ctor_type nsi_demo_cg2)) {ONE} (kind_num_indices {DEMO_IM}) (return_type (nsi_ctor_type nsi_demo_cg2)) ({selected})"),
            &format!("Eq Nat (list_length (kapp_args (return_type (nsi_ctor_type nsi_demo_cg2)))) (Nat.add {ONE} (kind_num_indices {DEMO_IM}))"));
        checks::caller(
            &spec,
            "nwr_demo_selected_second_ctor IndCtorEnv.empty",
            DEMO_FACTS,
        );
        checks::caller(
            &spec,
            "nwr_demo_installed_success IndCtorEnv.empty",
            &format!("Eq Bool (nrb_block_return_b nsi_demo_installed {BLOCK}) Bool.true"),
        );
    });
}

#[test]
fn raw_block_return_nonzero_positions_and_metadata() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (term, expected) in [
            (
                format!("nsi_at NamedMemberSource nsi_demo_sources {ONE}"),
                "OptionType.some NamedMemberSource nsi_demo_g".to_owned(),
            ),
            (
                format!("nsi_at NamedCtorSource (nsi_member_ctors nsi_demo_g) {ONE}"),
                "OptionType.some NamedCtorSource nsi_demo_cg2".to_owned(),
            ),
            (
                format!("nsi_at NamedCtorSource (nsi_member_ctors nsi_demo_g) {TWO}"),
                "OptionType.none NamedCtorSource".to_owned(),
            ),
            (
                format!("nrb_name_at {BLOCK} {ONE}"),
                "OptionType.some Name nrb_demo_g".to_owned(),
            ),
            (
                format!("nrb_name_at (kind_ctor_names {DEMO_IM}) {ONE}"),
                format!("OptionType.some Name (Name.str nrb_demo_g {ONE})"),
            ),
            (
                "kind_for nsi_demo_installed nrb_demo_g".to_owned(),
                format!("OptionType.some KIndMeta {DEMO_IM}"),
            ),
            (
                "kctor_for nsi_demo_installed (nsi_ctor_name nsi_demo_cg2)".to_owned(),
                format!("OptionType.some KCtorMeta {DEMO_CM}"),
            ),
            (format!("kind_all_names {DEMO_IM}"), BLOCK.to_owned()),
            (format!("kind_num_indices {DEMO_IM}"), ONE.to_owned()),
            (format!("kctor_index {DEMO_CM}"), ONE.to_owned()),
            (format!("kctor_num_fields {DEMO_CM}"), ONE.to_owned()),
            (format!("kctor_parent {DEMO_CM}"), "nrb_demo_g".to_owned()),
            (
                "count_pi (nsi_member_type nsi_demo_f)".to_owned(),
                ONE.to_owned(),
            ),
            (
                "count_pi (nsi_member_type nsi_demo_g)".to_owned(),
                TWO.to_owned(),
            ),
            (
                "count_pi (nsi_ctor_type nsi_demo_cg2)".to_owned(),
                TWO.to_owned(),
            ),
        ] {
            checks::computes(spec, &term, &expected);
        }
        checks::not_def_eq(spec, "nrb_demo_f", "nrb_demo_g");
        checks::not_def_eq(spec, "nsi_demo_cg", "nsi_demo_cg2");
        checks::caller(spec, "nsi_demo_second_ctor IndCtorEnv.empty",
            &format!("Eq (OptionType KCtorMeta) (kctor_for nsi_demo_installed (nsi_ctor_name nsi_demo_cg2)) (OptionType.some KCtorMeta {DEMO_CM})"));
        checks::caller(spec, "nfi_demo_second_family IndCtorEnv.empty",
            &format!("Eq (OptionType KIndMeta) (kind_for nsi_demo_installed nrb_demo_g) (OptionType.some KIndMeta {DEMO_IM})"));
    });
}

#[test]
fn raw_block_return_whole_guard_controls_and_empty_constructors() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (sources, expected) in [
            ("nsi_demo_sources", "Bool.true"),
            ("(ListType.nil NamedMemberSource)", "Bool.false"),
            ("nwr_empty_ctor_sources", "Bool.true"),
            ("nsi_demo_collision_sources", "Bool.false"),
            ("nwr_bad_other_sources", "Bool.false"),
            ("nwr_short_former_sources", "Bool.false"),
            ("nwr_wrong_level_sources", "Bool.false"),
        ] {
            checks::computes(
                spec,
                &format!("nwr_raw_return_b nrb_demo_levels {ONE} {sources}"),
                expected,
            );
        }
        // An empty constructor list is a successful inner all-fold, while an
        // empty outer block is refused by its separate nonempty condition.
        checks::computes(spec, "nwr_all_index_b NamedCtorSource (fun (_j : Nat) (_c : NamedCtorSource) => Bool.false) (ListType.nil NamedCtorSource)", "Bool.true");
        checks::computes(spec, "nwr_all_index_b NamedCtorSource (fun (_j : Nat) (_c : NamedCtorSource) => Bool.false) (ListType.cons NamedCtorSource nsi_demo_cf (ListType.nil NamedCtorSource))", "Bool.false");
        checks::computes(spec, &format!("nrb_block_return_b (nsi_raw_install nrb_demo_levels {ONE} nwr_empty_ctor_sources IndCtorEnv.empty) (nsi_names NamedMemberSource nsi_member_name nwr_empty_ctor_sources)"), "Bool.true");
        checks::caller(spec, "nwr_empty_ctor_installed_success IndCtorEnv.empty", &format!("Eq Bool (nrb_block_return_b (nsi_raw_install nrb_demo_levels {ONE} nwr_empty_ctor_sources IndCtorEnv.empty) (nsi_names NamedMemberSource nsi_member_name nwr_empty_ctor_sources)) Bool.true"));
        // G is locally acceptable with the fixed first reference, but another
        // member's wrong return head causes the complete raw guard to fail.
        let bad_block = "(nsi_names NamedMemberSource nsi_member_name nwr_bad_other_sources)";
        checks::computes(spec, &format!("nwr_member_fields_b nrb_demo_levels {ONE} {bad_block} (nsi_member_meta nrb_demo_levels {ONE} {bad_block} nwr_bad_other_member) {ONE} nsi_demo_g"), "Bool.true");
        checks::computes(
            spec,
            &format!("nwr_nonempty_b nrb_demo_levels {ONE} nwr_bad_other_sources"),
            "Bool.false",
        );
    });
}

#[test]
fn raw_block_return_unrelated_old_lookups_and_cross_kind_order() {
    run_with_stack(|| {
        let spec = shared_spec();
        checks::caller(spec, "nsi_demo_unrelated_old_lookup", &format!("forall (base : IndCtorEnv), Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install nrb_demo_levels {ONE} nsi_demo_sources base) nrb_demo_u) (kctor_for base nrb_demo_u)"));
        checks::caller(spec, "nfi_demo_unrelated_old_kind", &format!("forall (base : IndCtorEnv), Eq (OptionType KIndMeta) (kind_for (nsi_raw_install nrb_demo_levels {ONE} nsi_demo_sources base) nrb_demo_u) (kind_for base nrb_demo_u)"));
        let old_ctor = format!("(IndCtorEnv.addCtor IndCtorEnv.empty nrb_demo_u {DEMO_CM})");
        let old_kind = format!("(IndCtorEnv.addInd IndCtorEnv.empty nrb_demo_u {DEMO_IM})");
        checks::computes(spec, &format!("kctor_for (nsi_raw_install nrb_demo_levels {ONE} nsi_demo_sources {old_ctor}) nrb_demo_u"), &format!("OptionType.some KCtorMeta {DEMO_CM}"));
        checks::computes(spec, &format!("kind_for (nsi_raw_install nrb_demo_levels {ONE} nsi_demo_sources {old_kind}) nrb_demo_u"), &format!("OptionType.some KIndMeta {DEMO_IM}"));
        // Installation remains an ordered operation even for a colliding raw
        // input. These computations assert shadowing, not admission of it.
        checks::computes(spec, &format!("kctor_for (nsi_raw_install nrb_demo_levels {ONE} nsi_demo_collision_sources IndCtorEnv.empty) nrb_demo_cf"), "OptionType.none KCtorMeta");
        let colliding_member =
            "(NamedMemberSource.mk nrb_demo_cf nrb_demo_g_type (ListType.nil NamedCtorSource))";
        let reversed = format!("(ListType.cons NamedMemberSource {colliding_member} (ListType.cons NamedMemberSource nsi_demo_f (ListType.nil NamedMemberSource)))");
        checks::computes(spec, &format!("kind_for (nsi_raw_install nrb_demo_levels {ONE} {reversed} IndCtorEnv.empty) nrb_demo_cf"), "OptionType.none KIndMeta");
        checks::computes(spec, &format!("kctor_for (nsi_raw_install nrb_demo_levels {ONE} {reversed} IndCtorEnv.empty) nrb_demo_cf"), &format!("OptionType.some KCtorMeta (nsi_ctor_meta nrb_demo_levels {ONE} nrb_demo_f Nat.zero nsi_demo_cf)"));
        checks::computes(
            spec,
            &format!("nwr_raw_return_b nrb_demo_levels {ONE} {reversed}"),
            "Bool.false",
        );
    });
}
