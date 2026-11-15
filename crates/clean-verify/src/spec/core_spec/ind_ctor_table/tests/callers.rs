// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Callers over captured Eq/Prod metadata and arbitrary shared tables.
//! Cross-kind collisions below are algebraic controls, not admitted environments.

use super::checks;
use crate::test_utils::{run_with_stack, shared_spec};

const ENV: &str = "(red_ind_ctor the_red_env)";
const INSTALLED: &str = "(ict_append (red_ind_ctor the_red_env) ict_eq_updates)";
const FAMILY: &str = "kcre_eq_type_name";
const IM: &str = "kcre_eq_ind_meta";
const CN: &str = "kcre_eq_refl_name";
const CM: &str = "kcre_eq_refl_meta";
const ONE: &str = "(Nat.succ Nat.zero)";
const TWO: &str = "(Nat.succ (Nat.succ Nat.zero))";

#[test]
fn ind_ctor_table_actual_eq_append_uses_captured_metadata() {
    run_with_stack(|| {
        let spec = shared_spec();
        // The aliases come from the actual source capture in red_env_reflect.
        // ict_eq_updates is just these two updates, not the full captured table.
        checks::computes(spec, ENV, "kcre_ind_ctor_env");
        checks::computes(
            spec,
            "ict_eq_updates",
            &format!(
                "IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty {FAMILY} {IM}) {CN} {CM}"
            ),
        );
        for env in [ENV, INSTALLED] {
            for (lookup, name, expected) in [
                ("kind_for", FAMILY, format!("OptionType.some KIndMeta {IM}")),
                ("kctor_for", CN, format!("OptionType.some KCtorMeta {CM}")),
                ("kind_for", CN, "OptionType.none KIndMeta".to_owned()),
                ("kctor_for", FAMILY, "OptionType.none KCtorMeta".to_owned()),
            ] {
                checks::computes(spec, &format!("{lookup} {env} {name}"), &expected);
            }
        }
        for (term, expected) in [
            (
                format!("kind_sig {IM}"),
                "kcre_eq_type_signature".to_owned(),
            ),
            (
                format!("kctor_sig {CM}"),
                "kcre_eq_refl_signature".to_owned(),
            ),
            (format!("kctor_parent {CM}"), FAMILY.to_owned()),
            (format!("kind_num_params {IM}"), TWO.to_owned()),
            (format!("kind_num_indices {IM}"), ONE.to_owned()),
            (format!("kctor_num_params {CM}"), TWO.to_owned()),
            (format!("kctor_num_fields {CM}"), "Nat.zero".to_owned()),
            (format!("kctor_index {CM}"), "Nat.zero".to_owned()),
            (
                format!("kind_all_names {IM}"),
                format!("ListType.cons Name {FAMILY} (ListType.nil Name)"),
            ),
            (
                format!("kind_ctor_names {IM}"),
                format!("ListType.cons Name {CN} (ListType.nil Name)"),
            ),
            (
                format!("kcre_ind_ctor_tenv {FAMILY}"),
                "OptionType.some KConstSig kcre_eq_type_signature".to_owned(),
            ),
            (
                format!("kcre_ind_ctor_tenv {CN}"),
                "OptionType.some KConstSig kcre_eq_refl_signature".to_owned(),
            ),
        ] {
            checks::computes(spec, &term, &expected);
        }
        checks::not_def_eq(spec, FAMILY, CN);
        checks::caller(
            spec,
            &format!("ict_eq_kind {ENV}"),
            &format!("Eq (OptionType KIndMeta) (kind_for {INSTALLED} {FAMILY}) (OptionType.some KIndMeta {IM})"),
        );
        checks::caller(
            spec,
            &format!("ict_eq_ctor {ENV}"),
            &format!("Eq (OptionType KCtorMeta) (kctor_for {INSTALLED} {CN}) (OptionType.some KCtorMeta {CM})"),
        );
    });
}

#[test]
fn ind_ctor_table_symbolic_unequal_name_callers_and_registration() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        for (prefix, lookup, meta) in [
            ("kind", "kind_for", "KIndMeta"),
            ("ctor", "kctor_for", "KCtorMeta"),
        ] {
            checks::caller(
                &spec,
                &format!("fun (base updates : IndCtorEnv) (q : Name) => ict_{prefix}_append updates base q"),
                &format!("forall (base updates : IndCtorEnv) (q : Name), Eq (OptionType {meta}) ({lookup} (ict_append base updates) q) (Bool.rec (fun (_b : Bool) => OptionType {meta}) ({lookup} base q) ({lookup} updates q) (ict_has_name_b updates q))"),
            );
            for (insert, suffix, inserted_meta) in [
                ("addInd", "ind", "KIndMeta"),
                ("addCtor", "ctor", "KCtorMeta"),
            ] {
                checks::caller(
                    &spec,
                    &format!("fun (base : IndCtorEnv) (n q : Name) (m : {inserted_meta}) (different : Eq Bool (name_eqb n q) Bool.false) => ict_{prefix}_add_{suffix}_other base n q m different"),
                    &format!("forall (base : IndCtorEnv) (n q : Name) (m : {inserted_meta}), Eq Bool (name_eqb n q) Bool.false -> Eq (OptionType {meta}) ({lookup} (IndCtorEnv.{insert} base n m) q) ({lookup} base q)"),
                );
            }
            for (branch, flag, endpoint) in
                [("fresh", "false", "base"), ("seen", "true", "updates")]
            {
                checks::caller(
                    &spec,
                    &format!("fun (base updates : IndCtorEnv) (q : Name) (h : Eq Bool (ict_has_name_b updates q) Bool.{flag}) => ict_{prefix}_append_{branch} updates base q h"),
                    &format!("forall (base updates : IndCtorEnv) (q : Name), Eq Bool (ict_has_name_b updates q) Bool.{flag} -> Eq (OptionType {meta}) ({lookup} (ict_append base updates) q) ({lookup} {endpoint} q)"),
                );
            }
        }
        // Compose both insertion kinds at an unrelated symbolic query. The
        // only assumption concerns names; neither lookup equation is supplied.
        let ty = r"forall (base : IndCtorEnv) (n q : Name) (im : KIndMeta) (cm : KCtorMeta),
 Eq Bool (name_eqb n q) Bool.false ->
 Eq (OptionType KIndMeta) (kind_for (IndCtorEnv.addCtor (IndCtorEnv.addInd base n im) n cm) q) (kind_for base q)";
        let body = r"fun (base : IndCtorEnv) (n q : Name) (im : KIndMeta) (cm : KCtorMeta)
 (different : Eq Bool (name_eqb n q) Bool.false) =>
 Eq.trans (OptionType KIndMeta)
  (kind_for (IndCtorEnv.addCtor (IndCtorEnv.addInd base n im) n cm) q)
  (kind_for (IndCtorEnv.addInd base n im) q) (kind_for base q)
  (ict_kind_add_ctor_other (IndCtorEnv.addInd base n im) n q cm different)
  (ict_kind_add_ind_other base n q im different)";
        super::super::theorem(
            &mut spec,
            "ict_test_symbolic_two_insertions_preserve_other",
            ty,
            body,
            "Test-only composition of two insertion lemmas at an unequal name",
        )
        .expect("symbolic composed caller registers");
        checks::record(
            &spec,
            "ict_test_symbolic_two_insertions_preserve_other",
            ty,
            body,
            Some(true),
        );
    });
}

#[test]
fn ind_ctor_table_cross_kind_shadowing_and_append_order() {
    run_with_stack(|| {
        let spec = shared_spec();
        // Deliberate name collisions need no admission or environment-soundness
        // premise for the table equations. They are not legal source blocks.
        let ctor_last = format!("(IndCtorEnv.addCtor ict_eq_updates {FAMILY} {CM})");
        let ind_last = format!("(IndCtorEnv.addInd ict_eq_updates {CN} {IM})");
        for (updates, name, kind_result, ctor_result) in [
            (
                &ctor_last,
                FAMILY,
                "OptionType.none KIndMeta".to_owned(),
                format!("OptionType.some KCtorMeta {CM}"),
            ),
            (
                &ind_last,
                CN,
                format!("OptionType.some KIndMeta {IM}"),
                "OptionType.none KCtorMeta".to_owned(),
            ),
        ] {
            let installed = format!("(ict_append {ENV} {updates})");
            checks::computes(spec, &format!("kind_for {installed} {name}"), &kind_result);
            checks::computes(spec, &format!("kctor_for {installed} {name}"), &ctor_result);
            checks::computes(
                spec,
                &format!("ict_has_name_b {updates} {name}"),
                "Bool.true",
            );
        }
        checks::caller(
            spec,
            &format!("ict_eq_ctor_shadows_ind {ENV}"),
            &format!("Eq (OptionType KIndMeta) (kind_for (ict_append {ENV} {ctor_last}) {FAMILY}) (OptionType.none KIndMeta)"),
        );
        checks::caller(
            spec,
            &format!("ict_eq_ind_shadows_ctor {ENV}"),
            &format!("Eq (OptionType KCtorMeta) (kctor_for (ict_append {ENV} {ind_last}) {CN}) (OptionType.none KCtorMeta)"),
        );
        let conflict = format!("(IndCtorEnv.addCtor IndCtorEnv.empty {FAMILY} {CM})");
        let eq_last = format!("(ict_append {conflict} ict_eq_updates)");
        let conflict_last = format!("(ict_append ict_eq_updates {conflict})");
        for (table, kind_result, ctor_result) in [
            (
                &eq_last,
                format!("OptionType.some KIndMeta {IM}"),
                "OptionType.none KCtorMeta".to_owned(),
            ),
            (
                &conflict_last,
                "OptionType.none KIndMeta".to_owned(),
                format!("OptionType.some KCtorMeta {CM}"),
            ),
        ] {
            checks::computes(spec, &format!("kind_for {table} {FAMILY}"), &kind_result);
            checks::computes(spec, &format!("kctor_for {table} {FAMILY}"), &ctor_result);
        }
        checks::not_def_eq(
            spec,
            &format!("kind_for {eq_last} {FAMILY}"),
            &format!("kind_for {conflict_last} {FAMILY}"),
        );
    });
}

#[test]
fn ind_ctor_table_has_name_tracks_both_kinds() {
    run_with_stack(|| {
        let spec = shared_spec();
        for name in [FAMILY, CN, "Name.anonymous"] {
            checks::computes(
                spec,
                &format!("ict_has_name_b IndCtorEnv.empty {name}"),
                "Bool.false",
            );
        }
        for (name, expected) in [
            (FAMILY, "Bool.true"),
            (CN, "Bool.true"),
            ("Name.anonymous", "Bool.false"),
            ("kcre_prod_type_name", "Bool.false"),
            ("kcre_prod_mk_name", "Bool.false"),
        ] {
            checks::computes(
                spec,
                &format!("ict_has_name_b ict_eq_updates {name}"),
                expected,
            );
        }
        // A wrong-kind lookup returning none does not make a name fresh.
        for (insert, name, meta, lookup, result_type) in [
            ("addCtor", FAMILY, CM, "kind_for", "KIndMeta"),
            ("addInd", CN, IM, "kctor_for", "KCtorMeta"),
        ] {
            let stream = format!("(IndCtorEnv.{insert} IndCtorEnv.empty {name} {meta})");
            checks::computes(
                spec,
                &format!("ict_has_name_b {stream} {name}"),
                "Bool.true",
            );
            checks::computes(
                spec,
                &format!("{lookup} {stream} {name}"),
                &format!("OptionType.none {result_type}"),
            );
            checks::not_def_eq(
                spec,
                &format!("ict_has_name_b {stream} {name}"),
                "Bool.false",
            );
        }
        checks::caller(
            spec,
            &format!("ict_eq_unrelated_kind {ENV}"),
            &format!("Eq (OptionType KIndMeta) (kind_for {INSTALLED} Name.anonymous) (kind_for {ENV} Name.anonymous)"),
        );
    });
}

#[test]
fn ind_ctor_table_eq_append_preserves_actual_prod_entries() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (prefix, lookup, name, meta_type, meta) in [
            (
                "kind",
                "kind_for",
                "kcre_prod_type_name",
                "KIndMeta",
                "kcre_prod_ind_meta",
            ),
            (
                "ctor",
                "kctor_for",
                "kcre_prod_mk_name",
                "KCtorMeta",
                "kcre_prod_ctor_meta",
            ),
        ] {
            for eq_name in [FAMILY, CN] {
                checks::computes(spec, &format!("name_eqb {eq_name} {name}"), "Bool.false");
            }
            checks::computes(
                spec,
                &format!("ict_has_name_b ict_eq_updates {name}"),
                "Bool.false",
            );
            for table in [ENV, INSTALLED] {
                checks::computes(
                    spec,
                    &format!("{lookup} {table} {name}"),
                    &format!("OptionType.some {meta_type} {meta}"),
                );
            }
            checks::caller(
                spec,
                &format!("ict_{prefix}_append_fresh ict_eq_updates {ENV} {name} (Eq.refl Bool Bool.false)"),
                &format!("Eq (OptionType {meta_type}) ({lookup} {INSTALLED} {name}) (OptionType.some {meta_type} {meta})"),
            );
        }
        for (source, expected) in [
            ("kind_sig kcre_prod_ind_meta", "kcre_prod_type_signature"),
            ("kctor_sig kcre_prod_ctor_meta", "kcre_prod_mk_signature"),
            ("kctor_parent kcre_prod_ctor_meta", "kcre_prod_type_name"),
            ("kind_num_params kcre_prod_ind_meta", TWO),
            ("kind_num_indices kcre_prod_ind_meta", "Nat.zero"),
            ("kctor_num_fields kcre_prod_ctor_meta", TWO),
            (
                "kind_ctor_names kcre_prod_ind_meta",
                "ListType.cons Name kcre_prod_mk_name (ListType.nil Name)",
            ),
        ] {
            checks::computes(spec, source, expected);
        }
        // The nonempty Prod lookup distinguishes the two-update stream from
        // the actual table; the stream has no Prod declaration to look up.
        checks::computes(
            spec,
            "kind_for ict_eq_updates kcre_prod_type_name",
            "OptionType.none KIndMeta",
        );
        checks::not_def_eq(
            spec,
            "kind_for ict_eq_updates kcre_prod_type_name",
            &format!("kind_for {ENV} kcre_prod_type_name"),
        );
    });
}
