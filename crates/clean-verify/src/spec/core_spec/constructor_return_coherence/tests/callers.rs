// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real model admission and source-image callers, not Rust admission execution.

use super::{checks, run_with_stack, shared_spec};

const ONE: &str = "(Nat.succ Nat.zero)";
const TWO: &str = "(Nat.succ (Nat.succ Nat.zero))";
const THREE: &str = "(Nat.succ (Nat.succ (Nat.succ Nat.zero)))";
const FOUR: &str = "(Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))";
const S1: &str = "(KExpr.sort (Level.succ Level.zero))";
const FAMILY: &str = "(KExpr.const kcre_prod_type_name (ListType.nil Level))";

fn named_return() -> String {
    format!("(KExpr.app (KExpr.app {FAMILY} (KExpr.bvar {THREE})) (KExpr.bvar {TWO}))")
}

#[test]
fn constructor_return_coherence_actual_admission_and_selected_spine() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (value, ty) in [
            (
                "rpa_family_typed",
                "Typing rpa_ind_ty (KExpr.sort (Level.imax rpa_u2 (Level.imax rpa_u2 rpa_u2)))",
            ),
            (
                "rpa_ctor_typed",
                "CtxTyping rpa_G0 rpa_ctor_ty (KExpr.sort rpa_ctor_level)",
            ),
            (
                "rpa_fields_bounded",
                "FieldsBounded rpa_u1 rpa_G0 rpa_two rpa_ctor_ty",
            ),
            (
                "rpa_well_formed",
                "WellFormedCtorDecls KEnv.empty Nat.zero rpa_two rpa_ind_ty rpa_ctors",
            ),
            ("rpa_extension", "InductiveExtension KEnv.empty rpa_env"),
            ("rpa_env_sound", "EnvSound rpa_env"),
            (
                "ac_existing_admitted_caller",
                "Eq Bool (return_args_wf_from Nat.zero Nat.zero (KExpr.bvar Nat.zero)) Bool.true",
            ),
        ] {
            checks::caller(spec, value, ty);
        }
        let found = "(Eq.refl (OptionType CtorDecl) (OptionType.some CtorDecl (CtorDecl.mk rpa_one rpa_ctor_ty)))";
        let selected = format!("KEnv.empty Nat.zero rpa_two rpa_ind_ty rpa_ctors rpa_well_formed Nat.zero rpa_one rpa_ctor_ty {found}");
        checks::caller(
            spec,
            &format!("arc_admitted_selected_arity {selected}"),
            &format!("Le {TWO} {FOUR}"),
        );
        let shape = "Eq KExpr (return_type rpa_ctor_ty) (arc_return_spine rpa_four rpa_two)";
        checks::caller(
            spec,
            &format!("arc_admitted_selected_spine {selected}"),
            shape,
        );
        checks::caller(spec,
            &format!("arc_sound_selected_spine KEnv.empty Nat.zero rpa_two rpa_ind_ty rpa_ctors rpa_env_sound Nat.zero rpa_one rpa_ctor_ty {found}"), shape);
        checks::caller(
            spec,
            "arc_return_guard_spine rpa_four rpa_two rpa_return rpa_uniform_from_admission",
            shape,
        );
        checks::caller(spec, "arc_prod_spine_from_admission", shape);
        checks::computes(
            spec,
            "ac_ctor_at rpa_ctors Nat.zero",
            "OptionType.some CtorDecl (CtorDecl.mk rpa_one rpa_ctor_ty)",
        );
        checks::computes(
            spec,
            &format!("ac_ctor_at rpa_ctors {ONE}"),
            "OptionType.none CtorDecl",
        );
    });
}

#[test]
fn constructor_return_coherence_full_underflow_guard_refuses() {
    run_with_stack(|| {
        let spec = shared_spec();
        let raw = format!("(arc_return_spine Nat.zero {ONE})");
        checks::computes(
            spec,
            &raw,
            "KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)",
        );
        checks::computes(spec, &format!("count_pi {raw}"), "Nat.zero");
        checks::computes(
            spec,
            &format!("return_args_wf_from Nat.zero {ONE} {raw}"),
            "Bool.true",
        );
        checks::computes(
            spec,
            &format!("nat_leb {ONE} (count_pi {raw})"),
            "Bool.false",
        );
        // The full admission guard rejects, despite the raw return guard passing.
        checks::computes(spec, &format!("ctor_return_wf_b {ONE} {raw}"), "Bool.false");
        checks::caller(
            spec,
            "arc_raw_underflow_guard_passes",
            &format!("Eq Bool (return_args_wf_from Nat.zero {ONE} {raw}) Bool.true"),
        );
        checks::caller(
            spec,
            "arc_underflow_arity_refuses",
            &format!("Eq Bool (nat_leb {ONE} Nat.zero) Bool.false"),
        );
        checks::caller(
            spec,
            &format!("arc_return_guard_spine Nat.zero {ONE} {raw} arc_raw_underflow_guard_passes"),
            &format!("Eq KExpr {raw} {raw}"),
        );
        checks::computes(spec, "ac_env_returns_b ac_bad_env", "Bool.false");
        checks::computes(
            spec,
            &format!("ctor_return_wf_b {ONE} ac_bad_ct"),
            "Bool.false",
        );
        // Do not invent a witness for this intentionally uninhabited premise.
        checks::caller(
            spec,
            "ac_nonuniform_environment_refused",
            "EnvSound ac_bad_env -> Empty",
        );
    });
}

#[test]
fn constructor_return_coherence_emitted_prod_closes_self_at_depth_four() {
    run_with_stack(|| {
        let spec = shared_spec();
        let result = named_return();
        let signature = format!("(KExpr.pi {S1} (KExpr.pi {S1} (KExpr.pi (KExpr.bvar {ONE}) (KExpr.pi (KExpr.bvar {ONE}) {result}))))");
        checks::computes(
            spec,
            "kconst_type kcre_prod_type_signature",
            &format!("KExpr.pi {S1} (KExpr.pi {S1} {S1})"),
        );
        checks::computes(spec, "kconst_type kcre_prod_mk_signature", &signature);
        checks::computes(spec, "count_pi (kconst_type kcre_prod_mk_signature)", FOUR);
        checks::computes(
            spec,
            &format!("instantiate rpa_ctor_ty {FAMILY}"),
            &signature,
        );
        checks::computes(
            spec,
            &format!("instantiate_at (return_type rpa_ctor_ty) {FAMILY} {FOUR}"),
            &result,
        );
        checks::computes(
            spec,
            "return_type (kconst_type kcre_prod_mk_signature)",
            &result,
        );
        checks::computes(
            spec,
            "kapp_fn (return_type (kconst_type kcre_prod_mk_signature))",
            FAMILY,
        );
        checks::computes(spec, "kapp_args (return_type (kconst_type kcre_prod_mk_signature))",
            &format!("ListType.cons KExpr (KExpr.bvar {THREE}) (ListType.cons KExpr (KExpr.bvar {TWO}) (ListType.nil KExpr))"));
        checks::caller(
            spec,
            "rpa_close_self",
            &format!(
                "Eq KExpr (instantiate rpa_ctor_ty {FAMILY}) (kconst_type kcre_prod_mk_signature)"
            ),
        );
        checks::caller(
            spec,
            "arc_prod_close_canonical",
            &format!(
                "Eq KExpr (instantiate_at (return_type rpa_ctor_ty) {FAMILY} {FOUR}) {result}"
            ),
        );
        checks::caller(
            spec,
            "arc_prod_source_return",
            &format!("Eq KExpr (return_type (kconst_type kcre_prod_mk_signature)) {result}"),
        );
        checks::not_def_eq(
            spec,
            &result,
            &format!("KExpr.app (KExpr.app {FAMILY} (KExpr.bvar {TWO})) (KExpr.bvar {THREE})"),
        );
        checks::not_def_eq(
            spec,
            FAMILY,
            "KExpr.const kcre_prod_mk_name (ListType.nil Level)",
        );
    });
}

#[test]
fn constructor_return_coherence_actual_names_signatures_and_metadata() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (source, expected) in [
            ("rpa_source_name Nat.zero", "kcre_prod_type_name"),
            ("rpa_source_name rpa_one", "kcre_prod_mk_name"),
            (
                "name_eqb kcre_prod_type_name kcre_prod_mk_name",
                "Bool.false",
            ),
            (
                "kconst_params kcre_prod_type_signature",
                "ListType.nil Name",
            ),
            ("kconst_params kcre_prod_mk_signature", "ListType.nil Name"),
            ("kind_sig kcre_prod_ind_meta", "kcre_prod_type_signature"),
            ("kind_num_params kcre_prod_ind_meta", TWO),
            ("kind_num_indices kcre_prod_ind_meta", "Nat.zero"),
            (
                "kind_ctor_names kcre_prod_ind_meta",
                "ListType.cons Name kcre_prod_mk_name (ListType.nil Name)",
            ),
            ("kctor_sig kcre_prod_ctor_meta", "kcre_prod_mk_signature"),
            ("kctor_parent kcre_prod_ctor_meta", "kcre_prod_type_name"),
            ("kctor_num_params kcre_prod_ctor_meta", TWO),
            ("kctor_num_fields kcre_prod_ctor_meta", TWO),
            ("kctor_index kcre_prod_ctor_meta", "Nat.zero"),
            (
                "kind_for kcre_ind_ctor_env kcre_prod_type_name",
                "OptionType.some KIndMeta kcre_prod_ind_meta",
            ),
            (
                "kctor_for kcre_ind_ctor_env kcre_prod_mk_name",
                "OptionType.some KCtorMeta kcre_prod_ctor_meta",
            ),
            (
                "kind_for kcre_ind_ctor_env kcre_prod_mk_name",
                "OptionType.none KIndMeta",
            ),
            (
                "kctor_for kcre_ind_ctor_env kcre_prod_type_name",
                "OptionType.none KCtorMeta",
            ),
            (
                "kcre_ind_ctor_tenv kcre_prod_type_name",
                "OptionType.some KConstSig kcre_prod_type_signature",
            ),
            (
                "kcre_ind_ctor_tenv kcre_prod_mk_name",
                "OptionType.some KConstSig kcre_prod_mk_signature",
            ),
        ] {
            checks::computes(spec, source, expected);
        }
        checks::caller(spec, "rpa_ctor_signature",
            &format!("Eq KConstSig (KConstSig.mk (ListType.nil Name) (instantiate rpa_ctor_ty {FAMILY})) (kctor_sig kcre_prod_ctor_meta)"));
        checks::not_def_eq(spec, "kcre_prod_type_name", "kcre_prod_mk_name");
    });
}

#[test]
fn constructor_return_coherence_connected_consumer_uses_admission() {
    run_with_stack(|| {
        let spec = shared_spec();
        // The continuation consumes four facts supplied by the proved caller.
        // Its C is genuinely Type-valued EnvSound, not a Prop used as Type.
        let source = format!(
            "rpa_connected_admission (EnvSound rpa_env) \
             (fun (sound : EnvSound rpa_env) \
              (_guard : Eq Bool (return_args_wf_from (count_pi rpa_ctor_ty) rpa_two (return_type rpa_ctor_ty)) Bool.true) \
              (_signature : Eq KConstSig (KConstSig.mk (ListType.nil Name) (instantiate rpa_ctor_ty {FAMILY})) (kctor_sig kcre_prod_ctor_meta)) \
              (_lookup : Eq (OptionType KCtorMeta) (kctor_for kcre_ind_ctor_env kcre_prod_mk_name) (OptionType.some KCtorMeta kcre_prod_ctor_meta)) => sound)"
        );
        checks::caller(spec, &source, "EnvSound rpa_env");
    });
}
