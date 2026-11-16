// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual generic self-closing callers within the existing admission fragment.
//! The chosen Name is connected to emitted metadata only by the finite Prod
//! witness; no general named/indexed admission or projection typing is claimed.

use super::super::{generic_closing as cohort, theorem};
use super::{assert_absent, checks, run_with_stack, shared_spec};

const FAMILY: &str = "(KExpr.const kcre_prod_type_name (@ListType.nil Level))";
const ONE: &str = "(Nat.succ Nat.zero)";

fn named_return() -> String {
    format!("(KExpr.app (KExpr.app {FAMILY} (KExpr.bvar rpa_three)) (KExpr.bvar rpa_two))")
}

#[test]
fn constructor_return_coherence_generic_closing_admitted_source() {
    run_with_stack(|| {
        let spec = shared_spec();
        let found = "(@Eq.refl (OptionType CtorDecl) (@OptionType.some CtorDecl (CtorDecl.mk rpa_one rpa_ctor_ty)))";
        let selected = format!("KEnv.empty Nat.zero rpa_two rpa_ind_ty rpa_ctors rpa_well_formed Nat.zero rpa_one rpa_ctor_ty {found}");
        let raw_closed = format!("(instantiate rpa_ctor_ty {FAMILY})");
        let named = "(gcc_named_return_spine kcre_prod_type_name rpa_four rpa_two)";
        let slots = named_return();

        // Both the raw return shape and the arity are derived from this actual
        // admitted selected constructor; no desired endpoint is a premise.
        checks::caller(
            spec,
            &format!("gcc_admitted_return_named {selected} kcre_prod_type_name"),
            &format!("@Eq KExpr (return_type {raw_closed}) {named}"),
        );
        checks::caller(
            spec,
            &format!("gcc_admitted_closed_arity {selected} kcre_prod_type_name"),
            &format!("Le rpa_two (count_pi {raw_closed})"),
        );
        checks::caller(
            spec,
            &format!("gcc_close_return_spine kcre_prod_type_name rpa_four rpa_two (arc_admitted_selected_arity {selected})"),
            &format!("@Eq KExpr (instantiate_at (arc_return_spine rpa_four rpa_two) {FAMILY} rpa_four) {named}"),
        );
        checks::caller(
            spec,
            "gcc_count_pi_close_const rpa_ctor_ty kcre_prod_type_name Nat.zero",
            &format!("@Eq Nat (count_pi {raw_closed}) (count_pi rpa_ctor_ty)"),
        );
        checks::caller(
            spec,
            "gcc_return_type_close_self rpa_ctor_ty kcre_prod_type_name",
            &format!("@Eq KExpr (return_type {raw_closed}) (instantiate_at (return_type rpa_ctor_ty) {FAMILY} (count_pi rpa_ctor_ty))"),
        );
        for (value, ty) in [
            (
                "gcc_prod_admitted_named",
                format!("@Eq KExpr (return_type {raw_closed}) {named}"),
            ),
            (
                "gcc_prod_source_named",
                format!("@Eq KExpr (return_type (kconst_type kcre_prod_mk_signature)) {named}"),
            ),
            (
                "gcc_prod_source_slots",
                format!("@Eq KExpr (return_type (kconst_type kcre_prod_mk_signature)) {slots}"),
            ),
            (
                "gcc_prod_source_count",
                "@Eq Nat (count_pi (kconst_type kcre_prod_mk_signature)) rpa_four".to_string(),
            ),
            (
                "gcc_prod_closed_arity",
                format!("Le rpa_two (count_pi {raw_closed})"),
            ),
        ] {
            checks::caller(spec, value, &ty);
        }

        // These are actual data computations, separate from proof-constant
        // inference. The named data definition must remain transparent.
        checks::computes(spec, named, &slots);
        checks::computes(spec, &raw_closed, "kconst_type kcre_prod_mk_signature");
        checks::computes(spec, &format!("count_pi {raw_closed}"), "rpa_four");
        checks::computes(
            spec,
            "return_type (kconst_type kcre_prod_mk_signature)",
            &slots,
        );
        checks::computes(spec, &format!("kapp_fn {named}"), FAMILY);
        checks::computes(
            spec,
            &format!("kapp_args {named}"),
            "@ListType.cons KExpr (KExpr.bvar rpa_three) (@ListType.cons KExpr (KExpr.bvar rpa_two) (@ListType.nil KExpr))",
        );
    });
}

#[test]
fn constructor_return_coherence_generic_closing_underflow_boundary() {
    run_with_stack(|| {
        let spec = shared_spec();
        let raw = format!("(arc_return_spine Nat.zero {ONE})");
        let closed = format!("(instantiate_at {raw} {FAMILY} Nat.zero)");
        let captured = format!("(KExpr.app {FAMILY} {FAMILY})");
        let false_endpoint = format!("(gcc_named_return_spine kcre_prod_type_name Nat.zero {ONE})");

        checks::computes(
            spec,
            &format!("return_args_wf_from Nat.zero {ONE} {raw}"),
            "Bool.true",
        );
        // Test the complete admission guard, not just its nat_leb component.
        checks::computes(spec, &format!("ctor_return_wf_b {ONE} {raw}"), "Bool.false");
        checks::caller(
            spec,
            "gcc_underflow_raw_guard_passes",
            &format!("@Eq Bool (return_args_wf_from Nat.zero {ONE} {raw}) Bool.true"),
        );
        checks::caller(
            spec,
            "gcc_underflow_full_guard_refuses",
            &format!("@Eq Bool (ctor_return_wf_b {ONE} {raw}) Bool.false"),
        );
        checks::caller(
            spec,
            "gcc_underflow_captures_parameter kcre_prod_type_name",
            &format!("@Eq KExpr {closed} {captured}"),
        );
        checks::computes(spec, &closed, &captured);
        checks::computes(
            spec,
            &false_endpoint,
            &format!("KExpr.app {FAMILY} (KExpr.bvar Nat.zero)"),
        );
        checks::not_def_eq(spec, &closed, &false_endpoint);
    });
}

#[test]
fn constructor_return_coherence_generic_closing_forgeries_not_registered() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        let original_count = spec.definitions().len();
        assert_eq!(
            cohort::NEGATIVE_CONTROLS
                .iter()
                .map(|&(name, _, _)| name)
                .collect::<Vec<_>>(),
            [
                "gcc_forged_wrong_family",
                "gcc_forged_wrong_order",
                "gcc_forged_underflow_endpoint",
            ]
        );
        for &(name, ty, body) in cohort::NEGATIVE_CONTROLS {
            checks::tuple_ast(name, ty, body);
            assert_absent(&spec, name);
            let error = theorem(
                &mut spec,
                name,
                ty,
                body,
                "Actual generic constructor-closing false endpoint",
            )
            .expect_err("well-parsed wrong family/order/captured endpoint must fail");
            checks::type_mismatch(name, error);
            assert_absent(&spec, name);
            assert_eq!(
                spec.definitions().len(),
                original_count,
                "failed registration inserts nothing"
            );
        }
    });
}
