// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-check pins for the subject-reduction bundle
//! (`subject_reduction_bundle.rs`, Aristotle SubjRed.lean port). Confirms the
//! `TypingEnvCoherent` interface, the weakening tower, the substitution tower,
//! and the preservation theorems register, are DerivedProved with EMPTY axiom
//! closure, and re-typecheck against the live kernel environment.

use crate::test_utils::build_spec_with_stack;
use crate::Specification;

fn build_spec() -> Specification {
    build_spec_with_stack()
}

/// Paren-balance guard for the generated proof-term strings (fast failure
/// with a location, instead of a deep parse error inside spec build).
#[test]
fn test_subject_reduction_bundle_terms_paren_balanced() {
    for (name, term) in [
        ("ctx_wk_lookup", super::ctx_wk_lookup_value()),
        ("weaken_gen", super::weaken_gen_value()),
        ("def_eq_psubst", super::def_eq_psubst_value()),
        ("subst_typing_up", super::subst_typing_up_value()),
        ("subst_typing_scons", super::subst_typing_scons_value()),
        ("substitution_general", super::substitution_general_value()),
        ("ctx_def_eq_lookup", super::ctx_def_eq_lookup_value()),
        ("ctx_conv", super::ctx_conv_value()),
        ("ctx_app_gen", super::ctx_app_gen_value()),
        ("ctx_lam_gen", super::ctx_lam_gen_value()),
        ("ctx_pi_gen", super::ctx_pi_gen_value()),
        ("ctx_let_gen", super::ctx_let_gen_value()),
        (
            "delta_preserves_typing_ctx",
            super::delta_preserves_typing_ctx_value(),
        ),
        (
            "srb_beta_redex_preserves",
            super::srb_beta_redex_preserves_value(),
        ),
        (
            "beta_reduces_preserves_typing_ctx",
            super::beta_reduces_preserves_typing_ctx_value(),
        ),
    ] {
        let mut depth: i64 = 0;
        let mut min_at = 0usize;
        for (pos, ch) in term.chars().enumerate() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth < 0 {
                        min_at = pos;
                        break;
                    }
                }
                _ => {}
            }
        }
        assert!(
            depth == 0,
            "{name}: unbalanced parens (final depth {depth}, first negative at {min_at});\n\
             term:\n{term}"
        );
    }
}

/// Inductives + generated recursors/constructors of the bundle register.
#[test]
fn test_subject_reduction_bundle_inductives_registered() {
    let spec = build_spec();
    for name in [
        "TypingEnvCoherent",
        "TypingEnvCoherent.mk",
        "TypingEnvCoherent.rec",
        "CtxWk",
        "CtxWk.zero",
        "CtxWk.succ",
        "CtxWk.rec",
        "CtxDefEq",
        "CtxDefEq.nil",
        "CtxDefEq.cons",
        "CtxDefEq.rec",
        "wkpos",
        "SubstTyping",
        "srb_app_fn",
        "srb_app_arg",
        "srb_lam_ty",
        "srb_lam_body",
        "srb_pi_dom",
        "srb_pi_cod",
        "srb_sort_ne_let",
        "srb_bvar_ne_let",
        "srb_const_ne_let",
        "subject_reduction_ctx_motive",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the subject-reduction bundle"
        );
    }
}

/// Every DerivedProved lemma of the bundle carries a proof term, declares an
/// empty axiom closure, and re-typechecks in the live kernel environment.
#[test]
fn test_subject_reduction_bundle_reverifies() {
    let spec = build_spec();
    for name in [
        // interface projectors
        "tec_tenv_psubst_closed",
        "tec_tenv_lift_closed",
        "tec_delta_psubst",
        "tec_iota_psubst",
        "tec_defval_typed",
        "tec_iota_typed",
        // wkpos + lift helpers
        "wkpos_zero",
        "wkpos_rec_succ",
        "wkpos_succ_succ",
        "lift_bvar_wkpos_rec",
        "lift_at_bvar_wkpos",
        "lift_exchange_zero",
        "lift_instantiate_zero",
        // weakening tower
        "ctx_wk_lookup",
        "weaken_gen",
        "weaken1",
        // def_eq_psubst + substitution tower
        "def_eq_psubst",
        "subst_typing_id",
        "subst_typing_up",
        "subst_typing_scons",
        "substitution_general",
        "substitution_typing_ctx",
        // context conversion
        "ctx_def_eq_refl",
        "ctx_def_eq_lookup",
        "ctx_conv",
        // generation (const_ne_* discriminations are reused from
        // par_reduces_d_diamond, not re-registered here)
        "ctx_app_gen",
        "ctx_lam_gen",
        "ctx_pi_gen",
        // let promotion (task #28): let generation + its srb-lane discriminations
        "ctx_let_gen",
        "srb_sort_ne_let",
        "srb_bvar_ne_let",
        "srb_const_ne_let",
        // preservation
        "opt_case_type",
        "delta_preserves_typing_ctx",
        "srb_beta_redex_preserves",
        "beta_reduces_preserves_typing_ctx",
        "subject_reduction_ctx",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} must not be an axiom");
        assert!(def.value_src.is_some(), "{name} must carry a proof term");
        assert!(
            def.axiom_deps.is_empty(),
            "{name} must declare empty axiom closure: {:?}",
            def.axiom_deps
        );
        spec.verify_definition(name)
            .unwrap_or_else(|e| panic!("{name} should re-typecheck in the spec env: {e:?}"));
    }
}
