// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests verifying DefEq.beta and DefEq.rec are UNTYPED (no beta typing
//! premises) after the church_rosser_whnf retirement (#2859). The typed beta
//! evidence now lives in TypedDefEq.beta; the raw DefEq lane carries the literal
//! kernel reduction rule. Part of #2859 (supersedes the #2872 typed-premise
//! design).

use crate::spec::types::ProofStatus;
use crate::test_utils::build_spec_with_stack;

// TEMP DIAGNOSTIC DUMP — remove before commit.
#[test]
fn _dump_generated_recursors() {
    let spec = build_spec_with_stack();
    for n in [
        "Typing.rec",
        "TypedDefEq.rec",
        "DefinitionalExtension.rec",
        "ProdType.rec",
    ] {
        if let Some(d) = spec.definitions().get(n) {
            eprintln!(
                "==== {n} (is_axiom={}) ====\n{:?}\n",
                d.is_axiom, d.elaborated_type
            );
        } else {
            eprintln!("==== {n}: MISSING ====");
        }
    }
}

// =========================================================================
// DefEq.beta is untyped (#2859 — church_rosser_whnf retirement)
// =========================================================================

#[test]
fn test_def_eq_beta_is_untyped() {
    let spec = build_spec_with_stack();
    let beta = spec
        .definitions()
        .get("DefEq.beta")
        .expect("DefEq.beta should exist");

    // DefEq is now a genuine `add_inductive`; DefEq.beta is a kernel-generated
    // constructor (not a value-less axiom). Its `type_src` is the
    // "(constructor of DefEq)" placeholder, so faithfulness is checked against the
    // kernel-ELABORATED constructor type (same pattern as the DefEqJoinable /
    // KernelDefEqAccepts inductive-faithfulness tests).
    assert!(
        !beta.is_axiom,
        "DefEq.beta should be a kernel-generated constructor, not an axiom"
    );

    // #2859: DefEq.beta is the literal UNTYPED beta rule —
    //   forall (A b a : KExpr), DefEq (app (lam A b) a) (instantiate b a).
    // It must carry NO typing witnesses (those moved to TypedDefEq.beta).
    let beta_ty = format!(
        "{:?}",
        beta.elaborated_type
            .as_ref()
            .expect("DefEq.beta should record its elaborated type")
    );
    assert!(
        !beta_ty.contains("Typing"),
        "DefEq.beta must carry no typing premises (untyped #2859): {beta_ty}"
    );
    // The conclusion is the standard beta equality over `instantiate`.
    for pinned in ["DefEq", "instantiate"] {
        assert!(
            beta_ty.contains(pinned),
            "DefEq.beta's elaborated type should reference {pinned}: {beta_ty}"
        );
    }
    // With no typing premises, the constructor records no Typing dependency.
    assert!(
        beta.dependencies
            .as_ref()
            .map(|d| !d.contains("Typing"))
            .unwrap_or(true),
        "untyped DefEq.beta should not depend on Typing: {:?}",
        beta.dependencies
    );
}

#[test]
fn test_def_eq_rec_beta_case_is_untyped() {
    let spec = build_spec_with_stack();
    let rec = spec
        .definitions()
        .get("DefEq.rec")
        .expect("DefEq.rec should exist");

    // DefEq.rec is now the kernel-GENERATED recursor of the `add_inductive DefEq`
    // (not a hand-written axiom); `type_src` is the "(recursor of DefEq)"
    // placeholder, so the untypedness is checked against the elaborated recursor
    // type. Because DefEq is a 0-param / 2-index family, the generated recursor
    // layout (motive -> minors -> indices -> major) reproduces the retired
    // hand-written argument order verbatim.
    assert!(
        !rec.is_axiom,
        "DefEq.rec should be a kernel-generated recursor, not an axiom"
    );
    let rec_ty = format!(
        "{:?}",
        rec.elaborated_type
            .as_ref()
            .expect("DefEq.rec should record its elaborated type")
    );
    // #2859: NO minor premise (beta or otherwise) exposes a Typing witness — the
    // whole DefEq family is untyped, so the generated recursor mentions no Typing.
    assert!(
        !rec_ty.contains("Typing"),
        "DefEq.rec must carry no typing premises in any minor (untyped #2859): {rec_ty}"
    );
    // The beta minor constructs the untyped DefEq.beta constructor. The kernel
    // `Name` Debug format is STRUCTURAL (nested `Str(Str(Anon,"DefEq"),"beta")`),
    // NOT dotted, so we match the constructor's leaf segment `"beta"` (the only
    // `beta` name in the DefEq family) together with the beta reduct `instantiate`
    // (the untyped conclusion `(λA.b) a ≡ instantiate b a`).
    assert!(
        rec_ty.contains("\"beta\"") && rec_ty.contains("instantiate"),
        "DefEq.rec beta minor should reference the untyped DefEq.beta constructor \
         over `instantiate`: {rec_ty}"
    );
}

#[test]
fn test_beta_reduction_alias_discards_typed_premises() {
    let spec = build_spec_with_stack();
    let br = spec
        .definitions()
        .get("beta_reduction")
        .expect("beta_reduction should exist");

    // beta_reduction stays a backward-compatible TYPED alias: its statement still
    // requires the domain/body/argument typing witnesses (so existing consumers'
    // call shapes are preserved).
    assert!(
        br.type_src.contains("Typing A (KExpr.sort u)"),
        "beta_reduction should still require domain typing: {}",
        br.type_src
    );
    assert!(
        br.type_src.contains("Typing b B"),
        "beta_reduction should still require body typing: {}",
        br.type_src
    );
    assert!(
        br.type_src.contains("Typing a A"),
        "beta_reduction should still require argument typing: {}",
        br.type_src
    );
    // #2859: but the PROOF discharges those premises by applying the now-untyped
    // DefEq.beta (3 args), binding and discarding the typing witnesses.
    let value = br
        .value_src
        .as_ref()
        .expect("beta_reduction should have a value");
    assert!(
        value.contains("DefEq.beta A b a"),
        "beta_reduction value should apply the untyped DefEq.beta: {value}"
    );
    assert!(
        !value.contains("DefEq.beta A b a B u hA hb ha"),
        "beta_reduction value must not forward the retired typed args: {value}"
    );
    assert_eq!(
        br.proof_status,
        ProofStatus::DerivedProved,
        "beta_reduction should be DerivedProved (direct alias)"
    );
}

#[test]
fn test_typed_def_eq_to_def_eq_beta_case_drops_premises() {
    let spec = build_spec_with_stack();
    let bridge = spec
        .definitions()
        .get("typed_def_eq_to_def_eq")
        .expect("typed_def_eq_to_def_eq should exist");
    let value = bridge
        .value_src
        .as_ref()
        .expect("typed_def_eq_to_def_eq should have a proof term");

    // #2859: TypedDefEq.beta still carries typing premises, but raw DefEq.beta is
    // now UNTYPED — so the bridge's beta arm binds those premises and DROPS them,
    // applying the 3-arg DefEq.beta.
    assert!(
        value.contains("DefEq.beta A body arg"),
        "typed_def_eq_to_def_eq should apply the untyped 3-arg DefEq.beta: {value}"
    );
    assert!(
        !value.contains("DefEq.beta A body arg B u hA hbody harg"),
        "typed_def_eq_to_def_eq must not forward the retired typed args: {value}"
    );
    assert_eq!(
        bridge.proof_status,
        ProofStatus::DerivedProved,
        "typed_def_eq_to_def_eq should remain DerivedProved"
    );
}

#[test]
fn test_def_eq_respects_subst_at_beta_case_is_untyped() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("def_eq_respects_subst_at")
        .expect("def_eq_respects_subst_at should exist");
    let value = def
        .value_src
        .as_ref()
        .expect("def_eq_respects_subst_at should have a proof term");

    // #2859: DefEq.rec's beta case is now UNTYPED, so the beta handler in
    // def_eq_respects_subst_at binds only A0/body/arg (plus the motive args w/d)
    // and receives NO typing premises.
    assert!(
        !value.contains("(_hA0 : Typing A0 (KExpr.sort u0))"),
        "def_eq_respects_subst_at beta case must not receive hA0 (untyped #2859): {value}"
    );
    assert!(
        !value.contains("(_hbody0 : Typing body B0)"),
        "def_eq_respects_subst_at beta case must not receive hbody0 (untyped #2859): {value}"
    );
    assert!(
        !value.contains("(_harg0 : Typing arg A0)"),
        "def_eq_respects_subst_at beta case must not receive harg0 (untyped #2859): {value}"
    );
    // It forwards to beta_subst_commutes_at with no typing witnesses.
    assert!(
        value.contains("beta_subst_commutes_at A0 body arg w d wd wr"),
        "def_eq_respects_subst_at should forward untyped args to beta_subst_commutes_at: {value}"
    );
    // After #2872: the beta_subst_commutes_at forward-reference cycle is broken
    // by staged registration (beta_subst_commutes_at's body is spliced in once
    // def_eq_respects_subst_at exists and is kernel-verified). The placeholder
    // church_rosser_whnf — only ever inherited from that forward declaration —
    // is discharged, so def_eq_respects_subst_at is DerivedProved with an empty
    // helper-axiom closure.
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "def_eq_respects_subst_at should be DerivedProved once beta_subst_commutes_at is spliced (#2872)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "def_eq_respects_subst_at should have an empty helper-axiom closure after the splice: {:?}",
        def.axiom_deps
    );
}

#[test]
fn test_beta_subst_commutes_is_unconditional() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("beta_subst_commutes")
        .expect("beta_subst_commutes should exist");

    // #2859: with DefEq.beta untyped, beta_subst_commutes is unconditional — it
    // carries NO typing premises, only the env-wellformedness hypotheses and the
    // substituted-beta DefEq conclusion.
    assert!(
        !def.type_src.contains("Typing A (KExpr.sort u)"),
        "beta_subst_commutes must not require domain typing (untyped #2859): {}",
        def.type_src
    );
    assert!(
        !def.type_src.contains("Typing body B"),
        "beta_subst_commutes must not require body typing (untyped #2859): {}",
        def.type_src
    );
    assert!(
        !def.type_src.contains("Typing arg A"),
        "beta_subst_commutes must not require argument typing (untyped #2859): {}",
        def.type_src
    );
    assert!(
        def.type_src.contains(
            "DefEq (instantiate (KExpr.app (KExpr.lam A body) arg) w) \
             (instantiate (instantiate body arg) w)"
        ),
        "beta_subst_commutes should state the substituted-beta DefEq: {}",
        def.type_src
    );
    // After #2872: beta_subst_commutes proves DefEq.beta transported through
    // def_eq_respects_subst, which is now DerivedProved with an empty helper
    // closure (the beta_subst_commutes_at cycle is spliced and kernel-verified).
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "beta_subst_commutes should be DerivedProved once the cycle is spliced (#2872)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "beta_subst_commutes should have an empty helper-axiom closure after the splice: {:?}",
        def.axiom_deps
    );
}

#[test]
fn test_beta_reduces_preserves_def_eq_is_proved_after_untyped_beta() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("beta_reduces_preserves_def_eq")
        .expect("beta_reduces_preserves_def_eq should exist");

    // beta_reduces_preserves_def_eq is now a kernel-checked DerivedProved bridge:
    // untyping DefEq.beta (church_rosser_whnf retirement) lets beta_reduces.rec
    // discharge every arm with the UNTYPED DefEq constructors (beta/let contract via
    // DefEq.beta; forall_/let route through the reducible KExpr aliases), so the
    // bridge from the `beta_reduces` relation to DefEq now carries a closed proof term.
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "beta_reduces_preserves_def_eq is proved via the untyped beta_reduces.rec bridge"
    );
    assert!(
        def.value_src.is_some(),
        "beta_reduces_preserves_def_eq carries a beta_reduces.rec proof term"
    );
    assert!(
        !def.is_axiom,
        "beta_reduces_preserves_def_eq should remain a DerivedLemma, not axiom"
    );
}
