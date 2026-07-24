// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for `env::proof_quality` MASQUERADE detectors.
//!
//! Tests operate directly on synthesised `Expr` values — no Environment
//! fixtures, no registered Definitions, no axiom fixtures. The goal is to
//! exercise each detector (M2/M3/M4 + helpers) in isolation.
//!
//! End-to-end `add_decl` integration is covered by `tests_add_decl_audit.rs`
//! when `CLEAN_STRICT_PROOF_QUALITY=1` is set; that path hits real kernel
//! registration and is tracked separately.

use super::{
    classify_discarding_body, equality_has_identical_sides, expr_uses_bvar, find_unused_ih,
    head_const, peel_lambdas, refl_root_depth, strict_mode_enabled_for_value,
};
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr, ExprKind, LevelVec};
use crate::name::Name;

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn const_(s: &str) -> Expr {
    Expr::from_kind(ExprKind::Const(name(s), LevelVec::new()))
}

fn bvar(i: u32) -> Expr {
    Expr::bvar(i)
}

#[test]
fn head_const_reads_app_head() {
    let e = Expr::apps(const_("Eq.refl"), [const_("Nat"), const_("zero")]);
    assert_eq!(head_const(&e).map(Name::to_string), Some("Eq.refl".into()));
}

#[test]
fn peel_lambdas_counts_binders() {
    let body = bvar(0);
    let inner = Expr::lam(BinderInfo::Default, const_("Nat"), body);
    let outer = Expr::lam(BinderInfo::Default, const_("Nat"), inner);
    let (peeled, depth) = peel_lambdas(&outer);
    assert_eq!(depth, 2);
    assert!(matches!(peeled.kind(), ExprKind::BVar(0)));
}

#[test]
fn m4_flags_bare_eq_refl_proof() {
    // Proof term: `@Eq.refl Nat zero`
    let proof = Expr::apps(const_("Eq.refl"), [const_("Nat"), const_("zero")]);
    let depth = refl_root_depth(&proof);
    assert_eq!(depth, Some(0));
}

#[test]
fn m4_flags_eq_trans_of_refl() {
    // `Eq.trans h (Eq.refl _)` — peel Eq.trans (last arg) then see Eq.refl.
    let refl = Expr::apps(const_("Eq.refl"), [const_("Nat"), const_("zero")]);
    let proof = Expr::apps(const_("Eq.trans"), [const_("h"), refl]);
    let depth = refl_root_depth(&proof);
    assert_eq!(depth, Some(1));
}

#[test]
fn m4_clean_on_recursor_proof() {
    // `Nat.rec motive base step n` is not a refl root.
    let proof = Expr::apps(
        const_("Nat.rec"),
        [
            const_("motive"),
            const_("base"),
            const_("step"),
            const_("n"),
        ],
    );
    assert_eq!(refl_root_depth(&proof), None);
}

// ─── M4 vacuity gate (`equality_has_identical_sides`) ──────────────────────────
// `check_proof_nontrivial` only raises M4 when BOTH `refl_root_depth(value)` is
// Some AND the proved type is a vacuous `Eq a a`. These tests exercise that
// conjunction directly (no Environment needed); the end-to-end coverage over the
// real corpus lives in `tests_masquerade_gate`.

#[test]
fn m4_flags_vacuous_eq_identical_sides() {
    // proof `@Eq.refl Nat a` proving type `@Eq Nat a a` — IDENTICAL sides → a
    // vacuous `Eq a a`. Both M4 conditions hold → flagged. (Detector still
    // catches the real masquerade.)
    let proof = Expr::apps(const_("Eq.refl"), [const_("Nat"), const_("a")]);
    let ty = Expr::apps(const_("Eq"), [const_("Nat"), const_("a"), const_("a")]);
    assert!(refl_root_depth(&proof).is_some());
    assert!(
        equality_has_identical_sides(&ty),
        "vacuous Eq a a must be flagged by M4"
    );
}

#[test]
fn m4_clean_on_distinct_sides_refl() {
    // proof `@Eq.refl Nat (Nat.sub a 0)` proving `@Eq Nat (Nat.sub a 0) a` —
    // DISTINCT sides, defeq only by computation → GENUINE proof, NOT M4. (This is
    // the over-fire fix: still a refl root, but the equality is not vacuous.)
    let sub = Expr::apps(const_("Nat.sub"), [const_("a"), const_("Nat.zero")]);
    let proof = Expr::apps(const_("Eq.refl"), [const_("Nat"), sub.clone()]);
    let ty = Expr::apps(const_("Eq"), [const_("Nat"), sub, const_("a")]);
    assert!(
        refl_root_depth(&proof).is_some(),
        "still a refl-rooted proof"
    );
    assert!(
        !equality_has_identical_sides(&ty),
        "distinct sides → genuine, not M4"
    );
}

#[test]
fn m4_clean_on_non_equality_reflexive_prop() {
    // Type `Rat.Raw.Equiv p p` is reflexive but its head is NOT `Eq`/`HEq`, so a
    // refl proof of it is out of M4's scope and must not be flagged.
    let ty = Expr::apps(const_("Rat.Raw.Equiv"), [const_("p"), const_("p")]);
    assert!(!equality_has_identical_sides(&ty));
}

#[test]
fn m4_identical_sides_detected_under_pi() {
    // `∀ a : Nat, @Eq Nat a a` — peel the Pi, the equality has identical sides.
    let eq = Expr::apps(const_("Eq"), [const_("Nat"), bvar(0), bvar(0)]);
    let ty = Expr::pi(BinderInfo::Default, const_("Nat"), eq);
    assert!(equality_has_identical_sides(&ty));

    // `∀ a : Nat, @Eq Nat (Nat.succ a) a` — distinct sides under the Pi.
    let lhs = Expr::app(const_("Nat.succ"), bvar(0));
    let eq2 = Expr::apps(const_("Eq"), [const_("Nat"), lhs, bvar(0)]);
    let ty2 = Expr::pi(BinderInfo::Default, const_("Nat"), eq2);
    assert!(!equality_has_identical_sides(&ty2));
}

#[test]
fn m3_unused_ih_is_a_structural_observation_not_a_masquerade() {
    // STEP minor: `fun (k : Nat) (ih : motive k) => Nat.succ k` — the genuine
    // induction hypothesis `ih : motive k` (BVar(0)) is NEVER used.
    //
    // The `find_unused_ih` STRUCTURAL DIAGNOSTIC correctly identifies this
    // pattern (it pinpoints the real motive-typed IH binder, not just BVar(0)).
    // But this is NOT a masquerade: on a kernel-checked corpus an unused IH means
    // the per-case goal was provable directly — the sound "recursor used for case
    // analysis" idiom (e.g. `Nat.min_comm`, `Nat.pred_le`, `Int.le_antisymm`).
    // Accordingly `check_proof_nontrivial` does NOT push an
    // `UnusedInductionHypothesis` finding (verified end-to-end by the
    // always-on `tests_masquerade_gate`, whose flagged set is EMPTY). This test
    // documents that the analyzer still works while the gate ignores it.
    let motive_app = Expr::app(const_("motive"), bvar(0)); // motive k  (k = BVar 0)
    let body = Expr::app(const_("Nat.succ"), bvar(1)); // Nat.succ k — ignores ih
    let inner = Expr::lam(BinderInfo::Default, motive_app, body); // fun ih => …
    let minor = Expr::lam(BinderInfo::Default, const_("Nat"), inner); // fun k => …
                                                                      // Full proof: `Nat.rec motive base minor n` (motive at arg index 0).
    let proof = Expr::apps(
        const_("Nat.rec"),
        [const_("motive"), const_("base"), minor, const_("n")],
    );
    // Structural analyzer pinpoints the unused IH …
    let witness = find_unused_ih(&proof);
    assert_eq!(witness.map(|n| n.to_string()), Some("Nat.rec".into()));
}

#[test]
fn m3_clean_when_ih_is_used() {
    // STEP minor: `fun (k : Nat) (ih : motive k) => Nat.succ ih` — IH live.
    let motive_app = Expr::app(const_("motive"), bvar(0));
    let body = Expr::app(const_("Nat.succ"), bvar(0)); // uses ih (BVar 0)
    let inner = Expr::lam(BinderInfo::Default, motive_app, body);
    let minor = Expr::lam(BinderInfo::Default, const_("Nat"), inner);
    let proof = Expr::apps(
        const_("Nat.rec"),
        [const_("motive"), const_("base"), minor, const_("n")],
    );
    assert_eq!(find_unused_ih(&proof), None);
}

#[test]
fn m3_clean_on_base_minor_without_ih() {
    // BASE minor: `fun f g h => @Eq.refl Rat Rat.zero` — binds THREE variables
    // and uses NONE, but NONE of them is a motive application (their types are
    // plain constants `F`/`G`/`H`). This is a base case: no induction hypothesis
    // exists, so M3 must NOT flag it. (Old heuristic over-fired here because it
    // only checked "≥2 binders and BVar(0) unused".)
    let refl = Expr::apps(const_("Eq.refl"), [const_("Rat"), const_("Rat.zero")]);
    let l_h = Expr::lam(BinderInfo::Default, const_("H"), refl);
    let l_g = Expr::lam(BinderInfo::Default, const_("G"), l_h);
    let base = Expr::lam(BinderInfo::Default, const_("F"), l_g);
    // `Nat.rec motive base step n` with a clean (non-lambda) step placeholder.
    let proof = Expr::apps(
        const_("Nat.rec"),
        [const_("motive"), base, const_("step"), const_("n")],
    );
    assert_eq!(find_unused_ih(&proof), None);
}

#[test]
fn classify_discarding_body_detects_identity_on_arg() {
    // Value: `fun x => x` — identity on arg 0.
    let value = Expr::lam(BinderInfo::Default, const_("Nat"), bvar(0));
    let info = ConstantInfo {
        name: name("F"),
        level_params: vec![],
        type_: const_("Nat"),
        value: Some(value),
        is_reducible: true,
        reducibility: Reducibility::Reducible,
        kind: ConstantKind::Definition,
    };
    assert!(classify_discarding_body(&info).is_some());
}

#[test]
fn classify_discarding_body_detects_constant_body() {
    // Value: `fun x y => const_expr` (neither x nor y used).
    let inner = Expr::lam(BinderInfo::Default, const_("Nat"), const_("zero"));
    let outer = Expr::lam(BinderInfo::Default, const_("Nat"), inner);
    let info = ConstantInfo {
        name: name("F"),
        level_params: vec![],
        type_: const_("Nat"),
        value: Some(outer),
        is_reducible: true,
        reducibility: Reducibility::Reducible,
        kind: ConstantKind::Definition,
    };
    assert!(classify_discarding_body(&info).is_some());
}

#[test]
fn classify_discarding_body_clean_on_real_computation() {
    // Value: `fun x => Nat.succ x` — uses its argument.
    let body = Expr::app(const_("Nat.succ"), bvar(0));
    let value = Expr::lam(BinderInfo::Default, const_("Nat"), body);
    let info = ConstantInfo {
        name: name("F"),
        level_params: vec![],
        type_: const_("Nat"),
        value: Some(value),
        is_reducible: true,
        reducibility: Reducibility::Reducible,
        kind: ConstantKind::Definition,
    };
    assert_eq!(classify_discarding_body(&info), None);
}

#[test]
fn strict_mode_flag_parser_is_exact_and_process_isolated() {
    // Do not mutate `CLEAN_STRICT_PROOF_QUALITY` here. Unit tests run in one
    // process, and every concurrent prelude builder consults that flag while
    // registering its many theorems. A set/remove test therefore made unrelated
    // import-prelude tests nondeterministically enter strict MASQUERADE mode.
    assert!(!strict_mode_enabled_for_value(None));
    assert!(strict_mode_enabled_for_value(Some("1")));
    assert!(!strict_mode_enabled_for_value(Some("0")));
    assert!(!strict_mode_enabled_for_value(Some("true")));
    assert!(!strict_mode_enabled_for_value(Some(" 1")));
}

#[test]
fn expr_uses_bvar_respects_binder_shift() {
    // `fun x => BVar(1)` — the inner BVar(1) is free-in-lambda and refers to
    // an outer binder (index 0 at the outer level after the +1 shift). So
    // `expr_uses_bvar(&lam, 0)` == true (finds the BVar under the lambda
    // after the shift).
    let body = bvar(1);
    let lam = Expr::lam(BinderInfo::Default, const_("Nat"), body);
    assert!(expr_uses_bvar(&lam, 0));
    // A truly non-referring body: `fun x => zero` — no BVar at all.
    let lam2 = Expr::lam(BinderInfo::Default, const_("Nat"), const_("zero"));
    assert!(!expr_uses_bvar(&lam2, 0));
    assert!(!expr_uses_bvar(&lam2, 1));
}
