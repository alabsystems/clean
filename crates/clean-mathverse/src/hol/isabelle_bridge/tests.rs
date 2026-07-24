// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-check + foundational-closure tests for the connective-iso library and
//! the syntax-directed composer.
//!
//! Every declaration built here is `add_decl`-checked into a real
//! [`Environment`] and its transitive axiom closure asserted `⊆
//! FOUNDATIONAL_AXIOMS` — the honest evidence that the cross-lane bridge is a
//! real, foundational, kernel-checked proof, not a restatement.

use super::*;
use clean_kernel::{is_foundational_axiom, Declaration, Environment, Name};

fn bridge_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_iff().expect("init_iff");
    env.init_or().expect("init_or");
    env.init_exists().expect("init_exists");
    env
}

/// `add_decl` a theorem and assert its transitive axiom closure is foundational.
fn add_and_check(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(name),
        level_params: Vec::new(),
        type_,
        value,
    })
    .unwrap_or_else(|e| panic!("kernel rejected `{name}`: {e:?}"));

    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("no axiom_deps for `{name}`"));
    let non_foundational: Vec<String> = deps
        .iter()
        .filter(|n| !is_foundational_axiom(n))
        .map(ToString::to_string)
        .collect();
    assert!(
        non_foundational.is_empty(),
        "`{name}` has non-foundational axioms in its closure: {non_foundational:?}"
    );
}

/// ∀-close `body` over the given `Prop`-typed free-fvar ids (outer→inner order).
fn forall_props(ids: &[u64], body: Expr) -> Expr {
    let mut e = body;
    for &id in ids.iter().rev() {
        e = Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            e.abstract_fvar(FVarId::new(id)),
        );
    }
    e
}

/// λ-close `body` over the given `Prop`-typed free-fvar ids (outer→inner order).
fn lambda_props(ids: &[u64], body: Expr) -> Expr {
    let mut e = body;
    for &id in ids.iter().rev() {
        e = Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            e.abstract_fvar(FVarId::new(id)),
        );
    }
    e
}

/// ∀/λ-close over free-fvar ids of an arbitrary (shared) type.
fn close_over(ids: &[u64], ty: Expr, is_lambda: bool, body: Expr) -> Expr {
    let mut e = body;
    for &id in ids.iter().rev() {
        let inner = e.abstract_fvar(FVarId::new(id));
        e = if is_lambda {
            Expr::lam(BinderInfo::Default, ty.clone(), inner)
        } else {
            Expr::pi(BinderInfo::Default, ty.clone(), inner)
        };
    }
    e
}

fn pvar(id: u64) -> Expr {
    Expr::fvar(FVarId::new(id))
}

// ---------------------------------------------------------------------------
// Part 1 — the connective-iso library: every lemma kernel-checks + is foundational.
// ---------------------------------------------------------------------------

#[test]
fn test_iso_library_all_kernel_verified_foundational() {
    let mut env = bridge_env();
    let lemmas = iso_lemmas();
    assert_eq!(
        lemmas.len(),
        9,
        "iso library must cover the HOL logical signature"
    );
    for l in lemmas {
        add_and_check(&mut env, l.name, l.type_, l.value);
    }
}

// ---------------------------------------------------------------------------
// Part 2 — the composer: 4 pilot cases + 6 synthetic cases kernel-check as whole
// -statement `isa ↔ ml` bridges, each with a foundational closure.
// ---------------------------------------------------------------------------

/// Compose `isa ↔ ml`, ∀-close over the given Prop atom ids, and kernel-check.
fn check_composed_props(name: &str, atom_ids: &[u64], isa: Expr, ml: Expr) {
    let mut env = bridge_env();
    let proof = compose_bridge(&isa, &ml)
        .unwrap_or_else(|e| panic!("compose_bridge declined `{name}`: {e:?}"));
    let type_ = forall_props(atom_ids, m_iff(isa, ml));
    let value = lambda_props(atom_ids, proof);
    add_and_check(&mut env, name, type_, value);
}

#[test]
fn test_compose_pilot_conj() {
    let (p, q) = (pvar(1), pvar(2));
    check_composed_props(
        "compose.conj",
        &[1, 2],
        isa_conj(p.clone(), q.clone()),
        m_and(p, q),
    );
}

#[test]
fn test_compose_pilot_disj() {
    let (p, q) = (pvar(1), pvar(2));
    check_composed_props(
        "compose.disj",
        &[1, 2],
        isa_disj(p.clone(), q.clone()),
        m_or(p, q),
    );
}

#[test]
fn test_compose_pilot_not() {
    let p = pvar(1);
    check_composed_props("compose.not", &[1], isa_not(p.clone()), m_not(p));
}

#[test]
fn test_compose_pilot_de_morgan() {
    // isa: @Eq Prop (isaNot (isaConj P Q)) (isaDisj (isaNot P) (isaNot Q))
    // ml : Iff (Not (And P Q)) (Or (Not P) (Not Q))
    let (p, q) = (pvar(1), pvar(2));
    let isa = eq_prop(
        isa_not(isa_conj(p.clone(), q.clone())),
        isa_disj(isa_not(p.clone()), isa_not(q.clone())),
    );
    let ml = m_iff(
        m_not(m_and(p.clone(), q.clone())),
        m_or(m_not(p.clone()), m_not(q)),
    );
    check_composed_props("compose.de_morgan", &[1, 2], isa, ml);
}

#[test]
fn test_compose_synth_imp() {
    // Isabelle implication IS the clean arrow.
    let (p, q) = (pvar(1), pvar(2));
    check_composed_props(
        "compose.imp",
        &[1, 2],
        arrow(p.clone(), q.clone()),
        arrow(p, q),
    );
}

#[test]
fn test_compose_synth_nested() {
    // isaNot (isaConj (isaDisj P Q) R)  ↔  Not (And (Or P Q) R)
    let (p, q, r) = (pvar(1), pvar(2), pvar(3));
    let isa = isa_not(isa_conj(isa_disj(p.clone(), q.clone()), r.clone()));
    let ml = m_not(m_and(m_or(p, q), r));
    check_composed_props("compose.nested", &[1, 2, 3], isa, ml);
}

#[test]
fn test_compose_synth_iff_carrier() {
    // @Eq Prop P Q  ↔  Iff P Q
    let (p, q) = (pvar(1), pvar(2));
    check_composed_props(
        "compose.iff_carrier",
        &[1, 2],
        eq_prop(p.clone(), q.clone()),
        m_iff(p, q),
    );
}

#[test]
fn test_compose_synth_true_false_consts() {
    // isaConj isaTrue isaFalse  ↔  And True False   (no atoms)
    check_composed_props(
        "compose.true_false",
        &[],
        isa_conj(isa_true(), isa_false()),
        m_and(m_true(), m_false()),
    );
}

#[test]
fn test_compose_synth_forall_first_order() {
    // ∀ (P Q : Nat → Prop), (∀ x:Nat, isaConj (P x) (Q x)) ↔ (∀ x:Nat, And (P x) (Q x))
    let nat = Expr::const_str("Nat");
    let pred_ty = arrow(nat.clone(), Expr::prop());
    let (pv, qv) = (pvar(10), pvar(11));
    let isa = pi(nat.clone(), 500, {
        let (pv, qv) = (pv.clone(), qv.clone());
        move |x| isa_conj(Expr::app(pv, x.clone()), Expr::app(qv, x))
    });
    let ml = pi(nat, 500, {
        let (pv, qv) = (pv.clone(), qv.clone());
        move |x| m_and(Expr::app(pv, x.clone()), Expr::app(qv, x))
    });

    let mut env = bridge_env();
    let proof = compose_bridge(&isa, &ml).expect("compose forall");
    let type_ = close_over(&[10, 11], pred_ty.clone(), false, m_iff(isa, ml));
    let value = close_over(&[10, 11], pred_ty, true, proof);
    add_and_check(&mut env, "compose.forall_first_order", type_, value);
}

// ---------------------------------------------------------------------------
// Part 3 — honest declining.
// ---------------------------------------------------------------------------

#[test]
fn test_compose_declines_exists_out_of_scope() {
    // ∃ (x : Nat), P x  — Exists is out of scope for the composer.
    let nat = Expr::const_str("Nat");
    let p = pvar(10);
    let pred = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::app(p.clone(), Expr::bvar(0)),
    );
    let ml = Expr::apps(
        Expr::const_str_levels("Exists", vec![obj_level()]),
        [nat.clone(), pred.clone()],
    );
    let isa = isa_ex(nat, p);
    assert_eq!(
        compose_bridge(&isa, &ml),
        Err(BridgeError::OutOfScope("Exists")),
    );
}

#[test]
fn test_compose_declines_isa_mismatch() {
    // Mathlib says `And P Q` but the provided Isabelle side is `isaDisj P Q`.
    let (p, q) = (pvar(1), pvar(2));
    let isa = isa_disj(p.clone(), q.clone());
    let ml = m_and(p, q);
    assert_eq!(compose_bridge(&isa, &ml), Err(BridgeError::IsaMismatch));
}

#[test]
fn test_compose_declines_carrier_sort() {
    // A bare sort in a proposition slot is a carrier mismatch.
    let ml = m_not(Expr::prop());
    let isa = isa_not(Expr::prop());
    assert_eq!(compose_bridge(&isa, &ml), Err(BridgeError::CarrierMismatch));
}

// ---------------------------------------------------------------------------
// Part 4 — the KernelBridged discharge term: a REAL Clean proof of the Isabelle
// statement, composed from a Mathlib witness + the foundational connective
// bridge. Each `add_decl`s a `Declaration::Theorem` whose TYPE is the Isabelle
// statement (NOT the `isa ↔ ml` bridge) and asserts a foundational closure.
// ---------------------------------------------------------------------------

#[test]
fn test_discharge_isa_true_from_prelude_witness() {
    // Mathlib witness: the prelude constant `True.intro : True` (foundational).
    // Bridge discharges the Isabelle statement `isaTrue` end-to-end.
    let mut env = bridge_env();
    let isa = isa_true();
    let value = discharge_value(&isa, &m_true(), c("True.intro")).expect("discharge isaTrue");
    add_and_check(&mut env, "discharge.isa_true", isa, value);
}

#[test]
fn test_discharge_isa_conj_from_named_kv_witness() {
    // Register a NAMED foundational theorem standing in for a Mathlib-KV constant
    // (`demo.kv_and_tt : And True True`), then discharge the Isabelle statement
    // `isaConj isaTrue isaTrue` by referencing that constant BY NAME — the exact
    // by-name reference the production discharge path uses.
    let mut env = bridge_env();
    let kv_name = "demo.kv_and_tt";
    let kv_type = m_and(m_true(), m_true());
    let kv_value = and_intro(m_true(), m_true(), c("True.intro"), c("True.intro"));
    add_and_check(&mut env, kv_name, kv_type.clone(), kv_value);

    let isa = isa_conj(isa_true(), isa_true());
    let value = discharge_value(&isa, &kv_type, c(kv_name)).expect("discharge isaConj");
    add_and_check(&mut env, "discharge.isa_conj_tt", isa, value);
}

// ---------------------------------------------------------------------------
// Part 5 — Isabelle-side def-const normalization. The importer's `embed_term`
// spells connectives with the reducible definition consts `isabelle.def.HOL.*`
// (which δ-unfold to the impredicative encoding), NOT the impredicative encoding
// the composer walks. `normalize_isa_connectives` bridges the two spellings.
// ---------------------------------------------------------------------------

/// The importer's def-const spelling of a connective head (a bare `Const`).
fn def_head(name: &str) -> Expr {
    Expr::const_str(name)
}

#[test]
fn test_normalize_unfolds_def_const_connectives() {
    let (p, q) = (pvar(1), pvar(2));
    let dc_conj = |a: Expr, b: Expr| Expr::apps(def_head("isabelle.def.HOL.conj"), [a, b]);
    let dc_disj = |a: Expr, b: Expr| Expr::apps(def_head("isabelle.def.HOL.disj"), [a, b]);
    let dc_not = |a: Expr| Expr::apps(def_head("isabelle.def.HOL.Not"), [a]);

    // Applied binary/unary connective def-consts δ-unfold to the impredicative
    // builders the composer walks.
    assert_eq!(
        normalize_isa_connectives(&dc_conj(p.clone(), q.clone())),
        isa_conj(p.clone(), q.clone()),
    );
    // Nested: `¬(P ∧ Q)` spelled with def-consts unfolds structurally.
    assert_eq!(
        normalize_isa_connectives(&dc_not(dc_conj(p.clone(), q.clone()))),
        isa_not(isa_conj(p.clone(), q.clone())),
    );
    // Nullary `True`/`False` (and the `Code_Generator.holds` alias of `True`).
    assert_eq!(
        normalize_isa_connectives(&def_head("isabelle.def.HOL.True")),
        isa_true(),
    );
    assert_eq!(
        normalize_isa_connectives(&def_head("isabelle.def.Code_Generator.holds")),
        isa_true(),
    );
    assert_eq!(
        normalize_isa_connectives(&def_head("isabelle.def.HOL.False")),
        isa_false(),
    );
    // A de-Morgan-shaped whole statement (`Eq Prop` carrier, disj/not/conj under
    // it) normalizes to exactly the composer's hand-built encoding.
    let isa_def = eq_prop(
        dc_not(dc_conj(p.clone(), q.clone())),
        dc_disj(dc_not(p.clone()), dc_not(q.clone())),
    );
    let isa_impred = eq_prop(
        isa_not(isa_conj(p.clone(), q.clone())),
        isa_disj(isa_not(p.clone()), isa_not(q.clone())),
    );
    assert_eq!(normalize_isa_connectives(&isa_def), isa_impred);

    // Under a binder: `∀ P, isaDisj P (¬P)` spelled with def-consts. The unfolded
    // connective introduces its own `∀C` binder, so the outer ∀-bound `P` must be
    // de-Bruijn-shifted — NOT captured. We build the expected side the same
    // capture-safe way (fresh fvar, then abstract) rather than splicing a raw
    // `bvar 0` (which would sit at the wrong depth under `isaDisj`'s `∀C`).
    let em_def = Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        dc_disj(Expr::bvar(0), dc_not(Expr::bvar(0))),
    );
    let em_impred = {
        let pf = pvar(7);
        let body = isa_disj(pf.clone(), isa_not(pf));
        Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            body.abstract_fvar(FVarId::new(7)),
        )
    };
    assert_eq!(normalize_isa_connectives(&em_def), em_impred);
}

#[test]
fn test_normalize_identity_on_impredicative() {
    // Already-impredicative statements are left byte-identical (no def-consts to
    // unfold) — the guarantee that the raw-encoding composer/discharge tests are
    // unaffected by pre-normalization.
    let (p, q) = (pvar(1), pvar(2));
    for raw in [
        isa_true(),
        isa_false(),
        isa_not(p.clone()),
        isa_conj(p.clone(), q.clone()),
        isa_disj(isa_not(p.clone()), q.clone()),
        eq_prop(
            isa_not(isa_conj(p.clone(), q.clone())),
            isa_disj(isa_not(p.clone()), isa_not(q.clone())),
        ),
        arrow(p.clone(), q.clone()),
    ] {
        assert_eq!(
            normalize_isa_connectives(&raw),
            raw,
            "normalize must be identity on {raw:?}"
        );
    }
}

#[test]
fn test_compose_bridge_accepts_def_const_spelling() {
    // The composer, fed a def-const-spelled Isabelle side, produces the SAME
    // foundational bridge it does for the raw encoding (pre-normalization is
    // transparent to the caller). de Morgan capstone, def-const spelled.
    let (p, q) = (pvar(1), pvar(2));
    let dc_conj = |a: Expr, b: Expr| Expr::apps(def_head("isabelle.def.HOL.conj"), [a, b]);
    let dc_disj = |a: Expr, b: Expr| Expr::apps(def_head("isabelle.def.HOL.disj"), [a, b]);
    let dc_not = |a: Expr| Expr::apps(def_head("isabelle.def.HOL.Not"), [a]);
    let isa_def = eq_prop(
        dc_not(dc_conj(p.clone(), q.clone())),
        dc_disj(dc_not(p.clone()), dc_not(q.clone())),
    );
    let ml = m_iff(
        m_not(m_and(p.clone(), q.clone())),
        m_or(m_not(p.clone()), m_not(q.clone())),
    );
    let from_def = compose_bridge(&isa_def, &ml).expect("compose def-const de morgan");
    // The proof is over the impredicative (normalized) side, identical to the raw
    // path's — so it kernel-checks against the impredicative statement type.
    let isa_impred = eq_prop(
        isa_not(isa_conj(p.clone(), q.clone())),
        isa_disj(isa_not(p.clone()), isa_not(q.clone())),
    );
    let mut env = bridge_env();
    let type_ = forall_props(&[1, 2], m_iff(isa_impred, ml));
    let value = lambda_props(&[1, 2], from_def);
    add_and_check(&mut env, "compose.def_de_morgan", type_, value);
}

#[test]
fn test_discharge_declines_on_out_of_scope() {
    // The discharge term inherits the composer's honest declines: an Exists-shaped
    // Mathlib type is out of scope, so no term is emitted.
    let nat = Expr::const_str("Nat");
    let p = pvar(10);
    let pred = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::app(p.clone(), Expr::bvar(0)),
    );
    let ml = Expr::apps(
        Expr::const_str_levels("Exists", vec![obj_level()]),
        [nat.clone(), pred],
    );
    let isa = isa_ex(nat, p);
    assert_eq!(
        discharge_value(&isa, &ml, c("some.exists_witness")).map(|_| ()),
        Err(BridgeError::OutOfScope("Exists")),
    );
}
