// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness-anchor tests for the **directed / simplicial layer — Rung 2**
//! (Riehl–Shulman). The strict directed interval `𝟚`, its bounded total order
//! `≤`, and the extension / hom types `hom_A(x,y) := ⟨ 𝟚 → A | {0↦x, 1↦y} ⟩`.
//!
//! All terms are built directly as kernel `Expr`s; the directed primitives are
//! registered as well-typed reserved-`Const` axioms via
//! [`register_directed_axioms`] (opt-in, mode-gated `CleanMode::Directed`, NOT in
//! the classical TCB), so the existing inference / certificate machinery accepts
//! the encoding unchanged — plain `Const`/`App` spines, no new `ExprKind`.
//!
//! Headline anchors:
//! * [`test_dir_order_asymmetry`] — `0₂ ≤ 1₂ ↝ Unit` (inhabited) while
//!   `1₂ ≤ 0₂ ↝ Empty` (uninhabited): directedness is real, not the symmetric `I`.
//! * [`test_id_arrow_builds`] — the reflexivity 1-cell `idArr A x : hom_A(x,x)`
//!   builds as `homLam A (λ_:𝟚. x)`, a genuine derived term.
//! * [`test_directed_le_inert_in_cubical_mode`] — the directed order does NOT
//!   reduce outside `Directed` mode (clean separation from the cubical `I`).

use super::*;

use crate::env::Declaration;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::reduction::directed::{
    dir_comp, dir_composite_type, dir_degen_composite_witness, dir_hom, dir_hom2, dir_hom_app,
    dir_hom_lam, dir_i0, dir_i1, dir_id_arr, dir_interval, dir_is_segal, dir_le,
    register_directed_axioms,
};
use crate::tc::reduction::kan::{
    is_contr_type, register_glue_axioms, register_kan_system_axioms, register_sigma_axioms,
};
use std::sync::Arc;

fn nm(s: &str) -> Name {
    Name::from_string(s)
}
fn cst(s: &str) -> Expr {
    Expr::const_(nm(s), Vec::<Level>::new())
}

/// `Type = Sort 1`, the level of `A : Type`.
fn type_level() -> Level {
    Level::succ(Level::zero())
}
fn unit() -> Expr {
    cst("Unit")
}
fn unit_tt() -> Expr {
    cst("Unit.tt")
}
fn empty() -> Expr {
    cst("Empty")
}

/// A `Directed`-mode environment with the directed axioms, the `Unit`/`Empty`
/// inductives the order reduction lands in, a carrier `A : Type` with points
/// `x y : A`, a function `g : 𝟚 → A`, a neutral interval point `iv : 𝟚`, and a
/// neutral hom `p : hom_A(x,y)`.
fn dir_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Directed);
    install_directed(&mut env);
    env
}

fn install_directed(env: &mut Environment) {
    register_directed_axioms(env).expect("register directed axioms");

    // Unit — single-constructor unit type (generates Unit.rec).
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nm("Unit"),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: nm("Unit.tt"),
                type_: unit(),
            }],
        }],
    })
    .expect("Unit inductive should register");

    // Empty — zero-constructor type (generates Empty.rec).
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nm("Empty"),
            type_: Expr::type_(),
            constructors: vec![],
        }],
    })
    .expect("Empty inductive should register");

    let mut axiom = |name: &str, type_: Expr| {
        env.add_decl(Declaration::Axiom {
            name: nm(name),
            level_params: vec![],
            type_,
        })
        .unwrap_or_else(|e| panic!("axiom {name} should register: {e:?}"));
    };
    axiom("A", Expr::type_());
    axiom("x", cst("A"));
    axiom("y", cst("A"));
    axiom("g", Expr::arrow(dir_interval(), cst("A"))); // g : 𝟚 → A
    axiom("iv", dir_interval()); // a neutral interval point
    axiom("p", dir_hom(type_level(), cst("A"), cst("x"), cst("y"))); // a neutral hom
}

fn tc(env: &Environment) -> TypeChecker<'_> {
    TypeChecker::with_mode(env, CleanMode::Directed)
}

// ── The directed interval `𝟚` and its endpoints ────────────────────────────────

#[test]
fn test_dir_interval_and_endpoints_typecheck() {
    let env = dir_env();
    let tc = tc(&env);

    // 𝟚 : Type.
    let ity = tc.infer_type(&dir_interval()).expect("𝟚 should type-check");
    assert!(tc.is_def_eq(&ity, &Expr::type_()), "𝟚 : Type; got {ity:?}");
    // 0₂ , 1₂ : 𝟚.
    let t0 = tc.infer_type(&dir_i0()).expect("0₂ should type-check");
    let t1 = tc.infer_type(&dir_i1()).expect("1₂ should type-check");
    assert!(tc.is_def_eq(&t0, &dir_interval()), "0₂ : 𝟚; got {t0:?}");
    assert!(tc.is_def_eq(&t1, &dir_interval()), "1₂ : 𝟚; got {t1:?}");
}

#[test]
fn test_dir_le_typechecks() {
    let env = dir_env();
    let tc = tc(&env);
    let le = dir_le(dir_i0(), dir_i1());
    let ty = tc.infer_type(&le).expect("Dir.le 0₂ 1₂ should type-check");
    assert!(
        tc.is_def_eq(&ty, &Expr::type_()),
        "le 0₂ 1₂ : Type; got {ty:?}"
    );
}

// ── The directedness anchor: the order is asymmetric ───────────────────────────

#[test]
fn test_dir_order_asymmetry() {
    let env = dir_env();
    let tc = tc(&env);

    // The full order table of the 2-element poset {0 < 1}.
    assert!(
        tc.is_def_eq(&dir_le(dir_i0(), dir_i0()), &unit()),
        "0₂ ≤ 0₂ ≡ Unit (reflexive)"
    );
    assert!(
        tc.is_def_eq(&dir_le(dir_i0(), dir_i1()), &unit()),
        "0₂ ≤ 1₂ ≡ Unit (the directed step HOLDS)"
    );
    assert!(
        tc.is_def_eq(&dir_le(dir_i1(), dir_i1()), &unit()),
        "1₂ ≤ 1₂ ≡ Unit (reflexive)"
    );
    assert!(
        tc.is_def_eq(&dir_le(dir_i1(), dir_i0()), &empty()),
        "1₂ ≤ 0₂ ≡ Empty (the reverse does NOT hold — asymmetry)"
    );

    // The asymmetry is genuine: 0≤1 and 1≤0 are NOT the same type.
    assert!(
        !tc.is_def_eq(&dir_le(dir_i0(), dir_i1()), &dir_le(dir_i1(), dir_i0())),
        "0₂ ≤ 1₂ (Unit) must NOT be def-eq to 1₂ ≤ 0₂ (Empty)"
    );
    assert!(
        !tc.is_def_eq(&dir_le(dir_i0(), dir_i1()), &empty()),
        "0₂ ≤ 1₂ must NOT collapse to Empty"
    );
}

#[test]
fn test_dir_0_le_1_is_inhabited() {
    // `Unit.tt : Dir.le 0₂ 1₂` — the directed step has a closed proof.
    let mut env = dir_env();
    env.add_decl(Declaration::Definition {
        name: nm("step01"),
        level_params: vec![],
        type_: dir_le(dir_i0(), dir_i1()),
        value: unit_tt(),
        is_reducible: false,
    })
    .expect("Unit.tt : Dir.le 0₂ 1₂ should type-check (0 ≤ 1 holds)");
}

#[test]
fn test_dir_1_le_0_is_refuted() {
    let env = dir_env();
    let tc = tc(&env);

    // No closed `Unit.tt`-proof: `Unit.tt`'s type (Unit) is NOT `Dir.le 1₂ 0₂`
    // (which is Empty).
    let tt_ty = tc.infer_type(&unit_tt()).expect("Unit.tt : Unit");
    assert!(
        !tc.is_def_eq(&tt_ty, &dir_le(dir_i1(), dir_i0())),
        "Unit.tt does NOT inhabit Dir.le 1₂ 0₂"
    );

    // And the negation is PROVABLE: `λ (h : 1₂ ≤ 0₂). h : (1₂ ≤ 0₂) → Empty`,
    // because `Dir.le 1₂ 0₂ ≡ Empty` definitionally.
    let mut env2 = dir_env();
    let neg = Expr::lam(
        BinderInfo::Default,
        dir_le(dir_i1(), dir_i0()),
        Expr::bvar(0),
    );
    env2.add_decl(Declaration::Definition {
        name: nm("not_1_le_0"),
        level_params: vec![],
        type_: Expr::arrow(dir_le(dir_i1(), dir_i0()), empty()),
        value: neg,
        is_reducible: false,
    })
    .expect("¬(1₂ ≤ 0₂) should be provable (Dir.le 1₂ 0₂ ≡ Empty)");
}

#[test]
fn test_dir_le_reflexivity_and_neutral_stuck() {
    let env = dir_env();
    let tc = tc(&env);

    // Reflexivity at a neutral point: iv ≤ iv ≡ Unit.
    assert!(
        tc.is_def_eq(&dir_le(cst("iv"), cst("iv")), &unit()),
        "iv ≤ iv ≡ Unit (reflexivity at a neutral interval point)"
    );

    // A genuinely-undecided pair stays stuck: `iv ≤ 0₂` is neither Unit nor Empty
    // (we do not know whether the neutral `iv` is 0₂ or 1₂).
    let neutral = dir_le(cst("iv"), dir_i0());
    assert!(
        !tc.is_def_eq(&neutral, &unit()),
        "iv ≤ 0₂ must NOT reduce to Unit (undecided)"
    );
    assert!(
        !tc.is_def_eq(&neutral, &empty()),
        "iv ≤ 0₂ must NOT reduce to Empty (undecided)"
    );
    // It WHNFs to itself (a stuck neutral order term).
    let w = tc.whnf(&neutral);
    assert!(
        matches!(w.get_app_fn().kind(), ExprKind::Const(n, _) if *n == nm("Dir.le")),
        "iv ≤ 0₂ stays a stuck `Dir.le` application; got {w:?}"
    );
}

// ── Extension / hom types ──────────────────────────────────────────────────────

#[test]
fn test_dir_hom_typechecks() {
    let env = dir_env();
    let tc = tc(&env);
    // hom_A(x,y) : Type.
    let hom = dir_hom(type_level(), cst("A"), cst("x"), cst("y"));
    let ty = tc.infer_type(&hom).expect("hom_A(x,y) should type-check");
    assert!(
        tc.is_def_eq(&ty, &Expr::type_()),
        "hom_A(x,y) : Type; got {ty:?}"
    );
}

#[test]
fn test_id_arrow_builds() {
    // The reflexivity 1-cell `idArr A x := homLam A (λ_:𝟚. x) : hom_A(x,x)` is a
    // genuine derived term (NOT an axiom): a constant directed morphism whose
    // endpoints are both `x`.
    let mut env = dir_env();
    let id_arr = dir_id_arr(type_level(), cst("A"), cst("x"));
    env.add_decl(Declaration::Definition {
        name: nm("idArr"),
        level_params: vec![],
        type_: dir_hom(type_level(), cst("A"), cst("x"), cst("x")),
        value: id_arr.clone(),
        is_reducible: false,
    })
    .expect("idArr : hom_A(x,x) should type-check (the reflexivity 1-cell)");

    // Independently: its inferred type is def-eq to hom_A(x,x).
    let tc = tc(&env);
    let ty = tc.infer_type(&id_arr).expect("idArr should infer");
    assert!(
        tc.is_def_eq(&ty, &dir_hom(type_level(), cst("A"), cst("x"), cst("x"))),
        "infer(idArr) ≡ hom_A(x,x); got {ty:?}"
    );
}

#[test]
fn test_hom_app_beta() {
    let env = dir_env();
    let tc = tc(&env);

    // homApp A (g 0₂) (g 1₂) (homLam A g) iv  ↝  g iv   (β).
    let g0 = Expr::app(cst("g"), dir_i0());
    let g1 = Expr::app(cst("g"), dir_i1());
    let hl = dir_hom_lam(type_level(), cst("A"), cst("g"));
    let app = dir_hom_app(type_level(), cst("A"), g0, g1, hl, cst("iv"));
    let expected = Expr::app(cst("g"), cst("iv"));
    assert!(
        tc.is_def_eq(&app, &expected),
        "homApp … (homLam A g) iv ↝ g iv (β); whnf = {:?}",
        tc.whnf(&app)
    );
}

#[test]
fn test_hom_app_boundary() {
    let env = dir_env();
    let tc = tc(&env);

    // For a NEUTRAL hom `p : hom_A(x,y)` (β cannot fire), the endpoints restrict:
    //   homApp A x y p 0₂ ↝ x ,  homApp A x y p 1₂ ↝ y.
    let app0 = dir_hom_app(
        type_level(),
        cst("A"),
        cst("x"),
        cst("y"),
        cst("p"),
        dir_i0(),
    );
    let app1 = dir_hom_app(
        type_level(),
        cst("A"),
        cst("x"),
        cst("y"),
        cst("p"),
        dir_i1(),
    );
    assert!(
        tc.is_def_eq(&app0, &cst("x")),
        "homApp A x y p 0₂ ↝ x; whnf = {:?}",
        tc.whnf(&app0)
    );
    assert!(
        tc.is_def_eq(&app1, &cst("y")),
        "homApp A x y p 1₂ ↝ y; whnf = {:?}",
        tc.whnf(&app1)
    );

    // A neutral hom applied at a neutral point stays stuck.
    let appn = dir_hom_app(
        type_level(),
        cst("A"),
        cst("x"),
        cst("y"),
        cst("p"),
        cst("iv"),
    );
    assert!(
        !tc.is_def_eq(&appn, &cst("x")) && !tc.is_def_eq(&appn, &cst("y")),
        "homApp A x y p iv stays stuck (neutral p, neutral i)"
    );
}

// ── Clean separation from the cubical layer ────────────────────────────────────

#[test]
fn test_directed_le_inert_in_cubical_mode() {
    // The directed order is gated on `CleanMode::Directed`. In a `Cubical`-mode
    // checker the same `Dir.le 1₂ 0₂` term does NOT reduce to `Empty` — it stays
    // a stuck neutral application. This is the structural guarantee that the two
    // foundations (directed `𝟚` vs cubical `I`) never interfere.
    let mut env = Environment::with_mode(CleanMode::Cubical);
    install_directed(&mut env);
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let le10 = dir_le(dir_i1(), dir_i0());
    assert!(
        !tc.is_def_eq(&le10, &empty()),
        "Dir.le 1₂ 0₂ must stay inert (NOT ≡ Empty) outside Directed mode"
    );
    let le01 = dir_le(dir_i0(), dir_i1());
    assert!(
        !tc.is_def_eq(&le01, &unit()),
        "Dir.le 0₂ 1₂ must stay inert (NOT ≡ Unit) outside Directed mode"
    );
    // It WHNFs to itself (no directed reduction fired).
    let w = tc.whnf(&le10);
    assert!(
        matches!(w.get_app_fn().kind(), ExprKind::Const(n, _) if *n == nm("Dir.le")),
        "Dir.le 1₂ 0₂ stays a `Dir.le` application in Cubical mode; got {w:?}"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// The 2LTT bridge + Segal core (Rung 2, directed composition)
//
// The bridge: in `CleanMode::Directed` the cubical machinery (`Path`/`isContr`/
// `Sigma`/`hcomp`/`coe`) is ALSO available (`CleanMode::has_cubical_layer`), so a
// directed type can talk about contractibility of its hom-composites — the Segal
// condition. The directed-specific `Dir.*` reductions stay Directed-only.
// ════════════════════════════════════════════════════════════════════════════

fn interval_cubical() -> Expr {
    Expr::from_kind(ExprKind::CubicalInterval)
}

/// A `Directed`-mode env carrying BOTH the directed axioms (incl. the Segal
/// `Dir.Hom2`/`Dir.degen2`) AND the cubical Kan/Glue/Sigma axioms (the 2LTT
/// bridge), plus a third point `z : A` and two composable arrows
/// `f : hom_A(x,y)`, `gg : hom_A(y,z)`.
fn segal_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Directed);
    install_directed(&mut env);
    // The bridge: the cubical layer is registered into the Directed-mode env.
    register_kan_system_axioms(&mut env).expect("register kan system axioms");
    register_glue_axioms(&mut env).expect("register glue axioms");
    register_sigma_axioms(&mut env).expect("register sigma axioms");

    env.add_decl(Declaration::Axiom {
        name: nm("z"),
        level_params: vec![],
        type_: cst("A"),
    })
    .expect("z : A registers");
    env.add_decl(Declaration::Axiom {
        name: nm("f"),
        level_params: vec![],
        type_: dir_hom(type_level(), cst("A"), cst("x"), cst("y")),
    })
    .expect("f : hom_A(x,y) registers");
    env.add_decl(Declaration::Axiom {
        name: nm("gg"),
        level_params: vec![],
        type_: dir_hom(type_level(), cst("A"), cst("y"), cst("z")),
    })
    .expect("gg : hom_A(y,z) registers");
    env
}

// ── The bridge: cubical Path / isContr type-check in Directed mode ──────────────

#[test]
fn test_bridge_path_typechecks_in_directed_mode() {
    // The 2LTT bridge: a cubical `Path` type-checks in `Directed` mode, where it
    // was previously a `ModeRequired` error.
    let env = segal_env();
    let tc = tc(&env);

    // Path (λ_:I. A) x y : Type.
    let path = Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(Expr::lam(BinderInfo::Default, interval_cubical(), cst("A"))),
        left: Arc::new(cst("x")),
        right: Arc::new(cst("y")),
    });
    let ty = tc
        .infer_type(&path)
        .expect("cubical Path should type-check in Directed mode (the 2LTT bridge)");
    assert!(
        tc.is_def_eq(&ty, &Expr::type_()),
        "Path (λ_.A) x y : Type in Directed mode; got {ty:?}"
    );
}

#[test]
fn test_bridge_iscontr_typechecks_in_directed_mode() {
    // `isContr A` (the Σ-encoded contractibility from Rung 1) type-checks in
    // Directed mode — THIS is the capability the Segal condition needs.
    let env = segal_env();
    let tc = tc(&env);

    let ic = is_contr_type(type_level(), &cst("A"));
    let ty = tc
        .infer_type(&ic)
        .expect("isContr A should type-check in Directed mode (the 2LTT bridge)");
    assert!(
        tc.is_def_eq(&ty, &Expr::type_()),
        "isContr A : Type in Directed mode; got {ty:?}"
    );
}

#[test]
fn test_bridge_does_not_leak_into_cubical_mode() {
    // The bridge is one-directional in capability: Directed gains the cubical
    // layer, but Cubical does NOT gain the directed reductions. `Dir.le 1₂ 0₂`
    // must stay inert in Cubical mode (re-anchoring the asymmetry separation
    // alongside the bridge), while a cubical `Path` still works there.
    let mut env = Environment::with_mode(CleanMode::Cubical);
    install_directed(&mut env);
    register_kan_system_axioms(&mut env).expect("kan");
    register_sigma_axioms(&mut env).expect("sigma");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // Directed order stays inert in Cubical mode (no directed reduction).
    assert!(
        !tc.is_def_eq(&dir_le(dir_i1(), dir_i0()), &empty()),
        "Dir.le 1₂ 0₂ must stay inert in Cubical mode (bridge does not leak)"
    );
    // But the cubical layer itself still works in Cubical mode.
    let ic = is_contr_type(type_level(), &cst("A"));
    let ty = tc
        .infer_type(&ic)
        .expect("isContr A still type-checks in Cubical mode");
    assert!(tc.is_def_eq(&ty, &Expr::type_()));
}

// ── Segal: the 2-simplex filler, isSegal, comp, and the degeneracy anchor ───────

#[test]
fn test_hom2_filler_typechecks() {
    // The 2-simplex filler type `Dir.Hom2 A x y z f g h : Type`, with the three
    // edges `f : hom(x,y)`, `gg : hom(y,z)`, `h : hom(x,z)`.
    let mut env = segal_env();
    // h : hom_A(x,z) — the composite-edge slot.
    env.add_decl(Declaration::Axiom {
        name: nm("h"),
        level_params: vec![],
        type_: dir_hom(type_level(), cst("A"), cst("x"), cst("z")),
    })
    .expect("h : hom_A(x,z) registers");
    let tc = tc(&env);

    let hom2 = dir_hom2(
        type_level(),
        cst("A"),
        cst("x"),
        cst("y"),
        cst("z"),
        cst("f"),
        cst("gg"),
        cst("h"),
    );
    let ty = tc
        .infer_type(&hom2)
        .expect("Dir.Hom2 A x y z f gg h should type-check");
    assert!(
        tc.is_def_eq(&ty, &Expr::type_()),
        "Hom2 A x y z f gg h : Type; got {ty:?}"
    );
}

#[test]
fn test_is_segal_typechecks() {
    // `isSegal A` — "every composable pair has a contractible type of composites"
    // — is itself a `Type` (a property of `A`), built over the bridge's `isContr`.
    let env = segal_env();
    let tc = tc(&env);

    let seg = dir_is_segal(type_level(), &cst("A"));
    let ty = tc
        .infer_type(&seg)
        .expect("isSegal A should type-check (uses the cubical isContr via the bridge)");
    assert!(
        tc.is_def_eq(&ty, &Expr::type_()),
        "isSegal A : Type; got {ty:?}"
    );
}

#[test]
fn test_composite_type_typechecks() {
    // The composite-witness type `Σ (h:hom(x,z)). Hom2 A x y z f gg h : Type`.
    let env = segal_env();
    let tc = tc(&env);

    let comp_ty = dir_composite_type(
        type_level(),
        &cst("A"),
        &cst("x"),
        &cst("y"),
        &cst("z"),
        &cst("f"),
        &cst("gg"),
    );
    let ty = tc
        .infer_type(&comp_ty)
        .expect("compositeType should type-check");
    assert!(
        tc.is_def_eq(&ty, &Expr::type_()),
        "compositeType A x y z f gg : Type; got {ty:?}"
    );
}

#[test]
fn test_degeneracy_inhabits_composite_type() {
    // THE ANCHOR: the composite type of `(id_y, gg)` is genuinely INHABITED by the
    // degenerate 2-simplex `(gg, degen2 …)` — composition of an identity with `gg`
    // exists and is `gg`, with a real filler. (Inhabitation is real; full
    // contractibility of this concrete case is the deferred Δ² piece.)
    let mut env = segal_env();
    let lvl = type_level();
    let id_y = dir_id_arr(lvl.clone(), cst("A"), cst("y"));
    // compositeType A y y z (idArr A y) gg.
    let comp_ty = dir_composite_type(
        lvl.clone(),
        &cst("A"),
        &cst("y"),
        &cst("y"),
        &cst("z"),
        &id_y,
        &cst("gg"),
    );
    let witness = dir_degen_composite_witness(lvl, &cst("A"), &cst("y"), &cst("z"), &cst("gg"));
    env.add_decl(Declaration::Definition {
        name: nm("degenComposite"),
        level_params: vec![],
        type_: comp_ty,
        value: witness,
        is_reducible: false,
    })
    .expect("(gg, degen2) inhabits compositeType A y y z (id_y) gg — the degeneracy anchor");
}

#[test]
fn test_comp_typechecks_from_segal_witness() {
    // `comp seg x y z f gg : hom_A(x,z)` — composition DEFINED as the centre of the
    // contractible composite type, given an (abstract) Segal witness `seg`. This is
    // the headline unlock: composition exists for a Segal type, projected via the
    // bridge's `Sigma.fst` from the `isContr` centre.
    let mut env = segal_env();
    let lvl = type_level();
    env.add_decl(Declaration::Axiom {
        name: nm("seg"),
        level_params: vec![],
        type_: dir_is_segal(lvl.clone(), &cst("A")),
    })
    .expect("opaque seg : isSegal A registers");
    let tc = tc(&env);

    // seg x y z f gg : isContr (compositeType A x y z f gg).
    let seg_app = Expr::apps(
        cst("seg"),
        [cst("x"), cst("y"), cst("z"), cst("f"), cst("gg")],
    );
    let comp = dir_comp(
        lvl.clone(),
        &cst("A"),
        &cst("x"),
        &cst("y"),
        &cst("z"),
        &cst("f"),
        &cst("gg"),
        &seg_app,
    );
    let ty = tc
        .infer_type(&comp)
        .expect("comp seg x y z f gg should type-check");
    let expected = dir_hom(lvl, cst("A"), cst("x"), cst("z"));
    assert!(
        tc.is_def_eq(&ty, &expected),
        "comp seg x y z f gg : hom_A(x,z); got {ty:?}"
    );
}

#[test]
fn test_comp_of_identity_anchor_typechecks() {
    // The identity/degeneracy anchor through `comp`: given a Segal witness, the
    // composite `comp seg y y z (id_y) gg : hom_A(y,z)` is defined (the centre of
    // the contractible composite type whose concrete inhabitant is `(gg, degen2)`).
    let mut env = segal_env();
    let lvl = type_level();
    env.add_decl(Declaration::Axiom {
        name: nm("seg"),
        level_params: vec![],
        type_: dir_is_segal(lvl.clone(), &cst("A")),
    })
    .expect("opaque seg : isSegal A registers");
    let tc = tc(&env);

    let id_y = dir_id_arr(lvl.clone(), cst("A"), cst("y"));
    // seg y y z (id_y) gg : isContr (compositeType A y y z (id_y) gg).
    let seg_app = Expr::apps(
        cst("seg"),
        [cst("y"), cst("y"), cst("z"), id_y.clone(), cst("gg")],
    );
    let comp = dir_comp(
        lvl.clone(),
        &cst("A"),
        &cst("y"),
        &cst("y"),
        &cst("z"),
        &id_y,
        &cst("gg"),
        &seg_app,
    );
    let ty = tc
        .infer_type(&comp)
        .expect("comp seg y y z (id_y) gg should type-check");
    let expected = dir_hom(lvl, cst("A"), cst("y"), cst("z"));
    assert!(
        tc.is_def_eq(&ty, &expected),
        "comp seg y y z (id_y) gg : hom_A(y,z); got {ty:?}"
    );
}
