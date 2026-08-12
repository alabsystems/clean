// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness-anchor tests for **Deliverable A — `hcomp`-in-a-universe ↝ `Glue`**.
//!
//! The CCHM computation rule for a homogeneous composite *of types*:
//!
//! ```text
//! hcomp {Sort ℓ} [ φᵢ ↦ Tᵢ ] A   ↝   Glue A [ φᵢ ↦ (Tᵢ i1, coeEquiv Tᵢ) ]
//! ```
//!
//! fires only when the element type is a universe `Sort ℓ` and the extent is
//! genuinely neutral (the on-a-true-face / empty-extent rules already handled the
//! degenerate extents). Each cell's equivalence is the just-landed
//! [`coe_equiv`] (`coeEquiv Tᵢ : Equiv (Tᵢ i1) (Tᵢ i0)`); soundness rests on the
//! `hcomp` boundary `Tᵢ i0 ≡ A` (on the face φᵢ), so the cell `e` has exactly the
//! `Equiv (Tᵢ i1) A` the `Glue.Sys.cons` cell demands.
//!
//! These tests use a tube whose boundary holds **globally** — `Tᵢ = ua e`'s Glue
//! line, for which `Tᵢ i0 ≡ A` and `Tᵢ i1 ≡ B` compute — so the produced `Glue`
//! is a genuinely well-typed closed term (`infer_type` succeeds, anchoring type
//! preservation).

use super::*;

use crate::env::Declaration;
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::reduction::kan::{
    coe_equiv, glue_ua, is_equiv_coe, register_glue_axioms, register_kan_system_axioms,
};
use std::sync::Arc;

// ── Leaves ────────────────────────────────────────────────────────────────────

fn nm(s: &str) -> Name {
    Name::from_string(s)
}
fn cst(s: &str) -> Expr {
    Expr::const_(nm(s), Vec::<Level>::new())
}
fn interval() -> Expr {
    Expr::from_kind(ExprKind::CubicalInterval)
}
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn i0() -> Expr {
    Expr::from_kind(ExprKind::CubicalI0)
}
fn i1() -> Expr {
    Expr::from_kind(ExprKind::CubicalI1)
}
fn lam(dom: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, dom, body)
}
/// The level of the *glued types* (`A`, `B`, `Tᵢ i1` all `: Type = Sort 1`); the
/// `Glue`/`Equiv`/`coeEquiv` output lives at this level.
fn glued_level() -> Level {
    Level::succ(Level::zero()) // 1
}
/// The level of a `System` whose **elements are types** (`Type : Sort 2`), so the
/// tube system of an `hcomp {Type}` is encoded with `System.cons.{2}`.
fn sys_of_types_level() -> Level {
    Level::succ(Level::succ(Level::zero())) // 2
}

// ── Cofibration / system / glue encoding helpers ───────────────────────────────

fn face_eq1(r: Expr) -> Expr {
    Expr::app(cst("Cofib.eq1"), r)
}
fn cofib_top() -> Expr {
    cst("Cofib.top")
}
fn cofib_or(x: Expr, y: Expr) -> Expr {
    Expr::apps(cst("Cofib.or"), [x, y])
}
/// `System.cons.{ℓ} A φ head tail`.
fn sys_cons(level: Level, a: Expr, face: Expr, head: Expr, tail: Expr) -> Expr {
    Expr::apps(
        Expr::const_(nm("System.cons"), vec![level]),
        [a, face, head, tail],
    )
}
fn sys_nil(level: Level, a: Expr) -> Expr {
    Expr::app(Expr::const_(nm("System.nil"), vec![level]), a)
}
/// `Glue.Sys.cons.{ℓ} B φ T e ie tail` / `Glue.Sys.nil.{ℓ} B`.
#[allow(clippy::too_many_arguments)]
fn glue_sys_cons(
    level: Level,
    b: Expr,
    face: Expr,
    t: Expr,
    e: Expr,
    ie: Expr,
    tail: Expr,
) -> Expr {
    Expr::apps(
        Expr::const_(nm("Glue.Sys.cons"), vec![level]),
        [b, face, t, e, ie, tail],
    )
}
fn glue_sys_nil(level: Level, b: Expr) -> Expr {
    Expr::app(Expr::const_(nm("Glue.Sys.nil"), vec![level]), b)
}
/// `Glue.{ℓ} B φ sys`.
fn glue(level: Level, b: Expr, phi: Expr, sys: Expr) -> Expr {
    Expr::apps(Expr::const_(nm("Glue"), vec![level]), [b, phi, sys])
}
fn hcomp(ty: Expr, phi: Expr, u: Expr, base: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(ty),
        phi: Arc::new(phi),
        u: Arc::new(u),
        base: Arc::new(base),
    })
}

/// The `ua e` Glue *line* `λ i. Glue B [(i=0)↦(A,e), (i=1)↦(B, idEquiv B)]` as a
/// tube `I → Type`. Its boundary holds **globally**: `(line) i0 ↝ A`,
/// `(line) i1 ↝ B` (the Glue total-face rule), so it is a sound tube for a
/// universe `hcomp` (`Tᵢ i0 ≡ A` not just on the face).
fn ua_line(a: &Expr, b: &Expr, e: &Expr) -> Expr {
    let ua = glue_ua(a, b, e, glued_level());
    let ExprKind::CubicalPathLam { body } = ua.kind() else {
        panic!("glue_ua must produce a CubicalPathLam");
    };
    lam(interval(), body.as_ref().clone())
}

// ── Environment ────────────────────────────────────────────────────────────────

/// Cubical env: Kan + Glue axioms, plus `A B : Type`, an equivalence
/// `e : Equiv A B`, neutral intervals `jv kv : I`, and a non-universe opaque type
/// `C : Type` with a point `c0 : C` (the "must not fire" floor).
fn uni_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    register_kan_system_axioms(&mut env).expect("register kan system axioms");
    register_glue_axioms(&mut env).expect("register glue axioms");

    let mut axiom = |name: &str, type_: Expr| {
        env.add_decl(Declaration::Axiom {
            name: nm(name),
            level_params: vec![],
            type_,
        })
        .unwrap_or_else(|e| panic!("axiom {name} should register: {e:?}"));
    };

    axiom("A", Expr::type_());
    axiom("B", Expr::type_());
    axiom(
        "e",
        Expr::apps(
            Expr::const_(nm("Equiv"), vec![glued_level()]),
            [cst("A"), cst("B")],
        ),
    );
    axiom("jv", interval());
    axiom("kv", interval());
    axiom("C", Expr::type_());
    axiom("c0", cst("C"));
    env
}

fn infer(tc: &TypeChecker<'_>, e: &Expr) -> Expr {
    tc.infer_type_with_cert(e)
        .unwrap_or_else(|err| panic!("infer failed for {e:?}: {err:?}"))
        .0
}

// ═════════════════════════════════════════════════════════════════════════════
// 1 — the rule FIRES on a neutral face, lands on a well-typed `Glue`
// ═════════════════════════════════════════════════════════════════════════════

#[test]
fn test_hcomp_universe_neutral_face_reduces_to_glue() {
    let env = uni_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // hcomp {Type} [(jv=1) ↦ (ua e)-line] A   (jv neutral ⇒ the new rule fires).
    let tube = ua_line(&cst("A"), &cst("B"), &cst("e"));
    let system = sys_cons(
        sys_of_types_level(),
        Expr::type_(),
        face_eq1(cst("jv")),
        tube.clone(),
        sys_nil(sys_of_types_level(), Expr::type_()),
    );
    let h = hcomp(Expr::type_(), face_eq1(cst("jv")), system, cst("A"));

    // The redex type-checks (`: Type`).
    let h_ty = infer(&tc, &h);
    assert!(tc.is_def_eq(&h_ty, &Expr::type_()), "hcomp {{Type}} : Type");

    let reduct = tc.whnf(&h);

    // It genuinely fired (not a stuck `CubicalHComp`) and is `Glue`-headed.
    assert!(
        !matches!(reduct.kind(), ExprKind::CubicalHComp { .. }),
        "the universe→Glue rule must fire on a neutral face; stayed stuck: {reduct:?}"
    );
    let ExprKind::Const(head, _) = reduct.get_app_fn().kind() else {
        panic!("reduct must be a Const-headed `Glue` spine; got {reduct:?}");
    };
    assert_eq!(
        *head,
        nm("Glue"),
        "reduct must be Glue-headed; got {head:?}"
    );

    // `Glue A φ sys` — 3 args, base ≡ A (the floor).
    let args = reduct.get_app_args();
    assert_eq!(args.len(), 3, "Glue takes (B, φ, sys); got {reduct:?}");
    assert!(
        tc.is_def_eq(args[0], &cst("A")),
        "the Glue base must be the hcomp floor A; got {:?}",
        args[0]
    );

    // TYPE PRESERVATION: the produced Glue is a well-typed type (`: Type`).
    let r_ty = infer(&tc, &reduct);
    assert!(
        tc.is_def_eq(&r_ty, &Expr::type_()),
        "Glue reduct : Type (type preserved); got {r_ty:?}"
    );

    // The single cell's glued type is the tube lid `Tᵢ i1 ≡ B`.
    let cells = tc
        .parse_glue_system_for_test(args[2])
        .expect("the produced Glue system parses");
    assert_eq!(cells.len(), 1, "exactly one cell; got {}", cells.len());
    assert!(
        tc.is_def_eq(&cells[0].1, &cst("B")),
        "the cell glued-type must be Tᵢ i1 ≡ B; got {:?}",
        cells[0].1
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 2 — boundary: the total-face value agrees with the Glue boundary rule
// ═════════════════════════════════════════════════════════════════════════════

/// `hcomp {Type} [⊤↦T] A ≡ T i1` (the on-a-true-face rule, type-agnostic), and the
/// **Glue boundary rule** on the corresponding total cell agrees:
/// `Glue A [⊤↦(T i1, coeEquiv T)] ↝ T i1`. Both reduce to `T i1 ≡ B`.
#[test]
fn test_hcomp_universe_total_face_matches_glue_boundary() {
    let env = uni_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let tube = ua_line(&cst("A"), &cst("B"), &cst("e"));
    let lid = Expr::app(tube.clone(), i1()); // T i1

    // (a) hcomp total-face route: `hcomp {Type} [⊤↦T] A ↝ T i1 ≡ B`.
    let system = sys_cons(
        sys_of_types_level(),
        Expr::type_(),
        cofib_top(),
        tube.clone(),
        sys_nil(sys_of_types_level(), Expr::type_()),
    );
    let h = hcomp(Expr::type_(), cofib_top(), system, cst("A"));
    let h_reduct = tc.whnf(&h);
    assert!(
        tc.is_def_eq(&h_reduct, &lid),
        "hcomp {{Type}} [⊤↦T] A ≡ T i1; got {h_reduct:?}"
    );
    assert!(tc.is_def_eq(&h_reduct, &cst("B")), "T i1 ≡ B");

    // (b) Glue boundary route on the SAME total cell the rule would build:
    // `Glue A [⊤↦(T i1, coeEquiv T)] ↝ T i1`.
    let glue_total = glue(
        glued_level(),
        cst("A"),
        cofib_top(),
        glue_sys_cons(
            glued_level(),
            cst("A"),
            cofib_top(),
            lid.clone(),
            coe_equiv(&tube, glued_level()),
            is_equiv_coe(glued_level(), &tube),
            glue_sys_nil(glued_level(), cst("A")),
        ),
    );
    let g_reduct = tc.whnf(&glue_total);
    assert!(
        tc.is_def_eq(&g_reduct, &lid),
        "Glue A [⊤↦(T i1, coeEquiv T)] ↝ T i1; got {g_reduct:?}"
    );
    // The two routes agree (boundary coherence).
    assert!(
        tc.is_def_eq(&h_reduct, &g_reduct),
        "the hcomp total-face value and the Glue boundary value must agree"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 3 — MUST NOT fire for a non-`Sort` floor type
// ═════════════════════════════════════════════════════════════════════════════

/// `hcomp {C} [(jv=1)↦λ_.c0] c0` with `C : Type` an opaque (non-universe,
/// non-inductive) element type stays a **stuck** `CubicalHComp` — the universe→Glue
/// rule is gated on the element type being a `Sort`, and the constructor rule does
/// not apply to an axiom floor.
#[test]
fn test_hcomp_non_universe_floor_does_not_glue() {
    let env = uni_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let tube = lam(interval(), cst("c0")); // λ_:I. c0 : I → C
    let system = sys_cons(
        glued_level(), // C : Sort 1 ⇒ System over C is at level 1
        cst("C"),
        face_eq1(cst("jv")),
        tube,
        sys_nil(glued_level(), cst("C")),
    );
    let h = hcomp(cst("C"), face_eq1(cst("jv")), system, cst("c0"));

    // Type-checks (so this is a genuine, well-formed hcomp), and stays stuck.
    let h_ty = infer(&tc, &h);
    assert!(tc.is_def_eq(&h_ty, &cst("C")), "hcomp {{C}} : C");

    let reduct = tc.whnf(&h);
    assert!(
        matches!(reduct.kind(), ExprKind::CubicalHComp { .. }),
        "a non-Sort floor must NOT become a Glue; got {reduct:?}"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// 4 — MULTI-branch system (two cells) → a two-cell Glue; determinism
// ═════════════════════════════════════════════════════════════════════════════

/// A two-branch universe `hcomp` (`[(jv=1)↦T, (kv=1)↦T]`, the shape the composed-
/// `ua` winding line produces) reduces to a **two-cell** `Glue`, and WHNF is
/// deterministic.
#[test]
fn test_hcomp_universe_multibranch_to_two_cell_glue() {
    let env = uni_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let tube = ua_line(&cst("A"), &cst("B"), &cst("e"));
    let lvl = sys_of_types_level();
    // [(jv=1) ↦ T, (kv=1) ↦ T]  (same tube ⇒ overlap agreement is trivial).
    let system = sys_cons(
        lvl.clone(),
        Expr::type_(),
        face_eq1(cst("jv")),
        tube.clone(),
        sys_cons(
            lvl.clone(),
            Expr::type_(),
            face_eq1(cst("kv")),
            tube.clone(),
            sys_nil(lvl, Expr::type_()),
        ),
    );
    let phi = cofib_or(face_eq1(cst("jv")), face_eq1(cst("kv")));
    let h = hcomp(Expr::type_(), phi, system, cst("A"));

    // Well-typed redex.
    let h_ty = infer(&tc, &h);
    assert!(tc.is_def_eq(&h_ty, &Expr::type_()), "hcomp {{Type}} : Type");

    let reduct = tc.whnf(&h);
    let ExprKind::Const(head, _) = reduct.get_app_fn().kind() else {
        panic!("reduct must be Glue-headed; got {reduct:?}");
    };
    assert_eq!(*head, nm("Glue"));
    let args = reduct.get_app_args();
    let cells = tc
        .parse_glue_system_for_test(args[2])
        .expect("the produced Glue system parses");
    assert_eq!(cells.len(), 2, "two branches ⇒ two Glue cells");
    assert!(
        tc.is_def_eq(&cells[0].1, &cst("B")) && tc.is_def_eq(&cells[1].1, &cst("B")),
        "both cell glued-types must be Tᵢ i1 ≡ B"
    );

    // Type preservation on the multi-cell Glue, and determinism.
    let r_ty = infer(&tc, &reduct);
    assert!(tc.is_def_eq(&r_ty, &Expr::type_()), "two-cell Glue : Type");
    let r2 = tc.whnf(&h);
    assert!(tc.is_def_eq(&reduct, &r2), "WHNF must be deterministic");
}

// ═════════════════════════════════════════════════════════════════════════════
// 5 — the produced Glue's `unglue` β behaves
// ═════════════════════════════════════════════════════════════════════════════

/// `unglue` on a `glue` intro over the produced Glue base reduces to the
/// underlying base point (the Glue machinery the rule feeds into is sound).
#[test]
fn test_produced_glue_unglue_beta() {
    let mut env = uni_env();
    env.add_decl(Declaration::Axiom {
        name: nm("a"),
        level_params: vec![],
        type_: cst("A"),
    })
    .expect("a : A");
    env.add_decl(Declaration::Axiom {
        name: nm("tB"),
        level_params: vec![],
        type_: cst("B"),
    })
    .expect("tB : B");
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let tube = ua_line(&cst("A"), &cst("B"), &cst("e"));
    let lid = Expr::app(tube.clone(), i1()); // T i1 ≡ B
    let equiv = coe_equiv(&tube, glued_level()); // Equiv (T i1) (T i0) ≡ Equiv B A
    let face = face_eq1(cst("jv"));

    // glue A (T i1) φ (coeEquiv T) (isEquivCoe T) tB a : Glue A φ [φ↦(T i1, coeEquiv T)].
    let g = Expr::apps(
        Expr::const_(nm("glue"), vec![glued_level()]),
        [
            cst("A"),
            lid.clone(),
            face.clone(),
            equiv.clone(),
            is_equiv_coe(glued_level(), &tube),
            cst("tB"),
            cst("a"),
        ],
    );
    // unglue A φ [φ↦(T i1, coeEquiv T, isEquivCoe T)] g ↝ a.
    let sys = glue_sys_cons(
        glued_level(),
        cst("A"),
        face.clone(),
        lid,
        equiv,
        is_equiv_coe(glued_level(), &tube),
        glue_sys_nil(glued_level(), cst("A")),
    );
    let ung = Expr::apps(
        Expr::const_(nm("unglue"), vec![glued_level()]),
        [cst("A"), face, sys, g],
    );
    let reduct = tc.whnf(&ung);
    assert!(
        tc.is_def_eq(&reduct, &cst("a")),
        "unglue (glue … a) ↝ a; got {reduct:?}"
    );
}
