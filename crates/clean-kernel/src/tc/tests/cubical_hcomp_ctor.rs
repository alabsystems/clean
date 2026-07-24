// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness tests for the **`hcomp`-commutes-with-constructors** Kan reduction
//! (Step 6) — the rule that pushes a genuinely-stuck `hcomp` (face φ neither ⊤
//! nor ⊥) through the constructors of a **non-higher** inductive floor:
//!
//! ```text
//! hcomp {I} [φ↦u] (c a₁…aₙ)  ↝  c a₁′…aₙ′ ,   aᵢ′ = hcomp {Aᵢ} [φ↦ projᵢ(u)] aᵢ
//! ```
//!
//! Scoped (partial but sound) to the two cases the rule can discharge:
//!   * **nullary** constructor `c` ↝ the floor `c` (no args to project), and
//!   * **single self-recursive field** (`Nat.succ`-like) ↝
//!     `c (hcomp {I} [φ↦ map pred u] aᵢ)`, with `pred` the recursor-built field
//!     projection.
//!
//! The rule is **gated to non-HIT inductives**: `hcomp {S¹}` on a point
//! constructor stays stuck (a path constructor breaks no-confusion).

use super::*;

use crate::env::Declaration;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::reduction::kan::register_kan_system_axioms;
use std::sync::Arc;

// ── Leaves ──────────────────────────────────────────────────────────────────

fn nm(s: &str) -> Name {
    Name::from_string(s)
}
fn cst(s: &str) -> Expr {
    Expr::const_(nm(s), Vec::<Level>::new())
}
fn interval() -> Expr {
    Expr::from_kind(ExprKind::CubicalInterval)
}
fn i1() -> Expr {
    Expr::from_kind(ExprKind::CubicalI1)
}
fn nat() -> Expr {
    cst("Nat")
}
fn zero() -> Expr {
    cst("Nat.zero")
}
fn succ(n: Expr) -> Expr {
    Expr::app(cst("Nat.succ"), n)
}

/// The atomic face `(r = 1)` in the reserved cofibration encoding.
fn face_eq1(r: Expr) -> Expr {
    Expr::app(cst("Cofib.eq1"), r)
}
/// The total cofibration `⊤`.
fn cofib_top() -> Expr {
    cst("Cofib.top")
}

/// `hcomp {Nat} [phi ↦ u] base` (legacy single-branch system: `u : I → Nat`).
fn hcomp(phi: Expr, u: Expr, base: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(nat()),
        phi: Arc::new(phi),
        u: Arc::new(u),
        base: Arc::new(base),
    })
}

/// A constant interval tube `λ _:I. value : I → Nat`.
fn const_tube(value: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, interval(), value)
}

// ── Environments ────────────────────────────────────────────────────────────

/// Cubical env with the minimal `Nat` inductive (zero/succ, which generates
/// `Nat.rec`), the reserved cofibration constants, and a **neutral** interval
/// variable `j : I` (so the face `(j=1)` is neither ⊤ nor ⊥ — the genuinely-new
/// rule fires). A second neutral `a : Nat` lets us check the projected system in
/// situ on a non-constructor floor.
fn nat_cubical_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nm("Nat"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: nm("Nat.zero"),
                    type_: nat(),
                },
                Constructor {
                    name: nm("Nat.succ"),
                    type_: Expr::arrow(nat(), nat()),
                },
            ],
        }],
    };
    env.add_inductive(decl).expect("Nat inductive registers");
    register_kan_system_axioms(&mut env).expect("cofibration axioms register");
    env.add_decl(Declaration::Axiom {
        name: nm("j"),
        level_params: vec![],
        type_: interval(),
    })
    .expect("neutral interval j registers");
    env.add_decl(Declaration::Axiom {
        name: nm("a"),
        level_params: vec![],
        type_: nat(),
    })
    .expect("neutral Nat a registers");
    env
}

/// Cubical env with the circle `S¹` (`base : S¹`, `loop : Path (λ_:I.S¹) base base`)
/// plus the cofibration constants and a neutral interval `j : I`. `S¹` is a HIT:
/// the constructor-commutation rule MUST NOT fire on it.
fn s1_cubical_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    let loop_ty = {
        let line = Expr::lam(BinderInfo::Default, interval(), cst("S1"));
        Expr::from_kind(ExprKind::CubicalPath {
            ty: Arc::new(line),
            left: Arc::new(cst("S1.base")),
            right: Arc::new(cst("S1.base")),
        })
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nm("S1"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: nm("S1.base"),
                    type_: cst("S1"),
                },
                Constructor {
                    name: nm("S1.loop"),
                    type_: loop_ty,
                },
            ],
        }],
    };
    env.add_inductive(decl).expect("S¹ HIT registers");
    register_kan_system_axioms(&mut env).expect("cofibration axioms register");
    env.add_decl(Declaration::Axiom {
        name: nm("j"),
        level_params: vec![],
        type_: interval(),
    })
    .expect("neutral interval j registers");
    env
}

// ── 1. Nullary constructor on a NEUTRAL face (the genuinely-new rule) ─────────

#[test]
fn test_hcomp_nullary_neutral_face_reduces_to_floor() {
    let env = nat_cubical_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // hcomp {Nat} [(j=1) ↦ λ_. zero] zero — face (j=1) is neutral (j : I), so the
    // on-a-face (A) and empty-extent (B) rules do NOT fire; this is the new rule.
    let h = hcomp(face_eq1(cst("j")), const_tube(zero()), zero());

    let reduct = tc.whnf(&h);
    assert!(
        tc.is_def_eq(&reduct, &zero()),
        "hcomp [(j=1)↦u] zero should reduce to zero, got {reduct:?}"
    );
    // It genuinely reduced (not left as a stuck CubicalHComp).
    assert!(
        !matches!(reduct.kind(), ExprKind::CubicalHComp { .. }),
        "the nullary rule must fire on a neutral face, but hcomp stayed stuck"
    );
}

// ── 2. Single recursive field (succ) on a NEUTRAL face ───────────────────────

#[test]
fn test_hcomp_succ_neutral_face_collapses_to_base_numeral() {
    let env = nat_cubical_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // hcomp {Nat} [(j=1) ↦ λ_. succ zero] (succ zero)
    //   ↝ succ (hcomp {Nat} [(j=1) ↦ λj. pred ((λ_.succ zero) j)] zero)
    //   ↝ succ zero                                  (inner: nullary zero rule)
    let h = hcomp(face_eq1(cst("j")), const_tube(succ(zero())), succ(zero()));

    let reduct = tc.whnf(&h);
    // The rule genuinely fired (not a stuck CubicalHComp) and the result is the
    // base numeral. (`reduce_nat` may re-fold `succ (… ↝ zero)` to the literal `1`,
    // which is itself def-eq to `succ zero` — both are accepted.)
    assert!(
        !matches!(reduct.kind(), ExprKind::CubicalHComp { .. }),
        "the succ rule must fire on a neutral face, but hcomp stayed stuck: {reduct:?}"
    );
    assert!(
        tc.is_def_eq(&reduct, &succ(zero())),
        "hcomp [(j=1)↦u] (succ zero) should collapse to succ zero, got {reduct:?}"
    );

    // Two levels deep: succ (succ zero) collapses likewise.
    let h2 = hcomp(
        face_eq1(cst("j")),
        const_tube(succ(succ(zero()))),
        succ(succ(zero())),
    );
    assert!(
        tc.is_def_eq(&tc.whnf(&h2), &succ(succ(zero()))),
        "hcomp [(j=1)↦u] (succ (succ zero)) should collapse to succ (succ zero)"
    );
}

// ── 3. Boundary coherence: ⊤-route and the new-rule route agree ──────────────

#[test]
fn test_hcomp_constructor_boundary_coherence_on_true_face() {
    let env = nat_cubical_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // On a TRUE face ⊤, the existing on-a-face rule (A) fires: hcomp [⊤↦u] base ↝ u i1.
    let tube = const_tube(succ(zero()));
    let on_true = hcomp(cofib_top(), tube.clone(), succ(zero()));
    let true_route = tc.whnf(&on_true);
    assert!(
        tc.is_def_eq(&true_route, &succ(zero())),
        "⊤-face hcomp should give u i1 = succ zero, got {true_route:?}"
    );
    // ...which equals `u i1` literally.
    assert!(
        tc.is_def_eq(&true_route, &Expr::app(tube, i1())),
        "⊤-face route must be exactly `u i1`"
    );

    // The constructor-commutation route (fired on a neutral face with the SAME
    // constant tube) yields the same lid — boundary coherence.
    let on_neutral = hcomp(face_eq1(cst("j")), const_tube(succ(zero())), succ(zero()));
    let new_route = tc.whnf(&on_neutral);
    assert!(
        tc.is_def_eq(&true_route, &new_route),
        "⊤-route and constructor-rule route must agree (both succ zero)"
    );
}

// ── 4. Type preservation ─────────────────────────────────────────────────────

#[test]
fn test_hcomp_constructor_rule_preserves_type() {
    let env = nat_cubical_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // Nullary: infer(hcomp) ≡ infer(reduct) ≡ Nat.
    let h0 = hcomp(face_eq1(cst("j")), const_tube(zero()), zero());
    let h0_ty = tc.infer_type(&h0).expect("nullary hcomp type-checks");
    let r0_ty = tc
        .infer_type(&tc.whnf(&h0))
        .expect("nullary reduct type-checks");
    assert!(tc.is_def_eq(&h0_ty, &nat()), "hcomp : Nat");
    assert!(tc.is_def_eq(&r0_ty, &nat()), "reduct : Nat");
    assert!(tc.is_def_eq(&h0_ty, &r0_ty), "type preserved (nullary)");

    // Succ on a NEUTRAL floor `a : Nat` — the projected (pred-mapped) system
    // survives in the reduct's inner (stuck) hcomp, so this also checks the
    // projection is well-typed *in situ*: infer must still land in Nat.
    let h1 = hcomp(
        face_eq1(cst("j")),
        const_tube(succ(cst("a"))),
        succ(cst("a")),
    );
    let h1_ty = tc.infer_type(&h1).expect("succ hcomp type-checks");
    let reduct = tc.whnf(&h1);
    assert!(
        matches!(reduct.get_app_fn().kind(), ExprKind::Const(n, _) if *n == nm("Nat.succ")),
        "neutral-floor succ rule should produce `succ (inner hcomp)`, got {reduct:?}"
    );
    let r1_ty = tc
        .infer_type(&reduct)
        .expect("succ reduct (with projected system) type-checks");
    assert!(tc.is_def_eq(&h1_ty, &nat()), "succ hcomp : Nat");
    assert!(tc.is_def_eq(&r1_ty, &nat()), "succ reduct : Nat");
    assert!(tc.is_def_eq(&h1_ty, &r1_ty), "type preserved (succ)");
}

// ── 5. The recursor-built field projection (`pred`) is correct ───────────────

#[test]
fn test_field_projection_is_correct_predecessor() {
    let env = nat_cubical_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let pred = tc
        .build_field_projection_for_test(&nm("Nat"), &nm("Nat.succ"))
        .expect("Nat.succ field projection builds");

    // pred (succ zero) ≡ zero ; pred (succ (succ zero)) ≡ succ zero — the used
    // (on-face) behaviour of projᵢ, the only behaviour soundness depends on.
    assert!(
        tc.is_def_eq(&tc.whnf(&Expr::app(pred.clone(), succ(zero()))), &zero()),
        "pred (succ zero) should be zero"
    );
    assert!(
        tc.is_def_eq(
            &tc.whnf(&Expr::app(pred.clone(), succ(succ(zero())))),
            &succ(zero())
        ),
        "pred (succ (succ zero)) should be succ zero"
    );
    // And it is a well-typed total `Nat → Nat`.
    let pred_ty = tc.infer_type(&pred).expect("pred type-checks");
    assert!(
        tc.is_def_eq(&pred_ty, &Expr::arrow(nat(), nat())),
        "pred : Nat → Nat, got {pred_ty:?}"
    );
}

// ── 6. MUST NOT fire on a HIT (S¹) ───────────────────────────────────────────

#[test]
fn test_hcomp_does_not_fire_on_hit_point_constructor() {
    let env = s1_cubical_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // hcomp {S¹} [(j=1) ↦ λ_. base] base — `base` is a *nullary* point
    // constructor, but S¹ is a HIT (has the path constructor `loop`), so the
    // constructor-commutation rule must NOT push through: the term stays STUCK.
    let h = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(cst("S1")),
        phi: Arc::new(face_eq1(cst("j"))),
        u: Arc::new(Expr::lam(BinderInfo::Default, interval(), cst("S1.base"))),
        base: Arc::new(cst("S1.base")),
    });

    let reduct = tc.whnf(&h);
    assert!(
        matches!(reduct.kind(), ExprKind::CubicalHComp { .. }),
        "hcomp on a HIT point constructor must stay stuck, but it reduced to {reduct:?}"
    );
}

// ── 7. SOUNDNESS regression: cap / floor-agreement (`uᵢ i0 ≡ base` on φᵢ) ─────

/// A **floor-disagreeing** `hcomp` must be REJECTED by inference (both the release
/// fast path and the certificate path). `hcomp {Nat} [(j=1) ↦ λ_. succ zero] zero`
/// has tube i0-cap `succ zero` which does NOT equal the floor `zero` on the face
/// (j=1); accepting it lets `<j>` of it inhabit `Path Nat 0 1`, from which a closed
/// proof of `Empty` follows (the reported soundness hole). The cap check
/// (`validate_hcomp_cap`) must reject it.
#[test]
fn test_hcomp_cap_floor_disagreement_rejected() {
    let env = nat_cubical_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // tube `λ_. succ zero`, floor `zero` — disagree on the (neutral) face (j=1).
    let bad = hcomp(face_eq1(cst("j")), const_tube(succ(zero())), zero());

    assert!(
        tc.infer_type(&bad).is_err(),
        "floor-disagreeing hcomp must be rejected by infer_type (fast path)"
    );
    assert!(
        tc.infer_type_with_cert(&bad).is_err(),
        "floor-disagreeing hcomp must be rejected by infer_type_with_cert (cert path)"
    );

    // The path-lam route to the inconsistency must also be rejected:
    // `<j> hcomp {Nat} [(j=1) ↦ λ_. succ zero] zero` (j = BVar0; face uses BVar0).
    let bad_body = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(nat()),
        phi: Arc::new(face_eq1(Expr::bvar(0))),
        u: Arc::new(const_tube(succ(zero()))),
        base: Arc::new(zero()),
    });
    let bad_path = Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(bad_body),
    });
    assert!(
        tc.infer_type(&bad_path).is_err(),
        "`<j> H` (Path Nat 0 1 witness) must be rejected (fast path)"
    );
    assert!(
        tc.infer_type_with_cert(&bad_path).is_err(),
        "`<j> H` (Path Nat 0 1 witness) must be rejected (cert path)"
    );
}

/// The cap check must NOT over-reject a **well-formed** `hcomp`: a tube whose
/// i0-cap equals the floor (here globally) on a neutral face still type-checks.
#[test]
fn test_hcomp_cap_well_formed_still_accepted() {
    let env = nat_cubical_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // tube `λ_. succ zero`, floor `succ zero` — agree (constant cap = floor).
    let good = hcomp(face_eq1(cst("j")), const_tube(succ(zero())), succ(zero()));
    assert!(
        tc.infer_type(&good).is_ok(),
        "well-formed (cap = floor) hcomp must still type-check (fast path)"
    );
    assert!(
        tc.infer_type_with_cert(&good).is_ok(),
        "well-formed (cap = floor) hcomp must still type-check (cert path)"
    );

    // A ⊥ (inactive) face imposes no cap constraint: tube may be anything.
    let inactive = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(nat()),
        phi: Arc::new(Expr::from_kind(ExprKind::CubicalI0)), // (i0 = 1) ⇒ ⊥
        u: Arc::new(const_tube(zero())),
        base: Arc::new(succ(zero())),
    });
    assert!(
        tc.infer_type(&inactive).is_ok(),
        "⊥-face hcomp imposes no cap constraint and must type-check"
    );
}
