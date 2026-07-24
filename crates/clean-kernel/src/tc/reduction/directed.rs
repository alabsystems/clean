// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Directed / simplicial type theory — **Rung 2** (Riehl–Shulman), the
//! foundational first layer: the **strict directed interval `𝟚`** (the
//! 1-simplex `Δ¹`), its bounded total order `≤`, and the **extension / hom
//! types** `hom_A(x,y) := ⟨ 𝟚 → A | {0↦x, 1↦y} ⟩`.
//!
//! ## Why a reserved-`Const` encoding (and not a new `ExprKind` variant)
//!
//! Exactly as for the cubical cofibration/`Glue` machinery (see
//! [`crate::tc::reduction::kan`]): the directed primitives — the interval
//! `Dir.𝟚`, its endpoints `Dir.0₂`/`Dir.1₂`, the order `Dir.le`, the hom-type
//! former `Dir.Hom`, and its intro/elim `Dir.homLam`/`Dir.homApp` — are ordinary
//! `Const`/`App` terms over **reserved heads** with genuinely well-typed axiom
//! types (registered by [`register_directed_axioms`]). So every generic kernel
//! traversal (inference, `def_eq`, the certificate builder/verifier, display)
//! handles them unchanged, and there is **no new variant** to thread through the
//! 17-file checklist. They are **opt-in and mode-gated** (`CleanMode::Directed`),
//! NOT part of the classical TCB.
//!
//! ## Cleanly SEPARATE from the cubical interval `I`
//!
//! The directed interval `𝟚` is a `Const "Dir.𝟚"`; the cubical interval `I` is
//! the *distinct* `ExprKind::CubicalInterval`. The cubical interpreter keys on
//! `CubicalInterval`/`Cofib.*`/`Glue`; the directed interpreter (this module)
//! keys on `Dir.*`. They share no names and no `ExprKind`, so the symmetric
//! (invertible) cubical `I` and the directed (asymmetric) `𝟚` never interfere.
//! Crucially, `𝟚` has **no reversal `~`** — that is the whole point: `𝟚` is
//! directed; `I` is symmetric.
//!
//! ## Soundness anchors
//!
//! * **Decidable order / asymmetry.** [`TypeChecker::try_directed_reduction`]
//!   decides `Dir.le` on literal endpoints exactly as the 2-element poset
//!   `{0 < 1}`: `le 0₂ 0₂ ↝ Unit`, `le 0₂ 1₂ ↝ Unit`, `le 1₂ 1₂ ↝ Unit`,
//!   `le 1₂ 0₂ ↝ Empty` (plus reflexivity `le x x ↝ Unit`). So `0₂ ≤ 1₂` is
//!   inhabited (`Unit.tt`) while `1₂ ≤ 0₂` is **definitionally `Empty`** — there
//!   is no closed proof, and `¬(1₂ ≤ 0₂)` is provable. Directedness is real, not
//!   collapsed to the invertible cubical `I`. Every rule is type-preserving
//!   (`Dir.le x y : Type` and `Unit`/`Empty : Type`).
//! * **Hom computation.** `homApp A x y (homLam A f) i ↝ f i` (β), and the
//!   boundaries `homApp A x y p 0₂ ↝ x`, `homApp A x y p 1₂ ↝ y` — the extension
//!   type's restriction-to-the-face rule. Type-preserving (`homApp … : A`, and
//!   `x`, `y`, `f i : A`). The id-arrow `idArr A x := homLam A (λ_:𝟚. x)` then
//!   has type `Dir.Hom A x x` — the reflexivity 1-cell, a genuine derived
//!   definition (not an axiom).

use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::whnf::WhnfMode;
use crate::tc::TypeChecker;

/// Reserved constant names for the **Expr-encoding** of the directed interval,
/// its order, and the extension / hom types. All under the `Dir.` namespace so
/// they are visibly distinct from the cubical `Cofib.*`/`Glue`/`System.*` heads
/// and the `ExprKind::Cubical*` interval.
///
/// ```text
/// Dir.𝟚                                  : Type                 -- the strict interval Δ¹
/// Dir.0₂ , Dir.1₂                        : Dir.𝟚                -- the two endpoints
/// Dir.le                                 : Dir.𝟚 → Dir.𝟚 → Type -- the order 0 ≤ x ≤ 1
/// Dir.Hom.{u}   (A:Sort u)(x y:A)        : Sort u               -- hom_A(x,y) = ⟨𝟚→A|{0↦x,1↦y}⟩
/// Dir.homLam.{u}(A:Sort u)(f:𝟚→A)        : Dir.Hom A (f 0₂)(f 1₂) -- intro
/// Dir.homApp.{u}(A:Sort u)(x y:A)(p:Dir.Hom A x y)(i:𝟚) : A     -- elim (β + boundary)
/// ```
pub(crate) mod dir_names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub static DIR_INTERVAL: LazyLock<Name> = LazyLock::new(|| Name::from_string("Dir.𝟚"));
    pub static DIR_I0: LazyLock<Name> = LazyLock::new(|| Name::from_string("Dir.0₂"));
    pub static DIR_I1: LazyLock<Name> = LazyLock::new(|| Name::from_string("Dir.1₂"));
    pub static DIR_LE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Dir.le"));
    pub static DIR_HOM: LazyLock<Name> = LazyLock::new(|| Name::from_string("Dir.Hom"));
    pub static DIR_HOM_LAM: LazyLock<Name> = LazyLock::new(|| Name::from_string("Dir.homLam"));
    pub static DIR_HOM_APP: LazyLock<Name> = LazyLock::new(|| Name::from_string("Dir.homApp"));
    // Segal layer (the 2-simplex filler + its degeneracy).
    pub static DIR_HOM2: LazyLock<Name> = LazyLock::new(|| Name::from_string("Dir.Hom2"));
    pub static DIR_DEGEN2: LazyLock<Name> = LazyLock::new(|| Name::from_string("Dir.degen2"));
}

/// The directed interval `𝟚` as a (nullary) reserved `Const`.
pub(crate) fn dir_interval() -> Expr {
    Expr::const_(dir_names::DIR_INTERVAL.clone(), Vec::<Level>::new())
}

/// The source endpoint `0₂ : 𝟚`.
pub(crate) fn dir_i0() -> Expr {
    Expr::const_(dir_names::DIR_I0.clone(), Vec::<Level>::new())
}

/// The target endpoint `1₂ : 𝟚`.
pub(crate) fn dir_i1() -> Expr {
    Expr::const_(dir_names::DIR_I1.clone(), Vec::<Level>::new())
}

/// The order proposition `x ≤ y` (`Dir.le x y : Type`).
pub(crate) fn dir_le(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(dir_names::DIR_LE.clone(), Vec::<Level>::new()),
        [x, y],
    )
}

/// The hom / extension type `hom_A(x,y)` at level `lvl` (`Dir.Hom.{lvl} A x y`).
pub(crate) fn dir_hom(lvl: Level, a: Expr, x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(dir_names::DIR_HOM.clone(), vec![lvl]),
        [a, x, y],
    )
}

/// The hom introduction `homLam A f : hom_A(f 0₂, f 1₂)` (`f : 𝟚 → A`).
pub(crate) fn dir_hom_lam(lvl: Level, a: Expr, f: Expr) -> Expr {
    Expr::apps(
        Expr::const_(dir_names::DIR_HOM_LAM.clone(), vec![lvl]),
        [a, f],
    )
}

/// The hom elimination / application `homApp A x y p i : A`.
pub(crate) fn dir_hom_app(lvl: Level, a: Expr, x: Expr, y: Expr, p: Expr, i: Expr) -> Expr {
    Expr::apps(
        Expr::const_(dir_names::DIR_HOM_APP.clone(), vec![lvl]),
        [a, x, y, p, i],
    )
}

/// The **identity arrow** (reflexivity 1-cell) `idArr A x : hom_A(x, x)`, built
/// as the constant directed morphism `homLam A (λ _:𝟚. x)`. This is a genuine
/// derived term (`homLam` of a constant function), NOT an axiom — its endpoints
/// are `(λ_.x) 0₂ ≡ x` and `(λ_.x) 1₂ ≡ x`, so it inhabits `Dir.Hom A x x`.
///
/// `x` must be a closed-at-depth-0 term (no loose `BVar 0`); callers pass a term
/// from the ambient context, which is then placed under the fresh `λ _:𝟚`
/// binder. Because directed-mode terms are locally-nameless (binders opened to
/// `FVar`s before reaching here), `x` carries no de Bruijn reference to the new
/// binder, so no shifting is required.
pub(crate) fn dir_id_arr(lvl: Level, a: Expr, x: Expr) -> Expr {
    let const_x = Expr::lam(BinderInfo::Default, dir_interval(), x);
    dir_hom_lam(lvl, a, const_x)
}

// ────────────────────────────────────────────────────────────────────────────
// Segal layer — the 2-simplex filler `Dir.Hom2`, its degeneracy `Dir.degen2`,
// and the `isSegal` / `comp` constructions built on top of the **2LTT bridge**
// (the cubical `Sigma`/`isContr`/`Path` machinery is available in Directed mode,
// see `CleanMode::has_cubical_layer`).
// ────────────────────────────────────────────────────────────────────────────

/// The **2-simplex filler / triangle type** `Dir.Hom2 A x y z f g h` — the type
/// of 2-simplices `Δ² → A` whose three edges are the directed morphisms
/// `f : hom_A(x,y)` (the `0→1` face), `g : hom_A(y,z)` (the `1→2` face), and the
/// **composite** `h : hom_A(x,z)` (the `0→2` face). This is the directed analogue
/// of an extension type over the 2-simplex shape `Δ²`; here it is a reserved
/// `Const` former (no shape algebra yet — see the roadmap), so the *type* of
/// composite-witnesses is nameable even before the full `Δ²` cofibration lattice.
#[allow(clippy::too_many_arguments)]
pub(crate) fn dir_hom2(
    lvl: Level,
    a: Expr,
    x: Expr,
    y: Expr,
    z: Expr,
    f: Expr,
    g: Expr,
    h: Expr,
) -> Expr {
    Expr::apps(
        Expr::const_(dir_names::DIR_HOM2.clone(), vec![lvl]),
        [a, x, y, z, f, g, h],
    )
}

/// The **degenerate 2-simplex** `Dir.degen2 A y z g : Dir.Hom2 A y y z (idArr A y) g g`
/// — the triangle `s₀(g)` of an arrow `g : hom_A(y,z)`, whose `0→1` edge is the
/// identity `idArr A y`, `1→2` edge is `g`, and composite `0→2` edge is `g`. It
/// witnesses that `g` is *a* composite of `id_y` then `g` (`comp(g, id_y) ≃ g`).
/// Sound: degeneracies exist in every simplicial type (the `σ₀` map), so this
/// triangle is genuinely inhabited — like `homLam`, an introduction with a
/// model-justified inhabitant, not a contractibility claim.
pub(crate) fn dir_degen2(lvl: Level, a: Expr, y: Expr, z: Expr, g: Expr) -> Expr {
    Expr::apps(
        Expr::const_(dir_names::DIR_DEGEN2.clone(), vec![lvl]),
        [a, y, z, g],
    )
}

/// The **type of composite-witnesses** of `f : hom_A(x,y)` and `g : hom_A(y,z)`:
///
/// ```text
/// compositeType A x y z f g := Σ (h : hom_A(x,z)). Dir.Hom2 A x y z f g h
/// ```
///
/// i.e. a composite edge `h` *together with* a 2-simplex filling the triangle
/// `f, g, h`. Built with the cubical `Sigma` from the 2LTT bridge. `a x y z f g`
/// are valid in the current context; `lvl` is the universe of `A`.
pub(crate) fn dir_composite_type(
    lvl: Level,
    a: &Expr,
    x: &Expr,
    y: &Expr,
    z: &Expr,
    f: &Expr,
    g: &Expr,
) -> Expr {
    use crate::tc::reduction::kan::sigma_type;
    let hom_xz = dir_hom(lvl.clone(), a.clone(), x.clone(), z.clone());
    // B = λ (h : hom_A(x,z)). Dir.Hom2 A x y z f g h.   Under `λ h`, the captured
    // a/x/y/z/f/g lift by one and `h` is BVar0.
    let bfam = Expr::lam(
        BinderInfo::Default,
        hom_xz.clone(),
        dir_hom2(
            lvl.clone(),
            a.lift(1),
            x.lift(1),
            y.lift(1),
            z.lift(1),
            f.lift(1),
            g.lift(1),
            Expr::bvar(0),
        ),
    );
    sigma_type(lvl, &hom_xz, &bfam)
}

/// The **Segal condition** `isSegal A` — "every composable pair of arrows has a
/// *contractible* type of composites":
///
/// ```text
/// isSegal A := Π (x y z : A) (f : hom_A(x,y)) (g : hom_A(y,z)).
///                isContr (compositeType A x y z f g)
/// ```
///
/// The `isContr` is the cubical contractibility from the 2LTT bridge — THIS is
/// what the bridge unlocks (it is unavailable to the bare directed interval). For
/// a Segal type the composite is unique up to a contractible choice, the directed
/// analogue of "composition exists and is essentially unique". `a` (= A) is valid
/// in the current context; `lvl` is the universe of `A`.
pub(crate) fn dir_is_segal(lvl: Level, a: &Expr) -> Expr {
    use crate::tc::reduction::kan::is_contr_type;
    // Telescope Π x. Π y. Π z. Π f. Π g. isContr(compositeType …), de Bruijn
    // computed at the innermost (body) context [x,y,z,f,g] over the ambient `a`.
    //   [x,y,z,f,g]: a lifts by 5; x=BVar4, y=BVar3, z=BVar2, f=BVar1, g=BVar0.
    let a5 = a.lift(5);
    let body = is_contr_type(
        lvl.clone(),
        &dir_composite_type(
            lvl.clone(),
            &a5,
            &Expr::bvar(4),
            &Expr::bvar(3),
            &Expr::bvar(2),
            &Expr::bvar(1),
            &Expr::bvar(0),
        ),
    );
    // g : hom_A(y,z)  under [x,y,z,f]: a lifts 4; y=BVar2, z=BVar1.
    let g_dom = dir_hom(lvl.clone(), a.lift(4), Expr::bvar(2), Expr::bvar(1));
    // f : hom_A(x,y)  under [x,y,z]: a lifts 3; x=BVar2, y=BVar1.
    let f_dom = dir_hom(lvl.clone(), a.lift(3), Expr::bvar(2), Expr::bvar(1));
    Expr::pi(
        BinderInfo::Default,
        a.clone(), // x : A
        Expr::pi(
            BinderInfo::Default,
            a.lift(1), // y : A
            Expr::pi(
                BinderInfo::Default,
                a.lift(2), // z : A
                Expr::pi(
                    BinderInfo::Default,
                    f_dom,
                    Expr::pi(BinderInfo::Default, g_dom, body),
                ),
            ),
        ),
    )
}

/// **Composition for a Segal type** `comp seg x y z f g : hom_A(x,z)`, defined as
/// the **centre of the contractible composite type**:
///
/// ```text
/// comp seg x y z f g := ((seg x y z f g).centre).fst
/// ```
///
/// where `seg x y z f g : isContr (compositeType …)`, its `.centre` (the `isContr`
/// first projection) is the chosen composite-witness `(h, filler) : compositeType`,
/// and the outer `.fst` reads off the composite arrow `h : hom_A(x,z)`. Both
/// projections are the cubical `Sigma.fst` from the bridge. This is composition
/// *conditional on a Segal witness* — it does NOT assert `A` is Segal; it is the
/// honest "centre of the contractible type" that the Segal condition provides.
///
/// `seg x y z f g` (the applied contractibility witness) and `a x y z f g` are
/// valid in the current context; `lvl` is the universe of `A`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn dir_comp(
    lvl: Level,
    a: &Expr,
    x: &Expr,
    y: &Expr,
    z: &Expr,
    f: &Expr,
    g: &Expr,
    seg_app: &Expr,
) -> Expr {
    use crate::tc::reduction::kan::{is_contr_bfam, sigma_fst};
    let comp_ty = dir_composite_type(lvl.clone(), a, x, y, z, f, g);
    // centre : compositeType  =  (seg_app : isContr compositeType).fst
    let centre = sigma_fst(lvl.clone(), &comp_ty, &is_contr_bfam(&comp_ty), seg_app);
    // comp = centre.fst : hom_A(x,z).  The composite Σ's components:
    //   A-part = hom_A(x,z); B-family = λ h. Dir.Hom2 A x y z f g h.
    let hom_xz = dir_hom(lvl.clone(), a.clone(), x.clone(), z.clone());
    let bfam = Expr::lam(
        BinderInfo::Default,
        hom_xz.clone(),
        dir_hom2(
            lvl.clone(),
            a.lift(1),
            x.lift(1),
            y.lift(1),
            z.lift(1),
            f.lift(1),
            g.lift(1),
            Expr::bvar(0),
        ),
    );
    sigma_fst(lvl, &hom_xz, &bfam, &centre)
}

/// A **concrete inhabitant** of the composite type `compositeType A y y z (idArr A y) g`
/// — the identity/degeneracy *anchor*. It witnesses that the composite of `id_y`
/// then `g` exists and is `g`, packaged with the degenerate 2-simplex filler:
///
/// ```text
/// (g, degen2 A y z g) : Σ (h : hom_A(y,z)). Dir.Hom2 A y y z (idArr A y) g h
/// ```
///
/// This is genuine *inhabitation* of the composite type for a concrete pair (so
/// the Segal `isContr` of this case is non-vacuous). Full *contractibility* of
/// the concrete case needs the `Δ²` extension / inner-horn uniqueness — roadmap.
/// `a` (= A), `y`, `z`, `g` are valid in the current context; `lvl` is `A`'s
/// universe.
pub(crate) fn dir_degen_composite_witness(
    lvl: Level,
    a: &Expr,
    y: &Expr,
    z: &Expr,
    g: &Expr,
) -> Expr {
    use crate::tc::reduction::kan::sigma_mk;
    let id_y = dir_id_arr(lvl.clone(), a.clone(), y.clone());
    let hom_yz = dir_hom(lvl.clone(), a.clone(), y.clone(), z.clone());
    // B = λ (h : hom_A(y,z)). Dir.Hom2 A y y z (idArr A y) g h  (captured terms lift by 1).
    let bfam = Expr::lam(
        BinderInfo::Default,
        hom_yz.clone(),
        dir_hom2(
            lvl.clone(),
            a.lift(1),
            y.lift(1),
            y.lift(1),
            z.lift(1),
            id_y.lift(1),
            g.lift(1),
            Expr::bvar(0),
        ),
    );
    let degen = dir_degen2(lvl.clone(), a.clone(), y.clone(), z.clone(), g.clone());
    sigma_mk(lvl, &hom_yz, &bfam, g.clone(), degen)
}

/// Register the reserved **directed** constants (see [`dir_names`]) into a
/// **`CleanMode::Directed`** environment, with the interval/type-valued axiom
/// types that make the Expr-encoding genuinely well-typed. The existing
/// inference, certificate builder and certificate verifier then accept
/// `Dir.𝟚`/`Dir.le`/`Dir.Hom`/`Dir.homLam`/`Dir.homApp` terms unchanged — they
/// are plain `Const`/`App` spines.
///
/// The order reduction `Dir.le i j` lands in genuine `Unit`/`Empty` inductives;
/// callers must therefore also register `Unit` (with constructor `Unit.tt`) and
/// `Empty` (zero constructors) inductives so the asymmetry is a real
/// type-theoretic (in)habitation fact, not an opaque axiom dance.
///
/// SOUNDNESS of the axiom set:
/// * `Dir.𝟚` is an opaque type former asserted to be a `Type` with two
///   inhabitants `0₂`/`1₂`. An opaque inhabited type introduces no inconsistency
///   (it is just the 2-element poset, a perfectly good set).
/// * `Dir.le` is an opaque relation `𝟚 → 𝟚 → Type` whose only computation is the
///   [`TypeChecker::try_directed_reduction`] order table (`Unit`/`Empty` on the
///   four endpoint pairs + reflexivity). It has **no introduction axiom**: the
///   only way to inhabit `Dir.le i j` is through the reduction to `Unit` (then
///   `Unit.tt`). So `Dir.le 1₂ 0₂ ↝ Empty` is genuinely uninhabited — no closed
///   proof of `1 ≤ 0` exists, consistent with the `{0 < 1}` poset; and the
///   reduction is type-preserving (`Dir.le x y : Type`, `Unit`/`Empty : Type`).
/// * `Dir.Hom` is the extension/hom-type former; `Dir.homLam` asserts
///   `hom_A(f 0₂, f 1₂)` is inhabited given `f : 𝟚 → A` (true in the intended
///   model — the function *is* the morphism); `Dir.homApp` projects back to `A`
///   (result independent of the hom structure, sound by construction, like
///   `unglue`). Their computation rules (β + boundary) are type-preserving.
///
/// Idempotent-ish: register once per environment. Returns the first registration
/// error if any.
// Not yet wired to a production caller (directed environments are configured by
// tests for now); exercised by the directed soundness-anchor tests.
#[allow(dead_code)]
pub(crate) fn register_directed_axioms(env: &mut Environment) -> Result<(), crate::env::EnvError> {
    let interval = dir_interval;
    let u = Name::from_string("u");
    let lu = Level::param(u.clone());
    let sort_u = Expr::sort(lu.clone());

    // Level-monomorphic heads (the interval, its endpoints, and the order).
    let mut mono = |name: &str, type_: Expr| -> Result<(), crate::env::EnvError> {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
    };

    // Dir.𝟚 : Type  (the strict interval, a `Sort 1`).
    mono("Dir.𝟚", Expr::type_())?;
    // Dir.0₂ , Dir.1₂ : Dir.𝟚.
    mono("Dir.0₂", interval())?;
    mono("Dir.1₂", interval())?;
    // Dir.le : Dir.𝟚 → Dir.𝟚 → Type — the bounded total order `0 ≤ x ≤ 1`.
    mono(
        "Dir.le",
        Expr::arrow(interval(), Expr::arrow(interval(), Expr::type_())),
    )?;

    // Level-polymorphic heads (the hom-type former and its intro/elim).
    let mut poly = |name: &str, type_: Expr| -> Result<(), crate::env::EnvError> {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![u.clone()],
            type_,
        })
    };

    // Dir.Hom.{u} (A : Sort u) (x y : A) : Sort u.
    // de Bruijn: under [A] A=BVar0; under [A,x] A=BVar1; result `Sort u`.
    let hom_ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // x : A
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // y : A
                sort_u.clone(),
            ),
        ),
    );
    poly("Dir.Hom", hom_ty)?;

    // Dir.homLam.{u} (A : Sort u) (f : 𝟚 → A) : Dir.Hom A (f 0₂) (f 1₂).
    // de Bruijn: the domain `𝟚 → A` is `Π(_:𝟚). A`; under that arrow's binder
    // (context [A, _]) `A` is BVar1. Under [A, f] the result `Dir.Hom A (f 0₂)(f 1₂)`
    // has A=BVar1, f=BVar0.
    let hom_lam_ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::arrow(interval(), Expr::bvar(1)), // f : 𝟚 → A  (A under the arrow binder)
            dir_hom(
                lu.clone(),
                Expr::bvar(1),                      // A
                Expr::app(Expr::bvar(0), dir_i0()), // f 0₂
                Expr::app(Expr::bvar(0), dir_i1()), // f 1₂
            ),
        ),
    );
    poly("Dir.homLam", hom_lam_ty)?;

    // Dir.homApp.{u} (A : Sort u) (x y : A) (p : Dir.Hom A x y) (i : 𝟚) : A.
    // de Bruijn:
    //   [A]            A=0          (x : A)
    //   [A,x]          A=1          (y : A)
    //   [A,x,y]        A=2,x=1,y=0  (p : Dir.Hom A x y)
    //   [A,x,y,p]      A=3          (i : 𝟚)
    //   [A,x,y,p,i]    A=4          (result A)
    let hom_app_ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // x : A
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // y : A
                Expr::pi(
                    BinderInfo::Default,
                    dir_hom(lu.clone(), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)), // p : Dir.Hom A x y
                    Expr::pi(
                        BinderInfo::Default,
                        interval(),    // i : 𝟚
                        Expr::bvar(4), // result : A
                    ),
                ),
            ),
        ),
    );
    poly("Dir.homApp", hom_app_ty)?;

    // ── Segal layer (the 2-simplex filler + its degeneracy) ──────────────────
    //
    // SOUNDNESS of the Segal axiom set:
    // * `Dir.Hom2` is an opaque type former for the 2-simplex/triangle filler
    //   `Δ² → A` with prescribed edges. Like `Dir.Hom`, it is an inhabited-in-the
    //   -model `Sort u` former; naming the *type* of fillers adds no inconsistency
    //   (it carries no introduction beyond `degen2`, so it cannot manufacture a
    //   contradiction). `isSegal`/`comp` only *quantify over* and *project from*
    //   it; they never assert it is contractible.
    // * `Dir.degen2` asserts the one genuinely-true filler: the degeneracy
    //   `s₀(g)` of an arrow `g : hom_A(y,z)`, with edges `id_y, g, g`. Degeneracies
    //   exist in every simplicial type, so this inhabitant is real (sound exactly
    //   like `homLam` — a model-justified introduction).

    // Dir.Hom2.{u} (A:Sort u)(x y z:A)(f:Hom A x y)(g:Hom A y z)(h:Hom A x z) : Sort u.
    // de Bruijn (binders A,x,y,z,f,g,h):
    //   x:[A] A=0;  y:[A,x] A=1;  z:[A,x,y] A=2;
    //   f:[A,x,y,z]   Hom A x y = Hom(3,2,1);
    //   g:[A,x,y,z,f] Hom A y z = Hom(4,2,1);
    //   h:[A,x,y,z,f,g] Hom A x z = Hom(5,4,2);  result [A..h]: Sort u.
    let hom2_ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // x : A
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // y : A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(2), // z : A
                    Expr::pi(
                        BinderInfo::Default,
                        dir_hom(lu.clone(), Expr::bvar(3), Expr::bvar(2), Expr::bvar(1)), // f
                        Expr::pi(
                            BinderInfo::Default,
                            dir_hom(lu.clone(), Expr::bvar(4), Expr::bvar(2), Expr::bvar(1)), // g
                            Expr::pi(
                                BinderInfo::Default,
                                dir_hom(lu.clone(), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2)), // h
                                sort_u.clone(),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    poly("Dir.Hom2", hom2_ty)?;

    // Dir.degen2.{u} (A:Sort u)(y z:A)(g:Hom A y z) : Hom2 A y y z (idArr A y) g g.
    // de Bruijn (binders A,y,z,g):
    //   y:[A] A=0;  z:[A,y] A=1;  g:[A,y,z] Hom A y z = Hom(2,1,0);
    //   result [A,y,z,g]: A=3, y=2, z=1, g=0.
    //   idArr A y = homLam A (λ_:𝟚. y); under the extra λ, y = BVar3.
    let id_arr_y = dir_hom_lam(
        lu.clone(),
        Expr::bvar(3),                                             // A
        Expr::lam(BinderInfo::Default, interval(), Expr::bvar(3)), // λ_:𝟚. y
    );
    let degen2_ty = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // y : A
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // z : A
                Expr::pi(
                    BinderInfo::Default,
                    dir_hom(lu.clone(), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)), // g : Hom A y z
                    dir_hom2(
                        lu.clone(),
                        Expr::bvar(3), // A
                        Expr::bvar(2), // v0 = y
                        Expr::bvar(2), // v1 = y (degenerate vertex)
                        Expr::bvar(1), // v2 = z
                        id_arr_y,      // f = idArr A y
                        Expr::bvar(0), // g
                        Expr::bvar(0), // h = g (composite)
                    ),
                ),
            ),
        ),
    );
    poly("Dir.degen2", degen2_ty)?;

    Ok(())
}

impl<'env> TypeChecker<'env> {
    /// Attempt one head-reduction step for an encoded **directed** redex
    /// (`Dir.le …`, `Dir.homApp …`). `head` is the spine-head constant of `e`
    /// (already extracted by the WHNF trampoline). Only called in
    /// `CleanMode::Directed` (gated at the call site in `whnf.rs`, mirroring the
    /// `Cubical`-gated `try_glue_reduction`). Returns `None` (stuck) for any
    /// non-directed head or any redex that does not decide.
    ///
    /// SOUNDNESS: every reduct below is type-preserving and reflects a valid law
    /// of the directed interval. A fully-neutral redex stays **stuck** — a stuck
    /// term is sound; a wrong reduction is not.
    pub(in crate::tc) fn try_directed_reduction(
        &self,
        e: &Expr,
        head: &Name,
        mode: WhnfMode,
    ) -> Option<Expr> {
        if *head == *dir_names::DIR_LE {
            return self.try_dir_le_reduction(e, mode);
        }
        if *head == *dir_names::DIR_HOM_APP {
            return self.try_dir_hom_app_reduction(e, mode);
        }
        None
    }

    /// Decide the directed order `Dir.le a b` exactly as the 2-element poset
    /// `{0 < 1}`:
    ///
    /// ```text
    /// le 0₂ 0₂ ↝ Unit   le 0₂ 1₂ ↝ Unit   le 1₂ 1₂ ↝ Unit   le 1₂ 0₂ ↝ Empty
    /// le a  a  ↝ Unit                                        (reflexivity)
    /// ```
    ///
    /// Any other (genuinely neutral, non-equal) pair stays **stuck**. This is the
    /// directedness anchor: `0₂ ≤ 1₂ ↝ Unit` (inhabited by `Unit.tt`) while
    /// `1₂ ≤ 0₂ ↝ Empty` (uninhabited; `¬(1₂ ≤ 0₂)` provable). Type-preserving:
    /// `Dir.le a b : Type` and `Unit`/`Empty : Type`.
    fn try_dir_le_reduction(&self, e: &Expr, mode: WhnfMode) -> Option<Expr> {
        let args = e.get_app_args();
        if args.len() != 2 {
            return None;
        }
        let a = self.whnf_recurse(args[0], mode);
        let b = self.whnf_recurse(args[1], mode);

        let is_i0 =
            |x: &Expr| matches!(x.kind(), ExprKind::Const(n, _) if *n == *dir_names::DIR_I0);
        let is_i1 =
            |x: &Expr| matches!(x.kind(), ExprKind::Const(n, _) if *n == *dir_names::DIR_I1);

        let unit = || Expr::const_(Name::from_string("Unit"), Vec::<Level>::new());
        let empty = || Expr::const_(Name::from_string("Empty"), Vec::<Level>::new());

        // The four endpoint pairs (the order table of {0 < 1}).
        if (is_i0(&a) && is_i0(&b))      // 0 ≤ 0
            || (is_i0(&a) && is_i1(&b))  // 0 ≤ 1
            || (is_i1(&a) && is_i1(&b))
        // 1 ≤ 1
        {
            return Some(unit());
        }
        if is_i1(&a) && is_i0(&b) {
            // 1 ≤ 0 — the one false case; directedness made manifest.
            return Some(empty());
        }
        // Reflexivity `a ≤ a` for any (possibly neutral) point `a` that is
        // definitionally equal to `b`. Sound: `x ≤ x` always holds in a poset.
        if self.is_def_eq(&a, &b) {
            return Some(unit());
        }
        None
    }

    /// Compute `Dir.homApp A x y p i` — the extension/hom eliminator:
    ///
    /// ```text
    /// homApp A x y (homLam A' f) i ↝ f i        (β: a morphism applied is its function)
    /// homApp A x y p 0₂           ↝ x           (boundary at the source)
    /// homApp A x y p 1₂           ↝ y           (boundary at the target)
    /// ```
    ///
    /// β is tried first; then the literal-endpoint boundaries. A neutral `p` with
    /// a neutral `i` stays **stuck**. Type-preserving: `homApp … : A`, and `x`,
    /// `y`, `f i` all have type `A`. The two rules are coherent — for a
    /// well-typed `homApp A x y (homLam A' f) 0₂`, β gives `f 0₂` and the boundary
    /// gives `x`, but typing forces `x ≡ f 0₂` (since `homLam f : Dir.Hom A (f 0₂)(f 1₂)`).
    fn try_dir_hom_app_reduction(&self, e: &Expr, mode: WhnfMode) -> Option<Expr> {
        let args = e.get_app_args();
        // Dir.homApp A x y p i — the five explicit arguments.
        if args.len() != 5 {
            return None;
        }
        let x = args[1];
        let y = args[2];
        let p = args[3];
        let i = args[4];

        // β: p ↝ Dir.homLam A' f  ⇒  f i.
        let p_whnf = self.whnf_recurse(p, mode);
        if let ExprKind::Const(p_head, _) = p_whnf.get_app_fn().kind() {
            if *p_head == *dir_names::DIR_HOM_LAM {
                let p_args = p_whnf.get_app_args();
                // Dir.homLam A f — A and f.
                if p_args.len() == 2 {
                    let f = p_args[1];
                    return Some(Expr::app(f.clone(), i.clone()));
                }
            }
        }

        // Boundary at the literal endpoints.
        let i_whnf = self.whnf_recurse(i, mode);
        if matches!(i_whnf.kind(), ExprKind::Const(n, _) if *n == *dir_names::DIR_I0) {
            return Some(x.clone());
        }
        if matches!(i_whnf.kind(), ExprKind::Const(n, _) if *n == *dir_names::DIR_I1) {
            return Some(y.clone());
        }
        None
    }
}
