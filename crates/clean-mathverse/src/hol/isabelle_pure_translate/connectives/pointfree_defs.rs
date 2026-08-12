// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful clean polymorphic `Definition`s for the point-free HOL logical
//! constants whose bodies are genuinely *definitionally* equal to their `_def`
//! RHS (unlike `HOL.All`, whose `∀x. P x` is only propositionally equal to
//! `P = λx.True` and so uses a `propext` bridge instead):
//!
//! ```text
//! HOL.Uniq          : (α⇒Prop)⇒Prop  := λP. ∀x y. P x → P y → x = y
//! HOL.Ex1           : (α⇒Prop)⇒Prop  := λP. ∃x. P x ∧ (∀y. P y → y = x)
//! HOL.Let           : α ⇒ (α⇒β) ⇒ β  := λs f. f s
//! HOL.induct_forall : (α⇒Prop)⇒Prop  := λP. ∀x. P x
//! HOL.induct_equal  : α ⇒ α ⇒ Prop   := λx y. @Eq α x y
//! HOL.NO_MATCH      : α ⇒ β ⇒ Prop   := λ_ _. True
//! HOL.induct_conj   : Prop⇒Prop⇒Prop := λA B. conj A B
//! HOL.ASSUMPTION    : Prop⇒Prop      := λA. A
//! Code_Generator.holds : Prop        := ((λx:Prop. x) = (λx:Prop. x))
//! ```
//!
//! The last three are **monomorphic** (no object type variables): `induct_conj`
//! (`induct_conj A B ≡ A ∧ B`) and `ASSUMPTION` (`ASSUMPTION A ≡ A`) are the
//! induction/ML-tactic marker wrappers over `bool`, and `Code_Generator.holds`
//! (`holds ≡ ((λx. x) ≡ (λx. x))`) is the code-generator's `prop`-level truth —
//! definitionally the SAME `Eq (Prop→Prop) id id` encoding as `HOL.True`.
//!
//! Each has **no axiom content** (built from `∀`/`→`/`@Eq`/the `∃`/`∧`/`True`
//! encodings — pure λ, foundational closure), so it is a genuine conservative
//! extension and every consumer stays `KernelVerified` to the three foundationals.
//! [`Ctx::embed_const_term`] emits each occurrence of one of these constants as its
//! def-const applied to the use-site's solved object type(s), so an applied LHS
//! `C args` δβ-reduces to exactly the same body the `…_def_raw` RHS spells — making
//! the point-free definitional axiom genuinely reflexive (kernel-checked `Eq.refl`
//! over DISTINCT operands: the def-const LHS vs the embedded body), never a
//! `body = body` tautology.

use clean_kernel::expr::FVarId;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Expr};

use super::super::obj_level;
use super::sets::ex_encoding;

/// The kernel declaration name of the clean polymorphic `Definition` registered
/// for a point-free HOL logical constant, or `None` for any other name. Routing
/// [`Ctx::embed_const_term`] through this makes each constant's occurrences share
/// one defeq-unfolding head symbol (like [`super::connective_def_name`]).
pub(crate) fn pointfree_const_def_name(name: &str) -> Option<&'static str> {
    match name {
        "HOL.Uniq" => Some("isabelle.def.HOL.Uniq"),
        "HOL.Ex1" => Some("isabelle.def.HOL.Ex1"),
        "HOL.Let" => Some("isabelle.def.HOL.Let"),
        "HOL.induct_forall" => Some("isabelle.def.HOL.induct_forall"),
        "HOL.induct_equal" => Some("isabelle.def.HOL.induct_equal"),
        "HOL.NO_MATCH" => Some("isabelle.def.HOL.NO_MATCH"),
        "HOL.induct_conj" => Some("isabelle.def.HOL.induct_conj"),
        "HOL.ASSUMPTION" => Some("isabelle.def.HOL.ASSUMPTION"),
        "Code_Generator.holds" => Some("isabelle.def.Code_Generator.holds"),
        // The `HOL.ATP` first-order aliases of the connectives/quantifiers
        // (`fFalse ≡ False`, `fNot ≡ λP. ¬P`, `fAll ≡ λP. All P`, …): each
        // def-const's value δβ-unfolds to exactly the aliased connective's own
        // embedding, so the `ATP.f*_def_raw` axioms verify reflexively.
        "ATP.fFalse" => Some("isabelle.def.ATP.fFalse"),
        "ATP.fTrue" => Some("isabelle.def.ATP.fTrue"),
        "ATP.fNot" => Some("isabelle.def.ATP.fNot"),
        "ATP.fconj" => Some("isabelle.def.ATP.fconj"),
        "ATP.fdisj" => Some("isabelle.def.ATP.fdisj"),
        "ATP.fimplies" => Some("isabelle.def.ATP.fimplies"),
        "ATP.fAll" => Some("isabelle.def.ATP.fAll"),
        "ATP.fEx" => Some("isabelle.def.ATP.fEx"),
        "ATP.fequal" => Some("isabelle.def.ATP.fequal"),
        "ATP.fComp" => Some("isabelle.def.ATP.fComp"),
        "ATP.fChoice" => Some("isabelle.def.ATP.fChoice"),
        _ => None,
    }
}

/// `@Eq α a b` at the object level.
fn eq_obj(alpha: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [alpha, a, b],
    )
}

/// The `HOL.True` connective def-const (`isabelle.def.HOL.True`, a closed `Prop`).
fn true_const() -> Expr {
    Expr::const_str("isabelle.def.HOL.True")
}

/// The `HOL.conj` connective def-const (`isabelle.def.HOL.conj : Prop→Prop→Prop`).
fn conj_const() -> Expr {
    Expr::const_str("isabelle.def.HOL.conj")
}

/// `HOL.Uniq : (α⇒Prop)⇒Prop := λ(P:α→Prop). ∀(x y:α). P x → P y → x = y`.
/// One leading `Type` binder α.
fn build_uniq() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_9a01); // α : Type
    let fp = FVarId::new(0x1_9a02); // P : α → Prop
    let fx = FVarId::new(0x1_9a03); // x : α
    let fy = FVarId::new(0x1_9a04); // y : α
    let alpha = || Expr::fvar(fa);
    let p = || Expr::fvar(fp);
    let pred_ty = || Expr::arrow(alpha(), Expr::prop());

    // body: ∀x y. P x → P y → x = y
    let px = Expr::app(p(), Expr::fvar(fx));
    let py = Expr::app(p(), Expr::fvar(fy));
    let eq_xy = eq_obj(alpha(), Expr::fvar(fx), Expr::fvar(fy));
    let imp2 = Expr::arrow(px, Expr::arrow(py, eq_xy));
    // ∀y. imp2
    let forall_y = Expr::pi(BinderInfo::Default, alpha(), imp2.abstract_fvar(fy));
    // ∀x. forall_y
    let forall_xy = Expr::pi(BinderInfo::Default, alpha(), forall_y.abstract_fvar(fx));

    // value: λ(α:Type)(P:α→Prop). forall_xy
    let v = forall_xy.abstract_fvar(fp);
    let v = Expr::lam(BinderInfo::Default, pred_ty(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    // type: Π(α:Type)(P:α→Prop). Prop
    let t = Expr::prop().abstract_fvar(fp);
    let t = Expr::pi(BinderInfo::Default, pred_ty(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `HOL.Ex1 : (α⇒Prop)⇒Prop := λ(P:α→Prop). ∃x. P x ∧ (∀y. P y → y = x)`.
/// Uses the impredicative `∃` ([`ex_encoding`]) and the `HOL.conj` def-const so it
/// coincides with the embedded RHS (which uses the same `Ex`/`conj` arms).
fn build_ex1() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_9b01); // α : Type
    let fp = FVarId::new(0x1_9b02); // P : α → Prop
    let fx = FVarId::new(0x1_9b03); // x : α  (the ∃-bound witness)
    let fy = FVarId::new(0x1_9b04); // y : α
    let alpha = || Expr::fvar(fa);
    let p = || Expr::fvar(fp);
    let pred_ty = || Expr::arrow(alpha(), Expr::prop());

    // inner predicate `λx. P x ∧ (∀y. P y → y = x)`
    let px = Expr::app(p(), Expr::fvar(fx));
    let py = Expr::app(p(), Expr::fvar(fy));
    let eq_yx = eq_obj(alpha(), Expr::fvar(fy), Expr::fvar(fx));
    let uniq_body = Expr::arrow(py, eq_yx);
    let forall_y = Expr::pi(BinderInfo::Default, alpha(), uniq_body.abstract_fvar(fy));
    // P x ∧ (∀y. …)
    let conj = Expr::apps(conj_const(), [px, forall_y]);
    // inner : λx. conj
    let inner = Expr::lam(BinderInfo::Default, alpha(), conj.abstract_fvar(fx));
    // ∃x. inner  via the impredicative encoding over α with predicate `inner`.
    let ex_body = ex_encoding(&alpha(), &inner);

    // value: λ(α:Type)(P:α→Prop). ex_body
    let v = ex_body.abstract_fvar(fp);
    let v = Expr::lam(BinderInfo::Default, pred_ty(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    let t = Expr::prop().abstract_fvar(fp);
    let t = Expr::pi(BinderInfo::Default, pred_ty(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `HOL.Let : α ⇒ (α⇒β) ⇒ β := λ(s:α)(f:α→β). f s`. Two leading `Type` binders
/// α, β (in the RHS-embedding first-occurrence order: α from `λs:α`, then β).
fn build_let() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_9c01); // α : Type
    let fb = FVarId::new(0x1_9c02); // β : Type
    let fs = FVarId::new(0x1_9c03); // s : α
    let ff = FVarId::new(0x1_9c04); // f : α → β
    let alpha = || Expr::fvar(fa);
    let beta = || Expr::fvar(fb);
    let fun_ty = || Expr::arrow(alpha(), beta());

    // body: f s
    let body = Expr::app(Expr::fvar(ff), Expr::fvar(fs));
    // value: λ(α β:Type)(s:α)(f:α→β). f s — innermost-first.
    let v = body.abstract_fvar(ff);
    let v = Expr::lam(BinderInfo::Default, fun_ty(), v);
    let v = v.abstract_fvar(fs);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fb);
    let v = Expr::lam(BinderInfo::Default, Expr::type_(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    // type: Π(α β:Type)(s:α)(f:α→β). β
    let t = beta().abstract_fvar(ff);
    let t = Expr::pi(BinderInfo::Default, fun_ty(), t);
    let t = t.abstract_fvar(fs);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fb);
    let t = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `HOL.induct_forall : (α⇒Prop)⇒Prop := λ(P:α→Prop). ∀x. P x`.
fn build_induct_forall() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_9d01); // α : Type
    let fp = FVarId::new(0x1_9d02); // P : α → Prop
    let fx = FVarId::new(0x1_9d03); // x : α
    let alpha = || Expr::fvar(fa);
    let pred_ty = || Expr::arrow(alpha(), Expr::prop());

    let px = Expr::app(Expr::fvar(fp), Expr::fvar(fx));
    let forall_x = Expr::pi(BinderInfo::Default, alpha(), px.abstract_fvar(fx));

    let v = forall_x.abstract_fvar(fp);
    let v = Expr::lam(BinderInfo::Default, pred_ty(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    let t = Expr::prop().abstract_fvar(fp);
    let t = Expr::pi(BinderInfo::Default, pred_ty(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `HOL.induct_equal : α ⇒ α ⇒ Prop := λ(x y:α). @Eq α x y`.
fn build_induct_equal() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_9e01); // α : Type
    let fx = FVarId::new(0x1_9e02); // x : α
    let fy = FVarId::new(0x1_9e03); // y : α
    let alpha = || Expr::fvar(fa);

    let body = eq_obj(alpha(), Expr::fvar(fx), Expr::fvar(fy));
    let v = body.abstract_fvar(fy);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fx);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    // type: Π(α:Type)(x y:α). Prop
    let t = Expr::prop().abstract_fvar(fy);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fx);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `HOL.NO_MATCH : α ⇒ β ⇒ Prop := λ(_:α)(_:β). True`. Two leading `Type` binders.
fn build_no_match() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_9f01); // α : Type
    let fb = FVarId::new(0x1_9f02); // β : Type
    let fpat = FVarId::new(0x1_9f03); // pat : α (ignored)
    let fval = FVarId::new(0x1_9f04); // val : β (ignored)
    let alpha = || Expr::fvar(fa);
    let beta = || Expr::fvar(fb);

    let body = true_const();
    let v = body.abstract_fvar(fval);
    let v = Expr::lam(BinderInfo::Default, beta(), v);
    let v = v.abstract_fvar(fpat);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fb);
    let v = Expr::lam(BinderInfo::Default, Expr::type_(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    let t = Expr::prop().abstract_fvar(fval);
    let t = Expr::pi(BinderInfo::Default, beta(), t);
    let t = t.abstract_fvar(fpat);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fb);
    let t = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `HOL.induct_conj : Prop ⇒ Prop ⇒ Prop := λ(A B:Prop). conj A B` — the
/// induction-package conjunction marker (`induct_conj_def`:
/// `induct_conj A B ≡ A ∧ B`). Monomorphic; uses the `HOL.conj` def-const so an
/// applied `induct_conj A B` δβ-reduces to exactly the embedded `_def` RHS.
fn build_induct_conj() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a001); // A : Prop
    let fb = FVarId::new(0x1_a002); // B : Prop

    let body = Expr::apps(conj_const(), [Expr::fvar(fa), Expr::fvar(fb)]);
    let v = body.abstract_fvar(fb);
    let v = Expr::lam(BinderInfo::Default, Expr::prop(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::prop(), v);

    let type_ = Expr::arrow(Expr::prop(), Expr::arrow(Expr::prop(), Expr::prop()));
    (value, type_)
}

/// `HOL.ASSUMPTION : Prop ⇒ Prop := λ(A:Prop). A` — the ML-tactic assumption
/// marker (`ASSUMPTION_def`: `ASSUMPTION A ≡ A`, the identity on `bool`).
fn build_assumption() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a101); // A : Prop
    let v = Expr::fvar(fa).abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::prop(), v);
    let type_ = Expr::arrow(Expr::prop(), Expr::prop());
    (value, type_)
}

// ---------------------------------------------------------------------------
// `HOL.ATP` first-order aliases (round-9). The ATP theory defines a first-order
// alias for each connective/quantifier (`fFalse ≡ False`, `fNot ≡ λP. ¬P`,
// `fconj ≡ λP Q. P ∧ Q`, `fAll ≡ λP. All P`, `fequal ≡ λx y. x = y`,
// `fComp ≡ λP x. ¬ P x`, `fChoice ≡ Eps`, …). Each def-const's value is the
// aliased connective's OWN embedding (the `isabelle.def.HOL.*` def-consts /
// `Pi`-arrow / `@Eq` / the impredicative `∃`), so an applied `fX args`
// δβ-reduces to exactly what the `ATP.fX_def_raw` RHS embeds to — the raw
// axiom is genuinely reflexive, never a `body = body` tautology (the stored
// LHS stays the def-const application, the RHS the direct connective form).
// No axiom content anywhere: pure λ over the foundational encodings.
// ---------------------------------------------------------------------------

/// `ATP.fFalse : bool := False` — the def-const value IS the `HOL.False`
/// def-const (which δ-unfolds to the `∀P. P` encoding).
fn build_atp_ffalse() -> (Expr, Expr) {
    (Expr::const_str("isabelle.def.HOL.False"), Expr::prop())
}

/// `ATP.fTrue : bool := True` — the `HOL.True` def-const.
fn build_atp_ftrue() -> (Expr, Expr) {
    (Expr::const_str("isabelle.def.HOL.True"), Expr::prop())
}

/// `ATP.fNot : bool ⇒ bool := λ(A:Prop). Not A` (the `HOL.Not` def-const).
fn build_atp_fnot() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a201); // A : Prop
    let body = Expr::app(Expr::const_str("isabelle.def.HOL.Not"), Expr::fvar(fa));
    let value = Expr::lam(BinderInfo::Default, Expr::prop(), body.abstract_fvar(fa));
    let type_ = Expr::arrow(Expr::prop(), Expr::prop());
    (value, type_)
}

/// A binary `bool ⇒ bool ⇒ bool` ATP alias `λ(A B:Prop). body(A, B)`.
fn build_atp_binary(body: impl FnOnce(Expr, Expr) -> Expr) -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a301); // A : Prop
    let fb = FVarId::new(0x1_a302); // B : Prop
    let b = body(Expr::fvar(fa), Expr::fvar(fb));
    let v = b.abstract_fvar(fb);
    let v = Expr::lam(BinderInfo::Default, Expr::prop(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::prop(), v);
    let type_ = Expr::arrow(Expr::prop(), Expr::arrow(Expr::prop(), Expr::prop()));
    (value, type_)
}

/// `ATP.fconj : bool⇒bool⇒bool := λA B. conj A B` (the `HOL.conj` def-const).
fn build_atp_fconj() -> (Expr, Expr) {
    build_atp_binary(|a, b| Expr::apps(conj_const(), [a, b]))
}

/// `ATP.fdisj : bool⇒bool⇒bool := λA B. disj A B` (the `HOL.disj` def-const).
fn build_atp_fdisj() -> (Expr, Expr) {
    build_atp_binary(|a, b| Expr::apps(Expr::const_str("isabelle.def.HOL.disj"), [a, b]))
}

/// `ATP.fimplies : bool⇒bool⇒bool := λA B. A → B` (implication is the clean
/// arrow, exactly how an applied `HOL.implies` embeds).
fn build_atp_fimplies() -> (Expr, Expr) {
    build_atp_binary(Expr::arrow)
}

/// `ATP.fAll : (α⇒bool)⇒bool := λ(α:Type)(P:α→Prop). ∀x. P x` — same shape as
/// [`build_induct_forall`] (an applied `HOL.All P` embeds to the clean `Pi`).
fn build_atp_fall() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a401); // α : Type
    let fp = FVarId::new(0x1_a402); // P : α → Prop
    let fx = FVarId::new(0x1_a403); // x : α
    let alpha = || Expr::fvar(fa);
    let pred_ty = || Expr::arrow(alpha(), Expr::prop());

    let px = Expr::app(Expr::fvar(fp), Expr::fvar(fx));
    let forall_x = Expr::pi(BinderInfo::Default, alpha(), px.abstract_fvar(fx));

    let v = forall_x.abstract_fvar(fp);
    let v = Expr::lam(BinderInfo::Default, pred_ty(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    let t = Expr::prop().abstract_fvar(fp);
    let t = Expr::pi(BinderInfo::Default, pred_ty(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `ATP.fEx : (α⇒bool)⇒bool := λ(α:Type)(P:α→Prop). ∃x. P x` via the
/// impredicative [`ex_encoding`] (exactly how an applied `HOL.Ex P` embeds).
fn build_atp_fex() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a501); // α : Type
    let fp = FVarId::new(0x1_a502); // P : α → Prop
    let alpha = || Expr::fvar(fa);
    let pred_ty = || Expr::arrow(alpha(), Expr::prop());

    let ex_body = ex_encoding(&alpha(), &Expr::fvar(fp));
    let v = ex_body.abstract_fvar(fp);
    let v = Expr::lam(BinderInfo::Default, pred_ty(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    let t = Expr::prop().abstract_fvar(fp);
    let t = Expr::pi(BinderInfo::Default, pred_ty(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `ATP.fequal : α⇒α⇒bool := λ(α:Type)(x y:α). @Eq α x y` — same shape as
/// [`build_induct_equal`].
fn build_atp_fequal() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a601); // α : Type
    let fx = FVarId::new(0x1_a602); // x : α
    let fy = FVarId::new(0x1_a603); // y : α
    let alpha = || Expr::fvar(fa);

    let body = eq_obj(alpha(), Expr::fvar(fx), Expr::fvar(fy));
    let v = body.abstract_fvar(fy);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fx);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    let t = Expr::prop().abstract_fvar(fy);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fx);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `ATP.fComp : (α⇒bool)⇒α⇒bool := λ(α:Type)(P:α→Prop)(x:α). Not (P x)`.
fn build_atp_fcomp() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a701); // α : Type
    let fp = FVarId::new(0x1_a702); // P : α → Prop
    let fx = FVarId::new(0x1_a703); // x : α
    let alpha = || Expr::fvar(fa);
    let pred_ty = || Expr::arrow(alpha(), Expr::prop());

    let px = Expr::app(Expr::fvar(fp), Expr::fvar(fx));
    let body = Expr::app(Expr::const_str("isabelle.def.HOL.Not"), px);
    let v = body.abstract_fvar(fx);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fp);
    let v = Expr::lam(BinderInfo::Default, pred_ty(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    let t = Expr::prop().abstract_fvar(fx);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fp);
    let t = Expr::pi(BinderInfo::Default, pred_ty(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `ATP.fChoice : (α⇒bool)⇒α := λ(α:Type)(eps:(α→Prop)→α). eps` — the
/// dictionary-style identity over the (opaque) `Hilbert_Choice.Eps` argument.
/// [`Ctx::embed_pointfree_const`] applies the def-const to the solved `α` and
/// the shared `const:Hilbert_Choice.Eps` param — the SAME param a bare `Eps`
/// occurrence embeds to — so `fChoice ≡ Eps` δβ-reduces to reflexivity while
/// the stored statement keeps two structurally distinct operands.
fn build_atp_fchoice() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a801); // α : Type
    let fe = FVarId::new(0x1_a802); // eps : (α → Prop) → α
    let alpha = || Expr::fvar(fa);
    let eps_ty = || Expr::arrow(Expr::arrow(alpha(), Expr::prop()), alpha());

    let v = Expr::fvar(fe).abstract_fvar(fe);
    let v = Expr::lam(BinderInfo::Default, eps_ty(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    let t = eps_ty().abstract_fvar(fe);
    let t = Expr::pi(BinderInfo::Default, eps_ty(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

// NOTE: `Code_Generator.holds` (`isabelle.def.Code_Generator.holds`) is
// registered by [`super::connective_definition_decls`] (it shares the
// `HOL.True` encoding `@Eq (Prop→Prop) (λx.x) (λx.x)`). It is deliberately NOT
// duplicated in [`pointfree_definition_decls`] below: the two round-6 branches
// each added a registration, and the second `add_decl` was a permanent
// `DuplicateName` (silently ignored by the production drivers' `let _ =`,
// panicking the `pointfree_env` test helper). `pointfree_const_def_name` still
// maps the constant, so every embed/def_raw path resolves the shared def-const
// unchanged.

/// The point-free HOL logical constants (`Uniq`/`Ex1`/`Let`/`induct_forall`/
/// `induct_equal`/`NO_MATCH`) as clean [`Declaration::Definition`]s. Registered
/// into the verifier's accumulating environment up front (like
/// [`super::connective_definition_decls`]) so each constant's occurrences share one
/// defeq-unfolding head and the point-free `…_def_raw` axiom verifies reflexively.
/// `True`/`conj` def-consts (their bodies' dependencies) are already registered by
/// [`super::connective_definition_decls`] before these, so the δ-unfolding chain
/// closes.
#[must_use]
pub(crate) fn pointfree_definition_decls() -> Vec<Declaration> {
    let entries: [(&str, (Expr, Expr)); 19] = [
        ("HOL.Uniq", build_uniq()),
        ("HOL.Ex1", build_ex1()),
        ("HOL.Let", build_let()),
        ("HOL.induct_forall", build_induct_forall()),
        ("HOL.induct_equal", build_induct_equal()),
        ("HOL.NO_MATCH", build_no_match()),
        ("HOL.induct_conj", build_induct_conj()),
        ("HOL.ASSUMPTION", build_assumption()),
        ("ATP.fFalse", build_atp_ffalse()),
        ("ATP.fTrue", build_atp_ftrue()),
        ("ATP.fNot", build_atp_fnot()),
        ("ATP.fconj", build_atp_fconj()),
        ("ATP.fdisj", build_atp_fdisj()),
        ("ATP.fimplies", build_atp_fimplies()),
        ("ATP.fAll", build_atp_fall()),
        ("ATP.fEx", build_atp_fex()),
        ("ATP.fequal", build_atp_fequal()),
        ("ATP.fComp", build_atp_fcomp()),
        ("ATP.fChoice", build_atp_fchoice()),
    ];
    entries
        .into_iter()
        .filter_map(|(name, (value, type_))| {
            pointfree_const_def_name(name).map(|def| Declaration::Definition {
                name: Name::from_string(def),
                level_params: Vec::new(),
                type_,
                value,
                is_reducible: true,
            })
        })
        .collect()
}
