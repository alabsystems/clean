// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful clean polymorphic `Definition`s for the **BNF** (Bounded Natural
//! Functor) datatype-package combinator constants whose `_def` / `_def_raw`
//! bodies are closed lambdas over the already-mapped `∀`/`→`/`@Eq`/`Ball`/`Bex`/
//! `∃`/`∧`/`Prod.mk` encodings:
//!
//! ```text
//! BNF_Composition.id_bnf : α → α                         := λx. x
//! BNF_Def.convol   : (α→β) → (α→γ) → α → β×γ             := λf g a. (f a, g a)
//! BNF_Def.rel_fun  : (α→γ→bool) → (β→δ→bool) → (α→β) → (γ→δ) → bool
//!                                                        := λA B f g. ∀x y. A x y → B (f x) (g y)
//! BNF_Def.rel_set  : (α→β→bool) → α set → β set → bool
//!                                := λR A B. (∀x∈A. ∃y∈B. R x y) ∧ (∀y∈B. ∃x∈A. R x y)
//! BNF_Def.eq_onp   : (α→bool) → α → α → bool            := λR x y. R x ∧ x = y
//! BNF_Def.vimage2p : (α→δ) → (β→ε) → (δ→ε→γ) → α → β → γ := λf g R x y. R (f x) (g y)
//! BNF_Def.Grp      : α set → (α→β) → α → β → bool        := λA f a b. b = f a ∧ a ∈ A
//! BNF_Def.Gr       : α set → (α→β) → (α×β) set          := λA f. {(x, f x) | x ∈ A}
//! BNF_Def.csquare  : α set → (β→γ) → (δ→γ) → (α→β) → (α→δ) → bool
//!                                := λA f1 f2 p1 p2. ∀a∈A. f1 (p1 a) = f2 (p2 a)
//! ```
//!
//! Each body is exactly what the constant's own HOL `…_def` RHS embeds to (the
//! clean `Pi`-∀, the `Set.Ball`/`Bex` [`ball_encoding`]/[`bex_encoding`], the
//! impredicative `∃` [`ex_encoding`], the `HOL.conj` def-const, the object-level
//! `@Eq`, `Prod.mk`), so each constant's `…_def`/`…_def_raw` definitional axiom
//! becomes genuinely reflexive — provable by `Eq.refl(lhs)`, which the kernel
//! accepts **iff** the def-const LHS δβ-reduces to the embedded RHS (see the
//! `is_bnf_def`-gated arm in `translate.rs`). Faithful (never a `B = B`
//! tautology): the stored proposition keeps the real `C args = RHS` shape, with
//! the def-const application and the embedded body as DISTINCT operands. No axiom
//! content anywhere — pure λ over the foundational encodings, so every consumer
//! stays `KernelVerified` to the three foundationals.
//!
//! The polymorphism is handled generically: each constant's HOL **schematic
//! type** ([`bnf_schematic`]) drives the object-type-variable order
//! ([`method_obj_tvars`], first-occurrence) that both the def-const's leading
//! `Type` binders and [`Ctx::embed_bnf_combinator`]'s use-site instantiation
//! ([`match_tvars`]) share.

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Expr};

use super::super::super::isabelle_pure::{IsaProvenTheorem, IsaTerm, IsaType};
use super::super::{
    match_tvars, method_obj_tvars, obj_level, pure_eq_parts, strip_leading_imps, term_app_spine,
    Ctx, TranslateError,
};
use super::sets::{ball_encoding, bex_encoding, ex_encoding};

// ---------------------------------------------------------------------------
// Names / schematic HOL types
// ---------------------------------------------------------------------------

/// The kernel declaration name of the clean polymorphic `Definition` registered
/// for a BNF combinator constant, or `None` for any other name.
pub(crate) fn bnf_def_const_name(name: &str) -> Option<&'static str> {
    match name {
        "BNF_Composition.id_bnf" => Some("isabelle.def.BNF_Composition.id_bnf"),
        "BNF_Def.convol" => Some("isabelle.def.BNF_Def.convol"),
        "BNF_Def.rel_fun" => Some("isabelle.def.BNF_Def.rel_fun"),
        "BNF_Def.rel_set" => Some("isabelle.def.BNF_Def.rel_set"),
        "BNF_Def.eq_onp" => Some("isabelle.def.BNF_Def.eq_onp"),
        "BNF_Def.vimage2p" => Some("isabelle.def.BNF_Def.vimage2p"),
        "BNF_Def.Grp" => Some("isabelle.def.BNF_Def.Grp"),
        "BNF_Def.Gr" => Some("isabelle.def.BNF_Def.Gr"),
        "BNF_Def.csquare" => Some("isabelle.def.BNF_Def.csquare"),
        // Round-13 wellorder/recursor lane: the trivial (identity-BNF) datatype
        // recursor/constructor-iso and the dead-identity predicate.
        "Basic_BNF_LFPs.xtor" => Some("isabelle.def.Basic_BNF_LFPs.xtor"),
        "Basic_BNF_LFPs.ctor_rec" => Some("isabelle.def.Basic_BNF_LFPs.ctor_rec"),
        "BNF_Composition.DEADID.pred_DEADID" => {
            Some("isabelle.def.BNF_Composition.DEADID.pred_DEADID")
        }
        // Round-13 wellorder set-builders: the initial-/strict-initial-segment
        // relation sections and the `isMinim` predicate are closed lambdas over the
        // `set = predicate` model (`Collect` = identity, `member x S` = `S x`), so
        // they register faithfully and unblock `wo_rel.adm_wo`.
        "Order_Relation.under" => Some("isabelle.def.Order_Relation.under"),
        "Order_Relation.underS" => Some("isabelle.def.Order_Relation.underS"),
        "BNF_Wellorder_Relation.wo_rel.isMinim" => {
            Some("isabelle.def.BNF_Wellorder_Relation.wo_rel.isMinim")
        }
        "BNF_Wellorder_Relation.wo_rel.adm_wo" => {
            Some("isabelle.def.BNF_Wellorder_Relation.wo_rel.adm_wo")
        }
        // Round-14 wellorder lane: `max2` is a CLOSED lambda over `HOL.If` +
        // `member` + `Pair` (`max2 r a b = if (a,b)∈r then b else a`), registrable
        // exactly like `under`/`underS` — the `HOL.If` def-const is already registered.
        "BNF_Wellorder_Relation.wo_rel.max2" => {
            Some("isabelle.def.BNF_Wellorder_Relation.wo_rel.max2")
        }
        _ => None,
    }
}

// --- HOL type builders (schematic, with `TVar`s) ---
fn tv(n: &str) -> IsaType {
    IsaType::TVar {
        n: n.to_string(),
        i: 0,
    }
}
fn fun(a: IsaType, b: IsaType) -> IsaType {
    IsaType::Type {
        n: "fun".to_string(),
        a: vec![a, b],
    }
}
fn boolt() -> IsaType {
    IsaType::Type {
        n: "HOL.bool".to_string(),
        a: Vec::new(),
    }
}
fn sett(a: IsaType) -> IsaType {
    IsaType::Type {
        n: "Set.set".to_string(),
        a: vec![a],
    }
}
fn prodt(a: IsaType, b: IsaType) -> IsaType {
    IsaType::Type {
        n: "Product_Type.prod".to_string(),
        a: vec![a, b],
    }
}

/// Whether `thm` is a BNF combinator **definitional axiom** — after stripping any
/// leading `⟹`/`⋀` premises, its conclusion is a `Pure.eq`/`HOL.eq` equation whose
/// LHS application spine is headed by a registered BNF combinator constant
/// ([`bnf_def_const_name`]). The LHS then embeds (via [`Ctx::embed_bnf_combinator`])
/// to the def-const, which δβ-reduces to exactly the embedded RHS, so the whole
/// equation is reflexive — the `translate.rs` arm proves it by `Eq.refl`. Scopes
/// that reflexive arm to precisely these defs, leaving every unrelated equation on
/// its recorded proof.
pub(crate) fn is_bnf_def(thm: &IsaProvenTheorem) -> bool {
    let concl = strip_leading_imps(&thm.prop);
    let Some((lhs, _rhs)) = pure_eq_parts(concl) else {
        return false;
    };
    let (head, _args) = term_app_spine(lhs);
    matches!(head, IsaTerm::Const { n, .. }
        if bnf_def_const_name(n).is_some() || super::bnf_opaque_def_const_name(n).is_some())
}

/// The exact HOL schematic type of a BNF combinator constant (matching the raw
/// export). Drives the object-type-variable order shared by the def-const's
/// leading `Type` binders and the use-site instantiation.
pub(crate) fn bnf_schematic(name: &str) -> Option<IsaType> {
    let (a, b, c, d, e) = (tv("'a"), tv("'b"), tv("'c"), tv("'d"), tv("'e"));
    Some(match name {
        // α → α
        "BNF_Composition.id_bnf" => fun(a.clone(), a),
        // (α→β) → (α→γ) → α → β×γ
        "BNF_Def.convol" => fun(
            fun(a.clone(), b.clone()),
            fun(fun(a.clone(), c.clone()), fun(a, prodt(b, c))),
        ),
        // (α→γ→bool) → (β→δ→bool) → (α→β) → (γ→δ) → bool
        "BNF_Def.rel_fun" => fun(
            fun(a.clone(), fun(c.clone(), boolt())),
            fun(
                fun(b.clone(), fun(d.clone(), boolt())),
                fun(fun(a, b), fun(fun(c, d), boolt())),
            ),
        ),
        // (α→β→bool) → α set → β set → bool
        "BNF_Def.rel_set" => fun(
            fun(a.clone(), fun(b.clone(), boolt())),
            fun(sett(a), fun(sett(b), boolt())),
        ),
        // (α→bool) → α → α → bool
        "BNF_Def.eq_onp" => fun(fun(a.clone(), boolt()), fun(a.clone(), fun(a, boolt()))),
        // (α→δ) → (β→ε) → (δ→ε→γ) → α → β → γ
        "BNF_Def.vimage2p" => fun(
            fun(a.clone(), d.clone()),
            fun(
                fun(b.clone(), e.clone()),
                fun(fun(d, fun(e, c.clone())), fun(a, fun(b, c))),
            ),
        ),
        // α set → (α→β) → α → β → bool
        "BNF_Def.Grp" => fun(
            sett(a.clone()),
            fun(fun(a.clone(), b.clone()), fun(a, fun(b, boolt()))),
        ),
        // α set → (α→β) → (α×β) set
        "BNF_Def.Gr" => fun(
            sett(a.clone()),
            fun(fun(a.clone(), b.clone()), sett(prodt(a, b))),
        ),
        // α set → (β→γ) → (δ→γ) → (α→β) → (α→δ) → bool
        "BNF_Def.csquare" => fun(
            sett(a.clone()),
            fun(
                fun(b.clone(), c.clone()),
                fun(
                    fun(d.clone(), c),
                    fun(fun(a.clone(), b), fun(fun(a, d), boolt())),
                ),
            ),
        ),
        // α → α  (identity BNF recursor / constructor-iso)
        "Basic_BNF_LFPs.xtor" | "Basic_BNF_LFPs.ctor_rec" => fun(a.clone(), a),
        // α → bool  (dead-identity predicate)
        "BNF_Composition.DEADID.pred_DEADID" => fun(a, boolt()),
        // (α×α) set → α → α set  (under/underS: relation sections)
        "Order_Relation.under" | "Order_Relation.underS" => {
            fun(sett(prodt(a.clone(), a.clone())), fun(a.clone(), sett(a)))
        }
        // (α×α) set → α set → α → bool  (isMinim)
        "BNF_Wellorder_Relation.wo_rel.isMinim" => fun(
            sett(prodt(a.clone(), a.clone())),
            fun(sett(a.clone()), fun(a, boolt())),
        ),
        // (α×α) set → ((α→β)→α→β) → bool  (adm_wo)
        "BNF_Wellorder_Relation.wo_rel.adm_wo" => fun(
            sett(prodt(a.clone(), a.clone())),
            fun(fun(fun(a.clone(), b.clone()), fun(a, b)), boolt()),
        ),
        // (α×α) set → α → α → α  (max2)
        "BNF_Wellorder_Relation.wo_rel.max2" => fun(
            sett(prodt(a.clone(), a.clone())),
            fun(a.clone(), fun(a.clone(), a)),
        ),
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// Definition-building framework
// ---------------------------------------------------------------------------

/// Per-constant builder scratch: the object-type-variable fvars (in
/// [`method_obj_tvars`] first-occurrence order) plus a fresh-fvar allocator for
/// the body's local (`∀`/`∃`/`Ball`) binders. All fvars are abstracted away in
/// [`finish`]; only per-build distinctness matters.
struct BnfBuild {
    tv: BTreeMap<String, Expr>,
    tv_fvars: Vec<FVarId>,
    next_local: u64,
}

impl BnfBuild {
    fn new(schematic: &IsaType, base: u64) -> Option<Self> {
        let tvs = method_obj_tvars(schematic)?;
        let mut tv = BTreeMap::new();
        let mut tv_fvars = Vec::new();
        for (k, (n, _i)) in tvs.iter().enumerate() {
            let f = FVarId::new(base + k as u64);
            tv.insert(n.clone(), Expr::fvar(f));
            tv_fvars.push(f);
        }
        Some(Self {
            tv,
            tv_fvars,
            next_local: base + 0x1000,
        })
    }

    /// The fvar `Expr` for a tvar name (`"'a"`, …).
    fn t(&self, n: &str) -> Expr {
        self.tv
            .get(n)
            .cloned()
            .expect("bnf builder: unknown tvar name")
    }

    /// A fresh, distinct fvar for a value/local binder.
    fn fresh(&mut self) -> FVarId {
        let f = FVarId::new(self.next_local);
        self.next_local += 1;
        f
    }
}

/// Assemble the `(value, type)` of a def-const from the tvar fvars, the value
/// argument `(fvar, clean-type)` list (outer→inner), the innermost `body`, and
/// the `result` clean type. Wraps `λ tvars. λ args. body` and
/// `Π tvars. Π args. result`, abstracting the fvars innermost-first. The leading
/// `Type` binders are in `tv_fvars` (= [`method_obj_tvars`]) order, which
/// [`Ctx::embed_bnf_combinator`] mirrors when instantiating.
fn finish(tv_fvars: &[FVarId], args: &[(FVarId, Expr)], body: Expr, result: Expr) -> (Expr, Expr) {
    // VALUE: λ args. body, then λ tvars — innermost-first.
    let mut value = body;
    for (f, ty) in args.iter().rev() {
        value = value.abstract_fvar(*f);
        value = Expr::lam(BinderInfo::Default, ty.clone(), value);
    }
    for f in tv_fvars.iter().rev() {
        value = value.abstract_fvar(*f);
        value = Expr::lam(BinderInfo::Default, Expr::type_(), value);
    }
    // TYPE: Π args. result, then Π tvars.
    let mut type_ = result;
    for (f, ty) in args.iter().rev() {
        type_ = type_.abstract_fvar(*f);
        type_ = Expr::pi(BinderInfo::Default, ty.clone(), type_);
    }
    for f in tv_fvars.iter().rev() {
        type_ = type_.abstract_fvar(*f);
        type_ = Expr::pi(BinderInfo::Default, Expr::type_(), type_);
    }
    (value, type_)
}

/// `@Eq.{obj} α a b` — the object-level HOL equality, exactly as `embed_term`
/// emits `HOL.eq`.
fn eq_obj(alpha: &Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [alpha.clone(), a, b],
    )
}

/// `@Prod.mk.{0,0} α β a b` — clean's pair constructor, exactly as `embed_pair`
/// emits `Product_Type.Pair`.
fn prod_mk(alpha: &Expr, beta: &Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Prod.mk", vec![Level::zero(), Level::zero()]),
        [alpha.clone(), beta.clone(), a, b],
    )
}

/// `@Prod.{0,0} α β` — clean's product type, exactly as `embed_type` emits
/// `Product_Type.prod`.
fn prod_ty(alpha: &Expr, beta: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Prod", vec![Level::zero(), Level::zero()]),
        [alpha.clone(), beta.clone()],
    )
}

/// The `HOL.conj` def-const `isabelle.def.HOL.conj : Prop→Prop→Prop`, applied.
fn conj(a: Expr, b: Expr) -> Expr {
    Expr::apps(super::conj_def_const(), [a, b])
}

// --- per-constant bodies ---

/// `id_bnf : α → α := λx. x`.
fn build_id_bnf(b: &mut BnfBuild) -> (Expr, Expr) {
    let alpha = b.t("'a");
    let x = b.fresh();
    finish(&b.tv_fvars, &[(x, alpha.clone())], Expr::fvar(x), alpha)
}

/// `convol : (α→β)→(α→γ)→α→β×γ := λf g a. (f a, g a)`.
fn build_convol(b: &mut BnfBuild) -> (Expr, Expr) {
    let (ta, tb, tc) = (b.t("'a"), b.t("'b"), b.t("'c"));
    let (f, g, a) = (b.fresh(), b.fresh(), b.fresh());
    let fa = Expr::app(Expr::fvar(f), Expr::fvar(a));
    let ga = Expr::app(Expr::fvar(g), Expr::fvar(a));
    let body = prod_mk(&tb, &tc, fa, ga);
    finish(
        &b.tv_fvars,
        &[
            (f, Expr::arrow(ta.clone(), tb.clone())),
            (g, Expr::arrow(ta.clone(), tc.clone())),
            (a, ta),
        ],
        body,
        prod_ty(&tb, &tc),
    )
}

/// `rel_fun : (α→γ→bool)→(β→δ→bool)→(α→β)→(γ→δ)→bool
///   := λA B f g. ∀x y. A x y → B (f x) (g y)`.
fn build_rel_fun(b: &mut BnfBuild) -> (Expr, Expr) {
    let (ta, tb, tc, td) = (b.t("'a"), b.t("'b"), b.t("'c"), b.t("'d"));
    let (ra, rb, f, g) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    let (x, y) = (b.fresh(), b.fresh());
    // A x y → B (f x) (g y)
    let axy = Expr::apps(Expr::fvar(ra), [Expr::fvar(x), Expr::fvar(y)]);
    let bfg = Expr::apps(
        Expr::fvar(rb),
        [
            Expr::app(Expr::fvar(f), Expr::fvar(x)),
            Expr::app(Expr::fvar(g), Expr::fvar(y)),
        ],
    );
    let imp = Expr::arrow(axy, bfg);
    // ∀y:γ. imp ; ∀x:α. …
    let all_y = Expr::pi(BinderInfo::Default, tc.clone(), imp.abstract_fvar(y));
    let all_x = Expr::pi(BinderInfo::Default, ta.clone(), all_y.abstract_fvar(x));
    let rel_a = Expr::arrow(ta.clone(), Expr::arrow(tc.clone(), Expr::prop()));
    let rel_b = Expr::arrow(tb.clone(), Expr::arrow(td.clone(), Expr::prop()));
    finish(
        &b.tv_fvars,
        &[
            (ra, rel_a),
            (rb, rel_b),
            (f, Expr::arrow(ta, tb)),
            (g, Expr::arrow(tc, td)),
        ],
        all_x,
        Expr::prop(),
    )
}

/// `rel_set : (α→β→bool)→α set→β set→bool
///   := λR A B. (∀x∈A. ∃y∈B. R x y) ∧ (∀y∈B. ∃x∈A. R x y)`.
fn build_rel_set(b: &mut BnfBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let (r, sa, sb) = (b.fresh(), b.fresh(), b.fresh());
    // conjunct 1: Ball A (λx. Bex B (λy. R x y))
    let (x1, y1) = (b.fresh(), b.fresh());
    let rxy1 = Expr::apps(Expr::fvar(r), [Expr::fvar(x1), Expr::fvar(y1)]);
    let inner1 = Expr::lam(BinderInfo::Default, tb.clone(), rxy1.abstract_fvar(y1));
    let bex1 = Expr::apps(bex_encoding(&tb), [Expr::fvar(sb), inner1]);
    let pred1 = Expr::lam(BinderInfo::Default, ta.clone(), bex1.abstract_fvar(x1));
    let conj1 = Expr::apps(ball_encoding(&ta), [Expr::fvar(sa), pred1]);
    // conjunct 2: Ball B (λy. Bex A (λx. R x y))
    let (x2, y2) = (b.fresh(), b.fresh());
    let rxy2 = Expr::apps(Expr::fvar(r), [Expr::fvar(x2), Expr::fvar(y2)]);
    let inner2 = Expr::lam(BinderInfo::Default, ta.clone(), rxy2.abstract_fvar(x2));
    let bex2 = Expr::apps(bex_encoding(&ta), [Expr::fvar(sa), inner2]);
    let pred2 = Expr::lam(BinderInfo::Default, tb.clone(), bex2.abstract_fvar(y2));
    let conj2 = Expr::apps(ball_encoding(&tb), [Expr::fvar(sb), pred2]);
    let body = conj(conj1, conj2);
    let rel = Expr::arrow(ta.clone(), Expr::arrow(tb.clone(), Expr::prop()));
    finish(
        &b.tv_fvars,
        &[
            (r, rel),
            (sa, Expr::arrow(ta, Expr::prop())),
            (sb, Expr::arrow(tb, Expr::prop())),
        ],
        body,
        Expr::prop(),
    )
}

/// `eq_onp : (α→bool)→α→α→bool := λR x y. R x ∧ x = y`.
fn build_eq_onp(b: &mut BnfBuild) -> (Expr, Expr) {
    let ta = b.t("'a");
    let (r, x, y) = (b.fresh(), b.fresh(), b.fresh());
    let rx = Expr::app(Expr::fvar(r), Expr::fvar(x));
    let eqxy = eq_obj(&ta, Expr::fvar(x), Expr::fvar(y));
    let body = conj(rx, eqxy);
    finish(
        &b.tv_fvars,
        &[
            (r, Expr::arrow(ta.clone(), Expr::prop())),
            (x, ta.clone()),
            (y, ta),
        ],
        body,
        Expr::prop(),
    )
}

/// `vimage2p : (α→δ)→(β→ε)→(δ→ε→γ)→α→β→γ := λf g R x y. R (f x) (g y)`.
fn build_vimage2p(b: &mut BnfBuild) -> (Expr, Expr) {
    let (ta, tb, tc, td, te) = (b.t("'a"), b.t("'b"), b.t("'c"), b.t("'d"), b.t("'e"));
    let (f, g, r, x, y) = (b.fresh(), b.fresh(), b.fresh(), b.fresh(), b.fresh());
    let body = Expr::apps(
        Expr::fvar(r),
        [
            Expr::app(Expr::fvar(f), Expr::fvar(x)),
            Expr::app(Expr::fvar(g), Expr::fvar(y)),
        ],
    );
    let r_ty = Expr::arrow(td.clone(), Expr::arrow(te.clone(), tc.clone()));
    finish(
        &b.tv_fvars,
        &[
            (f, Expr::arrow(ta.clone(), td)),
            (g, Expr::arrow(tb.clone(), te)),
            (r, r_ty),
            (x, ta),
            (y, tb),
        ],
        body,
        tc,
    )
}

/// `Grp : α set→(α→β)→α→β→bool := λA f a b. b = f a ∧ a ∈ A`.
fn build_grp(b: &mut BnfBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let (sa, f, a, bb) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    let fa = Expr::app(Expr::fvar(f), Expr::fvar(a));
    let eq_bfa = eq_obj(&tb, Expr::fvar(bb), fa);
    let mem = Expr::app(Expr::fvar(sa), Expr::fvar(a)); // a ∈ A  ==  A a
    let body = conj(eq_bfa, mem);
    finish(
        &b.tv_fvars,
        &[
            (sa, Expr::arrow(ta.clone(), Expr::prop())),
            (f, Expr::arrow(ta.clone(), tb.clone())),
            (a, ta),
            (bb, tb),
        ],
        body,
        Expr::prop(),
    )
}

/// `Gr : α set→(α→β)→(α×β) set := λA f. {(x, f x) | x ∈ A}`, i.e.
/// `λA f. λp. ∃x. p = (x, f x) ∧ x ∈ A` (under the `set = predicate` model).
fn build_gr(b: &mut BnfBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let (sa, f, p, x) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    let prod_ab = prod_ty(&ta, &tb);
    // predicate λx:α. p = (x, f x) ∧ x ∈ A
    let pair = prod_mk(
        &ta,
        &tb,
        Expr::fvar(x),
        Expr::app(Expr::fvar(f), Expr::fvar(x)),
    );
    let eqp = eq_obj(&prod_ab, Expr::fvar(p), pair);
    let mem = Expr::app(Expr::fvar(sa), Expr::fvar(x));
    let pred_body = conj(eqp, mem);
    let pred = Expr::lam(BinderInfo::Default, ta.clone(), pred_body.abstract_fvar(x));
    let ex = ex_encoding(&ta, &pred);
    // λp:α×β. ∃x. …
    let body = Expr::lam(BinderInfo::Default, prod_ab.clone(), ex.abstract_fvar(p));
    finish(
        &b.tv_fvars,
        &[
            (sa, Expr::arrow(ta.clone(), Expr::prop())),
            (f, Expr::arrow(ta, tb)),
        ],
        body,
        Expr::arrow(prod_ab, Expr::prop()),
    )
}

/// `csquare : α set→(β→γ)→(δ→γ)→(α→β)→(α→δ)→bool
///   := λA f1 f2 p1 p2. ∀a∈A. f1 (p1 a) = f2 (p2 a)`.
fn build_csquare(b: &mut BnfBuild) -> (Expr, Expr) {
    let (ta, tb, tc, td) = (b.t("'a"), b.t("'b"), b.t("'c"), b.t("'d"));
    let (sa, f1, f2, p1, p2, a) = (
        b.fresh(),
        b.fresh(),
        b.fresh(),
        b.fresh(),
        b.fresh(),
        b.fresh(),
    );
    let lhs = Expr::app(Expr::fvar(f1), Expr::app(Expr::fvar(p1), Expr::fvar(a)));
    let rhs = Expr::app(Expr::fvar(f2), Expr::app(Expr::fvar(p2), Expr::fvar(a)));
    let eqf = eq_obj(&tc, lhs, rhs);
    let pred = Expr::lam(BinderInfo::Default, ta.clone(), eqf.abstract_fvar(a));
    let body = Expr::apps(ball_encoding(&ta), [Expr::fvar(sa), pred]);
    finish(
        &b.tv_fvars,
        &[
            (sa, Expr::arrow(ta.clone(), Expr::prop())),
            (f1, Expr::arrow(tb.clone(), tc.clone())),
            (f2, Expr::arrow(td.clone(), tc)),
            (p1, Expr::arrow(ta.clone(), tb)),
            (p2, Expr::arrow(ta, td)),
        ],
        body,
        Expr::prop(),
    )
}

/// `xtor : α → α := λx. x` (identity BNF constructor-iso). Also `ctor_rec`, the
/// identity-BNF datatype recursor, which the package defines as the identity too.
fn build_identity(b: &mut BnfBuild) -> (Expr, Expr) {
    let alpha = b.t("'a");
    let x = b.fresh();
    finish(&b.tv_fvars, &[(x, alpha.clone())], Expr::fvar(x), alpha)
}

/// `pred_DEADID : α → bool := λx. True` (the dead-identity BNF predicate — the
/// always-true predicate). The `True` is the SAME `isabelle.def.HOL.True`
/// def-const `embed_term` emits for a bare `HOL.True`, so the body δ-matches the
/// embedded RHS; `bool` embeds to `Prop`, so the result type is `Prop`.
fn build_pred_deadid(b: &mut BnfBuild) -> (Expr, Expr) {
    let alpha = b.t("'a");
    let x = b.fresh();
    let tru = Expr::const_str("isabelle.def.HOL.True");
    finish(&b.tv_fvars, &[(x, alpha)], tru, Expr::prop())
}

/// `HOL.Not A` — the SAME `isabelle.def.HOL.Not` def-const applied form
/// `embed_term` emits for an applied `HOL.Not`.
fn not_def(a: Expr) -> Expr {
    Expr::app(Expr::const_str("isabelle.def.HOL.Not"), a)
}

/// `Order_Relation.under : (α×α) set → α → α set
///   := λr a. {b. (b,a) ∈ r}`. Under `set = predicate` (`Collect` = identity,
/// `member x S` = `S x`), the section `under r a` is `λb. r (b, a)`.
fn build_under(b: &mut BnfBuild) -> (Expr, Expr) {
    let alpha = b.t("'a");
    let (r, a, bb) = (b.fresh(), b.fresh(), b.fresh());
    let pair = prod_mk(&alpha, &alpha, Expr::fvar(bb), Expr::fvar(a));
    let mem = Expr::app(Expr::fvar(r), pair); // r (b, a)
    let body = Expr::lam(BinderInfo::Default, alpha.clone(), mem.abstract_fvar(bb));
    let r_ty = Expr::arrow(prod_ty(&alpha, &alpha), Expr::prop());
    finish(
        &b.tv_fvars,
        &[(r, r_ty), (a, alpha.clone())],
        body,
        Expr::arrow(alpha, Expr::prop()),
    )
}

/// `Order_Relation.underS : (α×α) set → α → α set
///   := λr a. {b. b ≠ a ∧ (b,a) ∈ r}` i.e. `λr a b. ¬(b = a) ∧ r (b, a)`.
fn build_unders(b: &mut BnfBuild) -> (Expr, Expr) {
    let alpha = b.t("'a");
    let (r, a, bb) = (b.fresh(), b.fresh(), b.fresh());
    let neq = not_def(eq_obj(&alpha, Expr::fvar(bb), Expr::fvar(a)));
    let pair = prod_mk(&alpha, &alpha, Expr::fvar(bb), Expr::fvar(a));
    let mem = Expr::app(Expr::fvar(r), pair);
    let inner = conj(neq, mem);
    let body = Expr::lam(BinderInfo::Default, alpha.clone(), inner.abstract_fvar(bb));
    let r_ty = Expr::arrow(prod_ty(&alpha, &alpha), Expr::prop());
    finish(
        &b.tv_fvars,
        &[(r, r_ty), (a, alpha.clone())],
        body,
        Expr::arrow(alpha, Expr::prop()),
    )
}

/// `wo_rel.isMinim : (α×α) set → α set → α → bool
///   := λr A b. b ∈ A ∧ (∀a∈A. (b,a) ∈ r)` i.e. `λr A b. A b ∧ Ball A (λa. r (b,a))`.
/// (The exported `_def` carries a leading `wo_rel r ⟹`, discharged vacuously by the
/// reflexive arm — the equation itself is unconditional.)
fn build_isminim(b: &mut BnfBuild) -> (Expr, Expr) {
    let alpha = b.t("'a");
    let (r, aset, bb, a) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    let ab = Expr::app(Expr::fvar(aset), Expr::fvar(bb)); // b ∈ A
    let pair = prod_mk(&alpha, &alpha, Expr::fvar(bb), Expr::fvar(a));
    let mem = Expr::app(Expr::fvar(r), pair); // (b,a) ∈ r
    let pred = Expr::lam(BinderInfo::Default, alpha.clone(), mem.abstract_fvar(a));
    let ball = Expr::apps(ball_encoding(&alpha), [Expr::fvar(aset), pred]);
    let body = conj(ab, ball);
    let r_ty = Expr::arrow(prod_ty(&alpha, &alpha), Expr::prop());
    let aset_ty = Expr::arrow(alpha.clone(), Expr::prop());
    finish(
        &b.tv_fvars,
        &[(r, r_ty), (aset, aset_ty), (bb, alpha)],
        body,
        Expr::prop(),
    )
}

/// `wo_rel.adm_wo : (α×α) set → ((α→β)→α→β) → bool
///   := λr H. ∀f g x. (∀y∈underS r x. f y = g y) → H f x = H g x`. Its body's only
/// non-trivial constituent is `underS`, which is registered above, so the closed
/// lambda δ-matches the embedded RHS. (Leading `wo_rel r ⟹` discharged vacuously.)
fn build_adm_wo(b: &mut BnfBuild) -> (Expr, Expr) {
    let (alpha, beta) = (b.t("'a"), b.t("'b"));
    let (r, h, f, g, x, y) = (
        b.fresh(),
        b.fresh(),
        b.fresh(),
        b.fresh(),
        b.fresh(),
        b.fresh(),
    );
    let fun_ab = Expr::arrow(alpha.clone(), beta.clone());
    // premise: Ball (underS r x) (λy. f y = g y)
    let unders_rx = Expr::apps(
        Expr::const_str("isabelle.def.Order_Relation.underS"),
        [alpha.clone(), Expr::fvar(r), Expr::fvar(x)],
    );
    let eq_fg = eq_obj(
        &beta,
        Expr::app(Expr::fvar(f), Expr::fvar(y)),
        Expr::app(Expr::fvar(g), Expr::fvar(y)),
    );
    let pred_y = Expr::lam(BinderInfo::Default, alpha.clone(), eq_fg.abstract_fvar(y));
    let premise = Expr::apps(ball_encoding(&alpha), [unders_rx, pred_y]);
    // conclusion: H f x = H g x
    let eq_h = eq_obj(
        &beta,
        Expr::apps(Expr::fvar(h), [Expr::fvar(f), Expr::fvar(x)]),
        Expr::apps(Expr::fvar(h), [Expr::fvar(g), Expr::fvar(x)]),
    );
    let imp = Expr::arrow(premise, eq_h);
    // ∀f g x. …  (x innermost)
    let all_x = Expr::pi(BinderInfo::Default, alpha.clone(), imp.abstract_fvar(x));
    let all_g = Expr::pi(BinderInfo::Default, fun_ab.clone(), all_x.abstract_fvar(g));
    let all_f = Expr::pi(BinderInfo::Default, fun_ab.clone(), all_g.abstract_fvar(f));
    let r_ty = Expr::arrow(prod_ty(&alpha, &alpha), Expr::prop());
    let h_ty = Expr::arrow(fun_ab.clone(), fun_ab);
    finish(&b.tv_fvars, &[(r, r_ty), (h, h_ty)], all_f, Expr::prop())
}

/// `wo_rel.max2 : (α×α) set → α → α → α
///   := λr a b. if (a,b) ∈ r then b else a`, i.e. `λr a b. If α (r (a,b)) b a`.
/// Under `set = predicate` (`member x S` = `S x`), the condition `(a,b) ∈ r` is
/// `r (a,b)` and the `if` is the SAME `isabelle.def.HOL.If` def-const the RHS
/// embeds to, so the closed lambda δβ-matches the embedded RHS. (The exported
/// `_def` carries a leading `wo_rel r ⟹`, discharged vacuously by the reflexive
/// arm — the equation itself is unconditional.)
fn build_max2(b: &mut BnfBuild) -> (Expr, Expr) {
    let alpha = b.t("'a");
    let (r, a, bb) = (b.fresh(), b.fresh(), b.fresh());
    let pair = prod_mk(&alpha, &alpha, Expr::fvar(a), Expr::fvar(bb)); // (a, b)
    let cond = Expr::app(Expr::fvar(r), pair); // (a,b) ∈ r  ==  r (a,b)
    let if_app = Expr::apps(
        Expr::const_str_levels(super::hol_if_def_name(), vec![obj_level()]),
        [alpha.clone(), cond, Expr::fvar(bb), Expr::fvar(a)],
    );
    let r_ty = Expr::arrow(prod_ty(&alpha, &alpha), Expr::prop());
    finish(
        &b.tv_fvars,
        &[(r, r_ty), (a, alpha.clone()), (bb, alpha.clone())],
        if_app,
        alpha,
    )
}

/// Every BNF combinator constant, with its dedicated fvar-id base.
type BnfBuilder = fn(&mut BnfBuild) -> (Expr, Expr);
const BNF_CONSTANTS: [(&str, u64, BnfBuilder); 17] = [
    ("BNF_Composition.id_bnf", 0x1B00_0000, build_id_bnf),
    ("BNF_Def.convol", 0x1B01_0000, build_convol),
    ("BNF_Def.rel_fun", 0x1B02_0000, build_rel_fun),
    ("BNF_Def.rel_set", 0x1B03_0000, build_rel_set),
    ("BNF_Def.eq_onp", 0x1B04_0000, build_eq_onp),
    ("BNF_Def.vimage2p", 0x1B05_0000, build_vimage2p),
    ("BNF_Def.Grp", 0x1B06_0000, build_grp),
    ("BNF_Def.Gr", 0x1B07_0000, build_gr),
    ("BNF_Def.csquare", 0x1B08_0000, build_csquare),
    ("Basic_BNF_LFPs.xtor", 0x1B09_0000, build_identity),
    ("Basic_BNF_LFPs.ctor_rec", 0x1B0A_0000, build_identity),
    (
        "BNF_Composition.DEADID.pred_DEADID",
        0x1B0B_0000,
        build_pred_deadid,
    ),
    ("Order_Relation.under", 0x1B0C_0000, build_under),
    ("Order_Relation.underS", 0x1B0D_0000, build_unders),
    (
        "BNF_Wellorder_Relation.wo_rel.isMinim",
        0x1B0E_0000,
        build_isminim,
    ),
    (
        "BNF_Wellorder_Relation.wo_rel.adm_wo",
        0x1B0F_0000,
        build_adm_wo,
    ),
    (
        "BNF_Wellorder_Relation.wo_rel.max2",
        0x1B10_0000,
        build_max2,
    ),
];

/// The BNF combinator constants as clean [`Declaration::Definition`]s. Registered
/// into the verifier's accumulating environment up front (like
/// [`super::fun_combinator_definition_decls`]) so each constant's occurrences
/// share one defeq-unfolding head and its `…_def`/`…_def_raw` axiom verifies
/// reflexively. Registered AFTER the connective def-consts (`HOL.conj`, the
/// impredicative `∃`/`Ball`/`Bex` dependencies) so the δ-unfolding chain closes.
/// Non-fatal on registration failure: the constant's nodes simply stay unmapped.
#[must_use]
pub(crate) fn bnf_combinator_definition_decls() -> Vec<Declaration> {
    BNF_CONSTANTS
        .iter()
        .filter_map(|(name, base, build)| {
            let schematic = bnf_schematic(name)?;
            let mut b = BnfBuild::new(&schematic, *base)?;
            let (value, type_) = build(&mut b);
            bnf_def_const_name(name).map(|def| Declaration::Definition {
                name: Name::from_string(def),
                level_params: Vec::new(),
                type_,
                value,
                is_reducible: true,
            })
        })
        .collect()
}

impl Ctx {
    /// Embed an occurrence of a BNF combinator constant to its registered
    /// polymorphic def-const ([`bnf_def_const_name`]) applied to the use-site's
    /// solved object types, so the constant's `…_def`/`…_def_raw` axiom verifies
    /// reflexively (`C args` δβ-reduces to the embedded body) and every occurrence
    /// shares one defeq-unfolding head. `use_ty` is the constant's instantiated
    /// HOL type; the object type parameters are solved by matching the
    /// [`bnf_schematic`] against it ([`match_tvars`], in first-occurrence order).
    /// Returns `None` when the type does not match (the caller then falls back to
    /// the opaque `const:` param; the kernel re-checks either way).
    pub(crate) fn embed_bnf_combinator(
        &mut self,
        n: &str,
        use_ty: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some(def) = bnf_def_const_name(n) else {
            return Ok(None);
        };
        let Some(schematic) = bnf_schematic(n) else {
            return Ok(None);
        };
        let Some(tvs) = method_obj_tvars(&schematic) else {
            return Ok(None);
        };
        let Some(subs) = match_tvars(&schematic, use_ty, &tvs) else {
            return Ok(None);
        };
        let mut e = Expr::const_str(def);
        for (_tv, ty) in &subs {
            let te = self.embed_type(ty)?;
            e = Expr::app(e, te);
        }
        Ok(Some(e))
    }
}
