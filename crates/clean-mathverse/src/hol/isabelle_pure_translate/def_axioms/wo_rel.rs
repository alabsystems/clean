// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful clean polymorphic `Definition`s for the **`wo_rel`** (well-order
//! locale) constants whose `_def` / `_def_raw` bodies thread HOL's definite
//! description `HOL.The` (`THE x. …`) over an already-registered predicate — the
//! extremum-style pattern (`def_axioms::hilbert`), specialised to the wellorder
//! minimum and its `Above`/`AboveS` successors:
//!
//! ```text
//! wo_rel.minim : (α×α)set → αset → α    := λr A. THE b. isMinim r A b
//! wo_rel.supr  : (α×α)set → αset → α    := λr A. minim r (Above r A)
//! wo_rel.suc   : (α×α)set → αset → α    := λr A. minim r (AboveS r A)
//! ```
//!
//! `isMinim` (`connectives::bnf_defs`), `Above`/`AboveS` (`connectives::bnf_cardinal`,
//! opaque `Relation.Field` slot) and `HOL.The` (`def_axioms::hilbert`) are all
//! registered def-consts, so each of these bodies is a closed lambda over them once
//! the `Nonempty α` witness `HOL.The` needs is threaded as a leading value binder.
//! At each use-site [`Ctx::embed_wo_the_const`] supplies that witness as the SAME
//! shared `Nonempty α` parameter ([`nonempty_param_key`]) the RHS's `HOL.The`
//! occurrence threads (via [`Ctx::embed_hol_the`]), and — for `supr`/`suc` — the
//! opaque `Relation.Field` argument `Above`/`AboveS` abstract, re-embedded through
//! the ordinary `Const` dispatch. So each `_def` LHS `C r A` δβ-reduces to EXACTLY
//! what its RHS embeds to, and the whole (premise-guarded) definitional equation is
//! reflexive — proved by `Eq.refl` through the [`is_wo_the_def`]-gated arm in
//! `translate.rs`.
//!
//! ## Faithfulness
//!
//! Every stored type is the REAL definitional equation (the exported `wo_rel r ⟹
//! C r A ≡ …` with its real premise and DISTINCT operands — never a `body = body`
//! tautology, never fabricated). The kernel re-checks `Eq.refl α lhs : @Eq α lhs
//! rhs`, accepting **iff** the def-const δβ-reduces to the RHS, so a wrong body or
//! witness/`Field` supply **rejects, never false-verifies**. No axioms beyond the
//! foundational closure of `HOL.The` (`Classical.choice`/`propext`/`Quot.sound`), so
//! every consumer stays `KernelVerified` to the three foundationals.

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Expr};

// Parent (`isabelle_pure_translate`) glob — mirrors `hilbert.rs`; brings the
// `IsaProvenTheorem`/`IsaTerm`/`IsaType` re-exports, the `obj_level`/`pure_eq_parts`/
// `strip_leading_imps`/`term_app_spine` helpers, `Ctx`/`TranslateError`, and the
// `hilbert` `Nonempty`-witness helpers (`nonempty`/`nonempty_param_key`/
// `the_applied_ne`).
use super::super::*;

/// The kernel declaration name of the clean polymorphic `Definition` registered
/// for a `wo_rel` `The`-threaded constant (`minim`/`supr`/`suc`), or `None`.
pub(crate) fn wo_the_def_const_name(name: &str) -> Option<&'static str> {
    match name {
        "BNF_Wellorder_Relation.wo_rel.minim" => {
            Some("isabelle.def.BNF_Wellorder_Relation.wo_rel.minim")
        }
        "BNF_Wellorder_Relation.wo_rel.supr" => {
            Some("isabelle.def.BNF_Wellorder_Relation.wo_rel.supr")
        }
        "BNF_Wellorder_Relation.wo_rel.suc" => {
            Some("isabelle.def.BNF_Wellorder_Relation.wo_rel.suc")
        }
        _ => None,
    }
}

// --- clean type / term helpers (`bool = Prop`, `α set = α → Prop`, `α × β = Prod α β`) ---

fn cset(a: &Expr) -> Expr {
    Expr::arrow(a.clone(), Expr::prop())
}
fn cprod(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Prod", vec![Level::zero(), Level::zero()]),
        [a.clone(), b.clone()],
    )
}
/// `(α×α) set` clean type `(α×α) → Prop`.
fn crel(a: &Expr) -> Expr {
    cset(&cprod(a, a))
}
/// The `Relation.Field` slot's clean type `((α×α)→Prop) → (α→Prop)`.
fn field_slot_ty(a: &Expr) -> Expr {
    Expr::arrow(crel(a), cset(a))
}

const ISMINIM_DEF: &str = "isabelle.def.BNF_Wellorder_Relation.wo_rel.isMinim";
const MINIM_DEF: &str = "isabelle.def.BNF_Wellorder_Relation.wo_rel.minim";
const ABOVE_DEF: &str = "isabelle.def.Order_Relation.Above";
const ABOVES_DEF: &str = "isabelle.def.Order_Relation.AboveS";

/// `wo_rel.minim : (α×α)set → αset → α
///   := λr A. THE b. isMinim r A b`, i.e. the epsilon `The` over the (registered)
/// `isMinim r A` predicate, threaded with an explicit `Nonempty α`:
///
/// ```text
/// isabelle.def.<minim> : Type → Nonempty α → ((α×α)→Prop) → (α→Prop) → α
///   := λα hne r A. isabelle.def.HOL.The α hne (λb. isMinim_def α r A b)
/// ```
pub(crate) fn build_wo_minim_value_and_type() -> (Expr, Expr) {
    let type_1 = Expr::type_();
    let fa = FVarId::new(0x1_7e01); // α : Type
    let fhne = FVarId::new(0x1_7e02); // hne : Nonempty α
    let fr = FVarId::new(0x1_7e03); // r : (α×α)→Prop
    let fset = FVarId::new(0x1_7e04); // A : α→Prop
    let fb = FVarId::new(0x1_7e05); // b : α (predicate binder)
    let alpha = || Expr::fvar(fa);

    // predicate λb. isMinim_def α r A b — the SAME η-expanded form
    // `embed_term(λb. isMinim r A b)` produces for the RHS.
    let inner = Expr::apps(
        Expr::const_str(ISMINIM_DEF),
        [alpha(), Expr::fvar(fr), Expr::fvar(fset), Expr::fvar(fb)],
    );
    let pred = Expr::lam(BinderInfo::Default, alpha(), inner.abstract_fvar(fb));
    let body = the_applied_ne(&alpha(), &Expr::fvar(fhne), &pred);

    wrap_two_arg(fa, fhne, fr, fset, type_1, body)
}

/// `wo_rel.supr : (α×α)set → αset → α := λr A. minim r (Above r A)`:
///
/// ```text
/// isabelle.def.<supr> : Type → Nonempty α → (Field-slot) → ((α×α)→Prop) → (α→Prop) → α
///   := λα hne field r A. minim_def α hne r (Above_def α field r A)
/// ```
pub(crate) fn build_wo_supr_value_and_type() -> (Expr, Expr) {
    build_wo_succ_value_and_type(ABOVE_DEF)
}

/// `wo_rel.suc : (α×α)set → αset → α := λr A. minim r (AboveS r A)` — as
/// [`build_wo_supr_value_and_type`] but over `AboveS` (the strict successor set).
pub(crate) fn build_wo_suc_value_and_type() -> (Expr, Expr) {
    build_wo_succ_value_and_type(ABOVES_DEF)
}

/// Shared builder for `supr`/`suc` (differing only in `Above` vs `AboveS`):
/// `λα hne field r A. minim_def α hne r (<above> α field r A)`.
fn build_wo_succ_value_and_type(above_def: &str) -> (Expr, Expr) {
    let type_1 = Expr::type_();
    let fa = FVarId::new(0x1_7e11); // α : Type
    let fhne = FVarId::new(0x1_7e12); // hne : Nonempty α
    let ffield = FVarId::new(0x1_7e13); // field : ((α×α)→Prop)→(α→Prop)
    let fr = FVarId::new(0x1_7e14); // r : (α×α)→Prop
    let fset = FVarId::new(0x1_7e15); // A : α→Prop
    let alpha = || Expr::fvar(fa);

    // <above> α field r A : α→Prop
    let above = Expr::apps(
        Expr::const_str(above_def),
        [
            alpha(),
            Expr::fvar(ffield),
            Expr::fvar(fr),
            Expr::fvar(fset),
        ],
    );
    // minim_def α hne r (<above> …) : α
    let body = Expr::apps(
        Expr::const_str(MINIM_DEF),
        [alpha(), Expr::fvar(fhne), Expr::fvar(fr), above],
    );

    // value: λα hne field r A. body — abstract innermost-first.
    let v = body.abstract_fvar(fset);
    let v = Expr::lam(BinderInfo::Default, cset(&alpha()), v);
    let v = v.abstract_fvar(fr);
    let v = Expr::lam(BinderInfo::Default, crel(&alpha()), v);
    let v = v.abstract_fvar(ffield);
    let v = Expr::lam(BinderInfo::Default, field_slot_ty(&alpha()), v);
    let v = v.abstract_fvar(fhne);
    let v = Expr::lam(BinderInfo::Default, nonempty(&alpha()), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, type_1.clone(), v);

    // type: Π α hne field r A. α.
    let t = alpha().abstract_fvar(fset);
    let t = Expr::pi(BinderInfo::Default, cset(&alpha()), t);
    let t = t.abstract_fvar(fr);
    let t = Expr::pi(BinderInfo::Default, crel(&alpha()), t);
    let t = t.abstract_fvar(ffield);
    let t = Expr::pi(BinderInfo::Default, field_slot_ty(&alpha()), t);
    let t = t.abstract_fvar(fhne);
    let t = Expr::pi(BinderInfo::Default, nonempty(&alpha()), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, type_1, t);

    (value, type_)
}

/// Wrap a `minim`-shaped body `λα hne r A. body : Πα hne r A. α` (no `Field` slot).
fn wrap_two_arg(
    fa: FVarId,
    fhne: FVarId,
    fr: FVarId,
    fset: FVarId,
    type_1: Expr,
    body: Expr,
) -> (Expr, Expr) {
    let alpha = || Expr::fvar(fa);
    let v = body.abstract_fvar(fset);
    let v = Expr::lam(BinderInfo::Default, cset(&alpha()), v);
    let v = v.abstract_fvar(fr);
    let v = Expr::lam(BinderInfo::Default, crel(&alpha()), v);
    let v = v.abstract_fvar(fhne);
    let v = Expr::lam(BinderInfo::Default, nonempty(&alpha()), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, type_1.clone(), v);

    let t = alpha().abstract_fvar(fset);
    let t = Expr::pi(BinderInfo::Default, cset(&alpha()), t);
    let t = t.abstract_fvar(fr);
    let t = Expr::pi(BinderInfo::Default, crel(&alpha()), t);
    let t = t.abstract_fvar(fhne);
    let t = Expr::pi(BinderInfo::Default, nonempty(&alpha()), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, type_1, t);
    (value, type_)
}

/// The `wo_rel` `The`-threaded constants (`minim`/`supr`/`suc`) as clean
/// [`Declaration::Definition`]s, in dependency order (`minim` before `supr`/`suc`,
/// which reference `isabelle.def.<minim>` and the `Above`/`AboveS` def-consts).
/// Registered AFTER `HOL.The`, the `isMinim` BNF combinator and the `Above`/`AboveS`
/// opaque combinators their bodies depend on. Non-fatal on registration failure.
#[must_use]
pub(crate) fn wo_the_definition_decls() -> Vec<Declaration> {
    let entries: [(&str, (Expr, Expr)); 3] = [
        (MINIM_DEF, build_wo_minim_value_and_type()),
        (
            "isabelle.def.BNF_Wellorder_Relation.wo_rel.supr",
            build_wo_supr_value_and_type(),
        ),
        (
            "isabelle.def.BNF_Wellorder_Relation.wo_rel.suc",
            build_wo_suc_value_and_type(),
        ),
    ];
    entries
        .into_iter()
        .map(|(name, (value, type_))| Declaration::Definition {
            name: Name::from_string(name),
            level_params: Vec::new(),
            type_,
            value,
            is_reducible: true,
        })
        .collect()
}

/// Read the object type `α` off a `wo_rel` `The`-const type `(α×α)set → αset → α`
/// (its first arrow's domain is `(α×α)set = Set.set (Product_Type.prod α α)`).
fn wo_rel_alpha(t: &IsaType) -> Option<&IsaType> {
    let IsaType::Type { n, a } = t else {
        return None;
    };
    if n != "fun" || a.len() != 2 {
        return None;
    }
    let IsaType::Type { n: sn, a: sa } = &a[0] else {
        return None;
    };
    if sn != "Set.set" || sa.len() != 1 {
        return None;
    }
    let IsaType::Type { n: pn, a: pa } = &sa[0] else {
        return None;
    };
    if pn != "Product_Type.prod" || pa.len() != 2 {
        return None;
    }
    Some(&pa[0])
}

/// The HOL type of the `Relation.Field` argument at object type `α`:
/// `(α×α)set → αset`.
fn field_hol_ty(alpha: &IsaType) -> IsaType {
    let set = |x: IsaType| IsaType::Type {
        n: "Set.set".to_string(),
        a: vec![x],
    };
    let prod = IsaType::Type {
        n: "Product_Type.prod".to_string(),
        a: vec![alpha.clone(), alpha.clone()],
    };
    IsaType::Type {
        n: "fun".to_string(),
        a: vec![set(prod), set(alpha.clone())],
    }
}

/// Whether `thm` is a `wo_rel` `The`-threaded definitional axiom — after stripping
/// leading `⟹`/`⋀` premises its conclusion is a `Pure.eq`/`HOL.eq` whose LHS spine
/// is headed by a registered `minim`/`supr`/`suc` constant ([`wo_the_def_const_name`]).
pub(crate) fn is_wo_the_def(thm: &IsaProvenTheorem) -> bool {
    let concl = strip_leading_imps(&thm.prop);
    let Some((lhs, _rhs)) = pure_eq_parts(concl) else {
        return false;
    };
    let (head, _args) = term_app_spine(lhs);
    matches!(head, IsaTerm::Const { n, .. } if wo_the_def_const_name(n).is_some())
}

impl Ctx {
    /// Embed an occurrence of a `wo_rel` `The`-threaded constant (`minim`/`supr`/
    /// `suc`) to its registered def-const ([`wo_the_def_const_name`]) applied to the
    /// use-site object type `α` and the shared `Nonempty α` parameter (and, for
    /// `supr`/`suc`, the re-embedded `Relation.Field` argument they abstract). The
    /// def-const δ-unfolds to the epsilon-`The`-over-`isMinim` body the RHS spells,
    /// so its `…_def`/`…_def_raw` axiom verifies reflexively. Returns `None` when the
    /// type is not the expected `(α×α)set → αset → α` shape (the caller then falls
    /// back to the opaque `const:` param; the kernel re-checks either way).
    pub(crate) fn embed_wo_the_const(
        &mut self,
        n: &str,
        t: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some(def) = wo_the_def_const_name(n) else {
            return Ok(None);
        };
        let Some(alpha_ty) = wo_rel_alpha(t) else {
            return Ok(None);
        };
        let alpha = self.embed_type(alpha_ty)?;
        let hne = self.term_param(&nonempty_param_key(&alpha), nonempty(&alpha));
        let mut e = Expr::apps(Expr::const_str(def), [alpha.clone(), hne]);
        // `supr`/`suc` thread the opaque `Relation.Field` slot their `Above`/`AboveS`
        // component abstracts — supplied by re-embedding the actual constant at `α`
        // (the SAME parameter / poly-inst def-const a bare occurrence embeds to), so
        // the LHS δβ-reduces to exactly the RHS embedding.
        if matches!(
            n,
            "BNF_Wellorder_Relation.wo_rel.supr" | "BNF_Wellorder_Relation.wo_rel.suc"
        ) {
            let field = self.embed_const_term(&IsaTerm::Const {
                n: "Relation.Field".to_string(),
                t: field_hol_ty(alpha_ty),
            })?;
            e = Expr::app(e, field);
        }
        Ok(Some(e))
    }
}
