// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful clean polymorphic `Definition`s for the **BNF leaf** combinator
//! constants whose `_def` / `_def_raw` bodies are NOT closed lambdas over the
//! mapped encodings — they reference **opaque HOL constants** with no closed clean
//! image (`Relation.Field`, `Finite_Set.finite`, `Hilbert_Choice.Eps`, the prod
//! selectors):
//!
//! ```text
//! BNF_Cardinal_Arithmetic.cinfinite : (α×α) set → bool  := λr. ¬ finite (Field r)
//! BNF_Cardinal_Arithmetic.cfinite   : (α×α) set → bool  := λr.   finite (Field r)
//! BNF_Def.pick_middlep : (α→β→bool)→(β→γ→bool)→α→γ→β
//!                                  := λP Q a c. Eps (λb. P a b ∧ Q b c)
//! BNF_Def.fstOp : (α→β→bool)→(β→γ→bool)→(α×γ)→(α×β)
//!                                  := λP Q ac. (fst ac, pick_middlep P Q (fst ac) (snd ac))
//! BNF_Def.sndOp : (α→β→bool)→(β→γ→bool)→(α×γ)→(β×γ)
//!                                  := λP Q ac. (pick_middlep P Q (fst ac) (snd ac), snd ac)
//! ```
//!
//! Because the opaque constants have no closed clean image, each combinator's
//! clean `Definition` abstracts them as **leading value binders** (the
//! `fChoice`/`Eps` opaque-const-arg pattern). At every use-site
//! [`Ctx::embed_bnf_opaque_combinator`] supplies each opaque binder by
//! **re-embedding the actual HOL constant** at the solved instantiation — the
//! SAME `const:` parameter (or registered poly-inst def-const) that a bare
//! occurrence of the constant embeds to. So the combinator's `_def` LHS
//! δβ-reduces to EXACTLY what its RHS embeds to, and the whole definitional
//! equation is reflexive ([`Eq.refl`], via the `is_bnf_def`-gated arm in
//! `translate.rs`).
//!
//! ## Round-14: relators / predicators / set-functions / `collect`
//!
//! The same opaque-const-arg framework hosts the concrete sum/prod/fun BNF
//! relator, predicator, and set-function `_def`s, plus `collect`. Their bodies
//! are NOT the case-split shapes one might expect — the datatype package generates
//! each as a **least fixed point** `Inductive.complete_lattice_class.lfp (λp x…. …)`
//! of a constant (recursion-free) functional (or, for `collect`, a set-instance
//! `Complete_Lattices.Sup_class.Sup`). Those two overloaded class methods are the
//! only opaque slots; every other constituent (`Inl`/`Inr`/`Pair` → the real
//! type-parameterised `@Sum.inl`/`@Sum.inr`/`@Prod.mk`, the `∀`/`∃`/`∨`/`∧`/`@Eq`
//! connectives, `Set.image`) is built directly:
//!
//! ```text
//! Basic_BNFs.pred_fun  A B = λf. ∀x. A x → B (f x)                         (no opaque slot)
//! Basic_BNFs.pred_prod P Q = lfp (λp x. ∃a b. x=(a,b) ∧ P a ∧ Q b)
//! Basic_BNFs.pred_sum  P Q = lfp (λp x. (∃a. x=Inl a ∧ P a) ∨ (∃b. x=Inr b ∧ Q b))
//! Basic_BNFs.rel_prod  R S = lfp (λp x1 x2. ∃a b c d. x1=(a,c) ∧ x2=(b,d) ∧ R a b ∧ S c d)
//! BNF_Def.rel_sum      R S = lfp (λp x1 x2. (∃a c. …Inl…∧R a c) ∨ (∃b d. …Inr…∧S b d))
//! Basic_BNFs.fstsp p = lfp (λpa x. x = fst p)   sndsp p = lfp (λpa x. x = snd p)
//! Basic_BNFs.setlp s = lfp (λp x. ∃x'. x=x' ∧ s = Inl x')   (setrp: Inr)
//! Basic_BNFs.setl  s = Collect (λx. setlp s x)             (setr: setrp; Collect = id)
//! BNF_Def.collect F x = Sup (image (λf. f x) F)            (Sup at the set instance)
//! ```
//!
//! Each `lfp`/`Sup` occurs at a SINGLE instantiation per body, so its name-only
//! opaque supply never aliases (unlike the two-`Field` cardinal family). `setl`/
//! `setr` reference the `setlp`/`setrp` def-const and forward the SAME `lfp` slot.
//!
//! ## The cardinal-arithmetic family (`csum`/`cprod`/`cexp`/`Csum`) — round-17
//!
//! Those four reference `card_of ∘ Field` at **two type instantiations** (`α`,
//! `β`): each body is `card_of (<combiner> (Field r1) (Field r2))` for a combiner
//! `Plus`/`Sigma`/`Func`. r12/r13 diagnosed the blocker as the two `Field`
//! occurrences colliding on a name-only key. This is the SAME two-`Field` shape
//! r15/r16 cracked for `embedS`/`iso`: the round-16 `const_param` type-suffix
//! keying (`const_param_key`) mints DISTINCT params for `Field@α` and `Field@β`'s
//! inner ops, so the re-embedded `Field@α`/`Field@β` pair is well-typed and the
//! `_def` verifies reflexively. The prerequisite is registering `card_of` itself
//! (`card_of A = SOME r. card_order_on A r`, a single-instantiation Hilbert `Eps`
//! over the opaque `card_order_on`, structurally identical to `cinfinite`); the
//! arithmetic bodies then reference the `card_of` def-const, forwarding its
//! `Eps`/`card_order_on` slots at the combined instance. `cardSuc` ships the same
//! way (`Eps` over `isCardSuc`). The monomorphic `cone`/`ctwo` (`card_of {()}` /
//! `card_of UNIV::bool set`) carry NO type variable and NO two-`Field` collision —
//! a separable follow-up (they need the concrete unit/bool set-constructor images
//! hard-wired at the Expr level). See `docs/analysis/zproof-cardinal-wall.md`.
//!
//! ## Faithfulness
//!
//! Every stored type is the REAL definitional equation, with the named def-const
//! application (`@isabelle.def.C tvars opaques`) and the embedded body as DISTINCT
//! operands — never a `body = body` tautology, never fabricated. The kernel
//! re-checks `Eq.refl α lhs : @Eq α lhs rhs`, accepting **iff** the def-const
//! δβ-reduces to the RHS, so a wrong body/opaque-supply **rejects, never
//! false-verifies**. No axioms: pure λ over the foundational encodings plus the
//! opaque-const binders, so every consumer stays `KernelVerified` to the three
//! foundationals.

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Expr};

use super::super::super::isabelle_pure::{IsaTerm, IsaType};
use super::super::{match_tvars, method_obj_tvars, obj_level, Ctx, TranslateError};
use super::sets::ball_encoding;
use super::{ex_encoding, image_encoding};

// ---------------------------------------------------------------------------
// Names / schematic HOL types
// ---------------------------------------------------------------------------

/// The kernel declaration name of the clean polymorphic `Definition` registered
/// for an **opaque-arg** BNF combinator constant, or `None` for any other name.
pub(crate) fn bnf_opaque_def_const_name(name: &str) -> Option<&'static str> {
    match name {
        "BNF_Cardinal_Arithmetic.cinfinite" => {
            Some("isabelle.def.BNF_Cardinal_Arithmetic.cinfinite")
        }
        "BNF_Cardinal_Arithmetic.cfinite" => Some("isabelle.def.BNF_Cardinal_Arithmetic.cfinite"),
        "BNF_Def.pick_middlep" => Some("isabelle.def.BNF_Def.pick_middlep"),
        "BNF_Def.fstOp" => Some("isabelle.def.BNF_Def.fstOp"),
        "BNF_Def.sndOp" => Some("isabelle.def.BNF_Def.sndOp"),
        // Round-14 relators/predicators + set-functions + `collect`. Each body
        // references an OPAQUE overloaded class method (`Inductive.complete_lattice
        // _class.lfp` at a single instance, or `Complete_Lattices.Sup_class.Sup` at
        // the set instance) with no closed clean image, supplied at the use-site by
        // re-embedding the actual HOL constant.
        "BNF_Def.rel_sum" => Some("isabelle.def.BNF_Def.rel_sum"),
        "BNF_Def.collect" => Some("isabelle.def.BNF_Def.collect"),
        "Basic_BNFs.pred_fun" => Some("isabelle.def.Basic_BNFs.pred_fun"),
        "Basic_BNFs.pred_prod" => Some("isabelle.def.Basic_BNFs.pred_prod"),
        "Basic_BNFs.pred_sum" => Some("isabelle.def.Basic_BNFs.pred_sum"),
        "Basic_BNFs.rel_prod" => Some("isabelle.def.Basic_BNFs.rel_prod"),
        "Basic_BNFs.fstsp" => Some("isabelle.def.Basic_BNFs.fstsp"),
        "Basic_BNFs.sndsp" => Some("isabelle.def.Basic_BNFs.sndsp"),
        "Basic_BNFs.setl" => Some("isabelle.def.Basic_BNFs.setl"),
        "Basic_BNFs.setr" => Some("isabelle.def.Basic_BNFs.setr"),
        "Basic_BNFs.setlp" => Some("isabelle.def.Basic_BNFs.setlp"),
        "Basic_BNFs.setrp" => Some("isabelle.def.Basic_BNFs.setrp"),
        // Round-14 wellorder set-builders `Above`/`AboveS` — closed EXCEPT for the
        // single opaque `Relation.Field` reference (a SINGLE type instantiation `α`,
        // no `card_of` two-type collision), so they ship via the opaque-arg framework
        // exactly like `cinfinite`/`cfinite` (which also carry a single `Field`).
        "Order_Relation.Above" => Some("isabelle.def.Order_Relation.Above"),
        "Order_Relation.AboveS" => Some("isabelle.def.Order_Relation.AboveS"),
        // Round-15 wellorder embedding cluster. Each body composes from the already-
        // registered `under` (`bnf_defs`), `bij_betw` (`fun_defs`) and `embed` (this
        // module) def-consts plus the opaque `Relation.Field` slot(s) `Above`/`AboveS`
        // proved out. `embed`/`ord_to_filter` use a SINGLE `Field` instantiation (`α`)
        // and ship here. `embedS`/`iso` reference `Field` at BOTH `α` and `β`, which
        // hits the two-`Field` poly-inst inner-param collision (r13 §4 — the same wall
        // as `csum`/`cprod`); they kernel-reject on the re-embedded `Field@α`/`Field@β`
        // pair, so they are DEFERRED (documented in `docs/analysis/zproof-r15-embedding.md`).
        "BNF_Wellorder_Embedding.embed" => Some("isabelle.def.BNF_Wellorder_Embedding.embed"),
        // Round-16: the two-`Field` strict-embedding / isomorphism predicates. They
        // reference `Field` at BOTH `α` and `β`; the r16 `const_param` type-suffix
        // keying makes `polyinst.Field@α` and `polyinst.Field@β`'s inner ops distinct
        // params, so the re-embedded `Field@α`/`Field@β` pair is well-typed and the
        // `_def` verifies reflexively (previously deferred — r15 §4).
        "BNF_Wellorder_Embedding.embedS" => Some("isabelle.def.BNF_Wellorder_Embedding.embedS"),
        "BNF_Wellorder_Embedding.iso" => Some("isabelle.def.BNF_Wellorder_Embedding.iso"),
        "BNF_Wellorder_Constructions.ord_to_filter" => {
            Some("isabelle.def.BNF_Wellorder_Constructions.ord_to_filter")
        }
        // Round-17 (cardinal wall). `card_of A = SOME r. card_order_on A r` and
        // `cardSuc r = SOME r'. isCardSuc r r'` are Hilbert-`Eps` choices over an
        // opaque `card_order_on` / `isCardSuc` predicate — a SINGLE type
        // instantiation, so they ship exactly like `cinfinite`/`cfinite`. Their
        // registration is the prerequisite for the two-`Field` cardinal arithmetic.
        "BNF_Cardinal_Order_Relation.card_of" => {
            Some("isabelle.def.BNF_Cardinal_Order_Relation.card_of")
        }
        "BNF_Cardinal_Order_Relation.cardSuc" => {
            Some("isabelle.def.BNF_Cardinal_Order_Relation.cardSuc")
        }
        // Round-17 cardinal arithmetic — the two-`Field`/two-type wall. Each body is
        // `card_of (<combiner> (Field r1) (Field r2))` with `Field` at BOTH `α` and
        // `β`, unblocked by the same `const_param` type-suffix keying that landed
        // `embedS`/`iso` (r16). They reference the `card_of` def-const above,
        // forwarding its `Eps`/`card_order_on` opaque slots at the combined instance.
        "BNF_Cardinal_Arithmetic.csum" => Some("isabelle.def.BNF_Cardinal_Arithmetic.csum"),
        "BNF_Cardinal_Arithmetic.cprod" => Some("isabelle.def.BNF_Cardinal_Arithmetic.cprod"),
        "BNF_Cardinal_Arithmetic.cexp" => Some("isabelle.def.BNF_Cardinal_Arithmetic.cexp"),
        "BNF_Cardinal_Arithmetic.Csum" => Some("isabelle.def.BNF_Cardinal_Arithmetic.Csum"),
        _ => None,
    }
}

/// The kernel names of the already-registered constituent def-consts the embedding
/// cluster bodies reference directly (supplying their type/value args), so each
/// occurrence δβ-reduces to exactly what the corresponding RHS sub-term embeds to.
const UNDER_DEF: &str = "isabelle.def.Order_Relation.under";
const BIJ_BETW_DEF: &str = "isabelle.def.Fun.bij_betw";
const EMBED_DEF: &str = "isabelle.def.BNF_Wellorder_Embedding.embed";
/// The registered `card_of` def-const; the cardinal-arithmetic bodies reference it
/// directly (forwarding its `Eps`/`card_order_on` opaque slots at the combined
/// instance), so each `card_of (…)` sub-term δβ-reduces to exactly what a bare
/// `card_of` occurrence in the RHS embeds to.
const CARD_OF_DEF: &str = "isabelle.def.BNF_Cardinal_Order_Relation.card_of";

// --- HOL type builders (schematic, with `TVar`s) ---
fn tv(n: &str) -> IsaType {
    IsaType::TVar {
        n: n.to_string(),
        i: 0,
    }
}
fn hfun(a: IsaType, b: IsaType) -> IsaType {
    IsaType::Type {
        n: "fun".to_string(),
        a: vec![a, b],
    }
}
fn hbool() -> IsaType {
    IsaType::Type {
        n: "HOL.bool".to_string(),
        a: Vec::new(),
    }
}
fn hset(a: IsaType) -> IsaType {
    IsaType::Type {
        n: "Set.set".to_string(),
        a: vec![a],
    }
}
fn hprod(a: IsaType, b: IsaType) -> IsaType {
    IsaType::Type {
        n: "Product_Type.prod".to_string(),
        a: vec![a, b],
    }
}
fn hsum(a: IsaType, b: IsaType) -> IsaType {
    IsaType::Type {
        n: "Sum_Type.sum".to_string(),
        a: vec![a, b],
    }
}

/// The exact HOL schematic type of an opaque-arg BNF combinator constant
/// (matching the raw export). Drives the object-type-variable order shared by the
/// def-const's leading `Type` binders and the use-site instantiation.
pub(crate) fn bnf_opaque_schematic(name: &str) -> Option<IsaType> {
    let (a, b, c, d) = (tv("'a"), tv("'b"), tv("'c"), tv("'d"));
    let rel = |x: IsaType| hset(hprod(x.clone(), x)); // ('x×'x) set
    Some(match name {
        // (α×α)set → bool
        "BNF_Cardinal_Arithmetic.cinfinite" | "BNF_Cardinal_Arithmetic.cfinite" => {
            hfun(rel(a), hbool())
        }
        // (α→β→bool) → (β→γ→bool) → α → γ → β
        "BNF_Def.pick_middlep" => hfun(
            hfun(a.clone(), hfun(b.clone(), hbool())),
            hfun(
                hfun(b.clone(), hfun(c.clone(), hbool())),
                hfun(a.clone(), hfun(c, b)),
            ),
        ),
        // (α→β→bool) → (β→γ→bool) → (α×γ) → (α×β)
        "BNF_Def.fstOp" => hfun(
            hfun(a.clone(), hfun(b.clone(), hbool())),
            hfun(
                hfun(b.clone(), hfun(c.clone(), hbool())),
                hfun(hprod(a.clone(), c), hprod(a, b)),
            ),
        ),
        // (α→β→bool) → (β→γ→bool) → (α×γ) → (β×γ)
        "BNF_Def.sndOp" => hfun(
            hfun(a.clone(), hfun(b.clone(), hbool())),
            hfun(
                hfun(b.clone(), hfun(c.clone(), hbool())),
                hfun(hprod(a, c.clone()), hprod(b, c)),
            ),
        ),
        // (α→β) → bool  (function-BNF predicator: pred_fun A B f = ∀x. A x → B(f x))
        "Basic_BNFs.pred_fun" => hfun(
            hfun(a.clone(), hbool()),
            hfun(
                hfun(b.clone(), hbool()),
                hfun(hfun(a.clone(), b.clone()), hbool()),
            ),
        ),
        // (α→bool) → (β→bool) → (α×β → bool)  (prod-BNF predicator)
        "Basic_BNFs.pred_prod" => hfun(
            hfun(a.clone(), hbool()),
            hfun(
                hfun(b.clone(), hbool()),
                hfun(hprod(a.clone(), b.clone()), hbool()),
            ),
        ),
        // (α→bool) → (β→bool) → (α+β → bool)  (sum-BNF predicator)
        "Basic_BNFs.pred_sum" => hfun(
            hfun(a.clone(), hbool()),
            hfun(
                hfun(b.clone(), hbool()),
                hfun(hsum(a.clone(), b.clone()), hbool()),
            ),
        ),
        // (α→β→bool) → (γ→δ→bool) → (α×γ → β×δ → bool)  (prod-BNF relator).
        // NB the schematic uses the first-occurrence tvar order (α,β,γ,δ).
        "Basic_BNFs.rel_prod" => hfun(
            hfun(a.clone(), hfun(b.clone(), hbool())),
            hfun(
                hfun(c.clone(), hfun(d.clone(), hbool())),
                hfun(
                    hprod(a.clone(), c.clone()),
                    hfun(hprod(b.clone(), d.clone()), hbool()),
                ),
            ),
        ),
        // (α→β→bool) → (γ→δ→bool) → (α+γ → β+δ → bool)  (sum-BNF relator).
        "BNF_Def.rel_sum" => hfun(
            hfun(a.clone(), hfun(b.clone(), hbool())),
            hfun(
                hfun(c.clone(), hfun(d.clone(), hbool())),
                hfun(
                    hsum(a.clone(), c.clone()),
                    hfun(hsum(b.clone(), d.clone()), hbool()),
                ),
            ),
        ),
        // α×β → α set  /  α×β → β set  (prod projections as select-predicates)
        "Basic_BNFs.fstsp" => hfun(hprod(a.clone(), b.clone()), hfun(a.clone(), hbool())),
        "Basic_BNFs.sndsp" => hfun(hprod(a.clone(), b.clone()), hfun(b.clone(), hbool())),
        // The `p` predicators return `'a ⇒ bool` (the raw membership predicate); the
        // `setl`/`setr` set-functions return `'a set` — DISTINCT HOL type-constructor
        // heads (`fun` vs `Set.set`), so their schematics must differ for `match_tvars`
        // to solve the use-site instantiation from the exported `_def` constant type.
        "Basic_BNFs.setlp" => hfun(hsum(a.clone(), b.clone()), hfun(a.clone(), hbool())),
        "Basic_BNFs.setrp" => hfun(hsum(a.clone(), b.clone()), hfun(b.clone(), hbool())),
        "Basic_BNFs.setl" => hfun(hsum(a.clone(), b.clone()), hset(a.clone())),
        "Basic_BNFs.setr" => hfun(hsum(a.clone(), b.clone()), hset(b.clone())),
        // (α → β set) set → α → β set  (collect = Sup ∘ image-application)
        "BNF_Def.collect" => hfun(
            hset(hfun(a.clone(), hset(b.clone()))),
            hfun(a.clone(), hset(b.clone())),
        ),
        // (α×α)set → αset → αset  (Above / AboveS)
        "Order_Relation.Above" | "Order_Relation.AboveS" => {
            hfun(rel(a.clone()), hfun(hset(a.clone()), hset(a)))
        }
        // (α×α)set → (β×β)set → (α→β) → bool  (embed — the order-embedding predicate;
        // embedS/iso share the SAME schematic — a strict-embedding / isomorphism refine
        // `embed` with an added `bij_betw` conjunct, same argument shape).
        "BNF_Wellorder_Embedding.embed"
        | "BNF_Wellorder_Embedding.embedS"
        | "BNF_Wellorder_Embedding.iso" => hfun(
            rel(a.clone()),
            hfun(rel(b.clone()), hfun(hfun(a.clone(), b.clone()), hbool())),
        ),
        // (α×α)set → (α×α)set → αset  (ord_to_filter — both relations at α)
        "BNF_Wellorder_Constructions.ord_to_filter" => {
            hfun(rel(a.clone()), hfun(rel(a.clone()), hset(a)))
        }
        // αset → (α×α)set  (card_of — the canonical well-order of a set)
        "BNF_Cardinal_Order_Relation.card_of" => hfun(hset(a.clone()), rel(a)),
        // (α×α)set → ((α set × α set))set  (cardSuc — a relation on `α set`)
        "BNF_Cardinal_Order_Relation.cardSuc" => hfun(rel(a.clone()), rel(hset(a))),
        // (α×α)set → (β×β)set → ((α+β)×(α+β))set  (cardinal sum `+c`)
        "BNF_Cardinal_Arithmetic.csum" => hfun(
            rel(a.clone()),
            hfun(rel(b.clone()), rel(hsum(a.clone(), b.clone()))),
        ),
        // (α×α)set → (β×β)set → ((α×β)×(α×β))set  (cardinal product `*c`)
        "BNF_Cardinal_Arithmetic.cprod" => hfun(
            rel(a.clone()),
            hfun(rel(b.clone()), rel(hprod(a.clone(), b.clone()))),
        ),
        // (β×β)set → (α×α)set → ((α⇒β)×(α⇒β))set  (cardinal exponent `^c`; first
        // argument is the `'b`-relation, second the `'a`-relation — NB tvar order).
        "BNF_Cardinal_Arithmetic.cexp" => hfun(
            rel(b.clone()),
            hfun(rel(a.clone()), rel(hfun(a.clone(), b.clone()))),
        ),
        // (α×α)set → (α → (β×β)set) → ((α×β)×(α×β))set  (dependent cardinal sum)
        "BNF_Cardinal_Arithmetic.Csum" => hfun(
            rel(a.clone()),
            hfun(
                hfun(a.clone(), rel(b.clone())),
                rel(hprod(a.clone(), b.clone())),
            ),
        ),
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// Clean type helpers (Expr level) — `bool = Prop`, `α set = α → Prop`,
// `α × β = Prod α β`.
// ---------------------------------------------------------------------------

fn cset(a: &Expr) -> Expr {
    Expr::arrow(a.clone(), Expr::prop())
}
fn cprod_ty(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Prod", vec![Level::zero(), Level::zero()]),
        [a.clone(), b.clone()],
    )
}
fn crel(a: &Expr) -> Expr {
    cset(&cprod_ty(a, a))
}
/// `@Prod.mk.{0,0} α β a b` — clean's pair constructor (`Product_Type.Pair`).
fn prod_mk(alpha: &Expr, beta: &Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Prod.mk", vec![Level::zero(), Level::zero()]),
        [alpha.clone(), beta.clone(), a, b],
    )
}
/// `@Sum.{0,0} α β` — clean's disjoint-sum type (`Sum_Type.sum`).
fn csum_ty(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Sum", vec![Level::zero(), Level::zero()]),
        [a.clone(), b.clone()],
    )
}
/// `@Sum.inl.{0,0} α β : α → Sum α β` — clean's left injection (`Sum_Type.Inl`).
fn sum_inl(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Sum.inl", vec![Level::zero(), Level::zero()]),
        [a.clone(), b.clone()],
    )
}
/// `@Sum.inr.{0,0} α β : β → Sum α β` — clean's right injection (`Sum_Type.Inr`).
fn sum_inr(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Sum.inr", vec![Level::zero(), Level::zero()]),
        [a.clone(), b.clone()],
    )
}
/// `@Eq.{obj} α a b` — the object-level HOL equality, exactly as `embed_term`
/// emits `HOL.eq`.
fn eq_obj(alpha: &Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [alpha.clone(), a, b],
    )
}
/// The `HOL.conj` def-const, applied.
fn conj(a: Expr, b: Expr) -> Expr {
    Expr::apps(super::conj_def_const(), [a, b])
}
/// The `HOL.disj` def-const, applied.
fn disj(a: Expr, b: Expr) -> Expr {
    Expr::apps(super::disj_def_const(), [a, b])
}
/// The `HOL.Not` def-const, applied.
fn not_(a: Expr) -> Expr {
    Expr::app(Expr::const_str("isabelle.def.HOL.Not"), a)
}
/// The clean type of an overloaded complete-lattice `lfp` at the lattice whose
/// carrier embeds to `carrier`: `((carrier → carrier) → carrier)`.
fn lfp_clean_ty(carrier: &Expr) -> Expr {
    Expr::arrow(
        Expr::arrow(carrier.clone(), carrier.clone()),
        carrier.clone(),
    )
}
/// The HOL type of an overloaded complete-lattice `lfp` at a lattice with carrier
/// HOL type `carrier`: `((carrier ⇒ carrier) ⇒ carrier)`.
fn lfp_hol_ty(carrier: IsaType) -> IsaType {
    hfun(hfun(carrier.clone(), carrier.clone()), carrier)
}

// ---------------------------------------------------------------------------
// Definition-building framework (with opaque-const arg slots)
// ---------------------------------------------------------------------------

/// Per-constant builder scratch: the object-type-variable fvars (in
/// [`method_obj_tvars`] first-occurrence order), the ordered opaque-const arg
/// slots (fvar + clean type), and a fresh-fvar allocator for the body's local
/// (`∀`/`∃`/`λ`) binders. All fvars are abstracted in [`OpaqueBuild::finish`].
struct OpaqueBuild {
    tv: BTreeMap<String, Expr>,
    tv_fvars: Vec<FVarId>,
    opaque: Vec<(FVarId, Expr)>,
    next_opaque: u64,
    next_local: u64,
}

impl OpaqueBuild {
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
            opaque: Vec::new(),
            next_opaque: base + 0x100,
            next_local: base + 0x1000,
        })
    }

    /// The fvar `Expr` for a tvar name (`"'a"`, …).
    fn t(&self, n: &str) -> Expr {
        self.tv
            .get(n)
            .cloned()
            .expect("bnf-cardinal builder: unknown tvar name")
    }

    /// Allocate the next opaque-const arg slot with clean type `ty`; returns its
    /// fvar `Expr`. The slot ORDER here MUST match the supply order in
    /// [`Ctx::embed_bnf_opaque_combinator`].
    fn opaque(&mut self, ty: Expr) -> Expr {
        let f = FVarId::new(self.next_opaque);
        self.next_opaque += 1;
        self.opaque.push((f, ty));
        Expr::fvar(f)
    }

    /// A fresh, distinct fvar for a value/local binder.
    fn fresh(&mut self) -> FVarId {
        let f = FVarId::new(self.next_local);
        self.next_local += 1;
        f
    }

    /// Assemble `(value, type)`: `λ tv. λ opaque. λ args. body` /
    /// `Π tv. Π opaque. Π args. result`. Abstracts innermost-first (args, then the
    /// opaque slots, then the tvars), so [`Ctx::embed_bnf_opaque_combinator`]'s
    /// `def-const @tvs @opaques` leaves exactly `λ args. body : Π args. result` for
    /// the use-site application to β-reduce.
    fn finish(&self, args: &[(FVarId, Expr)], body: Expr, result: Expr) -> (Expr, Expr) {
        let mut value = body;
        for (f, ty) in args.iter().rev() {
            value = value.abstract_fvar(*f);
            value = Expr::lam(BinderInfo::Default, ty.clone(), value);
        }
        for (f, ty) in self.opaque.iter().rev() {
            value = value.abstract_fvar(*f);
            value = Expr::lam(BinderInfo::Default, ty.clone(), value);
        }
        for f in self.tv_fvars.iter().rev() {
            value = value.abstract_fvar(*f);
            value = Expr::lam(BinderInfo::Default, Expr::type_(), value);
        }
        let mut type_ = result;
        for (f, ty) in args.iter().rev() {
            type_ = type_.abstract_fvar(*f);
            type_ = Expr::pi(BinderInfo::Default, ty.clone(), type_);
        }
        for (f, ty) in self.opaque.iter().rev() {
            type_ = type_.abstract_fvar(*f);
            type_ = Expr::pi(BinderInfo::Default, ty.clone(), type_);
        }
        for f in self.tv_fvars.iter().rev() {
            type_ = type_.abstract_fvar(*f);
            type_ = Expr::pi(BinderInfo::Default, Expr::type_(), type_);
        }
        (value, type_)
    }
}

// --- per-constant bodies (opaque slot order is documented + mirrored in
//     `embed_bnf_opaque_combinator`'s supply order) ---

/// `cinfinite r = ¬ finite (Field r)`. Slots: [field@α, finite@α].
fn build_cinfinite(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let a = b.t("'a");
    let field = b.opaque(Expr::arrow(crel(&a), cset(&a)));
    let finite = b.opaque(Expr::arrow(cset(&a), Expr::prop()));
    let r = b.fresh();
    let body = not_(Expr::app(finite, Expr::app(field, Expr::fvar(r))));
    b.finish(&[(r, crel(&a))], body, Expr::prop())
}

/// `cfinite r = finite (Field r)`. Slots: [field@α, finite@α].
fn build_cfinite(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let a = b.t("'a");
    let field = b.opaque(Expr::arrow(crel(&a), cset(&a)));
    let finite = b.opaque(Expr::arrow(cset(&a), Expr::prop()));
    let r = b.fresh();
    let body = Expr::app(finite, Expr::app(field, Expr::fvar(r)));
    b.finish(&[(r, crel(&a))], body, Expr::prop())
}

/// `pick_middlep P Q a c = Eps (λb. P a b ∧ Q b c)`. Slots: [eps@β].
fn build_pick_middlep(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb, tc) = (b.t("'a"), b.t("'b"), b.t("'c"));
    // Eps : (β → bool) → β
    let eps = b.opaque(Expr::arrow(
        Expr::arrow(tb.clone(), Expr::prop()),
        tb.clone(),
    ));
    let (p, q, a, c) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    let bnd = b.fresh();
    let pab = Expr::apps(Expr::fvar(p), [Expr::fvar(a), Expr::fvar(bnd)]);
    let qbc = Expr::apps(Expr::fvar(q), [Expr::fvar(bnd), Expr::fvar(c)]);
    let pred_body = conj(pab, qbc);
    let pred = Expr::lam(
        BinderInfo::Default,
        tb.clone(),
        pred_body.abstract_fvar(bnd),
    );
    let body = Expr::app(eps, pred);
    let p_ty = Expr::arrow(ta.clone(), Expr::arrow(tb.clone(), Expr::prop()));
    let q_ty = Expr::arrow(tb.clone(), Expr::arrow(tc.clone(), Expr::prop()));
    b.finish(&[(p, p_ty), (q, q_ty), (a, ta), (c, tc)], body, tb)
}

/// The `isabelle.def.BNF_Def.pick_middlep` def-const applied to its three tvar
/// types + the (shared) `eps` slot + `P Q x y` — the middle element used by both
/// `fstOp` and `sndOp`.
#[allow(clippy::too_many_arguments)]
fn pick_middlep_app(
    ta: &Expr,
    tb: &Expr,
    tc: &Expr,
    eps: &Expr,
    p: &Expr,
    q: &Expr,
    x: Expr,
    y: Expr,
) -> Expr {
    Expr::apps(
        Expr::const_str("isabelle.def.BNF_Def.pick_middlep"),
        [
            ta.clone(),
            tb.clone(),
            tc.clone(),
            eps.clone(),
            p.clone(),
            q.clone(),
            x,
            y,
        ],
    )
}

/// `fstOp P Q ac = (fst ac, pick_middlep P Q (fst ac) (snd ac))`.
/// Slots: [eps@β, fst@(α×γ→α), snd@(α×γ→γ)].
fn build_fstop(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb, tc) = (b.t("'a"), b.t("'b"), b.t("'c"));
    let ac_ty = cprod_ty(&ta, &tc);
    let eps = b.opaque(Expr::arrow(
        Expr::arrow(tb.clone(), Expr::prop()),
        tb.clone(),
    ));
    let fst = b.opaque(Expr::arrow(ac_ty.clone(), ta.clone()));
    let snd = b.opaque(Expr::arrow(ac_ty.clone(), tc.clone()));
    let (p, q, ac) = (b.fresh(), b.fresh(), b.fresh());
    let fac = Expr::app(fst, Expr::fvar(ac));
    let sac = Expr::app(snd, Expr::fvar(ac));
    let mid = pick_middlep_app(
        &ta,
        &tb,
        &tc,
        &eps,
        &Expr::fvar(p),
        &Expr::fvar(q),
        fac.clone(),
        sac,
    );
    let body = prod_mk(&ta, &tb, fac, mid);
    let p_ty = Expr::arrow(ta.clone(), Expr::arrow(tb.clone(), Expr::prop()));
    let q_ty = Expr::arrow(tb.clone(), Expr::arrow(tc.clone(), Expr::prop()));
    b.finish(
        &[(p, p_ty), (q, q_ty), (ac, ac_ty)],
        body,
        cprod_ty(&ta, &tb),
    )
}

/// `sndOp P Q ac = (pick_middlep P Q (fst ac) (snd ac), snd ac)`.
/// Slots: [eps@β, fst@(α×γ→α), snd@(α×γ→γ)].
fn build_sndop(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb, tc) = (b.t("'a"), b.t("'b"), b.t("'c"));
    let ac_ty = cprod_ty(&ta, &tc);
    let eps = b.opaque(Expr::arrow(
        Expr::arrow(tb.clone(), Expr::prop()),
        tb.clone(),
    ));
    let fst = b.opaque(Expr::arrow(ac_ty.clone(), ta.clone()));
    let snd = b.opaque(Expr::arrow(ac_ty.clone(), tc.clone()));
    let (p, q, ac) = (b.fresh(), b.fresh(), b.fresh());
    let fac = Expr::app(fst, Expr::fvar(ac));
    let sac = Expr::app(snd, Expr::fvar(ac));
    let mid = pick_middlep_app(
        &ta,
        &tb,
        &tc,
        &eps,
        &Expr::fvar(p),
        &Expr::fvar(q),
        fac,
        sac.clone(),
    );
    let body = prod_mk(&tb, &tc, mid, sac);
    let p_ty = Expr::arrow(ta.clone(), Expr::arrow(tb.clone(), Expr::prop()));
    let q_ty = Expr::arrow(tb.clone(), Expr::arrow(tc.clone(), Expr::prop()));
    b.finish(
        &[(p, p_ty), (q, q_ty), (ac, ac_ty)],
        body,
        cprod_ty(&tb, &tc),
    )
}

// --- Round-14 relators / predicators / set-functions / collect ---

/// `pred_fun A B = λf. ∀x. A x → B (f x)` (function-BNF predicator). No opaque
/// slot — a genuinely closed lambda over `∀`/`→`, registered here (zero opaque
/// slots) for uniformity with the sibling predicators.
fn build_pred_fun(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let (pa, pb, f, x) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    let ax = Expr::app(Expr::fvar(pa), Expr::fvar(x));
    let bfx = Expr::app(Expr::fvar(pb), Expr::app(Expr::fvar(f), Expr::fvar(x)));
    let all_x = Expr::pi(
        BinderInfo::Default,
        ta.clone(),
        Expr::arrow(ax, bfx).abstract_fvar(x),
    );
    let f_ty = Expr::arrow(ta.clone(), tb.clone());
    let body = Expr::lam(BinderInfo::Default, f_ty.clone(), all_x.abstract_fvar(f));
    let pa_ty = Expr::arrow(ta.clone(), Expr::prop());
    let pb_ty = Expr::arrow(tb.clone(), Expr::prop());
    b.finish(
        &[(pa, pa_ty), (pb, pb_ty)],
        body,
        Expr::arrow(f_ty, Expr::prop()),
    )
}

/// The lfp-generated functional wrapper: `lfp (λp:carrier. λx:elem. inner)` where
/// `p` is the (unused) recursion binder. `lfp` is the opaque slot (already
/// allocated by the caller). Shared by the set-function / predicator builders.
fn lfp_unary(lfp: Expr, carrier: &Expr, elem: &Expr, x: FVarId, p: FVarId, inner: Expr) -> Expr {
    let lam_x = Expr::lam(BinderInfo::Default, elem.clone(), inner.abstract_fvar(x));
    let func = Expr::lam(BinderInfo::Default, carrier.clone(), lam_x.abstract_fvar(p));
    Expr::app(lfp, func)
}

/// `setlp s = lfp (λp x. ∃x'. x = x' ∧ s = Inl x')`. Slot: [lfp@(α set)].
fn build_setlp(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let carrier = cset(&ta);
    let lfp = b.opaque(lfp_clean_ty(&carrier));
    let sum_ty = csum_ty(&ta, &tb);
    let (s, p, x, xp) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    let eq_xx = eq_obj(&ta, Expr::fvar(x), Expr::fvar(xp));
    let inl = Expr::app(sum_inl(&ta, &tb), Expr::fvar(xp));
    let eq_s = eq_obj(&sum_ty, Expr::fvar(s), inl);
    let pred = Expr::lam(
        BinderInfo::Default,
        ta.clone(),
        conj(eq_xx, eq_s).abstract_fvar(xp),
    );
    let inner = ex_encoding(&ta, &pred);
    let body = lfp_unary(lfp, &carrier, &ta, x, p, inner);
    b.finish(&[(s, sum_ty)], body, cset(&ta))
}

/// `setrp s = lfp (λp x. ∃x'. x = x' ∧ s = Inr x')`. Slot: [lfp@(β set)].
fn build_setrp(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let carrier = cset(&tb);
    let lfp = b.opaque(lfp_clean_ty(&carrier));
    let sum_ty = csum_ty(&ta, &tb);
    let (s, p, x, xp) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    let eq_xx = eq_obj(&tb, Expr::fvar(x), Expr::fvar(xp));
    let inr = Expr::app(sum_inr(&ta, &tb), Expr::fvar(xp));
    let eq_s = eq_obj(&sum_ty, Expr::fvar(s), inr);
    let pred = Expr::lam(
        BinderInfo::Default,
        tb.clone(),
        conj(eq_xx, eq_s).abstract_fvar(xp),
    );
    let inner = ex_encoding(&tb, &pred);
    let body = lfp_unary(lfp, &carrier, &tb, x, p, inner);
    b.finish(&[(s, sum_ty)], body, cset(&tb))
}

/// `setl s = Collect (λx. setlp s x)` — `Collect` is identity under the predicate
/// model, so `setl s = λx. setlp s x`. References the `setlp` def-const and
/// forwards the SAME `lfp` slot `setlp` re-embeds at the use-site. Slot: [lfp@(α set)].
fn build_setl(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let carrier = cset(&ta);
    let lfp = b.opaque(lfp_clean_ty(&carrier));
    let sum_ty = csum_ty(&ta, &tb);
    let (s, x) = (b.fresh(), b.fresh());
    let setlp_app = Expr::apps(
        Expr::const_str("isabelle.def.Basic_BNFs.setlp"),
        [ta.clone(), tb.clone(), lfp, Expr::fvar(s), Expr::fvar(x)],
    );
    let body = Expr::lam(BinderInfo::Default, ta.clone(), setlp_app.abstract_fvar(x));
    b.finish(&[(s, sum_ty)], body, cset(&ta))
}

/// `setr s = Collect (λx. setrp s x)` = `λx. setrp s x`. Slot: [lfp@(β set)].
fn build_setr(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let carrier = cset(&tb);
    let lfp = b.opaque(lfp_clean_ty(&carrier));
    let sum_ty = csum_ty(&ta, &tb);
    let (s, x) = (b.fresh(), b.fresh());
    let setrp_app = Expr::apps(
        Expr::const_str("isabelle.def.Basic_BNFs.setrp"),
        [ta.clone(), tb.clone(), lfp, Expr::fvar(s), Expr::fvar(x)],
    );
    let body = Expr::lam(BinderInfo::Default, tb.clone(), setrp_app.abstract_fvar(x));
    b.finish(&[(s, sum_ty)], body, cset(&tb))
}

/// `fstsp p = lfp (λpa x. x = fst p)`. Slots: [lfp@(α set), fst@(α×β→α)].
fn build_fstsp(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let carrier = cset(&ta);
    let lfp = b.opaque(lfp_clean_ty(&carrier));
    let prod_ty = cprod_ty(&ta, &tb);
    let fst = b.opaque(Expr::arrow(prod_ty.clone(), ta.clone()));
    let (p, pa, x) = (b.fresh(), b.fresh(), b.fresh());
    let inner = eq_obj(&ta, Expr::fvar(x), Expr::app(fst, Expr::fvar(p)));
    let body = lfp_unary(lfp, &carrier, &ta, x, pa, inner);
    b.finish(&[(p, prod_ty)], body, cset(&ta))
}

/// `sndsp p = lfp (λpa x. x = snd p)`. Slots: [lfp@(β set), snd@(α×β→β)].
fn build_sndsp(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let carrier = cset(&tb);
    let lfp = b.opaque(lfp_clean_ty(&carrier));
    let prod_ty = cprod_ty(&ta, &tb);
    let snd = b.opaque(Expr::arrow(prod_ty.clone(), tb.clone()));
    let (p, pa, x) = (b.fresh(), b.fresh(), b.fresh());
    let inner = eq_obj(&tb, Expr::fvar(x), Expr::app(snd, Expr::fvar(p)));
    let body = lfp_unary(lfp, &carrier, &tb, x, pa, inner);
    b.finish(&[(p, prod_ty)], body, cset(&tb))
}

/// `pred_prod P1 P2 = lfp (λp x. ∃a b. x = (a,b) ∧ P1 a ∧ P2 b)`.
/// Slot: [lfp@((α×β) set)].
fn build_pred_prod(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let prod_ty = cprod_ty(&ta, &tb);
    let carrier = cset(&prod_ty);
    let lfp = b.opaque(lfp_clean_ty(&carrier));
    let (pa, pb, p, x, a1, b1) = (
        b.fresh(),
        b.fresh(),
        b.fresh(),
        b.fresh(),
        b.fresh(),
        b.fresh(),
    );
    let pair = prod_mk(&ta, &tb, Expr::fvar(a1), Expr::fvar(b1));
    let eqx = eq_obj(&prod_ty, Expr::fvar(x), pair);
    let p1a = Expr::app(Expr::fvar(pa), Expr::fvar(a1));
    let p2b = Expr::app(Expr::fvar(pb), Expr::fvar(b1));
    let inner_body = conj(eqx, conj(p1a, p2b));
    let pred_b = Expr::lam(
        BinderInfo::Default,
        tb.clone(),
        inner_body.abstract_fvar(b1),
    );
    let ex_b = ex_encoding(&tb, &pred_b);
    let pred_a = Expr::lam(BinderInfo::Default, ta.clone(), ex_b.abstract_fvar(a1));
    let inner = ex_encoding(&ta, &pred_a);
    let body = lfp_unary(lfp, &carrier, &prod_ty, x, p, inner);
    let pa_ty = Expr::arrow(ta.clone(), Expr::prop());
    let pb_ty = Expr::arrow(tb.clone(), Expr::prop());
    b.finish(&[(pa, pa_ty), (pb, pb_ty)], body, carrier)
}

/// `pred_sum P1 P2 = lfp (λp x. (∃a. x = Inl a ∧ P1 a) ∨ (∃b. x = Inr b ∧ P2 b))`.
/// Slot: [lfp@((α+β) set)].
fn build_pred_sum(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let sum_ty = csum_ty(&ta, &tb);
    let carrier = cset(&sum_ty);
    let lfp = b.opaque(lfp_clean_ty(&carrier));
    let (pa, pb, p, x, a1, b1) = (
        b.fresh(),
        b.fresh(),
        b.fresh(),
        b.fresh(),
        b.fresh(),
        b.fresh(),
    );
    // disjunct 1: ∃a. x = Inl a ∧ P1 a
    let inl = Expr::app(sum_inl(&ta, &tb), Expr::fvar(a1));
    let eq1 = eq_obj(&sum_ty, Expr::fvar(x), inl);
    let inner1 = conj(eq1, Expr::app(Expr::fvar(pa), Expr::fvar(a1)));
    let pred_a = Expr::lam(BinderInfo::Default, ta.clone(), inner1.abstract_fvar(a1));
    let ex_a = ex_encoding(&ta, &pred_a);
    // disjunct 2: ∃b. x = Inr b ∧ P2 b
    let inr = Expr::app(sum_inr(&ta, &tb), Expr::fvar(b1));
    let eq2 = eq_obj(&sum_ty, Expr::fvar(x), inr);
    let inner2 = conj(eq2, Expr::app(Expr::fvar(pb), Expr::fvar(b1)));
    let pred_b = Expr::lam(BinderInfo::Default, tb.clone(), inner2.abstract_fvar(b1));
    let ex_b = ex_encoding(&tb, &pred_b);
    let inner = disj(ex_a, ex_b);
    let body = lfp_unary(lfp, &carrier, &sum_ty, x, p, inner);
    let pa_ty = Expr::arrow(ta.clone(), Expr::prop());
    let pb_ty = Expr::arrow(tb.clone(), Expr::prop());
    b.finish(&[(pa, pa_ty), (pb, pb_ty)], body, carrier)
}

/// The lfp-generated **binary** relator functional wrapper:
/// `lfp (λp:rt. λx1:t1. λx2:t2. inner)` with `p` the unused recursion binder.
fn lfp_binary(
    lfp: Expr,
    rt: &Expr,
    t1: &Expr,
    t2: &Expr,
    x1: FVarId,
    x2: FVarId,
    p: FVarId,
    inner: Expr,
) -> Expr {
    let lam_x2 = Expr::lam(BinderInfo::Default, t2.clone(), inner.abstract_fvar(x2));
    let lam_x1 = Expr::lam(BinderInfo::Default, t1.clone(), lam_x2.abstract_fvar(x1));
    let func = Expr::lam(BinderInfo::Default, rt.clone(), lam_x1.abstract_fvar(p));
    Expr::app(lfp, func)
}

/// `rel_prod R1 R2 = lfp (λp x1 x2. ∃a b c d. x1=(a,c) ∧ x2=(b,d) ∧ R1 a b ∧ R2 c d)`.
/// Slot: [lfp@((α×γ)→(β×δ)→bool)].
fn build_rel_prod(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb, tc, td) = (b.t("'a"), b.t("'b"), b.t("'c"), b.t("'d"));
    let prod_ac = cprod_ty(&ta, &tc);
    let prod_bd = cprod_ty(&tb, &td);
    let rt = Expr::arrow(prod_ac.clone(), Expr::arrow(prod_bd.clone(), Expr::prop()));
    let lfp = b.opaque(lfp_clean_ty(&rt));
    let (r1, r2, p, x1, x2) = (b.fresh(), b.fresh(), b.fresh(), b.fresh(), b.fresh());
    let (a1, b1, c1, d1) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    let pair_ac = prod_mk(&ta, &tc, Expr::fvar(a1), Expr::fvar(c1));
    let pair_bd = prod_mk(&tb, &td, Expr::fvar(b1), Expr::fvar(d1));
    let eq1 = eq_obj(&prod_ac, Expr::fvar(x1), pair_ac);
    let eq2 = eq_obj(&prod_bd, Expr::fvar(x2), pair_bd);
    let r1app = Expr::apps(Expr::fvar(r1), [Expr::fvar(a1), Expr::fvar(b1)]);
    let r2app = Expr::apps(Expr::fvar(r2), [Expr::fvar(c1), Expr::fvar(d1)]);
    let inner_body = conj(eq1, conj(eq2, conj(r1app, r2app)));
    // ∃a ∃b ∃c ∃d  (a outermost … d innermost)
    let pred_d = Expr::lam(
        BinderInfo::Default,
        td.clone(),
        inner_body.abstract_fvar(d1),
    );
    let ex_d = ex_encoding(&td, &pred_d);
    let pred_c = Expr::lam(BinderInfo::Default, tc.clone(), ex_d.abstract_fvar(c1));
    let ex_c = ex_encoding(&tc, &pred_c);
    let pred_b = Expr::lam(BinderInfo::Default, tb.clone(), ex_c.abstract_fvar(b1));
    let ex_b = ex_encoding(&tb, &pred_b);
    let pred_a = Expr::lam(BinderInfo::Default, ta.clone(), ex_b.abstract_fvar(a1));
    let inner = ex_encoding(&ta, &pred_a);
    let body = lfp_binary(lfp, &rt, &prod_ac, &prod_bd, x1, x2, p, inner);
    let r1_ty = Expr::arrow(ta.clone(), Expr::arrow(tb.clone(), Expr::prop()));
    let r2_ty = Expr::arrow(tc.clone(), Expr::arrow(td.clone(), Expr::prop()));
    b.finish(&[(r1, r1_ty), (r2, r2_ty)], body, rt)
}

/// `rel_sum R1 R2 = lfp (λp x1 x2.
///     (∃a c. x1=Inl a ∧ x2=Inl c ∧ R1 a c) ∨ (∃b d. x1=Inr b ∧ x2=Inr d ∧ R2 b d))`.
/// Slot: [lfp@((α+γ)→(β+δ)→bool)]. The two `Inl`/`Inr` occurrences per disjunct
/// are at DISTINCT type instantiations, but each embeds to a real type-parameterised
/// `@Sum.inl/inr α γ` (resp. `β δ`) constant — no name-only aliasing.
fn build_rel_sum(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb, tc, td) = (b.t("'a"), b.t("'b"), b.t("'c"), b.t("'d"));
    let sum_ac = csum_ty(&ta, &tc);
    let sum_bd = csum_ty(&tb, &td);
    let rt = Expr::arrow(sum_ac.clone(), Expr::arrow(sum_bd.clone(), Expr::prop()));
    let lfp = b.opaque(lfp_clean_ty(&rt));
    let (r1, r2, p, x1, x2) = (b.fresh(), b.fresh(), b.fresh(), b.fresh(), b.fresh());
    // disjunct 1: ∃a:α c:β. x1 = Inl a ∧ (x2 = Inl c ∧ R1 a c)
    let (a1, e1) = (b.fresh(), b.fresh());
    let inl_ac = Expr::app(sum_inl(&ta, &tc), Expr::fvar(a1));
    let inl_bd = Expr::app(sum_inl(&tb, &td), Expr::fvar(e1));
    let eq1 = eq_obj(&sum_ac, Expr::fvar(x1), inl_ac);
    let eq2 = eq_obj(&sum_bd, Expr::fvar(x2), inl_bd);
    let r1app = Expr::apps(Expr::fvar(r1), [Expr::fvar(a1), Expr::fvar(e1)]);
    let inner1 = conj(eq1, conj(eq2, r1app));
    let pred_e1 = Expr::lam(BinderInfo::Default, tb.clone(), inner1.abstract_fvar(e1));
    let ex_e1 = ex_encoding(&tb, &pred_e1);
    let pred_a1 = Expr::lam(BinderInfo::Default, ta.clone(), ex_e1.abstract_fvar(a1));
    let ex_a1 = ex_encoding(&ta, &pred_a1);
    // disjunct 2: ∃b:γ d:δ. x1 = Inr b ∧ (x2 = Inr d ∧ R2 b d)
    let (g1, d1) = (b.fresh(), b.fresh());
    let inr_ac = Expr::app(sum_inr(&ta, &tc), Expr::fvar(g1));
    let inr_bd = Expr::app(sum_inr(&tb, &td), Expr::fvar(d1));
    let eq3 = eq_obj(&sum_ac, Expr::fvar(x1), inr_ac);
    let eq4 = eq_obj(&sum_bd, Expr::fvar(x2), inr_bd);
    let r2app = Expr::apps(Expr::fvar(r2), [Expr::fvar(g1), Expr::fvar(d1)]);
    let inner2 = conj(eq3, conj(eq4, r2app));
    let pred_d1 = Expr::lam(BinderInfo::Default, td.clone(), inner2.abstract_fvar(d1));
    let ex_d1 = ex_encoding(&td, &pred_d1);
    let pred_g1 = Expr::lam(BinderInfo::Default, tc.clone(), ex_d1.abstract_fvar(g1));
    let ex_g1 = ex_encoding(&tc, &pred_g1);
    let inner = disj(ex_a1, ex_g1);
    let body = lfp_binary(lfp, &rt, &sum_ac, &sum_bd, x1, x2, p, inner);
    let r1_ty = Expr::arrow(ta.clone(), Expr::arrow(tb.clone(), Expr::prop()));
    let r2_ty = Expr::arrow(tc.clone(), Expr::arrow(td.clone(), Expr::prop()));
    b.finish(&[(r1, r1_ty), (r2, r2_ty)], body, rt)
}

/// `collect F x = Sup (image (λf. f x) F)`. `Sup` is the SET-instance complete-
/// lattice `Sup` (`(β set) set ⇒ β set`), which embeds to the compositional
/// `lattice_set_encoding`; supplied opaquely and applied to the faithful
/// `image_encoding`. Slot: [Sup@((β set) set → β set)].
fn build_collect(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let set_b = cset(&tb); // β set
    let fprime = Expr::arrow(ta.clone(), set_b.clone()); // α → β set  (image function type)
    let sup_ty = Expr::arrow(cset(&set_b), set_b.clone()); // (β set) set → β set
    let sup = b.opaque(sup_ty);
    let big_f_ty = cset(&fprime); // (α → β set) set
    let (big_f, x, f) = (b.fresh(), b.fresh(), b.fresh());
    // probe: λf:(α→β set). f x   : β set
    let fx = Expr::app(Expr::fvar(f), Expr::fvar(x));
    let probe = Expr::lam(BinderInfo::Default, fprime.clone(), fx.abstract_fvar(f));
    let img = Expr::apps(image_encoding(&fprime, &set_b), [probe, Expr::fvar(big_f)]);
    let body = Expr::app(sup, img);
    b.finish(&[(big_f, big_f_ty), (x, ta)], body, set_b)
}

/// `Above r A = {b. b ∈ Field r ∧ (∀a∈A. (a,b) ∈ r)}` (the upper bounds of `A`),
/// i.e. under the `set = predicate` model `λb. (Field r) b ∧ Ball A (λa. r (a,b))`.
/// Slots: [field@α] (`Relation.Field : (α×α)set → αset`). The `Set.Collect` is
/// stripped (identity), `member x S` = `S x`; the exported membership is
/// `member (Pair a b) r` (Ball binder `a` FIRST, `Collect` binder `b` second).
fn build_above(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let a = b.t("'a");
    let field = b.opaque(Expr::arrow(crel(&a), cset(&a)));
    let (r, aset, bb, x) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    // b ∈ Field r  ==  (field r) b
    let mem_field = Expr::app(Expr::app(field, Expr::fvar(r)), Expr::fvar(bb));
    // Ball A (λa. r (a,b))
    let pair = prod_mk(&a, &a, Expr::fvar(x), Expr::fvar(bb));
    let mem_r = Expr::app(Expr::fvar(r), pair);
    let pred = Expr::lam(BinderInfo::Default, a.clone(), mem_r.abstract_fvar(x));
    let ball = Expr::apps(ball_encoding(&a), [Expr::fvar(aset), pred]);
    let inner = conj(mem_field, ball);
    let body = Expr::lam(BinderInfo::Default, a.clone(), inner.abstract_fvar(bb));
    b.finish(&[(r, crel(&a)), (aset, cset(&a))], body, cset(&a))
}

/// `AboveS r A = {b. b ∈ Field r ∧ (∀a∈A. b ≠ a ∧ (a,b) ∈ r)}` (the strict upper
/// bounds), i.e. `λb. (Field r) b ∧ Ball A (λa. ¬(b=a) ∧ r (a,b))`. Slots: [field@α].
/// The exported inequality is `¬(b = a)` and the membership `member (Pair a b) r`.
fn build_aboves(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let a = b.t("'a");
    let field = b.opaque(Expr::arrow(crel(&a), cset(&a)));
    let (r, aset, bb, x) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    let mem_field = Expr::app(Expr::app(field, Expr::fvar(r)), Expr::fvar(bb));
    // λa. ¬(b=a) ∧ r (a,b)
    let neq = not_(eq_obj(&a, Expr::fvar(bb), Expr::fvar(x)));
    let pair = prod_mk(&a, &a, Expr::fvar(x), Expr::fvar(bb));
    let mem_r = Expr::app(Expr::fvar(r), pair);
    let pred_body = conj(neq, mem_r);
    let pred = Expr::lam(BinderInfo::Default, a.clone(), pred_body.abstract_fvar(x));
    let ball = Expr::apps(ball_encoding(&a), [Expr::fvar(aset), pred]);
    let inner = conj(mem_field, ball);
    let body = Expr::lam(BinderInfo::Default, a.clone(), inner.abstract_fvar(bb));
    b.finish(&[(r, crel(&a)), (aset, cset(&a))], body, cset(&a))
}

// --- Round-15 wellorder embedding cluster ---

/// `embed r r' f = Ball (Field r) (λa. bij_betw f (under r a) (under r' (f a)))`
/// (`f` is an order-embedding of `r` into `r'`). Slot: [field@α]. `under` (at `α`
/// and `β`) and `bij_betw` (at `(α,β)`) are referenced through their registered
/// def-consts directly, so each byte-matches the corresponding RHS sub-term.
fn build_embed(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let field = b.opaque(Expr::arrow(crel(&ta), cset(&ta))); // Field@α
    let (r, rp, f, a) = (b.fresh(), b.fresh(), b.fresh(), b.fresh());
    // under r a : α set   (under@α)
    let under_ra = Expr::apps(
        Expr::const_str(UNDER_DEF),
        [ta.clone(), Expr::fvar(r), Expr::fvar(a)],
    );
    // under r' (f a) : β set   (under@β)
    let fa = Expr::app(Expr::fvar(f), Expr::fvar(a));
    let under_rpfa = Expr::apps(Expr::const_str(UNDER_DEF), [tb.clone(), Expr::fvar(rp), fa]);
    // bij_betw f (under r a) (under r' (f a)) : bool   (bij_betw@(α,β))
    let bij = Expr::apps(
        Expr::const_str(BIJ_BETW_DEF),
        [ta.clone(), tb.clone(), Expr::fvar(f), under_ra, under_rpfa],
    );
    // λa:α. bij   : α → bool
    let pred = Expr::lam(BinderInfo::Default, ta.clone(), bij.abstract_fvar(a));
    // Ball (Field r) (λa. …)
    let field_r = Expr::app(field, Expr::fvar(r));
    let body = Expr::apps(ball_encoding(&ta), [field_r, pred]);
    let f_ty = Expr::arrow(ta.clone(), tb.clone());
    b.finish(
        &[(r, crel(&ta)), (rp, crel(&tb)), (f, f_ty)],
        body,
        Expr::prop(),
    )
}

/// `ord_to_filter r0 r = image (Eps (λf. embed r r0 f)) (Field r)` — the image of
/// `Field r` under some order-embedding of `r` into `r0`. Slots: [eps@(α→α), field@α].
/// `embed` is at `(α,α)` (forwarding the same `field@α` slot). NB the exported
/// argument order is `ord_to_filter r0 r` but the embedding is `embed r r0 f`.
fn build_ord_to_filter(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let a = b.t("'a");
    let fun_aa = Expr::arrow(a.clone(), a.clone()); // α → α
                                                    // Eps : ((α→α)→bool) → (α→α)
    let eps = b.opaque(Expr::arrow(
        Expr::arrow(fun_aa.clone(), Expr::prop()),
        fun_aa.clone(),
    ));
    let field = b.opaque(Expr::arrow(crel(&a), cset(&a))); // Field@α
    let (r0, r, f) = (b.fresh(), b.fresh(), b.fresh());
    // embed r r0 f   (embed def-const at (α,α), forwarding field)
    let embed_app = Expr::apps(
        Expr::const_str(EMBED_DEF),
        [
            a.clone(),
            a.clone(),
            field.clone(),
            Expr::fvar(r),
            Expr::fvar(r0),
            Expr::fvar(f),
        ],
    );
    // λf:(α→α). embed r r0 f   : (α→α) → bool
    let pred = Expr::lam(
        BinderInfo::Default,
        fun_aa.clone(),
        embed_app.abstract_fvar(f),
    );
    // Eps (λf. …) : α → α
    let chosen = Expr::app(eps, pred);
    // Field r : α set
    let field_r = Expr::app(field, Expr::fvar(r));
    // image (Eps …) (Field r) : α set
    let body = Expr::apps(image_encoding(&a, &a), [chosen, field_r]);
    b.finish(&[(r0, crel(&a)), (r, crel(&a))], body, cset(&a))
}

// --- Round-17 cardinal family (card_of / cardSuc + two-Field arithmetic) ---

/// The `card_of` def-const applied to its instance type `t`, its two forwarded
/// opaque slots (`eps@t`, `card_order_on@t`) and the set argument `arg` (of clean
/// type `t set`). δβ-reduces to `Eps (λr:(t×t)set. card_order_on arg r)` — exactly
/// what a bare `card_of arg` occurrence embeds to.
fn card_of_app(t: &Expr, eps: &Expr, cardord: &Expr, arg: Expr) -> Expr {
    Expr::apps(
        Expr::const_str(CARD_OF_DEF),
        [t.clone(), eps.clone(), cardord.clone(), arg],
    )
}

/// `card_of A = Eps (λr:(α×α)set. card_order_on A r)`. Slots: [eps@α, card_order_on@α].
fn build_card_of(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let a = b.t("'a");
    let rel_a = crel(&a); // (α×α)set
    let eps = b.opaque(Expr::arrow(
        Expr::arrow(rel_a.clone(), Expr::prop()),
        rel_a.clone(),
    ));
    let cardord = b.opaque(Expr::arrow(
        cset(&a),
        Expr::arrow(rel_a.clone(), Expr::prop()),
    ));
    let (aset, r) = (b.fresh(), b.fresh());
    let app_ = Expr::apps(cardord, [Expr::fvar(aset), Expr::fvar(r)]);
    let pred = Expr::lam(BinderInfo::Default, rel_a.clone(), app_.abstract_fvar(r));
    let body = Expr::app(eps, pred);
    b.finish(&[(aset, cset(&a))], body, rel_a)
}

/// `cardSuc r = Eps (λr':((α set × α set))set. isCardSuc r r')`.
/// Slots: [eps@(α set), isCardSuc@α]. The chosen `r'` is a relation on `α set`.
fn build_cardsuc(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let a = b.t("'a");
    let rel_a = crel(&a); // (α×α)set
    let rel_setalpha = crel(&cset(&a)); // ((α set × α set))set
    let eps = b.opaque(Expr::arrow(
        Expr::arrow(rel_setalpha.clone(), Expr::prop()),
        rel_setalpha.clone(),
    ));
    let iscardsuc = b.opaque(Expr::arrow(
        rel_a.clone(),
        Expr::arrow(rel_setalpha.clone(), Expr::prop()),
    ));
    let (r, rp) = (b.fresh(), b.fresh());
    let app_ = Expr::apps(iscardsuc, [Expr::fvar(r), Expr::fvar(rp)]);
    let pred = Expr::lam(
        BinderInfo::Default,
        rel_setalpha.clone(),
        app_.abstract_fvar(rp),
    );
    let body = Expr::app(eps, pred);
    b.finish(&[(r, rel_a)], body, rel_setalpha)
}

/// `csum r1 r2 = card_of (Plus (Field r1) (Field r2))`.
/// Slots: [eps@(α+β), card_order_on@(α+β), Plus@(α,β), Field@α, Field@β].
fn build_csum(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let sum_t = csum_ty(&ta, &tb); // α+β
    let rel_sum = crel(&sum_t); // ((α+β)×(α+β))set
    let eps = b.opaque(Expr::arrow(
        Expr::arrow(rel_sum.clone(), Expr::prop()),
        rel_sum.clone(),
    ));
    let cardord = b.opaque(Expr::arrow(
        cset(&sum_t),
        Expr::arrow(rel_sum.clone(), Expr::prop()),
    ));
    // Plus : α set → β set → (α+β)set
    let plus = b.opaque(Expr::arrow(cset(&ta), Expr::arrow(cset(&tb), cset(&sum_t))));
    let field_a = b.opaque(Expr::arrow(crel(&ta), cset(&ta))); // Field@α
    let field_b = b.opaque(Expr::arrow(crel(&tb), cset(&tb))); // Field@β
    let (r1, r2) = (b.fresh(), b.fresh());
    let fld1 = Expr::app(field_a, Expr::fvar(r1));
    let fld2 = Expr::app(field_b, Expr::fvar(r2));
    let plus_app = Expr::apps(plus, [fld1, fld2]);
    let body = card_of_app(&sum_t, &eps, &cardord, plus_app);
    b.finish(&[(r1, crel(&ta)), (r2, crel(&tb))], body, rel_sum)
}

/// `cprod r1 r2 = card_of (Sigma (Field r1) (λ_:α. Field r2))`.
/// Slots: [eps@(α×β), card_order_on@(α×β), Sigma@(α,β), Field@α, Field@β].
fn build_cprod(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let prod_t = cprod_ty(&ta, &tb); // α×β
    let rel_prod = crel(&prod_t); // ((α×β)×(α×β))set
    let eps = b.opaque(Expr::arrow(
        Expr::arrow(rel_prod.clone(), Expr::prop()),
        rel_prod.clone(),
    ));
    let cardord = b.opaque(Expr::arrow(
        cset(&prod_t),
        Expr::arrow(rel_prod.clone(), Expr::prop()),
    ));
    // Sigma : α set → (α → β set) → (α×β)set
    let sigma = b.opaque(Expr::arrow(
        cset(&ta),
        Expr::arrow(Expr::arrow(ta.clone(), cset(&tb)), cset(&prod_t)),
    ));
    let field_a = b.opaque(Expr::arrow(crel(&ta), cset(&ta))); // Field@α
    let field_b = b.opaque(Expr::arrow(crel(&tb), cset(&tb))); // Field@β
    let (r1, r2, uu) = (b.fresh(), b.fresh(), b.fresh());
    let fld1 = Expr::app(field_a, Expr::fvar(r1));
    let fld2 = Expr::app(field_b, Expr::fvar(r2)); // constant in uu
    let lam_uu = Expr::lam(BinderInfo::Default, ta.clone(), fld2.abstract_fvar(uu));
    let sigma_app = Expr::apps(sigma, [fld1, lam_uu]);
    let body = card_of_app(&prod_t, &eps, &cardord, sigma_app);
    b.finish(&[(r1, crel(&ta)), (r2, crel(&tb))], body, rel_prod)
}

/// `cexp r1 r2 = card_of (Func (Field r2) (Field r1))` (NB `r1` is the `'b`-relation,
/// `r2` the `'a`-relation, and the exponent is at `α⇒β`).
/// Slots: [eps@(α⇒β), card_order_on@(α⇒β), Func@(α,β), Field@α, Field@β].
fn build_cexp(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let fun_ab = Expr::arrow(ta.clone(), tb.clone()); // α⇒β
    let rel_fun = crel(&fun_ab); // ((α⇒β)×(α⇒β))set
    let eps = b.opaque(Expr::arrow(
        Expr::arrow(rel_fun.clone(), Expr::prop()),
        rel_fun.clone(),
    ));
    let cardord = b.opaque(Expr::arrow(
        cset(&fun_ab),
        Expr::arrow(rel_fun.clone(), Expr::prop()),
    ));
    // Func : α set → β set → (α⇒β)set
    let func = b.opaque(Expr::arrow(
        cset(&ta),
        Expr::arrow(cset(&tb), cset(&fun_ab)),
    ));
    let field_a = b.opaque(Expr::arrow(crel(&ta), cset(&ta))); // Field@α (from r2)
    let field_b = b.opaque(Expr::arrow(crel(&tb), cset(&tb))); // Field@β (from r1)
    let (r1, r2) = (b.fresh(), b.fresh());
    let fld_r2 = Expr::app(field_a, Expr::fvar(r2)); // Field r2 : α set
    let fld_r1 = Expr::app(field_b, Expr::fvar(r1)); // Field r1 : β set
    let func_app = Expr::apps(func, [fld_r2, fld_r1]);
    let body = card_of_app(&fun_ab, &eps, &cardord, func_app);
    // cexp : (β×β)set → (α×α)set → …
    b.finish(&[(r1, crel(&tb)), (r2, crel(&ta))], body, rel_fun)
}

/// `Csum r rs = card_of (Sigma (Field r) (λi:α. Field (rs i)))`.
/// Slots: [eps@(α×β), card_order_on@(α×β), Sigma@(α,β), Field@α, Field@β].
fn build_csum_dep(b: &mut OpaqueBuild) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let prod_t = cprod_ty(&ta, &tb); // α×β
    let rel_prod = crel(&prod_t);
    let eps = b.opaque(Expr::arrow(
        Expr::arrow(rel_prod.clone(), Expr::prop()),
        rel_prod.clone(),
    ));
    let cardord = b.opaque(Expr::arrow(
        cset(&prod_t),
        Expr::arrow(rel_prod.clone(), Expr::prop()),
    ));
    let sigma = b.opaque(Expr::arrow(
        cset(&ta),
        Expr::arrow(Expr::arrow(ta.clone(), cset(&tb)), cset(&prod_t)),
    ));
    let field_a = b.opaque(Expr::arrow(crel(&ta), cset(&ta))); // Field@α (from r)
    let field_b = b.opaque(Expr::arrow(crel(&tb), cset(&tb))); // Field@β (from rs i)
    let (r, rs, i) = (b.fresh(), b.fresh(), b.fresh());
    let fld_r = Expr::app(field_a, Expr::fvar(r)); // α set
    let rs_i = Expr::app(Expr::fvar(rs), Expr::fvar(i)); // (β×β)set
    let fld_rsi = Expr::app(field_b, rs_i); // β set
    let lam_i = Expr::lam(BinderInfo::Default, ta.clone(), fld_rsi.abstract_fvar(i));
    let sigma_app = Expr::apps(sigma, [fld_r, lam_i]);
    let body = card_of_app(&prod_t, &eps, &cardord, sigma_app);
    let rs_ty = Expr::arrow(ta.clone(), crel(&tb)); // α → (β×β)set
    b.finish(&[(r, crel(&ta)), (rs, rs_ty)], body, rel_prod)
}

/// `embedS r r' f = embed r r' f ∧ ¬ bij_betw f (Field r) (Field r')` (a STRICT
/// order-embedding — an embedding that is not onto) and, dually,
/// `iso r r' f = embed r r' f ∧ bij_betw f (Field r) (Field r')` (an order
/// isomorphism). `negate` selects `embedS` (`true`) vs `iso` (`false`).
///
/// Slots: **[field@α, field@β]** — `Relation.Field` at BOTH type instantiations
/// (`Field r` at `α` inside `bij_betw`'s first set-arg, `Field r'` at `β` inside
/// its second). This is the two-`Field` shape r13 §4 / r15 §4 diagnosed as the
/// recurring poly-inst inner-parameter collision: before the round-16 const-param
/// type-suffix keying (`const_param_key`), the `sup`/`Domain`/`Range` ops woven
/// inside `polyinst.Field@α` and `polyinst.Field@β` aliased onto ONE ill-typed
/// param and the re-embedded `Field@α`/`Field@β` pair kernel-rejected. With the
/// keying fix each instantiation's inner ops get DISTINCT params, so the two
/// `Field` slots embed to well-typed distinct poly-inst terms and the equation is
/// reflexive. `embed r r' f` is the round-15 `embed` def-const at `(α,β)`
/// forwarding the SAME `field@α` slot; `bij_betw` is `Fun.bij_betw` at `(α,β)`.
fn build_embed_bij(b: &mut OpaqueBuild, negate: bool) -> (Expr, Expr) {
    let (ta, tb) = (b.t("'a"), b.t("'b"));
    let field_a = b.opaque(Expr::arrow(crel(&ta), cset(&ta))); // Field@α
    let field_b = b.opaque(Expr::arrow(crel(&tb), cset(&tb))); // Field@β
    let (r, rp, f) = (b.fresh(), b.fresh(), b.fresh());
    // embed r r' f : bool — the `embed` def-const at (α,β), forwarding field@α.
    let embed_app = Expr::apps(
        Expr::const_str(EMBED_DEF),
        [
            ta.clone(),
            tb.clone(),
            field_a.clone(),
            Expr::fvar(r),
            Expr::fvar(rp),
            Expr::fvar(f),
        ],
    );
    // bij_betw f (Field r) (Field r') : bool — bij_betw@(α,β) on the two Field sets.
    let field_r = Expr::app(field_a, Expr::fvar(r)); // Field@α r  : α set
    let field_rp = Expr::app(field_b, Expr::fvar(rp)); // Field@β r' : β set
    let bij_app = Expr::apps(
        Expr::const_str(BIJ_BETW_DEF),
        [ta.clone(), tb.clone(), Expr::fvar(f), field_r, field_rp],
    );
    let second = if negate { not_(bij_app) } else { bij_app };
    let body = conj(embed_app, second);
    let f_ty = Expr::arrow(ta.clone(), tb.clone());
    b.finish(
        &[(r, crel(&ta)), (rp, crel(&tb)), (f, f_ty)],
        body,
        Expr::prop(),
    )
}

fn build_embeds(b: &mut OpaqueBuild) -> (Expr, Expr) {
    build_embed_bij(b, true)
}

fn build_iso(b: &mut OpaqueBuild) -> (Expr, Expr) {
    build_embed_bij(b, false)
}

type OpaqueBuilder = fn(&mut OpaqueBuild) -> (Expr, Expr);
/// Every opaque-arg BNF combinator, with its dedicated fvar-id base and builder.
/// **`pick_middlep` MUST precede `fstOp`/`sndOp`** (their def-const values
/// reference `isabelle.def.BNF_Def.pick_middlep`, so it must be `add_decl`'d
/// first).
const BNF_OPAQUE_CONSTANTS: [(&str, u64, OpaqueBuilder); 29] = [
    (
        "BNF_Cardinal_Arithmetic.cinfinite",
        0x1C00_0000,
        build_cinfinite,
    ),
    (
        "BNF_Cardinal_Arithmetic.cfinite",
        0x1C01_0000,
        build_cfinite,
    ),
    ("BNF_Def.pick_middlep", 0x1C06_0000, build_pick_middlep),
    ("BNF_Def.fstOp", 0x1C07_0000, build_fstop),
    ("BNF_Def.sndOp", 0x1C08_0000, build_sndop),
    // Round-14: predicators / relators / set-functions / collect. **`setlp`/`setrp`
    // MUST precede `setl`/`setr`** (whose def-const values reference them).
    ("Basic_BNFs.pred_fun", 0x1C10_0000, build_pred_fun),
    ("Basic_BNFs.pred_prod", 0x1C11_0000, build_pred_prod),
    ("Basic_BNFs.pred_sum", 0x1C12_0000, build_pred_sum),
    ("Basic_BNFs.rel_prod", 0x1C13_0000, build_rel_prod),
    ("BNF_Def.rel_sum", 0x1C14_0000, build_rel_sum),
    ("Basic_BNFs.fstsp", 0x1C15_0000, build_fstsp),
    ("Basic_BNFs.sndsp", 0x1C16_0000, build_sndsp),
    ("Basic_BNFs.setlp", 0x1C17_0000, build_setlp),
    ("Basic_BNFs.setrp", 0x1C18_0000, build_setrp),
    ("Basic_BNFs.setl", 0x1C19_0000, build_setl),
    ("Basic_BNFs.setr", 0x1C1A_0000, build_setr),
    ("BNF_Def.collect", 0x1C1B_0000, build_collect),
    ("Order_Relation.Above", 0x1C09_0000, build_above),
    ("Order_Relation.AboveS", 0x1C0A_0000, build_aboves),
    // Round-15/16 embedding cluster. **`embed` MUST precede `ord_to_filter`,
    // `embedS`, and `iso`** (their def-const values reference
    // `isabelle.def.BNF_Wellorder_Embedding.embed`).
    ("BNF_Wellorder_Embedding.embed", 0x1C1C_0000, build_embed),
    // Round-16: strict-embedding / isomorphism (two-`Field`, unblocked by the
    // `const_param` type-suffix keying).
    ("BNF_Wellorder_Embedding.embedS", 0x1C1D_0000, build_embeds),
    ("BNF_Wellorder_Embedding.iso", 0x1C1E_0000, build_iso),
    (
        "BNF_Wellorder_Constructions.ord_to_filter",
        0x1C1F_0000,
        build_ord_to_filter,
    ),
    // Round-17 cardinal family. **`card_of` MUST precede `csum`/`cprod`/`cexp`/
    // `Csum`** (their def-const values reference
    // `isabelle.def.BNF_Cardinal_Order_Relation.card_of`).
    (
        "BNF_Cardinal_Order_Relation.card_of",
        0x1C20_0000,
        build_card_of,
    ),
    (
        "BNF_Cardinal_Order_Relation.cardSuc",
        0x1C21_0000,
        build_cardsuc,
    ),
    ("BNF_Cardinal_Arithmetic.csum", 0x1C22_0000, build_csum),
    ("BNF_Cardinal_Arithmetic.cprod", 0x1C23_0000, build_cprod),
    ("BNF_Cardinal_Arithmetic.cexp", 0x1C24_0000, build_cexp),
    ("BNF_Cardinal_Arithmetic.Csum", 0x1C25_0000, build_csum_dep),
];

/// The opaque-arg BNF combinator constants as clean [`Declaration::Definition`]s,
/// in dependency order (`pick_middlep` before `fstOp`/`sndOp`). Registered into
/// the verifier's accumulating environment AFTER the connective def-consts
/// (`HOL.conj`/`HOL.Not`) their bodies depend on. Non-fatal on registration
/// failure: the constant's nodes simply stay unmapped.
#[must_use]
pub(crate) fn bnf_opaque_combinator_definition_decls() -> Vec<Declaration> {
    BNF_OPAQUE_CONSTANTS
        .iter()
        .filter_map(|(name, base, build)| {
            let schematic = bnf_opaque_schematic(name)?;
            let mut b = OpaqueBuild::new(&schematic, *base)?;
            let (value, type_) = build(&mut b);
            bnf_opaque_def_const_name(name).map(|def| Declaration::Definition {
                name: Name::from_string(def),
                level_params: Vec::new(),
                type_,
                value,
                is_reducible: true,
            })
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Use-site embedding
// ---------------------------------------------------------------------------

/// The ordered opaque-const supply for a combinator: `(hol_const_name,
/// hol_type_at_instantiation)`, in the SAME order the builder allocated its
/// [`OpaqueBuild::opaque`] slots. `sub` looks up a solved tvar. Each entry is
/// re-embedded through the ordinary `Const` dispatch, so it byte-matches the
/// bare occurrence in the RHS.
fn opaque_supply(name: &str, sub: &dyn Fn(&str) -> IsaType) -> Vec<(&'static str, IsaType)> {
    let (a, b, c, d) = (sub("'a"), sub("'b"), sub("'c"), sub("'d"));
    let rel = |x: IsaType| hset(hprod(x.clone(), x));
    let field = |x: IsaType| ("Relation.Field", hfun(rel(x.clone()), hset(x)));
    let finite = |x: IsaType| ("Finite_Set.finite", hfun(hset(x), hbool()));
    // `Inductive.complete_lattice_class.lfp` at the complete lattice whose carrier
    // HOL type is `carrier` (an opaque overloaded class method, re-embedded).
    let lfp = |carrier: IsaType| ("Inductive.complete_lattice_class.lfp", lfp_hol_ty(carrier));
    // The two `card_of`-forwarded opaque slots at instance `t`: the Hilbert `Eps`
    // over `(t×t)set` predicates and the `card_order_on : t set → (t×t)set → bool`.
    let eps_rel = |t: IsaType| {
        (
            "Hilbert_Choice.Eps",
            hfun(hfun(rel(t.clone()), hbool()), rel(t)),
        )
    };
    let card_order_on = |t: IsaType| {
        (
            "BNF_Cardinal_Order_Relation.card_order_on",
            hfun(hset(t.clone()), hfun(rel(t), hbool())),
        )
    };
    match name {
        "BNF_Cardinal_Arithmetic.cinfinite" | "BNF_Cardinal_Arithmetic.cfinite" => {
            vec![field(a.clone()), finite(a)]
        }
        "BNF_Def.pick_middlep" => {
            // Eps : (β → bool) → β
            vec![("Hilbert_Choice.Eps", hfun(hfun(b.clone(), hbool()), b))]
        }
        "BNF_Def.fstOp" | "BNF_Def.sndOp" => {
            let ac = hprod(a.clone(), c.clone());
            vec![
                ("Hilbert_Choice.Eps", hfun(hfun(b.clone(), hbool()), b)),
                ("Product_Type.prod.fst", hfun(ac.clone(), a)),
                ("Product_Type.prod.snd", hfun(ac, c)),
            ]
        }
        // Round-14. `lfp` at the single lattice instance each body uses.
        "Basic_BNFs.pred_fun" => Vec::new(),
        "Basic_BNFs.pred_prod" => vec![lfp(hfun(hprod(a, b), hbool()))],
        "Basic_BNFs.pred_sum" => vec![lfp(hfun(hsum(a, b), hbool()))],
        "Basic_BNFs.rel_prod" => {
            vec![lfp(hfun(hprod(a, c), hfun(hprod(b, d), hbool())))]
        }
        "BNF_Def.rel_sum" => {
            vec![lfp(hfun(hsum(a, c), hfun(hsum(b, d), hbool())))]
        }
        "Basic_BNFs.fstsp" => vec![
            lfp(hfun(a.clone(), hbool())),
            ("Product_Type.prod.fst", hfun(hprod(a.clone(), b), a)),
        ],
        "Basic_BNFs.sndsp" => vec![
            lfp(hfun(b.clone(), hbool())),
            ("Product_Type.prod.snd", hfun(hprod(a, b.clone()), b)),
        ],
        "Basic_BNFs.setlp" | "Basic_BNFs.setl" => vec![lfp(hfun(a, hbool()))],
        "Basic_BNFs.setrp" | "Basic_BNFs.setr" => vec![lfp(hfun(b, hbool()))],
        "BNF_Def.collect" => {
            // Sup at the set instance `(β set) set ⇒ β set`.
            vec![(
                "Complete_Lattices.Sup_class.Sup",
                hfun(hset(hset(b.clone())), hset(b)),
            )]
        }
        // `Relation.Field : (α×α)set → αset` — a SINGLE instantiation at `α`.
        "Order_Relation.Above" | "Order_Relation.AboveS" => {
            vec![field(a)]
        }
        // Round-15. `embed` carries a single `Field@α` (the `Ball (Field r) …` domain).
        "BNF_Wellorder_Embedding.embed" => vec![field(a)],
        // Round-16. `embedS`/`iso` carry TWO `Field` slots — `Field@α` (`Field r`,
        // shared with the forwarded `embed`) then `Field@β` (`Field r'`), in the
        // builder's `opaque` allocation order.
        "BNF_Wellorder_Embedding.embedS" | "BNF_Wellorder_Embedding.iso" => {
            vec![field(a), field(b)]
        }
        // `ord_to_filter` — `Eps : ((α→α)→bool)→(α→α)` (the chosen embedding) then a
        // single `Field@α` (the `image … (Field r)` domain).
        "BNF_Wellorder_Constructions.ord_to_filter" => {
            let fun_aa = hfun(a.clone(), a.clone());
            vec![
                (
                    "Hilbert_Choice.Eps",
                    hfun(hfun(fun_aa.clone(), hbool()), fun_aa),
                ),
                field(a),
            ]
        }
        // Round-17. `card_of`/`cardSuc` carry a single-instantiation `Eps` over the
        // opaque `card_order_on`/`isCardSuc` predicate.
        "BNF_Cardinal_Order_Relation.card_of" => {
            vec![eps_rel(a.clone()), card_order_on(a)]
        }
        "BNF_Cardinal_Order_Relation.cardSuc" => {
            // `Eps` over `((α set × α set))set` and `isCardSuc : (α×α)set →
            // ((α set × α set))set → bool`.
            let set_a = hset(a.clone());
            vec![
                eps_rel(set_a.clone()),
                (
                    "BNF_Cardinal_Order_Relation.isCardSuc",
                    hfun(rel(a), hfun(rel(set_a), hbool())),
                ),
            ]
        }
        // Round-17 cardinal arithmetic. Each forwards `card_of`'s two slots at the
        // combined instance, then the combiner (`Plus`/`Sigma`/`Func`), then the two
        // `Field` slots at `α` and `β`.
        "BNF_Cardinal_Arithmetic.csum" => {
            let sum = hsum(a.clone(), b.clone());
            vec![
                eps_rel(sum.clone()),
                card_order_on(sum.clone()),
                (
                    "Sum_Type.Plus",
                    hfun(hset(a.clone()), hfun(hset(b.clone()), hset(sum))),
                ),
                field(a),
                field(b),
            ]
        }
        "BNF_Cardinal_Arithmetic.cprod" | "BNF_Cardinal_Arithmetic.Csum" => {
            let prod = hprod(a.clone(), b.clone());
            vec![
                eps_rel(prod.clone()),
                card_order_on(prod.clone()),
                (
                    "Product_Type.Sigma",
                    hfun(
                        hset(a.clone()),
                        hfun(hfun(a.clone(), hset(b.clone())), hset(prod)),
                    ),
                ),
                field(a),
                field(b),
            ]
        }
        "BNF_Cardinal_Arithmetic.cexp" => {
            let fn_ab = hfun(a.clone(), b.clone());
            vec![
                eps_rel(fn_ab.clone()),
                card_order_on(fn_ab.clone()),
                (
                    "BNF_Wellorder_Constructions.Func",
                    hfun(hset(a.clone()), hfun(hset(b.clone()), hset(fn_ab))),
                ),
                field(a),
                field(b),
            ]
        }
        _ => Vec::new(),
    }
}

impl Ctx {
    /// Embed an occurrence of an **opaque-arg** BNF combinator constant to its
    /// registered def-const ([`bnf_opaque_def_const_name`]) applied to the
    /// use-site's solved object types AND the re-embedded opaque constants it
    /// abstracts. The object type parameters are solved by matching
    /// [`bnf_opaque_schematic`] against `use_ty` ([`match_tvars`]). Each opaque
    /// slot ([`opaque_supply`]) is supplied by [`Self::embed_const_term`] on the
    /// actual HOL constant at the solved instantiation — the SAME parameter /
    /// canonical encoding a bare occurrence embeds to — so the combinator's `_def`
    /// LHS δβ-reduces to EXACTLY the embedded RHS. Returns `None` when the type
    /// does not match (the caller falls back to the opaque `const:` param; the
    /// kernel re-checks either way).
    pub(crate) fn embed_bnf_opaque_combinator(
        &mut self,
        n: &str,
        use_ty: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some(def) = bnf_opaque_def_const_name(n) else {
            return Ok(None);
        };
        let Some(schematic) = bnf_opaque_schematic(n) else {
            return Ok(None);
        };
        let Some(tvs) = method_obj_tvars(&schematic) else {
            return Ok(None);
        };
        let Some(subs) = match_tvars(&schematic, use_ty, &tvs) else {
            return Ok(None);
        };
        // A closure resolving a tvar name to its solved instantiation (falling
        // back to the schematic name if — defensively — absent).
        let sub = |name: &str| -> IsaType {
            subs.iter()
                .find(|((sn, _), _)| sn == name)
                .map(|(_, ty)| ty.clone())
                .unwrap_or_else(|| tv(name))
        };
        let mut e = Expr::const_str(def);
        // Type arguments (in `method_obj_tvars` / schematic order).
        for (_tv, ty) in &subs {
            let te = self.embed_type(ty)?;
            e = Expr::app(e, te);
        }
        // Opaque-const arguments (re-embedded through the ordinary dispatch).
        for (cname, cty) in opaque_supply(n, &sub) {
            let arg = self.embed_const_term(&IsaTerm::Const {
                n: cname.to_string(),
                t: cty,
            })?;
            e = Expr::app(e, arg);
        }
        Ok(Some(e))
    }
}
