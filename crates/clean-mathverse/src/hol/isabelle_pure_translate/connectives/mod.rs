// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HOL logical connectives and combinators: True/False/Not/conj/disj encodings and
//! definitions, `HOL.If`, `Fun.comp`/`Fun.id`, set/lattice/ball/bex encodings and the
//! bare-connective η-expansion support.
//!
//! Part of the [`super`] Pure proof-term → clean kernel translator; split
//! out of the original single-file module purely for readability — the code is
//! moved verbatim, the behaviour is byte-identical.

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr};

use super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaTerm, IsaType};
use super::*;

mod bnf_cardinal;
mod bnf_defs;
mod bridges;
mod fun_defs;
mod instance_ops;
mod pointfree_defs;
mod sets;

pub(crate) use bnf_cardinal::*;
pub(crate) use bnf_defs::*;
pub(crate) use bridges::*;
pub(crate) use fun_defs::*;
pub(crate) use instance_ops::*;
pub(crate) use pointfree_defs::*;
pub(crate) use sets::*;

/// Whether `name` is a logical/structural connective that
/// [`Ctx::embed_bare_connective`] embeds to its η-expanded semantic lambda when
/// it appears **bare** (un-applied). These are exactly the heads whose *applied*
/// forms `embed_term` rewrites to a clean `Pi`/`Eq`; embedding the bare form to
/// the matching lambda keeps the two β-equal (fixing the connective fold/unfold
/// asymmetry). `HOL.conj`/`disj`/`Not`/`True`/`False` are NOT here — those embed
/// to their registered def-consts (which already unify bare and applied uses).
pub(crate) fn is_bare_connective(name: &str) -> bool {
    matches!(
        name,
        "Pure.imp" | "HOL.implies" | "Pure.all" | "HOL.All" | "HOL.eq" | "Pure.eq" | "="
    )
}

/// The faithful CIC encoding of a HOL logical connective (propositional
/// fragment), or `None` if `name` is not one we encode. Uses clean `Prop`
/// quantification/implication so each HOL `_def` becomes reflexivity and the
/// connective intro/elim proofs translate without special-casing.
pub(crate) fn connective_encoding(name: &str) -> Option<Expr> {
    // Fresh fvar id space (abstracted away immediately; only per-encoding
    // distinctness matters).
    const A: u64 = 0x5f10_0001;
    const B: u64 = 0x5f10_0002;
    const C: u64 = 0x5f10_0003;
    let prop_prop = Expr::arrow(Expr::prop(), Expr::prop());
    // False ≡ ∀P. P
    let false_enc = || prop_pi(C, |p| p);
    match name {
        // True ≡ ((λx:Prop. x) = (λx:Prop. x))
        //
        // `Code_Generator.holds` is Pure-level truth re-branded for the code
        // generator (`holds ≡ ((λx::prop. x) ≡ (λx::prop. x))`,
        // `Code_Generator.holds_def_raw`): under `prop ↦ Prop` its defining body
        // is EXACTLY the `HOL.True` encoding, so it shares the same shape (its
        // own def-const, registered below, δ-unfolds to this encoding, making
        // `holds_def_raw` reflexive and unblocking the `holds` consumer cascade).
        "HOL.True" | "Code_Generator.holds" => {
            let id = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
            Some(Expr::apps(
                Expr::const_str_levels("Eq", vec![obj_level()]),
                [prop_prop, id.clone(), id],
            ))
        }
        // False ≡ ∀P. P
        "HOL.False" => Some(false_enc()),
        // Not A ≡ A → False
        "HOL.Not" => Some(prop_lam(A, |a| Expr::arrow(a, false_enc()))),
        // A ∧ B ≡ ∀C. (A → B → C) → C
        "HOL.conj" => Some(prop_lam(A, |a| {
            prop_lam(B, move |b| {
                prop_pi(C, move |c| {
                    Expr::arrow(Expr::arrow(a.clone(), Expr::arrow(b.clone(), c.clone())), c)
                })
            })
        })),
        // A ∨ B ≡ ∀C. (A → C) → (B → C) → C
        "HOL.disj" => Some(prop_lam(A, |a| {
            prop_lam(B, move |b| {
                prop_pi(C, move |c| {
                    Expr::arrow(
                        Expr::arrow(a.clone(), c.clone()),
                        Expr::arrow(Expr::arrow(b.clone(), c.clone()), c),
                    )
                })
            })
        })),
        _ => None,
    }
}

pub(crate) fn connective_def_name(name: &str) -> Option<&'static str> {
    match name {
        "HOL.True" => Some("isabelle.def.HOL.True"),
        "HOL.False" => Some("isabelle.def.HOL.False"),
        "HOL.Not" => Some("isabelle.def.HOL.Not"),
        "HOL.conj" => Some("isabelle.def.HOL.conj"),
        "HOL.disj" => Some("isabelle.def.HOL.disj"),
        "Code_Generator.holds" => Some("isabelle.def.Code_Generator.holds"),
        _ => None,
    }
}

/// The clean type of each monomorphic HOL connective definition: `Prop` for the
/// nullary `True`/`False`, `Prop → Prop` for `Not`, `Prop → Prop → Prop` for the
/// binary `conj`/`disj`.
pub(crate) fn connective_def_type(name: &str) -> Option<Expr> {
    match name {
        "HOL.True" | "HOL.False" | "Code_Generator.holds" => Some(Expr::prop()),
        "HOL.Not" => Some(Expr::arrow(Expr::prop(), Expr::prop())),
        "HOL.conj" | "HOL.disj" => Some(Expr::arrow(
            Expr::prop(),
            Expr::arrow(Expr::prop(), Expr::prop()),
        )),
        _ => None,
    }
}

/// The monomorphic HOL connectives as clean [`Declaration::Definition`]s, in
/// dependency order (`True`, `False`, `Not`, `conj`, `disj`). Each definition's
/// `value` is the inline [`connective_encoding`]; its const head is what
/// [`Ctx::embed_term`] emits for an occurrence of the connective. The verifier
/// ([`super::isabelle_pure_verify`]) `add_decl`s these once into its accumulating
/// environment before replaying the closure, so every connective occurrence
/// shares one defeq-unfolding symbol — abstract and concrete occurrences no
/// longer disagree (the conjI/disjI fold/unfold asymmetry). All are over `Prop`,
/// so there are no level or type parameters.
#[must_use]
pub(crate) fn connective_definition_decls() -> Vec<Declaration> {
    [
        "HOL.True",
        "HOL.False",
        "HOL.Not",
        "HOL.conj",
        "HOL.disj",
        "Code_Generator.holds",
    ]
    .into_iter()
    .filter_map(|n| {
        let name = connective_def_name(n)?;
        let type_ = connective_def_type(n)?;
        let value = connective_encoding(n)?;
        Some(Declaration::Definition {
            name: Name::from_string(name),
            level_params: Vec::new(),
            type_,
            value,
            is_reducible: true,
        })
    })
    .collect()
}

/// The kernel declaration name of the clean polymorphic `Definition` registered
/// for HOL's if-then-else `HOL.If` (`isabelle.def.HOL.If`).
pub(crate) fn hol_if_def_name() -> &'static str {
    "isabelle.def.HOL.If"
}

/// The faithful clean polymorphic `Definition` value+type for HOL's if-then-else
/// `HOL.If : bool ⇒ 'a ⇒ 'a ⇒ 'a` (condition first in Isabelle order).
///
/// Under the embedding `HOL.bool ↦ Prop`, the clean definition is
/// ```text
/// isabelle.def.HOL.If : Π(α : Sort u). Prop → α → α → α
///   := λ(α : Sort u)(c : Prop)(x : α)(y : α). @ite.{u} α c (decInst c) x y
/// ```
/// where `decInst c : Decidable c` is the **classical** decidability instance
/// ```text
/// decInst c := @Classical.choice.{1} (Decidable c)
///   (@Or.rec c (c → False) (λ_. Nonempty (Decidable c))
///       (λh : c.         Nonempty.intro (Decidable c) (Decidable.isTrue  c h))
///       (λh : c → False. Nonempty.intro (Decidable c) (Decidable.isFalse c h))
///       (Classical.em c)).
/// ```
/// This is exactly HOL's classical `if`: when `c` holds it selects `x`, otherwise
/// `y`. The case split is over the **Prop** `Or` (small elimination into the Prop
/// `Nonempty (Decidable c)`, which the kernel permits), and `Classical.choice`
/// extracts the `Decidable c` witness. Its transitive axiom closure is therefore
/// `⊆ {Classical.choice, propext, funext}` — all foundational — so importing it
/// keeps every consumer `KernelVerified` to the three foundationals.
///
/// `embed_term` emits each `HOL.If` occurrence as this definition's const applied
/// to the use-site element type (`@isabelle.def.HOL.If.{u} T`), so a recursive
/// list/option function whose `…_def` body spells `if … then … else …`
/// (`List.filter`, `List.find`, `List.takeWhile`, …) embeds with the same head on
/// the LHS use-site and the RHS body — making the definitional equation genuinely
/// reflexive (kernel-checked `Eq.refl`), never a tautology.
pub(crate) fn build_hol_if_value_and_type() -> (Expr, Expr) {
    let sort_u = Expr::sort(Level::param(Name::from_string("u")));
    let prop = Expr::prop();
    let l1 = Level::succ(Level::zero());
    let dec = |c: Expr| Expr::app(Expr::const_str("Decidable"), c);

    // Distinct fresh fvar ids for the four binders and the arm hypothesis.
    let fa = FVarId::new(0x1_5f01);
    let fc = FVarId::new(0x1_5f02);
    let fx = FVarId::new(0x1_5f03);
    let fy = FVarId::new(0x1_5f04);
    let fh = FVarId::new(0x1_5f05);
    let alpha = || Expr::fvar(fa);
    let c = || Expr::fvar(fc);
    let not_c = || Expr::arrow(c(), Expr::const_str("False"));
    let or_c = || Expr::apps(Expr::const_str("Or"), [c(), not_c()]);

    // motive: λ_:Or c (¬c). Nonempty (Decidable c) — constant in its bound var.
    let motive = Expr::lam(
        BinderInfo::Default,
        or_c(),
        Expr::app(
            Expr::const_str_levels("Nonempty", vec![l1.clone()]),
            dec(c()),
        ),
    );
    // pos: λ(h:c). Nonempty.intro (Decidable c) (Decidable.isTrue c h)
    let pos_body = Expr::apps(
        Expr::const_str_levels("Nonempty.intro", vec![l1.clone()]),
        [
            dec(c()),
            Expr::apps(Expr::const_str("Decidable.isTrue"), [c(), Expr::fvar(fh)]),
        ],
    );
    let pos = Expr::lam(BinderInfo::Default, c(), pos_body.abstract_fvar(fh));
    // neg: λ(h:¬c). Nonempty.intro (Decidable c) (Decidable.isFalse c h)
    let neg_body = Expr::apps(
        Expr::const_str_levels("Nonempty.intro", vec![l1.clone()]),
        [
            dec(c()),
            Expr::apps(Expr::const_str("Decidable.isFalse"), [c(), Expr::fvar(fh)]),
        ],
    );
    let neg = Expr::lam(BinderInfo::Default, not_c(), neg_body.abstract_fvar(fh));
    let em = Expr::app(Expr::const_str("Classical.em"), c());
    let nonempty_dec = Expr::apps(
        Expr::const_str("Or.rec"),
        [c(), not_c(), motive, pos, neg, em],
    );
    let dec_inst = Expr::apps(
        Expr::const_str_levels("Classical.choice", vec![l1]),
        [dec(c()), nonempty_dec],
    );
    let ite_app = Expr::apps(
        Expr::const_str_levels("ite", vec![Level::param(Name::from_string("u"))]),
        [alpha(), c(), dec_inst, Expr::fvar(fx), Expr::fvar(fy)],
    );

    // value: λ(α:Sort u)(c:Prop)(x:α)(y:α). ite … — abstract innermost-first.
    let v = ite_app.abstract_fvar(fy);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fx);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fc);
    let v = Expr::lam(BinderInfo::Default, prop.clone(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, sort_u.clone(), v);

    // type: Π(α:Sort u)(c:Prop)(x:α)(y:α). α.
    let t = alpha().abstract_fvar(fy);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fx);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fc);
    let t = Expr::pi(BinderInfo::Default, prop, t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, sort_u, t);

    (value, type_)
}

/// HOL's if-then-else as a clean [`Declaration::Definition`]
/// (`isabelle.def.HOL.If`). Registered into the verifier's accumulating
/// environment up front (like [`connective_definition_decls`]) so every `HOL.If`
/// occurrence shares one defeq-unfolding head symbol. See
/// [`build_hol_if_value_and_type`] for the faithful body and its foundational
/// axiom closure.
#[must_use]
pub(crate) fn hol_if_definition_decl() -> Declaration {
    let (value, type_) = build_hol_if_value_and_type();
    Declaration::Definition {
        name: Name::from_string(hol_if_def_name()),
        level_params: vec![Name::from_string("u")],
        type_,
        value,
        is_reducible: true,
    }
}

/// The kernel declaration name of the clean polymorphic `Definition` registered
/// for HOL's function composition `Fun.comp` (`isabelle.def.Fun.comp`).
pub(crate) fn fun_comp_def_name() -> &'static str {
    "isabelle.def.Fun.comp"
}

/// The kernel declaration name of the clean polymorphic `Definition` registered
/// for HOL's identity `Fun.id` (`isabelle.def.Fun.id`).
pub(crate) fn fun_id_def_name() -> &'static str {
    "isabelle.def.Fun.id"
}

/// HOL's function composition `Fun.comp` as a faithful clean polymorphic
/// [`Declaration::Definition`] (`isabelle.def.Fun.comp`).
///
/// HOL's `comp_def` is `comp f g ≡ λx. f (g x)` with the constant typed
/// `('b⇒'c) ⇒ ('a⇒'b) ⇒ ('a⇒'c)`. Object HOL types embed at clean `Type`
/// (`Sort 1`), so the faithful definition is the monomorphic-universe term
/// ```text
/// isabelle.def.Fun.comp : Π(α β γ : Type). (β → γ) → (α → β) → α → γ
///   := λ(α β γ : Type)(f : β → γ)(g : α → β)(x : α). f (g x)
/// ```
/// with **three** leading `Type` binders (`α`, `β`, `γ` discovered in the body's
/// first-occurrence order — `α` from the `λx:α`, then `β`, then `γ`). It has no
/// axiom content (pure λ), so every consumer stays `KernelVerified` to the three
/// foundationals. [`Ctx::embed_term`] emits each `Fun.comp` occurrence as this
/// const applied to the use-site's three solved type arguments, so an applied LHS
/// `Fun.comp f g` δ-reduces to the same `λx. f (g x)` the `comp_def` RHS spells —
/// making the definitional axiom genuinely reflexive (kernel-checked `Eq.refl`),
/// and every downstream `comp`-using lemma δ-consistent.
pub(crate) fn build_fun_comp_value_and_type() -> (Expr, Expr) {
    // α from the `λx:α` (first), β = comp's result element, γ = the shared middle.
    // Naming: f : β → γ, g : α → β, x : α, body f (g x) : γ.
    let fa = FVarId::new(0x1_6c01); // α
    let fb = FVarId::new(0x1_6c02); // β
    let fg = FVarId::new(0x1_6c03); // γ (gamma)
    let ff = FVarId::new(0x1_6c04); // f : β → γ
    let fgf = FVarId::new(0x1_6c05); // g : α → β
    let fx = FVarId::new(0x1_6c06); // x : α
    let alpha = || Expr::fvar(fa);
    let beta = || Expr::fvar(fb);
    let gamma = || Expr::fvar(fg);
    let f_ty = || Expr::arrow(beta(), gamma());
    let g_ty = || Expr::arrow(alpha(), beta());

    // body: f (g x)  —  g x : β, f (g x) : γ.
    let body = Expr::app(Expr::fvar(ff), Expr::app(Expr::fvar(fgf), Expr::fvar(fx)));
    // value: λ(α β γ:Type)(f:β→γ)(g:α→β)(x:α). f (g x) — abstract innermost-first.
    let v = body.abstract_fvar(fx);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fgf);
    let v = Expr::lam(BinderInfo::Default, g_ty(), v);
    let v = v.abstract_fvar(ff);
    let v = Expr::lam(BinderInfo::Default, f_ty(), v);
    let v = v.abstract_fvar(fg);
    let v = Expr::lam(BinderInfo::Default, Expr::type_(), v);
    let v = v.abstract_fvar(fb);
    let v = Expr::lam(BinderInfo::Default, Expr::type_(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    // type: Π(α β γ:Type)(f:β→γ)(g:α→β)(x:α). γ.
    let t = gamma().abstract_fvar(fx);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fgf);
    let t = Expr::pi(BinderInfo::Default, g_ty(), t);
    let t = t.abstract_fvar(ff);
    let t = Expr::pi(BinderInfo::Default, f_ty(), t);
    let t = t.abstract_fvar(fg);
    let t = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    let t = t.abstract_fvar(fb);
    let t = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);

    (value, type_)
}

/// HOL's identity `Fun.id` as a faithful clean polymorphic
/// [`Declaration::Definition`] (`isabelle.def.Fun.id`).
///
/// HOL's `id_def` is `id ≡ λx. x` with the constant typed `'a ⇒ 'a`. Object HOL
/// types embed at clean `Type` (`Sort 1`), so the faithful definition is
/// ```text
/// isabelle.def.Fun.id : Π(α : Type). α → α  :=  λ(α : Type)(x : α). x
/// ```
/// with one leading `Type` binder. It has no axiom content. [`Ctx::embed_term`]
/// emits each `Fun.id` occurrence as this const applied to the use-site's solved
/// element type, so the bare LHS `Fun.id` δ-reduces to `λx. x` = the `id_def` RHS,
/// making the definitional axiom reflexive and `id`-using lemmas δ-consistent.
pub(crate) fn build_fun_id_value_and_type() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_6d01); // α
    let fx = FVarId::new(0x1_6d02); // x : α
    let alpha = || Expr::fvar(fa);

    // value: λ(α:Type)(x:α). x
    let v = Expr::fvar(fx).abstract_fvar(fx);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    // type: Π(α:Type)(x:α). α
    let t = alpha().abstract_fvar(fx);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);

    (value, type_)
}

/// HOL's function composition `Fun.comp` as a clean [`Declaration::Definition`]
/// (`isabelle.def.Fun.comp`). Registered into the verifier's accumulating
/// environment up front (like [`connective_definition_decls`] /
/// [`hol_if_definition_decl`]) so every `Fun.comp` occurrence shares one
/// defeq-unfolding head symbol. See [`build_fun_comp_value_and_type`].
#[must_use]
pub(crate) fn fun_comp_definition_decl() -> Declaration {
    let (value, type_) = build_fun_comp_value_and_type();
    Declaration::Definition {
        name: Name::from_string(fun_comp_def_name()),
        level_params: Vec::new(),
        type_,
        value,
        is_reducible: true,
    }
}

/// HOL's identity `Fun.id` as a clean [`Declaration::Definition`]
/// (`isabelle.def.Fun.id`). Registered into the verifier's accumulating
/// environment up front. See [`build_fun_id_value_and_type`].
#[must_use]
pub(crate) fn fun_id_definition_decl() -> Declaration {
    let (value, type_) = build_fun_id_value_and_type();
    Declaration::Definition {
        name: Name::from_string(fun_id_def_name()),
        level_params: Vec::new(),
        type_,
        value,
        is_reducible: true,
    }
}

/// The kernel declaration name of the clean polymorphic `Definition` registered
/// for Pure's judgement-forming marker `Pure.term`, or `None` for any other name.
///
/// Only `Pure.term` gets a def-const: `Pure.sort_constraint` is a **sort
/// constraint** ([`is_class_app`]) that `embed_term` erases to the vacuous `True`
/// (like `OFCLASS`), so its applied occurrences never reach the bare-const
/// def-routing — registering a `Pure.sort_constraint` def-const would be dead. The
/// `sort_constraint_def` axiom (`sort_constraint TYPE('a) ≡ term TYPE('a)`) is
/// instead discharged by the dedicated `propext` bridge
/// [`super::super::prove_sort_constraint_def`].
pub(crate) fn pure_meta_def_name(name: &str) -> Option<&'static str> {
    match name {
        "Pure.term" => Some("isabelle.def.Pure.term"),
        _ => None,
    }
}

/// The faithful clean polymorphic `Definition` value+type for Pure's judgement
/// marker `Pure.term`.
///
/// Pure's `term_def` is `Pure.term x ≡ (⋀A. A ⟹ A)`: the marker is a pure
/// meta-logic assertion ("`x` is a well-formed term of its type") whose statement
/// is, for every `x`, the polymorphic *meta-truth* `⋀A. A ⟹ A` — a
/// trivially-inhabited `Prop` (`λ(A:Prop)(h:A). h`) that is **independent of the
/// argument**. Under the embedding `⋀A. A ⟹ A` becomes clean `∀(A:Prop). A → A`,
/// so the faithful, conservative definition is
/// ```text
/// isabelle.def.Pure.term : Π(α : Type). α → Prop
///   := λ(α : Type)(_ : α). ∀(A : Prop). A → A
/// ```
/// The argument type `α` is left generic (`Type`) and ignored by the body. It
/// carries **no axiom content** (a closed inhabited `Prop`, pure λ), so it is a
/// genuine conservative extension and every consumer stays `KernelVerified` to the
/// three foundationals. [`Ctx::embed_term`] emits each `Pure.term` occurrence as
/// this def-const applied to the use-site's argument type and argument, so the LHS
/// `Pure.term x` δβ-reduces to `∀A. A → A` = the `term_def` RHS — making the
/// definitional axiom genuinely reflexive (kernel-checked `Eq.refl`), never a
/// `body = body` tautology.
pub(crate) fn pure_meta_true_value_and_type() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_7e01); // α : Type (the argument type — ignored)
    let fx = FVarId::new(0x1_7e02); // _ : α (the ignored argument)
    let alpha = || Expr::fvar(fa);

    // body: ∀(A:Prop). A → A  (the meta-truth `⋀A. A ⟹ A`), closed w.r.t. α/x.
    let meta_true = prop_pi(0x1_7e03, |a| Expr::arrow(a.clone(), a));

    // value: λ(α:Type)(_:α). ∀(A:Prop). A → A — abstract innermost-first.
    let v = meta_true.abstract_fvar(fx); // no fx occurrence, so this is a no-op
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    // type: Π(α:Type)(_:α). Prop.
    let t = Expr::prop().abstract_fvar(fx); // Prop is closed, no-op abstraction
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);

    (value, type_)
}

/// Pure's judgement marker `Pure.term` as a clean [`Declaration::Definition`]
/// (`isabelle.def.Pure.term`). Registered into the verifier's accumulating
/// environment up front (like [`connective_definition_decls`]). Its body is a
/// closed, inhabited `Prop` with no axiom content, so `term_def` verifies
/// reflexively and every `Pure.term` use-site is δ-consistent. See
/// [`pure_meta_true_value_and_type`].
#[must_use]
pub(crate) fn pure_meta_definition_decls() -> Vec<Declaration> {
    let (value, type_) = pure_meta_true_value_and_type();
    match pure_meta_def_name("Pure.term") {
        Some(name) => vec![Declaration::Definition {
            name: Name::from_string(name),
            level_params: Vec::new(),
            type_,
            value,
            is_reducible: true,
        }],
        None => Vec::new(),
    }
}

/// Register the faithful clean inductive types for the HOL datatypes that clean's
/// prelude does not already provide, into the verifier's accumulating environment.
///
/// Currently this is `Num.num` (the binary-numeral datatype
/// `One | Bit0 of num | Bit1 of num`) — clean's prelude already has `Nat`, so the
/// `Nat.nat` mapping needs no registration. Registering `Num` makes the kernel
/// auto-generate `Num.rec`, which [`Ctx::embed_rec_num`] targets; the constructor
/// mappings (`Num.num.One/Bit0/Bit1`) then resolve to real constructors and the
/// numeral definitions reduce by iota. A registration failure is non-fatal — the
/// `Num`-using nodes simply fail to resolve their consts and are honestly rejected
/// (never miscounted). Idempotent: `add_inductive` is a no-op if `Num` is present.
pub(crate) fn register_datatype_inductives(env: &mut Environment) {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};

    if env.get_inductive(&Name::from_string("Num")).is_some() {
        return;
    }
    let num = Expr::const_str("Num");
    // Num : Type (Sort 1).
    let num_type = Expr::type_();
    // One : Num ; Bit0 : Num → Num ; Bit1 : Num → Num.
    let bit_ty = Expr::arrow(num.clone(), num.clone());
    let decl = InductiveDecl {
        level_params: Vec::new(),
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Num"),
            type_: num_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("Num.num.One"),
                    type_: num.clone(),
                },
                Constructor {
                    name: Name::from_string("Num.num.Bit0"),
                    type_: bit_ty.clone(),
                },
                Constructor {
                    name: Name::from_string("Num.num.Bit1"),
                    type_: bit_ty,
                },
            ],
        }],
    };
    let _ = env.add_inductive(decl);
}
