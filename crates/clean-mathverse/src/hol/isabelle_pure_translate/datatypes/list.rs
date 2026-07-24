// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Ctx` datatype-embedding methods for the `'a list` constructors, recursor,
//! case combinator and functor map: `embed_list_nil`, `embed_list_cons`,
//! `embed_rec_list`, `embed_case_list`, `embed_map_list`. Moved verbatim from
//! the original single-file `datatypes` module; behaviour is byte-identical.

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr};

use super::super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaTerm, IsaType};
use super::super::*;

impl Ctx {
    /// Embed HOL's `'a list` constructor `List.list.Nil : 'a list` to clean's
    /// `@List.nil.{0} α`, reading the element type `α` off the constant's
    /// instantiated HOL type `List.list['a]`. Returns `None` if the type is not a
    /// `List.list[_]` (caller falls back to an opaque param).
    pub(crate) fn embed_list_nil(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        let IsaType::Type { n, a } = t else {
            return Ok(None);
        };
        if n != "List.list" || a.len() != 1 {
            return Ok(None);
        }
        let alpha = self.embed_type(&a[0])?;
        Ok(Some(Expr::app(
            Expr::const_str_levels("List.nil", vec![Level::zero()]),
            alpha,
        )))
    }

    /// Embed HOL's `'a list` constructor `List.list.Cons : 'a ⇒ 'a list ⇒ 'a list`
    /// to clean's `@List.cons.{0} α`, reading `α` off the constant's first function
    /// domain. Returns `None` if the type is not `'a ⇒ _`.
    pub(crate) fn embed_list_cons(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        let Some((a_ty, _rest)) = fun_split(t) else {
            return Ok(None);
        };
        let alpha = self.embed_type(a_ty)?;
        Ok(Some(Expr::app(
            Expr::const_str_levels("List.cons", vec![Level::zero()]),
            alpha,
        )))
    }

    /// Embed an occurrence of HOL's `list` recursor `List.list.rec_list` to a bare
    /// clean lambda built over the prelude's `List.rec`.
    ///
    /// Isabelle's `rec_list` is primitive recursion over `list` with a *constant*
    /// (non-dependent) motive: its instantiated type is
    /// `β ⇒ ('a ⇒ 'a list ⇒ β ⇒ β) ⇒ 'a list ⇒ β`. Clean's `List.rec` is the
    /// dependent eliminator
    /// `{α} → (motive : List α → Sort u₁) → motive (nil α)
    ///  → ((hd:α) → (tl:List α) → motive tl → motive (cons α hd tl))
    ///  → (t:List α) → motive t`,
    /// so the faithful specialisation takes `motive := λ_:List α. β`:
    /// ```text
    /// λ(z:β)(c:α→List α→β→β)(t:List α).
    ///   @List.rec.{u₁,0} α (λ_:List α. β) z
    ///     (λ(hd:α)(tl:List α)(ih:β). c hd tl ih) t
    /// ```
    /// The element type `α` is read off the cons-arm's first domain and the motive
    /// result `β` off the first argument; their universe levels are read off the
    /// embedded sorts (`u₁ = 0` when β is `Prop`, else `1`; element level is `0`).
    /// The result is monomorphic — the kernel re-checks the saturated term. Returns
    /// `None` if the type is not the expected shape (caller falls back to a param).
    pub(crate) fn embed_rec_list(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = β ⇒ (('a ⇒ ('a list ⇒ (β ⇒ β))) ⇒ ('a list ⇒ β)).
        let Some((beta_ty, rest)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((cons_arm_ty, _res)) = fun_split(rest) else {
            return Ok(None);
        };
        // cons_arm_ty = 'a ⇒ ('a list ⇒ (β ⇒ β)); read `α` from its domain.
        let Some((alpha_ty, _)) = fun_split(cons_arm_ty) else {
            return Ok(None);
        };
        let beta = self.embed_type(beta_ty)?;
        let alpha = self.embed_type(alpha_ty)?;
        // Motive result universe `u₁`: Prop (Sort 0) when β is Prop, else Sort 1.
        let u1 = if matches!(beta.kind(), clean_kernel::expr::ExprKind::Sort(l) if l.is_zero()) {
            Level::zero()
        } else {
            Level::succ(Level::zero())
        };
        let list_alpha = Expr::app(
            Expr::const_str_levels("List", vec![Level::zero()]),
            alpha.clone(),
        );
        // motive : List α → Sort u₁, constant `λ_:List α. β`.
        let motive = Expr::lam(BinderInfo::Default, list_alpha.clone(), beta.clone());
        // cons-case adaptor: Isabelle's `c : 'a ⇒ 'a list ⇒ β ⇒ β` already matches
        // clean's `(hd:α) → (tl:List α) → motive tl → motive (cons α hd tl)` (motive
        // is constant β), so we η-wrap `λ(hd)(tl)(ih). c hd tl ih`. Inside
        // `λ(z)(c)(t).` c = bvar 1; inside the added `λ(hd)(tl)(ih).` (three binders),
        // c = bvar 4, hd = bvar 2, tl = bvar 1, ih = bvar 0.
        let cons_arm = Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            Expr::lam(
                BinderInfo::Default,
                list_alpha.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    beta.clone(),
                    Expr::apps(Expr::bvar(4), [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]),
                ),
            ),
        );
        // c_ty = α → List α → β → β.
        let c_ty = Expr::arrow(
            alpha.clone(),
            Expr::arrow(list_alpha.clone(), Expr::arrow(beta.clone(), beta.clone())),
        );
        // λ(z:β)(c:c_ty)(t:List α). @List.rec.{u₁,0} α motive z cons_arm t
        let body = Expr::apps(
            Expr::const_str_levels("List.rec", vec![u1, Level::zero()]),
            [
                alpha.clone(),
                motive,
                Expr::bvar(2), // z (Nil case)
                cons_arm,
                Expr::bvar(0), // t
            ],
        );
        let lam = Expr::lam(
            BinderInfo::Default,
            beta,
            Expr::lam(
                BinderInfo::Default,
                c_ty,
                Expr::lam(BinderInfo::Default, list_alpha, body),
            ),
        );
        Ok(Some(lam))
    }

    /// Embed an occurrence of HOL's `list` **case combinator**
    /// `List.list.case_list` (`case t of [] ⇒ z | x#xs ⇒ f x xs`) to a bare clean
    /// lambda over `List.rec`.
    ///
    /// Its instantiated type is `β ⇒ ('a ⇒ 'a list ⇒ β) ⇒ 'a list ⇒ β`. Clean's
    /// `List.rec` with the constant motive `λ_:List α. β` and a cons arm that
    /// *drops* the recursive value gives exactly case analysis:
    /// ```text
    /// λ(z:β)(f:α→List α→β)(t:List α).
    ///   @List.rec.{u₁,0} α (λ_:List α. β) z
    ///     (λ(hd:α)(tl:List α)(_ih:β). f hd tl) t
    /// ```
    /// `α`, `β` and the universe `u₁` are read off the constant's instantiated type;
    /// the kernel re-checks the saturated term. Returns `None` if the type is not the
    /// expected `β ⇒ ('a ⇒ 'a list ⇒ β) ⇒ 'a list ⇒ β` shape.
    pub(crate) fn embed_case_list(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = β ⇒ (('a ⇒ ('a list ⇒ β)) ⇒ ('a list ⇒ β)).
        let Some((beta_ty, rest)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((case_arm_ty, _res)) = fun_split(rest) else {
            return Ok(None);
        };
        // case_arm_ty = 'a ⇒ ('a list ⇒ β); read `α` from its domain.
        let Some((alpha_ty, _)) = fun_split(case_arm_ty) else {
            return Ok(None);
        };
        let beta = self.embed_type(beta_ty)?;
        let alpha = self.embed_type(alpha_ty)?;
        let u1 = if matches!(beta.kind(), clean_kernel::expr::ExprKind::Sort(l) if l.is_zero()) {
            Level::zero()
        } else {
            Level::succ(Level::zero())
        };
        let list_alpha = Expr::app(
            Expr::const_str_levels("List", vec![Level::zero()]),
            alpha.clone(),
        );
        let motive = Expr::lam(BinderInfo::Default, list_alpha.clone(), beta.clone());
        // cons-case adaptor: `f : 'a ⇒ 'a list ⇒ β` applied to head & tail, ignoring
        // the recursive value `_ih`. Inside `λ(z)(f)(t).` f = bvar 1; inside the
        // added `λ(hd)(tl)(_ih).`, f = bvar 4, hd = bvar 2, tl = bvar 1.
        let cons_arm = Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            Expr::lam(
                BinderInfo::Default,
                list_alpha.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    beta.clone(),
                    Expr::apps(Expr::bvar(4), [Expr::bvar(2), Expr::bvar(1)]),
                ),
            ),
        );
        let f_ty = Expr::arrow(alpha.clone(), Expr::arrow(list_alpha.clone(), beta.clone()));
        let body = Expr::apps(
            Expr::const_str_levels("List.rec", vec![u1, Level::zero()]),
            [
                alpha.clone(),
                motive,
                Expr::bvar(2), // z (Nil case)
                cons_arm,
                Expr::bvar(0), // t
            ],
        );
        let lam = Expr::lam(
            BinderInfo::Default,
            beta,
            Expr::lam(
                BinderInfo::Default,
                f_ty,
                Expr::lam(BinderInfo::Default, list_alpha, body),
            ),
        );
        Ok(Some(lam))
    }

    /// Embed HOL's list **functor map** `List.list.map : ('a⇒'b) ⇒ 'a list ⇒ 'b list`
    /// to a bare clean lambda built over the prelude's `List.rec`.
    ///
    /// Isabelle defines `map` *not* as a plain `rec_list` fold but through the BNF
    /// (bounded-natural-functor) machinery:
    /// `map f ≡ ctor_fold_list (ctor_list ∘ map_pre_list f id)`, where
    /// `ctor_fold_list ≡ λs. Eps (λg. mor_list … g)` is the **unique morphism**
    /// (a `Hilbert_Choice.Eps` over the BNF morphism relation `mor_list`, which is
    /// stated over the internal initial-algebra carrier `list_IITN_list` via
    /// `Abs_list`/`Rep_list`/`str_init_list`). That body has **no δ-path** to a
    /// recursor — `ctor_fold_list = rec_list` is the BNF *initiality theorem*, a real
    /// proof, not a definitional unfolding — so `map_def` does not close in the
    /// list-function registry (its RHS embeds the BNF internals as opaque params).
    ///
    /// The faithful image is instead the genuine recursive map semantics, exactly as
    /// `rec_list`/`case_list` are mapped *directly* to `List.rec` (bypassing their own
    /// equally-non-computational BNF/`The`-based `_def` axioms):
    /// ```text
    /// λ(f:α→β)(t:List α).
    ///   @List.rec.{1,0} α (λ_:List α. List β) (@List.nil β)
    ///     (λ(hd:α)(tl:List α)(ih:List β). @List.cons β (f hd) ih) t
    /// ```
    /// This reduces by the kernel's iota rule to the characteristic equations
    /// `map f [] = []` and `map f (x#xs) = (f x)#(map f xs)` — precisely HOL's
    /// `List.list.map_1`/`map_2` — so those simp lemmas and `map`'s consumers verify.
    /// `α`,`β` are read off the constant's instantiated type `(α⇒β) ⇒ list α ⇒ list β`
    /// (both element levels are `0`; the motive result `List β` lives in `Sort 1`, so
    /// `u₁ = 1`). The kernel re-checks the saturated term, so a wrong shape is
    /// rejected. Returns `None` if the type is not the expected functor-map shape
    /// (caller falls back to an opaque param). Gated on `instance_unfold` (the final
    /// escalation pass — strictly additive).
    pub(crate) fn embed_map_list(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = ('a ⇒ 'b) ⇒ ('a list ⇒ 'b list).
        let Some((fn_ty, rest)) = fun_split(t) else {
            return Ok(None);
        };
        // fn_ty = 'a ⇒ 'b; read α (domain), β (codomain).
        let Some((alpha_ty, beta_ty)) = fun_split(fn_ty) else {
            return Ok(None);
        };
        // rest = 'a list ⇒ 'b list; sanity-check the source is `List.list[_]`.
        let Some((src_ty, _dst_ty)) = fun_split(rest) else {
            return Ok(None);
        };
        if !matches!(src_ty, IsaType::Type { n, a } if n == "List.list" && a.len() == 1) {
            return Ok(None);
        }
        let alpha = self.embed_type(alpha_ty)?;
        let beta = self.embed_type(beta_ty)?;
        let list = |elem: &Expr| {
            Expr::app(
                Expr::const_str_levels("List", vec![Level::zero()]),
                elem.clone(),
            )
        };
        let list_alpha = list(&alpha);
        let list_beta = list(&beta);
        // motive : List α → Sort 1, constant `λ_:List α. List β`.
        let motive = Expr::lam(BinderInfo::Default, list_alpha.clone(), list_beta.clone());
        let nil_beta = Expr::app(
            Expr::const_str_levels("List.nil", vec![Level::zero()]),
            beta.clone(),
        );
        // cons-case: `λ(hd:α)(tl:List α)(ih:List β). @List.cons β (f hd) ih`.
        // Inside `λ(f)(t).` f = bvar 1; inside the added `λ(hd)(tl)(ih).`,
        // f = bvar 4, hd = bvar 2, ih = bvar 0.
        let cons_arm = Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            Expr::lam(
                BinderInfo::Default,
                list_alpha.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    list_beta.clone(),
                    Expr::apps(
                        Expr::const_str_levels("List.cons", vec![Level::zero()]),
                        [
                            beta.clone(),
                            Expr::app(Expr::bvar(4), Expr::bvar(2)), // f hd
                            Expr::bvar(0),                           // ih
                        ],
                    ),
                ),
            ),
        );
        // λ(f:α→β)(t:List α). @List.rec.{1,0} α motive nil cons_arm t
        let body = Expr::apps(
            Expr::const_str_levels("List.rec", vec![Level::succ(Level::zero()), Level::zero()]),
            [
                alpha.clone(),
                motive,
                nil_beta,
                cons_arm,
                Expr::bvar(0), // t
            ],
        );
        let lam = Expr::lam(
            BinderInfo::Default,
            Expr::arrow(alpha.clone(), beta),
            Expr::lam(BinderInfo::Default, list_alpha, body),
        );
        Ok(Some(lam))
    }
}
