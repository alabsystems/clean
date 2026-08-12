// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Ctx` BNF functor-map embedding methods: `embed_map_sum`, `embed_map_prod`,
//! `embed_map_option`, `embed_id_bnf`. Moved verbatim from the original
//! single-file `datatypes` module; behaviour is byte-identical.

use clean_kernel::level::Level;
use clean_kernel::{BinderInfo, Expr};

use super::super::super::isabelle_pure::IsaType;
use super::super::*;

impl Ctx {
    /// Embed the BNF **functor map for sum**, `Sum_Type.map_sum :
    /// ('a⇒'c) ⇒ ('b⇒'d) ⇒ 'a+'b ⇒ 'c+'d`, to a bare clean lambda over `Sum.rec`.
    /// HOL's `map_sum_def` is `λf g s. case s of Inl a ⇒ Inl (f a) | Inr a ⇒ Inr (g a)`,
    /// which is exactly clean's `Sum.rec` with the (constant) motive `λ_:Sum α β.
    /// Sum γ δ` and arms `λa. Sum.inl γ δ (f a)`, `λa. Sum.inr γ δ (g a)`:
    /// ```text
    /// λ(f:α→γ)(g:β→δ)(s:Sum α β).
    ///   @Sum.rec.{1,0,0} α β (λ_:Sum α β. Sum γ δ)
    ///     (λa:α. @Sum.inl γ δ (f a)) (λb:β. @Sum.inr γ δ (g b)) s
    /// ```
    /// The four element types `α,β,γ,δ` are read off the constant's instantiated
    /// type; the kernel re-checks the saturated term. Returns `None` on an
    /// unexpected shape (caller falls back to an opaque param). This is the genuine
    /// `map_sum` semantics — `map_sum f g (Inl a)` ⟶ `Inl (f a)` by iota — so the
    /// `map_pre_list`/BNF-functor `_def` axioms whose RHS mention `map_sum` close.
    pub(crate) fn embed_map_sum(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = ('a⇒'c) ⇒ (('b⇒'d) ⇒ (sum['a,'b] ⇒ sum['c,'d])).
        let Some((f_ty, rest)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((g_ty, rest2)) = fun_split(rest) else {
            return Ok(None);
        };
        let Some((_src_ty, _dst_ty)) = fun_split(rest2) else {
            return Ok(None);
        };
        let Some((a_ty, c_ty)) = fun_split(f_ty) else {
            return Ok(None);
        };
        let Some((b_ty, d_ty)) = fun_split(g_ty) else {
            return Ok(None);
        };
        let alpha = self.embed_type(a_ty)?;
        let gamma = self.embed_type(c_ty)?;
        let beta = self.embed_type(b_ty)?;
        let delta = self.embed_type(d_ty)?;
        let lvls = vec![Level::zero(), Level::zero()];
        let sum = |l: &Expr, r: &Expr| {
            Expr::apps(
                Expr::const_str_levels("Sum", lvls.clone()),
                [l.clone(), r.clone()],
            )
        };
        let sum_ab = sum(&alpha, &beta);
        let sum_cd = sum(&gamma, &delta);
        let f_clean = Expr::arrow(alpha.clone(), gamma.clone());
        let g_clean = Expr::arrow(beta.clone(), delta.clone());
        // Constant motive `λ_:Sum α β. Sum γ δ`.
        let motive = Expr::lam(BinderInfo::Default, sum_ab.clone(), sum_cd.clone());
        // inl arm: `λa:α. @Sum.inl γ δ (f a)`. Inside `λ(f)(g)(s)(a)`: f=bvar3, a=bvar0.
        let inl_arm = Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            Expr::apps(
                Expr::const_str_levels("Sum.inl", lvls.clone()),
                [
                    gamma.clone(),
                    delta.clone(),
                    Expr::app(Expr::bvar(3), Expr::bvar(0)),
                ],
            ),
        );
        // inr arm: `λb:β. @Sum.inr γ δ (g b)`. Inside `λ(f)(g)(s)(b)`: g=bvar2, b=bvar0.
        let inr_arm = Expr::lam(
            BinderInfo::Default,
            beta.clone(),
            Expr::apps(
                Expr::const_str_levels("Sum.inr", lvls.clone()),
                [
                    gamma.clone(),
                    delta.clone(),
                    Expr::app(Expr::bvar(2), Expr::bvar(0)),
                ],
            ),
        );
        // Inside `λ(f)(g)(s)`: s=bvar0. Sum.rec.{w,0,0} with motive in Sort 1.
        let body = Expr::apps(
            Expr::const_str_levels(
                "Sum.rec",
                vec![Level::succ(Level::zero()), Level::zero(), Level::zero()],
            ),
            [
                alpha.clone(),
                beta.clone(),
                motive,
                inl_arm,
                inr_arm,
                Expr::bvar(0),
            ],
        );
        Ok(Some(Expr::lam(
            BinderInfo::Default,
            f_clean,
            Expr::lam(
                BinderInfo::Default,
                g_clean,
                Expr::lam(BinderInfo::Default, sum_ab, body),
            ),
        )))
    }

    /// Embed the BNF **functor map for product**, `Product_Type.map_prod :
    /// ('a⇒'c) ⇒ ('b⇒'d) ⇒ 'a×'b ⇒ 'c×'d`. HOL's `map_prod_def` is
    /// `λf g. λ(x,y). (f x, g y)`, i.e. `λf g p. (f (fst p), g (snd p))`:
    /// ```text
    /// λ(f:α→γ)(g:β→δ)(p:Prod α β).
    ///   @Prod.mk γ δ (f (@Prod.fst α β p)) (g (@Prod.snd α β p))
    /// ```
    /// `α,β,γ,δ` read off the const type; kernel re-checked. Returns `None` on an
    /// unexpected shape.
    pub(crate) fn embed_map_prod(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = ('a⇒'c) ⇒ (('b⇒'d) ⇒ (prod['a,'b] ⇒ prod['c,'d])).
        let Some((f_ty, rest)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((g_ty, rest2)) = fun_split(rest) else {
            return Ok(None);
        };
        let Some((_src_ty, _dst_ty)) = fun_split(rest2) else {
            return Ok(None);
        };
        let Some((a_ty, c_ty)) = fun_split(f_ty) else {
            return Ok(None);
        };
        let Some((b_ty, d_ty)) = fun_split(g_ty) else {
            return Ok(None);
        };
        let alpha = self.embed_type(a_ty)?;
        let gamma = self.embed_type(c_ty)?;
        let beta = self.embed_type(b_ty)?;
        let delta = self.embed_type(d_ty)?;
        let lvls = vec![Level::zero(), Level::zero()];
        let prod = |l: &Expr, r: &Expr| {
            Expr::apps(
                Expr::const_str_levels("Prod", lvls.clone()),
                [l.clone(), r.clone()],
            )
        };
        let prod_ab = prod(&alpha, &beta);
        let f_clean = Expr::arrow(alpha.clone(), gamma.clone());
        let g_clean = Expr::arrow(beta.clone(), delta.clone());
        // Inside `λ(f)(g)(p)`: f=bvar2, g=bvar1, p=bvar0.
        let fst_p = Expr::apps(
            Expr::const_str_levels("Prod.fst", lvls.clone()),
            [alpha.clone(), beta.clone(), Expr::bvar(0)],
        );
        let snd_p = Expr::apps(
            Expr::const_str_levels("Prod.snd", lvls.clone()),
            [alpha.clone(), beta.clone(), Expr::bvar(0)],
        );
        let body = Expr::apps(
            Expr::const_str_levels("Prod.mk", lvls.clone()),
            [
                gamma.clone(),
                delta.clone(),
                Expr::app(Expr::bvar(2), fst_p),
                Expr::app(Expr::bvar(1), snd_p),
            ],
        );
        Ok(Some(Expr::lam(
            BinderInfo::Default,
            f_clean,
            Expr::lam(
                BinderInfo::Default,
                g_clean,
                Expr::lam(BinderInfo::Default, prod_ab, body),
            ),
        )))
    }

    /// Embed the BNF **functor map for option**, `Option.map_option :
    /// ('a⇒'b) ⇒ 'a option ⇒ 'b option`. HOL's `map_option_case` is
    /// `λf y. case y of None ⇒ None | Some x ⇒ Some (f x)`, i.e. clean's
    /// `Option.rec` with motive `λ_:Option α. Option β`:
    /// ```text
    /// λ(f:α→β)(o:Option α).
    ///   @Option.rec.{1,0} α (λ_:Option α. Option β)
    ///     (@Option.none β) (λa:α. @Option.some β (f a)) o
    /// ```
    /// `α,β` read off the const type; kernel re-checked. `those_def`'s RHS uses
    /// `map_option`, so mapping it closes `those`. Returns `None` on an unexpected
    /// shape.
    pub(crate) fn embed_map_option(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = ('a⇒'b) ⇒ (option['a] ⇒ option['b]).
        let Some((f_ty, _rest)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((a_ty, b_ty)) = fun_split(f_ty) else {
            return Ok(None);
        };
        let alpha = self.embed_type(a_ty)?;
        let beta = self.embed_type(b_ty)?;
        let opt = |e: &Expr| {
            Expr::app(
                Expr::const_str_levels("Option", vec![Level::zero()]),
                e.clone(),
            )
        };
        let opt_a = opt(&alpha);
        let opt_b = opt(&beta);
        let f_clean = Expr::arrow(alpha.clone(), beta.clone());
        let motive = Expr::lam(BinderInfo::Default, opt_a.clone(), opt_b.clone());
        let none_b = Expr::app(
            Expr::const_str_levels("Option.none", vec![Level::zero()]),
            beta.clone(),
        );
        // some arm: `λa:α. @Option.some β (f a)`. Inside `λ(f)(o)(a)`: f=bvar2, a=bvar0.
        let some_arm = Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            Expr::apps(
                Expr::const_str_levels("Option.some", vec![Level::zero()]),
                [beta.clone(), Expr::app(Expr::bvar(2), Expr::bvar(0))],
            ),
        );
        // Inside `λ(f)(o)`: o=bvar0.
        let body = Expr::apps(
            Expr::const_str_levels(
                "Option.rec",
                vec![Level::succ(Level::zero()), Level::zero()],
            ),
            [alpha.clone(), motive, none_b, some_arm, Expr::bvar(0)],
        );
        Ok(Some(Expr::lam(
            BinderInfo::Default,
            f_clean,
            Expr::lam(BinderInfo::Default, opt_a, body),
        )))
    }

    /// Embed the BNF composition identity `BNF_Composition.id_bnf : 'a ⇒ 'a` to
    /// `λx:α. x`. HOL's `id_bnf_def` is literally `id_bnf ≡ λx. x` (the BNF
    /// composition wrapper is the identity), so `map_pre_list ≡ id_bnf ∘ map_sum id
    /// (map_prod f1 f2) ∘ id_bnf` reduces to just the sum/prod map. `α` is read off
    /// the const type. Returns `None` if the type is not a single arrow.
    pub(crate) fn embed_id_bnf(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = 'a ⇒ 'a.
        let Some((a_ty, _res)) = fun_split(t) else {
            return Ok(None);
        };
        let alpha = self.embed_type(a_ty)?;
        Ok(Some(Expr::lam(BinderInfo::Default, alpha, Expr::bvar(0))))
    }
}
