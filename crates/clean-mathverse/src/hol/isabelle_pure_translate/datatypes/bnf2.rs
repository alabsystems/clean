// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Ctx` list-BNF constructor / initial-algebra-fold / pre-list shape-map
//! embedding methods: `embed_ctor_list`, `embed_ctor_fold_list`,
//! `embed_map_pre_list`. Moved verbatim from the original single-file
//! `datatypes` module; behaviour is byte-identical.

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr};

use super::super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaTerm, IsaType};
use super::super::*;

impl Ctx {
    /// Embed the **list BNF constructor** `List.list.ctor_list :
    /// unit + 'a×'a list ⇒ 'a list`. HOL's `ctor_list ≡ Abs_list ∘ str_init_list ∘
    /// map_pre_list id Rep_list` packages the two list constructors as a single
    /// sum-eliminator over the shape functor `unit + 'a×'a list`: `Inl () ↦ []`,
    /// `Inr (x, xs) ↦ x#xs`. Clean's `Sum.rec` with the constant motive
    /// `λ_. List α` gives exactly this:
    /// ```text
    /// λ(c:Sum Unit (Prod α (List α))).
    ///   @Sum.rec.{1,0,0} Unit (Prod α (List α)) (λ_. List α)
    ///     (λ_:Unit. @List.nil α)
    ///     (λp:Prod α (List α). @List.cons α (@Prod.fst α (List α) p) (@Prod.snd α (List α) p))
    ///     c
    /// ```
    /// This is the genuine constructor — `ctor_list (Inl ()) ⟶ []`,
    /// `ctor_list (Inr (x,xs)) ⟶ x#xs` by iota — so the `ctor_list`-spelled BNF
    /// `_def` axioms and lemmas close. `α` is read off the const type (the source
    /// `unit + 'a×'a list`); kernel re-checked. Returns `None` on an unexpected
    /// shape.
    pub(crate) fn embed_ctor_list(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = (unit + 'a×'a list) ⇒ 'a list.
        let Some((src_ty, _dst_ty)) = fun_split(t) else {
            return Ok(None);
        };
        // src = Sum_Type.sum[unit, prod['a, list['a]]].
        let IsaType::Type { n, a } = src_ty else {
            return Ok(None);
        };
        if n != "Sum_Type.sum" || a.len() != 2 {
            return Ok(None);
        }
        // a[1] = prod['a, list['a]]; read α from its first component.
        let IsaType::Type { n: pn, a: pa } = &a[1] else {
            return Ok(None);
        };
        if pn != "Product_Type.prod" || pa.len() != 2 {
            return Ok(None);
        }
        let alpha = self.embed_type(&pa[0])?;
        let lvls = vec![Level::zero(), Level::zero()];
        let unit = Expr::const_str("Unit");
        let list_alpha = Expr::app(
            Expr::const_str_levels("List", vec![Level::zero()]),
            alpha.clone(),
        );
        let prod_a_list = Expr::apps(
            Expr::const_str_levels("Prod", lvls.clone()),
            [alpha.clone(), list_alpha.clone()],
        );
        let sum_shape = Expr::apps(
            Expr::const_str_levels("Sum", lvls.clone()),
            [unit.clone(), prod_a_list.clone()],
        );
        // Constant motive `λ_:Sum Unit (Prod α (List α)). List α`.
        let motive = Expr::lam(BinderInfo::Default, sum_shape.clone(), list_alpha.clone());
        // inl arm: `λ_:Unit. @List.nil α`.
        let inl_arm = Expr::lam(
            BinderInfo::Default,
            unit.clone(),
            Expr::app(
                Expr::const_str_levels("List.nil", vec![Level::zero()]),
                alpha.clone(),
            ),
        );
        // inr arm: `λp:Prod α (List α). @List.cons α (fst p) (snd p)`. p=bvar0.
        let fst_p = Expr::apps(
            Expr::const_str_levels("Prod.fst", lvls.clone()),
            [alpha.clone(), list_alpha.clone(), Expr::bvar(0)],
        );
        let snd_p = Expr::apps(
            Expr::const_str_levels("Prod.snd", lvls.clone()),
            [alpha.clone(), list_alpha.clone(), Expr::bvar(0)],
        );
        let inr_arm = Expr::lam(
            BinderInfo::Default,
            prod_a_list.clone(),
            Expr::apps(
                Expr::const_str_levels("List.cons", vec![Level::zero()]),
                [alpha.clone(), fst_p, snd_p],
            ),
        );
        // Inside `λ(c)`: c=bvar0. Sum.rec.{1,0,0} (List α : Sort 1).
        let body = Expr::apps(
            Expr::const_str_levels(
                "Sum.rec",
                vec![Level::succ(Level::zero()), Level::zero(), Level::zero()],
            ),
            [
                unit.clone(),
                prod_a_list.clone(),
                motive,
                inl_arm,
                inr_arm,
                Expr::bvar(0),
            ],
        );
        Ok(Some(Expr::lam(BinderInfo::Default, sum_shape, body)))
    }

    /// Embed the **list BNF initial-algebra fold** `List.list.ctor_fold_list :
    /// (unit + 'a×'b ⇒ 'b) ⇒ 'a list ⇒ 'b`. HOL defines
    /// `ctor_fold_list ≡ λs. SOME f. mor_list UNIV ctor_list UNIV s f` — the unique
    /// algebra morphism from the initial algebra `(list, ctor_list)` to `(b, s)`,
    /// picked by Hilbert choice over the BNF morphism relation. By the BNF
    /// **initiality theorem** that unique morphism *is* the structural fold, so the
    /// faithful image is exactly clean's `List.rec` over the algebra `s` (which
    /// packages the nil value as `s (Inl ())` and the cons combiner as
    /// `λx ih. s (Inr (x, ih))`):
    /// ```text
    /// λ(s:Sum Unit (Prod α β) → β)(t:List α).
    ///   @List.rec.{u₁,0} α (λ_:List α. β)
    ///     (s (@Sum.inl Unit (Prod α β) Unit.unit))
    ///     (λ(x:α)(xs:List α)(ih:β). s (@Sum.inr Unit (Prod α β) (@Prod.mk α β x ih)))
    ///     t
    /// ```
    /// This is the genuine fold — `ctor_fold_list s [] ⟶ s (Inl ())`,
    /// `ctor_fold_list s (x#xs) ⟶ s (Inr (x, ctor_fold_list s xs))` by iota — and it
    /// is **definitionally equal** to `map`'s `List.rec` image (verified: the
    /// `map_def` axiom `map ≡ λf. ctor_fold_list (ctor_list ∘ map_pre_list f id)`
    /// closes by `Eq.refl`). `α` (source element), `β` (result), and the motive
    /// universe `u₁` are read off the const type. Kernel re-checked. Returns `None`
    /// on an unexpected shape.
    pub(crate) fn embed_ctor_fold_list(
        &mut self,
        t: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        // t = (unit + 'a×'b ⇒ 'b) ⇒ ('a list ⇒ 'b).
        let Some((s_ty, rest)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((src_ty, beta_ty)) = fun_split(rest) else {
            return Ok(None);
        };
        // src = 'a list; read α.
        let IsaType::Type { n: ln, a: la } = src_ty else {
            return Ok(None);
        };
        if ln != "List.list" || la.len() != 1 {
            return Ok(None);
        }
        let alpha = self.embed_type(&la[0])?;
        let beta = self.embed_type(beta_ty)?;
        let s_clean = self.embed_type(s_ty)?;
        let lvls = vec![Level::zero(), Level::zero()];
        let unit = Expr::const_str("Unit");
        let list_alpha = Expr::app(
            Expr::const_str_levels("List", vec![Level::zero()]),
            alpha.clone(),
        );
        let prod_a_b = Expr::apps(
            Expr::const_str_levels("Prod", lvls.clone()),
            [alpha.clone(), beta.clone()],
        );
        // motive universe u₁: Prop (Sort 0) when β is Prop, else Sort 1.
        let u1 = if matches!(beta.kind(), clean_kernel::expr::ExprKind::Sort(l) if l.is_zero()) {
            Level::zero()
        } else {
            Level::succ(Level::zero())
        };
        let motive = Expr::lam(BinderInfo::Default, list_alpha.clone(), beta.clone());
        // nil case: `s (@Sum.inl Unit (Prod α β) Unit.unit)`. Inside `λ(s)(t)`: s=bvar1.
        let inl_unit = Expr::apps(
            Expr::const_str_levels("Sum.inl", lvls.clone()),
            [unit.clone(), prod_a_b.clone(), Expr::const_str("Unit.unit")],
        );
        let nil_case = Expr::app(Expr::bvar(1), inl_unit);
        // cons case: `λ(x:α)(xs:List α)(ih:β). s (@Sum.inr Unit (Prod α β) (@Prod.mk α β x ih))`.
        // Inside `λ(s)(t)(x)(xs)(ih)`: s=bvar4, x=bvar2, ih=bvar0.
        let pair_x_ih = Expr::apps(
            Expr::const_str_levels("Prod.mk", lvls.clone()),
            [alpha.clone(), beta.clone(), Expr::bvar(2), Expr::bvar(0)],
        );
        let inr_pair = Expr::apps(
            Expr::const_str_levels("Sum.inr", lvls.clone()),
            [unit.clone(), prod_a_b.clone(), pair_x_ih],
        );
        let cons_case = Expr::lam(
            BinderInfo::Default,
            alpha.clone(),
            Expr::lam(
                BinderInfo::Default,
                list_alpha.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    beta.clone(),
                    Expr::app(Expr::bvar(4), inr_pair),
                ),
            ),
        );
        // Inside `λ(s)(t)`: t=bvar0.
        let body = Expr::apps(
            Expr::const_str_levels("List.rec", vec![u1, Level::zero()]),
            [alpha.clone(), motive, nil_case, cons_case, Expr::bvar(0)],
        );
        Ok(Some(Expr::lam(
            BinderInfo::Default,
            s_clean,
            Expr::lam(BinderInfo::Default, list_alpha, body),
        )))
    }

    /// Embed the **pre-list shape-functor map** `List.pre_list.list.map_pre_list :
    /// ('a⇒'c) ⇒ ('b⇒'d) ⇒ (unit + 'a×'b) ⇒ (unit + 'c×'d)`. HOL's
    /// `map_pre_list ≡ λf1 f2. id_bnf ∘ map_sum id (map_prod f1 f2) ∘ id_bnf`; since
    /// `id_bnf = id`, this is just `map_sum id (map_prod f1 f2)`. We build it
    /// directly over `Sum.rec`/`Prod`:
    /// ```text
    /// λ(f1:α→γ)(f2:β→δ)(c:Sum Unit (Prod α β)).
    ///   @Sum.rec.{1,0,0} Unit (Prod α β) (λ_. Sum Unit (Prod γ δ))
    ///     (λu:Unit. @Sum.inl Unit (Prod γ δ) u)
    ///     (λp:Prod α β. @Sum.inr Unit (Prod γ δ) (@Prod.mk γ δ (f1 (fst p)) (f2 (snd p))))
    ///     c
    /// ```
    /// `α,β,γ,δ` read off the const type; kernel re-checked. This closes
    /// `map_def`/`set_def` whose RHS route through `map_pre_list`. Returns `None` on
    /// an unexpected shape.
    pub(crate) fn embed_map_pre_list(
        &mut self,
        t: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        // t = ('a⇒'c) ⇒ (('b⇒'d) ⇒ ((unit + 'a×'b) ⇒ (unit + 'c×'d))).
        let Some((f1_ty, rest)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((f2_ty, rest2)) = fun_split(rest) else {
            return Ok(None);
        };
        let Some((_src_ty, _dst_ty)) = fun_split(rest2) else {
            return Ok(None);
        };
        let Some((a_ty, c_ty)) = fun_split(f1_ty) else {
            return Ok(None);
        };
        let Some((b_ty, d_ty)) = fun_split(f2_ty) else {
            return Ok(None);
        };
        let alpha = self.embed_type(a_ty)?;
        let gamma = self.embed_type(c_ty)?;
        let beta = self.embed_type(b_ty)?;
        let delta = self.embed_type(d_ty)?;
        let lvls = vec![Level::zero(), Level::zero()];
        let unit = Expr::const_str("Unit");
        let prod = |l: &Expr, r: &Expr| {
            Expr::apps(
                Expr::const_str_levels("Prod", lvls.clone()),
                [l.clone(), r.clone()],
            )
        };
        let sum = |l: &Expr, r: &Expr| {
            Expr::apps(
                Expr::const_str_levels("Sum", lvls.clone()),
                [l.clone(), r.clone()],
            )
        };
        let prod_ab = prod(&alpha, &beta);
        let prod_cd = prod(&gamma, &delta);
        let sum_in = sum(&unit, &prod_ab);
        let sum_out = sum(&unit, &prod_cd);
        let f1_clean = Expr::arrow(alpha.clone(), gamma.clone());
        let f2_clean = Expr::arrow(beta.clone(), delta.clone());
        let motive = Expr::lam(BinderInfo::Default, sum_in.clone(), sum_out.clone());
        // inl arm: `λu:Unit. @Sum.inl Unit (Prod γ δ) u`. u=bvar0.
        let inl_arm = Expr::lam(
            BinderInfo::Default,
            unit.clone(),
            Expr::apps(
                Expr::const_str_levels("Sum.inl", lvls.clone()),
                [unit.clone(), prod_cd.clone(), Expr::bvar(0)],
            ),
        );
        // inr arm: `λp:Prod α β. @Sum.inr Unit (Prod γ δ) (@Prod.mk γ δ (f1 (fst p)) (f2 (snd p)))`.
        // Inside `λ(f1)(f2)(c)(p)`: f1=bvar3, f2=bvar2, p=bvar0.
        let fst_p = Expr::apps(
            Expr::const_str_levels("Prod.fst", lvls.clone()),
            [alpha.clone(), beta.clone(), Expr::bvar(0)],
        );
        let snd_p = Expr::apps(
            Expr::const_str_levels("Prod.snd", lvls.clone()),
            [alpha.clone(), beta.clone(), Expr::bvar(0)],
        );
        let mapped_pair = Expr::apps(
            Expr::const_str_levels("Prod.mk", lvls.clone()),
            [
                gamma.clone(),
                delta.clone(),
                Expr::app(Expr::bvar(3), fst_p),
                Expr::app(Expr::bvar(2), snd_p),
            ],
        );
        let inr_arm = Expr::lam(
            BinderInfo::Default,
            prod_ab.clone(),
            Expr::apps(
                Expr::const_str_levels("Sum.inr", lvls.clone()),
                [unit.clone(), prod_cd.clone(), mapped_pair],
            ),
        );
        // Inside `λ(f1)(f2)(c)`: c=bvar0.
        let body = Expr::apps(
            Expr::const_str_levels(
                "Sum.rec",
                vec![Level::succ(Level::zero()), Level::zero(), Level::zero()],
            ),
            [
                unit.clone(),
                prod_ab.clone(),
                motive,
                inl_arm,
                inr_arm,
                Expr::bvar(0),
            ],
        );
        Ok(Some(Expr::lam(
            BinderInfo::Default,
            f1_clean,
            Expr::lam(
                BinderInfo::Default,
                f2_clean,
                Expr::lam(BinderInfo::Default, sum_in, body),
            ),
        )))
    }
}
