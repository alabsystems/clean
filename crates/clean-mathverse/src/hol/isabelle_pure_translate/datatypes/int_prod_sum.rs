// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Ctx` embedding methods for the Int-quotient bridge, `Prod`/`Sum`/`Option`
//! constructors & case combinators and `map_fun`: `int_abs_integ`,
//! `int_rep_integ`, `embed_pair`, `embed_case_prod`, `sum_elems`,
//! `embed_sum_ctor`, `embed_case_sum`, `embed_option_none`, `embed_option_some`,
//! `embed_case_option`, `embed_map_fun`. Moved verbatim from the original
//! single-file `datatypes` module; behaviour is byte-identical.

use clean_kernel::level::Level;
use clean_kernel::{BinderInfo, Expr};

use super::super::super::isabelle_pure::IsaType;
use super::super::*;

impl Ctx {
    /// The HOL int-quotient abstraction `Int.Abs_Integ : nat×nat ⇒ int`, bridged
    /// to clean's `Int`. The denoted integer of the representative `(a,b)` is the
    /// difference `a − b`, which clean's prelude computes directly with
    /// `Int.subNatNat : Nat → Nat → Int`. So
    /// `Abs_Integ = λp:Prod Nat Nat. Int.subNatNat (Prod.fst p) (Prod.snd p)`.
    /// Both `Prod` arguments are `Nat` (level 0), matching the prelude `Prod.{0,0}`.
    pub(crate) fn int_abs_integ(&self) -> Expr {
        let nat = Expr::const_str("Nat");
        let prod_nat_nat = Expr::apps(
            Expr::const_str_levels("Prod", vec![Level::zero(), Level::zero()]),
            [nat.clone(), nat.clone()],
        );
        let levels = vec![Level::zero(), Level::zero()];
        // p = bvar 0.
        let fst = Expr::apps(
            Expr::const_str_levels("Prod.fst", levels.clone()),
            [nat.clone(), nat.clone(), Expr::bvar(0)],
        );
        let snd = Expr::apps(
            Expr::const_str_levels("Prod.snd", levels),
            [nat.clone(), nat.clone(), Expr::bvar(0)],
        );
        let body = Expr::apps(Expr::const_str("Int.subNatNat"), [fst, snd]);
        Expr::lam(BinderInfo::Default, prod_nat_nat, body)
    }

    /// The HOL int-quotient representative `Int.Rep_Integ : int ⇒ nat×nat`, bridged
    /// to clean's `Int`. We pick the *canonical* representative of each class:
    /// `ofNat n ↦ (n, 0)` and `negSucc n ↦ (0, n+1)` (so `a − b` recovers the
    /// integer). This is exactly clean `Int.rec` with the two constructor arms:
    /// `λi:Int. @Int.rec.{1} (λ_:Int. Prod Nat Nat)
    ///            (λn:Nat. Prod.mk n 0) (λn:Nat. Prod.mk 0 (Nat.succ n)) i`.
    pub(crate) fn int_rep_integ(&self) -> Expr {
        let int = Expr::const_str("Int");
        let nat = Expr::const_str("Nat");
        let nat_zero = Expr::const_str("Nat.zero");
        let prod_levels = vec![Level::zero(), Level::zero()];
        let prod_nat_nat = Expr::apps(
            Expr::const_str_levels("Prod", prod_levels.clone()),
            [nat.clone(), nat.clone()],
        );
        // motive : Int → Sort 1 (Prod Nat Nat lives in Type = Sort 1).
        let motive = Expr::lam(BinderInfo::Default, int.clone(), prod_nat_nat.clone());
        let mk = |a: Expr, b: Expr| {
            Expr::apps(
                Expr::const_str_levels("Prod.mk", prod_levels.clone()),
                [nat.clone(), nat.clone(), a, b],
            )
        };
        // ofNat arm: λn:Nat. (n, 0)   — n is bvar 0.
        let of_nat_arm = Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            mk(Expr::bvar(0), nat_zero.clone()),
        );
        // negSucc arm: λn:Nat. (0, Suc n)   — n is bvar 0.
        let neg_succ_arm = Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            mk(
                nat_zero.clone(),
                Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
            ),
        );
        // λi:Int. Int.rec.{1} motive of_nat_arm neg_succ_arm i   — i is bvar 0.
        let body = Expr::apps(
            Expr::const_str_levels("Int.rec", vec![Level::succ(Level::zero())]),
            [motive, of_nat_arm, neg_succ_arm, Expr::bvar(0)],
        );
        Expr::lam(BinderInfo::Default, int, body)
    }

    /// Embed `Product_Type.Pair : 'a ⇒ 'b ⇒ 'a×'b` to clean's `Prod.mk` at the
    /// instantiated element types `'a`, `'b` (read off the constant's HOL type
    /// `'a ⇒ 'b ⇒ prod['a,'b]`). Returns `None` if the type is not that shape.
    pub(crate) fn embed_pair(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = 'a ⇒ ('b ⇒ prod['a,'b]).
        let Some((a_ty, rest)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((b_ty, _res)) = fun_split(rest) else {
            return Ok(None);
        };
        let a = self.embed_type(a_ty)?;
        let b = self.embed_type(b_ty)?;
        Ok(Some(Expr::apps(
            Expr::const_str_levels("Prod.mk", vec![Level::zero(), Level::zero()]),
            [a, b],
        )))
    }

    /// Embed `Product_Type.prod.case_prod : ('a⇒'b⇒'c) ⇒ 'a×'b ⇒ 'c` to
    /// `λ(f:'a→'b→'c)(p:Prod 'a 'b). f (Prod.fst p) (Prod.snd p)`. The element
    /// types `'a`, `'b` are read off the constant's instantiated HOL type. Returns
    /// `None` if the type is not the expected shape (caller falls back to a param).
    pub(crate) fn embed_case_prod(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = ('a ⇒ ('b ⇒ 'c)) ⇒ (prod['a,'b] ⇒ 'c).
        let Some((f_ty, _rest)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((a_ty, f_rest)) = fun_split(f_ty) else {
            return Ok(None);
        };
        let Some((b_ty, c_ty)) = fun_split(f_rest) else {
            return Ok(None);
        };
        let a = self.embed_type(a_ty)?;
        let b = self.embed_type(b_ty)?;
        let c = self.embed_type(c_ty)?;
        let prod_levels = vec![Level::zero(), Level::zero()];
        let prod_ab = Expr::apps(
            Expr::const_str_levels("Prod", prod_levels.clone()),
            [a.clone(), b.clone()],
        );
        let f_clean = Expr::arrow(a.clone(), Expr::arrow(b.clone(), c));
        // Inside `λ(f)(p).`, f = bvar 1, p = bvar 0.
        let fst = Expr::apps(
            Expr::const_str_levels("Prod.fst", prod_levels.clone()),
            [a.clone(), b.clone(), Expr::bvar(0)],
        );
        let snd = Expr::apps(
            Expr::const_str_levels("Prod.snd", prod_levels),
            [a, b, Expr::bvar(0)],
        );
        let app = Expr::apps(Expr::bvar(1), [fst, snd]);
        Ok(Some(Expr::lam(
            BinderInfo::Default,
            f_clean,
            Expr::lam(BinderInfo::Default, prod_ab, app),
        )))
    }

    /// Extract the two element types of a HOL `Sum_Type.sum['a,'b]` type, embedded
    /// to clean (`α`, `β`). Returns `None` if the type is not a binary `sum`.
    pub(crate) fn sum_elems(
        &mut self,
        sum_ty: &IsaType,
    ) -> Result<Option<(Expr, Expr)>, TranslateError> {
        let IsaType::Type { n, a } = sum_ty else {
            return Ok(None);
        };
        if n != "Sum_Type.sum" || a.len() != 2 {
            return Ok(None);
        }
        let alpha = self.embed_type(&a[0])?;
        let beta = self.embed_type(&a[1])?;
        Ok(Some((alpha, beta)))
    }

    /// Embed a HOL sum constructor (`Sum_Type.Inl : 'a ⇒ 'a+'b`, or
    /// `Sum_Type.Inr : 'b ⇒ 'a+'b`) to the clean prelude constructor `ctor`
    /// (`"Sum.inl"` / `"Sum.inr"`) with its implicit element type args supplied
    /// explicitly: `@<ctor>.{0,0} α β : <dom> → Sum α β`. The element types are
    /// read off the sum result type. Returns `None` if the constant type is not a
    /// `'_ ⇒ sum['a,'b]` arrow (then the caller keeps an opaque param).
    pub(crate) fn embed_sum_ctor(
        &mut self,
        t: &IsaType,
        ctor: &str,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some((_dom, sum_ty)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((alpha, beta)) = self.sum_elems(sum_ty)? else {
            return Ok(None);
        };
        Ok(Some(Expr::apps(
            Expr::const_str_levels(ctor, vec![Level::zero(), Level::zero()]),
            [alpha, beta],
        )))
    }

    /// Embed `Sum_Type.sum.case_sum : ('a⇒'c) ⇒ ('b⇒'c) ⇒ 'a+'b ⇒ 'c` to a bare
    /// clean lambda over the prelude `Sum.rec` with a constant motive `λ_:Sum α β. γ`
    /// (sum is non-recursive, so the recursor arms ignore no recursive value):
    /// ```text
    /// λ(f:α→γ)(g:β→γ)(s:Sum α β).
    ///   @Sum.rec.{w,0,0} (λ_:Sum α β. γ) f g s
    /// ```
    /// `α`,`β`,`γ` are read off the constant's instantiated HOL type; the motive
    /// level `w` is `0` when `γ : Prop` and `1` otherwise (the same constant-motive
    /// pattern as `embed_case_nat`). Returns `None` if the type is not the expected
    /// shape (then the caller keeps an opaque param, honestly typed).
    pub(crate) fn embed_case_sum(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = ('a⇒'c) ⇒ (('b⇒'c) ⇒ (sum['a,'b] ⇒ 'c)).
        let Some((f_ty, rest)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((g_ty, rest2)) = fun_split(rest) else {
            return Ok(None);
        };
        let Some((sum_ty, c_ty)) = fun_split(rest2) else {
            return Ok(None);
        };
        // α from f = 'a⇒'c, β from g = 'b⇒'c, γ = 'c.
        let Some((a_ty, _c1)) = fun_split(f_ty) else {
            return Ok(None);
        };
        let Some((b_ty, _c2)) = fun_split(g_ty) else {
            return Ok(None);
        };
        let alpha = self.embed_type(a_ty)?;
        let beta = self.embed_type(b_ty)?;
        let gamma = self.embed_type(c_ty)?;
        let _ = sum_ty; // result type already pins α,β; re-deriving would be redundant.
        let w = if matches!(gamma.kind(), clean_kernel::expr::ExprKind::Sort(l) if l.is_zero()) {
            Level::zero()
        } else {
            Level::succ(Level::zero())
        };
        let sum_ab = Expr::apps(
            Expr::const_str_levels("Sum", vec![Level::zero(), Level::zero()]),
            [alpha.clone(), beta.clone()],
        );
        // Constant motive `λ_:Sum α β. γ`.
        let motive = Expr::lam(BinderInfo::Default, sum_ab.clone(), gamma.clone());
        let f_clean = Expr::arrow(alpha.clone(), gamma.clone());
        let g_clean = Expr::arrow(beta.clone(), gamma.clone());
        // Inside `λ(f)(g)(s).` operands: f=bvar2, g=bvar1, s=bvar0. `Sum.rec`'s
        // leading binders are the implicit `{α}{β}{motive}` followed by the two
        // case arms and the major premise, so we supply α, β, motive explicitly.
        let body = Expr::apps(
            Expr::const_str_levels("Sum.rec", vec![w, Level::zero(), Level::zero()]),
            [
                alpha.clone(),
                beta.clone(),
                motive,
                Expr::bvar(2), // inl_case = f
                Expr::bvar(1), // inr_case = g
                Expr::bvar(0), // major = s
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

    /// Embed `Option.option.None : 'a option`  →  `@Option.none.{0} α`, reading the
    /// element type `α` off the constant's `option['a]` type. Returns `None` if the
    /// type is not `option['a]`.
    pub(crate) fn embed_option_none(
        &mut self,
        t: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        let IsaType::Type { n, a } = t else {
            return Ok(None);
        };
        if n != "Option.option" || a.len() != 1 {
            return Ok(None);
        }
        let alpha = self.embed_type(&a[0])?;
        Ok(Some(Expr::app(
            Expr::const_str_levels("Option.none", vec![Level::zero()]),
            alpha,
        )))
    }

    /// Embed `Option.option.Some : 'a ⇒ 'a option`  →  `@Option.some.{0} α`, reading
    /// `α` off the constant's `'a ⇒ option['a]` arrow. Returns `None` otherwise.
    pub(crate) fn embed_option_some(
        &mut self,
        t: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some((dom, opt_ty)) = fun_split(t) else {
            return Ok(None);
        };
        // Sanity: result must be option['a] with 'a = dom.
        let IsaType::Type { n, a } = opt_ty else {
            return Ok(None);
        };
        if n != "Option.option" || a.len() != 1 {
            return Ok(None);
        }
        let alpha = self.embed_type(dom)?;
        Ok(Some(Expr::app(
            Expr::const_str_levels("Option.some", vec![Level::zero()]),
            alpha,
        )))
    }

    /// Embed `Option.option.case_option : 'b ⇒ ('a⇒'b) ⇒ 'a option ⇒ 'b` to a bare
    /// clean lambda over `Option.rec` with a constant motive `λ_:Option α. β`
    /// (option is non-recursive):
    /// ```text
    /// λ(z:β)(f:α→β)(o:Option α).
    ///   @Option.rec.{w,0} (λ_:Option α. β) z f o
    /// ```
    /// HOL's `case None ⇒ z | Some a ⇒ f a`, matching `Option.rec`'s `none_case`
    /// then `some_case` order. `α`,`β` and the motive level `w` are read off the
    /// constant type. Returns `None` on an unexpected shape.
    pub(crate) fn embed_case_option(
        &mut self,
        t: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        // t = 'b ⇒ (('a⇒'b) ⇒ (option['a] ⇒ 'b)).
        let Some((z_ty, rest)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((f_ty, rest2)) = fun_split(rest) else {
            return Ok(None);
        };
        let Some((opt_ty, _b2)) = fun_split(rest2) else {
            return Ok(None);
        };
        // α from f = 'a⇒'b; β = 'b (= z_ty).
        let Some((a_ty, _b1)) = fun_split(f_ty) else {
            return Ok(None);
        };
        let alpha = self.embed_type(a_ty)?;
        let beta = self.embed_type(z_ty)?;
        let _ = opt_ty;
        let w = if matches!(beta.kind(), clean_kernel::expr::ExprKind::Sort(l) if l.is_zero()) {
            Level::zero()
        } else {
            Level::succ(Level::zero())
        };
        let option_a = Expr::app(
            Expr::const_str_levels("Option", vec![Level::zero()]),
            alpha.clone(),
        );
        let motive = Expr::lam(BinderInfo::Default, option_a.clone(), beta.clone());
        let f_clean = Expr::arrow(alpha.clone(), beta.clone());
        // Inside `λ(z)(f)(o).` operands: z=bvar2, f=bvar1, o=bvar0. `Option.rec`'s
        // leading binders are the implicit `{α}{motive}` then the two case arms and
        // the major premise, so we supply α and motive explicitly.
        let body = Expr::apps(
            Expr::const_str_levels("Option.rec", vec![w, Level::zero()]),
            [
                alpha.clone(),
                motive,
                Expr::bvar(2), // none_case = z
                Expr::bvar(1), // some_case = f
                Expr::bvar(0), // major = o
            ],
        );
        Ok(Some(Expr::lam(
            BinderInfo::Default,
            beta,
            Expr::lam(
                BinderInfo::Default,
                f_clean,
                Expr::lam(BinderInfo::Default, option_a, body),
            ),
        )))
    }

    /// Embed `Fun.map_fun : ('a⇒'b) ⇒ ('c⇒'d) ⇒ ('b⇒'c) ⇒ ('a⇒'d)` to
    /// `λ(g:'a→'b)(h:'c→'d)(f:'b→'c)(x:'a). h (f (g x))` (HOL's
    /// `map_fun g h f = h ∘ f ∘ g`). The four element types are read off the
    /// constant's instantiated HOL type. Returns `None` if the type is not the
    /// expected shape (caller falls back to an opaque param, honestly typed).
    pub(crate) fn embed_map_fun(&mut self, t: &IsaType) -> Result<Option<Expr>, TranslateError> {
        // t = ('a⇒'b) ⇒ (('c⇒'d) ⇒ (('b⇒'c) ⇒ ('a⇒'d))).
        let Some((gty, r1)) = fun_split(t) else {
            return Ok(None);
        };
        let Some((a_ty, b_ty)) = fun_split(gty) else {
            return Ok(None);
        };
        let Some((hty, r2)) = fun_split(r1) else {
            return Ok(None);
        };
        let Some((c_ty, d_ty)) = fun_split(hty) else {
            return Ok(None);
        };
        let Some((_fty, _r3)) = fun_split(r2) else {
            return Ok(None);
        };
        let (a, b) = (self.embed_type(a_ty)?, self.embed_type(b_ty)?);
        let (c, d) = (self.embed_type(c_ty)?, self.embed_type(d_ty)?);
        let g_clean = Expr::arrow(a.clone(), b.clone());
        let h_clean = Expr::arrow(c.clone(), d.clone());
        let f_clean = Expr::arrow(b.clone(), c.clone());
        // Inside `λ(g)(h)(f)(x).` g=bvar3, h=bvar2, f=bvar1, x=bvar0.
        let gx = Expr::app(Expr::bvar(3), Expr::bvar(0));
        let fgx = Expr::app(Expr::bvar(1), gx);
        let hfgx = Expr::app(Expr::bvar(2), fgx);
        Ok(Some(Expr::lam(
            BinderInfo::Default,
            g_clean,
            Expr::lam(
                BinderInfo::Default,
                h_clean,
                Expr::lam(
                    BinderInfo::Default,
                    f_clean,
                    Expr::lam(BinderInfo::Default, a, hfgx),
                ),
            ),
        )))
    }
}
