// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Companion facts to the keystone identity: the NONNEGATIVITY of the dyadic
//! square root, `NNReal.ofRat 0 _ ≤ NNReal.sqrtRat x`.

use super::IdentityConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// `NNReal.zero_le_sqrtRat : ∀ x, NNReal.le (NNReal.ofRat 0 (le_refl 0))
    ///                                          (NNReal.sqrtRat x)`.
    ///
    /// `NNReal.le (mk(const 0))(mk(sqrtSeq x))` ι-reduces (two `Quot.lift`
    /// steps) to `CauSeq.le (const(NNRat.ofRat 0))(sqrtSeq x)`, whose leaf at
    /// `(ε, n)` is `val(0) < val(dyadicApproxNN x n) + ε`, i.e. (defeq)
    /// `0 < a_n + ε`. Witness `N := 0`; `0 ≤ a_n` (`zero_le_dyadicApprox`) and
    /// `a_n < a_n+ε` give `0 < a_n+ε` by `lt_of_le_of_lt`.
    pub(crate) fn register_zero_le_sqrt_rat(&mut self, c: &IdentityConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.zero_le_sqrtRat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
        let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
        let zero_le_a = Expr::const_(Name::from_string("Rat.zero_le_dyadicApprox"), vec![]);
        let exists_intro = Expr::const_(
            Name::from_string("Exists.intro"),
            vec![Level::succ(Level::zero())],
        );

        // The nonneg `NNRat` zero: NNRat.ofRat 0 (le_refl 0).
        let h0_zero = Expr::app(le_refl.clone(), c.rat_zero.clone()); // 0 ≤ 0
        let nn_zero = Expr::apps(
            c.nnrat_of_rat.clone(),
            [c.rat_zero.clone(), h0_zero.clone()],
        );
        let of_zero = Expr::apps(
            c.nnreal_of_rat.clone(),
            [c.rat_zero.clone(), h0_zero.clone()],
        );

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let sx = Expr::app(c.nnreal_sqrt.clone(), x.clone());
            let concl = Expr::apps(nnle.clone(), [of_zero.clone(), sx]);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), concl))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());

            // Proof of `CauSeq.le (const nn_zero)(sqrtSeq x)`:
            //   fun ε hpos => Exists.intro Nat pred 0 witness.
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
            let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

            // pred N := ∀ n, N≤n → 0 < a_n + ε  (defeq to val(0) < val(seq..)+ε).
            let pred = |bb: &EnvDeclBuilder| -> Expr {
                let mut pn = EnvDeclBuilder::child_of(bb);
                let (cap_id, cap) = pn.fresh_local(c.nat.clone());
                let inner = {
                    let mut pi = EnvDeclBuilder::child_of(&pn);
                    let (n_id, n) = pi.fresh_local(c.nat.clone());
                    let hle_ty = c.nat_le(cap.clone(), n.clone());
                    let (hle_id, _hle) = pi.fresh_local(hle_ty.clone());
                    let a = c.approx(&x, n.clone());
                    let concl = c.lt(c.rat_zero.clone(), c.add(a.clone(), eps.clone()));
                    let e = pi.mk_pi(hle_id, BinderInfo::Default, hle_ty, concl);
                    let e = pi.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
                    pi.finish_child(e)
                };
                pn.finish_child(pn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner))
            };

            // witness : ∀ n, 0≤n → 0 < a_n + ε.
            let witness = {
                let mut wb = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = wb.fresh_local(c.nat.clone());
                let hle_ty = c.nat_le(c.nat_zero.clone(), n.clone());
                let (hle_id, _hle) = wb.fresh_local(hle_ty.clone());
                let a = c.approx(&x, n.clone());
                let a_eps = c.add(a.clone(), eps.clone());
                // 0 ≤ a_n.
                let h0a = Expr::apps(zero_le_a.clone(), [x.clone(), n.clone()]);
                // a_n < a_n + ε  (add_lt_add_left 0 ε a_n hpos : a_n+0 < a_n+ε; transport).
                let h_an_lt = c.x_lt_x_add_eps(&wb, &a, &eps, hpos.clone());
                // 0 < a_n + ε  (lt_of_le_of_lt 0 a_n (a_n+ε) (0≤a_n)(a_n<a_n+ε)).
                let body = c.lt_of_le_of_lt(c.rat_zero.clone(), a.clone(), a_eps, h0a, h_an_lt);
                let e = wb.mk_lam(hle_id, BinderInfo::Default, hle_ty, body);
                let e = wb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
                wb.finish_child(e)
            };

            let intro = Expr::apps(
                exists_intro.clone(),
                [c.nat.clone(), pred(&b), c.nat_zero.clone(), witness],
            );
            let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            // Bind x. The body has type CauSeq.le (const nn_zero)(sqrtSeq x),
            // defeq to NNReal.le (ofRat 0)(sqrtRat x) — kernel reconciles.
            let _ = nn_zero;
            b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
