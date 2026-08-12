// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the `p ≤ q` two-sided dyadic bounds
//! (Stage B3, sqrt run #4, rung 6f).
//!
//! # Why this module exists
//!
//! The dyadic `IsCauchy` proof (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.5 rung 6) compares two
//! indices `m, n ≥ N` by anchoring both to `N`. That needs the monotone +
//! telescoping bounds in the `≤`-indexed form (`p ≤ q → …`), which we obtain
//! from the gap-indexed lemmas (`Nat.add n d`) via the existential
//! `Nat.exists_eq_add_of_le`.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Nat.exists_eq_add_of_le : ∀ p q, Nat.le p q → ∃ d, Eq Nat q (Nat.add p d)`.
//! - `Rat.dyadicApprox_le_add : ∀ x n d,
//!       Rat.le (Rat.dyadicApprox x n) (Rat.dyadicApprox x (Nat.add n d))`.
//!   (monotone over the gap)
//! - `Rat.dyadicApprox_mono : ∀ x p q, Nat.le p q →
//!       Rat.le (Rat.dyadicApprox x p) (Rat.dyadicApprox x q)`.
//! - `Rat.dyadicApprox_le_add_inv_of_le : ∀ x p q, Nat.le p q →
//!       Rat.le (Rat.dyadicApprox x q)
//!              (Rat.add (Rat.dyadicApprox x p) (inv (ofNat 2^p)))`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Universe note
//!
//! `Nat.le.rec` / `Nat.rec` Prop-motives are universe 0. `Exists`/`Exists.elim`
//! over `Nat : Sort 1` are universe 1. `Eq`/`Eq.subst`/`congrArg` over
//! `Nat`/`Rat : Sort 1` are universe 1.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for the `≤`-indexed bounds rung.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) struct LeConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_pow: Expr,
    nat_le: Expr,
    #[cfg(test)]
    nat_le_refl: Expr,
    #[cfg(test)]
    nat_le_step: Expr,
    nat_le_rec: Expr,
    nat_rec_prop: Expr,
    rat: Expr,
    rat_add: Expr,
    #[cfg(test)]
    rat_mul: Expr,
    rat_inv: Expr,
    rat_le: Expr,
    rat_ofnat: Expr,
    rat_dyadic_approx: Expr,
    rat_dyadic_approx_le_succ: Expr,
    rat_dyadic_approx_le_add: Expr,
    rat_dyadic_approx_le_add_inv: Expr,
    rat_le_refl: Expr,
    rat_le_trans: Expr,
    nat_exists_eq_add_of_le: Expr,
    eq_nat: Expr,
    eq_nat_refl: Expr,
    eq_nat_symm: Expr,
    eq_rat_subst: Expr,
    congr_arg_nat_nat: Expr,
    congr_arg_nat_rat: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
}

impl LeConsts {
    pub(crate) fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_add: k("Nat.add"),
            nat_pow: k("Nat.pow"),
            nat_le: k("Nat.le"),
            #[cfg(test)]
            nat_le_refl: k("Nat.le.refl"),
            #[cfg(test)]
            nat_le_step: k("Nat.le.step"),
            nat_le_rec: k("Nat.le.rec"),
            nat_rec_prop: Expr::const_(Name::from_string("Nat.rec"), vec![l0]),
            rat: k("Rat"),
            rat_add: k("Rat.add"),
            #[cfg(test)]
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_le: k("Rat.le"),
            rat_ofnat: k("Rat.ofNat"),
            rat_dyadic_approx: k("Rat.dyadicApprox"),
            rat_dyadic_approx_le_succ: k("Rat.dyadicApprox_le_succ"),
            rat_dyadic_approx_le_add: k("Rat.dyadicApprox_le_add"),
            rat_dyadic_approx_le_add_inv: k("Rat.dyadicApprox_le_add_inv"),
            rat_le_refl: k("Rat.le_refl"),
            rat_le_trans: k("Rat.le_trans"),
            nat_exists_eq_add_of_le: k("Nat.exists_eq_add_of_le"),
            eq_nat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_nat_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_nat_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_rat_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg_nat_nat: Expr::const_(
                Name::from_string("congrArg"),
                vec![l1.clone(), l1.clone()],
            ),
            congr_arg_nat_rat: Expr::const_(
                Name::from_string("congrArg"),
                vec![l1.clone(), l1.clone()],
            ),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![l1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn npow2(&self, n: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), n])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn iv(&self, n: Expr) -> Expr {
        self.inv(self.ofnat(self.npow2(n)))
    }
    fn approx(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_approx.clone(), [x.clone(), n])
    }
    fn eq_nat_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_nat.clone(), [self.nat.clone(), a, b])
    }
    fn eq_nat_refl(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_nat_refl.clone(), [self.nat.clone(), a])
    }
    fn eq_nat_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_nat_symm.clone(), [self.nat.clone(), a, b, h])
    }
    /// `@Eq.subst Rat motive a b h_eq h`.
    fn eq_rat_subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_rat_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@congrArg.{1,1} Nat Nat a a' f h : f a = f a'`.
    fn congr_nat_nat(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg_nat_nat.clone(),
            [self.nat.clone(), self.nat.clone(), a, a2, f, h],
        )
    }
    /// `@congrArg.{1,1} Nat Rat a a' f h : f a = f a'`.
    fn congr_nat_rat(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg_nat_rat.clone(),
            [self.nat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, cc, h1, h2])
    }
    fn approx_le_succ(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_approx_le_succ.clone(), [x.clone(), n])
    }
    /// `∃ (d : Nat), p d`  := `@Exists.{1} Nat p`.
    fn exists_nat(&self, pred: Expr) -> Expr {
        Expr::apps(self.exists_c.clone(), [self.nat.clone(), pred])
    }
    /// The predicate `fun d => Eq Nat q (Nat.add p d)`.
    fn add_pred(&self, parent: &EnvDeclBuilder, p: &Expr, q: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (dd_id, dd) = d.fresh_local(self.nat.clone());
        let body = self.eq_nat_ty(q.clone(), self.nadd(p.clone(), dd));
        d.finish_child(d.mk_lam(dd_id, BinderInfo::Default, self.nat.clone(), body))
    }
}

impl Environment {
    /// Register the `≤`-indexed dyadic bounds. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_sqrt_cauchy_le(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_exists()?;
        self.init_nat()?;
        self.init_le()?; // Nat.le, Nat.le.refl, Nat.le.step, Nat.le.rec
        self.init_algebra_nnreal_sqrt_seq()?; // dyadicApprox, ofNat, Nat.pow
        self.init_algebra_nnreal_sqrt_cauchy_mono()?; // dyadicApprox_le_succ
        self.init_algebra_nnreal_sqrt_cauchy_tele()?; // dyadicApprox_le_add_inv
        self.init_rat_quotient_poc()?; // Rat.le_refl, Rat.le_trans

        let c = LeConsts::new();
        self.register_nat_exists_eq_add_of_le(&c)?;
        self.register_dyadic_approx_le_add(&c)?;
        self.register_dyadic_approx_mono(&c)?;
        self.register_dyadic_approx_le_add_inv_of_le(&c)?;
        Ok(())
    }

    /// `Nat.exists_eq_add_of_le : ∀ p q, Nat.le p q → ∃ d, Eq Nat q (Nat.add p d)`.
    fn register_nat_exists_eq_add_of_le(&mut self, c: &LeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.exists_eq_add_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nat.clone());
            let (q_id, q) = b.fresh_local(c.nat.clone());
            let hle = c.nat_le(p.clone(), q.clone());
            let (h_id, _h) = b.fresh_local(hle.clone());
            let concl = c.exists_nat(c.add_pred(&b, &p, &q));
            let e = b.mk_pi(h_id, BinderInfo::Default, hle, concl);
            let e = b.mk_pi(q_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nat.clone());
            let (q_id, q) = b.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(p.clone(), q.clone());
            let (h_id, h) = b.fresh_local(hle_ty.clone());

            // motive : (t : Nat) → Nat.le p t → Prop := fun t _ => ∃ d, t = p+d.
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.nat.clone());
                let hpt = c.nat_le(p.clone(), t.clone());
                let (ht_id, _ht) = mb.fresh_local(hpt.clone());
                let body = c.exists_nat(c.add_pred(&mb, &p, &t));
                let e = mb.mk_lam(ht_id, BinderInfo::Default, hpt, body);
                let e = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), e);
                mb.finish_child(e)
            };

            // refl minor : motive p (Nat.le.refl) = ∃ d, p = p+d.  Witness d=0:
            //   p = p+0 defeq; Exists.intro Nat (add_pred p p) 0 (Eq.refl p).
            let minor_refl = {
                let pred = c.add_pred(&b, &p, &p);
                Expr::apps(
                    c.exists_intro.clone(),
                    [
                        c.nat.clone(),
                        pred,
                        c.nat_zero.clone(),
                        c.eq_nat_refl(p.clone()),
                    ],
                )
            };

            // step minor : {t} → (h:Nat.le p t) → (ih:∃ d, t=p+d) → ∃ d, succ t = p+d.
            let minor_step = {
                let mut sb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = sb.fresh_local(c.nat.clone());
                let hpt = c.nat_le(p.clone(), t.clone());
                let (hpt_id, _hpt) = sb.fresh_local(hpt.clone());
                let ih_ty = c.exists_nat(c.add_pred(&sb, &p, &t));
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

                let succ_t = c.succ(t.clone());
                let goal = c.exists_nat(c.add_pred(&sb, &p, &succ_t));
                let pred_t = c.add_pred(&sb, &p, &t);
                let pred_succ_t = c.add_pred(&sb, &p, &succ_t);

                // elim fn : (d:Nat) → (hd : t = p+d) → ∃ d', succ t = p+d'.
                //   witness succ d: succ t = p + succ d (≡ succ(p+d)); proof
                //   congrArg Nat.succ hd : succ t = succ(p+d) ≡ p+succ d.
                let elim_fn = {
                    let mut eb = EnvDeclBuilder::child_of(&sb);
                    let (d_id, d) = eb.fresh_local(c.nat.clone());
                    let hd_ty = c.eq_nat_ty(t.clone(), c.nadd(p.clone(), d.clone()));
                    let (hd_id, hd) = eb.fresh_local(hd_ty.clone());
                    // congrArg Nat.succ hd : succ t = succ(p+d).
                    let succ_pd = c.succ(c.nadd(p.clone(), d.clone()));
                    let cong = c.congr_nat_nat(
                        t.clone(),
                        c.nadd(p.clone(), d.clone()),
                        c.nat_succ.clone(),
                        hd,
                    );
                    // cong : succ t = succ(p+d).  succ(p+d) ≡ p + succ d defeq, so this
                    // has type (succ t = p + succ d) up to defeq → fits the predicate.
                    let _ = succ_pd;
                    let intro = Expr::apps(
                        c.exists_intro.clone(),
                        [c.nat.clone(), pred_succ_t.clone(), c.succ(d.clone()), cong],
                    );
                    let e = eb.mk_lam(hd_id, BinderInfo::Default, hd_ty, intro);
                    let e = eb.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
                    eb.finish_child(e)
                };
                // @Exists.elim Nat pred_t goal ih elim_fn.
                let body = Expr::apps(
                    c.exists_elim.clone(),
                    [c.nat.clone(), pred_t, goal, ih, elim_fn],
                );

                let e = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let e = sb.mk_lam(hpt_id, BinderInfo::Default, hpt, e);
                let e = sb.mk_lam(t_id, BinderInfo::Implicit, c.nat.clone(), e);
                sb.finish_child(e)
            };

            // @Nat.le.rec p motive minor_refl minor_step q h.
            let rec = Expr::apps(
                c.nat_le_rec.clone(),
                [p.clone(), motive, minor_refl, minor_step, q.clone(), h],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, hle_ty, rec);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.dyadicApprox_le_add : ∀ x n d, le (a_n)(a_(n+d))`.
    /// `Nat.rec` on `d` (n fixed), last-step peel via `dyadicApprox_le_succ`.
    fn register_dyadic_approx_le_add(&mut self, c: &LeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicApprox_le_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let concl = c.le(
                c.approx(&x, n.clone()),
                c.approx(&x, c.nadd(n.clone(), d.clone())),
            );
            let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (d_id, d) = b.fresh_local(c.nat.clone());

            let a_n = c.approx(&x, n.clone());
            // motive : Nat → Prop := fun d => le a_n (a_(n+d)).
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (md_id, md) = mb.fresh_local(c.nat.clone());
                let body = c.le(a_n.clone(), c.approx(&x, c.nadd(n.clone(), md.clone())));
                mb.finish_child(mb.mk_lam(md_id, BinderInfo::Default, c.nat.clone(), body))
            };
            // base : le a_n (a_(n+0)) = le a_n a_n  (a_(n+0) ≡ a_n).
            let base = c.le_refl(a_n.clone());
            // step : ∀ d', le a_n (a_(n+d')) → le a_n (a_(n+succ d')).
            //   a_(n+succ d') ≡ a_(succ(n+d')). dyadicApprox_le_succ x (n+d') :
            //     le (a_(n+d'))(a_(succ(n+d'))).  le_trans.
            let step = {
                let mut sb = EnvDeclBuilder::child_of(&b);
                let (dp_id, dp) = sb.fresh_local(c.nat.clone());
                let a_npd = c.approx(&x, c.nadd(n.clone(), dp.clone()));
                let ih_ty = c.le(a_n.clone(), a_npd.clone());
                let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
                let a_succ_npd = c.approx(&x, c.succ(c.nadd(n.clone(), dp.clone())));
                let hsucc = c.approx_le_succ(&x, c.nadd(n.clone(), dp.clone()));
                let proof = c.le_trans(a_n.clone(), a_npd.clone(), a_succ_npd.clone(), ih, hsucc);
                // proof : le a_n (a_(succ(n+d'))) ≡ le a_n (a_(n+succ d')).
                let e = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
                let e = sb.mk_lam(dp_id, BinderInfo::Default, c.nat.clone(), e);
                sb.finish_child(e)
            };
            let rec = Expr::apps(c.nat_rec_prop.clone(), [motive, base, step, d.clone()]);

            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), rec);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.dyadicApprox_mono : ∀ x p q, Nat.le p q → le (a_p)(a_q)`.
    fn register_dyadic_approx_mono(&mut self, c: &LeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicApprox_mono");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (p_id, p) = b.fresh_local(c.nat.clone());
            let (q_id, q) = b.fresh_local(c.nat.clone());
            let hle = c.nat_le(p.clone(), q.clone());
            let (h_id, _h) = b.fresh_local(hle.clone());
            let concl = c.le(c.approx(&x, p.clone()), c.approx(&x, q.clone()));
            let e = b.mk_pi(h_id, BinderInfo::Default, hle, concl);
            let e = b.mk_pi(q_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (p_id, p) = b.fresh_local(c.nat.clone());
            let (q_id, q) = b.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(p.clone(), q.clone());
            let (h_id, h) = b.fresh_local(hle_ty.clone());

            let a_p = c.approx(&x, p.clone());
            let a_q = c.approx(&x, q.clone());
            // ex : ∃ d, q = p+d.
            let ex = Expr::apps(c.nat_exists_eq_add_of_le.clone(), [p.clone(), q.clone(), h]);
            let pred = c.add_pred(&b, &p, &q);
            let goal = c.le(a_p.clone(), a_q.clone());
            // elim fn : (d:Nat) → (hd : q = p+d) → le a_p a_q.
            let elim_fn = {
                let mut eb = EnvDeclBuilder::child_of(&b);
                let (d_id, d) = eb.fresh_local(c.nat.clone());
                let hd_ty = c.eq_nat_ty(q.clone(), c.nadd(p.clone(), d.clone()));
                let (hd_id, hd) = eb.fresh_local(hd_ty.clone());
                // base : le a_p (a_(p+d)) := dyadicApprox_le_add x p d.
                let base = Expr::apps(
                    c.rat_dyadic_approx_le_add.clone(),
                    [x.clone(), p.clone(), d.clone()],
                );
                let a_pd = c.approx(&x, c.nadd(p.clone(), d.clone()));
                // transport RHS a_(p+d) → a_q along (Eq.symm hd : p+d = q):
                //   congrArg (dyadicApprox x) (Eq.symm hd) : a_(p+d) = a_q.
                let approx_fn = {
                    let mut fb = EnvDeclBuilder::child_of(&eb);
                    let (m_id, m) = fb.fresh_local(c.nat.clone());
                    let body = c.approx(&x, m.clone());
                    fb.finish_child(fb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let hd_sym = c.eq_nat_symm(q.clone(), c.nadd(p.clone(), d.clone()), hd);
                let eq_approx =
                    c.congr_nat_rat(c.nadd(p.clone(), d.clone()), q.clone(), approx_fn, hd_sym);
                // transport base's RHS a_(p+d) → a_q: motive t := le a_p t.
                let motive_t = {
                    let mut mb = EnvDeclBuilder::child_of(&eb);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.le(a_p.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let proof = c.eq_rat_subst(motive_t, a_pd.clone(), a_q.clone(), eq_approx, base);
                let e = eb.mk_lam(hd_id, BinderInfo::Default, hd_ty, proof);
                let e = eb.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
                eb.finish_child(e)
            };
            let body = Expr::apps(
                c.exists_elim.clone(),
                [c.nat.clone(), pred, goal, ex, elim_fn],
            );

            let e = b.mk_lam(h_id, BinderInfo::Default, hle_ty, body);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.dyadicApprox_le_add_inv_of_le : ∀ x p q, Nat.le p q →
    ///     le (a_q) (a_p + inv(2^p))`.
    fn register_dyadic_approx_le_add_inv_of_le(&mut self, c: &LeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicApprox_le_add_inv_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (p_id, p) = b.fresh_local(c.nat.clone());
            let (q_id, q) = b.fresh_local(c.nat.clone());
            let hle = c.nat_le(p.clone(), q.clone());
            let (h_id, _h) = b.fresh_local(hle.clone());
            let rhs = c.add(c.approx(&x, p.clone()), c.iv(p.clone()));
            let concl = c.le(c.approx(&x, q.clone()), rhs);
            let e = b.mk_pi(h_id, BinderInfo::Default, hle, concl);
            let e = b.mk_pi(q_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (p_id, p) = b.fresh_local(c.nat.clone());
            let (q_id, q) = b.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(p.clone(), q.clone());
            let (h_id, h) = b.fresh_local(hle_ty.clone());

            let a_q = c.approx(&x, q.clone());
            let rhs = c.add(c.approx(&x, p.clone()), c.iv(p.clone()));
            let ex = Expr::apps(c.nat_exists_eq_add_of_le.clone(), [p.clone(), q.clone(), h]);
            let pred = c.add_pred(&b, &p, &q);
            let goal = c.le(a_q.clone(), rhs.clone());
            let elim_fn = {
                let mut eb = EnvDeclBuilder::child_of(&b);
                let (d_id, d) = eb.fresh_local(c.nat.clone());
                let hd_ty = c.eq_nat_ty(q.clone(), c.nadd(p.clone(), d.clone()));
                let (hd_id, hd) = eb.fresh_local(hd_ty.clone());
                // base : le (a_(p+d))(a_p + iv_p) := dyadicApprox_le_add_inv x p d.
                let base = Expr::apps(
                    c.rat_dyadic_approx_le_add_inv.clone(),
                    [x.clone(), p.clone(), d.clone()],
                );
                let a_pd = c.approx(&x, c.nadd(p.clone(), d.clone()));
                // eq_approx : a_(p+d) = a_q (congrArg over Eq.symm hd).
                let approx_fn = {
                    let mut fb = EnvDeclBuilder::child_of(&eb);
                    let (m_id, m) = fb.fresh_local(c.nat.clone());
                    let body = c.approx(&x, m.clone());
                    fb.finish_child(fb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
                };
                let hd_sym = c.eq_nat_symm(q.clone(), c.nadd(p.clone(), d.clone()), hd);
                let eq_approx =
                    c.congr_nat_rat(c.nadd(p.clone(), d.clone()), q.clone(), approx_fn, hd_sym);
                // transport base's LHS a_(p+d) → a_q: motive t := le t rhs.
                let motive_t = {
                    let mut mb = EnvDeclBuilder::child_of(&eb);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.le(t, rhs.clone());
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let proof = c.eq_rat_subst(motive_t, a_pd.clone(), a_q.clone(), eq_approx, base);
                let e = eb.mk_lam(hd_id, BinderInfo::Default, hd_ty, proof);
                let e = eb.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
                eb.finish_child(e)
            };
            let body = Expr::apps(
                c.exists_elim.clone(),
                [c.nat.clone(), pred, goal, ex, elim_fn],
            );

            let e = b.mk_lam(h_id, BinderInfo::Default, hle_ty, body);
            let e = b.mk_lam(q_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "Nat.exists_eq_add_of_le",
        "Rat.dyadicApprox_le_add",
        "Rat.dyadicApprox_mono",
        "Rat.dyadicApprox_le_add_inv_of_le",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_cauchy_le()
            .expect("init_algebra_nnreal_sqrt_cauchy_le");
        env.init_algebra_nnreal_sqrt_cauchy_le()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_dyadic_le_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_dyadic_le_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
