// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parseval RUNG 2 — the diagonal-collapse of a finite sum.
//!
//! `Fin.sum_diag_collapse : ∀ (n : Nat) (j : Fin n) (f : Fin n → Rat),
//!     (∀ (k : Fin n), (Eq (Fin n) k j → False) → f k = Rat.zero)
//!       → Fin.sum n f = f j`
//!
//! THE off-diagonal-killer rung: a finite sum whose summand vanishes everywhere
//! except a single index `j` collapses to that index's value. This is the
//! hypothesis-form bridge that turns the Kronecker dichotomy
//! (`prod_offdiag_eq_zero : j ≠ k → … = 0`, `prod_diag_eq_cube : … = 2^n`) into
//! the consumable `Σ = f j` shape RUNG 3 needs to collapse the Parseval
//! `y`-sum.
//!
//! Derived from the landed `Fin.sum_single` (the ite-Kronecker collapse) by
//! `Fin.sum_congr`:
//!   - bridge `H' : ∀ k, f k = @ite Rat (Eq (Fin n) k j) (inst n k j) (f j) 0`
//!     — proved per-point by `Decidable.rec` on `instDecidableEqFin n k j`.
//!     In each branch the `ite`'s instance becomes a concrete `Decidable`
//!     constructor, so the `ite` ι-reduces and the goal is def-eq to a plain
//!     equation closed directly (no `if_pos`/`if_neg` rewrite needed):
//!       · isTrue `heq : k = j` ⟹ goal def-eq `f k = f j`, closed by `Eq.rec`
//!         transporting `Eq.refl (f k)` along `heq`;
//!       · isFalse `hne` ⟹ goal def-eq `f k = 0`, closed by `H k hne`.
//!   - `Fin.sum_congr n f (kron j (f j)) H' : Fin.sum n f = Fin.sum n (kron …)`;
//!   - `Fin.sum_single n j (f j) (Fin.isLt n j) : Fin.sum n (kron …) = f j`.
//!
//! The required `Nat.lt (Fin.val n j) n` premise of `Fin.sum_single` is supplied
//! internally by `Fin.isLt`, so `Fin.sum_diag_collapse` needs no in-range side
//! condition. Closure ⊆ `Fin.sum_single`/`Fin.sum_congr`/`Fin.isLt`/
//! `Decidable.rec`/`Eq.rec` and the `Eq` built-ins — no domain axiom;
//! `ProofQuality::Constructive`.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_fin_sum::FinSumConsts;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct Rung2Consts {
    base: FinSumConsts,
    eq1: Expr,
    eq_trans: Expr,
    eq_rec: Expr,
    false_c: Expr,
    fin_islt: Expr,
    fin_sum_single: Expr,
    fin_sum_congr: Expr,
    dec: Expr,
    dec_rec: Expr,
}

impl Rung2Consts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        Self {
            base: FinSumConsts::new(),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            // @Eq.rec.{0, 1} : motive in Prop (l0), carrier Fin n in Type (l1).
            eq_rec: Expr::const_(Name::from_string("Eq.rec"), vec![l0.clone(), l1]),
            false_c: Expr::const_(Name::from_string("False"), vec![]),
            fin_islt: Expr::const_(Name::from_string("Fin.isLt"), vec![]),
            fin_sum_single: Expr::const_(Name::from_string("Fin.sum_single"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            dec: Expr::const_(Name::from_string("Decidable"), vec![]),
            dec_rec: Expr::const_(Name::from_string("Decidable.rec"), vec![l0]),
        }
    }

    fn rat(&self) -> Expr {
        self.base.rat.clone()
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.base.fin.clone(), n.clone())
    }
    fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.base.fin_sum.clone(), [n, f])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        self.base.rat_eq(l, r)
    }
    /// `@Eq (Fin n) a b`.
    fn eq_fin(&self, n: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.fin_of(n), a.clone(), b.clone()])
    }
    /// `@instDecidableEqFin n a b`.
    fn inst(&self, n: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.base.inst_dec_eq_fin.clone(),
            [n.clone(), a.clone(), b.clone()],
        )
    }
    /// `@ite Rat cond inst hi lo`.
    fn ite(&self, cond: Expr, inst: Expr, hi: Expr, lo: Expr) -> Expr {
        Expr::apps(self.base.ite.clone(), [self.rat(), cond, inst, hi, lo])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat(), a, b, cc, h1, h2])
    }
    /// `fun (k : Fin n) => @ite Rat (Eq (Fin n) k j) (inst n k j) x Rat.zero`.
    fn kron_fn(&self, parent: &EnvDeclBuilder, n: &Expr, j: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (k_id, k) = b.fresh_local(fin_n.clone());
        let body = self.ite(
            self.eq_fin(n, &k, j),
            self.inst(n, &k, j),
            x.clone(),
            self.base.rat_zero.clone(),
        );
        b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin_n, body))
    }
}

/// The pointwise hypothesis type at a fixed `n`, `j`, `f`:
/// `∀ (k : Fin n), (Eq (Fin n) k j → False) → f k = Rat.zero`.
fn hyp_ty(c: &Rung2Consts, parent: &EnvDeclBuilder, n: &Expr, j: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (k_id, k) = b.fresh_local(fin_n.clone());
    let ne = Expr::pi(BinderInfo::Default, c.eq_fin(n, &k, j), c.false_c.clone());
    let concl = c.eq_rat(Expr::app(f.clone(), k.clone()), c.base.rat_zero.clone());
    let body = Expr::arrow(ne, concl);
    b.finish_child(b.mk_pi(k_id, BinderInfo::Default, fin_n, body))
}

fn diag_type(c: &Rung2Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let fin_n = c.fin_of(&n);
    let (j_id, j) = b.fresh_local(fin_n.clone());
    let f_ty = c.base.fin_to_rat(n.clone());
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let h = hyp_ty(c, &b, &n, &j, &f);
    let (h_id, _h) = b.fresh_local(h.clone());
    let concl = c.eq_rat(c.sum(n.clone(), f.clone()), Expr::app(f.clone(), j.clone()));
    let r = b.mk_pi(h_id, BinderInfo::Default, h, concl);
    let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
    let r = b.mk_pi(j_id, BinderInfo::Default, fin_n, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.base.nat.clone(), r);
    b.finish(r)
}

fn diag_value(c: &Rung2Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.base.nat.clone());
    let fin_n = c.fin_of(&n);
    let (j_id, j) = b.fresh_local(fin_n.clone());
    let f_ty = c.base.fin_to_rat(n.clone());
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let h_ty = hyp_ty(c, &b, &n, &j, &f);
    let (h_id, hyp) = b.fresh_local(h_ty.clone());

    let fj = Expr::app(f.clone(), j.clone());
    let kron = c.kron_fn(&b, &n, &j, &fj);

    // bridge H' : ∀ (k : Fin n), f k = @ite Rat (Eq (Fin n) k j) (inst n k j) (f j) 0
    let h_prime = {
        let mut kb = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = kb.fresh_local(fin_n.clone());
        let fk = Expr::app(f.clone(), k.clone());
        let cond = c.eq_fin(&n, &k, &j);
        let inst_kj = c.inst(&n, &k, &j);
        let ite_term = c.ite(
            cond.clone(),
            inst_kj.clone(),
            fj.clone(),
            c.base.rat_zero.clone(),
        );

        // dmotive : (d : Decidable cond) → Prop := fun d => f k = @ite Rat cond d (f j) 0
        let dmotive = {
            let mut d = EnvDeclBuilder::child_of(&kb);
            let dec_c = Expr::app(c.dec.clone(), cond.clone());
            let (dd_id, dd) = d.fresh_local(dec_c.clone());
            let ite_d = c.ite(cond.clone(), dd, fj.clone(), c.base.rat_zero.clone());
            let body = c.eq_rat(fk.clone(), ite_d);
            d.finish_child(d.mk_lam(dd_id, BinderInfo::Default, dec_c, body))
        };

        // isFalse minor : fun (hne : cond → False) =>
        //   goal `f k = @ite Rat cond (isFalse hne) (f j) 0`. With the instance the
        //   concrete `isFalse` constructor, the ite ι-reduces to its `else` branch
        //   `Rat.zero`, so the goal is def-eq `f k = 0` — exactly `H k hne`.
        let false_minor = {
            let mut d = EnvDeclBuilder::child_of(&kb);
            let ne_ty = Expr::pi(BinderInfo::Default, cond.clone(), c.false_c.clone());
            let (hne_id, hne) = d.fresh_local(ne_ty.clone());
            // H k hne : f k = 0   (def-eq to the ι-reduced goal).
            let hk = Expr::apps(hyp.clone(), [k.clone(), hne.clone()]);
            d.finish_child(d.mk_lam(hne_id, BinderInfo::Default, ne_ty, hk))
        };

        // isTrue minor : fun (heq : cond) =>
        //   goal `f k = @ite Rat cond (isTrue heq) (f j) 0`. With the instance the
        //   concrete `isTrue` constructor, the ite ι-reduces to its `then` branch
        //   `f j`, so the goal is def-eq `f k = f j` — proven by Eq.rec on heq.
        let true_minor = {
            let mut d = EnvDeclBuilder::child_of(&kb);
            let (heq_id, heq) = d.fresh_local(cond.clone());
            // motive for Eq.rec : fun (w : Fin n) (_ : Eq (Fin n) k w) => f k = f w
            //   (transport target var `w`; motive at `(j, heq)` gives `f k = f j`,
            //    the base at `(k, rfl)` gives `f k = f k`). The eq binder is unused
            //    in the body, but Eq.rec's motive must take it.
            let rec_motive = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (w_id, w) = e.fresh_local(fin_n.clone());
                let eq_kw = c.eq_fin(&n, &k, &w);
                let (e_id, _ev) = e.fresh_local(eq_kw.clone());
                let body = c.eq_rat(fk.clone(), Expr::app(f.clone(), w.clone()));
                // motive is a 2-argument LAMBDA `fun w e => (f k = f w)` (the eq
                // binder unused in the body but required by Eq.rec's motive arity).
                let inner = e.mk_lam(e_id, BinderInfo::Default, eq_kw, body);
                e.finish_child(e.mk_lam(w_id, BinderInfo::Default, fin_n.clone(), inner))
            };
            // base : motive k rfl ≡ (f k = f k), inhabited by @Eq.refl Rat (f k).
            let rec_base = Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [c.rat(), fk.clone()],
            );
            // @Eq.rec.{0,1} (Fin n) k motive rec_base j heq : motive j heq ≡ (f k = f j)
            //   (def-eq to the ι-reduced isTrue goal `f k = @ite cond (isTrue heq) …`).
            let proof = Expr::apps(
                c.eq_rec.clone(),
                [
                    fin_n.clone(),
                    k.clone(),
                    rec_motive,
                    rec_base,
                    j.clone(),
                    heq.clone(),
                ],
            );
            d.finish_child(d.mk_lam(heq_id, BinderInfo::Default, cond.clone(), proof))
        };

        // @Decidable.rec.{0} cond dmotive false_minor true_minor (inst n k j) : goal
        let rec = Expr::apps(
            c.dec_rec.clone(),
            [
                cond.clone(),
                dmotive,
                false_minor,
                true_minor,
                inst_kj.clone(),
            ],
        );
        kb.finish_child(kb.mk_lam(k_id, BinderInfo::Default, fin_n.clone(), rec))
    };

    // congr_leg : Fin.sum n f = Fin.sum n (kron j (f j))
    let congr_leg = Expr::apps(
        c.fin_sum_congr.clone(),
        [n.clone(), f.clone(), kron.clone(), h_prime],
    );
    // single_leg : Fin.sum n (kron j (f j)) = f j
    //   Fin.sum_single n j (f j) (Fin.isLt n j).
    let islt = Expr::apps(c.fin_islt.clone(), [n.clone(), j.clone()]);
    let single_leg = Expr::apps(
        c.fin_sum_single.clone(),
        [n.clone(), j.clone(), fj.clone(), islt],
    );

    let sum_f = c.sum(n.clone(), f.clone());
    let sum_kron = c.sum(n.clone(), kron.clone());
    let proof = c.trans(sum_f, sum_kron, fj.clone(), congr_leg, single_leg);

    let val = b.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_ty, val);
    let val = b.mk_lam(j_id, BinderInfo::Default, fin_n, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `Fin.sum_diag_collapse : ∀ n j f,
    ///   (∀ k, (Eq (Fin n) k j → False) → f k = 0) → Fin.sum n f = f j`
    /// as a kernel-checked, constructive theorem. Idempotent.
    pub(crate) fn register_fin_sum_diag_collapse_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_diag_collapse");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?; // Fin.sum, Fin.sum_single, Fin.sum_congr
        self.init_ite()?;
        self.init_decidable_eq()?;
        self.register_fin_dec_eq_proof()?; // instDecidableEqFin

        let c = Rung2Consts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: diag_type(&c),
            value: diag_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_sum_diag_collapse_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_fin_sum_diag_collapse_theorem()
            .expect("register_fin_sum_diag_collapse_theorem");
        let n = Name::from_string("Fin.sum_diag_collapse");
        let info = env.get_const(&n).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ty = tc
            .infer_type(&Expr::const_(n, vec![]))
            .expect("Fin.sum_diag_collapse should type-check");
    }
}
