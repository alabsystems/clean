// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bound — Stage C-3 RESIDUAL component **H1** (the
//! self-product / `‖·‖₄ ≤ ‖·‖₂` shadow), built axiom-free.
//!
//! # Where this sits
//!
//! `BoolAnalysis.m2_from_contraction`
//! (`boolean_analysis_kkl_dualres_m2.rs`) reduces the dual `(4/3→4)`
//! hypercontractivity `f4 = Σ_x pow4(z x) ≤ 16·count³` to two facts: **H1**
//! `f4 ≤ s2 := (Σz²)²` and **H2** `s2 ≤ 16·count²`. H1 is the elementary
//! nonnegative power-sum bound
//!
//! ```text
//!   Σ_x (g x)²  ≤  (Σ_x g x)²        for nonnegative g
//! ```
//!
//! (at `g := z²` this is `Σ z⁴ ≤ (Σ z²)²`). Its proof drops the nonnegative
//! off-diagonal of the self-product: `(Σ g)² = Σ_x g x·(Σ g) ≥ Σ_x (g x)²`
//! because each term `g x ≤ Σ g` (the term is ≤ the whole nonnegative sum).
//!
//! This module lands that bound at the `Fin.sum` level (the carrier `subsetSum`
//! reducibly δ-unfolds to), AXIOM-FREE, plus its load-bearing primitive — the
//! **term-le-nonnegative-sum** lemma `f i ≤ Fin.sum n f` (absent on main).
//!
//! # What this module proves (axiom-free, kernel-checked)
//!
//! 1. **`Fin.sum_term_le_of_nonneg`** — the missing primitive
//!    ```text
//!    ∀ (n : Nat) (f : Fin n → Rat) (i : Fin n),
//!      (∀ j, 0 ≤ f j) → f i ≤ Fin.sum n f.
//!    ```
//!    `Nat.rec` on `n`; the successor step `Fin.lastCases` on `i` against
//!    `Fin.sum (succ k) f ≡ Rat.add (Fin.sum k (f∘castSucc)) (f (last k))`:
//!    the `last` branch is `le_add_of_nonneg_right` (prefix nonneg) + an
//!    `add_comm` transport; the `castSucc i'` branch chains the IH on
//!    `f∘castSucc` with `le_add_of_nonneg_right` (the `last` term nonneg). The
//!    `Fin 0` base is vacuous (`Fin.isLt` + `Nat.not_succ_le_zero`).
//!
//! 2. **`BoolAnalysis.fin_sum_sq_le_sq_sum_nonneg`** (H1)
//!    ```text
//!    ∀ (n : Nat) (g : Fin n → Rat),
//!      (∀ j, 0 ≤ g j) →
//!      Fin.sum n (fun j => Rat.mul (g j) (g j))
//!        ≤ Rat.mul (Fin.sum n g) (Fin.sum n g).
//!    ```
//!    `(Σg)·(Σg) = Σ_x g x·(Σg)` (`Fin.sum_smul`, reversed) bounds
//!    `Σ_x (g x)·(g x)` via `Fin.sum_le` with the per-`x`
//!    `g x·g x ≤ (Σg)·g x` (`mul_le_mul_of_nonneg_right` from rung 1).
//!
//! Both `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-
//! axiom closure (asserted by per-module tests). Both default AND
//! `--features math-overlays` builds green. Module gated
//! `cfg(any(test, feature = "math-overlays"))`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the H1 / term-le-sum builds.
struct H1Consts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    fin_last: Expr,
    fin_cast: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_lt: Expr,
    nat_rec0: Expr,
    not_succ_le_zero: Expr,
    false_elim0: Expr,
    fin_last_cases0: Expr,
    le_trans: Expr,
    le_add_nonneg_right: Expr,
    add_comm: Expr,
    sum_nonneg: Expr,
    sum_le: Expr,
    sum_smul: Expr,
    mul_le_right: Expr,
    eq_subst1: Expr,
}

impl H1Consts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            fin_val: k("Fin.val"),
            fin_islt: k("Fin.isLt"),
            fin_last: k("Fin.last"),
            fin_cast: k("Fin.castSucc"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![l0.clone()]),
            inst_le_rat: k("instLERat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_lt: k("Nat.lt"),
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]),
            not_succ_le_zero: k("Nat.not_succ_le_zero"),
            false_elim0: Expr::const_(Name::from_string("False.elim"), vec![l0.clone()]),
            fin_last_cases0: Expr::const_(Name::from_string("Fin.lastCases"), vec![l0]),
            le_trans: k("Rat.le_trans"),
            le_add_nonneg_right: k("Rat.le_add_of_nonneg_right"),
            add_comm: k("Rat.add_comm"),
            sum_nonneg: k("Fin.sum_nonneg"),
            sum_le: k("Fin.sum_le"),
            sum_smul: k("Fin.sum_smul"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn sum(&self, n: &Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), f])
    }
    fn val(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), i.clone()])
    }
    fn islt(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_islt.clone(), [n.clone(), i.clone()])
    }
    fn last(&self, k: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), k.clone())
    }
    fn cast(&self, k: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_cast.clone(), [k.clone(), i.clone()])
    }
    /// `Rat.le_trans a b c h1 h2 : a ≤ c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cc, h1, h2])
    }
    /// `Rat.le_add_of_nonneg_right a b h : a ≤ a + b`.
    fn le_add_right(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.le_add_nonneg_right.clone(), [a, b, h])
    }
    /// `Rat.add_comm a b : a + b = b + a`.
    fn add_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.add_comm.clone(), [a, b])
    }
    /// `Fin.sum_nonneg n f h : 0 ≤ Fin.sum n f`.
    fn sum_nonneg(&self, n: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.sum_nonneg.clone(), [n.clone(), f, h])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c h h0 : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, cc, h, h0])
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `f ∘ Fin.castSucc k := fun (i : Fin k) => f (Fin.castSucc k i)`.
    fn comp_cast(&self, parent: &EnvDeclBuilder, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = d.fresh_local(self.fin_of(k));
        let body = Expr::app(f.clone(), self.cast(k, &i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, self.fin_of(k), body))
    }
}

// ─────────────────── Rung 1: Fin.sum_term_le_of_nonneg ──────────────────────
//
//   ∀ (n) (f : Fin n → Rat) (i : Fin n), (∀ j, 0 ≤ f j) → f i ≤ Fin.sum n f

/// `∀ (j : Fin k), 0 ≤ f j`.
fn nonneg_hyp(c: &H1Consts, parent: &EnvDeclBuilder, k: &Expr, f: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = d.fresh_local(c.fin_of(k));
    let body = c.le(c.rat_zero.clone(), Expr::app(f.clone(), j));
    d.finish_child(d.mk_pi(j_id, BinderInfo::Default, c.fin_of(k), body))
}

/// `motive k := ∀ (f : Fin k → Rat) (i : Fin k), (∀ j, 0 ≤ f j) → f i ≤ Fin.sum k f`.
fn term_le_motive_body(c: &H1Consts, parent: &EnvDeclBuilder, k: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let ft = c.fin_to_rat(k);
    let (f_id, f) = d.fresh_local(ft.clone());
    let (i_id, i) = d.fresh_local(c.fin_of(k));
    let hyp = nonneg_hyp(c, &d, k, &f);
    let (h_id, _h) = d.fresh_local(hyp.clone());
    let concl = c.le(Expr::app(f.clone(), i.clone()), c.sum(k, f.clone()));
    let r = d.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let r = d.mk_pi(i_id, BinderInfo::Default, c.fin_of(k), r);
    let r = d.mk_pi(f_id, BinderInfo::Default, ft, r);
    d.finish_child(r)
}

fn build_term_le(c: &H1Consts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let ft = c.fin_to_rat(&n);
        let (f_id, f) = b.fresh_local(ft.clone());
        let (i_id, i) = b.fresh_local(c.fin_of(&n));
        let hyp = nonneg_hyp(c, &b, &n, &f);
        let (h_id, _h) = b.fresh_local(hyp.clone());
        let concl = c.le(Expr::app(f.clone(), i.clone()), c.sum(&n, f.clone()));
        let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
        let r = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), r);
        let r = b.mk_pi(f_id, BinderInfo::Default, ft, r);
        let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };

    let motive = {
        let mut b = EnvDeclBuilder::new();
        let (k_id, k) = b.fresh_local(c.nat.clone());
        let body = term_le_motive_body(c, &b, &k);
        b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // Base: M 0. `i : Fin 0` is impossible: Fin.isLt 0 i : val < 0, refuted.
    let base = {
        let mut b = EnvDeclBuilder::new();
        let nat_zero = c.nat_zero.clone();
        let ft = c.fin_to_rat(&nat_zero);
        let (f_id, f) = b.fresh_local(ft.clone());
        let (i_id, i) = b.fresh_local(c.fin_of(&nat_zero));
        let hyp = nonneg_hyp(c, &b, &nat_zero, &f);
        let (h_id, _h) = b.fresh_local(hyp.clone());
        let goal = c.le(Expr::app(f.clone(), i.clone()), c.sum(&nat_zero, f.clone()));
        let val0 = c.val(&nat_zero, &i);
        // Fin.isLt 0 i : Nat.lt (Fin.val 0 i) 0 ≡ Nat.le (succ val0) 0.
        let h_lt = c.islt(&nat_zero, &i);
        let false_pf = Expr::apps(c.not_succ_le_zero.clone(), [val0, h_lt]);
        let body = Expr::apps(c.false_elim0.clone(), [goal, false_pf]);
        let r = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
        let r = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&nat_zero), r);
        let r = b.mk_lam(f_id, BinderInfo::Default, ft, r);
        b.finish(r)
    };

    // Step.
    let step = {
        let mut b = EnvDeclBuilder::new();
        let (k_id, k) = b.fresh_local(c.nat.clone());
        let ih_ty = term_le_motive_body(c, &b, &k);
        let (ih_id, ih) = b.fresh_local(ih_ty.clone());
        let sk = c.succ(&k);
        let ft_sk = c.fin_to_rat(&sk);
        let (f_id, f) = b.fresh_local(ft_sk.clone());
        let (i_id, i) = b.fresh_local(c.fin_of(&sk));
        let hyp = nonneg_hyp(c, &b, &sk, &f);
        let (h_id, h) = b.fresh_local(hyp.clone());

        // shared terms.
        let f_cs = c.comp_cast(&b, &k, &f); // f ∘ castSucc
        let prefix = c.sum(&k, f_cs.clone()); // Fin.sum k (f∘cs)
        let last_k = c.last(&k);
        let f_last = Expr::app(f.clone(), last_k.clone()); // f (last k)
        let sum_sk = c.sum(&sk, f.clone()); // ≡ prefix + f_last

        // P : Fin (succ k) → Prop := fun w => f w ≤ Fin.sum (succ k) f.
        let p_motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (w_id, w) = d.fresh_local(c.fin_of(&sk));
            let body = c.le(Expr::app(f.clone(), w.clone()), sum_sk.clone());
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.fin_of(&sk), body))
        };

        // h_pre_nn : 0 ≤ prefix  (Fin.sum_nonneg k (f∘cs) (fun j => h (castSucc j)))
        let h_pre_nn = {
            let per = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (j_id, j) = d.fresh_local(c.fin_of(&k));
                let body = Expr::app(h.clone(), c.cast(&k, &j));
                d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(&k), body))
            };
            c.sum_nonneg(&k, f_cs.clone(), per)
        };
        let h_last_nn = Expr::app(h.clone(), last_k.clone()); // 0 ≤ f_last

        // last_case : f (last k) ≤ prefix + f_last.
        let last_case = {
            let f_last_plus_pre = c.add(f_last.clone(), prefix.clone());
            let pre_plus_f_last = c.add(prefix.clone(), f_last.clone());
            let h0 = c.le_add_right(f_last.clone(), prefix.clone(), h_pre_nn.clone());
            let ac = c.add_comm(f_last.clone(), prefix.clone()); // f_last+pre = pre+f_last
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = d.fresh_local(c.rat.clone());
                let body = c.le(f_last.clone(), z);
                d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
            };
            c.subst(motive, f_last_plus_pre, pre_plus_f_last, ac, h0)
        };

        // cast_case : (i' : Fin k) → f (castSucc i') ≤ prefix + f_last.
        let cast_case = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (ip_id, ip) = d.fresh_local(c.fin_of(&k));
            let per_ih = {
                let mut g = EnvDeclBuilder::child_of(&d);
                let (j_id, j) = g.fresh_local(c.fin_of(&k));
                let body = Expr::app(h.clone(), c.cast(&k, &j));
                g.finish_child(g.mk_lam(j_id, BinderInfo::Default, c.fin_of(&k), body))
            };
            // ih f_cs ip per_ih : (f∘cs) ip ≤ Fin.sum k (f∘cs)
            let f_cs_ip = Expr::app(f_cs.clone(), ip.clone()); // ≡ f (castSucc ip)
            let ih_app = Expr::apps(ih.clone(), [f_cs.clone(), ip.clone(), per_ih]);
            // prefix ≤ prefix + f_last
            let pre_plus = c.add(prefix.clone(), f_last.clone());
            let pre_le = c.le_add_right(prefix.clone(), f_last.clone(), h_last_nn.clone());
            let body = c.le_trans(f_cs_ip, prefix.clone(), pre_plus, ih_app, pre_le);
            d.finish_child(d.mk_lam(ip_id, BinderInfo::Default, c.fin_of(&k), body))
        };

        // @Fin.lastCases.{0} k P last_case cast_case i : f i ≤ Fin.sum (succ k) f.
        let lc = Expr::apps(
            c.fin_last_cases0.clone(),
            [k.clone(), p_motive, last_case, cast_case, i.clone()],
        );

        let r = b.mk_lam(h_id, BinderInfo::Default, hyp, lc);
        let r = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&sk), r);
        let r = b.mk_lam(f_id, BinderInfo::Default, ft_sk, r);
        let r = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
        let r = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let ft = c.fin_to_rat(&n);
        let (f_id, f) = b.fresh_local(ft.clone());
        let (i_id, i) = b.fresh_local(c.fin_of(&n));
        let hyp = nonneg_hyp(c, &b, &n, &f);
        let (h_id, h) = b.fresh_local(hyp.clone());
        let rec_app = Expr::apps(
            c.nat_rec0.clone(),
            [
                motive,
                base,
                step,
                n.clone(),
                f.clone(),
                i.clone(),
                h.clone(),
            ],
        );
        let r = b.mk_lam(h_id, BinderInfo::Default, hyp, rec_app);
        let r = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), r);
        let r = b.mk_lam(f_id, BinderInfo::Default, ft, r);
        let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };

    (ty, value)
}

// ───────────────── Rung 2: fin_sum_sq_le_sq_sum_nonneg (H1) ─────────────────
//
//   ∀ (n) (g : Fin n → Rat), (∀ j, 0 ≤ g j) →
//     Fin.sum n (fun j => g j · g j) ≤ (Fin.sum n g)·(Fin.sum n g)

/// `fun (j : Fin n) => Rat.mul (g j) (g j)`.
fn sq_fn(c: &H1Consts, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = d.fresh_local(c.fin_of(n));
    let gj = Expr::app(g.clone(), j.clone());
    let body = c.mul(gj.clone(), gj);
    d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), body))
}

/// `fun (j : Fin n) => Rat.mul (Fin.sum n g) (g j)` — the scaled summand
/// `Fin.sum_smul` collapses to `(Σg)·(Σg)`.
fn scaled_fn(c: &H1Consts, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, sg: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = d.fresh_local(c.fin_of(n));
    let body = c.mul(sg.clone(), Expr::app(g.clone(), j));
    d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(n), body))
}

fn build_h1(c: &H1Consts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let gt = c.fin_to_rat(&n);
        let (g_id, g) = b.fresh_local(gt.clone());
        let hyp = nonneg_hyp(c, &b, &n, &g);
        let (h_id, _h) = b.fresh_local(hyp.clone());
        let sum_g = c.sum(&n, g.clone());
        let lhs = c.sum(&n, sq_fn(c, &b, &n, &g));
        let rhs = c.mul(sum_g.clone(), sum_g);
        let concl = c.le(lhs, rhs);
        let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
        let r = b.mk_pi(g_id, BinderInfo::Default, gt, r);
        let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let gt = c.fin_to_rat(&n);
        let (g_id, g) = b.fresh_local(gt.clone());
        let hyp = nonneg_hyp(c, &b, &n, &g);
        let (h_id, h) = b.fresh_local(hyp.clone());

        let sum_g = c.sum(&n, g.clone()); // Σg
        let sq = sq_fn(c, &b, &n, &g); // fun j => g j·g j
        let scaled = scaled_fn(c, &b, &n, &g, &sum_g); // fun j => (Σg)·(g j)
        let lhs = c.sum(&n, sq.clone()); // Σ (g·g)
        let mid = c.sum(&n, scaled.clone()); // Σ ((Σg)·g)
        let rhs = c.mul(sum_g.clone(), sum_g.clone()); // (Σg)·(Σg)

        // pointwise : ∀ j, g j·g j ≤ (Σg)·(g j)
        let pointwise = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = d.fresh_local(c.fin_of(&n));
            let gj = Expr::app(g.clone(), j.clone());
            let h_gj_le_sg = Expr::apps(
                Expr::const_(Name::from_string("Fin.sum_term_le_of_nonneg"), vec![]),
                [n.clone(), g.clone(), j.clone(), h.clone()],
            );
            let h_gj_nn = Expr::app(h.clone(), j.clone());
            let body = c.mul_le_right(gj.clone(), gj.clone(), sum_g.clone(), h_gj_le_sg, h_gj_nn);
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(&n), body))
        };

        // h_le : Σ (g·g) ≤ Σ ((Σg)·g)   (Fin.sum_le n sq scaled pointwise)
        let h_le = Expr::apps(
            c.sum_le.clone(),
            [n.clone(), sq.clone(), scaled.clone(), pointwise],
        );

        // smul : Σ ((Σg)·g) = (Σg)·(Σg)   (Fin.sum_smul n (Σg) g)
        let smul = Expr::apps(c.sum_smul.clone(), [n.clone(), sum_g.clone(), g.clone()]);

        // close: subst smul into the ≤ RHS of h_le. motive z => Σ(g·g) ≤ z.
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = d.fresh_local(c.rat.clone());
            let body = c.le(lhs.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let proof = c.subst(motive, mid, rhs, smul, h_le);

        let r = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
        let r = b.mk_lam(g_id, BinderInfo::Default, gt, r);
        let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };

    (ty, value)
}

impl Environment {
    /// Register `Fin.sum_term_le_of_nonneg` — the term-le-nonnegative-sum
    /// primitive `f i ≤ Fin.sum n f` (`Nat.rec` + `Fin.lastCases`).
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_fin_sum_term_le_of_nonneg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_term_le_of_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_fin_sum()?; // Fin.sum, Fin.sum_nonneg, Fin.last/castSucc, Fin.isLt
        self.register_fin_last_cases()?; // Fin.lastCases
        self.register_rat_order_proofs()?; // Rat.le_trans
        self.register_rat_add_comm_proof()?; // Rat.add_comm
        self.rat_quotient_payoff_into_live()?; // Rat.le_add_of_nonneg_right
        self.register_nat_not_succ_le_zero_theorem()?; // Nat.not_succ_le_zero
        self.init_le()?; // Nat.lt

        let c = H1Consts::new();
        let (ty, value) = build_term_le(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register `BoolAnalysis.fin_sum_sq_le_sq_sum_nonneg` (H1):
    /// `Σ_j (g j)² ≤ (Σ_j g j)²` for nonnegative `g`. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_fin_sum_sq_le_sq_sum_nonneg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.fin_sum_sq_le_sq_sum_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_fin_sum_term_le_of_nonneg()?;
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_right
        self.register_fin_sum_smul_theorem()?; // Fin.sum_smul

        let c = H1Consts::new();
        let (ty, value) = build_h1(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Init hook for the H1 dual-final overlay module.
    pub fn init_boolean_analysis_kkl_dualfinal_h1(&mut self) -> Result<(), EnvError> {
        self.register_fin_sum_sq_le_sq_sum_nonneg()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::carrier_refutation::refute_conjecture;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualfinal_h1()
            .expect("init_boolean_analysis_kkl_dualfinal_h1");
        env.init_boolean_analysis_kkl_dualfinal_h1()
            .expect("idempotent");
        env
    }

    fn assert_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} proof must check against its type: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be foundational-only, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_fin_sum_term_le_of_nonneg_constructive() {
        assert_constructive(&env(), "Fin.sum_term_le_of_nonneg");
    }

    #[test]
    fn test_fin_sum_sq_le_sq_sum_nonneg_constructive() {
        assert_constructive(&env(), "BoolAnalysis.fin_sum_sq_le_sq_sum_nonneg");
    }

    /// THE TARGET-REFUTATION GATE. H1 is a TRUE implication (for nonnegative
    /// terms `Σ a² ≤ (Σ a)²` always — the off-diagonal cross terms are ≥ 0), so
    /// `refute_conjecture` must NOT manufacture a counterexample. (The nonneg
    /// hypothesis is essential: e.g. `a = (1, -1)` gives `Σa² = 2 > 0 = (Σa)²`.)
    #[test]
    fn test_h1_not_refuted() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.fin_sum_sq_le_sq_sum_nonneg",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "H1 (nonneg Σa² ≤ (Σa)²) is a TRUE implication; must NOT refute"
        );
    }
}
