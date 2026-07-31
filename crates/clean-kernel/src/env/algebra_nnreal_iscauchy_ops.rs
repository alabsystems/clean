// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — closure of `NNReal.IsCauchy` under pointwise addition.
//!
//! # Why this module exists
//!
//! With the Cauchy SUBTYPE carrier (`algebra_nnreal_cauchy.rs`), every
//! `NNReal.CauSeq.mk` requires an `IsCauchy` proof for the underlying sequence.
//! `NNReal.CauSeq.add` builds the pointwise-sum sequence `fun n => NNRat.add
//! (seq f n)(seq g n)`, so it needs:
//!
//! - `NNReal.IsCauchy_add : ∀ (f g : Nat → NNRat), IsCauchy f → IsCauchy g →
//!       IsCauchy (fun n => NNRat.add (f n)(g n))`
//!
//! Proof (ε/2 split, like `Equiv.trans`): instantiate `hf`,`hg` at `ε/2`
//! (positivity from `Rat.half_pos`), take `N := Nat.max N1 N2`. For `m,n ≥ N`,
//! `val (f m) < val (f n) + ε/2` and `val (g m) < val (g n) + ε/2`, so by
//! `Rat.add_lt_add` `(vf m + vg m) < (vf n + ε/2) + (vg n + ε/2)`, then the
//! recombination `(a + ε/2) + (b + ε/2) = (a + b) + ε` (assoc/comm/`add_halves`)
//! and `NNRat.val_add` transport land it at `val(add(f m)(g m)) <
//! val(add(f n)(g n)) + ε`. Symmetric for the reverse conjunct.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `IsCauchy_add`.
pub(crate) struct IsCauchyAddConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_two: Expr,
    nnrat: Expr,
    nnrat_add: Expr,
    nnrat_val: Expr,
    nnrat_val_add: Expr,
    is_cauchy: Expr,
    rat_add: Expr,
    rat_div: Expr,
    rat_lt: Expr,
    nat_le: Expr,
    // Lemmas.
    rat_half_pos: Expr,
    rat_add_lt_add: Expr,
    rat_add_assoc: Expr,
    rat_add_comm: Expr,
    rat_add_halves: Expr,
    nat_max: Expr,
    nat_le_max_left: Expr,
    nat_le_max_right: Expr,
    nat_le_trans: Expr,
    // Logic.
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    // Eq.{1} over Rat.
    #[cfg(test)]
    eq_rat: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
}

impl IsCauchyAddConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_two: k("Rat.two"),
            nnrat: k("NNRat"),
            nnrat_add: k("NNRat.add"),
            nnrat_val: k("NNRat.val"),
            nnrat_val_add: k("NNRat.val_add"),
            is_cauchy: k("NNReal.IsCauchy"),
            rat_add: k("Rat.add"),
            rat_div: k("Rat.div"),
            rat_lt: k("Rat.lt"),
            nat_le: k("Nat.le"),
            rat_half_pos: k("Rat.half_pos"),
            rat_add_lt_add: k("Rat.add_lt_add"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_comm: k("Rat.add_comm"),
            rat_add_halves: k("Rat.add_halves"),
            nat_max: k("Nat.max"),
            nat_le_max_left: k("Nat.le_max_left"),
            nat_le_max_right: k("Nat.le_max_right"),
            nat_le_trans: k("Nat.le_trans"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![lvl1.clone()]),
            #[cfg(test)]
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]),
        }
    }

    fn seq_ty(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.nat.clone(), self.nnrat.clone())
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn half(&self, eps: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [eps, self.rat_two.clone()])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    /// `NNRat.val (NNRat.add a b) : Rat`.
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    /// `NNRat.add a b : NNRat`.
    fn nnadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_add.clone(), [a, b])
    }
    /// `f n : NNRat`.
    fn at(&self, f: &Expr, n: &Expr) -> Expr {
        Expr::app(f.clone(), n.clone())
    }
    /// `val (f n) : Rat`.
    fn vat(&self, f: &Expr, n: &Expr) -> Expr {
        self.val(self.at(f, n))
    }
    fn is_cauchy(&self, f: Expr) -> Expr {
        Expr::app(self.is_cauchy.clone(), f)
    }
    /// The two-sided bound `And (Rat.lt x (y+ε)) (Rat.lt y (x+ε))`.
    fn bound_pair(&self, x: Expr, y: Expr, eps: Expr) -> Expr {
        let left = self.lt(x.clone(), self.add(y.clone(), eps.clone()));
        let right = self.lt(y, self.add(x, eps));
        self.and_ty(left, right)
    }
    fn and_left(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_left.clone(), [p, q, h])
    }
    fn and_right(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_right.clone(), [p, q, h])
    }
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p, q, hp, hq])
    }
    /// `Rat.add_lt_add a b c d hab hcd : (a+c) < (b+d)`.
    fn add_lt_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add.clone(), [a, b, cc, d, hab, hcd])
    }
    /// `Rat.add_assoc a b c : Eq Rat ((a+b)+c) (a+(b+c))`.
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    /// `Rat.add_comm a b : Eq Rat (a+b) (b+a)`.
    fn add_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add_comm.clone(), [a, b])
    }
    /// `Rat.add_halves eps : Eq Rat ((eps/2)+(eps/2)) eps`.
    fn add_halves(&self, eps: Expr) -> Expr {
        Expr::app(self.rat_add_halves.clone(), eps)
    }
    /// `@Eq.symm Rat a b h : Eq Rat b a`.
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    /// `@Eq.trans Rat a b c hab hbc : Eq Rat a c`.
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@congrArg Rat Rat a a' f h : Eq Rat (f a)(f a')`.
    fn congr_arg(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    /// `NNRat.val_add p q : Eq Rat (val (NNRat.add p q)) ((val p)+(val q))`.
    fn val_add(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_add.clone(), [p, q])
    }
    fn nat_le_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.nat_le_trans.clone(), [a, b, cc, hab, hbc])
    }

    /// The pointwise-sum raw sequence `fun n => NNRat.add (f n)(g n)`.
    fn sum_seq(&self, parent: &EnvDeclBuilder, f: &Expr, g: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n) = bn.fresh_local(self.nat.clone());
        let body = self.nnadd(self.at(f, &n), self.at(g, &n));
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), body))
    }

    /// `eq_recombine_pair a b eps : Eq Rat ((a+ε/2)+(b+ε/2)) ((a+b)+ε)`.
    ///
    /// Chain (`h := ε/2`):
    ///   (a+h)+(b+h)
    ///     = ((a+h)+b)+h      [symm assoc (a+h) b h]
    ///     = ((a+b)+h)+h      [congrArg (·+h) ((a+h)+b = (a+b)+h)]
    ///     = (a+b)+(h+h)      [assoc (a+b) h h]
    ///     = (a+b)+ε          [congrArg ((a+b)+·) (add_halves ε)]
    /// where `(a+h)+b = (a+b)+h` is itself:
    ///   (a+h)+b = a+(h+b) [assoc a h b] = a+(b+h) [congrArg (a+·)(comm h b)]
    ///           = (a+b)+h [symm assoc a b h].
    fn eq_recombine_pair(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        let h = self.half(eps.clone());
        let a_h = self.add(a.clone(), h.clone()); // a+h
        let b_h = self.add(b.clone(), h.clone()); // b+h
        let a_b = self.add(a.clone(), b.clone()); // a+b
        let hh = self.add(h.clone(), h.clone()); // h+h

        // sub : (a+h)+b = (a+b)+h.
        let sub = {
            // assoc a h b : (a+h)+b = a+(h+b).
            let s1 = self.add_assoc(a.clone(), h.clone(), b.clone());
            // congrArg (a+·) (comm h b) : a+(h+b) = a+(b+h).
            let comm = self.add_comm(h.clone(), b.clone());
            let add_a_fn = {
                let mut fb = EnvDeclBuilder::child_of(parent);
                let (t_id, t) = fb.fresh_local(self.rat.clone());
                let body = self.add(a.clone(), t);
                fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
            };
            let s2 = self.congr_arg(self.add(h.clone(), b.clone()), b_h.clone(), add_a_fn, comm);
            // symm assoc a b h : a+(b+h) = (a+b)+h.
            let s3 = self.eq_symm(
                self.add(a_b.clone(), h.clone()),
                self.add(a.clone(), b_h.clone()),
                self.add_assoc(a.clone(), b.clone(), h.clone()),
            );
            // chain (a+h)+b → a+(h+b) → a+(b+h) → (a+b)+h.
            let t_ahb = self.add(a_h.clone(), b.clone());
            let t_a_hb = self.add(a.clone(), self.add(h.clone(), b.clone()));
            let t_a_bh = self.add(a.clone(), b_h.clone());
            let t_abh = self.add(a_b.clone(), h.clone());
            let c1 = self.eq_trans(t_ahb.clone(), t_a_hb, t_a_bh.clone(), s1, s2);
            self.eq_trans(t_ahb, t_a_bh, t_abh, c1, s3)
        };

        // step A: (a+h)+(b+h) = ((a+h)+b)+h   [symm assoc (a+h) b h].
        let step_a = self.eq_symm(
            self.add(self.add(a_h.clone(), b.clone()), h.clone()),
            self.add(a_h.clone(), b_h.clone()),
            self.add_assoc(a_h.clone(), b.clone(), h.clone()),
        );
        // step B: ((a+h)+b)+h = ((a+b)+h)+h   [congrArg (·+h) sub].
        let add_h_fn = {
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = fb.fresh_local(self.rat.clone());
            let body = self.add(t, h.clone());
            fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let step_b = self.congr_arg(
            self.add(a_h.clone(), b.clone()),
            self.add(a_b.clone(), h.clone()),
            add_h_fn,
            sub,
        );
        // step C: ((a+b)+h)+h = (a+b)+(h+h)   [assoc (a+b) h h].
        let step_c = self.add_assoc(a_b.clone(), h.clone(), h.clone());
        // step D: (a+b)+(h+h) = (a+b)+ε       [congrArg ((a+b)+·) (add_halves ε)].
        let add_ab_fn = {
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = fb.fresh_local(self.rat.clone());
            let body = self.add(a_b.clone(), t);
            fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let step_d = self.congr_arg(
            hh.clone(),
            eps.clone(),
            add_ab_fn,
            self.add_halves(eps.clone()),
        );

        // chain A→B→C→D.
        let t0 = self.add(a_h.clone(), b_h.clone()); // (a+h)+(b+h)
        let t1 = self.add(self.add(a_h.clone(), b.clone()), h.clone()); // ((a+h)+b)+h
        let t2 = self.add(self.add(a_b.clone(), h.clone()), h.clone()); // ((a+b)+h)+h
        let t3 = self.add(a_b.clone(), hh); // (a+b)+(h+h)
        let t4 = self.add(a_b.clone(), eps.clone()); // (a+b)+ε
        let c1 = self.eq_trans(t0.clone(), t1.clone(), t2.clone(), step_a, step_b);
        let c2 = self.eq_trans(t0.clone(), t2.clone(), t3.clone(), c1, step_c);
        self.eq_trans(t0, t3, t4, c2, step_d)
    }
}

impl Environment {
    /// Register `NNReal.IsCauchy_add`. Idempotent.
    pub fn init_algebra_nnreal_iscauchy_ops(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cauchy()?; // IsCauchy, CauSeq, NNRat.*
        self.init_algebra_rat_half_pos()?; // Rat.half_pos, Rat.add_halves, Rat.two
        self.register_rat_add_lt_add()?; // Rat.add_lt_add
        self.init_rat_field_inst()?; // Rat.add_assoc, Rat.add_comm
        self.register_nat_minmax_proofs()?; // Nat.max, Nat.le_max_left/right
        self.register_nat_le_trans_proof()?; // Nat.le_trans

        let c = IsCauchyAddConsts::new();
        self.register_nnreal_is_cauchy_add(&c)
    }

    fn register_nnreal_is_cauchy_add(&mut self, c: &IsCauchyAddConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.IsCauchy_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.seq_ty());
            let (g_id, g) = b.fresh_local(c.seq_ty());
            let hf = c.is_cauchy(f.clone());
            let (hf_id, _h) = b.fresh_local(hf.clone());
            let hg = c.is_cauchy(g.clone());
            let (hg_id, _h2) = b.fresh_local(hg.clone());
            let sum = c.sum_seq(&b, &f, &g);
            let concl = c.is_cauchy(sum);
            let e = b.mk_pi(hg_id, BinderInfo::Default, hg, concl);
            let e = b.mk_pi(hf_id, BinderInfo::Default, hf, e);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.seq_ty(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.seq_ty(), e);
            b.finish(e)
        };
        let value = build_is_cauchy_add_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `pred_n f g eps N` fully applied with `N := cap`:
/// `∀ m n, N≤m → N≤n → bound_pair (val(f m))(val(f n)) eps` — the IsCauchy
/// witness predicate for a single sequence `f` (the `g` slot mirrors `f`).
/// Here used to spell the type of the `Exists.elim` hypotheses (over `f`/`g`).
fn pred_at(
    c: &IsCauchyAddConsts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    eps: &Expr,
    cap: &Expr,
) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = bn.fresh_local(c.nat.clone());
    let (n_id, n) = bn.fresh_local(c.nat.clone());
    let hle_m = c.nat_le(cap.clone(), m.clone());
    let (hlem_id, _h) = bn.fresh_local(hle_m.clone());
    let hle_n = c.nat_le(cap.clone(), n.clone());
    let (hlen_id, _h2) = bn.fresh_local(hle_n.clone());
    let concl = c.bound_pair(c.vat(f, &m), c.vat(f, &n), eps.clone());
    let e = bn.mk_pi(hlen_id, BinderInfo::Default, hle_n, concl);
    let e = bn.mk_pi(hlem_id, BinderInfo::Default, hle_m, e);
    let e = bn.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = bn.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    bn.finish_child(e)
}

/// The full `∃ N, pred N` for a sequence `f` at tolerance `eps`.
fn exists_pred(c: &IsCauchyAddConsts, parent: &EnvDeclBuilder, f: &Expr, eps: &Expr) -> Expr {
    let pred = {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (cap_id, cap) = bn.fresh_local(c.nat.clone());
        let body = pred_at(c, &bn, f, eps, &cap);
        bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), body))
    };
    Expr::apps(c.exists_c.clone(), [c.nat.clone(), pred])
}

fn pred_lambda(c: &IsCauchyAddConsts, parent: &EnvDeclBuilder, f: &Expr, eps: &Expr) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (cap_id, cap) = bn.fresh_local(c.nat.clone());
    let body = pred_at(c, &bn, f, eps, &cap);
    bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), body))
}

/// Build the proof term for `NNReal.IsCauchy_add`.
fn build_is_cauchy_add_proof(c: &IsCauchyAddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.seq_ty());
    let (g_id, g) = b.fresh_local(c.seq_ty());
    let hf_ty = c.is_cauchy(f.clone());
    let (hf_id, hf) = b.fresh_local(hf_ty.clone());
    let hg_ty = c.is_cauchy(g.clone());
    let (hg_id, hg) = b.fresh_local(hg_ty.clone());

    let sum = c.sum_seq(&b, &f, &g);

    // Goal: IsCauchy sum = ∀ ε, 0<ε → ∃ N, ∀ m n, N≤m → N≤n →
    //   bound_pair (val(sum m))(val(sum n)) ε.
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let half = c.half(eps.clone());
    let heps2 = Expr::apps(c.rat_half_pos.clone(), [eps.clone(), hpos.clone()]);

    // hf (ε/2) heps2 : ∃ N1, ∀ m n, N1≤m → N1≤n → bound_pair (vf m)(vf n) (ε/2).
    let exists_f = Expr::apps(hf.clone(), [half.clone(), heps2.clone()]);
    let exists_g = Expr::apps(hg.clone(), [half.clone(), heps2]);

    // Goal exists over the sum sequence at ε.
    let goal_exists = exists_pred(c, &b, &sum, &eps);

    let pred_f = pred_lambda(c, &b, &f, &half);
    let pred_g = pred_lambda(c, &b, &g, &half);

    let elim_outer = {
        let mut bo = EnvDeclBuilder::child_of(&b);
        let (n1_id, n1) = bo.fresh_local(c.nat.clone());
        let hn1_ty = pred_at(c, &bo, &f, &half, &n1);
        let (hn1_id, hn1) = bo.fresh_local(hn1_ty.clone());

        let elim_inner = {
            let mut bi = EnvDeclBuilder::child_of(&bo);
            let (n2_id, n2) = bi.fresh_local(c.nat.clone());
            let hn2_ty = pred_at(c, &bi, &g, &half, &n2);
            let (hn2_id, hn2) = bi.fresh_local(hn2_ty.clone());

            let nmax = Expr::apps(c.nat_max.clone(), [n1.clone(), n2.clone()]);

            // witness : ∀ m n, N≤m → N≤n → bound_pair (val(sum m))(val(sum n)) ε.
            let witness = {
                let mut bw = EnvDeclBuilder::child_of(&bi);
                let (m_id, m) = bw.fresh_local(c.nat.clone());
                let (n_id, n) = bw.fresh_local(c.nat.clone());
                let hle_m_ty = c.nat_le(nmax.clone(), m.clone());
                let (hlem_id, hle_m) = bw.fresh_local(hle_m_ty.clone());
                let hle_n_ty = c.nat_le(nmax.clone(), n.clone());
                let (hlen_id, hle_n) = bw.fresh_local(hle_n_ty.clone());

                // N1≤m, N1≤n, N2≤m, N2≤n via le_trans through max.
                let le_max_l = Expr::apps(c.nat_le_max_left.clone(), [n1.clone(), n2.clone()]);
                let le_max_r = Expr::apps(c.nat_le_max_right.clone(), [n1.clone(), n2.clone()]);
                let n1_le_m = c.nat_le_trans(
                    n1.clone(),
                    nmax.clone(),
                    m.clone(),
                    le_max_l.clone(),
                    hle_m.clone(),
                );
                let n1_le_n =
                    c.nat_le_trans(n1.clone(), nmax.clone(), n.clone(), le_max_l, hle_n.clone());
                let n2_le_m =
                    c.nat_le_trans(n2.clone(), nmax.clone(), m.clone(), le_max_r.clone(), hle_m);
                let n2_le_n = c.nat_le_trans(n2.clone(), nmax.clone(), n.clone(), le_max_r, hle_n);

                // base_f : bound_pair (vf m)(vf n) (ε/2) := hn1 m n n1_le_m n1_le_n.
                let base_f = Expr::apps(hn1.clone(), [m.clone(), n.clone(), n1_le_m, n1_le_n]);
                let base_g = Expr::apps(hn2.clone(), [m.clone(), n.clone(), n2_le_m, n2_le_n]);

                let vfm = c.vat(&f, &m);
                let vfn = c.vat(&f, &n);
                let vgm = c.vat(&g, &m);
                let vgn = c.vat(&g, &n);

                // conjuncts.
                let lf = c.lt(vfm.clone(), c.add(vfn.clone(), half.clone()));
                let rf = c.lt(vfn.clone(), c.add(vfm.clone(), half.clone()));
                let lg = c.lt(vgm.clone(), c.add(vgn.clone(), half.clone()));
                let rg = c.lt(vgn.clone(), c.add(vgm.clone(), half.clone()));
                let a_f = c.and_left(lf.clone(), rf.clone(), base_f.clone()); // vfm < vfn+h
                let b_f = c.and_right(lf, rf, base_f); // vfn < vfm+h
                let a_g = c.and_left(lg.clone(), rg.clone(), base_g.clone()); // vgm < vgn+h
                let b_g = c.and_right(lg, rg, base_g); // vgn < vgm+h

                // forward: (vfm+vgm) < (vfn+h)+(vgn+h)  := add_lt_add … a_f a_g.
                let fwd_raw = c.add_lt_add(
                    vfm.clone(),
                    c.add(vfn.clone(), half.clone()),
                    vgm.clone(),
                    c.add(vgn.clone(), half.clone()),
                    a_f,
                    a_g,
                );
                // recombine RHS: (vfn+h)+(vgn+h) = (vfn+vgn)+ε.
                let rec_fwd = c.eq_recombine_pair(&bw, &vfn, &vgn, &eps);
                let vfm_vgm = c.add(vfm.clone(), vgm.clone());
                let rhs_fwd = c.add(
                    c.add(vfn.clone(), half.clone()),
                    c.add(vgn.clone(), half.clone()),
                );
                let vfn_vgn_eps = c.add(c.add(vfn.clone(), vgn.clone()), eps.clone());
                let motive_fwd = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.lt(vfm_vgm.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // fwd_sum : (vfm+vgm) < (vfn+vgn)+ε.
                let fwd_sum = c.subst(motive_fwd, rhs_fwd, vfn_vgn_eps.clone(), rec_fwd, fwd_raw);

                // reverse: (vfn+vgn) < (vfm+h)+(vgm+h)  := add_lt_add … b_f b_g.
                let rev_raw = c.add_lt_add(
                    vfn.clone(),
                    c.add(vfm.clone(), half.clone()),
                    vgn.clone(),
                    c.add(vgm.clone(), half.clone()),
                    b_f,
                    b_g,
                );
                let rec_rev = c.eq_recombine_pair(&bw, &vfm, &vgm, &eps);
                let vfn_vgn = c.add(vfn.clone(), vgn.clone());
                let rhs_rev = c.add(
                    c.add(vfm.clone(), half.clone()),
                    c.add(vgm.clone(), half.clone()),
                );
                let vfm_vgm_eps = c.add(vfm_vgm.clone(), eps.clone());
                let motive_rev = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.lt(vfn_vgn.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let rev_sum = c.subst(motive_rev, rhs_rev, vfm_vgm_eps.clone(), rec_rev, rev_raw);

                // Now transport the Rat-sum endpoints back to val(sum m)/val(sum n).
                // val(sum m) ≡ val(NNRat.add (f m)(g m)) (defeq, sum m reduces), and
                // val_add (f m)(g m) : that = (vfm+vgm). Substitute both endpoints.
                let valadd_m = c.val_add(c.at(&f, &m), c.at(&g, &m)); // val(add(f m)(g m)) = vfm+vgm
                let valadd_n = c.val_add(c.at(&f, &n), c.at(&g, &n)); // val(add(f n)(g n)) = vfn+vgn
                let vsumm = c.val(c.nnadd(c.at(&f, &m), c.at(&g, &m))); // val(add(f m)(g m))
                let vsumn = c.val(c.nnadd(c.at(&f, &n), c.at(&g, &n))); // val(add(f n)(g n))

                // forward final: vsumm < vsumn + ε.
                // step 1: rewrite RHS summand vfn_vgn → vsumn via symm valadd_n.
                let mfwd_rhs = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.lt(vfm_vgm.clone(), c.add(t, eps.clone()));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let fwd1 = c.subst(
                    mfwd_rhs,
                    vfn_vgn.clone(),
                    vsumn.clone(),
                    c.eq_symm(vsumn.clone(), vfn_vgn.clone(), valadd_n.clone()),
                    fwd_sum,
                );
                // step 2: rewrite LHS vfm_vgm → vsumm via symm valadd_m.
                let mfwd_lhs = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.lt(t, c.add(vsumn.clone(), eps.clone()));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let fwd = c.subst(
                    mfwd_lhs,
                    vfm_vgm.clone(),
                    vsumm.clone(),
                    c.eq_symm(vsumm.clone(), vfm_vgm.clone(), valadd_m.clone()),
                    fwd1,
                );

                // reverse final: vsumn < vsumm + ε.
                let mrev_rhs = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.lt(vfn_vgn.clone(), c.add(t, eps.clone()));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let rev1 = c.subst(
                    mrev_rhs,
                    vfm_vgm.clone(),
                    vsumm.clone(),
                    c.eq_symm(vsumm.clone(), vfm_vgm.clone(), valadd_m),
                    rev_sum,
                );
                let mrev_lhs = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.lt(t, c.add(vsumm.clone(), eps.clone()));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let rev = c.subst(
                    mrev_lhs,
                    vfn_vgn.clone(),
                    vsumn.clone(),
                    c.eq_symm(vsumn.clone(), vfn_vgn.clone(), valadd_n),
                    rev1,
                );

                let l_final = c.lt(vsumm.clone(), c.add(vsumn.clone(), eps.clone()));
                let r_final = c.lt(vsumn.clone(), c.add(vsumm.clone(), eps.clone()));
                let proof = c.and_intro(l_final, r_final, fwd, rev);

                let e = bw.mk_lam(hlen_id, BinderInfo::Default, hle_n_ty, proof);
                let e = bw.mk_lam(hlem_id, BinderInfo::Default, hle_m_ty, e);
                let e = bw.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
                let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
                bw.finish_child(e)
            };

            // Exists.intro Nat (pred sum ε) nmax witness.
            let pred_sum = pred_lambda(c, &bi, &sum, &eps);
            let intro = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), pred_sum, nmax, witness],
            );
            let e = bi.mk_lam(hn2_id, BinderInfo::Default, hn2_ty, intro);
            let e = bi.mk_lam(n2_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };

        let elim_g = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nat.clone(),
                pred_g.clone(),
                goal_exists.clone(),
                exists_g.clone(),
                elim_inner,
            ],
        );
        let e = bo.mk_lam(hn1_id, BinderInfo::Default, hn1_ty, elim_g);
        let e = bo.mk_lam(n1_id, BinderInfo::Default, c.nat.clone(), e);
        bo.finish_child(e)
    };

    let elim_f = Expr::apps(
        c.exists_elim.clone(),
        [
            c.nat.clone(),
            pred_f.clone(),
            goal_exists,
            exists_f,
            elim_outer,
        ],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim_f);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(hg_id, BinderInfo::Default, hg_ty, e);
    let e = b.mk_lam(hf_id, BinderInfo::Default, hf_ty, e);
    let e = b.mk_lam(g_id, BinderInfo::Default, c.seq_ty(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.seq_ty(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_is_cauchy_add_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_iscauchy_ops()
            .expect("init_algebra_nnreal_iscauchy_ops");
        env.init_algebra_nnreal_iscauchy_ops().expect("idempotent");

        let nm = Name::from_string("NNReal.IsCauchy_add");
        let info = env.get_const(&nm).expect("IsCauchy_add registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("IsCauchy_add must kernel-check");

        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }
}
