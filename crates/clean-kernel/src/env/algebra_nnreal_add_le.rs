// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `NNReal.add_le_add` (additive monotonicity of `le`).
//!
//! # Why this module exists
//!
//! With `NNReal.add` (the lifted sum) and `NNReal.le` (the lifted strict-eventual
//! order) both landed, the ordered-monoid compatibility law
//! `x ≤ x' → y ≤ y' → x + y ≤ x' + y'` is the natural next rung. It lifts
//! through a 4-fold `Quot.ind` to a statement about representatives:
//!   `CauSeq.LE p p' → CauSeq.LE q q' → CauSeq.LE (add p q)(add p' q')`.
//!
//! # The per-index combination
//!
//! Instantiate both hypotheses at `ε/2`, take `N := Nat.max N1 N2`; at `n ≥ N`:
//!   `vp < vp' + ε/2`   and   `vq < vq' + ε/2`.
//! `Rat.add_lt_add` combines them: `(vp+vq) < ((vp'+ε/2)+(vq'+ε/2))`. The RHS
//! recombines to `(vp'+vq') + ε` via the 4-way regroup
//! `(a+h)+(b+h) = (a+b)+(h+h) = (a+b)+ε` (built here from `Rat.add_assoc` /
//! `Rat.add_comm` / `Rat.add_halves` — no new Rat axiom). Finally `NNRat.val_add`
//! rewrites `vp+vq → val(seq(add p q) n)` and `vp'+vq' → val(seq(add p' q') n)`,
//! giving exactly `CauSeq.LE (add p q)(add p' q')` at `n`.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.add_le_add : ∀ x x' y y',
//!       NNReal.le x x' → NNReal.le y y' → NNReal.le (NNReal.add x y)(NNReal.add x' y')`
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::algebra_nnreal_le_recovered::NNLeConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Extra handles `add_le_add` needs on top of `NNLeConsts` (the `NNRat`/`Rat`
/// sum machinery and `Rat.add_lt_add`/`add_comm`).
struct AddLeConsts {
    le: NNLeConsts,
    causeq_add: Expr,
    nnrat_add: Expr,
    nnrat_val: Expr,
    nnrat_val_add: Expr,
    rat_add_lt_add: Expr,
    rat_add_comm: Expr,
    eq_symm: Expr,
}

impl AddLeConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let lvl1 = Level::succ(Level::zero());
        Self {
            le: NNLeConsts::new(),
            causeq_add: k("NNReal.CauSeq.add"),
            nnrat_add: k("NNRat.add"),
            nnrat_val: k("NNRat.val"),
            nnrat_val_add: k("NNRat.val_add"),
            rat_add_lt_add: k("Rat.add_lt_add"),
            rat_add_comm: k("Rat.add_comm"),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1]),
        }
    }

    fn c(&self) -> &NNLeConsts {
        &self.le
    }
    /// `NNReal.CauSeq.add f g : CauSeq`.
    fn cauadd(&self, f: Expr, g: Expr) -> Expr {
        Expr::apps(self.causeq_add.clone(), [f, g])
    }
    /// `NNReal.CauSeq.seq f n : NNRat`.
    fn seq_at(&self, f: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.le.causeq_seq.clone(), f.clone()), n.clone())
    }
    /// `NNRat.val q : Rat`.
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    /// `NNRat.add a b : NNRat`.
    fn nnadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_add.clone(), [a, b])
    }
    /// `NNRat.val_add p q : Eq Rat (val (NNRat.add p q)) ((val p)+(val q))`.
    fn val_add(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_add.clone(), [p, q])
    }
    /// `Rat.add_lt_add a b cc d h1 h2 : (a+cc) < (b+d)`.
    fn add_lt_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add.clone(), [a, b, cc, d, h1, h2])
    }
    /// `Rat.add_comm a b : Eq Rat (a+b) (b+a)`.
    fn add_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add_comm.clone(), [a, b])
    }
    /// `@Eq.symm Rat a b h : Eq Rat b a`.
    fn eq_symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.le.rat.clone(), a, b, h])
    }

    /// `(a+h)+(b+h) = (a+b)+ε`, where `h = ε/2`. Pure `Rat` rewrite chain built
    /// from `add_assoc` / `add_comm` / `add_halves`.
    fn regroup4(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        let c = self.c();
        let h = c.half(eps.clone());
        let a_h = c.add(a.clone(), h.clone()); // a+h
        let b_h = c.add(b.clone(), h.clone()); // b+h
        let a_b = c.add(a.clone(), b.clone()); // a+b
        let h_h = c.add(h.clone(), h.clone()); // h+h

        // s1 : (a+h)+(b+h) = ((a+h)+b)+h   [symm (add_assoc (a+h) b h)].
        let assoc1 = c.add_assoc(a_h.clone(), b.clone(), h.clone()); // ((a+h)+b)+h = (a+h)+(b+h)
        let ahb = c.add(a_h.clone(), b.clone()); // (a+h)+b
        let ahb_h = c.add(ahb.clone(), h.clone()); // ((a+h)+b)+h
        let s1 = self.eq_symm_rat(ahb_h.clone(), c.add(a_h.clone(), b_h.clone()), assoc1);

        // e_ahb : (a+h)+b = (a+b)+h.
        //   (a+h)+b =[add_assoc a h b] a+(h+b) =[congr (a+·)(comm h b)] a+(b+h)
        //           =[symm (add_assoc a b h)] (a+b)+h.
        let asc_a_h_b = c.add_assoc(a.clone(), h.clone(), b.clone()); // (a+h)+b = a+(h+b)
        let h_b = c.add(h.clone(), b.clone());
        let b_h2 = c.add(b.clone(), h.clone());
        let comm_hb = self.add_comm(h.clone(), b.clone()); // h+b = b+h
        let add_a_fn = {
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = fb.fresh_local(c.rat.clone());
            let body = c.add(a.clone(), t);
            fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let congr_a = c.congr_arg(h_b.clone(), b_h2.clone(), add_a_fn, comm_hb); // a+(h+b)=a+(b+h)
        let a_hb = c.add(a.clone(), h_b.clone());
        let a_bh = c.add(a.clone(), b_h2.clone());
        let t1 = c.eq_trans_rat(ahb.clone(), a_hb, a_bh.clone(), asc_a_h_b, congr_a); // (a+h)+b = a+(b+h)
        let asc_a_b_h = c.add_assoc(a.clone(), b.clone(), h.clone()); // (a+b)+h = a+(b+h)
        let ab_h = c.add(a_b.clone(), h.clone());
        let asc_a_b_h_sym = self.eq_symm_rat(ab_h.clone(), a_bh.clone(), asc_a_b_h); // a+(b+h)=(a+b)+h
        let e_ahb = c.eq_trans_rat(ahb.clone(), a_bh, ab_h.clone(), t1, asc_a_b_h_sym); // (a+h)+b=(a+b)+h

        // s2 : ((a+h)+b)+h = ((a+b)+h)+h   [congr (·+h) e_ahb].
        let add_h_fn = {
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = fb.fresh_local(c.rat.clone());
            let body = c.add(t, h.clone());
            fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let abh_h = c.add(ab_h.clone(), h.clone()); // ((a+b)+h)+h
        let s2 = c.congr_arg(ahb.clone(), ab_h.clone(), add_h_fn, e_ahb);

        // s3 : ((a+b)+h)+h = (a+b)+(h+h)   [add_assoc (a+b) h h].
        let s3 = c.add_assoc(a_b.clone(), h.clone(), h.clone());
        let ab_hh = c.add(a_b.clone(), h_h.clone()); // (a+b)+(h+h)

        // s4 : (a+b)+(h+h) = (a+b)+ε   [congr ((a+b)+·)(add_halves eps)].
        let add_ab_fn = {
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = fb.fresh_local(c.rat.clone());
            let body = c.add(a_b.clone(), t);
            fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let s4 = c.congr_arg(
            h_h.clone(),
            eps.clone(),
            add_ab_fn,
            c.add_halves(eps.clone()),
        );
        let ab_eps = c.add(a_b.clone(), eps.clone());

        // chain: (a+h)+(b+h) →s1 ((a+h)+b)+h →s2 ((a+b)+h)+h →s3 (a+b)+(h+h) →s4 (a+b)+ε.
        let ahbh = c.add(a_h.clone(), b_h.clone());
        let c1 = c.eq_trans_rat(ahbh.clone(), ahb_h.clone(), abh_h.clone(), s1, s2);
        let c2 = c.eq_trans_rat(ahbh.clone(), abh_h, ab_hh.clone(), c1, s3);
        c.eq_trans_rat(ahbh, ab_hh, ab_eps, c2, s4)
    }
}

impl Environment {
    /// Register `NNReal.add_le_add`. Idempotent. Pulls in `NNReal.le` (hence the
    /// whole carrier + order), `NNReal.add`, `Rat.add_lt_add`, `Rat.add_comm`.
    pub fn init_algebra_nnreal_add_le(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_le()?;
        self.init_algebra_nnreal_add()?; // NNReal.CauSeq.add, NNReal.add, val_add
        self.register_rat_add_lt_add()?; // Rat.add_lt_add
        self.register_rat_add_comm_proof()?; // Rat.add_comm

        let c = AddLeConsts::new();
        self.register_nnreal_add_le_add_recovered(&c)
    }

    fn register_nnreal_add_le_add_recovered(&mut self, c: &AddLeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add_le_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nn = c.c();
        let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
        let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
        let le = |a: Expr, b: Expr| Expr::apps(nnle.clone(), [a, b]);
        let add = |a: Expr, b: Expr| Expr::apps(nnadd.clone(), [a, b]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(nn.nnreal.clone());
            let (x2_id, x2) = b.fresh_local(nn.nnreal.clone());
            let (y_id, y) = b.fresh_local(nn.nnreal.clone());
            let (y2_id, y2) = b.fresh_local(nn.nnreal.clone());
            let hx = le(x.clone(), x2.clone());
            let (hx_id, _) = b.fresh_local(hx.clone());
            let hy = le(y.clone(), y2.clone());
            let (hy_id, _) = b.fresh_local(hy.clone());
            let concl = le(add(x.clone(), y.clone()), add(x2.clone(), y2.clone()));
            let e = b.mk_pi(hy_id, BinderInfo::Default, hy, concl);
            let e = b.mk_pi(hx_id, BinderInfo::Default, hx, e);
            let e = b.mk_pi(y2_id, BinderInfo::Default, nn.nnreal.clone(), e);
            let e = b.mk_pi(y_id, BinderInfo::Default, nn.nnreal.clone(), e);
            let e = b.mk_pi(x2_id, BinderInfo::Default, nn.nnreal.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, nn.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_add_le_add_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Proof of `NNReal.add_le_add` via 4-fold `Quot.ind` (x, x', y, y').
fn build_add_le_add_proof(c: &AddLeConsts) -> Expr {
    let nn = c.c();
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let le = |a: Expr, b: Expr| Expr::apps(nnle.clone(), [a, b]);
    let add = |a: Expr, b: Expr| Expr::apps(nnadd.clone(), [a, b]);

    // Build the goal-after-binders motive body `lhs/rhs` for a (possibly
    // partially-mk'd) tuple. We nest 4 inductions; the innermost leaf builds the
    // CauSeq-level proof. We construct it bottom-up via helper closures, but
    // because Rust closures can't easily recurse with captured state, we inline
    // the 4 nested `Quot.ind`s explicitly (mirroring `add_assoc`/`le_trans`).

    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(nn.nnreal.clone());
    let (x2_id, x2) = b.fresh_local(nn.nnreal.clone());
    let (y_id, y) = b.fresh_local(nn.nnreal.clone());
    let (y2_id, y2) = b.fresh_local(nn.nnreal.clone());

    // The hypotheses-then-conclusion body for the goal, given the four NNReal
    // arguments (some of which may be `mk _`):
    let goal = |xx: &Expr, xx2: &Expr, yy: &Expr, yy2: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let hx = le(xx.clone(), xx2.clone());
        let (hx_id, _) = mb.fresh_local(hx.clone());
        let hy = le(yy.clone(), yy2.clone());
        let (hy_id, _) = mb.fresh_local(hy.clone());
        let concl = le(add(xx.clone(), yy.clone()), add(xx2.clone(), yy2.clone()));
        let e = mb.mk_pi(hy_id, BinderInfo::Default, hy, concl);
        let e = mb.mk_pi(hx_id, BinderInfo::Default, hx, e);
        mb.finish_child(e)
    };

    // Innermost (after all four are mk p / mk p' / mk q / mk q'): build the
    // function `fun hx hy => <CauSeq.LE proof>`.
    let leaf = |p: &Expr, p2: &Expr, q: &Expr, q2: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let mk_p = nn.quot_mk(p.clone());
        let mk_p2 = nn.quot_mk(p2.clone());
        let mk_q = nn.quot_mk(q.clone());
        let mk_q2 = nn.quot_mk(q2.clone());
        let hx_ty = le(mk_p.clone(), mk_p2.clone()); // ≡ CauSeq.LE p p2
        let (hx_id, hx) = mb.fresh_local(hx_ty.clone());
        let hy_ty = le(mk_q.clone(), mk_q2.clone()); // ≡ CauSeq.LE q q2
        let (hy_id, hy) = mb.fresh_local(hy_ty.clone());
        let body = build_causeq_add_le(c, &mb, p, p2, q, q2, &hx, &hy);
        let e = mb.mk_lam(hy_id, BinderInfo::Default, hy_ty, body);
        let e = mb.mk_lam(hx_id, BinderInfo::Default, hx_ty, e);
        mb.finish_child(e)
    };

    // ind on y2 (innermost), inside ind on y, inside ind on x2, inside ind on x.
    let ind_at = |parent: &EnvDeclBuilder,
                  scrut: &Expr,
                  motive_body: &dyn Fn(&Expr, &EnvDeclBuilder) -> Expr,
                  minor_body: &dyn Fn(&Expr, &EnvDeclBuilder) -> Expr|
     -> Expr {
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (u_id, u) = m.fresh_local(nn.nnreal.clone());
            let body = motive_body(&u, &m);
            m.finish_child(m.mk_lam(u_id, BinderInfo::Default, nn.nnreal.clone(), body))
        };
        let minor = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = m.fresh_local(nn.causeq.clone());
            let body = minor_body(&s, &m);
            m.finish_child(m.mk_lam(s_id, BinderInfo::Default, nn.causeq.clone(), body))
        };
        Expr::apps(
            nn.quot_ind.clone(),
            [
                nn.causeq.clone(),
                nn.causeq_equiv.clone(),
                motive,
                minor,
                scrut.clone(),
            ],
        )
    };

    // x-level.
    let outer = ind_at(&b, &x, &|u, m| goal(u, &x2, &y, &y2, m), &|p, mp| {
        let mk_p = nn.quot_mk(p.clone());
        // x2-level.
        ind_at(mp, &x2, &|u, m| goal(&mk_p, u, &y, &y2, m), &|p2, mp2| {
            let mk_p2 = nn.quot_mk(p2.clone());
            // y-level.
            ind_at(mp2, &y, &|u, m| goal(&mk_p, &mk_p2, u, &y2, m), &|q, mq| {
                let mk_q = nn.quot_mk(q.clone());
                // y2-level.
                ind_at(
                    mq,
                    &y2,
                    &|u, m| goal(&mk_p, &mk_p2, &mk_q, u, m),
                    &|q2, mq2| leaf(p, p2, q, q2, mq2),
                )
            })
        })
    });

    let e = b.mk_lam(y2_id, BinderInfo::Default, nn.nnreal.clone(), outer);
    let e = b.mk_lam(y_id, BinderInfo::Default, nn.nnreal.clone(), e);
    let e = b.mk_lam(x2_id, BinderInfo::Default, nn.nnreal.clone(), e);
    let e = b.mk_lam(x_id, BinderInfo::Default, nn.nnreal.clone(), e);
    b.finish(e)
}

/// `CauSeq.LE (add p q)(add p2 q2)` from `hx : CauSeq.LE p p2`, `hy : CauSeq.LE q q2`.
#[allow(clippy::too_many_arguments)]
fn build_causeq_add_le(
    c: &AddLeConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    p2: &Expr,
    q: &Expr,
    q2: &Expr,
    hx: &Expr,
    hy: &Expr,
) -> Expr {
    let nn = c.c();
    let cl = c.cauadd(p.clone(), q.clone()); // L = add p q
    let cr = c.cauadd(p2.clone(), q2.clone()); // R = add p2 q2

    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(nn.rat.clone());
    let hpos_ty = nn.lt(nn.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());
    let half = nn.half(eps.clone());
    let heps2 = Expr::apps(nn.rat_half_pos.clone(), [eps.clone(), hpos.clone()]);

    // src_x : ∃ N, ∀ n, N≤n → (vp)<(vp2)+half  := hx half heps2.
    let src_x = Expr::apps(hx.clone(), [half.clone(), heps2.clone()]);
    // src_y : ∃ N, ∀ n, N≤n → (vq)<(vq2)+half  := hy half heps2.
    let src_y = Expr::apps(hy.clone(), [half.clone(), heps2]);

    // Goal: ∃ N, ∀ n, N≤n → (v(L n)) < (v(R n) + ε).
    let goal_exists = nn.exists_pred(&b, &cl, &cr, &eps);
    let pred_x = nn.pred_n(&b, p, p2, &half);
    let pred_y = nn.pred_n(&b, q, q2, &half);

    let elim_outer = {
        let mut bo = EnvDeclBuilder::child_of(&b);
        let (n1_id, n1) = bo.fresh_local(nn.nat.clone());
        let hn1_ty = nn.pred_n_at(&bo, p, p2, &half, &n1);
        let (hn1_id, hn1) = bo.fresh_local(hn1_ty.clone());

        let elim_inner = {
            let mut bi = EnvDeclBuilder::child_of(&bo);
            let (n2_id, n2) = bi.fresh_local(nn.nat.clone());
            let hn2_ty = nn.pred_n_at(&bi, q, q2, &half, &n2);
            let (hn2_id, hn2) = bi.fresh_local(hn2_ty.clone());

            let nmax = Expr::apps(nn.nat_max.clone(), [n1.clone(), n2.clone()]);

            let witness = {
                let mut bw = EnvDeclBuilder::child_of(&bi);
                let (m_id, m) = bw.fresh_local(nn.nat.clone());
                let hle_ty = nn.nat_le(nmax.clone(), m.clone());
                let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

                let le_max_l = Expr::apps(nn.nat_le_max_left.clone(), [n1.clone(), n2.clone()]);
                let le_max_r = Expr::apps(nn.nat_le_max_right.clone(), [n1.clone(), n2.clone()]);
                let n1_le_m =
                    nn.nat_le_trans(n1.clone(), nmax.clone(), m.clone(), le_max_l, hle.clone());
                let n2_le_m = nn.nat_le_trans(n2.clone(), nmax.clone(), m.clone(), le_max_r, hle);

                // hx_n : vp < vp2 + half ;  hy_n : vq < vq2 + half.
                let hx_n = Expr::apps(hn1.clone(), [m.clone(), n1_le_m]);
                let hy_n = Expr::apps(hn2.clone(), [m.clone(), n2_le_m]);

                let pm = c.seq_at(p, &m);
                let p2m = c.seq_at(p2, &m);
                let qm = c.seq_at(q, &m);
                let q2m = c.seq_at(q2, &m);
                let vp = c.val(pm.clone());
                let vp2 = c.val(p2m.clone());
                let vq = c.val(qm.clone());
                let vq2 = c.val(q2m.clone());

                let vp2_half = nn.add(vp2.clone(), half.clone());
                let vq2_half = nn.add(vq2.clone(), half.clone());
                // comb : (vp+vq) < ((vp2+half)+(vq2+half))  := add_lt_add.
                let comb = c.add_lt_add(
                    vp.clone(),
                    vp2_half.clone(),
                    vq.clone(),
                    vq2_half.clone(),
                    hx_n,
                    hy_n,
                );

                // regroup : ((vp2+half)+(vq2+half)) = ((vp2+vq2)+ε).
                let regroup = c.regroup4(&bw, &vp2, &vq2, &eps);
                let vp_vq = nn.add(vp.clone(), vq.clone());
                let rhs_pair = nn.add(vp2_half, vq2_half);
                let vp2_vq2 = nn.add(vp2.clone(), vq2.clone());
                let vp2vq2_eps = nn.add(vp2_vq2.clone(), eps.clone());
                // transport comb's RHS via regroup: motive t := (vp+vq) < t.
                let motive1 = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(nn.rat.clone());
                    let body = nn.lt(vp_vq.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, nn.rat.clone(), body))
                };
                let step1 = nn.subst_rat(motive1, rhs_pair, vp2vq2_eps.clone(), regroup, comb);
                // step1 : (vp+vq) < ((vp2+vq2)+ε).

                // Now rewrite endpoints to val(seq L m) / val(seq R m).
                // val(seq L m) ≡ val(NNRat.add (p m)(q m)) ; val_add : that = vp+vq.
                let add_pq = c.nnadd(pm.clone(), qm.clone());
                let add_p2q2 = c.nnadd(p2m.clone(), q2m.clone());
                let v_lhs = c.val(add_pq.clone()); // ≡ val(seq L m)
                let v_rhs = c.val(add_p2q2.clone()); // ≡ val(seq R m)
                let val_add_l = c.val_add(pm.clone(), qm.clone()); // v_lhs = vp+vq
                let val_add_r = c.val_add(p2m.clone(), q2m.clone()); // v_rhs = vp2+vq2

                // step2 : v_lhs < ((vp2+vq2)+ε) — rewrite LHS (vp+vq)→v_lhs via symm val_add_l.
                let motive2 = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(nn.rat.clone());
                    let body = nn.lt(t, vp2vq2_eps.clone());
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, nn.rat.clone(), body))
                };
                let val_add_l_sym = c.eq_symm_rat(v_lhs.clone(), vp_vq.clone(), val_add_l);
                let step2 =
                    nn.subst_rat(motive2, vp_vq.clone(), v_lhs.clone(), val_add_l_sym, step1);

                // step3 : v_lhs < (v_rhs+ε) — rewrite the RHS summand (vp2+vq2)→v_rhs
                //   via symm val_add_r.  motive t := v_lhs < (t+ε).
                let motive3 = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(nn.rat.clone());
                    let body = nn.lt(v_lhs.clone(), nn.add(t, eps.clone()));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, nn.rat.clone(), body))
                };
                let val_add_r_sym = c.eq_symm_rat(v_rhs.clone(), vp2_vq2.clone(), val_add_r);
                let proof = nn.subst_rat(
                    motive3,
                    vp2_vq2.clone(),
                    v_rhs.clone(),
                    val_add_r_sym,
                    step2,
                );

                let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
                let e = bw.mk_lam(m_id, BinderInfo::Default, nn.nat.clone(), e);
                bw.finish_child(e)
            };

            let intro = Expr::apps(
                nn.exists_intro.clone(),
                [
                    nn.nat.clone(),
                    nn.pred_n(&bi, &cl, &cr, &eps),
                    nmax,
                    witness,
                ],
            );
            let e = bi.mk_lam(hn2_id, BinderInfo::Default, hn2_ty, intro);
            let e = bi.mk_lam(n2_id, BinderInfo::Default, nn.nat.clone(), e);
            bi.finish_child(e)
        };

        let elim_y = Expr::apps(
            nn.exists_elim.clone(),
            [
                nn.nat.clone(),
                pred_y.clone(),
                goal_exists.clone(),
                src_y,
                elim_inner,
            ],
        );
        let e = bo.mk_lam(hn1_id, BinderInfo::Default, hn1_ty, elim_y);
        let e = bo.mk_lam(n1_id, BinderInfo::Default, nn.nat.clone(), e);
        bo.finish_child(e)
    };

    let elim_x = Expr::apps(
        nn.exists_elim.clone(),
        [nn.nat.clone(), pred_x, goal_exists, src_x, elim_outer],
    );
    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim_x);
    let e = b.mk_lam(eps_id, BinderInfo::Default, nn.rat.clone(), e);
    b.finish_child(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_nnreal_add_le_add_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_add_le()
            .expect("init_algebra_nnreal_add_le");
        env.init_algebra_nnreal_add_le().expect("idempotent");

        let nm = Name::from_string("NNReal.add_le_add");
        let info = env.get_const(&nm).expect("NNReal.add_le_add registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("NNReal.add_le_add must kernel-check");

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
