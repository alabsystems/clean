// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coefficient arithmetic proofs: numeral addition and single-monomial
//! coefficient folding `(c·m) + (d·m) = (c+d)·m` (signed).
//!
//! Numerals are left-nested sums of `Rat.one`: `numeral(n) = (…((1+1)+1)…+1)`.
//! `numeral(n+1)` is *syntactically* `numeral(n) + Rat.one`, which makes the
//! recursive proofs below close on `Eq.refl`.

use super::{Monomial, RatPolyProver};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;

impl RatPolyProver {
    /// `numeral(a) + numeral(b) = numeral(a+b)` for `a, b ≥ 1`.
    pub(super) fn numeral_add(&self, parent: &EnvDeclBuilder, a: u32, b: u32) -> Expr {
        debug_assert!(a >= 1 && b >= 1);
        let na = self.numeral(a);
        if b == 1 {
            // numeral(a) + 1  ==  numeral(a+1)  (syntactically identical)
            let lhs = self.add(na.clone(), self.one());
            return self.refl(lhs);
        }
        // numeral(b) is `numeral(b-1) + 1`. lhs = numeral(a) + (numeral(b-1) + 1).
        let nb1 = self.numeral(b - 1);
        let lhs = self.add(na.clone(), self.add(nb1.clone(), self.one()));
        // symm add_assoc na nb1 1 : na + (nb1 + 1) = (na + nb1) + 1
        let assoc = self.aassoc_pub(na.clone(), nb1.clone(), self.one());
        let assoc_lhs = self.add(self.add(na.clone(), nb1.clone()), self.one());
        let h1 = self.symm(assoc_lhs.clone(), lhs.clone(), assoc);
        // recurse: na + nb1 = numeral(a+b-1); lift under (· + 1)
        let h_rec = self.numeral_add(parent, a, b - 1);
        let na_nb1 = self.add(na.clone(), nb1.clone());
        let num_abm1 = self.numeral(a + b - 1);
        let add_c = self.add_const();
        let cong = self.cong_left(
            parent,
            &add_c,
            na_nb1.clone(),
            num_abm1.clone(),
            self.one(),
            h_rec,
        );
        let folded = self.add(num_abm1, self.one()); // == numeral(a+b)
        self.trans(lhs, assoc_lhs, folded, h1, cong)
    }

    /// `aassoc` re-exported for the coeff module.
    fn aassoc_pub(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        self.c.aassoc(a, b, cc)
    }

    /// Fold two same-sign terms with the SAME monomial:
    /// `reify_term(s·a, m) + reify_term(s·b, m) = reify_term(s·(a+b), m)`,
    /// where `s ∈ {+1, −1}`, `a, b ≥ 1`. Returns the proof.
    pub(super) fn fold_same_sign(
        &self,
        parent: &EnvDeclBuilder,
        positive: bool,
        a: u32,
        b: u32,
        m: &Monomial,
    ) -> Expr {
        // First the positive-coefficient core: (na·m) + (nb·m) = (n(a+b)·m).
        let core = self.fold_pos(parent, a, b, m);
        if positive {
            return core;
        }
        // Negative: neg(P_a) + neg(P_b) = neg(P_a + P_b)  [neg_add_distrib],
        // then congr neg of core : neg(P_a + P_b) = neg(P_{a+b}).
        // We instead prove neg X + neg Y = neg (X + Y) via the add/neg algebra.
        let pa = self.reify_pos_term(a, m);
        let pb = self.reify_pos_term(b, m);
        let pab = self.reify_pos_term(a + b, m);
        // h_dist : neg pa + neg pb = neg (pa + pb)
        let h_dist = self.neg_add_distrib(parent, &pa, &pb);
        let neg_sum = self.neg(self.add(pa.clone(), pb.clone()));
        // congr neg core : neg (pa + pb) = neg pab
        let cong = self.cong_neg(parent, self.add(pa.clone(), pb.clone()), pab.clone(), core);
        let neg_pab = self.neg(pab.clone());
        let lhs = self.add(self.neg(pa), self.neg(pb));
        self.trans(lhs, neg_sum, neg_pab, h_dist, cong)
    }

    /// Positive coefficient fold `(na·m) + (nb·m) = (n(a+b)·m)`, `a,b ≥ 1`.
    ///
    /// Handles the `coeff == 1 ⇒ m` reification asymmetry: `reify_pos_term(1,m)`
    /// is `m` (no `1·m`), so we route through an explicit `one_mul` when needed.
    fn fold_pos(&self, parent: &EnvDeclBuilder, a: u32, b: u32, m: &Monomial) -> Expr {
        let mono = self.reify_monomial(m);
        // Bring both sides to the `numeral·mono` shape (uniform), then distribute.
        // ta = reify_pos_term(a,m), tb = reify_pos_term(b,m); lhs = ta + tb.
        let ta = self.reify_pos_term(a, m);
        let tb = self.reify_pos_term(b, m);
        let lhs = self.add(ta.clone(), tb.clone());

        // u_ta : ta = numeral(a)·mono   (refl if a≥2, else symm one_mul)
        let na_mono = if m.is_one() {
            self.numeral(a)
        } else {
            self.mul(self.numeral(a), mono.clone())
        };
        let nb_mono = if m.is_one() {
            self.numeral(b)
        } else {
            self.mul(self.numeral(b), mono.clone())
        };
        let u_ta = self.lift_to_numeral_mul(a, m);
        let u_tb = self.lift_to_numeral_mul(b, m);
        // lhs = (numeral(a)·mono) + (numeral(b)·mono)
        let add_c = self.add_const();
        let c1 = self.cong_left(
            parent,
            &add_c,
            ta.clone(),
            na_mono.clone(),
            tb.clone(),
            u_ta,
        );
        let step1_mid = self.add(na_mono.clone(), tb.clone());
        let c2 = self.cong_right(
            parent,
            &add_c,
            tb.clone(),
            nb_mono.clone(),
            na_mono.clone(),
            u_tb,
        );
        let uniform = self.add(na_mono.clone(), nb_mono.clone());
        let h_uniform = self.trans(lhs.clone(), step1_mid, uniform.clone(), c1, c2);

        // (numeral(a)·mono) + (numeral(b)·mono) = (numeral(a)+numeral(b))·mono
        //   [symm right_distrib numeral(a) numeral(b) mono]
        let sum_num = self.add(self.numeral(a), self.numeral(b));
        let dist_rhs = if m.is_one() {
            // when mono == 1, the `·mono` is `·1`; but our reify never writes
            // `numeral·1`. We special-case below.
            self.mul(sum_num.clone(), mono.clone())
        } else {
            self.mul(sum_num.clone(), mono.clone())
        };
        let rdist = self.rdist_pub(self.numeral(a), self.numeral(b), mono.clone());
        // rdist : (na+nb)·mono = na·mono + nb·mono ; we want the symm direction
        let h_undist = self.symm(dist_rhs.clone(), uniform.clone(), rdist);

        // (numeral(a)+numeral(b)) = numeral(a+b)  → lift under (·mono)
        let h_num = self.numeral_add(parent, a, b);
        let num_ab = self.numeral(a + b);
        let mul_c = self.mul_const();
        let c_num = self.cong_left(
            parent,
            &mul_c,
            sum_num.clone(),
            num_ab.clone(),
            mono.clone(),
            h_num,
        );
        let folded_mul = self.mul(num_ab.clone(), mono.clone());

        // folded_mul = reify_pos_term(a+b, m)  (refl if mono≠1; if mono==1, drop)
        let target = self.reify_pos_term(a + b, m);
        let h_final = self.collapse_numeral_mul(a + b, m);
        // h_final : numeral(a+b)·mono = target

        // chain: lhs = uniform = dist_rhs = folded_mul = target
        let s = self.trans(lhs.clone(), uniform, dist_rhs.clone(), h_uniform, h_undist);
        let s = self.trans(lhs.clone(), dist_rhs, folded_mul.clone(), s, c_num);
        self.trans(lhs, folded_mul, target, s, h_final)
    }

    /// `ta = numeral(a)·mono` (proof). For `a≥2` reify already IS that, so refl;
    /// for `a==1`, `reify_pos_term` gives bare `mono`, so `symm (one_mul mono)`.
    /// When `mono == 1`, both sides are `numeral(a)` (a≥1) → refl, or for a==1
    /// `reify` gives `Rat.one` and `numeral(1)` is also `Rat.one` → refl.
    fn lift_to_numeral_mul(&self, a: u32, m: &Monomial) -> Expr {
        let mono = self.reify_monomial(m);
        if m.is_one() {
            // reify_pos_term(a, 1) == numeral(a); target na_mono == numeral(a).
            let na = self.numeral(a);
            return self.refl(na);
        }
        if a == 1 {
            // reify_pos_term(1,m) == mono ; target == 1·mono. Want `mono = 1·mono`.
            let one_mono = self.mul(self.one(), mono.clone());
            let h = self.c.one_mul(mono.clone()); // 1·mono = mono  (nm = reify)
            return self.symm(one_mono, mono, h);
        }
        // a≥2: reify_pos_term(a,m) == numeral(a)·mono == target
        let na_mono = self.mul(self.numeral(a), mono);
        self.refl(na_mono)
    }

    /// `numeral(n)·mono = reify_pos_term(n, m)` (the inverse of `lift_to_numeral_mul`).
    fn collapse_numeral_mul(&self, n: u32, m: &Monomial) -> Expr {
        let mono = self.reify_monomial(m);
        if m.is_one() {
            let nn = self.numeral(n);
            return self.refl(nn);
        }
        if n == 1 {
            // numeral(1) == Rat.one ; 1·mono = mono  [one_mul]
            return self.c.one_mul(mono);
        }
        let nn_mono = self.mul(self.numeral(n), mono);
        self.refl(nn_mono)
    }

    /// `rdist a b c : (a+b)·c = a·c + b·c`.
    fn rdist_pub(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        self.c.rdist(a, b, cc)
    }

    /// `neg x + neg y = neg (x + y)`  (the additive `−` distributes over `+`).
    ///
    /// Built from the additive-group surface (`add_left_neg`, `add_neg_self`,
    /// `add_assoc`, `add_comm`, `add_zero`, `zero_add`, `add_right_cancel`):
    /// both `(−x)+(−y)` and `−(x+y)`, when summed with `(x+y)` on the right,
    /// reduce to `0`; `add_right_cancel` then yields their equality.
    pub(super) fn neg_add_distrib(&self, parent: &EnvDeclBuilder, x: &Expr, y: &Expr) -> Expr {
        let nx = self.neg(x.clone());
        let ny = self.neg(y.clone());
        let xy = self.add(x.clone(), y.clone());
        let nxny = self.add(nx.clone(), ny.clone()); // (−x)+(−y)
        let neg_xy = self.neg(xy.clone()); // −(x+y)

        // h1 : ((−x)+(−y)) + (x+y) = 0
        let h1 = self.inv_sum_to_zero(parent, x, y);
        // h2 : (−(x+y)) + (x+y) = 0    [add_left_neg (x+y)]
        let h2 = Expr::app(
            Expr::const_(crate::name::Name::from_string("Rat.add_left_neg"), vec![]),
            xy.clone(),
        );
        // h_comb : ((−x)+(−y)) + (x+y) = (−(x+y)) + (x+y)
        let lhs_sum = self.add(nxny.clone(), xy.clone());
        let rhs_sum = self.add(neg_xy.clone(), xy.clone());
        let h2_sym = self.symm(rhs_sum.clone(), self.zero(), h2);
        let h_comb = self.trans(lhs_sum, self.zero(), rhs_sum, h1, h2_sym);
        // `Rat.add_right_cancel a c b (h : a + c = b + c) : a = b` — the MIDDLE
        // argument is the cancelled term `c`, the THIRD is the result RHS `b`.
        // Here a = (−x)+(−y), c = (x+y), b = −(x+y), h_comb : a+c = b+c.
        let arc = Expr::const_(
            crate::name::Name::from_string("Rat.add_right_cancel"),
            vec![],
        );
        Expr::apps(arc, [nxny, xy, neg_xy, h_comb])
    }

    /// `((−x)+(−y)) + (x+y) = 0`, via the explicit reassociation chain.
    fn inv_sum_to_zero(&self, parent: &EnvDeclBuilder, x: &Expr, y: &Expr) -> Expr {
        let add_c = self.add_const();
        let nx = self.neg(x.clone());
        let ny = self.neg(y.clone());
        let xy = self.add(x.clone(), y.clone());
        let z = self.zero();

        // e0 = ((−x)+(−y)) + (x+y)
        let e0 = self.add(self.add(nx.clone(), ny.clone()), xy.clone());
        // s1 : e0 = (−x) + ((−y) + (x+y))     [add_assoc (−x) (−y) (x+y)]
        let s1 = self.aassoc_pub(nx.clone(), ny.clone(), xy.clone());
        let e1 = self.add(nx.clone(), self.add(ny.clone(), xy.clone()));
        // inside: (−y) + (x+y) = ((−y)+x)+y    [symm add_assoc (−y) x y]
        let ny_x = self.add(ny.clone(), x.clone());
        let ny_x_y = self.add(ny_x.clone(), y.clone());
        let h_in1 = self.symm(
            ny_x_y.clone(),
            self.add(ny.clone(), xy.clone()),
            self.aassoc_pub(ny.clone(), x.clone(), y.clone()),
        );
        // lift under (−x)+·  : e1 = (−x) + (((−y)+x)+y)
        let e2 = self.add(nx.clone(), ny_x_y.clone());
        let c_in1 = self.cong_right(
            parent,
            &add_c,
            self.add(ny.clone(), xy.clone()),
            ny_x_y.clone(),
            nx.clone(),
            h_in1,
        );
        // ((−y)+x) = (x+(−y))   [add_comm (−y) x] ; lift under (·+y) then under (−x)+·
        let x_ny = self.add(x.clone(), ny.clone());
        let h_comm = self.acomm(ny.clone(), x.clone());
        let c_comm_inner = self.cong_left(
            parent,
            &add_c,
            ny_x.clone(),
            x_ny.clone(),
            y.clone(),
            h_comm,
        );
        let x_ny_y = self.add(x_ny.clone(), y.clone());
        let c_comm = self.cong_right(
            parent,
            &add_c,
            ny_x_y.clone(),
            x_ny_y.clone(),
            nx.clone(),
            c_comm_inner,
        );
        let e3 = self.add(nx.clone(), x_ny_y.clone());
        // (x+(−y))+y = x + ((−y)+y)   [add_assoc x (−y) y]
        let ny_y = self.add(ny.clone(), y.clone());
        let x_plus_nyy = self.add(x.clone(), ny_y.clone());
        let h_assoc2 = self.aassoc_pub(x.clone(), ny.clone(), y.clone());
        let c_assoc2 = self.cong_right(
            parent,
            &add_c,
            x_ny_y.clone(),
            x_plus_nyy.clone(),
            nx.clone(),
            h_assoc2,
        );
        let e4 = self.add(nx.clone(), x_plus_nyy.clone());
        // (−y)+y = 0   [add_left_neg y] ; lift under (x + ·) then under (−x)+·
        let h_lny = Expr::app(
            Expr::const_(crate::name::Name::from_string("Rat.add_left_neg"), vec![]),
            y.clone(),
        );
        let x_plus_zero = self.add(x.clone(), z.clone());
        let c_lny_inner =
            self.cong_right(parent, &add_c, ny_y.clone(), z.clone(), x.clone(), h_lny);
        let c_lny = self.cong_right(
            parent,
            &add_c,
            x_plus_nyy.clone(),
            x_plus_zero.clone(),
            nx.clone(),
            c_lny_inner,
        );
        let e5 = self.add(nx.clone(), x_plus_zero.clone());
        // x+0 = x   [add_zero x] ; lift under (−x)+·
        let h_xz = Expr::app(self.add_zero.clone(), x.clone());
        let c_xz = self.cong_right(
            parent,
            &add_c,
            x_plus_zero.clone(),
            x.clone(),
            nx.clone(),
            h_xz,
        );
        let e6 = self.add(nx.clone(), x.clone());
        // (−x)+x = 0   [add_left_neg x]
        let h_lnx = Expr::app(
            Expr::const_(crate::name::Name::from_string("Rat.add_left_neg"), vec![]),
            x.clone(),
        );

        // chain e0 → e1 → e2 → e3 → e4 → e5 → e6 → 0
        let s = self.trans(e0.clone(), e1.clone(), e2.clone(), s1, c_in1);
        let s = self.trans(e0.clone(), e2, e3.clone(), s, c_comm);
        let s = self.trans(e0.clone(), e3, e4.clone(), s, c_assoc2);
        let s = self.trans(e0.clone(), e4, e5.clone(), s, c_lny);
        let s = self.trans(e0.clone(), e5, e6.clone(), s, c_xz);
        self.trans(e0, e6, z, s, h_lnx)
    }

    /// `Rat.neg Rat.zero = Rat.zero` (`−0 + 0 = 0 = 0 + 0`, cancel `0`).
    pub(super) fn neg_zero_eq(&self) -> Expr {
        let z = self.zero();
        let neg_z = self.neg(z.clone());
        let add_left_neg = Expr::const_(crate::name::Name::from_string("Rat.add_left_neg"), vec![]);
        let h_l = Expr::app(add_left_neg, z.clone()); // −0 + 0 = 0
        let h_r = Expr::apps(self.zero_add.clone(), [z.clone()]); // 0 + 0 = 0
        let zpz = self.add(z.clone(), z.clone());
        let h_r_sym = self.symm(zpz.clone(), z.clone(), h_r);
        let nz_pz = self.add(neg_z.clone(), z.clone());
        let h_comb = self.trans(nz_pz, z.clone(), zpz, h_l, h_r_sym);
        let arc = Expr::const_(
            crate::name::Name::from_string("Rat.add_right_cancel"),
            vec![],
        );
        Expr::apps(arc, [neg_z, z.clone(), z, h_comb])
    }

    /// Opposite-sign coefficient fold (nonzero sum): given `c1`, `c2` with
    /// opposite signs and `c1 + c2 ≠ 0`, prove
    /// `reify_term(c1,m) + reify_term(c2,m) = reify_term(c1+c2, m)`,
    /// returning `(proof, result_term)`.
    pub(super) fn fold_opposite(
        &self,
        parent: &EnvDeclBuilder,
        c1: i128,
        c2: i128,
        m: &Monomial,
    ) -> (Expr, super::combine::TermPub) {
        let sum = c1 + c2;
        let (pmag, nmag, pos_first) = if c1 > 0 {
            (c1 as u32, (-c2) as u32, true)
        } else {
            (c2 as u32, (-c1) as u32, false)
        };
        let p_e = self.reify_pos_term(pmag, m); // p·m
        let n_e = self.reify_pos_term(nmag, m); // n·m (magnitude)
        let neg_n = self.neg(n_e.clone());
        let h_core = self.fold_pos_minus(parent, pmag, nmag, m); // (p·m)+neg(n·m)=result
        let target = self.reify_term(sum, m);

        if pos_first {
            (
                h_core,
                super::combine::TermPub {
                    coeff: sum,
                    mono: m.clone(),
                },
            )
        } else {
            let actual = self.add(neg_n.clone(), p_e.clone());
            let oriented = self.add(p_e.clone(), neg_n.clone());
            let h_comm = self.acomm_pub(neg_n.clone(), p_e.clone());
            let proof = self.trans(actual, oriented, target, h_comm, h_core);
            (
                proof,
                super::combine::TermPub {
                    coeff: sum,
                    mono: m.clone(),
                },
            )
        }
    }

    fn acomm_pub(&self, a: Expr, b: Expr) -> Expr {
        self.c.acomm(a, b)
    }

    /// `(p·m) + neg(n·m) = reify_term(p−n, m)` for `p, n ≥ 1`, `p ≠ n`.
    fn fold_pos_minus(&self, parent: &EnvDeclBuilder, p: u32, n: u32, m: &Monomial) -> Expr {
        debug_assert!(p != n);
        let p_e = self.reify_pos_term(p, m);
        let n_e = self.reify_pos_term(n, m);
        let neg_n = self.neg(n_e.clone());
        let lhs = self.add(p_e.clone(), neg_n.clone());
        let add_c = self.add_const();

        if p > n {
            let d = p - n; // ≥ 1
            let dm = self.reify_pos_term(d, m);
            let nm = n_e.clone();
            let split_rhs = self.add(dm.clone(), nm.clone());
            let h_fold = self.fold_pos(parent, d, n, m); // (d·m)+(n·m)=(p·m)
            let h_split = self.symm(split_rhs.clone(), p_e.clone(), h_fold); // p·m = (d·m)+(n·m)
            let c1 = self.cong_left(
                parent,
                &add_c,
                p_e.clone(),
                split_rhs.clone(),
                neg_n.clone(),
                h_split,
            );
            let e1 = self.add(split_rhs.clone(), neg_n.clone());
            let h_assoc = self.c.aassoc(dm.clone(), nm.clone(), neg_n.clone());
            let nm_plus_negnm = self.add(nm.clone(), neg_n.clone());
            let e2 = self.add(dm.clone(), nm_plus_negnm.clone());
            let h_cancel = Expr::app(self.add_neg_self.clone(), nm.clone());
            let c_cancel = self.cong_right(
                parent,
                &add_c,
                nm_plus_negnm.clone(),
                self.zero(),
                dm.clone(),
                h_cancel,
            );
            let dm_plus_zero = self.add(dm.clone(), self.zero());
            let h_az = Expr::app(self.add_zero.clone(), dm.clone());
            let s = self.trans(lhs.clone(), e1.clone(), e2.clone(), c1, h_assoc);
            let s = self.trans(lhs.clone(), e2, dm_plus_zero.clone(), s, c_cancel);
            self.trans(lhs, dm_plus_zero, dm, s, h_az)
        } else {
            let e = n - p; // ≥ 1
            let em = self.reify_pos_term(e, m);
            let pm = p_e.clone();
            let n_split = self.add(pm.clone(), em.clone());
            let h_fold = self.fold_pos(parent, p, e, m); // (p·m)+(e·m)=(n·m)
            let h_nsplit = self.symm(n_split.clone(), n_e.clone(), h_fold); // n·m = (p·m)+(e·m)
            let neg_split = self.neg(n_split.clone());
            let c_neg = self.cong_neg(parent, n_e.clone(), n_split.clone(), h_nsplit);
            let lhs2 = self.add(pm.clone(), neg_split.clone());
            let c_lift = self.cong_right(
                parent,
                &add_c,
                neg_n.clone(),
                neg_split.clone(),
                pm.clone(),
                c_neg,
            );
            let neg_pm = self.neg(pm.clone());
            let neg_em = self.neg(em.clone());
            let neg_pm_em = self.add(neg_pm.clone(), neg_em.clone());
            // neg_split = −(pm+em) ; want `−(pm+em) = (−pm)+(−em)` = symm(neg_add_distrib).
            let h_dist0 = self.neg_add_distrib(parent, &pm, &em); // (−pm)+(−em) = −(pm+em)
            let h_dist = self.symm(neg_pm_em.clone(), neg_split.clone(), h_dist0); // neg_split = neg_pm_em
            let c_dist = self.cong_right(
                parent,
                &add_c,
                neg_split.clone(),
                neg_pm_em.clone(),
                pm.clone(),
                h_dist,
            );
            let e_after_dist = self.add(pm.clone(), neg_pm_em.clone());
            let pm_negpm = self.add(pm.clone(), neg_pm.clone());
            let assoc = self.c.aassoc(pm.clone(), neg_pm.clone(), neg_em.clone());
            let assoc_lhs = self.add(pm_negpm.clone(), neg_em.clone());
            let h_assoc = self.symm(assoc_lhs.clone(), e_after_dist.clone(), assoc);
            let h_cancel = Expr::app(self.add_neg_self.clone(), pm.clone());
            let c_cancel = self.cong_left(
                parent,
                &add_c,
                pm_negpm.clone(),
                self.zero(),
                neg_em.clone(),
                h_cancel,
            );
            let zero_plus = self.add(self.zero(), neg_em.clone());
            let h_zadd = Expr::apps(self.zero_add.clone(), [neg_em.clone()]);
            let s = self.trans(
                lhs.clone(),
                lhs2.clone(),
                e_after_dist.clone(),
                c_lift,
                c_dist,
            );
            let s = self.trans(lhs.clone(), e_after_dist, assoc_lhs.clone(), s, h_assoc);
            let s = self.trans(lhs.clone(), assoc_lhs, zero_plus.clone(), s, c_cancel);
            self.trans(lhs, zero_plus, neg_em, s, h_zadd)
        }
    }
}
