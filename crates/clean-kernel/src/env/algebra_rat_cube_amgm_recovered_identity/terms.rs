// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Term-level equality helpers for the polynomial normalizer: numeral
//! arithmetic on additive `Rat.one` literals, single coefficient·monomial
//! `term_expr` rewrites, and the per-monomial coefficient-merge lemma. All
//! produced terms are pure `Rat` ring rewrites (`right_distrib`, `mul_assoc`,
//! `add_assoc`, `add_neg_self`, `add_zero`, `one_mul`, `mul_neg`, `neg_neg`),
//! so the closure stays foundational.

use super::super::CubeAmGmConstsRecovered;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;
use crate::name::Name;

impl CubeAmGmConstsRecovered {
    // ── extra leaf bricks (avoid `Rat.neg_mul` — not registered) ──

    /// `Rat.add_neg_self a : a + (-a) = 0`.
    fn add_neg_self(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]),
            a.clone(),
        )
    }
    /// `Rat.add_left_neg a : (-a) + a = 0`.
    fn add_left_neg(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.add_left_neg"), vec![]),
            a.clone(),
        )
    }
    /// `Rat.zero_add a : 0 + a = a`.
    fn zero_add(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.zero_add"), vec![]),
            a.clone(),
        )
    }

    /// Derived `-(x+y) = (-x)+(-y)` (no `Rat.neg_add` brick exists). Group-law
    /// derivation from `add_assoc`/`add_comm`/`add_neg_self`/`add_left_neg`/
    /// `zero_add`/`add_zero`.
    pub(super) fn neg_add(&self, parent: &EnvDeclBuilder, x: &Expr, y: &Expr) -> Expr {
        let xy = self.add(x.clone(), y.clone());
        let neg_xy = self.neg(xy.clone());
        let nx = self.neg(x.clone());
        let ny = self.neg(y.clone());
        let z = self.add(ny.clone(), nx.clone()); // Z := (-y)+(-x)
        let add_c = self.add_op();

        // h1 : (x+y) + Z = 0.
        // (x+y)+Z = x + (y + Z)              [add_assoc x y Z]
        let s_a1 = self.aassoc(x.clone(), y.clone(), z.clone());
        let x_yz = self.add(x.clone(), self.add(y.clone(), z.clone()));
        // y + Z = y + ((-y)+(-x)) = (y + (-y)) + (-x)   [symm add_assoc y (-y) (-x)]
        let yz = self.add(y.clone(), z.clone());
        let assoc_y = self.aassoc(y.clone(), ny.clone(), nx.clone()); // (y+(-y))+(-x) = y+((-y)+(-x))
        let y_ny_nx = self.add(self.add(y.clone(), ny.clone()), nx.clone());
        let s_assoc_y = self.symm(y_ny_nx.clone(), yz.clone(), assoc_y); // y+Z = (y+(-y))+(-x)
                                                                         // (y+(-y)) → 0  [add_neg_self y], lift cong_l over (·+(-x))
        let yny = self.add(y.clone(), ny.clone());
        let ans_y = self.add_neg_self(y); // y+(-y) = 0
        let c_y = self.cong_l(parent, &add_c, yny.clone(), self.zero(), nx.clone(), ans_y);
        let zero_nx = self.add(self.zero(), nx.clone());
        // 0 + (-x) → (-x)  [zero_add]
        let za = self.zero_add(&nx);
        // y+Z = (0)+(-x) = (-x)
        let yz_to_znx = self.trans(yz.clone(), y_ny_nx.clone(), zero_nx.clone(), s_assoc_y, c_y);
        let yz_eq_nx = self.trans(yz.clone(), zero_nx.clone(), nx.clone(), yz_to_znx, za);
        // x + (y+Z) → x + (-x)  [cong_r yz_eq_nx]
        let c_xyz = self.cong_r(parent, &add_c, yz.clone(), nx.clone(), x.clone(), yz_eq_nx);
        let x_nx = self.add(x.clone(), nx.clone());
        // x + (-x) = 0  [add_neg_self x]
        let ans_x = self.add_neg_self(x);
        // chain h1: (x+y)+Z = x+(y+Z) = x+(-x) = 0
        let h1a = self.trans(
            self.add(xy.clone(), z.clone()),
            x_yz.clone(),
            x_nx.clone(),
            s_a1,
            c_xyz,
        );
        let h1 = self.trans(
            self.add(xy.clone(), z.clone()),
            x_nx.clone(),
            self.zero(),
            h1a,
            ans_x,
        );

        // h2 : Z = -(x+y).
        //   Z = 0 + Z                          [symm zero_add Z]
        //     = (-(x+y) + (x+y)) + Z           [cong_l (symm add_left_neg (x+y))]
        //     = -(x+y) + ((x+y) + Z)           [add_assoc]
        //     = -(x+y) + 0                     [cong_r h1]
        //     = -(x+y)                         [add_zero]
        let s_za_z = self.symm(
            self.add(self.zero(), z.clone()),
            z.clone(),
            self.zero_add(&z),
        ); // Z = 0+Z
        let zero_z = self.add(self.zero(), z.clone());
        let aln = self.add_left_neg(&xy); // (-(x+y))+(x+y) = 0
        let s_aln = self.symm(self.add(neg_xy.clone(), xy.clone()), self.zero(), aln); // 0 = (-(x+y))+(x+y)
        let c_zln = self.cong_l(
            parent,
            &add_c,
            self.zero(),
            self.add(neg_xy.clone(), xy.clone()),
            z.clone(),
            s_aln,
        );
        let lhs2 = self.add(self.add(neg_xy.clone(), xy.clone()), z.clone()); // ((-(x+y))+(x+y))+Z
                                                                              // add_assoc (-(x+y)) (x+y) Z : (((-(x+y))+(x+y))+Z) = (-(x+y))+((x+y)+Z)
        let assoc2 = self.aassoc(neg_xy.clone(), xy.clone(), z.clone());
        let negxy_xyz = self.add(neg_xy.clone(), self.add(xy.clone(), z.clone()));
        // cong_r h1 : (-(x+y))+((x+y)+Z) = (-(x+y))+0
        let c_h1 = self.cong_r(
            parent,
            &add_c,
            self.add(xy.clone(), z.clone()),
            self.zero(),
            neg_xy.clone(),
            h1,
        );
        let negxy_zero = self.add(neg_xy.clone(), self.zero());
        let az2 = self.add_zero(&neg_xy);
        // chain h2: Z = zero_z = lhs2 = negxy_xyz = negxy_zero = neg_xy
        let p1 = self.trans(z.clone(), zero_z.clone(), lhs2.clone(), s_za_z, c_zln);
        let p2 = self.trans(z.clone(), lhs2.clone(), negxy_xyz.clone(), p1, assoc2);
        let p3 = self.trans(z.clone(), negxy_xyz.clone(), negxy_zero.clone(), p2, c_h1);
        let h2 = self.trans(z.clone(), negxy_zero.clone(), neg_xy.clone(), p3, az2);
        // h2 : Z = -(x+y), i.e. (-y)+(-x) = -(x+y).

        // Final: -(x+y) = (-x)+(-y).
        //   (-x)+(-y) = (-y)+(-x)   [add_comm]
        //             = -(x+y)      [h2]
        //   symm ⇒ -(x+y) = (-x)+(-y).
        let nx_ny = self.add(nx.clone(), ny.clone());
        let comm = self.acomm(nx.clone(), ny.clone()); // (-x)+(-y) = (-y)+(-x)
        let nxny_eq_negxy = self.trans(nx_ny.clone(), z.clone(), neg_xy.clone(), comm, h2);
        // nxny_eq_negxy : nx_ny = neg_xy ; symm → neg_xy = nx_ny.
        self.symm(nx_ny, neg_xy, nxny_eq_negxy)
    }
    /// `Rat.neg_neg a : -(-a) = a`.
    pub(super) fn neg_neg(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.neg_neg"), vec![]),
            a.clone(),
        )
    }
    /// `Rat.add_zero a : a + 0 = a`.
    fn add_zero(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            a.clone(),
        )
    }
    /// `neg` congruence: `-x = -y` from `h : x = y`.
    pub(super) fn cong_neg_pub(
        &self,
        parent: &EnvDeclBuilder,
        x: &Expr,
        y: &Expr,
        h: &Expr,
    ) -> Expr {
        super::cong_neg(self, parent, x, y, h)
    }

    /// Proof `nat_lit(i) + nat_lit(j) = nat_lit(i+j)` for `i,j ≥ 1`.
    /// Left-nested additive numerals; recurse on `j`.
    pub(super) fn numeral_add(&self, parent: &EnvDeclBuilder, i: usize, j: usize) -> Expr {
        debug_assert!(i >= 1 && j >= 1);
        let li = self.nat_lit(i);
        if j == 1 {
            // nat_lit(i) + nat_lit(1) == nat_lit(i)+1 == nat_lit(i+1) syntactically.
            return self.refl(self.add(li.clone(), self.one()));
        }
        // nat_lit(j) == nat_lit(j-1) + 1  (syntactic).
        // nat_lit(i) + nat_lit(j) = nat_lit(i) + (nat_lit(j-1)+1)
        //   = (nat_lit(i) + nat_lit(j-1)) + 1     [symm add_assoc]
        //   = nat_lit(i+j-1) + 1                   [cong_left numeral_add(i,j-1)]
        //   = nat_lit(i+j)                         [syntactic]
        let lj = self.nat_lit(j);
        let ljm1 = self.nat_lit(j - 1);
        let one = self.one();
        let lhs = self.add(li.clone(), lj.clone()); // nat_lit(i) + nat_lit(j)
                                                    // step assoc: nat_lit(i) + (nat_lit(j-1)+1) = (nat_lit(i)+nat_lit(j-1)) + 1
        let assoc = self.aassoc(li.clone(), ljm1.clone(), one.clone()); // (a+b)+c = a+(b+c)
                                                                        // assoc : (li + ljm1) + 1 = li + (ljm1 + 1); we want the symm direction.
        let lhs_assoc_l = self.add(self.add(li.clone(), ljm1.clone()), one.clone());
        let lhs_assoc_r = self.add(li.clone(), self.add(ljm1.clone(), one.clone()));
        // lhs == lhs_assoc_r syntactically (since lj == ljm1+1)
        let s_assoc = self.symm(lhs_assoc_l.clone(), lhs_assoc_r.clone(), assoc); // li+(ljm1+1) = (li+ljm1)+1
                                                                                  // recurse: li + ljm1 = nat_lit(i+j-1)
        let inner = self.numeral_add(parent, i, j - 1);
        let target_inner = self.nat_lit(i + j - 1);
        let add_c = self.add_op();
        // cong_left: (li+ljm1)+1 = nat_lit(i+j-1)+1
        let cong = self.cong_l(
            parent,
            &add_c,
            self.add(li.clone(), ljm1.clone()),
            target_inner.clone(),
            one.clone(),
            inner,
        );
        let mid = self.add(target_inner, one); // nat_lit(i+j-1)+1 == nat_lit(i+j) syntactic
                                               // chain: lhs = lhs_assoc_l (s_assoc) = mid (cong)
        self.trans(lhs.clone(), lhs_assoc_l, mid, s_assoc, cong)
    }

    /// Proof `nat_lit(i) · nat_lit(j) = nat_lit(i*j)` for `i,j ≥ 1`.
    /// Recurse on `i`: `nat_lit(i) = nat_lit(i-1) + 1`.
    pub(super) fn numeral_mul(&self, parent: &EnvDeclBuilder, i: usize, j: usize) -> Expr {
        debug_assert!(i >= 1 && j >= 1);
        let lj = self.nat_lit(j);
        if i == 1 {
            // nat_lit(1)·nat_lit(j) = 1·nat_lit(j) = nat_lit(j) = nat_lit(1*j)
            return self.one_mul(lj);
        }
        // nat_lit(i)·lj = (nat_lit(i-1)+1)·lj
        //   = nat_lit(i-1)·lj + 1·lj        [right_distrib]
        //   = nat_lit((i-1)*j) + 1·lj       [cong_left numeral_mul(i-1,j)]
        //   = nat_lit((i-1)*j) + lj         [cong_right one_mul]
        //   = nat_lit((i-1)*j) + nat_lit(j) = nat_lit(i*j)  [numeral_add]
        let li = self.nat_lit(i); // == nat_lit(i-1) + 1 syntactically
        let lim1 = self.nat_lit(i - 1);
        let one = self.one();
        let lhs = self.mul(li.clone(), lj.clone());
        // right_distrib (nat_lit(i-1)) 1 lj : (nat_lit(i-1)+1)·lj = nat_lit(i-1)·lj + 1·lj
        let rdist = self.rdist(lim1.clone(), one.clone(), lj.clone());
        let lim1_lj = self.mul(lim1.clone(), lj.clone());
        let one_lj = self.mul(one.clone(), lj.clone());
        let sum0 = self.add(lim1_lj.clone(), one_lj.clone());
        let add_c = self.add_op();
        // cong_left numeral_mul(i-1,j): nat_lit(i-1)·lj = nat_lit((i-1)*j)
        let inner = self.numeral_mul(parent, i - 1, j);
        let target_inner = self.nat_lit((i - 1) * j);
        let c1 = self.cong_l(
            parent,
            &add_c,
            lim1_lj.clone(),
            target_inner.clone(),
            one_lj.clone(),
            inner,
        );
        let sum1 = self.add(target_inner.clone(), one_lj.clone());
        // cong_right one_mul: 1·lj = lj
        let om = self.one_mul(lj.clone());
        let c2 = self.cong_r(
            parent,
            &add_c,
            one_lj.clone(),
            lj.clone(),
            target_inner.clone(),
            om,
        );
        let sum2 = self.add(target_inner.clone(), lj.clone());
        // numeral_add((i-1)*j, j) : nat_lit((i-1)*j) + nat_lit(j) = nat_lit(i*j)
        let na = self.numeral_add(parent, (i - 1) * j, j);
        let target = self.nat_lit(i * j);
        // chain: lhs = sum0 (rdist) = sum1 (c1) = sum2 (c2) = target (na)
        let s1 = self.trans(lhs.clone(), sum0.clone(), sum1.clone(), rdist, c1);
        let s2 = self.trans(lhs.clone(), sum1, sum2.clone(), s1, c2);
        self.trans(lhs, sum2, target, s2, na)
    }

    /// `pub(super)` re-export for distrib helpers.
    pub(super) fn nmul_to_term_pub(&self, m: &Expr, n: usize) -> Expr {
        self.nmul_to_term(m, n)
    }
    /// `pub(super)` re-export for distrib helpers.
    pub(super) fn term_to_nmul_pub(&self, m: &Expr, n: usize) -> Expr {
        self.term_to_nmul(m, n)
    }

    /// `n·M = term_expr(M, n)` for `n ≥ 1`, nonempty mono `M`.
    /// When `n == 1`, `term_expr` is the bare `M`, so prove `1·M = M` (one_mul).
    /// Otherwise `term_expr` is `nat_lit(n)·M`, identical to `n·M` → refl.
    fn nmul_to_term(&self, m: &Expr, n: usize) -> Expr {
        if n == 1 {
            // 1·M = M
            self.one_mul(m.clone())
        } else {
            let nm = self.mul(self.nat_lit(n), m.clone());
            self.refl(nm)
        }
    }

    /// `term_expr(M, n) = n·M` (the reverse of `nmul_to_term`).
    fn term_to_nmul(&self, m: &Expr, n: usize) -> Expr {
        let nm = self.mul(self.nat_lit(n), m.clone());
        let term = if n == 1 { m.clone() } else { nm.clone() };
        if n == 1 {
            // M = 1·M : symm one_mul
            self.symm(
                self.mul(self.one(), m.clone()),
                m.clone(),
                self.one_mul(m.clone()),
            )
        } else {
            self.refl(term)
        }
    }

    /// Coefficient merge for a single shared monomial `M` (nonempty): prove
    /// `term_expr(M, i) + term_expr(M, j) = term_expr(M, i+j)`, for `i, j` of
    /// arbitrary sign (but `i+j ≠ 0`). Returns the proof term.
    pub(super) fn coeff_merge(&self, parent: &EnvDeclBuilder, m: &Expr, i: i64, j: i64) -> Expr {
        let ti = self.term_with(m, i);
        let tj = self.term_with(m, j);
        let lhs = self.add(ti.clone(), tj.clone());
        let sum = i + j;
        let tsum = self.term_with(m, sum);

        if i > 0 && j > 0 {
            // (i·M) + (j·M) = (i+j)·M
            // ti = term(i) ; convert to i·M, j·M.
            let im = self.mul(self.nat_lit(i as usize), m.clone());
            let jm = self.mul(self.nat_lit(j as usize), m.clone());
            let add_c = self.add_op();
            // ti = i·M
            let e_ti = self.term_to_nmul(m, i as usize);
            let c1 = self.cong_l(parent, &add_c, ti.clone(), im.clone(), tj.clone(), e_ti);
            // tj = j·M
            let e_tj = self.term_to_nmul(m, j as usize);
            let c2 = self.cong_r(parent, &add_c, tj.clone(), jm.clone(), im.clone(), e_tj);
            let im_jm = self.add(im.clone(), jm.clone());
            let chain_to_imjm = self.trans(
                lhs.clone(),
                self.add(im.clone(), tj.clone()),
                im_jm.clone(),
                c1,
                c2,
            );
            // i·M + j·M = (iL+jL)·M  [symm rdist]
            let il = self.nat_lit(i as usize);
            let jl = self.nat_lit(j as usize);
            let rdist = self.rdist(il.clone(), jl.clone(), m.clone()); // (iL+jL)·M = iL·M + jL·M
            let iljl = self.add(il.clone(), jl.clone());
            let iljl_m = self.mul(iljl.clone(), m.clone());
            let s_rdist = self.symm(iljl_m.clone(), im_jm.clone(), rdist);
            // (iL+jL)·M = (i+j)L·M  [cong_left numeral_add]
            let na = self.numeral_add(parent, i as usize, j as usize);
            let mul_c = self.mul_op();
            let sum_l = self.nat_lit(sum as usize);
            let cong_sum = self.cong_l(parent, &mul_c, iljl.clone(), sum_l.clone(), m.clone(), na);
            let sum_l_m = self.mul(sum_l.clone(), m.clone());
            // (i+j)L·M = term(i+j)  [reverse nmul_to_term]
            let e_back = self.nmul_to_term(m, sum as usize);
            // chain
            let chain1 = self.trans(
                lhs.clone(),
                im_jm.clone(),
                iljl_m.clone(),
                chain_to_imjm,
                s_rdist,
            );
            let chain2 = self.trans(lhs.clone(), iljl_m, sum_l_m.clone(), chain1, cong_sum);
            return self.trans(lhs, sum_l_m, tsum, chain2, e_back);
        }

        // Signed merges. Reduce to the positive case by routing through a
        // helper: prove `lhs = tsum` via the identity
        //   term(i) + term(j) = term(i+j)
        // expressed as `0 = (i+j) - i - j` cancellations. Implemented case-wise.
        self.coeff_merge_signed(parent, m, i, j, &lhs, &tsum)
    }

    /// Signed coefficient merge. Handles the cases that occur: `i>0, j<0` with
    /// `i+j` of either sign (and symmetric). Built from `add_neg_self`,
    /// `add_assoc`, `add_zero`, `right_distrib`, `numeral_add`.
    fn coeff_merge_signed(
        &self,
        parent: &EnvDeclBuilder,
        m: &Expr,
        i: i64,
        j: i64,
        lhs: &Expr,
        tsum: &Expr,
    ) -> Expr {
        let sum = i + j;

        // Both negative: -(|i|·M) + -(|j|·M) = -((|i|+|j|)·M) = term(sum).
        if i < 0 && j < 0 {
            let ai = (-i) as usize;
            let aj = (-j) as usize;
            let pi = self.term_with(m, -i); // |i|·M (positive form)
            let pj = self.term_with(m, -j);
            let neg_pi = self.neg(pi.clone());
            let neg_pj = self.neg(pj.clone());
            // lhs == (-pi) + (-pj). symm neg_add : (-pi)+(-pj) = -(pi+pj).
            let neg_add = self.neg_add(parent, &pi, &pj); // -(pi+pj) = (-pi)+(-pj)
            let pi_pj = self.add(pi.clone(), pj.clone());
            let neg_pipj = self.neg(pi_pj.clone());
            let s_neg_add = self.symm(
                neg_pipj.clone(),
                self.add(neg_pi.clone(), neg_pj.clone()),
                neg_add,
            );
            // pos merge: pi + pj = ((|i|+|j|)·M) = term(|sum|) (positive)
            let pos_merge = self.coeff_merge(parent, m, -i, -j); // |i|·M + |j|·M = term(|i|+|j|)
            let pos_sum = self.term_with(m, (ai + aj) as i64);
            // cong_neg: -(pi+pj) = -(pos_sum)
            let cong = self.cong_neg_pub(parent, &pi_pj, &pos_sum, &pos_merge);
            let neg_possum = self.neg(pos_sum.clone());
            // tsum (= term(sum), sum<0) is neg(pos_sum) syntactically.
            let chain = self.trans(
                lhs.clone(),
                neg_pipj.clone(),
                neg_possum.clone(),
                s_neg_add,
                cong,
            );
            let _ = tsum;
            return chain;
        }

        // j>0, i<0 (mirror of the i>0,j<0 case): commute then reuse.
        if i < 0 && j > 0 {
            let comm = self.acomm(self.term_with(m, i), self.term_with(m, j)); // ti+tj = tj+ti
            let swapped = self.add(self.term_with(m, j), self.term_with(m, i));
            let merged = self.coeff_merge(parent, m, j, i); // tj+ti = term(j+i)
            return self.trans(lhs.clone(), swapped, tsum.clone(), comm, merged);
        }
        if i > 0 && j < 0 && sum > 0 {
            let a = sum as usize; // i+j
            let b = (-j) as usize; // |j|
                                   // i == a + b. We prove:
                                   //   term(i) + term(j)
                                   //     where term(i)=iL·M (or M), term(j) = -(bL·M) (or -(M))
                                   // Goal: = term(sum) = aL·M (or M if a==1).
                                   //
                                   // Route: iL·M = (aL+bL)·M = aL·M + bL·M  [numeral_add symm + rdist]
                                   //   so lhs = (aL·M + bL·M) + (-(bL·M))
                                   //          = aL·M + (bL·M + -(bL·M))   [add_assoc]
                                   //          = aL·M + 0                  [add_neg_self]
                                   //          = aL·M                      [add_zero]
                                   //          = term(sum)                 [nmul_to_term]
            let il = self.nat_lit(i as usize);
            let al = self.nat_lit(a);
            let bl = self.nat_lit(b);
            let im = self.mul(il.clone(), m.clone());
            let am = self.mul(al.clone(), m.clone());
            let bm = self.mul(bl.clone(), m.clone());
            let neg_bm = self.neg(bm.clone());

            // ti (the materialized term(i)) → im
            let ti = self.term_with(m, i);
            let e_ti = self.term_to_nmul(m, i as usize); // ti = iL·M
                                                         // tj (materialized term(j)) → -(bL·M) ; term(j) for j<0 is neg(term_pos(|j|))
                                                         //   term_pos(b) = bL·M if b>1 else M. So tj = -(term_pos(b)).
            let tj = self.term_with(m, j);
            // We need tj = -(bL·M). If b==1, tj = -(M); convert M=1·M? Keep b≥1.
            let e_tj = {
                // term_pos(b) = bL·M  (e_back-style)
                let tpos = self.term_with(m, b as i64);
                let e_pos = self.term_to_nmul(m, b); // tpos = bL·M
                                                     // -(tpos) = -(bL·M)  [cong_neg]
                self.cong_neg_pub(parent, &tpos, &bm, &e_pos)
            };

            let add_c = self.add_op();
            // lhs = ti + tj  → im + tj  (cong_l e_ti)
            let c1 = self.cong_l(parent, &add_c, ti.clone(), im.clone(), tj.clone(), e_ti);
            // im + tj → im + (-(bL·M))  (cong_r e_tj)
            let c2 = self.cong_r(parent, &add_c, tj.clone(), neg_bm.clone(), im.clone(), e_tj);
            let im_negbm = self.add(im.clone(), neg_bm.clone());
            let to_imnegbm = self.trans(
                lhs.clone(),
                self.add(im.clone(), tj.clone()),
                im_negbm.clone(),
                c1,
                c2,
            );
            // im = aL·M + bL·M :  iL·M = (aL+bL)·M [cong_l (symm numeral_add)] = aL·M+bL·M [rdist]
            let na = self.numeral_add(parent, a, b); // aL + bL = iL  (since a+b = i)
            let albl = self.add(al.clone(), bl.clone());
            let mul_c = self.mul_op();
            // iL·M = (aL+bL)·M  : cong_l (symm na) on M  — na: aL+bL = iL, symm: iL = aL+bL
            let s_na = self.symm(albl.clone(), il.clone(), na);
            let cong_im = self.cong_l(parent, &mul_c, il.clone(), albl.clone(), m.clone(), s_na);
            let albl_m = self.mul(albl.clone(), m.clone());
            // (aL+bL)·M = aL·M + bL·M  [rdist]
            let rdist = self.rdist(al.clone(), bl.clone(), m.clone());
            let am_bm = self.add(am.clone(), bm.clone());
            let im_to_ambm = self.trans(im.clone(), albl_m.clone(), am_bm.clone(), cong_im, rdist);
            // lhs (= im + (-(bm))) rewrite im → am+bm  (cong_l)
            let cong_lhs = self.cong_l(
                parent,
                &add_c,
                im.clone(),
                am_bm.clone(),
                neg_bm.clone(),
                im_to_ambm,
            );
            let ambm_negbm = self.add(am_bm.clone(), neg_bm.clone());
            let chain_a = self.trans(
                lhs.clone(),
                im_negbm.clone(),
                ambm_negbm.clone(),
                to_imnegbm,
                cong_lhs,
            );
            // (am+bm) + (-bm) = am + (bm + (-bm))  [add_assoc]
            let assoc = self.aassoc(am.clone(), bm.clone(), neg_bm.clone());
            let am_bm_negbm = self.add(am.clone(), self.add(bm.clone(), neg_bm.clone()));
            let chain_b = self.trans(
                lhs.clone(),
                ambm_negbm.clone(),
                am_bm_negbm.clone(),
                chain_a,
                assoc,
            );
            // bm + (-bm) = 0  [add_neg_self], lift under (am + ·)
            let ans = self.add_neg_self(&bm); // bm + (-bm) = 0
            let cong_zero = self.cong_r(
                parent,
                &add_c,
                self.add(bm.clone(), neg_bm.clone()),
                self.zero(),
                am.clone(),
                ans,
            );
            let am_zero = self.add(am.clone(), self.zero());
            let chain_c = self.trans(
                lhs.clone(),
                am_bm_negbm.clone(),
                am_zero.clone(),
                chain_b,
                cong_zero,
            );
            // am + 0 = am  [add_zero]
            let azero = self.add_zero(&am);
            let chain_d = self.trans(lhs.clone(), am_zero.clone(), am.clone(), chain_c, azero);
            // am = term(sum)  [nmul_to_term a]
            let e_back = self.nmul_to_term(m, a);
            return self.trans(lhs.clone(), am.clone(), tsum.clone(), chain_d, e_back);
        }
        if i > 0 && j < 0 && sum < 0 {
            // i·M + (-(|j|·M)) = -(|sum|·M)   where |j| = i + |sum|.
            let s = (-sum) as usize; // |sum|
            let ii = i as usize; // i
            let il = self.nat_lit(ii);
            let sl = self.nat_lit(s);
            let im = self.mul(il.clone(), m.clone()); // i·M
            let sm = self.mul(sl.clone(), m.clone()); // |sum|·M
            let neg_im = self.neg(im.clone());
            let neg_sm = self.neg(sm.clone());
            let bm = self.mul(self.nat_lit((-j) as usize), m.clone()); // |j|·M
            let neg_bm = self.neg(bm.clone());

            let ti = self.term_with(m, i);
            let tj = self.term_with(m, j);
            let add_c = self.add_op();

            // ti → i·M
            let e_ti = self.term_to_nmul(m, ii);
            let c1 = self.cong_l(parent, &add_c, ti.clone(), im.clone(), tj.clone(), e_ti);
            // tj → -(|j|·M)
            let tpos = self.term_with(m, -j);
            let e_pos = self.term_to_nmul(m, (-j) as usize);
            let e_tj = self.cong_neg_pub(parent, &tpos, &bm, &e_pos);
            let c2 = self.cong_r(parent, &add_c, tj.clone(), neg_bm.clone(), im.clone(), e_tj);
            let im_negbm = self.add(im.clone(), neg_bm.clone());
            let to_imnegbm = self.trans(
                lhs.clone(),
                self.add(im.clone(), tj.clone()),
                im_negbm.clone(),
                c1,
                c2,
            );

            // |j|·M = i·M + |sum|·M :  (iL+sL)·M = iL·M+sL·M [rdist] with iL+sL = |j|L.
            //   bm = |j|·M = (iL+sL)·M [cong_l symm numeral_add] then rdist.
            let na = self.numeral_add(parent, ii, s); // iL+sL = |j|L
            let bl = self.nat_lit((-j) as usize);
            let ilsl = self.add(il.clone(), sl.clone());
            let mul_c = self.mul_op();
            let s_na = self.symm(ilsl.clone(), bl.clone(), na); // |j|L = iL+sL
            let cong_bm = self.cong_l(parent, &mul_c, bl.clone(), ilsl.clone(), m.clone(), s_na);
            let ilsl_m = self.mul(ilsl.clone(), m.clone());
            let rdist = self.rdist(il.clone(), sl.clone(), m.clone()); // (iL+sL)·M = iL·M+sL·M
            let im_sm = self.add(im.clone(), sm.clone());
            let bm_to_imsm = self.trans(bm.clone(), ilsl_m.clone(), im_sm.clone(), cong_bm, rdist);
            // -(|j|·M) = -(i·M + |sum|·M) [cong_neg] = (-(i·M)) + (-(|sum|·M)) [neg_add]
            let cong_neg = self.cong_neg_pub(parent, &bm, &im_sm, &bm_to_imsm);
            let neg_imsm = self.neg(im_sm.clone());
            let neg_add = self.neg_add(parent, &im, &sm); // -(im+sm) = (-im)+(-sm)
            let split = self.add(neg_im.clone(), neg_sm.clone());
            let negbm_to_split = self.trans(
                neg_bm.clone(),
                neg_imsm.clone(),
                split.clone(),
                cong_neg,
                neg_add,
            );
            // lift into lhs: im + (-(|j|·M)) → im + ((-im)+(-sm))   [cong_r]
            let cong_lhs = self.cong_r(
                parent,
                &add_c,
                neg_bm.clone(),
                split.clone(),
                im.clone(),
                negbm_to_split,
            );
            let im_split = self.add(im.clone(), split.clone());
            let chain_a = self.trans(
                lhs.clone(),
                im_negbm.clone(),
                im_split.clone(),
                to_imnegbm,
                cong_lhs,
            );
            // im + ((-im)+(-sm)) = (im + (-im)) + (-sm)   [symm add_assoc]
            let assoc = self.aassoc(im.clone(), neg_im.clone(), neg_sm.clone());
            let im_negim_negsm = self.add(self.add(im.clone(), neg_im.clone()), neg_sm.clone());
            let s_assoc = self.symm(im_negim_negsm.clone(), im_split.clone(), assoc);
            let chain_b = self.trans(
                lhs.clone(),
                im_split.clone(),
                im_negim_negsm.clone(),
                chain_a,
                s_assoc,
            );
            // (im + (-im)) → 0  [add_neg_self], lift cong_l over (·+(-sm))
            let ans = self.add_neg_self(&im);
            let cong_zero = self.cong_l(
                parent,
                &add_c,
                self.add(im.clone(), neg_im.clone()),
                self.zero(),
                neg_sm.clone(),
                ans,
            );
            let zero_negsm = self.add(self.zero(), neg_sm.clone());
            let chain_c = self.trans(
                lhs.clone(),
                im_negim_negsm.clone(),
                zero_negsm.clone(),
                chain_b,
                cong_zero,
            );
            // 0 + (-sm) = (-sm)  [zero_add]
            let za = self.zero_add(&neg_sm);
            let chain_d = self.trans(lhs.clone(), zero_negsm.clone(), neg_sm.clone(), chain_c, za);
            // neg_sm = term(sum)  (sum<0 → term_with neg-wraps |sum|·M = sm). But term_with
            //   for sum: |sum|≥1; if |sum|==1, term is -(M) not -(1·M). Bridge:
            //   -(sm) = -(term_with(m,|sum|))  via cong_neg (sm = |sum|·M = posTerm via nmul_to_term).
            let pos_sum = self.term_with(m, -sum); // positive form (M or |sum|·M)
            let e_back = self.nmul_to_term(m, s); // sm-form: nat_lit(s)·M = pos_sum
            let cong_back = self.cong_neg_pub(parent, &sm, &pos_sum, &e_back);
            return self.trans(
                lhs.clone(),
                neg_sm.clone(),
                tsum.clone(),
                chain_d,
                cong_back,
            );
        }
        panic!(
            "coeff_merge_signed: unhandled sign pattern i={i} j={j} sum={sum} — surface, don't mis-prove"
        );
    }

    /// Materialize `term_expr(M, coeff)` given the already-built monomial `Expr`
    /// `m` (nonempty). Mirrors `term_expr` exactly.
    pub(super) fn term_with(&self, m: &Expr, coeff: i64) -> Expr {
        debug_assert!(coeff != 0);
        let mag = coeff.unsigned_abs() as usize;
        let pos = if mag == 1 {
            m.clone()
        } else {
            self.mul(self.nat_lit(mag), m.clone())
        };
        if coeff < 0 {
            self.neg(pos)
        } else {
            pos
        }
    }
}
