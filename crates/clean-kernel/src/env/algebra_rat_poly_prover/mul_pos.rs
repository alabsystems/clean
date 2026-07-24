// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Positive-coefficient single-term multiplication, plus its two ingredients:
//! numeral multiplication (`numeral(a)·numeral(b) = numeral(a·b)`) and monomial
//! multiplication (sort a product of atoms into canonical order).
//!
//! Strategy for `reify_pos_term(a1,m1)·reify_pos_term(a2,m2)`: lift both to the
//! uniform `numeral·mono` shape, interchange via `Rat.mul_mul_mul_comm`
//! (`(N1·M1)·(N2·M2) = (N1·N2)·(M1·M2)`), fold `N1·N2 → numeral(a1·a2)` and
//! `M1·M2 → reify_mono(m1·m2)`, then collapse back to `reify_pos_term`.

use super::{Monomial, RatPolyProver};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;
use crate::name::Name;

impl RatPolyProver {
    /// `reify_pos_term(a1,m1) · reify_pos_term(a2,m2)
    ///    = reify_pos_term(a1·a2, m1·m2)`, for `a1, a2 ≥ 1`.
    pub(super) fn mul_pos_terms(
        &self,
        parent: &EnvDeclBuilder,
        a1: u32,
        m1: &Monomial,
        a2: u32,
        m2: &Monomial,
    ) -> Expr {
        let t1 = self.reify_pos_term(a1, m1);
        let t2 = self.reify_pos_term(a2, m2);
        let lhs = self.mul(t1.clone(), t2.clone());

        let n1 = self.numeral(a1);
        let n2 = self.numeral(a2);
        let mo1 = self.reify_monomial(m1);
        let mo2 = self.reify_monomial(m2);
        let nm1 = self.mul(n1.clone(), mo1.clone());
        let nm2 = self.mul(n2.clone(), mo2.clone());

        // u1 : t1 = n1·mo1 ; u2 : t2 = n2·mo2
        let u1 = self.to_nm(a1, m1);
        let u2 = self.to_nm(a2, m2);
        let mul_c = self.mul_const();
        let c1 = self.cong_left(parent, &mul_c, t1.clone(), nm1.clone(), t2.clone(), u1);
        let mid1 = self.mul(nm1.clone(), t2.clone());
        let c2 = self.cong_right(parent, &mul_c, t2.clone(), nm2.clone(), nm1.clone(), u2);
        let uniform = self.mul(nm1.clone(), nm2.clone()); // (n1·mo1)·(n2·mo2)
        let h_uniform = self.trans(lhs.clone(), mid1, uniform.clone(), c1, c2);

        // interchange: (n1·mo1)·(n2·mo2) = (n1·n2)·(mo1·mo2)
        let mmmc = Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]);
        let h_inter = Expr::apps(mmmc, [n1.clone(), mo1.clone(), n2.clone(), mo2.clone()]);
        let n1n2 = self.mul(n1.clone(), n2.clone());
        let mo1mo2 = self.mul(mo1.clone(), mo2.clone());
        let interchanged = self.mul(n1n2.clone(), mo1mo2.clone());

        // n1·n2 = numeral(a1·a2)
        let h_num = self.numeral_mul(parent, a1, a2);
        let num_prod = self.numeral(a1 * a2);
        let c_num = self.cong_left(
            parent,
            &mul_c,
            n1n2.clone(),
            num_prod.clone(),
            mo1mo2.clone(),
            h_num,
        );
        let after_num = self.mul(num_prod.clone(), mo1mo2.clone());

        // mo1·mo2 = reify_mono(m1·m2)
        let prod_m = m1.mul(m2);
        let h_mono = self.mono_mul(parent, m1, m2);
        let prod_mono_e = self.reify_monomial(&prod_m);
        let c_mono = self.cong_right(
            parent,
            &mul_c,
            mo1mo2.clone(),
            prod_mono_e.clone(),
            num_prod.clone(),
            h_mono,
        );
        let after_mono = self.mul(num_prod.clone(), prod_mono_e.clone());

        // collapse numeral(a1·a2)·reify_mono(m1·m2) = reify_pos_term(a1·a2, m1·m2)
        let target = self.reify_pos_term(a1 * a2, &prod_m);
        let h_collapse = self.collapse_nm(a1 * a2, &prod_m);

        let s = self.trans(
            lhs.clone(),
            uniform,
            interchanged.clone(),
            h_uniform,
            h_inter,
        );
        let s = self.trans(lhs.clone(), interchanged, after_num.clone(), s, c_num);
        let s = self.trans(lhs.clone(), after_num, after_mono.clone(), s, c_mono);
        self.trans(lhs, after_mono, target, s, h_collapse)
    }

    /// `reify_pos_term(a,m) = numeral(a)·reify_mono(m)`.
    fn to_nm(&self, a: u32, m: &Monomial) -> Expr {
        let mono = self.reify_monomial(m);
        let n = self.numeral(a);
        let nm = self.mul(n.clone(), mono.clone());
        if a == 1 && m.is_one() {
            // reify = Rat.one ; nm = 1·1. Want `1 = 1·1` = symm(one_mul 1).
            let one = self.one();
            let one_one = self.mul(one.clone(), one.clone()); // 1·1 == nm
            let h = self.c.one_mul(one.clone()); // 1·1 = 1   (nm = reify)
            return self.symm(one_one, one, h);
        }
        if a == 1 {
            // reify = mono ; nm = 1·mono. Want `mono = 1·mono` = symm(one_mul mono).
            let one_mono = self.mul(self.one(), mono.clone()); // == nm
            let h = self.c.one_mul(mono.clone()); // 1·mono = mono  (nm = reify)
            return self.symm(one_mono, mono, h);
        }
        if m.is_one() {
            // reify = numeral(a) ; nm = numeral(a)·1. Want `numeral(a) = numeral(a)·1`
            //   = symm(mul_one numeral(a)).
            let n_one = self.mul(n.clone(), self.one()); // == nm
            let h = self.mul_one_lemma(n.clone()); // numeral(a)·1 = numeral(a) (nm=reify)
            return self.symm(n_one, n.clone(), h);
        }
        // a≥2, m≠1: reify == numeral(a)·mono == nm. refl.
        self.refl(nm)
    }

    /// `numeral(n)·reify_mono(m) = reify_pos_term(n,m)`  (inverse of `to_nm`).
    fn collapse_nm(&self, n: u32, m: &Monomial) -> Expr {
        let mono = self.reify_monomial(m);
        let nn = self.numeral(n);
        let nm = self.mul(nn.clone(), mono.clone());
        if n == 1 && m.is_one() {
            // 1·1 = 1   [one_mul 1]
            return self.c.one_mul(self.one());
        }
        if n == 1 {
            // 1·mono = mono   [one_mul]
            return self.c.one_mul(mono);
        }
        if m.is_one() {
            // numeral(n)·1 = numeral(n)   [mul_one]
            return self.mul_one_lemma(nn);
        }
        self.refl(nm)
    }

    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one_lemma(&self, a: Expr) -> Expr {
        let mul_one = Expr::const_(Name::from_string("Rat.mul_one"), vec![]);
        Expr::app(mul_one, a)
    }

    /// `numeral(a)·numeral(b) = numeral(a·b)`, `a,b ≥ 1`.
    fn numeral_mul(&self, parent: &EnvDeclBuilder, a: u32, b: u32) -> Expr {
        debug_assert!(a >= 1 && b >= 1);
        let na = self.numeral(a);
        if b == 1 {
            // numeral(a)·1 = numeral(a) == numeral(a·1)   [mul_one]
            return self.mul_one_lemma(na);
        }
        // numeral(b) == numeral(b-1) + 1
        let nb1 = self.numeral(b - 1);
        let lhs = self.mul(na.clone(), self.add(nb1.clone(), self.one()));
        // left_distrib na numeral(b-1) 1 : na·(numeral(b-1)+1) = na·numeral(b-1) + na·1
        let h_ld = self.c.ldist(na.clone(), nb1.clone(), self.one());
        let na_nb1 = self.mul(na.clone(), nb1.clone());
        let na_one = self.mul(na.clone(), self.one());
        let split = self.add(na_nb1.clone(), na_one.clone());
        // na·numeral(b-1) = numeral(a·(b-1))  [recurse]
        let h_rec = self.numeral_mul(parent, a, b - 1);
        let num_ab1 = self.numeral(a * (b - 1));
        let add_c = self.add_const();
        let c0 = self.cong_left(
            parent,
            &add_c,
            na_nb1.clone(),
            num_ab1.clone(),
            na_one.clone(),
            h_rec,
        );
        let mid = self.add(num_ab1.clone(), na_one.clone());
        // na·1 = na = numeral(a)  [mul_one]
        let h_mo = self.mul_one_lemma(na.clone());
        let c1 = self.cong_right(
            parent,
            &add_c,
            na_one.clone(),
            na.clone(),
            num_ab1.clone(),
            h_mo,
        );
        let combined = self.add(num_ab1.clone(), na.clone()); // numeral(a(b-1)) + numeral(a)
                                                              // numeral(a(b-1)) + numeral(a) = numeral(a(b-1)+a) = numeral(a·b)
        let h_na = self.numeral_add(parent, a * (b - 1), a);
        let num_ab = self.numeral(a * b);
        // chain: lhs = split = mid = combined = num_ab
        let s = self.trans(lhs.clone(), split.clone(), mid.clone(), h_ld, c0);
        let s = self.trans(lhs.clone(), mid, combined.clone(), s, c1);
        self.trans(lhs, combined, num_ab, s, h_na)
    }
}
