// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The multiplicative engine: product distribution (`distribute`), single-term
//! multiplication (`mul_terms`), monomial multiplication (sort a product of
//! atoms into canonical order) and numeral multiplication.
//!
//! `distribute` expands `(Σ aᵢ)·(Σ bⱼ)` into the flat list `[aᵢ·bⱼ]` (each
//! reduced to a single canonical term by `mul_terms`), reified as a right-nested
//! sum ready for the additive normalizer.

use super::combine::TermPub;
use super::{Monomial, RatPolyProver};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;

impl RatPolyProver {
    /// Distribute `reify(A)·reify(B)` into the flat product term list.
    /// Returns `(prod_terms, prod_expr, proof : reify(A)·reify(B) = prod_expr)`
    /// where `prod_expr == reify_sterms(prod_terms)`.
    pub(super) fn distribute(
        &self,
        parent: &EnvDeclBuilder,
        a: &[TermPub],
        b: &[TermPub],
    ) -> (Vec<TermPub>, Expr, Expr) {
        let big_a = self.reify_sterms_pub(a);
        let big_b = self.reify_sterms_pub(b);
        let lhs = self.mul(big_a.clone(), big_b.clone());

        if a.is_empty() {
            // 0 · B = 0   [zero_mul B]
            let zm = Expr::const_(crate::name::Name::from_string("Rat.zero_mul"), vec![]);
            let h = Expr::app(zm, big_b.clone());
            return (Vec::new(), self.zero(), h);
        }
        if a.len() == 1 {
            // (a0)·B → distribute over B.
            let (terms, expr, h) = self.distribute_left_single(parent, &a[0], b);
            return (terms, expr, h);
        }
        // A = a0 + Arest. (a0 + Arest)·B = a0·B + Arest·B   [right_distrib]
        let a0 = a[0].clone();
        let arest = &a[1..];
        let a0_e = self.reify_term(a0.coeff, &a0.mono);
        let arest_e = self.reify_sterms_pub(arest);
        let h_rd = self.c.rdist(a0_e.clone(), arest_e.clone(), big_b.clone());
        let a0b = self.mul(a0_e.clone(), big_b.clone());
        let arestb = self.mul(arest_e.clone(), big_b.clone());
        let split = self.add(a0b.clone(), arestb.clone());
        // recurse: a0·B and Arest·B
        let (terms0, expr0, h0) = self.distribute_left_single(parent, &a0, b);
        let (terms_rest, expr_rest, h_rest) = self.distribute(parent, arest, b);
        // lift: a0·B + Arest·B = expr0 + Arest·B  [cong_left h0]
        let add_c = self.add_const();
        let c0 = self.cong_left(
            parent,
            &add_c,
            a0b.clone(),
            expr0.clone(),
            arestb.clone(),
            h0,
        );
        let mid = self.add(expr0.clone(), arestb.clone());
        // = expr0 + expr_rest  [cong_right h_rest]
        let c1 = self.cong_right(
            parent,
            &add_c,
            arestb.clone(),
            expr_rest.clone(),
            expr0.clone(),
            h_rest,
        );
        let combined = self.add(expr0.clone(), expr_rest.clone());
        // now flatten expr0 ++ expr_rest into one right-nested list
        let mut all = terms0.clone();
        all.extend(terms_rest.clone());
        let (flat_expr, h_flat) = self.flatten_two(parent, &terms0, &terms_rest);
        // chain: lhs = split = mid = combined = flat_expr
        let s = self.trans(lhs.clone(), split.clone(), mid.clone(), h_rd, c0);
        let s = self.trans(lhs.clone(), mid, combined.clone(), s, c1);
        let proof = self.trans(lhs, combined, flat_expr.clone(), s, h_flat);
        (all, flat_expr, proof)
    }

    /// `(a0)·reify(B)` distributed over B into a flat product list.
    fn distribute_left_single(
        &self,
        parent: &EnvDeclBuilder,
        a0: &TermPub,
        b: &[TermPub],
    ) -> (Vec<TermPub>, Expr, Expr) {
        let a0_e = self.reify_term(a0.coeff, &a0.mono);
        let big_b = self.reify_sterms_pub(b);
        let lhs = self.mul(a0_e.clone(), big_b.clone());
        if b.is_empty() {
            // a0 · 0 = 0   [mul_zero]
            let h = Expr::apps(self.mul_zero.clone(), [a0_e.clone()]);
            return (Vec::new(), self.zero(), h);
        }
        if b.len() == 1 {
            // a0 · b0 → single product
            let (term, h) = self.mul_terms(parent, a0, &b[0]);
            let e = self.reify_term(term.coeff, &term.mono);
            return (vec![term], e, h);
        }
        // a0 · (b0 + Brest) = a0·b0 + a0·Brest   [left_distrib]
        let b0 = b[0].clone();
        let brest = &b[1..];
        let b0_e = self.reify_term(b0.coeff, &b0.mono);
        let brest_e = self.reify_sterms_pub(brest);
        let h_ld = self.c.ldist(a0_e.clone(), b0_e.clone(), brest_e.clone());
        let a0b0 = self.mul(a0_e.clone(), b0_e.clone());
        let a0brest = self.mul(a0_e.clone(), brest_e.clone());
        let split = self.add(a0b0.clone(), a0brest.clone());
        let (term0, h0) = self.mul_terms(parent, a0, &b0);
        let term0_e = self.reify_term(term0.coeff, &term0.mono);
        let (terms_rest, expr_rest, h_rest) = self.distribute_left_single(parent, a0, brest);
        let add_c = self.add_const();
        let c0 = self.cong_left(
            parent,
            &add_c,
            a0b0.clone(),
            term0_e.clone(),
            a0brest.clone(),
            h0,
        );
        let mid = self.add(term0_e.clone(), a0brest.clone());
        let c1 = self.cong_right(
            parent,
            &add_c,
            a0brest.clone(),
            expr_rest.clone(),
            term0_e.clone(),
            h_rest,
        );
        let combined = self.add(term0_e.clone(), expr_rest.clone());
        let term0_list = vec![term0.clone()];
        let (flat_expr, h_flat) = self.flatten_two(parent, &term0_list, &terms_rest);
        let mut all = term0_list;
        all.extend(terms_rest);
        let s = self.trans(lhs.clone(), split.clone(), mid.clone(), h_ld, c0);
        let s = self.trans(lhs.clone(), mid, combined.clone(), s, c1);
        let proof = self.trans(lhs, combined, flat_expr.clone(), s, h_flat);
        (all, flat_expr, proof)
    }

    /// Multiply two single terms: prove
    /// `reify_term(c1,m1) · reify_term(c2,m2) = reify_term(c1·c2, m1·m2)`.
    fn mul_terms(&self, parent: &EnvDeclBuilder, t1: &TermPub, t2: &TermPub) -> (TermPub, Expr) {
        let c1 = t1.coeff;
        let c2 = t2.coeff;
        let prod_coeff = c1 * c2;
        let prod_mono = t1.mono.mul(&t2.mono);
        let result = TermPub {
            coeff: prod_coeff,
            mono: prod_mono.clone(),
        };
        // Reduce signs to a positive-coeff product, tracking the outer neg shape.
        let a1 = c1.unsigned_abs() as u32;
        let a2 = c2.unsigned_abs() as u32;
        let abs1 = self.reify_pos_term(a1, &t1.mono); // |c1|·m1
        let abs2 = self.reify_pos_term(a2, &t2.mono); // |c2|·m2
        let t1_e = self.reify_term(c1, &t1.mono);
        let t2_e = self.reify_term(c2, &t2.mono);
        let lhs = self.mul(t1_e.clone(), t2_e.clone());

        // h_pos : abs1 · abs2 = reify_pos_term(|c1·c2|, m1·m2)
        let h_pos = self.mul_pos_terms(parent, a1, &t1.mono, a2, &t2.mono);
        let pos_prod = self.reify_pos_term(prod_coeff.unsigned_abs() as u32, &prod_mono);

        let neg1 = c1 < 0;
        let neg2 = c2 < 0;
        let proof = match (neg1, neg2) {
            (false, false) => {
                // lhs == abs1·abs2 already (t_e == abs when positive). h_pos.
                h_pos
            }
            (true, false) => {
                // (neg abs1)·abs2 = neg(abs1·abs2)  [neg_mul]; then congr neg h_pos.
                let h_nm = self.neg_mul(parent, &abs1, &abs2);
                let neg_prod = self.neg(self.mul(abs1.clone(), abs2.clone()));
                let cong = self.cong_neg(
                    parent,
                    self.mul(abs1.clone(), abs2.clone()),
                    pos_prod.clone(),
                    h_pos,
                );
                let target = self.neg(pos_prod.clone());
                self.trans(lhs.clone(), neg_prod, target, h_nm, cong)
            }
            (false, true) => {
                // abs1·(neg abs2) = neg(abs1·abs2)  [mul_neg]
                let h_mn = self.c.mneg(abs1.clone(), abs2.clone());
                let neg_prod = self.neg(self.mul(abs1.clone(), abs2.clone()));
                let cong = self.cong_neg(
                    parent,
                    self.mul(abs1.clone(), abs2.clone()),
                    pos_prod.clone(),
                    h_pos,
                );
                let target = self.neg(pos_prod.clone());
                self.trans(lhs.clone(), neg_prod, target, h_mn, cong)
            }
            (true, true) => {
                // (neg abs1)·(neg abs2) = abs1·abs2  [neg_mul_neg]; then h_pos.
                let nmn = Expr::const_(crate::name::Name::from_string("Rat.neg_mul_neg"), vec![]);
                let h_nmn = Expr::apps(nmn, [abs1.clone(), abs2.clone()]);
                let prod = self.mul(abs1.clone(), abs2.clone());
                self.trans(lhs.clone(), prod, pos_prod.clone(), h_nmn, h_pos)
            }
        };
        (result, proof)
    }

    /// `Rat.neg_mul`-analog (not registered standalone): `(neg a)·b = neg(a·b)`.
    /// Built `(neg a)·b = b·(neg a)` [mul_comm] `= neg(b·a)` [mul_neg]
    /// `= neg(a·b)` [congr neg mul_comm].
    fn neg_mul(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr) -> Expr {
        let na = self.neg(a.clone());
        let lhs = self.mul(na.clone(), b.clone()); // (neg a)·b
        let b_na = self.mul(b.clone(), na.clone()); // b·(neg a)
        let h1 = self.c.mcomm(na.clone(), b.clone()); // (neg a)·b = b·(neg a)
        let h2 = self.c.mneg(b.clone(), a.clone()); // b·(neg a) = neg(b·a)
        let neg_ba = self.neg(self.mul(b.clone(), a.clone()));
        let h3 = self.cong_neg(
            parent,
            self.mul(b.clone(), a.clone()),
            self.mul(a.clone(), b.clone()),
            self.c.mcomm(b.clone(), a.clone()),
        );
        let neg_ab = self.neg(self.mul(a.clone(), b.clone()));
        let s = self.trans(lhs.clone(), b_na, neg_ba.clone(), h1, h2);
        self.trans(lhs, neg_ba, neg_ab, s, h3)
    }
}
