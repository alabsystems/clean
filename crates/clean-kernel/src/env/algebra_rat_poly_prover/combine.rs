// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The normal-form combiners: prove that the result of an `add`/`mul`/`neg` on
//! two *already-canonical* sums equals the canonical form of the combined
//! polynomial. All three reduce to the signed-term-list engine in
//! `combine_engine.rs`.

use super::{Monomial, Poly, RatPolyProver};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;

/// A signed monomial term carried with its (reduced) integer coefficient.
#[derive(Clone, PartialEq, Eq)]
pub(super) struct TermPub {
    pub(super) coeff: i128,
    pub(super) mono: Monomial,
}

impl RatPolyProver {
    /// Prove `reify(pa) + reify(pb) = reify(pa + pb)`.
    pub(super) fn prove_add_of_canon(&self, parent: &EnvDeclBuilder, pa: &Poly, pb: &Poly) -> Expr {
        let terms_a = self.poly_terms(pa);
        let terms_b = self.poly_terms(pb);
        let lhs = self.add(self.reify_poly(pa), self.reify_poly(pb));
        // Flatten (A + B) → concatenated term list.
        let mut concat = terms_a.clone();
        concat.extend(terms_b.clone());
        let concat_e = self.reify_sterms_pub(&concat);
        let (flat_expr, h_flat) = self.flatten_two(parent, &terms_a, &terms_b);
        debug_assert_eq!(flat_expr, concat_e);
        // Normalize the concatenation to canonical.
        let (canon_expr, h_norm) = self.normalize_list(parent, &concat, &concat_e);
        self.trans(lhs, concat_e, canon_expr, h_flat, h_norm)
    }

    /// Prove `reify(pa) · reify(pb) = reify(pa · pb)`.
    pub(super) fn prove_mul_of_canon(&self, parent: &EnvDeclBuilder, pa: &Poly, pb: &Poly) -> Expr {
        let terms_a = self.poly_terms(pa);
        let terms_b = self.poly_terms(pb);
        let lhs = self.mul(self.reify_poly(pa), self.reify_poly(pb));
        let (prod_terms, prod_expr, h_dist) = self.distribute(parent, &terms_a, &terms_b);
        let (canon_expr, h_norm) = self.normalize_list(parent, &prod_terms, &prod_expr);
        self.trans(lhs, prod_expr, canon_expr, h_dist, h_norm)
    }

    /// Prove `Rat.neg (reify(pa)) = reify(-pa)`.
    pub(super) fn prove_neg_of_canon(&self, parent: &EnvDeclBuilder, pa: &Poly) -> Expr {
        let terms = self.poly_terms(pa);
        self.push_neg(parent, &terms)
    }

    // ── term-list helpers shared with the engine ─────────────────────────────

    pub(super) fn poly_terms(&self, p: &Poly) -> Vec<TermPub> {
        p.sorted_terms()
            .into_iter()
            .map(|(coeff, mono)| TermPub { coeff, mono })
            .collect()
    }

    /// Reify a `TermPub` list as a right-nested sum.
    pub(super) fn reify_sterms_pub(&self, terms: &[TermPub]) -> Expr {
        if terms.is_empty() {
            return self.zero();
        }
        let mut iter = terms.iter().rev();
        let last = iter.next().expect("nonempty");
        let mut acc = self.reify_term(last.coeff, &last.mono);
        for t in iter {
            acc = self.add(self.reify_term(t.coeff, &t.mono), acc);
        }
        acc
    }

    /// Prove `reify(a) + reify(b) = reify(a ++ b)` (concatenation), peeling the
    /// left list onto the right via `Rat.add_assoc`; base `0 + B = B`.
    pub(super) fn flatten_two(
        &self,
        parent: &EnvDeclBuilder,
        a: &[TermPub],
        b: &[TermPub],
    ) -> (Expr, Expr) {
        let big_b = self.reify_sterms_pub(b);
        if a.is_empty() {
            let h = Expr::apps(self.zero_add.clone(), [big_b.clone()]);
            return (big_b, h);
        }
        if a.len() == 1 && b.is_empty() {
            // reify([a0]) + 0 = a0   [add_zero]; concat == [a0].
            let a0 = self.reify_term(a[0].coeff, &a[0].mono);
            let h = Expr::app(self.add_zero.clone(), a0.clone());
            return (a0, h);
        }
        // A = a0 + A'  (A' = reify(a[1..])); when a.len()==1, reify(a)==a0.
        let a0 = self.reify_term(a[0].coeff, &a[0].mono);
        let a_rest = &a[1..];
        let big_a = self.reify_sterms_pub(a);
        if a_rest.is_empty() {
            // a.len()==1, b nonempty: big_a == a0. (a0 + B) is already the concat.
            let result = self.add(a0.clone(), big_b.clone());
            return (result.clone(), self.refl(result));
        }
        let a_rest_expr = self.reify_sterms_pub(a_rest);
        // (A + B) = ((a0 + A') + B) = a0 + (A' + B)   [add_assoc a0 A' B]
        let h_assoc = self.aassoc_combine(a0.clone(), a_rest_expr.clone(), big_b.clone());
        let lhs = self.add(big_a.clone(), big_b.clone());
        let mid = self.add(a0.clone(), self.add(a_rest_expr.clone(), big_b.clone()));
        let (rest_flat, h_rest) = self.flatten_two(parent, a_rest, b);
        let add_c = self.add_const();
        let cong = self.cong_right(
            parent,
            &add_c,
            self.add(a_rest_expr.clone(), big_b.clone()),
            rest_flat.clone(),
            a0.clone(),
            h_rest,
        );
        let result = self.add(a0.clone(), rest_flat);
        let h = self.trans(lhs, mid, result.clone(), h_assoc, cong);
        (result, h)
    }

    fn aassoc_combine(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        self.c.aassoc(a, b, cc)
    }
}
