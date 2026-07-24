// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The signed-term-list normalizer engine: `normalize_list`, `insert_term`
//! (sorted insert with coefficient merge), `distribute` (product expansion) and
//! `push_neg` (negation over a sum). These turn a flat right-nested sum of
//! signed monomial terms into the sorted, coefficient-collected canonical poly,
//! with a kernel proof of equality.

use super::combine::TermPub as STerm;
use super::{Monomial, RatPolyProver};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;

impl RatPolyProver {
    /// Reify a signed-term list as a right-nested sum (alias of the public one).
    fn reify_sterms(&self, terms: &[STerm]) -> Expr {
        self.reify_sterms_pub(terms)
    }

    /// Normalize a flat term list (reified as `list_expr`) to canonical poly.
    /// Returns `(canon_expr, proof : list_expr = canon_expr)`.
    pub(super) fn normalize_list(
        &self,
        parent: &EnvDeclBuilder,
        terms: &[STerm],
        list_expr: &Expr,
    ) -> (Expr, Expr) {
        let (canon_terms, proof) = self.fold_list(parent, terms);
        let canon = self.reify_sterms(&canon_terms);
        debug_assert_eq!(&self.reify_sterms(terms), list_expr);
        (canon, proof)
    }

    /// Fold a flat list (right-nested) into sorted+collected canonical form.
    /// Returns `(canon_terms, proof : reify(terms) = reify(canon_terms))`.
    fn fold_list(&self, parent: &EnvDeclBuilder, terms: &[STerm]) -> (Vec<STerm>, Expr) {
        if terms.is_empty() {
            let z = self.zero();
            return (Vec::new(), self.refl(z));
        }
        if terms.len() == 1 {
            let e = self.reify_term(terms[0].coeff, &terms[0].mono);
            return (terms.to_vec(), self.refl(e));
        }
        // head :: rest ; reify(terms) = head + reify(rest)
        let head = terms[0].clone();
        let rest = &terms[1..];
        let (rest_canon, h_rest) = self.fold_list(parent, rest);
        let head_e = self.reify_term(head.coeff, &head.mono);
        let rest_e = self.reify_sterms(rest);
        let rest_canon_e = self.reify_sterms(&rest_canon);
        // lift h_rest under (head + ·): (head + rest_e) = (head + rest_canon_e)
        let add_c = self.add_const();
        let c1 = self.cong_right(
            parent,
            &add_c,
            rest_e.clone(),
            rest_canon_e.clone(),
            head_e.clone(),
            h_rest,
        );
        let lhs = self.add(head_e.clone(), rest_e);
        let mid = self.add(head_e.clone(), rest_canon_e);
        // insert head into the canonical rest_canon
        let (ins_terms, h_ins) = self.insert_term(parent, &head, &rest_canon);
        let ins_e = self.reify_sterms(&ins_terms);
        let proof = self.trans(lhs, mid, ins_e, c1, h_ins);
        (ins_terms, proof)
    }

    /// Insert a single term into a sorted+collected canonical list.
    /// Returns `(new_terms, proof : reify_term(t) + reify(sorted) = reify(new_terms))`.
    fn insert_term(
        &self,
        parent: &EnvDeclBuilder,
        t: &STerm,
        sorted: &[STerm],
    ) -> (Vec<STerm>, Expr) {
        let t_e = self.reify_term(t.coeff, &t.mono);
        if sorted.is_empty() {
            // t + 0 = t   [add_zero]
            let lhs = self.add(t_e.clone(), self.zero());
            let h = Expr::app(self.add_zero.clone(), t_e.clone());
            return (vec![t.clone()], h);
        }
        let head = sorted[0].clone();
        let rest = &sorted[1..];
        use std::cmp::Ordering;
        match t.mono.cmp(&head.mono) {
            Ordering::Greater => {
                // t leads; result already sorted: t :: sorted.  proof: refl.
                let mut out = vec![t.clone()];
                out.extend(sorted.to_vec());
                let e = self.reify_sterms(&out);
                (out, self.refl(e))
            }
            Ordering::Equal => self.insert_merge(parent, t, &head, rest),
            Ordering::Less => self.insert_deeper(parent, t, &head, rest),
        }
    }

    /// `t` and `head` share a monomial: merge coefficients, then prepend the rest.
    fn insert_merge(
        &self,
        parent: &EnvDeclBuilder,
        t: &STerm,
        head: &STerm,
        rest: &[STerm],
    ) -> (Vec<STerm>, Expr) {
        let m = &t.mono;
        let t_e = self.reify_term(t.coeff, m);
        let head_e = self.reify_term(head.coeff, m);
        let rest_e = self.reify_sterms(rest);
        let add_c = self.add_const();
        let new_coeff = t.coeff + head.coeff;

        if rest.is_empty() {
            // sorted == [head]: reify is just head_e (no trailing `+ 0`).
            // lhs = t + head_e ; fold the pair directly.
            let (merged_terms, h) = self.fold_pair(parent, t, head);
            return (merged_terms, h);
        }

        // sorted = head :: rest (rest nonempty) → reify = head_e + rest_e.
        let lhs = self.add(t_e.clone(), self.add(head_e.clone(), rest_e.clone()));
        // t + (head_e + rest_e) = (t + head_e) + rest_e   [symm add_assoc]
        let t_head = self.add(t_e.clone(), head_e.clone());
        let assoc = self.aassoc_eng(t_e.clone(), head_e.clone(), rest_e.clone());
        let assoc_lhs = self.add(t_head.clone(), rest_e.clone());
        let h_assoc = self.symm(assoc_lhs.clone(), lhs.clone(), assoc);
        // fold (t + head_e) → merged term(s)
        let (merged_terms, h_fold) = self.fold_pair(parent, t, head);
        let merged_e = self.reify_sterms(&merged_terms);
        if new_coeff == 0 {
            // merged_terms == [] ⇒ merged_e == 0. (t+head_e)+rest_e = 0 + rest_e = rest_e
            let c_fold = self.cong_left(
                parent,
                &add_c,
                t_head.clone(),
                self.zero(),
                rest_e.clone(),
                h_fold,
            );
            let zero_plus_rest = self.add(self.zero(), rest_e.clone());
            let h_zadd = Expr::apps(self.zero_add.clone(), [rest_e.clone()]);
            let s = self.trans(
                lhs.clone(),
                assoc_lhs.clone(),
                zero_plus_rest.clone(),
                h_assoc,
                c_fold,
            );
            let proof = self.trans(lhs, zero_plus_rest, rest_e.clone(), s, h_zadd);
            return (rest.to_vec(), proof);
        }
        // merged_terms == [merged] (single term, nonzero). (t+head_e)+rest_e =
        // merged_e + rest_e  [cong_left h_fold]
        let c_fold = self.cong_left(
            parent,
            &add_c,
            t_head.clone(),
            merged_e.clone(),
            rest_e.clone(),
            h_fold,
        );
        let merged_plus_rest = self.add(merged_e.clone(), rest_e.clone());
        let proof = self.trans(lhs, assoc_lhs, merged_plus_rest, h_assoc, c_fold);
        let mut out = merged_terms;
        out.extend(rest.to_vec());
        (out, proof)
    }

    /// `t.mono < head.mono`: `head` stays in front; recurse into `rest`.
    fn insert_deeper(
        &self,
        parent: &EnvDeclBuilder,
        t: &STerm,
        head: &STerm,
        rest: &[STerm],
    ) -> (Vec<STerm>, Expr) {
        let t_e = self.reify_term(t.coeff, &t.mono);
        let head_e = self.reify_term(head.coeff, &head.mono);
        let add_c = self.add_const();

        if rest.is_empty() {
            // sorted == [head] → reify = head_e. lhs = t + head_e.
            // t + head_e = head_e + t  [add_comm]  → [head, t]
            let lhs = self.add(t_e.clone(), head_e.clone());
            let h = self.acomm(t_e.clone(), head_e.clone());
            let out = vec![head.clone(), t.clone()];
            // reify([head, t]) = head_e + t_e
            return (out, h);
        }
        // sorted = head :: rest → reify = head_e + rest_e.
        let rest_e = self.reify_sterms(rest);
        let lhs = self.add(t_e.clone(), self.add(head_e.clone(), rest_e.clone()));
        // t + (head + rest) = (t + head) + rest   [symm add_assoc]
        let t_head = self.add(t_e.clone(), head_e.clone());
        let assoc = self.aassoc_eng(t_e.clone(), head_e.clone(), rest_e.clone());
        let assoc_lhs = self.add(t_head.clone(), rest_e.clone());
        let h_assoc = self.symm(assoc_lhs.clone(), lhs.clone(), assoc);
        // (t + head) = (head + t)  [add_comm] ; lift under (· + rest)
        let head_t = self.add(head_e.clone(), t_e.clone());
        let h_comm = self.acomm(t_e.clone(), head_e.clone());
        let c_comm = self.cong_left(
            parent,
            &add_c,
            t_head.clone(),
            head_t.clone(),
            rest_e.clone(),
            h_comm,
        );
        let headt_rest = self.add(head_t.clone(), rest_e.clone());
        // (head + t) + rest = head + (t + rest)   [add_assoc]
        let t_rest = self.add(t_e.clone(), rest_e.clone());
        let h_assoc2 = self.aassoc_eng(head_e.clone(), t_e.clone(), rest_e.clone());
        let head_trest = self.add(head_e.clone(), t_rest.clone());
        // recurse: insert t into rest
        let (ins_terms, h_ins) = self.insert_term(parent, t, rest);
        let ins_e = self.reify_sterms(&ins_terms);
        // lift h_ins (t + rest = ins_e) under (head + ·)
        let c_ins = self.cong_right(
            parent,
            &add_c,
            t_rest.clone(),
            ins_e.clone(),
            head_e.clone(),
            h_ins,
        );
        let head_ins = self.add(head_e.clone(), ins_e.clone());
        // chain: lhs → assoc_lhs → headt_rest → head_trest → head_ins
        let s = self.trans(
            lhs.clone(),
            assoc_lhs.clone(),
            headt_rest.clone(),
            h_assoc,
            c_comm,
        );
        let s = self.trans(lhs.clone(), headt_rest, head_trest.clone(), s, h_assoc2);
        let proof = self.trans(lhs, head_trest, head_ins, s, c_ins);
        let mut out = vec![head.clone()];
        out.extend(ins_terms);
        (out, proof)
    }

    /// Fold two terms with the SAME monomial (any signs).
    /// Returns `(result_terms, proof : reify_term(t1) + reify_term(t2) = reify(result_terms))`,
    /// where `result_terms` is `[]` (sum 0) or a single term.
    fn fold_pair(&self, parent: &EnvDeclBuilder, t1: &STerm, t2: &STerm) -> (Vec<STerm>, Expr) {
        debug_assert_eq!(t1.mono, t2.mono);
        let m = &t1.mono;
        let c1 = t1.coeff;
        let c2 = t2.coeff;
        let sum = c1 + c2;
        let t1_e = self.reify_term(c1, m);
        let t2_e = self.reify_term(c2, m);
        let lhs = self.add(t1_e.clone(), t2_e.clone());

        if sum == 0 {
            // c1 = +k, c2 = −k (or vice versa). reify gives (P) + (neg P) or
            // (neg P) + P → add_neg_self / add_left_neg.
            if c1 > 0 {
                // (k·m) + neg(k·m) = 0   [add_neg_self (k·m)]
                let p = self.reify_pos_term(c1 as u32, m);
                let h = Expr::app(self.add_neg_self.clone(), p);
                return (Vec::new(), h);
            } else {
                // neg(k·m) + (k·m) = 0   [add_left_neg (k·m)]
                let p = self.reify_pos_term(c2 as u32, m);
                let h = Expr::app(
                    Expr::const_(crate::name::Name::from_string("Rat.add_left_neg"), vec![]),
                    p,
                );
                return (Vec::new(), h);
            }
        }
        // both same sign?
        if (c1 > 0) == (c2 > 0) {
            let positive = c1 > 0;
            let a = c1.unsigned_abs() as u32;
            let b = c2.unsigned_abs() as u32;
            let h = self.fold_same_sign(parent, positive, a, b, m);
            return (
                vec![STerm {
                    coeff: sum,
                    mono: m.clone(),
                }],
                h,
            );
        }
        // opposite signs, nonzero sum: cancellation.
        let (h, result) = self.fold_opposite(parent, c1, c2, m);
        let _ = lhs;
        (vec![result], h)
    }

    /// `aassoc` for the engine module.
    fn aassoc_eng(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        self.c.aassoc(a, b, cc)
    }

    /// Push negation over a right-nested sum:
    /// `neg(reify(terms)) = reify(neg-each terms)`.
    pub(super) fn push_neg(&self, parent: &EnvDeclBuilder, terms: &[STerm]) -> Expr {
        self.push_neg_sterms(parent, terms)
    }

    fn push_neg_sterms(&self, parent: &EnvDeclBuilder, terms: &[STerm]) -> Expr {
        if terms.is_empty() {
            // neg 0 = 0
            return self.neg_zero_eq();
        }
        if terms.len() == 1 {
            // neg(reify_term(c,m)) = reify_term(-c,m)
            return self.neg_term(&terms[0]);
        }
        let head = &terms[0];
        let rest = &terms[1..];
        let head_e = self.reify_term(head.coeff, &head.mono);
        let rest_e = self.reify_sterms(rest);
        let sum_e = self.add(head_e.clone(), rest_e.clone());
        // neg(head + rest) = neg head + neg rest   [neg_add_distrib]
        let h_dist = self.neg_add_distrib(parent, &head_e, &rest_e);
        let nh = self.neg(head_e.clone());
        let nr = self.neg(rest_e.clone());
        let nh_nr = self.add(nh.clone(), nr.clone());
        // neg head = reify_term(-head)
        let h_head = self.neg_term(head);
        let neg_head_term = self.reify_term(-head.coeff, &head.mono);
        // neg rest = reify(neg rest)
        let h_rest = self.push_neg_sterms(parent, rest);
        let neg_rest_e = self.reify_sterms(&Self::neg_sterms(rest));
        let add_c = self.add_const();
        // (neg head + neg rest) = (reify_term(-head) + neg rest)
        let c1 = self.cong_left(
            parent,
            &add_c,
            nh.clone(),
            neg_head_term.clone(),
            nr.clone(),
            h_head,
        );
        let mid1 = self.add(neg_head_term.clone(), nr.clone());
        // (reify_term(-head) + neg rest) = (reify_term(-head) + neg_rest_e)
        let c2 = self.cong_right(
            parent,
            &add_c,
            nr.clone(),
            neg_rest_e.clone(),
            neg_head_term.clone(),
            h_rest,
        );
        let final_e = self.add(neg_head_term.clone(), neg_rest_e.clone());
        // chain: neg(head+rest) = nh_nr = mid1 = final_e
        let neg_lhs = self.neg(sum_e.clone());
        let s = self.trans(neg_lhs.clone(), nh_nr.clone(), mid1.clone(), h_dist, c1);
        self.trans(neg_lhs, mid1, final_e, s, c2)
    }

    fn neg_sterms(terms: &[STerm]) -> Vec<STerm> {
        terms
            .iter()
            .map(|t| STerm {
                coeff: -t.coeff,
                mono: t.mono.clone(),
            })
            .collect()
    }

    /// `neg(reify_term(c,m)) = reify_term(-c,m)`.
    fn neg_term(&self, t: &STerm) -> Expr {
        let m = &t.mono;
        let c = t.coeff;
        if c > 0 {
            // reify_term(c,m) = P (positive). neg P = reify_term(-c,m) which is
            // exactly `neg P` → refl.
            let p = self.reify_pos_term(c as u32, m);
            let neg_p = self.neg(p);
            self.refl(neg_p)
        } else {
            // reify_term(c,m) = neg P. neg(neg P) = P = reify_term(-c,m) [neg_neg]
            let p = self.reify_pos_term((-c) as u32, m);
            let neg_p = self.neg(p.clone());
            let neg_neg_p = self.neg(neg_p);
            // Rat.neg_neg P : neg(neg P) = P
            let h = Expr::app(self.neg_neg.clone(), p.clone());
            let _ = neg_neg_p;
            h
        }
    }
}
