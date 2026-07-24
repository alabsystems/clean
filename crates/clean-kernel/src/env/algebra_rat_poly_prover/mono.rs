// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Monomial multiplication: `reify_mono(m1)·reify_mono(m2) = reify_mono(m1·m2)`.
//!
//! Atoms reify as a LEFT-nested product `((x·y)·z)`. We concatenate the two
//! atom sequences (`P(s1)·P(s2) = P(s1 ++ s2)`, via `mul_assoc`) then
//! insertion-sort the concatenation into canonical ascending order (via
//! `mul_assoc`/`mul_comm` adjacent swaps lifted by `congrArg`). No coefficient
//! arithmetic — atoms never merge, they only reorder.

use super::{Monomial, RatPolyProver};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;
use crate::name::Name;

impl RatPolyProver {
    /// `reify_mono(m1) · reify_mono(m2) = reify_mono(m1·m2)`.
    pub(super) fn mono_mul(&self, parent: &EnvDeclBuilder, m1: &Monomial, m2: &Monomial) -> Expr {
        let s1 = self.mono_seq(m1);
        let s2 = self.mono_seq(m2);
        let p1 = self.reify_seq(&s1);
        let p2 = self.reify_seq(&s2);
        let lhs = self.mul(p1.clone(), p2.clone());

        // Handle the constant-monomial edge cases (reify_seq([]) == Rat.one).
        if s1.is_empty() {
            // 1 · P(s2) = P(s2) = reify_mono(m1·m2) (since m1·m2 == m2).
            return self.c.one_mul(p2);
        }
        if s2.is_empty() {
            // P(s1) · 1 = P(s1)   [mul_one]
            let mul_one = Expr::const_(Name::from_string("Rat.mul_one"), vec![]);
            return Expr::app(mul_one, p1);
        }

        // Step 1: concat  P(s1)·P(s2) = P(s1 ++ s2).
        let (concat_expr, h_concat) = self.concat_prod(parent, &s1, &s2);
        let mut concat: Vec<usize> = s1.clone();
        concat.extend(s2.clone());
        debug_assert_eq!(concat_expr, self.reify_seq(&concat));

        // Step 2: sort P(s1 ++ s2) into canonical order.
        let (sorted, h_sort) = self.sort_prod(parent, &concat);
        let sorted_expr = self.reify_seq(&sorted);
        debug_assert_eq!(sorted, self.mono_seq(&m1.mul(m2)));

        self.trans(lhs, concat_expr, sorted_expr, h_concat, h_sort)
    }

    /// `P(s1)·P(s2) = P(s1 ++ s2)` (left-nested), peeling s2 from the right.
    /// `P(s2) = P(s2_init)·x_last`, so `P(s1)·(P(s2_init)·x_last) =
    /// (P(s1)·P(s2_init))·x_last` [symm mul_assoc], recurse, then `·x_last`.
    fn concat_prod(&self, parent: &EnvDeclBuilder, s1: &[usize], s2: &[usize]) -> (Expr, Expr) {
        let p1 = self.reify_seq(s1);
        if s2.is_empty() {
            // P(s1)·1 = P(s1) — but callers guard s2 nonempty; keep for safety.
            let mul_one = Expr::const_(Name::from_string("Rat.mul_one"), vec![]);
            return (p1.clone(), Expr::app(mul_one, p1));
        }
        if s2.len() == 1 {
            // P(s1)·x = P(s1 ++ [x])   (left-nested: this IS the concat). refl.
            let x = self.vars[s2[0]].clone();
            let prod = self.mul(p1.clone(), x);
            return (prod.clone(), self.refl(prod));
        }
        let last = *s2.last().expect("nonempty");
        let s2_init = &s2[..s2.len() - 1];
        let p2_init = self.reify_seq(s2_init);
        let x_last = self.vars[last].clone();
        let p2 = self.reify_seq(s2);
        let lhs = self.mul(p1.clone(), p2.clone());
        // P(s2) == P(s2_init)·x_last, so lhs == p1·(p2_init·x_last).
        // symm mul_assoc p1 p2_init x_last : p1·(p2_init·x_last) = (p1·p2_init)·x_last
        let assoc = self.c.massoc(p1.clone(), p2_init.clone(), x_last.clone());
        let regrouped = self.mul(self.mul(p1.clone(), p2_init.clone()), x_last.clone());
        let h_assoc = self.symm(regrouped.clone(), lhs.clone(), assoc);
        // recurse: P(s1)·P(s2_init) = P(s1 ++ s2_init)
        let (rest_expr, h_rest) = self.concat_prod(parent, s1, s2_init);
        // lift under (· x_last)
        let mul_c = self.mul_const();
        let cong = self.cong_left(
            parent,
            &mul_c,
            self.mul(p1.clone(), p2_init.clone()),
            rest_expr.clone(),
            x_last.clone(),
            h_rest,
        );
        let result = self.mul(rest_expr, x_last);
        let h = self.trans(lhs, regrouped, result.clone(), h_assoc, cong);
        (result, h)
    }

    /// Insertion-sort a left-nested product `P(seq)` into ascending order.
    /// Returns `(sorted, proof : P(seq) = P(sorted))`.
    fn sort_prod(&self, parent: &EnvDeclBuilder, seq: &[usize]) -> (Vec<usize>, Expr) {
        if seq.len() <= 1 {
            let e = self.reify_seq(seq);
            return (seq.to_vec(), self.refl(e));
        }
        let last = *seq.last().expect("nonempty");
        let init = &seq[..seq.len() - 1];
        // P(seq) = P(init)·x_last.
        let (sorted_init, h_init) = self.sort_prod(parent, init);
        let p_init = self.reify_seq(init);
        let p_sorted_init = self.reify_seq(&sorted_init);
        let x_last = self.vars[last].clone();
        // lift h_init under (· x_last): P(init)·x = P(sorted_init)·x
        let mul_c = self.mul_const();
        let c0 = self.cong_left(
            parent,
            &mul_c,
            p_init.clone(),
            p_sorted_init.clone(),
            x_last.clone(),
            h_init,
        );
        let lhs = self.mul(p_init.clone(), x_last.clone());
        let mid = self.mul(p_sorted_init.clone(), x_last.clone());
        // insert x_last into sorted_init
        let (final_seq, h_ins) = self.insert_atom(parent, &sorted_init, last);
        let final_expr = self.reify_seq(&final_seq);
        let proof = self.trans(lhs, mid, final_expr, c0, h_ins);
        (final_seq, proof)
    }

    /// Insert atom `k` (outermost) into a sorted left-nested product `P(sorted)`.
    /// Proves `P(sorted)·x_k = P(insert k)`.
    fn insert_atom(
        &self,
        parent: &EnvDeclBuilder,
        sorted: &[usize],
        k: usize,
    ) -> (Vec<usize>, Expr) {
        let p_sorted = self.reify_seq(sorted);
        let x_k = self.vars[k].clone();
        let lhs = self.mul(p_sorted.clone(), x_k.clone());
        if sorted.is_empty() {
            // P([])·x_k = 1·x_k = x_k   [one_mul]
            return (vec![k], self.c.one_mul(x_k));
        }
        let j = *sorted.last().expect("nonempty");
        if k >= j {
            // already in order: P(sorted)·x_k == P(sorted ++ [k]). refl.
            let mut out = sorted.to_vec();
            out.push(k);
            return (out, self.refl(lhs));
        }
        // k < j: swap. When `sorted == [j]` (single), `P(sorted) == x_j` (no
        // `1·`), so `P(sorted)·x_k = x_j·x_k = x_k·x_j` [mul_comm] → `[k, j]`.
        if sorted.len() == 1 {
            let x_j = self.vars[j].clone();
            let h = self.c.mcomm(x_j.clone(), x_k.clone()); // x_j·x_k = x_k·x_j
            return (vec![k, j], h);
        }
        // sorted = sorted_init ++ [j] (sorted_init nonempty), P(sorted) = P(sorted_init)·x_j.
        let sorted_init = &sorted[..sorted.len() - 1];
        let p_init = self.reify_seq(sorted_init);
        let x_j = self.vars[j].clone();
        // (P_init·x_j)·x_k = P_init·(x_j·x_k)  [mul_assoc]
        let assoc1 = self.c.massoc(p_init.clone(), x_j.clone(), x_k.clone());
        let xj_xk = self.mul(x_j.clone(), x_k.clone());
        let e1 = self.mul(p_init.clone(), xj_xk.clone());
        // x_j·x_k = x_k·x_j  [mul_comm] ; lift under (P_init · ·)
        let xk_xj = self.mul(x_k.clone(), x_j.clone());
        let h_comm = self.c.mcomm(x_j.clone(), x_k.clone());
        let mul_c = self.mul_const();
        let c_comm = self.cong_right(
            parent,
            &mul_c,
            xj_xk.clone(),
            xk_xj.clone(),
            p_init.clone(),
            h_comm,
        );
        let e2 = self.mul(p_init.clone(), xk_xj.clone());
        // P_init·(x_k·x_j) = (P_init·x_k)·x_j  [symm mul_assoc]
        let assoc2 = self.c.massoc(p_init.clone(), x_k.clone(), x_j.clone());
        let regrouped = self.mul(self.mul(p_init.clone(), x_k.clone()), x_j.clone());
        let h_assoc2 = self.symm(regrouped.clone(), e2.clone(), assoc2);
        // recurse: insert k into sorted_init  →  (P_init·x_k = P(insert))
        let (ins_seq, h_ins) = self.insert_atom(parent, sorted_init, k);
        let ins_expr = self.reify_seq(&ins_seq);
        // lift under (· x_j)
        let c_ins = self.cong_left(
            parent,
            &mul_c,
            self.mul(p_init.clone(), x_k.clone()),
            ins_expr.clone(),
            x_j.clone(),
            h_ins,
        );
        let final_expr = self.mul(ins_expr.clone(), x_j.clone());
        // chain: lhs = e1 = e2 = regrouped = final_expr
        let s = self.trans(lhs.clone(), e1.clone(), e2.clone(), assoc1, c_comm);
        let s = self.trans(lhs.clone(), e2, regrouped.clone(), s, h_assoc2);
        let proof = self.trans(lhs, regrouped, final_expr, s, c_ins);
        let mut out = ins_seq;
        out.push(j);
        (out, proof)
    }
}
