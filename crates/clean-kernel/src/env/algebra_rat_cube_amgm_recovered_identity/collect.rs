// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verified collection / distribution / negation-push proofs for the
//! polynomial normalizer. Each function returns a kernel-checkable `Eq` proof
//! that a materialized intermediate equals the canonical poly form, built from
//! pure `Rat` ring lemmas (`add_assoc/comm`, `right_distrib`, `mul_assoc/comm`,
//! `one_mul`, `mul_neg`, `neg_neg`, `add_neg_self`, `add_zero`, `zero_add`).
//! No axioms, no `sorry`.

use super::super::CubeAmGmConstsRecovered;
use super::Mono;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;
use crate::name::Name;
use std::collections::BTreeMap;

/// Ordered list of (monomial, nonzero coeff), in canonical `BTreeMap` order.
pub(super) type TermList = Vec<(Mono, i64)>;

/// `pub(super)` view of the Rust-side single-term insert (for distrib).
pub(super) fn insert_one_pub(t: &(Mono, i64), list: &TermList) -> TermList {
    insert_one(t, list)
}

/// Prove `list_expr(a) + list_expr(b) = list_expr(merge(a,b))` (TermList view).
pub(super) fn prove_add_collect_list(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    a: &TermList,
    b: &TermList,
    p: &Expr,
    q: &Expr,
) -> Expr {
    add_poly(c, parent, a, b, p, q)
}

fn to_list(poly: &BTreeMap<Mono, i64>) -> TermList {
    poly.iter().map(|(m, &c)| (m.clone(), c)).collect()
}

impl CubeAmGmConstsRecovered {
    fn zero_add_lemma(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.zero_add"), vec![]),
            a.clone(),
        )
    }
    fn add_zero_lemma(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            a.clone(),
        )
    }

    /// `pub(super)` view for distrib.
    pub(super) fn list_expr_pub(&self, list: &TermList, p: &Expr, q: &Expr) -> Expr {
        self.list_expr(list, p, q)
    }
    /// `pub(super)` view for distrib.
    pub(super) fn term_of_pub(&self, t: &(Mono, i64), p: &Expr, q: &Expr) -> Expr {
        self.term_of(t, p, q)
    }

    /// Materialize the right-nested sum of a term list. Empty → `0`.
    fn list_expr(&self, list: &TermList, p: &Expr, q: &Expr) -> Expr {
        if list.is_empty() {
            return self.zero();
        }
        let term = |t: &(Mono, i64)| {
            let m = self.mono_expr_pub(&t.0, p, q);
            if t.0.is_empty() {
                // constant term
                self.const_term(t.1)
            } else {
                self.term_with(&m, t.1)
            }
        };
        let mut it = list.iter().rev();
        let mut acc = term(it.next().expect("nonempty"));
        for t in it {
            acc = self.add(term(t), acc);
        }
        acc
    }

    /// The constant term materialization (empty monomial), matching `term_expr`.
    fn const_term(&self, coeff: i64) -> Expr {
        debug_assert!(coeff != 0);
        let mag = coeff.unsigned_abs() as usize;
        let pos = self.nat_lit(mag);
        if coeff < 0 {
            self.neg(pos)
        } else {
            pos
        }
    }

    /// One materialized term for a list entry.
    fn term_of(&self, t: &(Mono, i64), p: &Expr, q: &Expr) -> Expr {
        if t.0.is_empty() {
            self.const_term(t.1)
        } else {
            let m = self.mono_expr_pub(&t.0, p, q);
            self.term_with(&m, t.1)
        }
    }
}

// ── add-collect ───────────────────────────────────────────────────────────

pub(super) fn prove_add_collect(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    a: &BTreeMap<Mono, i64>,
    b: &BTreeMap<Mono, i64>,
    out: &BTreeMap<Mono, i64>,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let a_list = to_list(a);
    let b_list = to_list(b);
    let out_list = to_list(out);
    debug_assert_eq!(merge_lists(&a_list, &b_list), out_list);
    add_poly(c, parent, &a_list, &b_list, p, q)
}

/// Prove `list_expr(a) + list_expr(b) = list_expr(merge(a,b))`.
fn add_poly(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    a: &TermList,
    b: &TermList,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let a_expr = c.list_expr(a, p, q);
    let b_expr = c.list_expr(b, p, q);
    let lhs = c.add(a_expr.clone(), b_expr.clone());

    if a.is_empty() {
        // 0 + B = B
        return c.zero_add_lemma(&b_expr);
    }
    if a.len() == 1 {
        // term(a0) + B = insert(a0, B)
        return insert_term(c, parent, &a[0], b, p, q);
    }
    // a = a0 :: rest  (len ≥ 2): a_expr = term(a0) + list_expr(rest).
    let a0 = &a[0];
    let rest: TermList = a[1..].to_vec();
    let t0 = c.term_of(a0, p, q);
    let rest_expr = c.list_expr(&rest, p, q);
    // lhs = (t0 + rest_expr) + B = t0 + (rest_expr + B)   [add_assoc]
    let assoc = c.aassoc(t0.clone(), rest_expr.clone(), b_expr.clone());
    let t0_rest_b = c.add(t0.clone(), c.add(rest_expr.clone(), b_expr.clone()));
    // recurse: rest_expr + B = list_expr(merge(rest,b))
    let merged_rest = merge_lists(&rest, b);
    let merged_rest_expr = c.list_expr(&merged_rest, p, q);
    let inner = add_poly(c, parent, &rest, b, p, q);
    let add_c = c.add_op();
    let cong = c.cong_r(
        parent,
        &add_c,
        c.add(rest_expr.clone(), b_expr.clone()),
        merged_rest_expr.clone(),
        t0.clone(),
        inner,
    );
    let t0_merged = c.add(t0.clone(), merged_rest_expr.clone());
    // now insert t0 into merged_rest
    let ins = insert_term(c, parent, a0, &merged_rest, p, q);
    let out_list = merge_lists(a, b);
    let out_expr = c.list_expr(&out_list, p, q);
    // chain: lhs = t0_rest_b (assoc) = t0_merged (cong) = out_expr (ins)
    let s1 = c.trans(
        lhs.clone(),
        t0_rest_b.clone(),
        t0_merged.clone(),
        assoc,
        cong,
    );
    c.trans(lhs, t0_merged, out_expr, s1, ins)
}

/// Prove `term_of(t) + list_expr(list) = list_expr(insert(t, list))`.
fn insert_term(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    t: &(Mono, i64),
    list: &TermList,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let t_expr = c.term_of(t, p, q);
    let list_expr = c.list_expr(list, p, q);
    let lhs = c.add(t_expr.clone(), list_expr.clone());

    if list.is_empty() {
        // term(t) + 0 = term(t)
        return c.add_zero_lemma(&t_expr);
    }

    let h0 = &list[0];
    let cmp = t.0.cmp(&h0.0);

    if list.len() == 1 {
        match cmp {
            std::cmp::Ordering::Less => {
                // already canonical: term(t)+term(h0) = list_expr([t,h0])
                c.refl(lhs)
            }
            std::cmp::Ordering::Equal => {
                // coeff merge (sum guaranteed nonzero in our runs; if zero, → 0)
                let sum = t.1 + h0.1;
                let m = c.mono_expr_pub(&t.0, p, q);
                if sum == 0 {
                    // term(t) + term(h0) = 0  — not expected; surface.
                    panic!("insert_term: coeff cancels to 0 for mono {:?}", t.0);
                }
                if t.0.is_empty() {
                    // constant merge: refl (syntactic) handled by numeral identity
                    prove_const_merge(c, parent, t.1, h0.1)
                } else {
                    c.coeff_merge(parent, &m, t.1, h0.1)
                }
            }
            std::cmp::Ordering::Greater => {
                // term(t) + term(h0) = term(h0) + term(t)   [add_comm]
                let h0e = c.term_of(h0, p, q);
                c.acomm(t_expr.clone(), h0e)
            }
        }
    } else {
        // list = h0 :: tail
        let tail: TermList = list[1..].to_vec();
        let h0e = c.term_of(h0, p, q);
        let tail_expr = c.list_expr(&tail, p, q);
        // list_expr = h0e + tail_expr  (definitional, since len≥2)
        match cmp {
            std::cmp::Ordering::Less => {
                // term(t) + (h0e + tail_expr) is already canonical
                c.refl(lhs)
            }
            std::cmp::Ordering::Equal => {
                let sum = t.1 + h0.1;
                // (t + (h0 + tail)) = ((t+h0) + tail)   [symm add_assoc]
                let assoc = c.aassoc(t_expr.clone(), h0e.clone(), tail_expr.clone());
                let t_h0_tail = c.add(c.add(t_expr.clone(), h0e.clone()), tail_expr.clone());
                let s_assoc = c.symm(t_h0_tail.clone(), lhs.clone(), assoc);
                let add_c = c.add_op();
                if sum == 0 {
                    // (t+h0) = 0, then 0 + tail = tail
                    let m = c.mono_expr_pub(&t.0, p, q);
                    let cancel = if t.0.is_empty() {
                        panic!("insert_term: const cancels to 0");
                    } else {
                        c.coeff_cancel(parent, &m, t.1, h0.1)
                    };
                    let zero_plus_tail = c.add(c.zero(), tail_expr.clone());
                    let cong = c.cong_l(
                        parent,
                        &add_c,
                        c.add(t_expr.clone(), h0e.clone()),
                        c.zero(),
                        tail_expr.clone(),
                        cancel,
                    );
                    let s_cong = c.trans(
                        t_h0_tail.clone(),
                        zero_plus_tail.clone(),
                        tail_expr.clone(),
                        cong,
                        c.zero_add_lemma(&tail_expr),
                    );
                    return c.trans(lhs, t_h0_tail, tail_expr, s_assoc, s_cong);
                }
                let merge = if t.0.is_empty() {
                    prove_const_merge(c, parent, t.1, h0.1)
                } else {
                    let m = c.mono_expr_pub(&t.0, p, q);
                    c.coeff_merge(parent, &m, t.1, h0.1)
                };
                let merged_term = c.term_of(&(t.0.clone(), sum), p, q);
                let cong = c.cong_l(
                    parent,
                    &add_c,
                    c.add(t_expr.clone(), h0e.clone()),
                    merged_term.clone(),
                    tail_expr.clone(),
                    merge,
                );
                let out_expr = c.add(merged_term, tail_expr);
                c.trans(lhs, t_h0_tail, out_expr, s_assoc, cong)
            }
            std::cmp::Ordering::Greater => {
                // t + (h0 + tail) = (t+h0)+tail [symm assoc] = (h0+t)+tail [cong_l comm]
                //   = h0 + (t+tail) [assoc] = h0 + insert(t,tail) [cong_r recurse]
                let assoc = c.aassoc(t_expr.clone(), h0e.clone(), tail_expr.clone());
                let t_h0_tail = c.add(c.add(t_expr.clone(), h0e.clone()), tail_expr.clone());
                let s_assoc = c.symm(t_h0_tail.clone(), lhs.clone(), assoc);
                let add_c = c.add_op();
                // (t+h0) → (h0+t)
                let comm = c.acomm(t_expr.clone(), h0e.clone());
                let h0_t = c.add(h0e.clone(), t_expr.clone());
                let cong_comm = c.cong_l(
                    parent,
                    &add_c,
                    c.add(t_expr.clone(), h0e.clone()),
                    h0_t.clone(),
                    tail_expr.clone(),
                    comm,
                );
                let h0t_tail = c.add(h0_t.clone(), tail_expr.clone());
                // (h0+t)+tail = h0 + (t+tail)  [add_assoc]
                let assoc2 = c.aassoc(h0e.clone(), t_expr.clone(), tail_expr.clone());
                let h0_t_tail = c.add(h0e.clone(), c.add(t_expr.clone(), tail_expr.clone()));
                // recurse: t + tail = insert(t, tail)
                let inner = insert_term(c, parent, t, &tail, p, q);
                let inserted = insert_one(t, &tail);
                let inserted_expr = c.list_expr(&inserted, p, q);
                let cong_rec = c.cong_r(
                    parent,
                    &add_c,
                    c.add(t_expr.clone(), tail_expr.clone()),
                    inserted_expr.clone(),
                    h0e.clone(),
                    inner,
                );
                let h0_inserted = c.add(h0e.clone(), inserted_expr.clone());
                // chain
                let s1 = c.trans(
                    lhs.clone(),
                    t_h0_tail.clone(),
                    h0t_tail.clone(),
                    s_assoc,
                    cong_comm,
                );
                let s2 = c.trans(lhs.clone(), h0t_tail.clone(), h0_t_tail.clone(), s1, assoc2);
                c.trans(lhs, h0_t_tail, h0_inserted, s2, cong_rec)
            }
        }
    }
}

/// Constant-term merge `const_term(i) + const_term(j) = const_term(i+j)`,
/// positive only (the only constant merges in RID are `n + 1`).
fn prove_const_merge(c: &CubeAmGmConstsRecovered, parent: &EnvDeclBuilder, i: i64, j: i64) -> Expr {
    assert!(i > 0 && j > 0, "const merge only positive: {i}+{j}");
    // const_term(i) = nat_lit(i), const_term(j)=nat_lit(j); nat_lit(i)+nat_lit(j) = nat_lit(i+j).
    c.numeral_add(parent, i as usize, j as usize)
}

// ── neg-push ──────────────────────────────────────────────────────────────

pub(super) fn prove_neg_push(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    a: &BTreeMap<Mono, i64>,
    out: &BTreeMap<Mono, i64>,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let a_list = to_list(a);
    let out_list = to_list(out);
    let _ = &out_list;
    neg_push_list(c, parent, &a_list, p, q)
}

/// Prove `-(list_expr(a)) = list_expr(neg(a))`.
fn neg_push_list(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    a: &TermList,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let a_expr = c.list_expr(a, p, q);
    let lhs = c.neg(a_expr.clone());
    if a.is_empty() {
        // -(0) = 0 ; out is empty → 0. Rat.neg_zero.
        return Expr::app(
            Expr::const_(Name::from_string("Rat.neg_zero"), vec![]),
            c.zero(),
        );
    }
    if a.len() == 1 {
        // -(term(a0)) = term(neg a0)
        return neg_term(c, parent, &a[0], p, q);
    }
    // a = a0 :: rest : a_expr = term(a0) + rest_expr.
    let a0 = &a[0];
    let rest: TermList = a[1..].to_vec();
    let t0 = c.term_of(a0, p, q);
    let rest_expr = c.list_expr(&rest, p, q);
    // -(t0 + rest_expr) = (-t0) + (-rest_expr)   [neg_add — derive]
    let neg_add = c.neg_add(parent, &t0, &rest_expr);
    let neg_t0 = c.neg(t0.clone());
    let neg_rest = c.neg(rest_expr.clone());
    let split = c.add(neg_t0.clone(), neg_rest.clone());
    let add_c = c.add_op();
    // -t0 = term(neg a0)
    let e_t0 = neg_term(c, parent, a0, p, q);
    let neg_a0_term = c.term_of(&(a0.0.clone(), -a0.1), p, q);
    let c1 = c.cong_l(
        parent,
        &add_c,
        neg_t0.clone(),
        neg_a0_term.clone(),
        neg_rest.clone(),
        e_t0,
    );
    let mid1 = c.add(neg_a0_term.clone(), neg_rest.clone());
    // -rest_expr = list_expr(neg rest)
    let e_rest = neg_push_list(c, parent, &rest, p, q);
    let neg_rest_list: TermList = rest.iter().map(|(m, cc)| (m.clone(), -cc)).collect();
    let neg_rest_expr = c.list_expr(&neg_rest_list, p, q);
    let c2 = c.cong_r(
        parent,
        &add_c,
        neg_rest.clone(),
        neg_rest_expr.clone(),
        neg_a0_term.clone(),
        e_rest,
    );
    let out_expr = c.add(neg_a0_term, neg_rest_expr);
    let s1 = c.trans(lhs.clone(), split.clone(), mid1.clone(), neg_add, c1);
    c.trans(lhs, mid1, out_expr, s1, c2)
}

/// `-(term_of(t)) = term_of(neg t)`.
fn neg_term(
    c: &CubeAmGmConstsRecovered,
    _parent: &EnvDeclBuilder,
    t: &(Mono, i64),
    p: &Expr,
    q: &Expr,
) -> Expr {
    let te = c.term_of(t, p, q);
    let lhs = c.neg(te.clone());
    let neg_t = c.term_of(&(t.0.clone(), -t.1), p, q);
    if t.1 > 0 {
        // term(t) is the positive form; -(pos) is exactly term_of(neg t) (which neg-wraps). refl.
        c.refl(lhs)
    } else {
        // t.1 < 0 : te = -(pos), so lhs = -(-(pos)) ; term_of(neg t) = pos. neg_neg.
        let _ = neg_t;
        // pos := term_of(|t|)
        let pos = c.term_of(&(t.0.clone(), -t.1), p, q);
        c.neg_neg(&pos)
    }
}

impl CubeAmGmConstsRecovered {
    /// `term(i) + term(j) = 0` for a cancelling pair (`i+j=0`), nonempty mono.
    fn coeff_cancel(&self, parent: &EnvDeclBuilder, m: &Expr, i: i64, j: i64) -> Expr {
        debug_assert_eq!(i + j, 0);
        // WLOG i>0, j=-i : (i·M) + (-(i·M)) = 0  [add_neg_self], modulo term_with shapes.
        let ti = self.term_with(m, i);
        let tj = self.term_with(m, j);
        let _lhs = self.add(ti.clone(), tj.clone());
        if i > 0 {
            // ti = pos(i), tj = -(pos(i)). add_neg_self pos(i).
            let pos = self.term_with(m, i);
            let ans = Expr::app(
                Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]),
                pos.clone(),
            );
            // lhs is literally pos + (-pos) = add_neg_self target.
            let _ = (parent, tj);
            ans
        } else {
            // ti = -(pos(|i|)), tj = pos(|i|). add_left_neg pos.
            let pos = self.term_with(m, -i);
            Expr::app(
                Expr::const_(Name::from_string("Rat.add_left_neg"), vec![]),
                pos,
            )
        }
    }
}

// ── ordered-list merge / insert (Rust side, mirrors the proof structure) ──

fn insert_one(t: &(Mono, i64), list: &TermList) -> TermList {
    let mut out = Vec::new();
    let mut placed = false;
    for h in list {
        if !placed {
            match t.0.cmp(&h.0) {
                std::cmp::Ordering::Less => {
                    out.push(t.clone());
                    placed = true;
                    out.push(h.clone());
                }
                std::cmp::Ordering::Equal => {
                    let s = t.1 + h.1;
                    if s != 0 {
                        out.push((t.0.clone(), s));
                    }
                    placed = true;
                }
                std::cmp::Ordering::Greater => out.push(h.clone()),
            }
        } else {
            out.push(h.clone());
        }
    }
    if !placed {
        out.push(t.clone());
    }
    out
}

fn merge_lists(a: &TermList, b: &TermList) -> TermList {
    let mut acc = b.clone();
    for t in a.iter().rev() {
        acc = insert_one(t, &acc);
    }
    acc
}

// ── mul-distrib ───────────────────────────────────────────────────────────

#[path = "collect/distrib.rs"]
mod distrib;
pub(super) use distrib::prove_mul_distrib;
