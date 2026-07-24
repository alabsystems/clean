// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verified polynomial product `poly_expr(a) · poly_expr(b) = poly_expr(out)`.
//!
//! Distributes via `left/right_distrib` into the sum of all term-products
//! `ai·bj`, normalizes each term-product to its canonical `(ca·cb)·(Ma⊎Mb)`
//! monomial form, then collects them with the add-collect engine. Pure `Rat`
//! ring lemmas throughout.

use super::super::super::CubeAmGmConstsRecovered;
use super::super::Mono;
use super::{merge_lists, prove_add_collect_list, TermList};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;
use std::collections::BTreeMap;

pub(in super::super) fn prove_mul_distrib(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    a: &BTreeMap<Mono, i64>,
    b: &BTreeMap<Mono, i64>,
    _out: &BTreeMap<Mono, i64>,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let a_list: TermList = a.iter().map(|(m, &cc)| (m.clone(), cc)).collect();
    let b_list: TermList = b.iter().map(|(m, &cc)| (m.clone(), cc)).collect();
    mul_poly(c, parent, &a_list, &b_list, p, q)
}

/// Prove `list_expr(a) · list_expr(b) = list_expr(canonical product)`.
fn mul_poly(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    a: &TermList,
    b: &TermList,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let a_expr = c.list_expr_pub(a, p, q);
    let b_expr = c.list_expr_pub(b, p, q);
    let lhs = c.mul(a_expr.clone(), b_expr.clone());

    if a.len() == 1 {
        // single term · B
        return term_mul_poly(c, parent, &a[0], b, p, q);
    }
    // a = a0 :: rest : a_expr = term(a0) + rest_expr.
    let a0 = &a[0];
    let rest: TermList = a[1..].to_vec();
    let t0 = c.term_of_pub(a0, p, q);
    let rest_expr = c.list_expr_pub(&rest, p, q);
    // (t0 + rest_expr) · B = t0·B + rest_expr·B   [right_distrib]
    let rdist = c.rdist(t0.clone(), rest_expr.clone(), b_expr.clone());
    let t0b = c.mul(t0.clone(), b_expr.clone());
    let restb = c.mul(rest_expr.clone(), b_expr.clone());
    let sum = c.add(t0b.clone(), restb.clone());
    let add_c = c.add_op();
    // t0·B = list_expr(prod0)
    let prod0 = term_times_list(a0, b);
    let prod0_expr = c.list_expr_pub(&prod0, p, q);
    let e_t0b = term_mul_poly(c, parent, a0, b, p, q);
    let c1 = c.cong_l(
        parent,
        &add_c,
        t0b.clone(),
        prod0_expr.clone(),
        restb.clone(),
        e_t0b,
    );
    let mid = c.add(prod0_expr.clone(), restb.clone());
    // rest_expr·B = list_expr(prodRest)
    let prod_rest = list_times_list(&rest, b);
    let prod_rest_expr = c.list_expr_pub(&prod_rest, p, q);
    let e_restb = mul_poly(c, parent, &rest, b, p, q);
    let c2 = c.cong_r(
        parent,
        &add_c,
        restb.clone(),
        prod_rest_expr.clone(),
        prod0_expr.clone(),
        e_restb,
    );
    let two_sums = c.add(prod0_expr.clone(), prod_rest_expr.clone());
    // combine: prod0_expr + prod_rest_expr = list_expr(merge)
    let merged = merge_lists(&prod0, &prod_rest);
    let merged_expr = c.list_expr_pub(&merged, p, q);
    let combine = prove_add_collect_list(c, parent, &prod0, &prod_rest, p, q);
    // chain: lhs = sum (rdist) = mid (c1) = two_sums (c2) = merged_expr (combine)
    let s1 = c.trans(lhs.clone(), sum.clone(), mid.clone(), rdist, c1);
    let s2 = c.trans(lhs.clone(), mid, two_sums.clone(), s1, c2);
    c.trans(lhs, two_sums, merged_expr, s2, combine)
}

/// Prove `term_of(t) · list_expr(b) = list_expr(t·b)`.
fn term_mul_poly(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    t: &(Mono, i64),
    b: &TermList,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let t_expr = c.term_of_pub(t, p, q);
    let b_expr = c.list_expr_pub(b, p, q);
    let lhs = c.mul(t_expr.clone(), b_expr.clone());

    if b.len() == 1 {
        return term_mul_term(c, parent, t, &b[0], p, q);
    }
    // b = b0 :: rest : b_expr = term(b0) + rest_expr.
    let b0 = &b[0];
    let rest: TermList = b[1..].to_vec();
    let s0 = c.term_of_pub(b0, p, q);
    let rest_expr = c.list_expr_pub(&rest, p, q);
    // t·(s0 + rest_expr) = t·s0 + t·rest_expr   [left_distrib]
    let ldist = c.ldist(t_expr.clone(), s0.clone(), rest_expr.clone());
    let ts0 = c.mul(t_expr.clone(), s0.clone());
    let trest = c.mul(t_expr.clone(), rest_expr.clone());
    let sum = c.add(ts0.clone(), trest.clone());
    let add_c = c.add_op();
    // t·s0 = list_expr([t*b0])
    let prod0 = vec![term_mul(t, b0)];
    let prod0_expr = c.list_expr_pub(&prod0, p, q);
    let e_ts0 = term_mul_term(c, parent, t, b0, p, q);
    let c1 = c.cong_l(
        parent,
        &add_c,
        ts0.clone(),
        prod0_expr.clone(),
        trest.clone(),
        e_ts0,
    );
    let mid = c.add(prod0_expr.clone(), trest.clone());
    // t·rest_expr = list_expr(t·rest)
    let prod_rest = term_times_list(t, &rest);
    let prod_rest_expr = c.list_expr_pub(&prod_rest, p, q);
    let e_trest = term_mul_poly(c, parent, t, &rest, p, q);
    let c2 = c.cong_r(
        parent,
        &add_c,
        trest.clone(),
        prod_rest_expr.clone(),
        prod0_expr.clone(),
        e_trest,
    );
    let two_sums = c.add(prod0_expr.clone(), prod_rest_expr.clone());
    let merged = merge_lists(&prod0, &prod_rest);
    let merged_expr = c.list_expr_pub(&merged, p, q);
    let combine = prove_add_collect_list(c, parent, &prod0, &prod_rest, p, q);
    let s1 = c.trans(lhs.clone(), sum.clone(), mid.clone(), ldist, c1);
    let s2 = c.trans(lhs.clone(), mid, two_sums.clone(), s1, c2);
    c.trans(lhs, two_sums, merged_expr, s2, combine)
}

// ── Rust-side product helpers ──

fn term_mul(a: &(Mono, i64), b: &(Mono, i64)) -> (Mono, i64) {
    let mut m: Mono = a.0.iter().chain(b.0.iter()).copied().collect();
    m.sort_unstable();
    (m, a.1 * b.1)
}

fn term_times_list(t: &(Mono, i64), list: &TermList) -> TermList {
    // distribute t over list; result already in canonical order because the
    // monomials keep list's order shifted by t's monomial (which is constant
    // across the list); we re-sort/merge to be safe.
    let mut acc: TermList = Vec::new();
    for s in list {
        acc = super::insert_one_pub(&term_mul(t, s), &acc);
    }
    acc
}

fn list_times_list(a: &TermList, b: &TermList) -> TermList {
    let mut acc: TermList = Vec::new();
    for t in a {
        let part = term_times_list(t, b);
        for x in &part {
            acc = super::insert_one_pub(x, &acc);
        }
    }
    acc
}

/// Sorted insert of a single atom into a sorted monomial.
fn mono_insert(m: &Mono, x: u8) -> Mono {
    let mut out = m.clone();
    out.push(x);
    out.sort_unstable();
    out
}

/// Prove `term_of(t) · term_of(s) = term_of(t·s)` for nonempty monos.
fn term_mul_term(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    t: &(Mono, i64),
    s: &(Mono, i64),
    p: &Expr,
    q: &Expr,
) -> Expr {
    let prod = term_mul(t, s);
    // Reduce to magnitudes; reattach sign at the end.
    let (sa, sb) = (t.1.signum(), s.1.signum());
    let (ma, mb) = (t.1.abs(), s.1.abs());
    let pt = (t.0.clone(), ma); // positive term
    let ps = (s.0.clone(), mb);

    let te = c.term_of_pub(t, p, q);
    let se = c.term_of_pub(s, p, q);
    let lhs = c.mul(te.clone(), se.clone());
    let pte = c.term_of_pub(&pt, p, q);
    let pse = c.term_of_pub(&ps, p, q);
    let mul_c = c.mul_op();

    // Positive product proof: pte·pse = posTerm(ma*mb, prod.0).
    let pos_prod = (prod.0.clone(), ma * mb);
    let pos_prod_e = c.term_of_pub(&pos_prod, p, q);
    let pos = pos_mul(c, parent, &pt, &ps, p, q); // pte·pse = pos_prod_e

    match (sa, sb) {
        (1, 1) => {
            // lhs = pte·pse = pos_prod_e = term_of(prod) (since prod coeff > 0)
            pos
        }
        (-1, 1) => {
            // te = -(pte), se = pse. lhs = (-(pte))·pse.
            //   (-a)·b = -(a·b)  — derive: (-a)·b = -(a·b) via mul_comm + mul_neg.
            //     a·b: pte·pse. (-pte)·pse = ?  Use: x·y where x=-pte:
            //       (-pte)·pse = pse·(-pte)  [mul_comm]
            //                  = -(pse·pte)  [mul_neg pse pte]
            //                  = -(pte·pse)  [cong_neg mul_comm]
            //                  = -(pos_prod_e)  [cong_neg pos]
            let neg_pte = c.neg(pte.clone());
            // step1: (-pte)·pse = pse·(-pte)
            let comm1 = c.mcomm(neg_pte.clone(), pse.clone());
            let pse_negpte = c.mul(pse.clone(), neg_pte.clone());
            // step2: pse·(-pte) = -(pse·pte)   [mul_neg]
            let mneg = c.mul_neg(&pse, &pte);
            let pse_pte = c.mul(pse.clone(), pte.clone());
            let neg_psepte = c.neg(pse_pte.clone());
            // step3: -(pse·pte) = -(pte·pse)   [cong_neg mul_comm]
            let comm2 = c.mcomm(pse.clone(), pte.clone());
            let pte_pse = c.mul(pte.clone(), pse.clone());
            let cong_comm = c.cong_neg_pub(parent, &pse_pte, &pte_pse, &comm2);
            let neg_ptepse = c.neg(pte_pse.clone());
            // step4: -(pte·pse) = -(pos_prod_e)   [cong_neg pos]
            let cong_pos = c.cong_neg_pub(parent, &pte_pse, &pos_prod_e, &pos);
            let neg_pos = c.neg(pos_prod_e.clone());
            // chain
            let s1 = c.trans(
                lhs.clone(),
                pse_negpte.clone(),
                neg_psepte.clone(),
                comm1,
                mneg,
            );
            let s2 = c.trans(lhs.clone(), neg_psepte, neg_ptepse.clone(), s1, cong_comm);
            // term_of(prod) for prod coeff<0 is neg(pos_prod_e). So target = neg_pos.
            c.trans(lhs, neg_ptepse, neg_pos, s2, cong_pos)
        }
        (1, -1) => {
            // se = -(pse). lhs = pte·(-(pse)) = -(pte·pse)  [mul_neg] = -(pos_prod_e) [cong_neg pos]
            let mneg = c.mul_neg(&pte, &pse);
            let pte_pse = c.mul(pte.clone(), pse.clone());
            let neg_ptepse = c.neg(pte_pse.clone());
            let cong_pos = c.cong_neg_pub(parent, &pte_pse, &pos_prod_e, &pos);
            let neg_pos = c.neg(pos_prod_e.clone());
            let s1 = c.trans(
                lhs.clone(),
                neg_ptepse.clone(),
                neg_pos.clone(),
                mneg,
                cong_pos,
            );
            let _ = mul_c;
            s1
        }
        (-1, -1) => {
            // te=-(pte), se=-(pse). (-pte)·(-pse) = pte·pse  [neg_mul_neg] = pos_prod_e [pos]
            let nmn = c.neg_mul_neg(&pte, &pse);
            let pte_pse = c.mul(pte.clone(), pse.clone());
            // chain: lhs = pte·pse (nmn) = pos_prod_e (pos)
            c.trans(lhs, pte_pse, pos_prod_e, nmn, pos)
        }
        _ => panic!("term_mul_term: zero coeff"),
    }
}

/// Positive-coefficient term product:
/// `posTerm(ca,Ma) · posTerm(cb,Mb) = posTerm(ca*cb, Ma⊎Mb)`, `ca,cb ≥ 1`.
fn pos_mul(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    a: &(Mono, i64),
    b: &(Mono, i64),
    p: &Expr,
    q: &Expr,
) -> Expr {
    let (ca, cb) = (a.1 as usize, b.1 as usize);
    let ma_e = c.mono_expr_pub(&a.0, p, q);
    let mb_e = c.mono_expr_pub(&b.0, p, q);
    let prod_mono = {
        let mut m = a.0.clone();
        m.extend_from_slice(&b.0);
        m.sort_unstable();
        m
    };
    let prod_mono_e = c.mono_expr_pub(&prod_mono, p, q);
    let cc = ca * cb;

    let ae = c.term_of_pub(a, p, q); // posTerm(ca,Ma)
    let be = c.term_of_pub(b, p, q);
    let lhs = c.mul(ae.clone(), be.clone());
    let mul_c = c.mul_op();

    // ── constant-factor cases (empty monomial) ──
    if a.0.is_empty() && b.0.is_empty() {
        // nat_lit(ca) · nat_lit(cb) = nat_lit(ca*cb) = posTerm(ca*cb, ∅).
        return c.numeral_mul(parent, ca, cb);
    }
    if a.0.is_empty() {
        // nat_lit(ca) · posTerm(cb,Mb) = posTerm(ca*cb, Mb).
        return pos_scalar_mul_left(c, parent, ca, b, p, q);
    }
    if b.0.is_empty() {
        // posTerm(ca,Ma) · nat_lit(cb) = posTerm(ca*cb, Ma).
        //   commute, then left-scalar.
        let comm = c.mcomm(ae.clone(), be.clone());
        let swapped = c.mul(be.clone(), ae.clone());
        let left = pos_scalar_mul_left(c, parent, cb, a, p, q); // nat_lit(cb)·posTerm(ca,Ma) = posTerm(ca*cb, Ma)
        let target = c.term_of_pub(&(a.0.clone(), (ca * cb) as i64), p, q);
        return c.trans(lhs, swapped, target, comm, left);
    }

    // First normalize both factors to `nat_lit(c)·M` form (or keep bare if c==1).
    // Build the fully-explicit `(nat_lit ca · Ma) · (nat_lit cb · Mb)` and prove
    // lhs = that, then reorder.
    // Convert ae → caL·Ma, be → cbL·Mb (term_to_nmul handles c==1 via one_mul).
    let cal_ma = c.mul(c.nat_lit(ca), ma_e.clone());
    let cbl_mb = c.mul(c.nat_lit(cb), mb_e.clone());
    let e_ae = c.term_to_nmul_pub(&ma_e, ca);
    let c1 = c.cong_l(parent, &mul_c, ae.clone(), cal_ma.clone(), be.clone(), e_ae);
    let mid1 = c.mul(cal_ma.clone(), be.clone());
    let e_be = c.term_to_nmul_pub(&mb_e, cb);
    let c2 = c.cong_r(
        parent,
        &mul_c,
        be.clone(),
        cbl_mb.clone(),
        cal_ma.clone(),
        e_be,
    );
    let full = c.mul(cal_ma.clone(), cbl_mb.clone()); // (caL·Ma)·(cbL·Mb)
    let to_full = c.trans(lhs.clone(), mid1, full.clone(), c1, c2);

    // Reorder (caL·Ma)·(cbL·Mb) = (caL·cbL)·(Ma·Mb)  [mul_mul_mul_comm].
    let reorder = c.mmmc(&c.nat_lit(ca), &ma_e, &c.nat_lit(cb), &mb_e);
    let cacb = c.mul(c.nat_lit(ca), c.nat_lit(cb));
    let mamb = c.mul(ma_e.clone(), mb_e.clone());
    let grouped = c.mul(cacb.clone(), mamb.clone());
    let to_grouped = c.trans(lhs.clone(), full, grouped.clone(), to_full, reorder);

    // (caL·cbL) → nat_lit(ca*cb)  [numeral_mul], lift via cong_l.
    let nm = c.numeral_mul(parent, ca, cb);
    let ccl = c.nat_lit(cc);
    let cong_num = c.cong_l(parent, &mul_c, cacb.clone(), ccl.clone(), mamb.clone(), nm);
    let ccl_mamb = c.mul(ccl.clone(), mamb.clone());
    let to_cclmamb = c.trans(lhs.clone(), grouped, ccl_mamb.clone(), to_grouped, cong_num);

    // (Ma·Mb) → mono_expr(prod_mono)  [mono reorder], lift via cong_r.
    let mono_eq = mul_mono(c, parent, &a.0, &b.0, p, q); // Ma·Mb = prod_mono_e
    let cong_mono = c.cong_r(
        parent,
        &mul_c,
        mamb.clone(),
        prod_mono_e.clone(),
        ccl.clone(),
        mono_eq,
    );
    let ccl_prod = c.mul(ccl.clone(), prod_mono_e.clone());
    let to_cclprod = c.trans(
        lhs.clone(),
        ccl_mamb,
        ccl_prod.clone(),
        to_cclmamb,
        cong_mono,
    );

    // nat_lit(cc)·prod_mono_e = posTerm(cc, prod_mono)  [nmul_to_term]
    let e_back = c.nmul_to_term_pub(&prod_mono_e, cc);
    let target = c.term_of_pub(&(prod_mono.clone(), cc as i64), p, q);
    c.trans(lhs, ccl_prod, target, to_cclprod, e_back)
}

/// Prove `nat_lit(k) · posTerm(cb, Mb) = posTerm(k*cb, Mb)`, `Mb` nonempty,
/// `k, cb ≥ 1`.
fn pos_scalar_mul_left(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    k: usize,
    b: &(Mono, i64),
    p: &Expr,
    q: &Expr,
) -> Expr {
    let cb = b.1 as usize;
    let mb_e = c.mono_expr_pub(&b.0, p, q);
    let be = c.term_of_pub(b, p, q); // posTerm(cb,Mb)
    let kl = c.nat_lit(k);
    let lhs = c.mul(kl.clone(), be.clone());
    let prod = k * cb;
    let target = c.term_of_pub(&(b.0.clone(), prod as i64), p, q);
    let mul_c = c.mul_op();

    // be = cbL·Mb  (term_to_nmul handles cb==1 via one_mul → Mb).
    let cbl_mb = c.mul(c.nat_lit(cb), mb_e.clone());
    let e_be = c.term_to_nmul_pub(&mb_e, cb); // be = cbL·Mb
    let cong_be = c.cong_r(parent, &mul_c, be.clone(), cbl_mb.clone(), kl.clone(), e_be);
    let kl_cblmb = c.mul(kl.clone(), cbl_mb.clone()); // kL·(cbL·Mb)

    // kL·(cbL·Mb) = (kL·cbL)·Mb   [symm mul_assoc]
    let assoc = c.massoc(kl.clone(), c.nat_lit(cb), mb_e.clone()); // (kL·cbL)·Mb = kL·(cbL·Mb)
    let klcbl = c.mul(kl.clone(), c.nat_lit(cb));
    let klcbl_mb = c.mul(klcbl.clone(), mb_e.clone());
    let s_assoc = c.symm(klcbl_mb.clone(), kl_cblmb.clone(), assoc);
    let to_klcblmb2 = c.trans(
        lhs.clone(),
        kl_cblmb.clone(),
        klcbl_mb.clone(),
        cong_be,
        s_assoc,
    );

    // (kL·cbL) = nat_lit(k*cb)   [numeral_mul], lift cong_l
    let nm = c.numeral_mul(parent, k, cb);
    let prodl = c.nat_lit(prod);
    let cong_num = c.cong_l(
        parent,
        &mul_c,
        klcbl.clone(),
        prodl.clone(),
        mb_e.clone(),
        nm,
    );
    let prodl_mb = c.mul(prodl.clone(), mb_e.clone());
    let to_prodlmb = c.trans(
        lhs.clone(),
        klcbl_mb.clone(),
        prodl_mb.clone(),
        to_klcblmb2,
        cong_num,
    );

    // nat_lit(prod)·Mb = posTerm(prod, Mb)   [nmul_to_term]
    let e_back = c.nmul_to_term_pub(&mb_e, prod);
    c.trans(lhs, prodl_mb, target, to_prodlmb, e_back)
}

/// Prove `mono_expr(Ma) · mono_expr(Mb) = mono_expr(Ma⊎Mb)`. Both nonempty.
fn mul_mono(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    ma: &Mono,
    mb: &Mono,
    p: &Expr,
    q: &Expr,
) -> Expr {
    debug_assert!(!ma.is_empty() && !mb.is_empty());
    let ma_e = c.mono_expr_pub(ma, p, q);
    let mb_e = c.mono_expr_pub(mb, p, q);
    let lhs = c.mul(ma_e.clone(), mb_e.clone());

    if mb.len() == 1 {
        return mul_atom(c, parent, ma, mb[0], p, q);
    }
    // mb = mb_init ++ [last] ; mono_expr(mb) = mono_expr(mb_init)·atom(last).
    let last = *mb.last().expect("nonempty");
    let mb_init: Mono = mb[..mb.len() - 1].to_vec();
    let mb_init_e = c.mono_expr_pub(&mb_init, p, q);
    let last_e = atom_expr(last, p, q);
    let mul_c = c.mul_op();
    // ma_e · (mb_init_e · last) = (ma_e · mb_init_e) · last   [symm mul_assoc]
    let assoc = c.massoc(ma_e.clone(), mb_init_e.clone(), last_e.clone());
    let lhs_assoc = c.mul(c.mul(ma_e.clone(), mb_init_e.clone()), last_e.clone());
    let s_assoc = c.symm(lhs_assoc.clone(), lhs.clone(), assoc);
    // ma_e · mb_init_e = mono_expr(ma ⊎ mb_init)  [recurse]
    let merged_init: Mono = {
        let mut m = ma.clone();
        m.extend_from_slice(&mb_init);
        m.sort_unstable();
        m
    };
    let merged_init_e = c.mono_expr_pub(&merged_init, p, q);
    let inner = mul_mono(c, parent, ma, &mb_init, p, q);
    let cong = c.cong_l(
        parent,
        &mul_c,
        c.mul(ma_e.clone(), mb_init_e.clone()),
        merged_init_e.clone(),
        last_e.clone(),
        inner,
    );
    let mid = c.mul(merged_init_e.clone(), last_e.clone());
    // mono_expr(merged_init)·last = mono_expr(insert(merged_init,last))  [mul_atom]
    let atom_step = mul_atom(c, parent, &merged_init, last, p, q);
    let final_mono = mono_insert(&merged_init, last);
    let final_e = c.mono_expr_pub(&final_mono, p, q);
    // chain: lhs = lhs_assoc (s_assoc) = mid (cong) = final_e (atom_step)
    let s1 = c.trans(lhs.clone(), lhs_assoc, mid.clone(), s_assoc, cong);
    c.trans(lhs, mid, final_e, s1, atom_step)
}

/// Prove `mono_expr(M) · atom(x) = mono_expr(insert(M,x))`. M nonempty.
fn mul_atom(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    m: &Mono,
    x: u8,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let m_e = c.mono_expr_pub(m, p, q);
    let x_e = atom_expr(x, p, q);
    let lhs = c.mul(m_e.clone(), x_e.clone());
    let last = *m.last().expect("nonempty");
    if x >= last {
        // appending x keeps sorted order: mono_expr(M)·x = mono_expr(M++[x]).
        // insert(M,x) == M++[x] since x is ≥ max.
        return c.refl(lhs);
    }
    // x < last. M = P ++ [last] (or single atom).
    if m.len() == 1 {
        // m = [last], x < last. mono_expr = atom(last). lhs = last·x.
        //   last·x = x·last  [mul_comm]; insert([last],x) = [x,last] (x<last).
        //   mono_expr([x,last]) = x·last.
        let comm = c.mcomm(m_e.clone(), x_e.clone());
        return comm;
    }
    let p_mono: Mono = m[..m.len() - 1].to_vec();
    let p_e = c.mono_expr_pub(&p_mono, p, q);
    let last_e = atom_expr(last, p, q);
    let mul_c = c.mul_op();
    // (p_e·last)·x = p_e·(last·x)  [mul_assoc]
    let assoc = c.massoc(p_e.clone(), last_e.clone(), x_e.clone());
    let pe_lastx = c.mul(p_e.clone(), c.mul(last_e.clone(), x_e.clone()));
    // last·x = x·last  [mul_comm], lift under (p_e · ·)
    let comm = c.mcomm(last_e.clone(), x_e.clone());
    let x_last = c.mul(x_e.clone(), last_e.clone());
    let cong_comm = c.cong_r(
        parent,
        &mul_c,
        c.mul(last_e.clone(), x_e.clone()),
        x_last.clone(),
        p_e.clone(),
        comm,
    );
    let pe_xlast = c.mul(p_e.clone(), x_last.clone());
    // p_e·(x·last) = (p_e·x)·last  [symm mul_assoc]
    let assoc2 = c.massoc(p_e.clone(), x_e.clone(), last_e.clone());
    let pex_last = c.mul(c.mul(p_e.clone(), x_e.clone()), last_e.clone());
    let s_assoc2 = c.symm(pex_last.clone(), pe_xlast.clone(), assoc2);
    // p_e·x = mono_expr(insert(P,x))  [recurse mul_atom]
    let inner = mul_atom(c, parent, &p_mono, x, p, q);
    let ins_p = mono_insert(&p_mono, x);
    let ins_p_e = c.mono_expr_pub(&ins_p, p, q);
    let cong_rec = c.cong_l(
        parent,
        &mul_c,
        c.mul(p_e.clone(), x_e.clone()),
        ins_p_e.clone(),
        last_e.clone(),
        inner,
    );
    let insp_last = c.mul(ins_p_e.clone(), last_e.clone());
    // insp_last = mono_expr(ins_p ++ [last]) ; since last is the max, ins_p++[last] = insert(m,x).
    let final_mono = mono_insert(m, x);
    let final_e = c.mono_expr_pub(&final_mono, p, q);
    // chain: lhs = pe_lastx (assoc) = pe_xlast (cong_comm) = pex_last (s_assoc2)
    //            = insp_last (cong_rec) = final_e (refl, syntactic)
    let s1 = c.trans(
        lhs.clone(),
        pe_lastx.clone(),
        pe_xlast.clone(),
        assoc,
        cong_comm,
    );
    let s2 = c.trans(lhs.clone(), pe_xlast, pex_last.clone(), s1, s_assoc2);
    let s3 = c.trans(lhs.clone(), pex_last, insp_last.clone(), s2, cong_rec);
    // insp_last and final_e must be syntactically equal.
    debug_assert_eq!(insp_last, final_e, "mul_atom final shape mismatch");
    s3
}

fn atom_expr(x: u8, p: &Expr, q: &Expr) -> Expr {
    if x == 0 {
        p.clone()
    } else {
        q.clone()
    }
}
