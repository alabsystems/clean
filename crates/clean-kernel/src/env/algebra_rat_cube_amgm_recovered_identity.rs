// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The ring identity `RID : (2p+q)³ = 27·((p·p)·q) + (((p−q)·(p−q))·(8p+q))`.
//!
//! Proven by a small *verified* polynomial normalizer: each `Rat` expression in
//! the two free atoms `p, q` (built from `Rat.add`/`Rat.mul`/`Rat.neg`/`Rat.sub`
//! and additive `Rat.one` numerals) is reduced to a canonical monomial sum
//! together with an `Eq` proof that the original equals its normal form. Both
//! sides of `RID` normalize to the SAME canonical form, so
//! `cube_s = nf = (lhs+r)` closes by `Eq.trans`. Every step is a pure `Rat` ring
//! lemma (`left/right_distrib`, `mul_assoc/comm`, `add_assoc/comm`, `one_mul`,
//! `mul_neg`) applied through `congrArg`, so the closure is foundational-only.

use super::CubeAmGmConstsRecovered;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;
use std::collections::BTreeMap;

/// A monomial: sorted multiset of atom ids (`0 = p`, `1 = q`). The empty vec is
/// the constant monomial `1`.
type Mono = Vec<u8>;

/// A normalized polynomial: monomial → signed integer coefficient (nonzero).
/// Plus the materialized canonical `Expr` and the proof `orig = nf`.
struct Normal {
    poly: BTreeMap<Mono, i64>,
    nf: Expr,
    /// proof : orig = nf
    proof: Expr,
}

/// Atom ids.
const P: u8 = 0;
const Q: u8 = 1;

impl CubeAmGmConstsRecovered {
    /// `pub(super)` re-export of `mono_expr` for the `terms`/`collect` helpers.
    pub(super) fn mono_expr_pub(&self, mono: &Mono, p: &Expr, q: &Expr) -> Expr {
        self.mono_expr(mono, p, q)
    }

    /// `pub(super)` re-export of `poly_expr`.
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) fn poly_expr_pub(&self, poly: &BTreeMap<Mono, i64>, p: &Expr, q: &Expr) -> Expr {
        self.poly_expr(poly, p, q)
    }

    /// Build a canonical monomial `Expr` for `mono` (product of atoms, the
    /// left-nested form `((a·b)·c)…`, constant `1` for the empty monomial).
    fn mono_expr(&self, mono: &Mono, p: &Expr, q: &Expr) -> Expr {
        if mono.is_empty() {
            return self.one();
        }
        let atom = |id: u8| if id == P { p.clone() } else { q.clone() };
        let mut acc = atom(mono[0]);
        for &id in &mono[1..] {
            acc = self.mul(acc, atom(id));
        }
        acc
    }

    /// Materialize a coefficient·monomial term as a canonical `Expr`.
    /// `coeff` is assumed nonzero. Positive `n`: `nlit(n)·mono` (or `mono` when
    /// `n==1` and the monomial is nonempty — to keep terms tight we still wrap;
    /// here we always wrap as `nlit·mono` except `mono==1` → `nlit`).
    /// Negative `n`: `Rat.neg (nlit(|n|)·mono)`.
    fn term_expr(&self, mono: &Mono, coeff: i64, p: &Expr, q: &Expr) -> Expr {
        debug_assert!(coeff != 0);
        let mag = coeff.unsigned_abs() as usize;
        let pos = if mono.is_empty() {
            // constant term: just the numeral
            self.nat_lit(mag)
        } else if mag == 1 {
            self.mono_expr(mono, p, q)
        } else {
            self.mul(self.nat_lit(mag), self.mono_expr(mono, p, q))
        };
        if coeff < 0 {
            self.neg(pos)
        } else {
            pos
        }
    }

    /// Materialize a whole poly map as a canonical right-nested sum of terms,
    /// ordered by the `BTreeMap` key order. Empty poly → `0` (unused here).
    fn poly_expr(&self, poly: &BTreeMap<Mono, i64>, p: &Expr, q: &Expr) -> Expr {
        let terms: Vec<Expr> = poly
            .iter()
            .map(|(m, &c)| self.term_expr(m, c, p, q))
            .collect();
        if terms.is_empty() {
            return self.zero();
        }
        // right-nested: t0 + (t1 + (t2 + …))
        let mut it = terms.into_iter().rev();
        let mut acc = it.next().expect("nonempty");
        for t in it {
            acc = self.add(t, acc);
        }
        acc
    }
}

/// Multiply two monomials (concatenate + sort).
fn mono_mul(a: &Mono, b: &Mono) -> Mono {
    let mut m: Mono = a.iter().chain(b.iter()).copied().collect();
    m.sort_unstable();
    m
}

/// Build the RID proof: `cube_s = lhs + r`.
///
/// `cube_s := ((s·s)·s)`, `s := (p+p)+q`;
/// `lhs := 27·((p·p)·q)`; `r := ((p−q)·(p−q))·((8·p)+q)`.
///
/// Both sides are normalized to the shared canonical poly; the equality is
/// `Eq.trans (cube_s = nf) (symm (lhs+r = nf))`.
pub(super) fn build_rid(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let s = c.add(c.add(p.clone(), p.clone()), q.clone());
    let cube_s = c.mul(c.mul(s.clone(), s.clone()), s.clone());

    let p2q = c.mul(c.mul(p.clone(), p.clone()), q.clone());
    let lhs = c.mul(c.nat_lit(27), p2q);
    let d = c.sub(p.clone(), q.clone());
    let dd = c.mul(d.clone(), d.clone());
    let eight_p = c.mul(c.nat_lit(8), p.clone());
    let eight_p_plus_q = c.add(eight_p, q.clone());
    let r = c.mul(dd, eight_p_plus_q);
    let lhs_plus_r = c.add(lhs.clone(), r.clone());

    let n_cube = normalize(c, parent, &cube_s, p, q);
    let n_rhs = normalize(c, parent, &lhs_plus_r, p, q);

    // Sanity (debug): both normal forms must coincide.
    debug_assert_eq!(
        n_cube.poly, n_rhs.poly,
        "RID normal forms differ: cube={:?} rhs={:?}",
        n_cube.poly, n_rhs.poly
    );

    // cube_s = nf  (n_cube.proof);  lhs+r = nf  (n_rhs.proof) ⇒ symm : nf = lhs+r.
    let nf = n_cube.nf.clone();
    let back = c.symm(lhs_plus_r.clone(), nf.clone(), n_rhs.proof);
    c.trans(cube_s, nf, lhs_plus_r, n_cube.proof, back)
}

/// Recursively normalize `e` (over atoms `p`, `q`) to canonical form, returning
/// the poly map, the materialized canonical `Expr`, and a proof `e = nf`.
fn normalize(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    e: &Expr,
    p: &Expr,
    q: &Expr,
) -> Normal {
    // Structural dispatch on the head constant.
    if let Some((op, a, b)) = as_binop(c, e) {
        match op {
            BinOp::Add => return norm_add(c, parent, &a, &b, p, q),
            BinOp::Mul => return norm_mul(c, parent, &a, &b, p, q),
            BinOp::Sub => {
                // a − b ≡ a + (−b) by delta on the reducible Rat.sub.
                // We prove `e = a + (−b)` by refl (defeq), then normalize the latter.
                let neg_b = c.neg(b.clone());
                let a_plus_negb = c.add(a.clone(), neg_b);
                let inner = normalize(c, parent, &a_plus_negb, p, q);
                // proof : e = inner.nf, with e =defeq a_plus_negb so refl-bridge.
                let bridge = c.refl(a_plus_negb.clone()); // a_plus_negb = a_plus_negb, and e ≡ a_plus_negb
                                                          // e = a_plus_negb (refl, defeq) then a_plus_negb = inner.nf
                let proof = c.trans(
                    e.clone(),
                    a_plus_negb,
                    inner.nf.clone(),
                    bridge,
                    inner.proof,
                );
                return Normal {
                    poly: inner.poly,
                    nf: inner.nf,
                    proof,
                };
            }
        }
    }
    if let Some(a) = as_neg(c, e) {
        return norm_neg(c, parent, &a, p, q);
    }
    // Atom or numeral leaf.
    norm_leaf(c, e, p, q)
}

enum BinOp {
    Add,
    Mul,
    Sub,
}

/// Match `Rat.add a b` / `Rat.mul a b` / `Rat.sub a b`.
fn as_binop(c: &CubeAmGmConstsRecovered, e: &Expr) -> Option<(BinOp, Expr, Expr)> {
    let (head, args) = uncurry(e);
    if args.len() != 2 {
        return None;
    }
    let name = const_name(&head)?;
    let op = match name.as_str() {
        "Rat.add" => BinOp::Add,
        "Rat.mul" => BinOp::Mul,
        "Rat.sub" => BinOp::Sub,
        _ => return None,
    };
    let _ = c;
    Some((op, args[0].clone(), args[1].clone()))
}

/// Match `Rat.neg a`.
fn as_neg(c: &CubeAmGmConstsRecovered, e: &Expr) -> Option<Expr> {
    let (head, args) = uncurry(e);
    if args.len() != 1 {
        return None;
    }
    if const_name(&head)?.as_str() == "Rat.neg" {
        let _ = c;
        Some(args[0].clone())
    } else {
        None
    }
}

/// `a + b`: normalize each, then merge.
fn norm_add(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    a: &Expr,
    b: &Expr,
    p: &Expr,
    q: &Expr,
) -> Normal {
    let na = normalize(c, parent, a, p, q);
    let nb = normalize(c, parent, b, p, q);

    // a + b = na.nf + nb.nf  (cong on both args).
    let add_op = c.add_op();
    // step1 : a + b = na.nf + b   (cong_left)
    let s1 = c.cong_l(
        parent,
        &add_op,
        a.clone(),
        na.nf.clone(),
        b.clone(),
        na.proof.clone(),
    );
    let mid = c.add(na.nf.clone(), b.clone());
    // step2 : na.nf + b = na.nf + nb.nf  (cong_right)
    let s2 = c.cong_r(
        parent,
        &add_op,
        b.clone(),
        nb.nf.clone(),
        na.nf.clone(),
        nb.proof.clone(),
    );
    let sum_nf = c.add(na.nf.clone(), nb.nf.clone());
    let to_sumnf = c.trans(c.add(a.clone(), b.clone()), mid, sum_nf.clone(), s1, s2);

    // merge polys.
    let mut poly = na.poly.clone();
    for (m, cc) in &nb.poly {
        *poly.entry(m.clone()).or_insert(0) += *cc;
    }
    poly.retain(|_, v| *v != 0);
    let nf = c.poly_expr(&poly, p, q);

    // proof : na.nf + nb.nf = nf  — the additive-collection equality.
    let merge = prove_add_collect(c, parent, &na.poly, &nb.poly, &poly, p, q);
    let proof = c.trans(
        c.add(a.clone(), b.clone()),
        sum_nf,
        nf.clone(),
        to_sumnf,
        merge,
    );
    Normal { poly, nf, proof }
}

/// `a * b`: normalize each, then distribute the product of the two canonical
/// sums into the canonical product poly.
fn norm_mul(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    a: &Expr,
    b: &Expr,
    p: &Expr,
    q: &Expr,
) -> Normal {
    let na = normalize(c, parent, a, p, q);
    let nb = normalize(c, parent, b, p, q);
    let mul_op = c.mul_op();
    // a*b = na.nf * b = na.nf * nb.nf.
    let s1 = c.cong_l(
        parent,
        &mul_op,
        a.clone(),
        na.nf.clone(),
        b.clone(),
        na.proof.clone(),
    );
    let mid = c.mul(na.nf.clone(), b.clone());
    let s2 = c.cong_r(
        parent,
        &mul_op,
        b.clone(),
        nb.nf.clone(),
        na.nf.clone(),
        nb.proof.clone(),
    );
    let prod_nf = c.mul(na.nf.clone(), nb.nf.clone());
    let to_prodnf = c.trans(c.mul(a.clone(), b.clone()), mid, prod_nf.clone(), s1, s2);

    // product poly.
    let mut poly: BTreeMap<Mono, i64> = BTreeMap::new();
    for (ma, ca) in &na.poly {
        for (mb, cb) in &nb.poly {
            *poly.entry(mono_mul(ma, mb)).or_insert(0) += ca * cb;
        }
    }
    poly.retain(|_, v| *v != 0);
    let nf = c.poly_expr(&poly, p, q);

    // proof : na.nf * nb.nf = nf.
    let dist = prove_mul_distrib(c, parent, &na.poly, &nb.poly, &poly, p, q);
    let proof = c.trans(
        c.mul(a.clone(), b.clone()),
        prod_nf,
        nf.clone(),
        to_prodnf,
        dist,
    );
    Normal { poly, nf, proof }
}

/// `−a`: normalize `a`, negate every coefficient.
fn norm_neg(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    a: &Expr,
    p: &Expr,
    q: &Expr,
) -> Normal {
    let na = normalize(c, parent, a, p, q);
    let neg_op = Expr::const_(crate::name::Name::from_string("Rat.neg"), vec![]);
    // −a = −(na.nf)  (cong on neg).
    let cong = cong_neg(c, parent, a, &na.nf, &na.proof);
    let neg_nf = Expr::app(neg_op, na.nf.clone());

    let mut poly = na.poly.clone();
    for v in poly.values_mut() {
        *v = -*v;
    }
    let nf = c.poly_expr(&poly, p, q);

    // proof : −(na.nf) = nf.
    let pushed = prove_neg_push(c, parent, &na.poly, &poly, p, q);
    let proof = c.trans(c.neg(a.clone()), neg_nf, nf.clone(), cong, pushed);
    Normal { poly, nf, proof }
}

/// `−e1 = −e2` from `h : e1 = e2`.
fn cong_neg(
    c: &CubeAmGmConstsRecovered,
    parent: &EnvDeclBuilder,
    e1: &Expr,
    e2: &Expr,
    h: &Expr,
) -> Expr {
    let neg_op = Expr::const_(crate::name::Name::from_string("Rat.neg"), vec![]);
    // congrArg over (fun w => Rat.neg w).
    let f = {
        use crate::expr::BinderInfo;
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = ch.fresh_local(c.rat());
        let body = Expr::app(neg_op.clone(), w);
        ch.finish_child(ch.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
    };
    use crate::level::Level;
    let l1 = Level::succ(Level::zero());
    let congr_arg = Expr::const_(
        crate::name::Name::from_string("congrArg"),
        vec![l1.clone(), l1],
    );
    Expr::apps(
        congr_arg,
        [c.rat(), c.rat(), e1.clone(), e2.clone(), f, h.clone()],
    )
}

/// Leaf: an atom (`p` or `q`) or an additive numeral (which we treat as the
/// constant monomial). Returns `e = e` (refl) plus its 1-term poly.
fn norm_leaf(c: &CubeAmGmConstsRecovered, e: &Expr, p: &Expr, q: &Expr) -> Normal {
    let mut poly = BTreeMap::new();
    // Identify p / q by syntactic equality on the local Expr.
    if e == p {
        poly.insert(vec![P], 1);
    } else if e == q {
        poly.insert(vec![Q], 1);
    } else {
        // Numeral leaf: treat as constant. We need its integer value. Built via
        // nat_lit, so count the `Rat.one`s — but at this point a leaf numeral
        // only arises if the input contained a literal. RID's inputs contain
        // literals 27 and 8 only as `nat_lit` already in canonical (mul) form,
        // never as bare additive leaves entering normalize. So a bare leaf here
        // is unexpected; fall back to a 1·(opaque) — but to stay sound we make
        // the constant monomial carry the literal's value.
        let val = numeral_value(c, e);
        poly.insert(vec![], val);
    }
    let nf = c.poly_expr(&poly, p, q);
    // For an atom, nf == e exactly (poly_expr of {[atom]:1} = mono_expr = e),
    // so refl closes. For a numeral, nf == e too (nat_lit reproduced).
    let proof = c.refl(e.clone());
    let _ = nf.clone();
    Normal { poly, nf, proof }
}

/// Count the additive `Rat.one`s in a `nat_lit`-shaped numeral. Left-nested:
/// `1`, `1+1`, `(1+1)+1`, …
fn numeral_value(c: &CubeAmGmConstsRecovered, e: &Expr) -> i64 {
    if e == &c.one() {
        return 1;
    }
    if let Some((BinOp::Add, a, b)) = as_binop(c, e) {
        if b == c.one() {
            return numeral_value(c, &a) + 1;
        }
    }
    // Unknown leaf — should not happen for RID. Treat as 0 to surface a poly
    // mismatch in the debug_assert rather than silently mis-prove.
    0
}

// ── uncurry / const-name helpers ──

fn uncurry(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut cur = e.clone();
    while let crate::expr::ExprKind::App(f, a) = cur.kind() {
        args.push((**a).clone());
        let f = (**f).clone();
        cur = f;
    }
    args.reverse();
    (cur, args)
}

fn const_name(e: &Expr) -> Option<String> {
    if let crate::expr::ExprKind::Const(n, _) = e.kind() {
        Some(n.to_string())
    } else {
        None
    }
}

// ── collection / distribution / negation-push equalities ──
// These prove that the materialized intermediate (`na.nf + nb.nf`, etc.) equals
// the materialized merged poly `nf`. Implemented in `collect.rs` / `terms.rs`.
#[path = "algebra_rat_cube_amgm_recovered_identity/collect.rs"]
mod collect;
#[path = "algebra_rat_cube_amgm_recovered_identity/terms.rs"]
mod terms;
use collect::{prove_add_collect, prove_mul_distrib, prove_neg_push};
