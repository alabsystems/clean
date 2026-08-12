// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! NNReal polynomial-identity helper — a ring-normalizer that EMITS
//! kernel-checkable proofs (it does NOT register kernel decls).
//!
//! Given two `NNReal` expressions built from atom `FVar`s, `NNReal.ofRat
//! (Rat.mk (Int.ofNat n) d) h` literal coefficients, `NNReal.add` and
//! `NNReal.mul`, that are EQUAL as polynomials over the commutative semiring
//! `NNReal`, [`prove_nnreal_poly_eq`] returns a proof term of type `Eq NNReal
//! lhs rhs`. When the two sides are NOT equal as semiring polynomials (or
//! contain a node the helper does not model), it returns `None`.
//!
//! # How it works (canonicalization + congruence-rewriting)
//!
//! `normalize(e) -> (Poly, proof : Eq NNReal e canon(Poly))` recurses on `e`:
//!
//!   * `FVar x`        → `Poly = [1·x]`; proof `symm (mul_one x)` (canon is
//!                       `x · ofRat 1`, so `x · ofRat 1 = x`, symm-flipped).
//!   * `ofRat c h`     → `Poly = [c·∅]`; proof `refl` (canon IS `ofRat c`).
//!   * `add a b`       → `Poly = norm(a) ⊕ norm(b)`; proof chains the two child
//!                       proofs under `add` congruence (`Eq.subst`), then a
//!                       structural `add`-merge proof.
//!   * `mul a b`       → `Poly = norm(a) ⊗ norm(b)`; proof chains the two child
//!                       proofs under `mul` congruence, then a distribute/merge
//!                       proof built from `mul_add`/`add_mul`/`mul_comm`/
//!                       `mul_assoc`/`ofRat_mul`.
//!
//! `canon(Poly)` is a DETERMINISTIC layout: monomials sorted by atom key,
//! right-associated sum; each monomial is `(x₁·(x₂·…·xₖ)) · ofRat c` (atoms
//! right-associated, coefficient on the RIGHT — so the unit drop uses the
//! landed `NNReal.mul_one`, NOT the missing `one_mul`). Coefficients are tracked
//! as FREE rational representatives `(num,den)` matching exactly what the
//! kernel's `Rat.add`/`Rat.mul` `Quot.lift`s compute (verified: distinct
//! representatives are NOT defeq, so the helper folds in lock-step with the
//! kernel and only ever bridges to the EXACT free representative via `refl`).
//!
//! Then `prove_nnreal_poly_eq lhs rhs := Eq.trans (norm lhs).proof
//! (Eq.symm (norm rhs).proof)` — valid exactly when `canon` of the two polys is
//! the SAME `Expr`, i.e. the two sides are the same polynomial. Every emitted
//! term is a composition of the foundational `Eq` constructors and the landed,
//! axiom-free `NNReal` semiring lemmas; nothing is trusted — the caller
//! kernel-checks the result.
//!
//! LIMITATION: the modelled grammar is `+`, `·`, atom-`FVar`, and `ofRat`
//! literal coefficients only (no subtraction — `NNReal` has none — no `pow`, no
//! non-literal `ofRat` arguments). Anything else ⇒ `None`.

use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr, ExprKind, FVarId};
use crate::level::Level;
use crate::name::Name;

// ─────────────────────────────────────────────────────────────────────────────
// Polynomial representation (free-representative rational coefficients).
// ─────────────────────────────────────────────────────────────────────────────

/// A monomial: a free-representative rational coefficient `num/den` times a
/// sorted multiset of atom `FVar` ids.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Mono {
    num: u128,
    den: u128,
    atoms: Vec<u64>,
}

/// A polynomial: monomials in canonical order (sorted by atom key), like-atom
/// monomials merged. The empty `Vec` is the zero polynomial.
type Poly = Vec<Mono>;

/// Free-representative rational add: `(n1/d1) + (n2/d2) = (n1·d2 + n2·d1)/(d1·d2)`
/// — EXACTLY the representative the kernel's `Rat.add` `Quot.lift` computes.
fn rat_add((n1, d1): (u128, u128), (n2, d2): (u128, u128)) -> (u128, u128) {
    (n1 * d2 + n2 * d1, d1 * d2)
}

/// Free-representative rational mul: `(n1/d1)·(n2/d2) = (n1·n2)/(d1·d2)`.
fn rat_mul((n1, d1): (u128, u128), (n2, d2): (u128, u128)) -> (u128, u128) {
    (n1 * n2, d1 * d2)
}

/// Compare two atom-keys for the canonical monomial ordering: shorter first,
/// then lexicographic on ids. Deterministic and total.
fn atom_key_cmp(a: &[u64], b: &[u64]) -> std::cmp::Ordering {
    a.len().cmp(&b.len()).then_with(|| a.iter().cmp(b.iter()))
}

// ─────────────────────────────────────────────────────────────────────────────
// Smart-constructors over the NNReal / Rat / Eq surface.
// ─────────────────────────────────────────────────────────────────────────────

/// Cached const handles + smart-constructors for emitting proof terms.
struct PolyConsts {
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_of_rat: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    rat: Expr,
    rat_mk: Expr,
    int_of_nat: Expr,
    rat_zero: Expr,
    rat_le_of_ble_eq_true: Expr,
    bool_c: Expr,
    bool_true: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
    // Landed NNReal semiring lemmas.
    mul_comm: Expr,
    mul_assoc: Expr,
    add_comm: Expr,
    add_assoc: Expr,
    mul_add: Expr,
    add_mul: Expr,
    ofrat_mul: Expr,
    ofrat_add: Expr,
    mul_one: Expr,
}

impl PolyConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_of_rat: k("NNReal.ofRat"),
            #[cfg(test)]
            rat: k("Rat"),
            rat_mk: k("Rat.mk"),
            int_of_nat: k("Int.ofNat"),
            rat_zero: k("Rat.zero"),
            rat_le_of_ble_eq_true: k("Rat.le_of_ble_eq_true"),
            bool_c: k("Bool"),
            bool_true: k("Bool.true"),
            eq1: kl("Eq"),
            eq_refl1: kl("Eq.refl"),
            eq_symm1: kl("Eq.symm"),
            eq_trans1: kl("Eq.trans"),
            eq_subst1: kl("Eq.subst"),
            mul_comm: k("NNReal.mul_comm"),
            mul_assoc: k("NNReal.mul_assoc"),
            add_comm: k("NNReal.add_comm"),
            add_assoc: k("NNReal.add_assoc"),
            mul_add: k("NNReal.mul_add"),
            add_mul: k("NNReal.add_mul"),
            ofrat_mul: k("NNReal.ofRat_mul"),
            ofrat_add: k("NNReal.ofRat_add"),
            mul_one: k("NNReal.mul_one"),
        }
    }

    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nnadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    /// `Rat.mk (Int.ofNat num) den`.
    fn frac(&self, num: u128, den: u128) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), Expr::nat_lit(num as u64)),
                Expr::nat_lit(den as u64),
            ],
        )
    }
    /// `Eq.refl Bool Bool.true` — the `Rat.ble` reflection witness.
    fn refl_true(&self) -> Expr {
        Expr::apps(
            self.eq_refl1.clone(),
            [self.bool_c.clone(), self.bool_true.clone()],
        )
    }
    /// `0 ≤ Rat.mk num den` for a concrete nonneg literal (boolean reflection).
    fn lit_nonneg(&self, num: u128, den: u128) -> Expr {
        Expr::apps(
            self.rat_le_of_ble_eq_true.clone(),
            [self.rat_zero.clone(), self.frac(num, den), self.refl_true()],
        )
    }
    /// `NNReal.ofRat (Rat.mk num den) (0 ≤ …)`.
    fn ofrat(&self, num: u128, den: u128) -> Expr {
        Expr::apps(
            self.nnreal_of_rat.clone(),
            [self.frac(num, den), self.lit_nonneg(num, den)],
        )
    }
    // ── Eq.{1} over NNReal ──────────────────────────────────────────────────
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    fn refl_nn(&self, a: &Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.nnreal.clone(), a.clone()])
    }
    fn symm_nn(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
    fn trans_nn(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                cc.clone(),
                h1,
                h2,
            ],
        )
    }
    fn subst_nn(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }

    /// Chain `Eq.trans` over a non-empty list of `(lhs, rhs, proof)` steps whose
    /// rhs/lhs line up: `[(a,b,p1),(b,c,p2),…]` ⇒ `a = last`.
    fn chain(&self, steps: Vec<(Expr, Expr, Expr)>) -> (Expr, Expr, Expr) {
        let mut it = steps.into_iter();
        let (mut a, mut b, mut acc) = it.next().expect("chain: non-empty");
        let start = a.clone();
        for (b2, c, p) in it {
            debug_assert_eq!(b, b2, "chain: misaligned step");
            acc = self.trans_nn(&start, &b, &c, acc, p);
            b = c;
            let _ = &b2;
        }
        a = start;
        (a, b, acc)
    }

    // ── Congruence rewriting under `+`/`·` subterms (the Eq.cong idiom) ──────
    // Each rewrites ONE subterm of a binary node, holding the other fixed, via
    // `Eq.subst` with a one-hole motive (`fun z => Eq NN (orig) (node-with-z)`).

    /// From `h : p = q`, prove `p·a = q·a` (left factor rewrite).
    fn cong_mul_left(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        q: &Expr,
        a: &Expr,
        h: Expr,
    ) -> Expr {
        let pa = self.nnmul(p, a);
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = m.fresh_local(self.nnreal.clone());
            let body = self.eq_nn(&pa, &self.nnmul(&z, a));
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.subst_nn(motive, p, q, h, self.refl_nn(&pa))
    }
    /// From `h : p = q`, prove `a·p = a·q` (right factor rewrite).
    fn cong_mul_right(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        p: &Expr,
        q: &Expr,
        h: Expr,
    ) -> Expr {
        let ap = self.nnmul(a, p);
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = m.fresh_local(self.nnreal.clone());
            let body = self.eq_nn(&ap, &self.nnmul(a, &z));
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.subst_nn(motive, p, q, h, self.refl_nn(&ap))
    }
    /// From `h : p = q`, prove `p+a = q+a` (left summand rewrite).
    fn cong_add_left(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        q: &Expr,
        a: &Expr,
        h: Expr,
    ) -> Expr {
        let pa = self.nnadd(p, a);
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = m.fresh_local(self.nnreal.clone());
            let body = self.eq_nn(&pa, &self.nnadd(&z, a));
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.subst_nn(motive, p, q, h, self.refl_nn(&pa))
    }
    /// From `h : p = q`, prove `a+p = a+q` (right summand rewrite).
    fn cong_add_right(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        p: &Expr,
        q: &Expr,
        h: Expr,
    ) -> Expr {
        let ap = self.nnadd(a, p);
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = m.fresh_local(self.nnreal.clone());
            let body = self.eq_nn(&ap, &self.nnadd(a, &z));
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.subst_nn(motive, p, q, h, self.refl_nn(&ap))
    }

    // ── Landed lemma applications (exact argument orders) ───────────────────
    /// `NNReal.mul_comm a b : a·b = b·a`.
    fn lem_mul_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.mul_assoc a b c : a·(b·c) = (a·b)·c`.
    fn lem_mul_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a.clone(), b.clone(), cc.clone()])
    }
    /// `NNReal.add_comm a b : a+b = b+a`.
    fn lem_add_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.add_comm.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.add_assoc a b c : (a+b)+c = a+(b+c)`.
    fn lem_add_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(self.add_assoc.clone(), [a.clone(), b.clone(), cc.clone()])
    }
    /// `NNReal.mul_add c a b : c·(a+b) = c·a + c·b`.
    fn lem_mul_add(&self, c: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.mul_add.clone(), [c.clone(), a.clone(), b.clone()])
    }
    /// `NNReal.add_mul a b c : (a+b)·c = a·c + b·c`.
    fn lem_add_mul(&self, a: &Expr, b: &Expr, c: &Expr) -> Expr {
        Expr::apps(self.add_mul.clone(), [a.clone(), b.clone(), c.clone()])
    }
    /// `NNReal.mul_one a : a · ofRat 1 = a`.
    fn lem_mul_one(&self, a: &Expr) -> Expr {
        Expr::apps(self.mul_one.clone(), [a.clone()])
    }
    /// `NNReal.ofRat_mul a b ha hb hab : ofRat a · ofRat b = ofRat (a·b)`.
    fn lem_ofrat_mul(&self, (n1, d1): (u128, u128), (n2, d2): (u128, u128)) -> Expr {
        let ra = self.frac(n1, d1);
        let rb = self.frac(n2, d2);
        let ha = self.lit_nonneg(n1, d1);
        let hb = self.lit_nonneg(n2, d2);
        let (np, dp) = rat_mul((n1, d1), (n2, d2));
        let hab = self.lit_nonneg(np, dp);
        Expr::apps(self.ofrat_mul.clone(), [ra, rb, ha, hb, hab])
    }
    /// `NNReal.ofRat_add a b ha hb hab : ofRat a + ofRat b = ofRat (a+b)`.
    fn lem_ofrat_add(&self, (n1, d1): (u128, u128), (n2, d2): (u128, u128)) -> Expr {
        let ra = self.frac(n1, d1);
        let rb = self.frac(n2, d2);
        let ha = self.lit_nonneg(n1, d1);
        let hb = self.lit_nonneg(n2, d2);
        let (ns, ds) = rat_add((n1, d1), (n2, d2));
        let hab = self.lit_nonneg(ns, ds);
        Expr::apps(self.ofrat_add.clone(), [ra, rb, ha, hb, hab])
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Canonical-expression layout (a deterministic function of a Poly).
// ─────────────────────────────────────────────────────────────────────────────

/// Right-associated product of atom `FVar`s `x₁·(x₂·…·xₖ)`. PRECONDITION:
/// non-empty.
fn atom_prod(c: &PolyConsts, atoms: &[u64]) -> Expr {
    let (last, init) = atoms.split_last().expect("atom_prod: non-empty");
    let mut acc = Expr::fvar(FVarId::new(*last));
    for id in init.iter().rev() {
        acc = c.nnmul(&Expr::fvar(FVarId::new(*id)), &acc);
    }
    acc
}

/// Canonical expression of a single monomial:
///   * `[]`        → `ofRat coeff`,
///   * `[x₁,…,xₖ]`  → `(x₁·(x₂·…·xₖ)) · ofRat coeff`  (coeff on the RIGHT, so the
///                     unit drop uses `NNReal.mul_one`).
fn mono_expr(c: &PolyConsts, m: &Mono) -> Expr {
    let coeff = c.ofrat(m.num, m.den);
    if m.atoms.is_empty() {
        coeff
    } else {
        c.nnmul(&atom_prod(c, &m.atoms), &coeff)
    }
}

/// Canonical expression of a whole poly: right-associated sum of monomial
/// exprs. The empty poly is `ofRat 0`.
fn poly_expr(c: &PolyConsts, p: &Poly) -> Expr {
    if p.is_empty() {
        return c.ofrat(0, 1);
    }
    let (last, init) = p.split_last().expect("poly_expr: non-empty");
    let mut acc = mono_expr(c, last);
    for m in init.iter().rev() {
        acc = c.nnadd(&mono_expr(c, m), &acc);
    }
    acc
}

// ─────────────────────────────────────────────────────────────────────────────
// Polynomial algebra (mirrors the kernel's free-representative arithmetic).
// ─────────────────────────────────────────────────────────────────────────────

/// Insert a monomial into a canonical poly, merging like-atom monomials by
/// adding their coefficients (free-representative add).
fn poly_insert(mut p: Poly, m: Mono) -> Poly {
    if let Some(slot) = p.iter_mut().find(|e| e.atoms == m.atoms) {
        let (n, d) = rat_add((slot.num, slot.den), (m.num, m.den));
        slot.num = n;
        slot.den = d;
    } else {
        p.push(m);
    }
    p.sort_by(|a, b| atom_key_cmp(&a.atoms, &b.atoms));
    p
}

/// `p ⊕ q` (canonical).
fn poly_add(mut p: Poly, q: Poly) -> Poly {
    for m in q {
        p = poly_insert(p, m);
    }
    p
}

/// `p ⊗ q` (canonical): pairwise monomial products, merged.
fn poly_mul(p: &Poly, q: &Poly) -> Poly {
    let mut out: Poly = Vec::new();
    for a in p {
        for b in q {
            let (n, d) = rat_mul((a.num, a.den), (b.num, b.den));
            let mut atoms = a.atoms.clone();
            atoms.extend_from_slice(&b.atoms);
            atoms.sort_unstable();
            out = poly_insert(
                out,
                Mono {
                    num: n,
                    den: d,
                    atoms,
                },
            );
        }
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// normalize: structural recursion producing (Poly, proof : e = canon(Poly)).
// ─────────────────────────────────────────────────────────────────────────────

/// Recognize a literal `NNReal.ofRat (Rat.mk (Int.ofNat n) d) _` and return
/// `(n, d)`. Returns `None` for non-literal `ofRat` arguments.
fn match_ofrat_literal(e: &Expr) -> Option<(u128, u128)> {
    let (head, args) = uncurry(e);
    if !is_const(head, "NNReal.ofRat") || args.len() != 2 {
        return None;
    }
    // args[0] = Rat.mk (Int.ofNat n) d
    let (mkh, mka) = uncurry(args[0]);
    if !is_const(mkh, "Rat.mk") || mka.len() != 2 {
        return None;
    }
    let n = match_int_ofnat(mka[0])?;
    let d = match_nat_lit(mka[1])?;
    Some((n, d))
}

fn match_int_ofnat(e: &Expr) -> Option<u128> {
    let (h, a) = uncurry(e);
    if is_const(h, "Int.ofNat") && a.len() == 1 {
        match_nat_lit(a[0])
    } else {
        None
    }
}

fn match_nat_lit(e: &Expr) -> Option<u128> {
    use crate::expr::{BigNat, Literal};
    match e.kind() {
        ExprKind::Lit(Literal::Nat(BigNat::Small(n))) => Some(*n as u128),
        _ => None,
    }
}

fn is_const(e: &Expr, name: &str) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == name)
}

/// Flatten an application spine `f a₁ … aₙ` into `(f, [a₁,…,aₙ])`.
fn uncurry(e: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut cur = e;
    while let ExprKind::App(f, a) = cur.kind() {
        args.push(a.as_ref());
        cur = f.as_ref();
    }
    args.reverse();
    (cur, args)
}

/// Recursive normalizer. Returns `(poly, proof : Eq NNReal e (poly_expr poly))`,
/// or `None` if `e` is outside the modelled grammar.
fn normalize(c: &PolyConsts, parent: &EnvDeclBuilder, e: &Expr) -> Option<(Poly, Expr)> {
    // ofRat literal coefficient.
    if let Some((n, d)) = match_ofrat_literal(e) {
        let poly = vec![Mono {
            num: n,
            den: d,
            atoms: vec![],
        }];
        // canon == e (same ofRat literal) ⇒ refl.
        return Some((poly, c.refl_nn(e)));
    }
    // Atom FVar.
    if let ExprKind::FVar(id) = e.kind() {
        let poly = vec![Mono {
            num: 1,
            den: 1,
            atoms: vec![id.as_u64()],
        }];
        // canon = x · ofRat 1 ; mul_one : x · ofRat 1 = x ; symm ⇒ x = canon.
        let canon = poly_expr(c, &poly);
        let proof = c.symm_nn(&canon, e, c.lem_mul_one(e));
        return Some((poly, proof));
    }
    // Binary node.
    let (head, args) = uncurry(e);
    if args.len() == 2 {
        if is_const(head, "NNReal.add") {
            return normalize_add(c, parent, e, args[0], args[1]);
        }
        if is_const(head, "NNReal.mul") {
            return normalize_mul(c, parent, e, args[0], args[1]);
        }
    }
    None
}

/// `normalize` for `e = add l r`.
fn normalize_add(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    e: &Expr,
    l: &Expr,
    r: &Expr,
) -> Option<(Poly, Expr)> {
    let (pl, proof_l) = normalize(c, parent, l)?;
    let (pr, proof_r) = normalize(c, parent, r)?;
    let canon_l = poly_expr(c, &pl);
    let canon_r = poly_expr(c, &pr);

    // step A: (l + r) = (canon_l + r)        [cong_add_left proof_l]
    let mid1 = c.nnadd(&canon_l, r);
    let sa = c.cong_add_left(parent, l, &canon_l, r, proof_l);
    // step B: (canon_l + r) = (canon_l + canon_r)   [cong_add_right proof_r]
    let mid2 = c.nnadd(&canon_l, &canon_r);
    let sb = c.cong_add_right(parent, &canon_l, r, &canon_r, proof_r);

    // step C: (canon_l + canon_r) = canon(pl ⊕ pr)  [structural concat+reorder]
    let merged = poly_add(pl.clone(), pr.clone());
    let canon_merged = poly_expr(c, &merged);
    let sc = prove_sum_merge(c, parent, &pl, &pr)?;

    let (a, b, p) = c.chain(vec![
        (e.clone(), mid1.clone(), sa),
        (mid1, mid2.clone(), sb),
        (mid2, canon_merged.clone(), sc),
    ]);
    debug_assert_eq!(a, *e);
    debug_assert_eq!(b, canon_merged);
    Some((merged, p))
}

/// `normalize` for `e = mul l r`.
fn normalize_mul(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    e: &Expr,
    l: &Expr,
    r: &Expr,
) -> Option<(Poly, Expr)> {
    let (pl, proof_l) = normalize(c, parent, l)?;
    let (pr, proof_r) = normalize(c, parent, r)?;
    let canon_l = poly_expr(c, &pl);
    let canon_r = poly_expr(c, &pr);

    // step A: (l · r) = (canon_l · r)
    let mid1 = c.nnmul(&canon_l, r);
    let sa = c.cong_mul_left(parent, l, &canon_l, r, proof_l);
    // step B: (canon_l · r) = (canon_l · canon_r)
    let mid2 = c.nnmul(&canon_l, &canon_r);
    let sb = c.cong_mul_right(parent, &canon_l, r, &canon_r, proof_r);

    // step C: (canon_l · canon_r) = canon(pl ⊗ pr)
    let product = poly_mul(&pl, &pr);
    let canon_prod = poly_expr(c, &product);
    let sc = prove_prod_merge(c, parent, &pl, &pr)?;

    let (a, b, p) = c.chain(vec![
        (e.clone(), mid1.clone(), sa),
        (mid1, mid2.clone(), sb),
        (mid2, canon_prod.clone(), sc),
    ]);
    debug_assert_eq!(a, *e);
    debug_assert_eq!(b, canon_prod);
    Some((product, p))
}

// ─────────────────────────────────────────────────────────────────────────────
// Structural rewrites that normalize already-canonical operands.
//
// `prove_sum_merge`/`prove_prod_merge` prove that the canonical sum/product of
// two ALREADY-canonical polys equals the canonical poly of their ⊕/⊗. These are
// the heart of the ring normalizer; built by reusing the SAME normalizer
// machinery indirectly through small, well-typed lemma chains.
// ─────────────────────────────────────────────────────────────────────────────

/// Prove `canon(p) + canon(q) = canon(p ⊕ q)` for canonical `p`, `q`.
///
/// Strategy: it suffices to prove that the *flattened concatenation* of the two
/// right-associated sums reorders/merges into the canonical sum. We do this by a
/// **monomial-by-monomial insertion**: fold `q`'s monomials into `p` one at a
/// time, each insertion justified by `add_assoc`/`add_comm` rewrites plus (when
/// the atoms collide) an `ofRat_add` coefficient fold under `mul`-congruence.
fn prove_sum_merge(c: &PolyConsts, parent: &EnvDeclBuilder, p: &Poly, q: &Poly) -> Option<Expr> {
    // Base: q empty ⇒ canon(p) + ofRat 0 = canon(p). We avoid needing add_zero
    // for the helper's grammar by never producing an empty q here unless p∪q is
    // also handled; route through the general builder.
    let lhs = c.nnadd(&poly_expr(c, p), &poly_expr(c, q));
    let mut acc_poly = p.clone();
    // current expression we have proven `lhs = current`
    let mut current = lhs.clone();
    let mut proof = c.refl_nn(&lhs);

    // We process q as a right-associated sum: m0 + (m1 + ( … )). Peel one at a
    // time off the FRONT, append to the accumulated p-sum via add_assoc, then
    // insert into canonical position.
    // For simplicity and robustness we rebuild from scratch: prove
    // `canon(p) + canon(q) = canon(p) ⊕-inserted q` by inserting each q-mono.
    let q_monos = q.clone();
    // Detach: we need to move each leading q-mono out of canon(q). Represent the
    // remaining q-tail explicitly.
    let mut remaining: Poly = q_monos;

    while !remaining.is_empty() {
        // current == canon(acc_poly) + canon(remaining)  (right-assoc q-sum)
        let head = remaining[0].clone();
        let tail: Poly = remaining[1..].to_vec();

        // (1) Peel: canon(acc) + canon(remaining)
        //          = canon(acc) + (mono(head) + canon(tail))         [refl, layout]
        //          = (canon(acc) + mono(head)) + canon(tail)         [add_assoc⁻¹]
        // When tail empty, canon(remaining) == mono(head) directly (no inner +).
        let acc_e = poly_expr(c, &acc_poly);
        let head_e = mono_expr(c, &head);

        let step_after_peel: Expr;
        let next_current: Expr;
        if tail.is_empty() {
            // current == acc_e + head_e  already. Now insert head into acc.
            let (inserted_poly, ins_proof) = prove_insert_mono(c, parent, &acc_poly, &head)?;
            // ins_proof : acc_e + head_e = canon(inserted_poly)
            let target = poly_expr(c, &inserted_poly);
            proof = c.trans_nn(&lhs, &current, &target, proof, ins_proof);
            acc_poly = inserted_poly;
            current = target;
            remaining = tail;
            continue;
        } else {
            // current == acc_e + (head_e + canon(tail))
            let tail_e = poly_expr(c, &tail);
            let inner = c.nnadd(&head_e, &tail_e);
            // add_assoc acc head_sum? We need (acc + (head + tail)) = ((acc+head)+tail)
            // NNReal.add_assoc a b c : (a+b)+c = a+(b+c). symm gives a+(b+c)=(a+b)+c.
            let assoc = c.lem_add_assoc(&acc_e, &head_e, &tail_e); // (acc+head)+tail = acc+(head+tail)
            let lhs_assoc = c.nnadd(&c.nnadd(&acc_e, &head_e), &tail_e);
            let rhs_assoc = c.nnadd(&acc_e, &inner);
            let assoc_symm = c.symm_nn(&lhs_assoc, &rhs_assoc, assoc);
            // current (== rhs_assoc) = lhs_assoc
            step_after_peel = assoc_symm;
            next_current = lhs_assoc;
            proof = c.trans_nn(&lhs, &current, &next_current, proof, step_after_peel);
            current = next_current;
            // Now current == (acc + head) + tail. Insert head into acc:
            let acc_plus_head = c.nnadd(&acc_e, &head_e);
            let (inserted_poly, ins_proof) = prove_insert_mono(c, parent, &acc_poly, &head)?;
            // ins_proof : acc_e + head_e = canon(inserted_poly)
            let inserted_e = poly_expr(c, &inserted_poly);
            // rewrite LEFT summand of (acc+head)+tail via ins_proof
            let cong = c.cong_add_left(parent, &acc_plus_head, &inserted_e, &tail_e, ins_proof);
            let new_current = c.nnadd(&inserted_e, &tail_e);
            proof = c.trans_nn(&lhs, &current, &new_current, proof, cong);
            current = new_current;
            acc_poly = inserted_poly;
            remaining = tail;
        }
    }

    // Now current == canon(acc_poly) where acc_poly == p ⊕ q (as a multiset of
    // monomials). But canonical ORDER may differ if insertion order produced a
    // different sort; poly_insert always re-sorts, so acc_poly is canonical and
    // equals poly_add(p,q). current == poly_expr(acc_poly).
    let final_poly = poly_add(p.clone(), q.clone());
    debug_assert_eq!(acc_poly, final_poly, "sum_merge poly mismatch");
    let final_e = poly_expr(c, &final_poly);
    debug_assert_eq!(current, final_e, "sum_merge expr mismatch");
    Some(proof)
}

/// Prove `canon(acc) + mono(head) = canon(acc ⊕ {head})` for canonical `acc`.
///
/// Two cases:
///   * head's atoms are NEW   → the result poly is `acc` with `head` spliced in
///     at its sorted position; we bubble `mono(head)` from the tail to that
///     position via `add_comm`/`add_assoc`.
///   * head's atoms COLLIDE with an existing monomial `mᵢ` → we bubble
///     `mono(head)` next to `mono(mᵢ)`, then fold the two coefficients with
///     `ofRat_add` under the appropriate `mul`-congruence.
fn prove_insert_mono(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    acc: &Poly,
    head: &Mono,
) -> Option<(Poly, Expr)> {
    let acc_e = poly_expr(c, acc);
    let head_e = mono_expr(c, head);
    let lhs = c.nnadd(&acc_e, &head_e);
    let result = poly_insert(acc.clone(), head.clone());

    // Collision? find existing index with same atoms.
    if let Some(idx) = acc.iter().position(|m| m.atoms == head.atoms) {
        // Bubble head_e so it is adjacent to acc[idx], fold coeffs.
        let proof = prove_insert_collide(c, parent, acc, head, idx, &lhs)?;
        return Some((result, proof));
    }

    // No collision: result = sorted(acc ++ [head]).
    let result_e = poly_expr(c, &result);
    // Prove acc_e + head_e = result_e by reordering the flat sum.
    let proof = prove_sum_reorder(c, parent, &lhs, &result_e)?;
    Some((result, proof))
}

/// Collision insert: `canon(acc) + mono(head) = canon(acc with mᵢ coeff += head)`.
fn prove_insert_collide(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    acc: &Poly,
    head: &Mono,
    idx: usize,
    lhs: &Expr,
) -> Option<Expr> {
    let mi = acc[idx].clone();
    let acc_e = poly_expr(c, acc);
    let head_e = mono_expr(c, head);

    // (1) Reorder so that mono(mᵢ) and mono(head) are adjacent and at the FRONT:
    //     acc_e + head_e  =  mono(mᵢ) + mono(head) + (rest)
    // where rest = canon(acc without mᵢ). We build the target multiset-sum
    // expression and prove equality by the generic reorder prover.
    let mut rest_poly = acc.clone();
    rest_poly.remove(idx);
    let folded = {
        let (n, d) = rat_add((mi.num, mi.den), (head.num, head.den));
        Mono {
            num: n,
            den: d,
            atoms: mi.atoms.clone(),
        }
    };

    // Target poly after fold (canonical):
    let mut result_poly = rest_poly.clone();
    result_poly = poly_insert(result_poly, folded.clone());
    let result_e = poly_expr(c, &result_poly);

    let mi_e = mono_expr(c, &mi);
    let pair_e = c.nnadd(&mi_e, &head_e); // mono(mi) + mono(head)
    let folded_e = mono_expr(c, &folded);
    let fold = prove_mono_coeff_fold(c, parent, &mi, head)?; // pair_e = folded_e

    if rest_poly.is_empty() {
        // lhs is some permutation of {mono(mi), mono(head)}; reorder to pair_e,
        // then fold.
        let s1 = prove_sum_reorder(c, parent, lhs, &pair_e)?;
        let (_, _, p) = c.chain(vec![
            (lhs.clone(), pair_e.clone(), s1),
            (pair_e, folded_e.clone(), fold),
        ]);
        let _ = &acc_e;
        return Some(p);
    }

    // rest non-empty. Right-assoc intermediate: mono(mi) + (mono(head) + rest).
    let rest_e = poly_expr(c, &rest_poly);
    let head_plus_rest = c.nnadd(&head_e, &rest_e);
    let grouped_ra = c.nnadd(&mi_e, &head_plus_rest); // mi + (head + rest)  [right-assoc]

    // step1: lhs = grouped_ra   (reorder; target is right-assoc).
    let s1 = prove_sum_reorder(c, parent, lhs, &grouped_ra)?;

    // step2: mi + (head + rest) = (mi + head) + rest   [add_assoc symm]
    let pair_plus_rest = c.nnadd(&pair_e, &rest_e);
    let assoc = c.lem_add_assoc(&mi_e, &head_e, &rest_e); // (mi+head)+rest = mi+(head+rest)
    let s2 = c.symm_nn(&pair_plus_rest, &grouped_ra, assoc); // grouped_ra = (mi+head)+rest

    // step3: fold the (mi+head) left summand → folded.
    let s3 = c.cong_add_left(parent, &pair_e, &folded_e, &rest_e, fold);
    let folded_plus_rest = c.nnadd(&folded_e, &rest_e);

    // step4: reorder folded + rest into the canonical result_e.
    let s4 = prove_sum_reorder(c, parent, &folded_plus_rest, &result_e)?;

    let (_, _, p) = c.chain(vec![
        (lhs.clone(), grouped_ra.clone(), s1),
        (grouped_ra, pair_plus_rest.clone(), s2),
        (pair_plus_rest, folded_plus_rest.clone(), s3),
        (folded_plus_rest, result_e.clone(), s4),
    ]);
    let _ = &acc_e;
    Some(p)
}

/// Fold two same-atom monomials' coefficients:
/// `mono(coeff a, atoms) + mono(coeff b, atoms) = mono(coeff a⊕b, atoms)`.
///
///   * atoms empty: `ofRat a + ofRat b = ofRat (a⊕b)`   [ofRat_add directly]
///   * atoms = P:   `(P·ofRat a) + (P·ofRat b)`
///                = `P·(ofRat a + ofRat b)`              [mul_add⁻¹, via comm]
///                ... here the layout is `(P · ofRat a)` so the common factor
///                P is on the LEFT; `add_mul⁻¹` gives `P·a + P·b = ... ` — we use
///                the distribute lemma in reverse and then `ofRat_add`.
fn prove_mono_coeff_fold(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    a: &Mono,
    b: &Mono,
) -> Option<Expr> {
    debug_assert_eq!(a.atoms, b.atoms);
    let coeff_a = (a.num, a.den);
    let coeff_b = (b.num, b.den);
    let (ns, ds) = rat_add(coeff_a, coeff_b);

    if a.atoms.is_empty() {
        // ofRat a + ofRat b = ofRat (a⊕b)
        return Some(c.lem_ofrat_add(coeff_a, coeff_b));
    }

    // P := atom_prod(atoms). lhs = (P · ofRat a) + (P · ofRat b).
    let pexpr = atom_prod(c, &a.atoms);
    let ofa = c.ofrat(a.num, a.den);
    let ofb = c.ofrat(b.num, b.den);
    let term_a = c.nnmul(&pexpr, &ofa);
    let term_b = c.nnmul(&pexpr, &ofb);
    let lhs = c.nnadd(&term_a, &term_b);

    // add_mul a' b' c' : (a'+b')·c' = a'·c' + b'·c'.  Set a'=ofRat a, b'=ofRat b,
    // c'=P : (ofRat a + ofRat b)·P = (ofRat a)·P + (ofRat b)·P.
    // But our terms are P·ofRat a, not (ofRat a)·P. Bridge by mul_comm on each.
    // Easier: use mul_add with c=P on the LEFT? mul_add c a b : c·(a+b)=c·a+c·b.
    // Our terms are P·ofRat a = c·a with c=P. So:
    //   mul_add P (ofRat a)(ofRat b) : P·(ofRat a + ofRat b) = P·ofRat a + P·ofRat b
    // symm ⇒ lhs = P·(ofRat a + ofRat b).
    let sum_of = c.nnadd(&ofa, &ofb);
    let p_times_sum = c.nnmul(&pexpr, &sum_of);
    let mul_add = c.lem_mul_add(&pexpr, &ofa, &ofb); // p·(a+b) = p·a + p·b
    let rhs_mul_add = c.nnadd(&term_a, &term_b);
    let s1 = c.symm_nn(&p_times_sum, &rhs_mul_add, mul_add); // lhs = p·(a+b)

    // fold coeff: ofRat a + ofRat b = ofRat(a⊕b)  ; rewrite right factor of mul.
    let ofsum = c.ofrat(ns, ds);
    let fold = c.lem_ofrat_add(coeff_a, coeff_b); // (ofRat a + ofRat b) = ofRat(a⊕b)
    let s2 = c.cong_mul_right(parent, &pexpr, &sum_of, &ofsum, fold); // p·(a+b) = p·ofRat(sum)

    let folded_term = c.nnmul(&pexpr, &ofsum); // == mono_expr(folded)
    let (_, _, proof) = c.chain(vec![
        (lhs.clone(), p_times_sum.clone(), s1),
        (p_times_sum, folded_term.clone(), s2),
    ]);
    Some(proof)
}

/// Prove that two NNReal `add`-sums over the SAME multiset of summand exprs are
/// equal: `from = to`, where both are right-associated sums whose summands are a
/// permutation of one another. Implemented by selection sort: repeatedly bring
/// the head summand of `to` to the front of the current sum via add_comm/assoc.
///
/// PRECONDITION: `from` and `to` are right-associated `add`-trees with the same
/// multiset of leaf summands (each leaf an opaque NNReal expr); leaves compared
/// by structural `Expr` equality.
fn prove_sum_reorder(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    from0: &Expr,
    to: &Expr,
) -> Option<Expr> {
    if from0 == to {
        return Some(c.refl_nn(from0));
    }
    // Reassociate `from0` to a right-associated sum first (so the selection-sort
    // machinery, which assumes right-assoc, applies). `to` is always built
    // right-assoc by the callers.
    let (from, reassoc_proof) = reassoc_add_right(c, parent, from0)?;
    if from == *to {
        return Some(reassoc_proof);
    }
    let from = &from;
    let to_leaves = split_add_sum(c, to);
    // Bring to_leaves[0] to the front of `from`, then recurse on the tails.
    let (head_target, _rest_target) = to_leaves.split_first()?;
    // Prove from = head_target + rest_of_from
    let (bring_proof, after_bring) = bring_to_front(c, parent, from, head_target)?;
    // after_bring == head_target + tail_from. Recurse: prove tail_from = rest_to.
    let from_leaves = split_add_sum(c, &after_bring);
    if from_leaves.is_empty() {
        return None;
    }
    let tail_from = rebuild_sum(c, &from_leaves[1..])?;
    let tail_to = rebuild_sum(c, &to_leaves[1..])?;
    let tail_proof = prove_sum_reorder(c, parent, &tail_from, &tail_to)?;
    // rewrite right summand: head + tail_from = head + tail_to
    let cong = c.cong_add_right(parent, head_target, &tail_from, &tail_to, tail_proof);
    let after_cong = c.nnadd(head_target, &tail_to);
    debug_assert_eq!(after_cong, *to);
    let (_, _, proof) = c.chain(vec![
        (from0.clone(), from.clone(), reassoc_proof),
        (from.clone(), after_bring.clone(), bring_proof),
        (after_bring, to.clone(), cong),
    ]);
    Some(proof)
}

/// Split a right-associated `add`-sum into its leaf summands (left-to-right).
fn split_add_sum(c: &PolyConsts, e: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    let mut cur = e.clone();
    loop {
        let (head, args) = uncurry(&cur);
        if is_const(head, "NNReal.add") && args.len() == 2 {
            out.push(args[0].clone());
            let next = args[1].clone();
            cur = next;
        } else {
            out.push(cur.clone());
            break;
        }
    }
    let _ = c;
    out
}

/// Fully flatten an `add`-tree of ANY association into its leaf summands
/// (left-to-right).
fn flatten_add_full(_c: &PolyConsts, e: &Expr) -> Vec<Expr> {
    fn go(e: &Expr, out: &mut Vec<Expr>) {
        let (head, args) = uncurry(e);
        if is_const(head, "NNReal.add") && args.len() == 2 {
            go(args[0], out);
            go(args[1], out);
        } else {
            out.push(e.clone());
        }
    }
    let mut out = Vec::new();
    go(e, &mut out);
    out
}

/// Reassociate an `add`-tree into the right-associated sum over its leaves.
/// Returns `(right_assoc_expr, proof : e = right_assoc_expr)`.
fn reassoc_add_right(c: &PolyConsts, parent: &EnvDeclBuilder, e: &Expr) -> Option<(Expr, Expr)> {
    let leaves = flatten_add_full(c, e);
    let ra = rebuild_sum(c, &leaves)?;
    if ra == *e {
        return Some((ra, c.refl_nn(e)));
    }
    let proof = prove_add_reassoc_eq(c, parent, e, &ra)?;
    Some((ra, proof))
}

/// Prove `e = ra` where both are sums over the same ordered leaf sequence, `ra`
/// fully right-associated. Recursive: peel `e`'s head, reassociate.
fn prove_add_reassoc_eq(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    e: &Expr,
    ra: &Expr,
) -> Option<Expr> {
    if e == ra {
        return Some(c.refl_nn(e));
    }
    let (head, args) = uncurry(e);
    if !is_const(head, "NNReal.add") || args.len() != 2 {
        return if e == ra { Some(c.refl_nn(e)) } else { None };
    }
    let x = args[0].clone();
    let y = args[1].clone();
    // If X is itself a sum (X = X1+X2), rotate via add_assoc:
    //   add_assoc X1 X2 Y : (X1+X2)+Y = X1+(X2+Y).
    let (xh, xa) = uncurry(&x);
    if is_const(xh, "NNReal.add") && xa.len() == 2 {
        let x1 = xa[0].clone();
        let x2 = xa[1].clone();
        let assoc = c.lem_add_assoc(&x1, &x2, &y); // (X1+X2)+Y = X1+(X2+Y)
        let rhs_assoc = c.nnadd(&x1, &c.nnadd(&x2, &y));
        let rec = prove_add_reassoc_eq(c, parent, &rhs_assoc, ra)?;
        let (_, _, proof) = c.chain(vec![
            (e.clone(), rhs_assoc.clone(), assoc),
            (rhs_assoc, ra.clone(), rec),
        ]);
        return Some(proof);
    }
    // X is a leaf: e = X + Y; ra should be X + (reassoc Y).
    let (rah, raa) = uncurry(ra);
    if is_const(rah, "NNReal.add") && raa.len() == 2 && *raa[0] == x {
        let ra_tail = raa[1].clone();
        let y_proof = prove_add_reassoc_eq(c, parent, &y, &ra_tail)?;
        let cong = c.cong_add_right(parent, &x, &y, &ra_tail, y_proof);
        return Some(cong);
    }
    None
}

/// Rebuild a right-associated `add`-sum from leaves. Empty ⇒ None.
fn rebuild_sum(c: &PolyConsts, leaves: &[Expr]) -> Option<Expr> {
    let (last, init) = leaves.split_last()?;
    let mut acc = last.clone();
    for l in init.iter().rev() {
        acc = c.nnadd(l, &acc);
    }
    Some(acc)
}

/// Prove `from = target + tail` where `target` is one of the leaf summands of
/// the right-associated sum `from`; returns `(proof, target + tail_expr)`.
fn bring_to_front(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    from: &Expr,
    target: &Expr,
) -> Option<(Expr, Expr)> {
    let leaves = split_add_sum(c, from);
    let pos = leaves.iter().position(|l| l == target)?;
    if pos == 0 {
        return Some((c.refl_nn(from), from.clone()));
    }
    // Remove leaf at pos, put it at front: build target + (rest in order).
    let mut rest: Vec<Expr> = leaves.clone();
    let removed = rest.remove(pos);
    debug_assert_eq!(removed, *target);
    let tail = rebuild_sum(c, &rest)?;
    let result = c.nnadd(target, &tail);
    // Prove from = result by a swap chain. Simplest robust route: both are sums
    // over the same leaves; prove via repeated adjacent swaps moving `target`
    // left. We implement a direct cons/rotate proof.
    let proof = prove_move_leaf_front(c, parent, from, pos)?;
    Some((proof, result))
}

/// Prove `from = (leafₚₒₛ) + (rest of leaves in order)`, moving the leaf at
/// `pos` (>0) to the front of the right-associated sum `from`. Adjacent-swap
/// bubble using `add_comm`/`add_assoc`.
fn prove_move_leaf_front(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    from: &Expr,
    pos: usize,
) -> Option<Expr> {
    // Move leaf left one step at a time: positions pos -> pos-1 -> … -> 0.
    let mut current = from.clone();
    let mut proof = c.refl_nn(from);
    let mut p = pos;
    while p > 0 {
        let (swapped, step) = swap_adjacent(c, parent, &current, p - 1)?;
        proof = c.trans_nn(from, &current, &swapped, proof, step);
        current = swapped;
        p -= 1;
    }
    Some(proof)
}

/// Swap leaves at index `i` and `i+1` of a right-associated sum; return
/// `(new_sum, proof : current = new_sum)`.
///
/// The sum from index `i` onward is `Lᵢ + (Lᵢ₊₁ + T)` (T possibly absent).
///   * if T present: `Lᵢ + (Lᵢ₊₁ + T) = (Lᵢ + Lᵢ₊₁) + T   [add_assoc⁻¹]`
///                  `= (Lᵢ₊₁ + Lᵢ) + T                     [add_comm on pair]`
///                  `= Lᵢ₊₁ + (Lᵢ + T)                     [add_assoc]`
///   * if T absent: `Lᵢ + Lᵢ₊₁ = Lᵢ₊₁ + Lᵢ                [add_comm]`
///
/// Performed under the prefix context `L₀+(…+(here))` via right-summand
/// congruence.
fn swap_adjacent(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    current: &Expr,
    i: usize,
) -> Option<(Expr, Expr)> {
    let leaves = split_add_sum(c, current);
    if i + 1 >= leaves.len() {
        return None;
    }
    // Build the sub-sum from index i onward and its swapped form; prove locally,
    // then lift under the prefix via nested cong_add_right.
    let li = leaves[i].clone();
    let lj = leaves[i + 1].clone();
    let has_tail = i + 2 < leaves.len();
    let tail = if has_tail {
        Some(rebuild_sum(c, &leaves[i + 2..])?)
    } else {
        None
    };

    let (sub_from, sub_to, sub_proof) = if let Some(t) = &tail {
        // Li + (Lj + T)
        let inner = c.nnadd(&lj, t);
        let sub_from = c.nnadd(&li, &inner);
        // (Li+Lj)+T
        let li_lj = c.nnadd(&li, &lj);
        let assoc_lhs = c.nnadd(&li_lj, t);
        let assoc = c.lem_add_assoc(&li, &lj, t); // (Li+Lj)+T = Li+(Lj+T)
        let s1 = c.symm_nn(&assoc_lhs, &sub_from, assoc); // sub_from = (Li+Lj)+T
                                                          // (Lj+Li)+T via add_comm on the pair, under left-summand cong
        let lj_li = c.nnadd(&lj, &li);
        let comm = c.lem_add_comm(&li, &lj); // Li+Lj = Lj+Li
        let s2 = c.cong_add_left(parent, &li_lj, &lj_li, t, comm); // (Li+Lj)+T = (Lj+Li)+T
        let comm_lhs = c.nnadd(&lj_li, t);
        // (Lj+Li)+T = Lj+(Li+T)  [add_assoc]
        let assoc2 = c.lem_add_assoc(&lj, &li, t); // (Lj+Li)+T = Lj+(Li+T)
        let li_t = c.nnadd(&li, t);
        let sub_to = c.nnadd(&lj, &li_t);
        let (_, _, p) = c.chain(vec![
            (sub_from.clone(), assoc_lhs.clone(), s1),
            (assoc_lhs, comm_lhs.clone(), s2),
            (comm_lhs, sub_to.clone(), assoc2),
        ]);
        (sub_from, sub_to, p)
    } else {
        // Li + Lj = Lj + Li
        let sub_from = c.nnadd(&li, &lj);
        let sub_to = c.nnadd(&lj, &li);
        let comm = c.lem_add_comm(&li, &lj);
        (sub_from, sub_to, comm)
    };

    // Lift sub_proof under the prefix L0 + (L1 + ( … + [sub] )) via nested
    // right-summand congruence.
    let mut proof = sub_proof;
    let mut from_e = sub_from;
    let mut to_e = sub_to;
    for k in (0..i).rev() {
        let prefix_leaf = leaves[k].clone();
        proof = c.cong_add_right(parent, &prefix_leaf, &from_e, &to_e, proof);
        from_e = c.nnadd(&prefix_leaf, &from_e);
        to_e = c.nnadd(&prefix_leaf, &to_e);
    }
    debug_assert_eq!(from_e, *current);
    Some((to_e, proof))
}

/// Prove `canon(p) · canon(q) = canon(p ⊗ q)` for canonical `p`, `q`.
///
/// Distribute the two sums fully (`mul_add`/`add_mul`), normalizing each
/// monomial×monomial product to canonical monomial layout, then SUM-merge the
/// resulting monomials via `prove_sum_merge`-style reordering.
fn prove_prod_merge(c: &PolyConsts, parent: &EnvDeclBuilder, p: &Poly, q: &Poly) -> Option<Expr> {
    // Reduce to a flat list of monomial-product terms by distribution, proving
    // canon(p)·canon(q) = Σ_{i,j} mono(pᵢ)·mono(qⱼ).  Distribution nests the two
    // levels (over p, then over q), so REASSOCIATE the result to a single flat
    // right-associated sum with one leaf per (i,j) term.
    let (dist_nested, dist_proof0) = distribute(c, parent, p, q)?;
    let (dist_sum_expr, reassoc_proof) = reassoc_add_right(c, parent, &dist_nested)?;
    let mul_start = c.nnmul(&poly_expr(c, p), &poly_expr(c, q));
    let dist_proof = c.trans_nn(
        &mul_start,
        &dist_nested,
        &dist_sum_expr,
        dist_proof0,
        reassoc_proof,
    );

    // Now rewrite each mono(pᵢ)·mono(qⱼ) into its canonical monomial form, in
    // place (left-to-right), accumulating equalities under sum-congruence.
    let prod_terms: Vec<(Mono, Mono)> = p
        .iter()
        .flat_map(|a| q.iter().map(move |b| (a.clone(), b.clone())))
        .collect();
    let (canon_terms_expr, canon_proof) =
        canonicalize_each_product(c, parent, &dist_sum_expr, &prod_terms)?;

    // canon_terms_expr is a right-assoc sum of canonical monomial exprs (with
    // possible duplicate atom-keys, and unsorted). Reorder+merge it into the
    // canonical poly_expr(poly_mul(p,q)).
    let target_poly = poly_mul(p, q);
    let target_e = poly_expr(c, &target_poly);
    let merge_proof =
        prove_monomial_sum_collapse(c, parent, &canon_terms_expr, &prod_terms, &target_poly)?;

    let (_, _, proof) = c.chain(vec![
        (mul_start, dist_sum_expr.clone(), dist_proof),
        (dist_sum_expr, canon_terms_expr.clone(), canon_proof),
        (canon_terms_expr, target_e.clone(), merge_proof),
    ]);
    Some(proof)
}

/// Distribute `canon(p)·canon(q)` into a right-associated sum
/// `Σᵢ (mono(pᵢ) · canon(q))` then `Σᵢⱼ mono(pᵢ)·mono(qⱼ)`. Returns
/// `(sum_expr, proof : canon(p)·canon(q) = sum_expr)`.
fn distribute(c: &PolyConsts, parent: &EnvDeclBuilder, p: &Poly, q: &Poly) -> Option<(Expr, Expr)> {
    let canon_q = poly_expr(c, q);
    // First distribute over p: canon(p)·canon(q) = Σᵢ mono(pᵢ)·canon(q).
    let (sum_over_p, proof_p) = distribute_left(c, parent, p, &canon_q)?;
    // Then within each term mono(pᵢ)·canon(q), distribute over q.
    let (sum_full, proof_q) = distribute_right_all_at_once(c, parent, p, q, &sum_over_p)?;
    let start = c.nnmul(&poly_expr(c, p), &canon_q);
    let (_, _, proof) = c.chain(vec![
        (start, sum_over_p.clone(), proof_p),
        (sum_over_p, sum_full.clone(), proof_q),
    ]);
    Some((sum_full, proof))
}

/// `canon(p)·Y = Σᵢ mono(pᵢ)·Y` (right-assoc over i) via repeated `add_mul`.
fn distribute_left(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    p: &Poly,
    y: &Expr,
) -> Option<(Expr, Expr)> {
    // canon(p) = mono(p0) + canon(p[1..])  (right-assoc).
    //   (mono(p0) + rest)·Y = mono(p0)·Y + rest·Y    [add_mul]
    //   recurse on rest·Y.
    if p.len() == 1 {
        let term = c.nnmul(&mono_expr(c, &p[0]), y);
        let _ = parent;
        return Some((term.clone(), c.refl_nn(&c.nnmul(&mono_expr(c, &p[0]), y))));
    }
    let head_e = mono_expr(c, &p[0]);
    let rest_poly: Poly = p[1..].to_vec();
    let rest_e = poly_expr(c, &rest_poly);
    let canon_p = poly_expr(c, p); // == head_e + rest_e
    let lhs = c.nnmul(&canon_p, y);
    // add_mul head rest Y : (head+rest)·Y = head·Y + rest·Y
    let add_mul = c.lem_add_mul(&head_e, &rest_e, y);
    let head_y = c.nnmul(&head_e, y);
    let rest_y = c.nnmul(&rest_e, y);
    let after = c.nnadd(&head_y, &rest_y); // head·Y + rest·Y
                                           // recurse: rest·Y = Σ mono·Y
    let (rest_sum, rest_proof) = distribute_left(c, parent, &rest_poly, y)?;
    let cong = c.cong_add_right(parent, &head_y, &rest_y, &rest_sum, rest_proof);
    let final_e = c.nnadd(&head_y, &rest_sum);
    let (_, _, proof) = c.chain(vec![
        (lhs.clone(), after.clone(), add_mul),
        (after, final_e.clone(), cong),
    ]);
    Some((final_e, proof))
}

/// In the sum `Σᵢ mono(pᵢ)·canon(q)`, distribute each `mono(pᵢ)·canon(q)` into
/// `Σⱼ mono(pᵢ)·mono(qⱼ)` (via `mul_add`), rewriting every leaf in place and
/// assembling the proof right-to-left with the in-sum leaf-rewrite helper.
fn distribute_right_all_at_once(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    p: &Poly,
    q: &Poly,
    sum_over_p: &Expr,
) -> Option<(Expr, Expr)> {
    let leaves = split_add_sum(c, sum_over_p);
    if leaves.len() != p.len() {
        return None;
    }
    // Precompute each leaf's distributed form + proof.
    let mut dist_forms: Vec<Expr> = Vec::with_capacity(p.len());
    let mut dist_proofs: Vec<Expr> = Vec::with_capacity(p.len());
    for pi in p {
        let mono_pi = mono_expr(c, pi);
        let (dl, dp) = distribute_mono_over(c, parent, &mono_pi, q)?;
        dist_forms.push(dl);
        dist_proofs.push(dp);
    }
    // Build current as right-assoc over leaves; rewrite from last to first.
    // current_leaves[j] holds the CURRENT form of leaf j (original until rewritten).
    let mut current_leaves: Vec<Expr> = leaves.clone();
    let mut proof = c.refl_nn(sum_over_p);
    let mut current = sum_over_p.clone();
    for k in (0..p.len()).rev() {
        // current == rebuild(current_leaves). Rewrite leaf k from leaves[k] to
        // dist_forms[k] under prefix current_leaves[0..k].
        let from_leaf = current_leaves[k].clone();
        let to_leaf = dist_forms[k].clone();
        let lifted = rewrite_leaf_in_sum(
            c,
            parent,
            &current_leaves,
            k,
            &from_leaf,
            &to_leaf,
            dist_proofs[k].clone(),
        )?;
        // new current
        let mut next_leaves = current_leaves.clone();
        next_leaves[k] = dist_forms[k].clone();
        let next = rebuild_sum(c, &next_leaves)?;
        proof = c.trans_nn(sum_over_p, &current, &next, proof, lifted);
        current = next;
        current_leaves = next_leaves;
    }
    Some((current, proof))
}

/// Distribute a single `mono(pᵢ) · canon(q)` into `Σⱼ mono(pᵢ)·mono(qⱼ)`
/// (right-assoc over j) via repeated `mul_add`. Returns
/// `(sum_expr, proof : mono(pᵢ)·canon(q) = sum_expr)`.
fn distribute_mono_over(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    mono_pi: &Expr,
    q: &Poly,
) -> Option<(Expr, Expr)> {
    if q.len() == 1 {
        let term = c.nnmul(mono_pi, &mono_expr(c, &q[0]));
        return Some((term.clone(), c.refl_nn(&term)));
    }
    let head_q = mono_expr(c, &q[0]);
    let rest_q: Poly = q[1..].to_vec();
    let rest_e = poly_expr(c, &rest_q);
    let canon_q = poly_expr(c, q); // head_q + rest_e
    let lhs = c.nnmul(mono_pi, &canon_q);
    // mul_add mono_pi head_q rest : mono_pi·(head+rest) = mono_pi·head + mono_pi·rest
    let mul_add = c.lem_mul_add(mono_pi, &head_q, &rest_e);
    let pi_head = c.nnmul(mono_pi, &head_q);
    let pi_rest = c.nnmul(mono_pi, &rest_e);
    let after = c.nnadd(&pi_head, &pi_rest);
    let (rest_sum, rest_proof) = distribute_mono_over(c, parent, mono_pi, &rest_q)?;
    let cong = c.cong_add_right(parent, &pi_head, &pi_rest, &rest_sum, rest_proof);
    let final_e = c.nnadd(&pi_head, &rest_sum);
    let (_, _, proof) = c.chain(vec![
        (lhs.clone(), after.clone(), mul_add),
        (after, final_e.clone(), cong),
    ]);
    Some((final_e, proof))
}

/// Rewrite the leaf at index `idx` of a right-associated sum (leaves `leaves`)
/// from `from_leaf` to `to_leaf`, given `proof : from_leaf = to_leaf`. Returns
/// a proof that the WHOLE sum equals the sum with leaf `idx` replaced.
///
/// Structure at `idx`: `(leaf_idx + suffix)` (suffix = leaves[idx+1..], absent
/// when idx is last). First rewrite the LEFT summand `leaf_idx → to_leaf`
/// holding the suffix fixed (`cong_add_left`, or the bare proof when no suffix),
/// then lift through the `prefix = leaves[..idx]` via nested right-summand
/// congruence.
fn rewrite_leaf_in_sum(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    leaves: &[Expr],
    idx: usize,
    from_leaf: &Expr,
    to_leaf: &Expr,
    proof: Expr,
) -> Option<Expr> {
    let suffix = &leaves[idx + 1..];
    // Local rewrite of the sub-sum starting at idx.
    let (mut from_e, mut to_e, mut p) = if suffix.is_empty() {
        (from_leaf.clone(), to_leaf.clone(), proof)
    } else {
        let suffix_e = rebuild_sum(c, suffix)?;
        let cong = c.cong_add_left(parent, from_leaf, to_leaf, &suffix_e, proof);
        (
            c.nnadd(from_leaf, &suffix_e),
            c.nnadd(to_leaf, &suffix_e),
            cong,
        )
    };
    // Lift through the prefix leaves[..idx].
    for pre in leaves[..idx].iter().rev() {
        p = c.cong_add_right(parent, pre, &from_e, &to_e, p);
        from_e = c.nnadd(pre, &from_e);
        to_e = c.nnadd(pre, &to_e);
    }
    let _ = (&from_e, &to_e);
    Some(p)
}

/// Rewrite each `mono(pᵢ)·mono(qⱼ)` leaf of the distributed sum into its
/// canonical monomial layout, in place. Returns `(new_sum, proof)`.
fn canonicalize_each_product(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    dist_sum: &Expr,
    terms: &[(Mono, Mono)],
) -> Option<(Expr, Expr)> {
    let leaves = split_add_sum(c, dist_sum);
    if leaves.len() != terms.len() {
        return None;
    }
    let mut current_leaves = leaves.clone();
    let mut proof = c.refl_nn(dist_sum);
    let mut current = dist_sum.clone();
    for k in (0..terms.len()).rev() {
        let (a, b) = &terms[k];
        let (canon_leaf, leaf_proof) = prove_mono_product(c, parent, a, b)?;
        let from_leaf = current_leaves[k].clone();
        let lifted = rewrite_leaf_in_sum(
            c,
            parent,
            &current_leaves,
            k,
            &from_leaf,
            &canon_leaf,
            leaf_proof,
        )?;
        let mut next_leaves = current_leaves.clone();
        next_leaves[k] = canon_leaf.clone();
        let next = rebuild_sum(c, &next_leaves)?;
        proof = c.trans_nn(dist_sum, &current, &next, proof, lifted);
        current = next;
        current_leaves = next_leaves;
    }
    Some((current, proof))
}

/// Prove `mono(a) · mono(b) = mono(a⊗b)` (canonical monomial layout).
///
/// `mono(a) = Pa · ofRat ca` (or `ofRat ca` if no atoms); similarly `mono(b)`.
/// Product canonical = `Pab · ofRat (ca·cb)` where `Pab` is the sorted merge of
/// the atom lists. We:
///   1. regroup the four factors `(Pa · ca)·(Pb · cb)` into `(Pa·Pb)·(ca·cb)`
///      via `mul_assoc`/`mul_comm`,
///   2. fold `ca·cb` with `ofRat_mul`,
///   3. reorder/normalize the atom product `Pa·Pb` into the sorted right-assoc
///      `Pab` via `mul_comm`/`mul_assoc`.
fn prove_mono_product(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    a: &Mono,
    b: &Mono,
) -> Option<(Expr, Expr)> {
    let mono_a = mono_expr(c, a);
    let mono_b = mono_expr(c, b);
    let lhs = c.nnmul(&mono_a, &mono_b);

    // Target monomial (canonical layout `(x₁·(…·xₖ)) · ofRat(ca·cb)`).
    let mut atoms = a.atoms.clone();
    atoms.extend_from_slice(&b.atoms);
    atoms.sort_unstable();
    let ca = (a.num, a.den);
    let cb = (b.num, b.den);
    let (cn, cd) = rat_mul(ca, cb);
    let target = Mono {
        num: cn,
        den: cd,
        atoms: atoms.clone(),
    };
    let target_e = mono_expr(c, &target);

    // ── No atoms: lhs = ofRat ca · ofRat cb, target = ofRat(ca·cb). ──────────
    if atoms.is_empty() {
        // lhs IS `ofRat ca · ofRat cb`; ofRat_mul proves it equals ofRat(ca·cb).
        return Some((target_e, c.lem_ofrat_mul(ca, cb)));
    }

    // ── Atoms present. ──────────────────────────────────────────────────────
    // inter := (x₁·(…·xₖ)) · (ofRat ca · ofRat cb)   — same atom-product layout
    //          as `target_e`, but with the unfolded coefficient pair.
    let atomprod = atom_prod(c, &atoms);
    let ofa = c.ofrat(ca.0, ca.1);
    let ofb = c.ofrat(cb.0, cb.1);
    let coeff_pair = c.nnmul(&ofa, &ofb);
    let inter = c.nnmul(&atomprod, &coeff_pair);

    // step1: lhs = inter   (commutative-monoid product permutation; arbitrary
    //         target association).
    let s1 = prove_mul_eq(c, parent, &lhs, &inter)?;
    // step2: rewrite the RIGHT factor (ofRat ca · ofRat cb) → ofRat(ca·cb), with
    //         the whole atom product fixed on the left (ONE congruence step).
    let ofab = c.ofrat(cn, cd);
    let fold = c.lem_ofrat_mul(ca, cb); // ofRat ca · ofRat cb = ofRat(ca·cb)
    let s2 = c.cong_mul_right(parent, &atomprod, &coeff_pair, &ofab, fold);

    debug_assert_eq!(c.nnmul(&atomprod, &ofab), target_e, "mono product layout");
    let (_, _, proof) = c.chain(vec![
        (lhs.clone(), inter.clone(), s1),
        (inter, target_e.clone(), s2),
    ]);
    Some((target_e, proof))
}

/// Flatten a right-/left-nested NNReal `mul`-tree into its leaf factors
/// (left-to-right). Leaves are atoms (`FVar`) or `ofRat` literals.
fn mul_factor_list(_c: &PolyConsts, e: &Expr) -> Vec<Expr> {
    fn go(e: &Expr, out: &mut Vec<Expr>) {
        let (head, args) = uncurry(e);
        if is_const(head, "NNReal.mul") && args.len() == 2 {
            go(args[0], out);
            go(args[1], out);
        } else {
            out.push(e.clone());
        }
    }
    let mut out = Vec::new();
    go(e, &mut out);
    out
}

/// Prove `from = to` for two NNReal `mul`-products over the SAME multiset of
/// leaf factors, where `to` may have ARBITRARY association. Route:
///   from → RA(from) → RA(to_leaves order) → to
/// via flatten-to-right-assoc + selection-sort + reassociate-into-`to`.
fn prove_mul_eq(c: &PolyConsts, parent: &EnvDeclBuilder, from: &Expr, to: &Expr) -> Option<Expr> {
    if from == to {
        return Some(c.refl_nn(from));
    }
    let from_leaves = mul_factor_list(c, from);
    let to_leaves = mul_factor_list(c, to);
    if !same_multiset(&from_leaves, &to_leaves) {
        return None;
    }
    // 1) reassociate `from` to right-assoc over from_leaves.
    let (ra_from, ra_proof) = reassoc_mul_right(c, parent, from)?;
    // 2) bubble-sort into `to_leaves` order ⇒ rebuild_mul(to_leaves).
    let sorted = rebuild_mul(c, &to_leaves)?;
    let sort_proof = prove_mul_permute(c, parent, &ra_from, &to_leaves)?;
    // 3) reassociate rebuild_mul(to_leaves) into `to`'s shape: prove
    //    `to = rebuild_mul(to_leaves)` then symm.
    let s3 = if sorted == *to {
        c.refl_nn(&sorted)
    } else {
        let to_to_ra = prove_mul_reassoc_eq(c, parent, to, &sorted)?; // to = sorted
        c.symm_nn(to, &sorted, to_to_ra) // sorted = to
    };
    let (_, _, proof) = c.chain(vec![
        (from.clone(), ra_from.clone(), ra_proof),
        (ra_from, sorted.clone(), sort_proof),
        (sorted, to.clone(), s3),
    ]);
    Some(proof)
}

/// Reassociate a `mul`-tree into the right-associated product over its leaves.
/// Returns `(right_assoc_expr, proof : e = right_assoc_expr)`.
fn reassoc_mul_right(c: &PolyConsts, parent: &EnvDeclBuilder, e: &Expr) -> Option<(Expr, Expr)> {
    let leaves = mul_factor_list(c, e);
    let ra = rebuild_mul(c, &leaves)?;
    if ra == *e {
        return Some((ra, c.refl_nn(e)));
    }
    // Prove e = ra by structural reassociation. We use the generic approach:
    // both are products over the same ordered leaves, differing only by
    // association; prove via repeated `mul_assoc`. Implement by recursion on the
    // head split of `e`.
    let proof = prove_mul_reassoc_eq(c, parent, e, &ra)?;
    Some((ra, proof))
}

/// Build a right-associated product from leaves. Empty ⇒ None.
fn rebuild_mul(c: &PolyConsts, leaves: &[Expr]) -> Option<Expr> {
    let (last, init) = leaves.split_last()?;
    let mut acc = last.clone();
    for l in init.iter().rev() {
        acc = c.nnmul(l, &acc);
    }
    Some(acc)
}

/// Prove `e = ra` where both are products over the same ordered leaf sequence,
/// `ra` fully right-associated. Recursive: peel `e`'s head leaf, reassociate.
fn prove_mul_reassoc_eq(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    e: &Expr,
    ra: &Expr,
) -> Option<Expr> {
    if e == ra {
        return Some(c.refl_nn(e));
    }
    // e = (X · Y); we want head-leaf · (reassoc rest).
    let (head, args) = uncurry(e);
    if !is_const(head, "NNReal.mul") || args.len() != 2 {
        // single leaf, must equal ra
        return if e == ra { Some(c.refl_nn(e)) } else { None };
    }
    let x = args[0].clone();
    let y = args[1].clone();
    // If X is itself a product (X = X1·X2), use mul_assoc to rotate:
    //   (X1·X2)·Y = X1·(X2·Y)   [mul_assoc X1 X2 Y]
    let (xh, xa) = uncurry(&x);
    if is_const(xh, "NNReal.mul") && xa.len() == 2 {
        let x1 = xa[0].clone();
        let x2 = xa[1].clone();
        // (X1·X2)·Y = X1·(X2·Y)
        let assoc = c.lem_mul_assoc(&x1, &x2, &y); // X1·(X2·Y) = (X1·X2)·Y
        let lhs_assoc = c.nnmul(&c.nnmul(&x1, &x2), &y); // == e
        let rhs_assoc = c.nnmul(&x1, &c.nnmul(&x2, &y));
        let assoc_symm = c.symm_nn(&rhs_assoc, &lhs_assoc, assoc); // e = X1·(X2·Y)
                                                                   // recurse on rhs_assoc
        let rec = prove_mul_reassoc_eq(c, parent, &rhs_assoc, ra)?;
        let (_, _, proof) = c.chain(vec![
            (e.clone(), rhs_assoc.clone(), assoc_symm),
            (rhs_assoc, ra.clone(), rec),
        ]);
        return Some(proof);
    }
    // X is a leaf: e = X · Y ; ra should be X · (reassoc Y).
    let (rah, raa) = uncurry(ra);
    if is_const(rah, "NNReal.mul") && raa.len() == 2 && *raa[0] == x {
        let ra_tail = raa[1].clone();
        let y_proof = prove_mul_reassoc_eq(c, parent, &y, &ra_tail)?;
        let cong = c.cong_mul_right(parent, &x, &y, &ra_tail, y_proof);
        return Some(cong);
    }
    None
}

/// Bubble-sort the right-assoc product `from` (over its leaves) into the leaf
/// order `to_leaves` via adjacent `mul_comm`/`mul_assoc` swaps. Returns proof
/// `from = rebuild_mul(to_leaves)`.
fn prove_mul_permute(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    from: &Expr,
    to_leaves: &[Expr],
) -> Option<Expr> {
    let mut current = from.clone();
    let mut proof = c.refl_nn(from);
    // selection sort: for each position, bring the desired leaf to front of the
    // suffix via adjacent swaps.
    for (target_pos, want) in to_leaves.iter().enumerate() {
        let cur_leaves = mul_factor_list(c, &current);
        // find `want` at index >= target_pos
        let found = cur_leaves
            .iter()
            .enumerate()
            .skip(target_pos)
            .find(|(_, l)| *l == want)
            .map(|(i, _)| i)?;
        let mut j = found;
        while j > target_pos {
            let (swapped, step) = mul_swap_adjacent(c, parent, &current, j - 1)?;
            proof = c.trans_nn(from, &current, &swapped, proof, step);
            current = swapped;
            j -= 1;
        }
    }
    let target = rebuild_mul(c, to_leaves)?;
    debug_assert_eq!(current, target, "mul permute final mismatch");
    Some(proof)
}

/// Swap factors at index `i`,`i+1` of a right-assoc product (analogue of
/// `swap_adjacent` for `mul`). Returns `(new_product, proof : current=new)`.
fn mul_swap_adjacent(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    current: &Expr,
    i: usize,
) -> Option<(Expr, Expr)> {
    let leaves = mul_factor_list(c, current);
    if i + 1 >= leaves.len() {
        return None;
    }
    let li = leaves[i].clone();
    let lj = leaves[i + 1].clone();
    let has_tail = i + 2 < leaves.len();
    let tail = if has_tail {
        Some(rebuild_mul(c, &leaves[i + 2..])?)
    } else {
        None
    };

    let (sub_from, sub_to, sub_proof) = if let Some(t) = &tail {
        let inner = c.nnmul(&lj, t);
        let sub_from = c.nnmul(&li, &inner); // Li·(Lj·T)
        let li_lj = c.nnmul(&li, &lj);
        let assoc_lhs = c.nnmul(&li_lj, t);
        // mul_assoc a b c : a·(b·c) = (a·b)·c  ⇒  Li·(Lj·T) = (Li·Lj)·T  (FORWARD).
        let assoc = c.lem_mul_assoc(&li, &lj, t);
        let s1 = assoc; // sub_from = assoc_lhs
        let lj_li = c.nnmul(&lj, &li);
        let comm = c.lem_mul_comm(&li, &lj); // Li·Lj = Lj·Li
        let s2 = c.cong_mul_left(parent, &li_lj, &lj_li, t, comm);
        let comm_lhs = c.nnmul(&lj_li, t);
        // mul_assoc Lj Li T : Lj·(Li·T) = (Lj·Li)·T ⇒ need its SYMM for
        // (Lj·Li)·T = Lj·(Li·T).
        let li_t = c.nnmul(&li, t);
        let sub_to = c.nnmul(&lj, &li_t);
        let assoc2 = c.lem_mul_assoc(&lj, &li, t); // sub_to = comm_lhs
        let assoc2_symm = c.symm_nn(&sub_to, &comm_lhs, assoc2); // comm_lhs = sub_to
        let (_, _, p) = c.chain(vec![
            (sub_from.clone(), assoc_lhs.clone(), s1),
            (assoc_lhs, comm_lhs.clone(), s2),
            (comm_lhs, sub_to.clone(), assoc2_symm),
        ]);
        (sub_from, sub_to, p)
    } else {
        let sub_from = c.nnmul(&li, &lj);
        let sub_to = c.nnmul(&lj, &li);
        let comm = c.lem_mul_comm(&li, &lj);
        (sub_from, sub_to, comm)
    };

    let mut proof = sub_proof;
    let mut from_e = sub_from;
    let mut to_e = sub_to;
    for k in (0..i).rev() {
        let prefix_leaf = leaves[k].clone();
        proof = c.cong_mul_right(parent, &prefix_leaf, &from_e, &to_e, proof);
        from_e = c.nnmul(&prefix_leaf, &from_e);
        to_e = c.nnmul(&prefix_leaf, &to_e);
    }
    debug_assert_eq!(from_e, *current);
    Some((to_e, proof))
}

/// Collapse a right-assoc sum of canonical monomial exprs (possibly with
/// duplicate atom-keys and unsorted) into the canonical poly_expr(target_poly),
/// by sum-reordering and coefficient-folding. `terms` gives the (a,b) products
/// in leaf order; `target_poly = poly_mul(p,q)`.
fn prove_monomial_sum_collapse(
    c: &PolyConsts,
    parent: &EnvDeclBuilder,
    sum_expr: &Expr,
    terms: &[(Mono, Mono)],
    target_poly: &Poly,
) -> Option<Expr> {
    // Build the multiset of canonical monomials present in sum_expr.
    let monos: Vec<Mono> = terms
        .iter()
        .map(|(a, b)| {
            let (cn, cd) = rat_mul((a.num, a.den), (b.num, b.den));
            let mut atoms = a.atoms.clone();
            atoms.extend_from_slice(&b.atoms);
            atoms.sort_unstable();
            Mono {
                num: cn,
                den: cd,
                atoms,
            }
        })
        .collect();

    // Fold the monos into a canonical poly incrementally, building the proof:
    // start from sum_expr == canon-sum of `monos` (in leaf order). Insert each
    // mono into an accumulator poly that we keep canonical, exactly like
    // prove_sum_merge but where the source sum is `monos` in given order.
    // Implementation: treat monos as a polynomial expression whose monomial
    // exprs are EXACTLY the leaves; reuse the incremental insert proof.
    let leaves = split_add_sum(c, sum_expr);
    if leaves.len() != monos.len() {
        return None;
    }
    // sanity: each leaf equals mono_expr(monos[i])
    for (lf, m) in leaves.iter().zip(monos.iter()) {
        if *lf != mono_expr(c, m) {
            return None;
        }
    }

    // acc starts as the first monomial; fold in the rest one at a time.
    let mut acc_poly: Poly = vec![monos[0].clone()];
    let mut current = sum_expr.clone();
    let mut proof = c.refl_nn(sum_expr);

    // current == mono(monos[0]) + (mono(monos[1]) + ( … ))
    // We process tail monomials left-to-right, each time peeling off the head of
    // the remaining tail and inserting into acc.
    let mut remaining: Vec<Mono> = monos[1..].to_vec();
    while !remaining.is_empty() {
        let head = remaining[0].clone();
        let tail = remaining[1..].to_vec();
        let acc_e = poly_expr(c, &acc_poly);
        let head_e = mono_expr(c, &head);

        if tail.is_empty() {
            // current == acc_e + head_e
            let (inserted, ins) = prove_insert_mono(c, parent, &acc_poly, &head)?;
            let target = poly_expr(c, &inserted);
            proof = c.trans_nn(sum_expr, &current, &target, proof, ins);
            current = target;
            acc_poly = inserted;
            remaining = tail;
        } else {
            // current == acc_e + (head_e + canon(tail))
            let tail_e = rebuild_sum(c, &tail.iter().map(|m| mono_expr(c, m)).collect::<Vec<_>>())?;
            let inner = c.nnadd(&head_e, &tail_e);
            let assoc = c.lem_add_assoc(&acc_e, &head_e, &tail_e); // (acc+head)+tail = acc+(head+tail)
            let lhs_assoc = c.nnadd(&c.nnadd(&acc_e, &head_e), &tail_e);
            let assoc_symm = c.symm_nn(&lhs_assoc, &c.nnadd(&acc_e, &inner), assoc);
            proof = c.trans_nn(sum_expr, &current, &lhs_assoc, proof, assoc_symm);
            current = lhs_assoc;
            // insert head into acc, rewrite left summand
            let acc_plus_head = c.nnadd(&acc_e, &head_e);
            let (inserted, ins) = prove_insert_mono(c, parent, &acc_poly, &head)?;
            let inserted_e = poly_expr(c, &inserted);
            let cong = c.cong_add_left(parent, &acc_plus_head, &inserted_e, &tail_e, ins);
            let new_current = c.nnadd(&inserted_e, &tail_e);
            proof = c.trans_nn(sum_expr, &current, &new_current, proof, cong);
            current = new_current;
            acc_poly = inserted;
            remaining = tail;
        }
    }

    debug_assert_eq!(&acc_poly, target_poly, "collapse poly mismatch");
    debug_assert_eq!(current, poly_expr(c, target_poly), "collapse expr mismatch");
    Some(proof)
}

// Helper: multiset equality of two Expr lists (structural).
fn same_multiset(a: &[Expr], b: &[Expr]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut used = vec![false; b.len()];
    for x in a {
        let mut found = false;
        for (j, y) in b.iter().enumerate() {
            if !used[j] && x == y {
                used[j] = true;
                found = true;
                break;
            }
        }
        if !found {
            return false;
        }
    }
    true
}

// ─────────────────────────────────────────────────────────────────────────────
// Public entry point.
// ─────────────────────────────────────────────────────────────────────────────

/// Emit a kernel-checkable proof of `Eq NNReal lhs rhs` when `lhs` and `rhs` are
/// equal as `NNReal` commutative-semiring polynomials over atom `FVar`s and
/// `ofRat` literal coefficients; `None` otherwise (unequal, or outside the
/// modelled grammar `{+, ·, atom-FVar, ofRat literal}`).
///
/// The returned term is a pure composition of foundational `Eq` constructors
/// and the landed axiom-free `NNReal` semiring lemmas. The helper does NOT
/// register kernel decls and trusts nothing — kernel-check the result.
pub(crate) fn prove_nnreal_poly_eq(lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    let c = PolyConsts::new();
    let parent = EnvDeclBuilder::new();
    let (pl, proof_l) = normalize(&c, &parent, lhs)?;
    let (pr, proof_r) = normalize(&c, &parent, rhs)?;
    // canonical forms must match exactly (same polynomial).
    if pl != pr {
        return None;
    }
    let canon = poly_expr(&c, &pl);
    // proof_l : lhs = canon ; proof_r : rhs = canon ⇒ symm proof_r : canon = rhs.
    let symm_r = c.symm_nn(rhs, &canon, proof_r);
    Some(c.trans_nn(lhs, &canon, rhs, proof_l, symm_r))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;
    use crate::tc::TypeChecker;

    /// A small test env pulling in the full NNReal semiring lemma surface plus
    /// `Eq`. Atoms are introduced as the test's own `FVar`s.
    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_semiring_units()
            .expect("units (mul_one/add_zero)");
        env.init_algebra_nnreal_reverse_square_algebra()
            .expect("mul_comm/mul_assoc/ofRat_mul");
        env.init_algebra_nnreal_add_comm_assoc()
            .expect("add_comm/add_assoc");
        env.init_algebra_nnreal_mul_distrib().expect("mul_add");
        env.init_algebra_nnreal_add_mul().expect("add_mul");
        env.init_algebra_nnreal_finsum_ofrat().expect("ofRat_add");
        env.init_eq().expect("eq");
        env
    }

    fn c() -> PolyConsts {
        PolyConsts::new()
    }

    /// Atom `FVar` with a small id (atoms are opaque NNReal vars).
    fn atom(id: u64) -> Expr {
        Expr::fvar(FVarId::new(id))
    }

    /// Type-check `proof : Eq NNReal lhs rhs` in a context binding the atom
    /// FVars used (ids 0..n) at type NNReal.
    fn check(env: &Environment, atoms: &[u64], lhs: &Expr, rhs: &Expr, proof: &Expr) {
        use crate::tc::LocalContext;
        let cc = c();
        let mut ctx = LocalContext::new();
        for id in atoms {
            ctx.push_with_id(
                FVarId::new(*id),
                Name::anon(),
                cc.nnreal.clone(),
                BinderInfo::Default,
            );
        }
        let tc = TypeChecker::with_context_and_mode(env, ctx, env.mode());
        let goal = cc.eq_nn(lhs, rhs);
        tc.check_type(proof, &goal)
            .unwrap_or_else(|e| panic!("proof must kernel-check against goal: {e:?}"));
    }

    fn ofrat(num: u128, den: u128) -> Expr {
        c().ofrat(num, den)
    }
    fn mul(a: &Expr, b: &Expr) -> Expr {
        c().nnmul(a, b)
    }
    fn add(a: &Expr, b: &Expr) -> Expr {
        c().nnadd(a, b)
    }

    // (1) (a+b)*(a+b) = a*a + 2*(a*b) + b*b
    #[test]
    fn test_square_of_sum() {
        let env = env();
        let (a, b) = (atom(0), atom(1));
        let lhs = mul(&add(&a, &b), &add(&a, &b));
        // a*a + (2*(a*b) + b*b)  — shape doesn't matter, helper canonicalizes both.
        let two_ab = mul(&ofrat(2, 1), &mul(&a, &b));
        let rhs = add(&mul(&a, &a), &add(&two_ab, &mul(&b, &b)));
        let proof = prove_nnreal_poly_eq(&lhs, &rhs).expect("(1) must prove");
        check(&env, &[0, 1], &lhs, &rhs, &proof);
    }

    // (2) (a+b)*c = a*c + b*c
    #[test]
    fn test_add_mul() {
        let env = env();
        let (a, b, cc) = (atom(0), atom(1), atom(2));
        let lhs = mul(&add(&a, &b), &cc);
        let rhs = add(&mul(&a, &cc), &mul(&b, &cc));
        let proof = prove_nnreal_poly_eq(&lhs, &rhs).expect("(2) must prove");
        check(&env, &[0, 1, 2], &lhs, &rhs, &proof);
    }

    // (3) a*(b+c) + d = a*b + a*c + d
    #[test]
    fn test_mul_add_reassoc() {
        let env = env();
        let (a, b, cc, d) = (atom(0), atom(1), atom(2), atom(3));
        let lhs = add(&mul(&a, &add(&b, &cc)), &d);
        let rhs = add(&mul(&a, &b), &add(&mul(&a, &cc), &d));
        let proof = prove_nnreal_poly_eq(&lhs, &rhs).expect("(3) must prove");
        check(&env, &[0, 1, 2, 3], &lhs, &rhs, &proof);
    }

    // (4) (a+b+c)^2 expanded — 6 distinct monomials.
    #[test]
    fn test_trinomial_square() {
        let env = env();
        let (a, b, cc) = (atom(0), atom(1), atom(2));
        let s = add(&a, &add(&b, &cc)); // a + (b + c)
        let lhs = mul(&s, &s);
        // a^2 + b^2 + c^2 + 2ab + 2ac + 2bc, in some shape.
        let rhs = add(
            &mul(&a, &a),
            &add(
                &mul(&b, &b),
                &add(
                    &mul(&cc, &cc),
                    &add(
                        &mul(&ofrat(2, 1), &mul(&a, &b)),
                        &add(
                            &mul(&ofrat(2, 1), &mul(&a, &cc)),
                            &mul(&ofrat(2, 1), &mul(&b, &cc)),
                        ),
                    ),
                ),
            ),
        );
        let proof = prove_nnreal_poly_eq(&lhs, &rhs).expect("(4) must prove");
        check(&env, &[0, 1, 2], &lhs, &rhs, &proof);
    }

    // (5) ofRat 3 * a * a + ofRat 5 * a * a = ofRat 8 * a * a
    #[test]
    fn test_coeff_add() {
        let env = env();
        let a = atom(0);
        let t3 = mul(&mul(&ofrat(3, 1), &a), &a);
        let t5 = mul(&mul(&ofrat(5, 1), &a), &a);
        let lhs = add(&t3, &t5);
        let rhs = mul(&mul(&ofrat(8, 1), &a), &a);
        let proof = prove_nnreal_poly_eq(&lhs, &rhs).expect("(5) must prove");
        check(&env, &[0], &lhs, &rhs, &proof);
    }

    // Negative: genuinely unequal polynomials ⇒ None.
    #[test]
    fn test_unequal_returns_none() {
        let (a, b) = (atom(0), atom(1));
        let lhs = mul(&add(&a, &b), &add(&a, &b)); // a²+2ab+b²
        let rhs = add(&mul(&a, &a), &mul(&b, &b)); // a²+b²
        assert!(
            prove_nnreal_poly_eq(&lhs, &rhs).is_none(),
            "unequal polys must return None"
        );
    }
}
