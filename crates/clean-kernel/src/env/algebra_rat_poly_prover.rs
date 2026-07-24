// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A minimal `Rat` polynomial-identity prover (meta-level proof-term generator).
//!
//! Given two `Rat` polynomial expressions built from `Rat.add` / `Rat.mul` /
//! `Rat.neg` / `Rat.sub` / `Rat.one` and a fixed list of atom indeterminates
//! (`vars`, as `Expr` FVars), `RatPolyProver::prove_poly_eq` constructs a kernel
//! `Eq` proof of `lhs = rhs` by normalization — when the two are equal as free
//! polynomials over the `Rat` ring.
//!
//! # Why
//!
//! The recurring bottleneck in the M2 / KKL chain is the *hand-assembled*
//! polynomial identity: `add_cube` (degree 3) cost a 800-line bespoke
//! `Eq.subst`/`congrArg` rewrite chain, and the M2 lemma (A) degree-9 identity
//! stalled two agents. This module replaces the bespoke chains with a SYSTEMATIC
//! generator: a ring normalizer that emits the proof as a by-product of
//! normalization, so any true ring identity over `Rat` becomes a one-call proof.
//!
//! # The representation
//!
//! A polynomial is a `Poly`: a sorted map from `Monomial` (an exponent vector
//! over `vars`, plus the constant monomial) to an integer coefficient
//! (`i128`) — the operations in scope (`+`, `·`, `−`, neg) keep integer
//! coefficients integer, so no denominator is needed. (Rat is a ring; the only
//! `Rat` *constant* the prover interprets is `Rat.one` — coefficients are
//! repeated additions of `Rat.one` exactly as `add_cube` writes `3 = (1+1)+1`.)
//!
//! # The proof
//!
//! `normalize(e) -> NormResult { poly, canon, proof : e = canon }`, by structural
//! recursion that mirrors the parse. Each node lifts its children's proofs by
//! `congrArg` (so `e = f A B` from `a = A`, `b = B`), then rewrites `f A B` to
//! the canonical `reify(combine pa pb)` via one of three *normal-form combiners*
//! (`prove_add_of_canon` / `prove_mul_of_canon` / `prove_neg_of_canon`) that act
//! on already-canonical sums. `prove_poly_eq lhs rhs` is then
//! `Eq.trans (normalize lhs).proof (Eq.symm (normalize rhs).proof)` once the two
//! canonical forms coincide.
//!
//! Every step is a genuine `Rat` ring lemma (`left/right_distrib`, `mul_comm`,
//! `mul_assoc`, `add_comm`, `add_assoc`, `one_mul`, `mul_neg`, `neg_neg`,
//! `add_neg_self`, `add_zero`, `zero_add`, `mul_zero`, `zero_mul`) chained with
//! the `Eq` toolkit, so a proof emitted by this module is `Constructive` with an
//! empty domain-axiom closure (foundational only) whenever its leaf lemmas are.

use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;
use crate::name::Name;
use std::collections::BTreeMap;

mod coeff;
mod combine;
mod combine_engine;
mod mono;
mod mul;
mod mul_pos;
mod normalize;
#[cfg(any(test, feature = "math-overlays"))]
mod validate;

/// A monomial: sorted exponent vector over the prover's `vars` (index → power).
/// The empty map is the constant monomial `1`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
pub(crate) struct Monomial {
    /// `(var_index, exponent)` pairs, strictly ascending by `var_index`, all
    /// exponents `≥ 1`. The constant monomial is the empty vector.
    powers: Vec<(usize, u32)>,
}

impl Monomial {
    fn one() -> Self {
        Monomial { powers: Vec::new() }
    }
    fn var(idx: usize) -> Self {
        Monomial {
            powers: vec![(idx, 1)],
        }
    }
    fn is_one(&self) -> bool {
        self.powers.is_empty()
    }
    /// Multiply two monomials (add exponents).
    fn mul(&self, other: &Monomial) -> Monomial {
        let mut map: BTreeMap<usize, u32> = BTreeMap::new();
        for &(v, e) in &self.powers {
            *map.entry(v).or_insert(0) += e;
        }
        for &(v, e) in &other.powers {
            *map.entry(v).or_insert(0) += e;
        }
        Monomial {
            powers: map.into_iter().collect(),
        }
    }
}

/// A polynomial: monomial → integer coefficient, with zero coefficients pruned.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub(crate) struct Poly {
    terms: BTreeMap<Monomial, i128>,
}

impl Poly {
    fn zero() -> Self {
        Poly {
            terms: BTreeMap::new(),
        }
    }
    fn one() -> Self {
        let mut terms = BTreeMap::new();
        terms.insert(Monomial::one(), 1i128);
        Poly { terms }
    }
    fn var(idx: usize) -> Self {
        let mut terms = BTreeMap::new();
        terms.insert(Monomial::var(idx), 1i128);
        Poly { terms }
    }
    fn add_term(&mut self, m: Monomial, c: i128) {
        let e = self.terms.entry(m.clone()).or_insert(0);
        *e += c;
        if *e == 0 {
            self.terms.remove(&m);
        }
    }
    fn add(&self, other: &Poly) -> Poly {
        let mut out = self.clone();
        for (m, c) in &other.terms {
            out.add_term(m.clone(), *c);
        }
        out.prune();
        out
    }
    fn neg(&self) -> Poly {
        let terms = self.terms.iter().map(|(m, c)| (m.clone(), -c)).collect();
        Poly { terms }
    }
    fn mul(&self, other: &Poly) -> Poly {
        let mut out = Poly::zero();
        for (m1, c1) in &self.terms {
            for (m2, c2) in &other.terms {
                out.add_term(m1.mul(m2), c1 * c2);
            }
        }
        out.prune();
        out
    }
    fn prune(&mut self) {
        self.terms.retain(|_, c| *c != 0);
    }
    /// Sorted, pruned (coeff, monomial) list in canonical (descending-monomial)
    /// order. Descending so the highest-degree / lexicographically-largest
    /// monomial leads — matches the `add_cube` `a³ + (…)` convention.
    #[cfg(test)]
    pub(crate) fn sorted_terms_dbg(&self) -> Vec<(i128, Monomial)> {
        self.sorted_terms()
    }
    fn sorted_terms(&self) -> Vec<(i128, Monomial)> {
        let mut v: Vec<(i128, Monomial)> = self
            .terms
            .iter()
            .filter(|(_, c)| **c != 0)
            .map(|(m, c)| (*c, m.clone()))
            .collect();
        v.sort_by(|a, b| b.1.cmp(&a.1));
        v
    }
}

/// Error from the polynomial-identity prover.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PolyProveError {
    /// An expression head was not one of `Rat.add/mul/neg/sub/one` or a known atom.
    UnrecognizedExpr(String),
    /// The two sides are not equal as polynomials (so no identity to prove).
    NotAnIdentity {
        /// Monomials whose coefficients differ (lhs − rhs).
        diff: Vec<(String, i128)>,
    },
}

/// The polynomial-identity prover. Wraps the constructive `Rat` ring surface
/// (`RingConsts`) and a fixed list of atom indeterminates.
pub(crate) struct RatPolyProver {
    c: RingConsts,
    /// The atom indeterminates, as `Expr`s (typically FVars or opaque consts).
    vars: Vec<Expr>,
    add_zero: Expr,
    zero_add: Expr,
    mul_zero: Expr,
    add_neg_self: Expr,
    neg_neg: Expr,
}

/// The result of normalizing an expression to canonical form.
pub(crate) struct NormResult {
    pub(crate) poly: Poly,
    pub(crate) canon: Expr,
    /// Proof `e = canon`.
    pub(crate) proof: Expr,
}

impl RatPolyProver {
    /// Create a prover over the given atom indeterminates (matched by structural
    /// equality against sub-expressions during parsing).
    pub(crate) fn new(vars: Vec<Expr>) -> Self {
        RatPolyProver {
            c: RingConsts::new(),
            vars,
            add_zero: Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            zero_add: Expr::const_(Name::from_string("Rat.zero_add"), vec![]),
            mul_zero: Expr::const_(Name::from_string("Rat.mul_zero"), vec![]),
            add_neg_self: Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]),
            neg_neg: Expr::const_(Name::from_string("Rat.neg_neg"), vec![]),
        }
    }

    fn rat(&self) -> Expr {
        self.c.rat()
    }
    fn one(&self) -> Expr {
        self.c.one()
    }
    fn zero(&self) -> Expr {
        self.c.o.rat_zero.clone()
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        self.c.add(a, b)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.c.mul(a, b)
    }
    fn neg(&self, a: Expr) -> Expr {
        self.c.neg(a)
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.c.sub(a, b)
    }
    fn acomm(&self, a: Expr, b: Expr) -> Expr {
        self.c.acomm(a, b)
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.c.eq(a, b)
    }
    fn refl(&self, a: Expr) -> Expr {
        Expr::apps(self.c.o.eq_refl.clone(), [self.rat(), a])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.c.symm(a, b, h)
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.c.trans(a, b, cc, h1, h2)
    }
    fn add_const(&self) -> Expr {
        self.c.add_const()
    }
    fn mul_const(&self) -> Expr {
        self.c.mul_const()
    }
    fn neg_const(&self) -> Expr {
        self.c.o.rat_neg.clone()
    }
    /// `(x op fixed) = (y op fixed)` from `h : x = y`.
    fn cong_left(
        &self,
        parent: &EnvDeclBuilder,
        op: &Expr,
        x: Expr,
        y: Expr,
        fixed: Expr,
        h: Expr,
    ) -> Expr {
        self.c.cong_left(parent, op, x, y, fixed, h)
    }
    /// `(fixed op x) = (fixed op y)` from `h : x = y`.
    fn cong_right(
        &self,
        parent: &EnvDeclBuilder,
        op: &Expr,
        x: Expr,
        y: Expr,
        fixed: Expr,
        h: Expr,
    ) -> Expr {
        self.c.cong_right(parent, op, x, y, fixed, h)
    }
    /// `congrArg Rat.neg h : neg x = neg y` from `h : x = y`.
    fn cong_neg(&self, parent: &EnvDeclBuilder, x: Expr, y: Expr, h: Expr) -> Expr {
        let f = self.neg_const();
        // congrArg expects f : Rat → Rat; Rat.neg already has that type, but to
        // match the `cong_left/right` lambda style we use a fresh lambda.
        let lam = {
            use crate::expr::BinderInfo;
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = ch.fresh_local(self.rat());
            let body = Expr::app(f, w);
            ch.finish_child(ch.mk_lam(w_id, BinderInfo::Default, self.rat(), body))
        };
        Expr::apps(
            self.c.congr_arg.clone(),
            [self.rat(), self.rat(), x, y, lam, h],
        )
    }

    // ── numerals: `n` as `((1+1)+…+1)` (n ≥ 1), matching `add_cube` ──────────
    /// The numeral `n` (`n ≥ 1`) as a left-nested sum of `Rat.one`.
    fn numeral(&self, n: u32) -> Expr {
        debug_assert!(n >= 1);
        let mut acc = self.one();
        for _ in 1..n {
            acc = self.add(acc, self.one());
        }
        acc
    }

    /// The canonical atom-index sequence of a monomial: ascending var-index,
    /// each repeated by its exponent. `[]` for the constant monomial.
    fn mono_seq(&self, m: &Monomial) -> Vec<usize> {
        let mut seq = Vec::new();
        for &(v, e) in &m.powers {
            for _ in 0..e {
                seq.push(v);
            }
        }
        seq
    }

    /// Left-nested product of an atom-index sequence; `[]` → `Rat.one`.
    fn reify_seq(&self, seq: &[usize]) -> Expr {
        let mut acc: Option<Expr> = None;
        for &v in seq {
            let atom = self.vars[v].clone();
            acc = Some(match acc {
                None => atom,
                Some(prev) => self.mul(prev, atom),
            });
        }
        acc.unwrap_or_else(|| self.one())
    }

    /// Reify a monomial as a left-nested product of atoms `((x·x)·y)…`, in
    /// ascending var-index order with repeats by exponent. The empty monomial
    /// reifies to `Rat.one`.
    fn reify_monomial(&self, m: &Monomial) -> Expr {
        self.reify_seq(&self.mono_seq(m))
    }

    /// Reify a single signed term `coeff · monomial` to its canonical `Expr`.
    ///
    /// - coeff `1`, monomial `1` → `Rat.one`
    /// - coeff `1`, monomial `m` → `reify(m)`
    /// - coeff `n>1`, monomial `1` → `numeral(n)`
    /// - coeff `n>1`, monomial `m` → `numeral(n) · reify(m)`
    /// - coeff `-k` → `Rat.neg (reify_pos_term(k, m))`
    fn reify_term(&self, coeff: i128, m: &Monomial) -> Expr {
        if coeff < 0 {
            let pos = self.reify_pos_term((-coeff) as u32, m);
            return self.neg(pos);
        }
        self.reify_pos_term(coeff as u32, m)
    }

    /// Reify a positive-coefficient term (`coeff ≥ 1`).
    fn reify_pos_term(&self, coeff: u32, m: &Monomial) -> Expr {
        let mono = self.reify_monomial(m);
        if coeff == 1 {
            mono
        } else if m.is_one() {
            self.numeral(coeff)
        } else {
            self.mul(self.numeral(coeff), mono)
        }
    }

    /// Reify a whole polynomial to its canonical `Expr`: a right-nested sum of
    /// the sorted terms `t_0 + (t_1 + (… + t_k))`. Empty poly reifies to `0`.
    fn reify_poly(&self, p: &Poly) -> Expr {
        let terms = p.sorted_terms();
        if terms.is_empty() {
            return self.zero();
        }
        let mut iter = terms.iter().rev();
        let (c0, m0) = iter.next().expect("nonempty");
        let mut acc = self.reify_term(*c0, m0);
        for (c, m) in iter {
            acc = self.add(self.reify_term(*c, m), acc);
        }
        acc
    }

    /// Parse an `Expr` into a `Poly` (no proof). Used to detect identities and
    /// to drive coefficient bookkeeping.
    pub(crate) fn parse(&self, e: &Expr) -> Result<Poly, PolyProveError> {
        use crate::expr::ExprKind;
        // atom match first
        if let Some(idx) = self.var_index(e) {
            return Ok(Poly::var(idx));
        }
        match e.kind() {
            ExprKind::Const(name, _) if name == &Name::from_string("Rat.one") => Ok(Poly::one()),
            ExprKind::Const(name, _) if name == &Name::from_string("Rat.zero") => Ok(Poly::zero()),
            _ => {
                // application heads
                let (head, args) = uncurry(e);
                if let ExprKind::Const(name, _) = head.kind() {
                    let s = name.to_string();
                    match (s.as_str(), args.len()) {
                        ("Rat.add", 2) => {
                            let a = self.parse(&args[0])?;
                            let b = self.parse(&args[1])?;
                            Ok(a.add(&b))
                        }
                        ("Rat.mul", 2) => {
                            let a = self.parse(&args[0])?;
                            let b = self.parse(&args[1])?;
                            Ok(a.mul(&b))
                        }
                        ("Rat.sub", 2) => {
                            let a = self.parse(&args[0])?;
                            let b = self.parse(&args[1])?;
                            Ok(a.add(&b.neg()))
                        }
                        ("Rat.neg", 1) => {
                            let a = self.parse(&args[0])?;
                            Ok(a.neg())
                        }
                        _ => Err(PolyProveError::UnrecognizedExpr(format!(
                            "head {s} with {} args",
                            args.len()
                        ))),
                    }
                } else {
                    Err(PolyProveError::UnrecognizedExpr(format!("{:?}", e.kind())))
                }
            }
        }
    }

    /// Find the index of `e` among the prover's `vars`, by structural equality.
    fn var_index(&self, e: &Expr) -> Option<usize> {
        self.vars.iter().position(|v| v == e)
    }

    /// Prove `lhs = rhs` (both `Rat` polynomial expressions) when they are equal
    /// as free polynomials. Returns the kernel proof term, or `Err` if they are
    /// not an identity (or contain unrecognized sub-terms).
    pub(crate) fn prove_poly_eq(
        &self,
        parent: &EnvDeclBuilder,
        lhs: &Expr,
        rhs: &Expr,
    ) -> Result<Expr, PolyProveError> {
        let nl = self.normalize(parent, lhs)?;
        let nr = self.normalize(parent, rhs)?;
        if nl.poly != nr.poly {
            let diff = poly_diff(&nl.poly, &nr.poly);
            return Err(PolyProveError::NotAnIdentity { diff });
        }
        // canonical forms are syntactically identical (same Poly ⇒ same reify).
        // proof : lhs = canon = rhs   via  trans (lhs=canon) (symm (rhs=canon)).
        let canon = nl.canon.clone();
        let symm_r = self.symm(rhs.clone(), nr.canon.clone(), nr.proof);
        Ok(self.trans(lhs.clone(), canon, rhs.clone(), nl.proof, symm_r))
    }

    /// Check, without building a proof, that `lhs` and `rhs` are the same poly.
    #[cfg(test)]
    pub(crate) fn is_identity(&self, lhs: &Expr, rhs: &Expr) -> Result<bool, PolyProveError> {
        Ok(self.parse(lhs)? == self.parse(rhs)?)
    }
}

/// Count the AST nodes of an expression (for scaling diagnostics).
#[cfg(test)]
pub(crate) fn expr_node_count(e: &Expr) -> usize {
    use crate::expr::ExprKind;
    match e.kind() {
        ExprKind::App(f, a) => 1 + expr_node_count(f) + expr_node_count(a),
        ExprKind::Lam(_, ty, b) | ExprKind::Pi(_, ty, b) => {
            1 + expr_node_count(ty) + expr_node_count(b)
        }
        _ => 1,
    }
}

/// Uncurry an application into `(head, args)`.
fn uncurry(e: &Expr) -> (Expr, Vec<Expr>) {
    use crate::expr::ExprKind;
    let mut args = Vec::new();
    let mut cur = e.clone();
    while let ExprKind::App(f, a) = cur.kind() {
        args.push((**a).clone());
        cur = (**f).clone();
    }
    args.reverse();
    (cur, args)
}

/// Human-readable coefficient differences (lhs − rhs) for error reporting.
fn poly_diff(lhs: &Poly, rhs: &Poly) -> Vec<(String, i128)> {
    let d = lhs.add(&rhs.neg());
    d.sorted_terms()
        .into_iter()
        .map(|(c, m)| (format!("{m:?}"), c))
        .collect()
}
