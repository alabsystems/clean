// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-point cross-term (CT) polynomial certificate — the first LIVE,
//! independently-validated brick of the genuine M2 `(4/3, 4)` hypercontractivity
//! proof.
//!
//! # The math (validated symbolically; max roundoff err `9e-10`)
//!
//! The M2 cross-term CT is PER-POINT-reducible via a superadditive functional.
//! With the cube-root substitution `s = |a|^{1/3}`, `r = |b|^{1/3}` (so
//! `|a|^{4/3} = s⁴`, `|a+b|⁴ = (s³+r³)⁴` same-sign), the per-point CT COLLAPSES
//! the irrational to a pure POLYNOMIAL — because `(4/3)·(3/2) = 2`:
//! `(NG·NH)^{3/2} = ((a+b)^{4/3}(a−b)^{4/3})^{3/2} = (a+b)²(a−b)²`.
//!
//! The per-point CT (same-sign, `a,b ≥ 0`, `a = s³`, `b = r³`) is the degree-12
//! inequality
//!
//! ```text
//!   4·(s⁴+r⁴)³  ≥  2·(s³+r³)⁴ + (4/3)·(s³+r³)²·(s³−r³)² + (2/81)·(s³−r³)⁴
//! ```
//!
//! with the EXACT factored certificate (verified symbolically):
//!
//! ```text
//!   4·(s⁴+r⁴)³ − [RHS]  =  (4/81)·(r−s)⁴ · OCTIC,
//!   OCTIC = 13r⁸+52r⁷s+130r⁶s²+100r⁵s³+58r⁴s⁴+100r³s⁵+130r²s⁶+52rs⁷+13s⁸
//! ```
//!
//! all OCTIC coefficients POSITIVE, hence nonneg on the orthant by inspection.
//!
//! # The subtraction-free reformulation (NNReal has no subtraction)
//!
//! Write `B := 4·(s⁴+r⁴)³`. The RHS expands to a FULLY POSITIVE polynomial
//! (every `(s³−r³)` subtraction cancels):
//!
//! ```text
//!   T := (272/81)(r¹²+s¹²) + (640/81)(r⁹s³+r³s⁹) + (256/27)r⁶s⁶.
//! ```
//!
//! The certificate `N := (4/81)(r−s)⁴·OCTIC = B − T` has NEGATIVE coefficients
//! when expanded, so it is NOT a bare nonneg-coefficient polynomial. We make
//! everything subtraction-free with the SINGLE master identity (pure `{s,r}`, no
//! division by the difference): writing `K := (4/81)·OCTIC`,
//! `Cpos := r⁴+6r²s²+s⁴`, `Cneg := 4r³s+4rs³` (so `(r−s)⁴ = Cpos − Cneg`),
//!
//! ```text
//!   (G_A*)   B + K·Cneg  =  T + K·Cpos                  [unconditional, all +].
//! ```
//!
//! `(G_A*)` holds because `B − T = K·(Cpos − Cneg) = K·(r−s)⁴ = N`.
//!
//! # `(r−s)⁴` in NNReal — the `e`-atom + the abstract reduction
//!
//! `(r−s)⁴` cannot be FORMED in `NNReal`. We carry it as an abstract atom
//! `e : NNReal` constrained by the SUBTRACTION-FREE defining relation
//! `hc : Cpos = e + Cneg` (i.e. `e = (r−s)⁴`). The per-point CT then follows from
//! `(G_A*)` + `hc` by pure semiring algebra: `K·Cpos = K·(e+Cneg) = K·e + K·Cneg`
//! (`mul_add`), so `(G_A*)` reads `B + K·Cneg = (T + K·e) + K·Cneg`; right-cancel
//! `K·Cneg` to get `B = T + K·e`; then `le_self_add` gives `T ≤ T + K·e = B`.
//!
//! This last reduction is `[`per_point_ct_reduction`]` — it is **ABSTRACT** in the
//! atoms `B, T, K, Cneg, Cpos, e` (the deep polynomial structure is irrelevant to
//! the cancellation), hence kernel-light and fully discharged.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `BoolAnalysis.per_point_ct_octic_nonneg` — `NNReal.zero ≤ OCTIC(r,s)`
//!   (all-positive coefficients; `le_self_add` floor + `zero_add`). The
//!   certificate-positivity sub-brick.
//! - `BoolAnalysis.per_point_ct_reduction` — the ABSTRACT per-point reduction
//!   `(B + K·Cneg = T + K·Cpos) → (Cpos = e + Cneg) → T ≤ B` over atoms
//!   `B T K Cneg Cpos e : NNReal`. Discharges the per-point CT inequality MODULO
//!   the master identity `(G_A*)` and the `(r−s)⁴` defining relation `hc`.
//!
//! # Heaviness note (HONEST)
//!
//! Discharging `(G_A*)` itself as a CONCRETE degree-12 `{s,r}` ring identity via
//! the generic `prove_nnreal_poly_eq` normalizer is PROHIBITIVE: a single
//! degree-12 monomial (`r¹²`) costs the normalizer ≈ 27 s to construct (its
//! per-factor selection-sort emits an `O(deg³)`-size congruence chain), and the
//! 13-monomial flat identity OOM-SIGKILLs the kernel check. The kernel *check* of
//! deep `mul` trees is fast (≈ 0 s for a manual `refl`); the cost is the
//! normalizer's PROOF-TERM construction. The concrete `(G_A*)` is therefore left
//! to a lower-degree (atomized) normalizer or a manual compact certificate; the
//! ABSTRACT reduction above is the kernel-checked, axiom-free content landed here.
//!
//! Each registered declaration is `Declaration::Theorem`, `ProofQuality::Constructive`,
//! with an EMPTY admitted-axiom closure (foundational only). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural` / `native_decide` / `unsafe` /
//! `Axiom`. FORBIDDEN here: `Rat.dist`, `Real`, `Real.sqrt`, `NNReal.sqrt` (the
//! per-point route is POLYNOMIAL — no sqrt).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// A flat monomial `(num, den, r_exp, s_exp)` — coefficient `num/den` times
/// `r^{r_exp}·s^{s_exp}`. Coefficients are in lowest terms and validated by the
/// symbolic certificate check (see module docs).
type MonoRow = (u64, u64, u32, u32);

/// `OCTIC := 13r⁸+52r⁷s+130r⁶s²+100r⁵s³+58r⁴s⁴+100r³s⁵+130r²s⁶+52rs⁷+13s⁸`.
/// All coefficients positive ⇒ `OCTIC ≥ 0` on the orthant.
const OCTIC_TERMS: &[MonoRow] = &[
    (13, 1, 0, 8),
    (52, 1, 1, 7),
    (130, 1, 2, 6),
    (100, 1, 3, 5),
    (58, 1, 4, 4),
    (100, 1, 5, 3),
    (130, 1, 6, 2),
    (52, 1, 7, 1),
    (13, 1, 8, 0),
];

/// Cached carrier atoms + smart-constructors for the per-point CT bricks.
struct PerPointConsts {
    nnreal: Expr,
    nnreal_zero: Expr,
    nnreal_zero_add: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_le: Expr,
    nnreal_of_rat: Expr,
    rat_mk: Expr,
    int_of_nat: Expr,
    rat_zero: Expr,
    rat_le_of_ble_eq_true: Expr,
    bool_c: Expr,
    bool_true: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    // Landed NNReal lemmas used by the assembly.
    nnreal_mul_add: Expr,
    nnreal_add_assoc: Expr,
    nnreal_le_self_add: Expr,
    nnreal_add_right_cancel: Expr,
}

impl PerPointConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            nnreal: k("NNReal"),
            nnreal_zero: k("NNReal.zero"),
            nnreal_zero_add: k("NNReal.zero_add"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_le: k("NNReal.le"),
            nnreal_of_rat: k("NNReal.ofRat"),
            rat_mk: k("Rat.mk"),
            int_of_nat: k("Int.ofNat"),
            rat_zero: k("Rat.zero"),
            rat_le_of_ble_eq_true: k("Rat.le_of_ble_eq_true"),
            bool_c: k("Bool"),
            bool_true: k("Bool.true"),
            eq1: kl("Eq"),
            eq_refl1: kl("Eq.refl"),
            eq_symm1: kl("Eq.symm"),
            eq_subst1: kl("Eq.subst"),
            nnreal_mul_add: k("NNReal.mul_add"),
            nnreal_add_assoc: k("NNReal.add_assoc"),
            nnreal_le_self_add: k("NNReal.le_self_add"),
            nnreal_add_right_cancel: k("NNReal.add_right_cancel"),
        }
    }

    // ── Rat / NNReal literal constructors ────────────────────────────────────
    fn nat_lit(&self, n: u64) -> Expr {
        Expr::nat_lit(n)
    }
    fn frac(&self, num: u64, den: u64) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(num)),
                self.nat_lit(den),
            ],
        )
    }
    fn refl_true(&self) -> Expr {
        Expr::apps(
            self.eq_refl1.clone(),
            [self.bool_c.clone(), self.bool_true.clone()],
        )
    }
    fn lit_nonneg(&self, num: u64, den: u64) -> Expr {
        Expr::apps(
            self.rat_le_of_ble_eq_true.clone(),
            [self.rat_zero.clone(), self.frac(num, den), self.refl_true()],
        )
    }
    /// `NNReal.ofRat (num/den) (nonneg)`.
    fn of_frac(&self, num: u64, den: u64) -> Expr {
        Expr::apps(
            self.nnreal_of_rat.clone(),
            [self.frac(num, den), self.lit_nonneg(num, den)],
        )
    }

    // ── NNReal smart-constructors ────────────────────────────────────────────
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nnadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }

    // ── Eq.{1} over NNReal ───────────────────────────────────────────────────
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
    fn subst_nn(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }

    /// `a·p = a·q` from `h : p = q` (NNReal), via `Eq.subst` on the right factor.
    fn congr_mul_right(
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

    // ── Landed lemma applications ────────────────────────────────────────────
    /// `NNReal.mul_add c a b : c·(a+b) = c·a + c·b`.
    fn mul_add(&self, c: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_add.clone(),
            [c.clone(), a.clone(), b.clone()],
        )
    }
    /// `NNReal.add_assoc a b c : (a+b)+c = a+(b+c)`.
    fn add_assoc(&self, a: &Expr, b: &Expr, c: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_assoc.clone(),
            [a.clone(), b.clone(), c.clone()],
        )
    }
    /// `NNReal.zero_add a : NNReal.add NNReal.zero a = a`.
    fn zero_add(&self, a: &Expr) -> Expr {
        Expr::apps(self.nnreal_zero_add.clone(), [a.clone()])
    }
    /// `NNReal.le_self_add a b : NNReal.le a (NNReal.add a b)`.
    fn le_self_add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le_self_add.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.add_right_cancel a b c (add a c = add b c) : a = b`.
    fn add_right_cancel(&self, a: &Expr, b: &Expr, c: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_right_cancel.clone(),
            [a.clone(), b.clone(), c.clone(), h],
        )
    }

    // ── Flat monomial-polynomial builders ────────────────────────────────────
    /// `r^{r_exp}·s^{s_exp}·ofRat(coeff)` — atoms ascending by id (r then s),
    /// right-nested, coefficient on the right.
    fn monomial(&self, r: &Expr, s: &Expr, row: &MonoRow) -> Expr {
        let (num, den, re, se) = *row;
        let coeff = self.of_frac(num, den);
        let total = re + se;
        if total == 0 {
            return coeff;
        }
        let mut atoms: Vec<&Expr> = Vec::with_capacity(total as usize);
        for _ in 0..re {
            atoms.push(r);
        }
        for _ in 0..se {
            atoms.push(s);
        }
        let (last, init) = atoms.split_last().expect("nonempty");
        let mut prod = (*last).clone();
        for a in init.iter().rev() {
            prod = self.nnmul(a, &prod);
        }
        self.nnmul(&prod, &coeff)
    }

    /// A flat polynomial `Σ coeffᵢ·rⁱsʲ` as a right-associated `add`-sum of
    /// monomials. PRECONDITION: non-empty.
    fn poly(&self, r: &Expr, s: &Expr, rows: &[MonoRow]) -> Expr {
        let (last, init) = rows.split_last().expect("poly: non-empty rows");
        let mut acc = self.monomial(r, s, last);
        for row in init.iter().rev() {
            acc = self.nnadd(&self.monomial(r, s, row), &acc);
        }
        acc
    }
}

impl Environment {
    /// Initialize the per-point CT polynomial-certificate bricks. Pulls in the
    /// `NNReal` order/algebra surface, then registers the bricks. Idempotent.
    /// No axiom added or removed.
    pub fn init_boolean_analysis_per_point_ct(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_mul_distrib()?; // NNReal.mul_add
        self.init_algebra_nnreal_add_comm_assoc()?; // NNReal.add_assoc
        self.init_algebra_nnreal_zero_add()?; // NNReal.zero, NNReal.zero_add
        self.init_algebra_nnreal_le_self_add()?; // NNReal.le_self_add
        self.init_algebra_nnreal_cancel()?; // NNReal.add_right_cancel
        self.init_eq()?;

        let c = PerPointConsts::new();
        self.register_octic_nonneg(&c)?;
        self.register_reduction(&c)?;
        Ok(())
    }

    /// `BoolAnalysis.per_point_ct_octic_nonneg` — `NNReal.zero ≤ OCTIC(r,s)`.
    fn register_octic_nonneg(&mut self, c: &PerPointConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.per_point_ct_octic_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_octic_nonneg(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.per_point_ct_reduction` — the abstract per-point reduction.
    fn register_reduction(&mut self, c: &PerPointConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.per_point_ct_reduction");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_reduction(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

// ─── Certificate positivity — OCTIC ≥ 0 ──────────────────────────────────────

/// `(type, value)` of `∀ r s : NNReal, NNReal.zero ≤ OCTIC(r,s)`.
///
/// `OCTIC` is a right-associated sum of positive-coefficient monomials, hence
/// nonneg. Proof: `le_self_add NNReal.zero OCTIC : zero ≤ zero + OCTIC`, then
/// transport along `zero_add OCTIC : zero + OCTIC = OCTIC` to land `zero ≤ OCTIC`.
fn build_octic_nonneg(c: &PerPointConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (r_id, r) = b.fresh_local(c.nnreal.clone());
        let (s_id, s) = b.fresh_local(c.nnreal.clone());
        let octic = c.poly(&r, &s, OCTIC_TERMS);
        let concl = c.nnle(&c.nnreal_zero.clone(), &octic);
        let e = b.mk_pi(s_id, BinderInfo::Default, c.nnreal.clone(), concl);
        b.finish(b.mk_pi(r_id, BinderInfo::Default, c.nnreal.clone(), e))
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (r_id, r) = b.fresh_local(c.nnreal.clone());
        let (s_id, s) = b.fresh_local(c.nnreal.clone());
        let octic = c.poly(&r, &s, OCTIC_TERMS);
        let zero = c.nnreal_zero.clone();
        let zero_plus_octic = c.nnadd(&zero, &octic);
        let floor_raw = c.le_self_add(&zero, &octic); // zero ≤ zero + OCTIC
        let id0 = c.zero_add(&octic); // zero + OCTIC = OCTIC
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = m.fresh_local(c.nnreal.clone());
            let body = c.nnle(&zero, &z);
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let body = c.subst_nn(motive, &zero_plus_octic, &octic, id0, floor_raw);
        let e = b.mk_lam(s_id, BinderInfo::Default, c.nnreal.clone(), body);
        b.finish(b.mk_lam(r_id, BinderInfo::Default, c.nnreal.clone(), e))
    };
    (ty, value)
}

// ─── The abstract per-point reduction ────────────────────────────────────────

/// `(type, value)` of the abstract per-point CT reduction:
///
/// ```text
///   ∀ (bb tt kk cneg cpos e : NNReal),
///     Eq NNReal (add bb (mul kk cneg)) (add tt (mul kk cpos)) →   -- (G_A*)
///     Eq NNReal cpos (add e cneg) →                               -- hc : e=(r−s)⁴
///       NNReal.le tt bb.
/// ```
///
/// Proof (pure semiring algebra over the atoms):
///   - `pCpos : kk·cpos = kk·e + kk·cneg`  (`congr_mul_right hc` then `mul_add`).
///   - rewrite `(G_A*)` RHS: `tt + kk·cpos = tt + (kk·e + kk·cneg)`;
///     `add_assoc` symm: `= (tt + kk·e) + kk·cneg`.
///   - so `bb + kk·cneg = (tt + kk·e) + kk·cneg`; `add_right_cancel` ⇒
///     `bb = tt + kk·e`.
///   - `le_self_add tt (kk·e) : tt ≤ tt + kk·e`; transport along `bb = tt+kk·e`
///     (symm) ⇒ `tt ≤ bb`.
fn build_reduction(c: &PerPointConsts) -> (Expr, Expr) {
    let schema = |b: &mut EnvDeclBuilder| {
        let (bb_id, bb) = b.fresh_local(c.nnreal.clone());
        let (tt_id, tt) = b.fresh_local(c.nnreal.clone());
        let (kk_id, kk) = b.fresh_local(c.nnreal.clone());
        let (cneg_id, cneg) = b.fresh_local(c.nnreal.clone());
        let (cpos_id, cpos) = b.fresh_local(c.nnreal.clone());
        let (e_id, e) = b.fresh_local(c.nnreal.clone());
        let kcneg = c.nnmul(&kk, &cneg);
        let kcpos = c.nnmul(&kk, &cpos);
        // hGA : add bb (kk·cneg) = add tt (kk·cpos).
        let hga_ty = c.eq_nn(&c.nnadd(&bb, &kcneg), &c.nnadd(&tt, &kcpos));
        let (hga_id, hga) = b.fresh_local(hga_ty.clone());
        // hc : cpos = add e cneg.
        let hc_ty = c.eq_nn(&cpos, &c.nnadd(&e, &cneg));
        let (hc_id, hc) = b.fresh_local(hc_ty.clone());
        (
            (bb_id, tt_id, kk_id, cneg_id, cpos_id, e_id, hga_id, hc_id),
            (
                bb, tt, kk, cneg, cpos, e, hga, hc, kcneg, kcpos, hga_ty, hc_ty,
            ),
        )
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (ids, vals) = schema(&mut b);
        let (bb_id, tt_id, kk_id, cneg_id, cpos_id, e_id, hga_id, hc_id) = ids;
        let (bb, tt, _kk, _cneg, _cpos, _e, _hga, _hc, _kcneg, _kcpos, hga_ty, hc_ty) = vals;
        let concl = c.nnle(&tt, &bb);
        let e1 = b.mk_pi(hc_id, BinderInfo::Default, hc_ty, concl);
        let e1 = b.mk_pi(hga_id, BinderInfo::Default, hga_ty, e1);
        let e1 = b.mk_pi(e_id, BinderInfo::Default, c.nnreal.clone(), e1);
        let e1 = b.mk_pi(cpos_id, BinderInfo::Default, c.nnreal.clone(), e1);
        let e1 = b.mk_pi(cneg_id, BinderInfo::Default, c.nnreal.clone(), e1);
        let e1 = b.mk_pi(kk_id, BinderInfo::Default, c.nnreal.clone(), e1);
        let e1 = b.mk_pi(tt_id, BinderInfo::Default, c.nnreal.clone(), e1);
        b.finish(b.mk_pi(bb_id, BinderInfo::Default, c.nnreal.clone(), e1))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (ids, vals) = schema(&mut b);
        let (bb_id, tt_id, kk_id, cneg_id, cpos_id, e_id, hga_id, hc_id) = ids;
        let (bb, tt, kk, cneg, cpos, e, hga, hc, kcneg, kcpos, hga_ty, hc_ty) = vals;

        let kce = c.nnmul(&kk, &e);
        let e_plus_cneg = c.nnadd(&e, &cneg);
        let kce_plus_kcneg = c.nnadd(&kce, &kcneg);
        let tt_plus_kcpos = c.nnadd(&tt, &kcpos);
        let tt_plus_kce = c.nnadd(&tt, &kce);

        // pCpos : kk·cpos = kk·e + kk·cneg.
        let kk_eplus = c.nnmul(&kk, &e_plus_cneg);
        let step1 = c.congr_mul_right(&b, &kk, &cpos, &e_plus_cneg, hc); // kk·cpos = kk·(e+cneg)
        let step2 = c.mul_add(&kk, &e, &cneg); // kk·(e+cneg) = kk·e + kk·cneg
        let p_cpos = c.subst_for_trans(&kk, &cpos, &kk_eplus, &kce_plus_kcneg, step1, step2);

        // rewrite (G_A*) RHS `tt + kk·cpos` → `tt + (kk·e + kk·cneg)` via pCpos on
        // the right summand of the add.
        let tt_plus_kceplus = c.nnadd(&tt, &kce_plus_kcneg);
        // motive z := add bb kcneg = add tt z, transporting the RHS's kk·cpos→…
        let hga2 = {
            // hga : add bb kcneg = add tt kcpos. Substitute kcpos → kce_plus_kcneg
            // using pCpos : kcpos = kce_plus_kcneg (i.e. rewrite the RHS).
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = m.fresh_local(c.nnreal.clone());
                let body = c.eq_nn(&c.nnadd(&bb, &kcneg), &c.nnadd(&tt, &z));
                m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
            };
            c.subst_nn(motive, &kcpos, &kce_plus_kcneg, p_cpos, hga)
        };
        // hga2 : add bb kcneg = add tt (kk·e + kk·cneg).

        // add_assoc symm: tt + (kk·e + kk·cneg) = (tt + kk·e) + kk·cneg.
        let assoc = c.add_assoc(&tt, &kce, &kcneg); // (tt+kce)+kcneg = tt+(kce+kcneg)
        let assoc_symm = c.symm_nn(&c.nnadd(&tt_plus_kce, &kcneg), &tt_plus_kceplus, assoc);
        // chain hga2 with assoc_symm: add bb kcneg = (tt+kce)+kcneg.
        let hga3 = {
            // transport hga2's RHS `tt + (kce+kcneg)` → `(tt+kce)+kcneg`.
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = m.fresh_local(c.nnreal.clone());
                let body = c.eq_nn(&c.nnadd(&bb, &kcneg), &z);
                m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
            };
            c.subst_nn(
                motive,
                &tt_plus_kceplus,
                &c.nnadd(&tt_plus_kce, &kcneg),
                assoc_symm,
                hga2,
            )
        };
        // hga3 : add bb kcneg = add (tt+kce) kcneg.

        // add_right_cancel bb (tt+kce) kcneg hga3 : bb = tt + kce.
        let bb_eq = c.add_right_cancel(&bb, &tt_plus_kce, &kcneg, hga3);

        // le_self_add tt kce : tt ≤ tt + kce. Transport RHS (tt+kce) → bb via
        // `symm bb_eq : (tt+kce) = bb`.
        let floor = c.le_self_add(&tt, &kce); // tt ≤ tt + kce
        let bb_eq_symm = c.symm_nn(&bb, &tt_plus_kce, bb_eq); // (tt+kce) = bb
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = m.fresh_local(c.nnreal.clone());
            let body = c.nnle(&tt, &z);
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let body = c.subst_nn(motive, &tt_plus_kce, &bb, bb_eq_symm, floor);

        let _ = (&hga_ty, &hc_ty, &cneg, &cpos, &e, &kk, &bb, &tt);
        let e1 = b.mk_lam(
            hc_id,
            BinderInfo::Default,
            c.eq_nn(&cpos, &e_plus_cneg),
            body,
        );
        let e1 = b.mk_lam(
            hga_id,
            BinderInfo::Default,
            c.eq_nn(&c.nnadd(&bb, &kcneg), &tt_plus_kcpos),
            e1,
        );
        let e1 = b.mk_lam(e_id, BinderInfo::Default, c.nnreal.clone(), e1);
        let e1 = b.mk_lam(cpos_id, BinderInfo::Default, c.nnreal.clone(), e1);
        let e1 = b.mk_lam(cneg_id, BinderInfo::Default, c.nnreal.clone(), e1);
        let e1 = b.mk_lam(kk_id, BinderInfo::Default, c.nnreal.clone(), e1);
        let e1 = b.mk_lam(tt_id, BinderInfo::Default, c.nnreal.clone(), e1);
        b.finish(b.mk_lam(bb_id, BinderInfo::Default, c.nnreal.clone(), e1))
    };
    (ty, value)
}

impl PerPointConsts {
    /// `Eq.trans`-style chaining specialised to `a·p = …`: given
    /// `h1 : a·p = mid` and `h2 : mid = q`, produce `a·p = q`. (A thin wrapper to
    /// keep `build_reduction` readable; uses `Eq.subst` to avoid spelling out the
    /// full `Eq.trans` argument list.)
    fn subst_for_trans(
        &self,
        a: &Expr,
        p: &Expr,
        mid: &Expr,
        q: &Expr,
        h1: Expr,
        h2: Expr,
    ) -> Expr {
        // h1 : (a·p) = mid ; h2 : mid = q. Rewrite mid → q in h1 via Eq.subst on h2.
        let ap = self.nnmul(a, p);
        let parent = EnvDeclBuilder::new();
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&parent);
            let (z_id, z) = m.fresh_local(self.nnreal.clone());
            let body = self.eq_nn(&ap, &z);
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.subst_nn(motive, mid, q, h2, h1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "BoolAnalysis.per_point_ct_octic_nonneg",
        "BoolAnalysis.per_point_ct_reduction",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_per_point_ct()
            .expect("init_boolean_analysis_per_point_ct");
        env.init_boolean_analysis_per_point_ct()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_per_point_ct_bricks_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_per_point_ct_bricks_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
