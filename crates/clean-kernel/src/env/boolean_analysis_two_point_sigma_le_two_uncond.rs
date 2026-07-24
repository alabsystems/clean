// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! M2 lemma (A) σ-route, PIECE 2 — the UNCONDITIONAL surface bound
//! `BoolAnalysis.two_point_sigma_le_two`:
//!
//! ```text
//!   ∀ s r : NNReal,
//!     Eq NNReal (add ((s·s)·s) ((r·r)·r)) (ofRat 2)        -- s³ + r³ = 2
//!     → NNReal.le (add s r) (ofRat 2).                     -- s + r ≤ 2
//! ```
//!
//! This is the σ≤2 piece of the deg-9 σ-route, with NO undischarged `hsos`
//! hypothesis: the AM-GM leaf `2sr ≤ s²+r²` is built unconditionally here (it is
//! the genuine order content `0 ≤ (s−r)²`, which over the subtraction-free
//! `NNReal` carrier needs a `CauSeq` leaf — supplied here, lifted from the
//! constructive `Rat` AM-GM).
//!
//! # The route (all pieces axiom-free)
//!
//! On the surface `s³+r³ = 2`, the bound `s+r ≤ 2` follows from
//! `(s+r)³ ≤ 4·(s³+r³) = 8 = 2³` via `NNReal.le_of_cube_le_cube`. The cube
//! inequality `(s+r)³ ≤ 4(s³+r³)` is exactly `0 ≤ 3·(s−r)²·(s+r)`; over `NNReal`
//! we route it through the additive identity + AM-GM:
//!
//!  1. **(identity, via the poly helper)**
//!     `(s+r)³ + 3(s²+r²)(s+r) = 4(s³+r³) + 6·sr·(s+r)`.
//!     (True over the commutative semiring `NNReal` — both sides subtraction-free;
//!     `crate::env::nnreal_poly_normalize::prove_nnreal_poly_eq` emits the proof.)
//!  2. **(AM-GM × 3(s+r))** `6·sr·(s+r) ≤ 3(s²+r²)(s+r)`, from the unconditional
//!     leaf `2sr ≤ s²+r²` (here `NNReal.two_mul_le_add_sq`) times `3(s+r)` via
//!     `NNReal.mul_le_mul_left`.
//!  3. **(chain + add-cancel)** chaining (1)=(2)≤ then cancelling the shared
//!     `3(s²+r²)(s+r)` via `NNReal.le_of_add_le_add_right` gives
//!     `(s+r)³ ≤ 4(s³+r³)`.
//!  4. **(surface + de-cube)** `4(s³+r³) = 4·(ofRat 2) = ofRat 8 = (ofRat 2)³`
//!     (`hsurf` + `NNReal.ofRat_mul`), so `(s+r)³ ≤ (ofRat 2)³`, and
//!     `NNReal.le_of_cube_le_cube` finishes `s+r ≤ ofRat 2`.
//!
//! # The AM-GM leaf (the only genuinely new content)
//!
//! `NNReal.two_mul_le_add_sq : ∀ s r : NNReal,
//!     NNReal.le (add (mul s r)(mul s r)) (add (mul s s)(mul r r))`
//!
//! — i.e. `sr + sr ≤ s² + r²`. Proved by the standalone, POINTWISE `CauSeq` leaf
//! `NNReal.CauSeq.two_mul_le_add_sq` (the bound holds at EVERY index, so the
//! witness is `N := Nat.zero`, mirroring `NNReal.CauSeq.le_self_add`), lifted to
//! abstract `NNReal` by a two-fold `Quot.ind` (mirroring
//! `NNReal.mul_le_mul_left`). The pointwise `Rat` content `vs·vr + vs·vr ≤
//! vs·vs + vr·vr` reuses the LANDED constructive `Rat` AM-GM
//! `BoolAnalysis.two_mul_le_add_of_sq_le_mul` (`t²≤uv ⟹ (1+1)·t ≤ u+v`) with
//! `t := vs·vr`, `u := vs·vs`, `v := vr·vr` (the square hypothesis collapses to
//! `(vs·vr)·(vs·vr) = (vs·vs)·(vr·vr)` by `Rat.mul_mul_mul_comm`), then
//! `(1+1)·(vs·vr) → vs·vr + vs·vr` via `Rat.right_distrib` + `Rat.one_mul`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural` / `native_decide`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::nnreal_poly_normalize::prove_nnreal_poly_eq;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the σ≤2 build.
struct SigmaLeTwoConsts {
    // sorts / quotient plumbing.
    nat: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    causeq: Expr,
    causeq_equiv: Expr,
    // NNReal surface.
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_le: Expr,
    nnreal_of_rat: Expr,
    nnreal_ofrat_mul: Expr,
    nnreal_add_le_add: Expr,
    nnreal_le_refl: Expr,
    nnreal_mul_le_mul_left: Expr,
    nnreal_le_of_add_le_add_right: Expr,
    nnreal_le_of_cube_le_cube: Expr,
    // CauSeq / NNRat pointwise.
    causeq_seq: Expr,
    causeq_le: Expr,
    causeq_add: Expr,
    causeq_mul: Expr,
    nnrat_val: Expr,
    nnrat_mul: Expr,
    nnrat_val_mul: Expr,
    nnrat_property: Expr,
    // Rat surface.
    rat_mk: Expr,
    int_of_nat: Expr,
    rat_le_of_ble_eq_true: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    nat_le: Expr,
    rat_one: Expr,
    rat_add_zero: Expr,
    rat_one_mul: Expr,
    rat_right_distrib: Expr,
    rat_mul_mul_mul_comm: Expr,
    rat_le_refl: Expr,
    rat_mul_nonneg: Expr,
    rat_add_lt_add_left: Expr,
    rat_lt_of_le_of_lt: Expr,
    bool_c: Expr,
    bool_true: Expr,
    // landed Rat AM-GM.
    amgm: Expr, // BoolAnalysis.two_mul_le_add_of_sq_le_mul
    // logic / Eq.{1}.
    exists_intro: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
    quot_mk: Expr,
    quot_ind: Expr,
}

impl SigmaLeTwoConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            causeq: k("NNReal.CauSeq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_le: k("NNReal.le"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_ofrat_mul: k("NNReal.ofRat_mul"),
            nnreal_add_le_add: k("NNReal.add_le_add"),
            nnreal_le_refl: k("NNReal.le.refl"),
            nnreal_mul_le_mul_left: k("NNReal.mul_le_mul_left"),
            nnreal_le_of_add_le_add_right: k("NNReal.le_of_add_le_add_right"),
            nnreal_le_of_cube_le_cube: k("NNReal.le_of_cube_le_cube"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_le: k("NNReal.CauSeq.le"),
            causeq_add: k("NNReal.CauSeq.add"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            nnrat_val: k("NNRat.val"),
            nnrat_mul: k("NNRat.mul"),
            nnrat_val_mul: k("NNRat.val_mul"),
            nnrat_property: k("NNRat.property"),
            rat_mk: k("Rat.mk"),
            int_of_nat: k("Int.ofNat"),
            rat_le_of_ble_eq_true: k("Rat.le_of_ble_eq_true"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            nat_le: k("Nat.le"),
            rat_one: k("Rat.one"),
            rat_add_zero: k("Rat.add_zero"),
            rat_one_mul: k("Rat.one_mul"),
            rat_right_distrib: k("Rat.right_distrib"),
            rat_mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            rat_le_refl: k("Rat.le_refl"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            bool_c: k("Bool"),
            bool_true: k("Bool.true"),
            amgm: k("BoolAnalysis.two_mul_le_add_of_sq_le_mul"),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            eq1: kl("Eq"),
            eq_refl1: kl("Eq.refl"),
            eq_symm1: kl("Eq.symm"),
            eq_trans1: kl("Eq.trans"),
            eq_subst1: kl("Eq.subst"),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![l1]),
        }
    }

    // ── NNReal constructors ──────────────────────────────────────────────────
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nnadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    /// `(a·a)·a` (left-nested cube, matching `le_of_cube_le_cube`).
    fn nncube(&self, a: &Expr) -> Expr {
        self.nnmul(&self.nnmul(a, a), a)
    }
    /// `Rat.mk (Int.ofNat num) den`.
    fn frac(&self, num: u64, den: u64) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), Expr::nat_lit(num)),
                Expr::nat_lit(den),
            ],
        )
    }
    fn refl_true(&self) -> Expr {
        Expr::apps(
            self.eq_refl1.clone(),
            [self.bool_c.clone(), self.bool_true.clone()],
        )
    }
    /// `0 ≤ Rat.mk num den` for a positive literal fraction (boolean reflection).
    fn lit_nonneg(&self, num: u64, den: u64) -> Expr {
        Expr::apps(
            self.rat_le_of_ble_eq_true.clone(),
            [self.rat_zero.clone(), self.frac(num, den), self.refl_true()],
        )
    }
    /// `NNReal.ofRat (num/den) (0 ≤ ·)`.
    fn of_frac(&self, num: u64, den: u64) -> Expr {
        Expr::apps(
            self.nnreal_of_rat.clone(),
            [self.frac(num, den), self.lit_nonneg(num, den)],
        )
    }
    /// `NNReal.ofRat_mul a b ha hb hab : ofRat a · ofRat b = ofRat (a·b)`.
    fn ofrat_mul(&self, (na, da): (u64, u64), (nb, db): (u64, u64)) -> Expr {
        let ra = self.frac(na, da);
        let rb = self.frac(nb, db);
        let ha = self.lit_nonneg(na, da);
        let hb = self.lit_nonneg(nb, db);
        // free-representative product (matches the kernel's Rat.mul Quot.lift).
        let hab = self.lit_nonneg(na * nb, da * db);
        Expr::apps(self.nnreal_ofrat_mul.clone(), [ra, rb, ha, hb, hab])
    }
    /// `NNReal.add_le_add a b c d (a≤b)(c≤d) : (a+c) ≤ (b+d)`.
    #[allow(clippy::too_many_arguments)]
    fn add_le_add(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_le_add.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone(), hab, hcd],
        )
    }
    /// `NNReal.le.refl a : a ≤ a`.
    fn le_refl(&self, a: &Expr) -> Expr {
        Expr::app(self.nnreal_le_refl.clone(), a.clone())
    }
    /// `NNReal.mul_le_mul_left a c d (c≤d) : a·c ≤ a·d`.
    fn mul_le_mul_left(&self, a: &Expr, cc: &Expr, d: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_le_mul_left.clone(),
            [a.clone(), cc.clone(), d.clone(), h],
        )
    }
    /// `NNReal.le_of_add_le_add_right a b c (a+c ≤ b+c) : a ≤ b`.
    fn le_of_add_le_add_right(&self, a: &Expr, b: &Expr, cc: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_of_add_le_add_right.clone(),
            [a.clone(), b.clone(), cc.clone(), h],
        )
    }
    /// `NNReal.le_of_cube_le_cube a b (a³ ≤ b³) : a ≤ b`.
    fn le_of_cube_le_cube(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_of_cube_le_cube.clone(),
            [a.clone(), b.clone(), h],
        )
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

    /// `NNReal` quotient carrier `Quot CauSeq Equiv`.
    fn nnreal_q(&self) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Quot"), vec![Level::succ(Level::zero())]),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
    /// `@Quot.mk.{1} CauSeq Equiv l : NNReal`.
    fn quot_mk(&self, l: &Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l.clone()],
        )
    }

    // ── Rat / CauSeq pointwise constructors ──────────────────────────────────
    fn radd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a.clone(), b.clone()])
    }
    fn rmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a.clone(), b.clone()])
    }
    fn rlt(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a.clone(), b.clone()])
    }
    fn rle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a.clone(), b.clone()])
    }
    fn nat_le_e(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a.clone(), b.clone()])
    }
    /// `CauSeq.seq x n : NNRat`.
    fn seq_at(&self, x: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone())
    }
    /// `NNRat.val (CauSeq.seq x n) : Rat`.
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), self.seq_at(x, n))
    }
    /// `CauSeq.add a b`.
    fn cau_add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.causeq_add.clone(), [a.clone(), b.clone()])
    }
    /// `CauSeq.mul a b`.
    fn cau_mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.causeq_mul.clone(), [a.clone(), b.clone()])
    }
    /// `CauSeq.le a b`.
    fn cau_le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.causeq_le.clone(), [a.clone(), b.clone()])
    }
    /// `NNRat.property q : 0 ≤ NNRat.val q`.
    fn property(&self, q: &Expr) -> Expr {
        Expr::app(self.nnrat_property.clone(), q.clone())
    }
    /// `NNRat.val_mul p q : val(mul p q) = val p · val q`.
    fn val_mul(&self, p: &Expr, q: &Expr) -> Expr {
        Expr::apps(self.nnrat_val_mul.clone(), [p.clone(), q.clone()])
    }

    // ── Rat Eq / subst helpers ───────────────────────────────────────────────
    fn eq_rat(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a.clone(), b.clone()])
    }
    fn refl_rat(&self, a: &Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), a.clone()])
    }
    fn symm_rat(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.rat.clone(), a.clone(), b.clone(), h],
        )
    }
    fn trans_rat(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.rat.clone(), a.clone(), b.clone(), cc.clone(), h1, h2],
        )
    }
    fn subst_rat(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn rmul_nonneg(&self, a: &Expr, b: &Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_nonneg.clone(), [a.clone(), b.clone(), ha, hb])
    }
    /// `Rat.le_refl a : a ≤ a`.
    fn rle_refl(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a.clone())
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr) -> Expr {
        Expr::apps(
            self.rat_mul_mul_mul_comm.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone()],
        )
    }
    /// `Rat.right_distrib a b c : (a+b)·c = a·c + b·c`.
    fn right_distrib(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.rat_right_distrib.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `Rat.one_mul a : 1·a = a`.
    fn one_mul(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a.clone())
    }
    /// `Rat.add_zero a : a+0 = a`.
    fn add_zero(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a.clone())
    }
    /// `Rat.add_lt_add_left a b c h : (c+a) < (c+b)`.
    fn add_lt_add_left(&self, a: &Expr, b: &Expr, cc: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.rat_add_lt_add_left.clone(),
            [a.clone(), b.clone(), cc.clone(), h],
        )
    }
    /// `Rat.lt_of_le_of_lt a b c h1 h2 : a < c`.
    fn lt_of_le_of_lt(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.rat_lt_of_le_of_lt.clone(),
            [a.clone(), b.clone(), cc.clone(), h1, h2],
        )
    }
    /// `BoolAnalysis.two_mul_le_add_of_sq_le_mul t u v ht hu hv hsq : (1+1)·t ≤ u+v`.
    #[allow(clippy::too_many_arguments)]
    fn amgm(&self, t: &Expr, u: &Expr, v: &Expr, ht: Expr, hu: Expr, hv: Expr, hsq: Expr) -> Expr {
        Expr::apps(
            self.amgm.clone(),
            [t.clone(), u.clone(), v.clone(), ht, hu, hv, hsq],
        )
    }
}

impl Environment {
    /// Register `NNReal.CauSeq.two_mul_le_add_sq`, `NNReal.two_mul_le_add_sq`,
    /// and `BoolAnalysis.two_point_sigma_le_two`. Idempotent; foundational-only.
    pub fn init_boolean_analysis_two_point_sigma_le_two_uncond(&mut self) -> Result<(), EnvError> {
        // surface infra used by the assembly.
        self.init_boolean_analysis_two_point_base_lemma_a()?; // ofRat_mul, ...
        self.init_algebra_nnreal_cube_mono()?; // NNReal.mul_le_mul_left, le.refl
        self.init_algebra_nnreal_le_add()?; // NNReal.add_le_add
        self.init_algebra_nnreal_cancel()?; // NNReal.le_of_add_le_add_right
        self.init_algebra_nnreal_reverse_cube()?; // NNReal.le_of_cube_le_cube
                                                  // pointwise AM-GM leaf infra.
        self.init_algebra_nnreal_mul_lift()?; // CauSeq.mul, NNReal.mul, NNRat.val_mul
        self.init_algebra_nnreal_add()?; // CauSeq.add, NNReal.add, NNRat.val_add
        self.init_algebra_nnreal_le()?; // CauSeq.le, NNReal.le
        self.init_algebra_nnreal_nnrat()?; // NNRat.property
        self.init_rat_field_inst()?; // Rat.add_zero, Rat.right_distrib, Rat.one_mul
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.init_boolean_analysis_order_toolkit_b1c()?; // Rat.lt_of_le_of_lt
        self.register_rat_order_proofs()?; // Rat.le_refl, Rat.mul_nonneg
        self.init_boolean_analysis_amgm()?; // BoolAnalysis.two_mul_le_add_of_sq_le_mul
                                            // NNReal semiring lemma surface used by `prove_nnreal_poly_eq` (Step 1).
        self.init_algebra_nnreal_semiring_units()?; // NNReal.mul_one, NNReal.add_zero
        self.init_algebra_nnreal_reverse_square_algebra()?; // mul_comm/mul_assoc/ofRat_mul
        self.init_algebra_nnreal_add_comm_assoc()?; // add_comm/add_assoc
        self.init_algebra_nnreal_mul_distrib()?; // mul_add
        self.init_algebra_nnreal_add_mul()?; // add_mul
        self.init_algebra_nnreal_finsum_ofrat()?; // ofRat_add
        self.init_exists()?;
        self.init_eq()?;

        let c = SigmaLeTwoConsts::new();
        self.register_causeq_two_mul_le_add_sq(&c)?;
        self.register_nnreal_two_mul_le_add_sq(&c)?;
        self.register_two_point_sigma_le_two(&c)?;
        Ok(())
    }

    /// `NNReal.CauSeq.two_mul_le_add_sq : ∀ fs fr : CauSeq,`
    /// `  CauSeq.le (add (mul fs fr)(mul fs fr)) (add (mul fs fs)(mul fr fr))`.
    fn register_causeq_two_mul_le_add_sq(&mut self, c: &SigmaLeTwoConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.two_mul_le_add_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (fs_id, fs) = b.fresh_local(c.causeq.clone());
            let (fr_id, fr) = b.fresh_local(c.causeq.clone());
            let sr = c.cau_mul(&fs, &fr);
            let lhs = c.cau_add(&sr, &sr);
            let ss = c.cau_mul(&fs, &fs);
            let rr = c.cau_mul(&fr, &fr);
            let rhs = c.cau_add(&ss, &rr);
            let concl = c.cau_le(&lhs, &rhs);
            let e = b.mk_pi(fr_id, BinderInfo::Default, c.causeq.clone(), concl);
            let e = b.mk_pi(fs_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        let value = build_causeq_two_mul_le_add_sq(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.two_mul_le_add_sq : ∀ s r : NNReal,`
    /// `  NNReal.le (add (mul s r)(mul s r)) (add (mul s s)(mul r r))`.
    fn register_nnreal_two_mul_le_add_sq(&mut self, c: &SigmaLeTwoConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.two_mul_le_add_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal_q();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(nnreal.clone());
            let (r_id, r) = b.fresh_local(nnreal.clone());
            let sr = c.nnmul(&s, &r);
            let lhs = c.nnadd(&sr, &sr);
            let ss = c.nnmul(&s, &s);
            let rr = c.nnmul(&r, &r);
            let rhs = c.nnadd(&ss, &rr);
            let concl = c.nnle(&lhs, &rhs);
            let e = b.mk_pi(r_id, BinderInfo::Default, nnreal.clone(), concl);
            let e = b.mk_pi(s_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_two_mul_le_add_sq(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.two_point_sigma_le_two : ∀ s r : NNReal,`
    /// `  Eq NNReal (add ((s·s)·s)((r·r)·r)) (ofRat 2) → NNReal.le (add s r)(ofRat 2)`.
    fn register_two_point_sigma_le_two(&mut self, c: &SigmaLeTwoConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.two_point_sigma_le_two");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_two_point_sigma_le_two(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The pointwise CauSeq AM-GM leaf.
// ─────────────────────────────────────────────────────────────────────────────

/// `NNReal.CauSeq.two_mul_le_add_sq` proof value: `sr+sr ≤ ss+rr` pointwise,
/// witness `N := Nat.zero` (the bound holds at every index).
fn build_causeq_two_mul_le_add_sq(c: &SigmaLeTwoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (fs_id, fs) = b.fresh_local(c.causeq.clone());
    let (fr_id, fr) = b.fresh_local(c.causeq.clone());

    let cl = c.cau_add(&c.cau_mul(&fs, &fr), &c.cau_mul(&fs, &fr)); // sr+sr (CauSeq)
    let cr = c.cau_add(&c.cau_mul(&fs, &fs), &c.cau_mul(&fr, &fr)); // ss+rr (CauSeq)

    // goal: CauSeq.le cl cr = ∀ ε, 0<ε → ∃ N, ∀ m, N≤m → vseq cl m < vseq cr m + ε.
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.rlt(&c.rat_zero, &eps);
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le_e(&c.nat_zero, &m);
        let (hle_id, _hle) = bw.fresh_local(hle_ty.clone());
        let proof = build_causeq_leaf(c, &bw, &fs, &fr, &m, &eps, &hpos);
        let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
        let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
        bw.finish_child(e)
    };

    let intro = Expr::apps(
        c.exists_intro.clone(),
        [
            c.nat.clone(),
            pred_n(c, &b, &cl, &cr, &eps),
            c.nat_zero.clone(),
            witness,
        ],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(fr_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(fs_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// `fun N => ∀ m, N≤m → vseq cl m < vseq cr m + ε`.
fn pred_n(c: &SigmaLeTwoConsts, parent: &EnvDeclBuilder, cl: &Expr, cr: &Expr, eps: &Expr) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (n_id, n_cap) = bn.fresh_local(c.nat.clone());
    let inner = {
        let mut bm = EnvDeclBuilder::child_of(&bn);
        let (m_id, m) = bm.fresh_local(c.nat.clone());
        let hle = c.nat_le_e(&n_cap, &m);
        let (hle_id, _hle) = bm.fresh_local(hle.clone());
        let dom = c.rlt(&c.vseq(cl, &m), &c.radd(&c.vseq(cr, &m), eps));
        let e = bm.mk_pi(hle_id, BinderInfo::Default, hle, dom);
        let e = bm.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
        bm.finish_child(e)
    };
    bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner))
}

/// At index `m`, the domination leaf `vseq(sr+sr) m < vseq(ss+rr) m + ε`.
fn build_causeq_leaf(
    c: &SigmaLeTwoConsts,
    parent: &EnvDeclBuilder,
    fs: &Expr,
    fr: &Expr,
    m: &Expr,
    eps: &Expr,
    hpos: &Expr,
) -> Expr {
    let vs = c.vseq(fs, m);
    let vr = c.vseq(fr, m);
    let vs_vr = c.rmul(&vs, &vr); // vs·vr
    let vs_vs = c.rmul(&vs, &vs); // vs·vs
    let vr_vr = c.rmul(&vr, &vr); // vr·vr
    let lhs_pt = c.radd(&vs_vr, &vs_vr); // vs·vr + vs·vr
    let rhs_pt = c.radd(&vs_vs, &vr_vr); // vs·vs + vr·vr

    // h_le : (vs·vr + vs·vr) ≤ (vs·vs + vr·vr)  — pointwise Rat AM-GM.
    let h_le = build_rat_amgm(c, parent, fs, fr, m);

    // h_lt0 : rhs_pt + 0 < rhs_pt + ε   (add_lt_add_left 0 ε rhs_pt hpos).
    let h_lt0 = c.add_lt_add_left(&c.rat_zero, eps, &rhs_pt, hpos.clone());
    let rhs_zero = c.radd(&rhs_pt, &c.rat_zero);
    let rhs_eps = c.radd(&rhs_pt, eps);
    let motive_lt = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(&t, &rhs_eps);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let h_lt = c.subst_rat(motive_lt, &rhs_zero, &rhs_pt, c.add_zero(&rhs_pt), h_lt0);

    // chain : lhs_pt < rhs_pt + ε.
    let chain = c.lt_of_le_of_lt(&lhs_pt, &rhs_pt, &rhs_eps, h_le, h_lt);

    // Transport so the conclusion matches the GOAL's reduced form:
    //   vseq(sr+sr) m < vseq(ss+rr) m + ε
    // ≡ val(add (mul fs fr)(mul fs fr)) < val(add (mul fs fs)(mul fr fr)) + ε.
    let seq_fs = c.seq_at(fs, m);
    let seq_fr = c.seq_at(fr, m);
    let sr_q = Expr::apps(c.nnrat_mul.clone(), [seq_fs.clone(), seq_fr.clone()]);
    let ss_q = Expr::apps(c.nnrat_mul.clone(), [seq_fs.clone(), seq_fs.clone()]);
    let rr_q = Expr::apps(c.nnrat_mul.clone(), [seq_fr.clone(), seq_fr.clone()]);

    let val_sr = c.val_mul(&seq_fs, &seq_fr); // val(sr_q) = vs·vr
    let val_sr_q = Expr::app(c.nnrat_val.clone(), sr_q);
    let val_ss = c.val_mul(&seq_fs, &seq_fs); // val(ss_q) = vs·vs
    let val_ss_q = Expr::app(c.nnrat_val.clone(), ss_q);
    let val_rr = c.val_mul(&seq_fr, &seq_fr); // val(rr_q) = vr·vr
    let val_rr_q = Expr::app(c.nnrat_val.clone(), rr_q);

    // rewrite LHS left vs·vr → val(sr_q).
    let chain = {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = mb.fresh_local(c.rat.clone());
            let body = c.rlt(&c.radd(&z, &vs_vr), &rhs_eps);
            mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let symm = c.symm_rat(&val_sr_q, &vs_vr, val_sr.clone());
        c.subst_rat(motive, &vs_vr, &val_sr_q, symm, chain)
    };
    // rewrite LHS right vs·vr → val(sr_q).
    let chain = {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = mb.fresh_local(c.rat.clone());
            let body = c.rlt(&c.radd(&val_sr_q, &z), &rhs_eps);
            mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let symm = c.symm_rat(&val_sr_q, &vs_vr, val_sr);
        c.subst_rat(motive, &vs_vr, &val_sr_q, symm, chain)
    };
    let lhs_goal = c.radd(&val_sr_q, &val_sr_q);
    // rewrite RHS vs·vs → val(ss_q).
    let chain = {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = mb.fresh_local(c.rat.clone());
            let body = c.rlt(&lhs_goal, &c.radd(&c.radd(&z, &vr_vr), eps));
            mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let symm = c.symm_rat(&val_ss_q, &vs_vs, val_ss);
        c.subst_rat(motive, &vs_vs, &val_ss_q, symm, chain)
    };
    // rewrite RHS vr·vr → val(rr_q). The result `(val(sr_q)+val(sr_q)) <
    // (val(ss_q)+val(rr_q)) + ε` is defeq to the goal.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(&lhs_goal, &c.radd(&c.radd(&val_ss_q, &z), eps));
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let symm = c.symm_rat(&val_rr_q, &vr_vr, val_rr);
    c.subst_rat(motive, &vr_vr, &val_rr_q, symm, chain)
}

/// Pointwise `Rat` AM-GM: `(vs·vr + vs·vr) ≤ (vs·vs + vr·vr)` where
/// `vs := vseq fs m`, `vr := vseq fr m` (both `NNRat.val …`, hence nonneg).
fn build_rat_amgm(
    c: &SigmaLeTwoConsts,
    parent: &EnvDeclBuilder,
    fs: &Expr,
    fr: &Expr,
    m: &Expr,
) -> Expr {
    let y = c.vseq(fs, m); // vs
    let d = c.vseq(fr, m); // vr
    let yd = c.rmul(&y, &d);
    let yy = c.rmul(&y, &y);
    let dd = c.rmul(&d, &d);
    let yy_dd = c.radd(&yy, &dd); // y·y + d·d

    // nonneg witnesses from NNRat.property.
    let h0y = c.property(&c.seq_at(fs, m)); // 0 ≤ vs
    let h0d = c.property(&c.seq_at(fr, m)); // 0 ≤ vr
    let h0yd = c.rmul_nonneg(&y, &d, h0y.clone(), h0d.clone()); // 0 ≤ y·d
    let h0yy = c.rmul_nonneg(&y, &y, h0y.clone(), h0y); // 0 ≤ y·y
    let h0dd = c.rmul_nonneg(&d, &d, h0d.clone(), h0d); // 0 ≤ d·d

    // hsq : (y·d)·(y·d) ≤ (y·y)·(d·d), via the identity (y·d)·(y·d) = (y·y)·(d·d).
    let yd_yd = c.rmul(&yd, &yd);
    let yy_dd_mul = c.rmul(&yy, &dd);
    let eq_sq = c.mmmc(&y, &d, &y, &d); // (y·d)·(y·d) = (y·y)·(d·d)
    let refl_rhs = c.rle_refl(&yy_dd_mul);
    let motive_hsq = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(c.rat.clone());
        let body = c.rle(&z, &yy_dd_mul);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let hsq = c.subst_rat(
        motive_hsq,
        &yy_dd_mul,
        &yd_yd,
        c.symm_rat(&yd_yd, &yy_dd_mul, eq_sq),
        refl_rhs,
    );

    // amgm : (1+1)·(y·d) ≤ y·y + d·d.
    let amgm = c.amgm(&yd, &yy, &dd, h0yd, h0yy, h0dd, hsq);

    // transport (1+1)·(y·d) → (y·d + y·d).
    let one = c.rat_one.clone();
    let one_plus_one = c.radd(&one, &one);
    let two_yd = c.rmul(&one_plus_one, &yd);
    let one_yd = c.rmul(&one, &yd);
    let rdist = c.right_distrib(&one, &one, &yd); // (1+1)·(y·d) = 1·(y·d)+1·(y·d)
    let one_yd_sum = c.radd(&one_yd, &one_yd);
    let om = c.one_mul(&yd); // 1·(y·d) = y·d

    let yd_plus_one_yd = c.radd(&yd, &one_yd);
    let step1 = {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = mb.fresh_local(c.rat.clone());
            let body = c.eq_rat(&one_yd_sum, &c.radd(&z, &one_yd));
            mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst_rat(motive, &one_yd, &yd, om.clone(), c.refl_rat(&one_yd_sum))
    };
    let yd_plus_yd = c.radd(&yd, &yd);
    let step2 = {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = mb.fresh_local(c.rat.clone());
            let body = c.eq_rat(&yd_plus_one_yd, &c.radd(&yd, &z));
            mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst_rat(motive, &one_yd, &yd, om, c.refl_rat(&yd_plus_one_yd))
    };
    let eq_fold = c.trans_rat(
        &two_yd,
        &one_yd_sum,
        &yd_plus_yd,
        rdist,
        c.trans_rat(&one_yd_sum, &yd_plus_one_yd, &yd_plus_yd, step1, step2),
    );

    let motive_final = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(c.rat.clone());
        let body = c.rle(&z, &yy_dd);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst_rat(motive_final, &two_yd, &yd_plus_yd, eq_fold, amgm)
}

/// `NNReal.two_mul_le_add_sq` via two nested `Quot.ind`s reducing the leaf to
/// `NNReal.CauSeq.two_mul_le_add_sq` (mirrors `NNReal.mul_le_mul_left`).
fn build_nnreal_two_mul_le_add_sq(c: &SigmaLeTwoConsts, nnreal: &Expr) -> Expr {
    let core = Expr::const_(Name::from_string("NNReal.CauSeq.two_mul_le_add_sq"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (s_id, s) = b.fresh_local(nnreal.clone());
    let (r_id, r) = b.fresh_local(nnreal.clone());

    let body = descend_s(c, &b, nnreal, &s, &r, &core);

    let e = b.mk_lam(r_id, BinderInfo::Default, nnreal.clone(), body);
    let e = b.mk_lam(s_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// Descend on `s`.
fn descend_s(
    c: &SigmaLeTwoConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    s: &Expr,
    r: &Expr,
    core: &Expr,
) -> Expr {
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let xr = c.nnmul(&x, r);
        let lhs = c.nnadd(&xr, &xr);
        let rhs = c.nnadd(&c.nnmul(&x, &x), &c.nnmul(r, r));
        let concl = c.nnle(&lhs, &rhs);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), concl))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (fs_id, fs) = mf.fresh_local(c.causeq.clone());
        let mks = c.quot_mk(&fs);
        let body = descend_r(c, &mf, nnreal, &mks, &fs, r, core);
        mf.finish_child(mf.mk_lam(fs_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            s.clone(),
        ],
    )
}

/// Descend on `r`. Leaf rep `fr` closes by `core fs fr`.
fn descend_r(
    c: &SigmaLeTwoConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mks: &Expr,
    fs: &Expr,
    r: &Expr,
    core: &Expr,
) -> Expr {
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = mb.fresh_local(nnreal.clone());
        let sy = c.nnmul(mks, &y);
        let lhs = c.nnadd(&sy, &sy);
        let rhs = c.nnadd(&c.nnmul(mks, mks), &c.nnmul(&y, &y));
        let concl = c.nnle(&lhs, &rhs);
        mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), concl))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (fr_id, fr) = mf.fresh_local(c.causeq.clone());
        let body = Expr::apps(core.clone(), [fs.clone(), fr.clone()]);
        mf.finish_child(mf.mk_lam(fr_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            r.clone(),
        ],
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// The σ≤2 assembly.
// ─────────────────────────────────────────────────────────────────────────────

/// `(type, value)` of `BoolAnalysis.two_point_sigma_le_two`.
fn build_two_point_sigma_le_two(c: &SigmaLeTwoConsts) -> (Expr, Expr) {
    let of2 = c.of_frac(2, 1);

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (s_id, s) = b.fresh_local(c.nnreal.clone());
        let (r_id, r) = b.fresh_local(c.nnreal.clone());
        let s3 = c.nncube(&s);
        let r3 = c.nncube(&r);
        let surf = c.nnadd(&s3, &r3);
        let hsurf_ty = c.eq_nn(&surf, &of2);
        let (h_id, _h) = b.fresh_local(hsurf_ty.clone());
        let concl = c.nnle(&c.nnadd(&s, &r), &of2);
        let e = b.mk_pi(h_id, BinderInfo::Default, hsurf_ty, concl);
        let e = b.mk_pi(r_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(b.mk_pi(s_id, BinderInfo::Default, c.nnreal.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        // FVar-id disjointness: `prove_nnreal_poly_eq` (Step 1) builds its proof
        // with its OWN `EnvDeclBuilder::new()`, whose motive FVars start at the
        // SAME base as ours. If our atoms `s,r` (and our child motive FVars)
        // overlapped the helper's range, an abstraction of `s` (id `base`) would
        // also capture a helper motive var with the same id. Reserve a large gap
        // first so `s,r` and all our motive FVars live strictly ABOVE the
        // helper's (bounded) range. The spacer locals are never used, so they do
        // not appear in the term and `finish` stays happy.
        for _ in 0..100_000 {
            let _ = b.fresh_local(c.nnreal.clone());
        }
        let (s_id, s) = b.fresh_local(c.nnreal.clone());
        let (r_id, r) = b.fresh_local(c.nnreal.clone());
        let s3 = c.nncube(&s);
        let r3 = c.nncube(&r);
        let surf = c.nnadd(&s3, &r3);
        let hsurf_ty = c.eq_nn(&surf, &of2);
        let (h_id, hsurf) = b.fresh_local(hsurf_ty.clone());

        let body = build_sigma_le_two_body(c, &b, &s, &r, &surf, &of2, hsurf);

        let e = b.mk_lam(h_id, BinderInfo::Default, hsurf_ty, body);
        let e = b.mk_lam(r_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(b.mk_lam(s_id, BinderInfo::Default, c.nnreal.clone(), e))
    };

    (ty, value)
}

/// The σ≤2 proof body (see module doc, steps 1–4).
#[allow(clippy::too_many_arguments)]
fn build_sigma_le_two_body(
    c: &SigmaLeTwoConsts,
    parent: &EnvDeclBuilder,
    s: &Expr,
    r: &Expr,
    surf: &Expr, // s³ + r³
    of2: &Expr,
    hsurf: Expr, // s³+r³ = ofRat 2
) -> Expr {
    let sigma = c.nnadd(s, r); // s + r
    let cube_sigma = c.nncube(&sigma); // (s+r)³
    let of3 = c.of_frac(3, 1);
    let of4 = c.of_frac(4, 1);

    let sr = c.nnmul(s, r); // s·r
    let two_sr = c.nnadd(&sr, &sr); // s·r + s·r   (= 2sr)
    let ss = c.nnmul(s, s); // s·s
    let rr = c.nnmul(r, r); // r·r
    let ss_rr = c.nnadd(&ss, &rr); // s² + r²

    // M := ofRat 3 · (s+r)   (the common multiplier of step 2).
    let m_factor = c.nnmul(&of3, &sigma);

    // C3 := M · (s²+r²) = 3·(s²+r²)·(s+r)  — the shared add-cancel term.
    let c3 = c.nnmul(&m_factor, &ss_rr);
    // six := M · (s·r + s·r) = 6·s·r·(s+r).
    let six = c.nnmul(&m_factor, &two_sr);
    // four_s3r3 := ofRat 4 · (s³ + r³).
    let four_s3r3 = c.nnmul(&of4, surf);

    // ── Step 1 (identity, helper): cube_sigma + C3 = four_s3r3 + six. ─────────
    let lhs_id = c.nnadd(&cube_sigma, &c3);
    let rhs_id = c.nnadd(&four_s3r3, &six);
    let step1 = prove_nnreal_poly_eq(&lhs_id, &rhs_id)
        .expect("σ-route Step 1: deg-3 NNReal poly identity must normalize");

    // ── Step 2 (AM-GM × M): six ≤ C3. ────────────────────────────────────────
    let amgm = Expr::apps(
        Expr::const_(Name::from_string("NNReal.two_mul_le_add_sq"), vec![]),
        [s.clone(), r.clone()],
    );
    let step2 = c.mul_le_mul_left(&m_factor, &two_sr, &ss_rr, amgm); // six ≤ C3

    // ── Step 3: chain + add-cancel ⟹ cube_sigma ≤ four_s3r3. ──────────────────
    let rhs_id_le = c.add_le_add(
        &four_s3r3,
        &four_s3r3,
        &six,
        &c3,
        c.le_refl(&four_s3r3),
        step2,
    ); // (four_s3r3 + six) ≤ (four_s3r3 + C3)

    let four_plus_six = c.nnadd(&four_s3r3, &six);
    let cube_plus_c3 = c.nnadd(&cube_sigma, &c3);
    let four_plus_c3 = c.nnadd(&four_s3r3, &c3);
    let motive_chain = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnle(&z, &four_plus_c3);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let chained = c.subst_nn(
        motive_chain,
        &four_plus_six,
        &cube_plus_c3,
        c.symm_nn(&cube_plus_c3, &four_plus_six, step1),
        rhs_id_le,
    ); // (cube_sigma + C3) ≤ (four_s3r3 + C3)

    let cube_le_four = c.le_of_add_le_add_right(&cube_sigma, &four_s3r3, &c3, chained);

    // ── Step 4: surface + de-cube. ───────────────────────────────────────────
    // rewrite four_s3r3 = ofRat 4 · (s³+r³) → ofRat 4 · (ofRat 2) via hsurf.
    let of4_of2 = c.nnmul(&of4, of2);
    let motive_surf = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnle(&cube_sigma, &c.nnmul(&of4, &z));
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let cube_le_44 = c.subst_nn(motive_surf, surf, of2, hsurf, cube_le_four);

    // ofRat 4 · ofRat 2 = ofRat 8.
    let of8 = c.of_frac(8, 1);
    let ofrat_mul_42 = c.ofrat_mul((4, 1), (2, 1));
    let motive_82 = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnle(&cube_sigma, &z);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let cube_le_8 = c.subst_nn(motive_82, &of4_of2, &of8, ofrat_mul_42, cube_le_44);

    // ofRat 8 = (ofRat 2)³ = ((ofRat 2)·(ofRat 2))·(ofRat 2).
    let cube_of2 = c.nncube(of2);
    let of2_of2 = c.nnmul(of2, of2);
    let e1 = c.ofrat_mul((2, 1), (2, 1)); // ofRat2·ofRat2 = ofRat 4
    let of4_again = c.of_frac(4, 1);
    let cong_inner = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(c.nnreal.clone());
        let body = c.eq_nn(&cube_of2, &c.nnmul(&z, of2));
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let cube_eq_42 = c.subst_nn(cong_inner, &of2_of2, &of4_again, e1, c.refl_nn(&cube_of2));
    let e2 = c.ofrat_mul((4, 1), (2, 1)); // ofRat4·ofRat2 = ofRat 8
    let of4again_of2 = c.nnmul(&of4_again, of2);
    let cube_eq_8 = c.trans_nn(&cube_of2, &of4again_of2, &of8, cube_eq_42, e2);

    let motive_decube = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnle(&cube_sigma, &z);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let cube_le_cube = c.subst_nn(
        motive_decube,
        &of8,
        &cube_of2,
        c.symm_nn(&cube_of2, &of8, cube_eq_8),
        cube_le_8,
    );

    c.le_of_cube_le_cube(&sigma, of2, cube_le_cube)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "NNReal.CauSeq.two_mul_le_add_sq",
        "NNReal.two_mul_le_add_sq",
        "BoolAnalysis.two_point_sigma_le_two",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_two_point_sigma_le_two_uncond()
            .expect("init_boolean_analysis_two_point_sigma_le_two_uncond");
        env.init_boolean_analysis_two_point_sigma_le_two_uncond()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_sigma_le_two_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_sigma_le_two_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
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
