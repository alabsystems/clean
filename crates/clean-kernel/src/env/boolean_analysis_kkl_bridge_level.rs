// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL hypercontractive BRIDGE — the LEVEL-RESTRICTION half (axiom-free).
//!
//! # Where this sits in the §9.6 bridge
//!
//! The genuine O'Donnell §9.6 per-coordinate bridge is
//!
//! ```text
//!   W^{≤k}[D_i f]  ≤  9^k · ‖T_{1/3} D_i f‖₂²            (A) low-band extraction
//!                  ≤  9^k · ‖D_i f‖_{4/3}²  =  9^k·4·Inf_i^{3/2}.   (B) DUAL HC step
//! ```
//!
//! Step (A) — the LEVEL RESTRICTION — is PURE rational `Rat.powNat`
//! exponent-monotonicity: it is the half that the `Rat`-only overlay CAN prove
//! axiom-free, and it is what isolates the genuinely-hard hypercontractive step
//! (B) (the dual `(4/3→2)` bound, NOT a syntactic consequence of the landed
//! FORWARD `hc24_at_third`). This module owns step (A) at the per-subset
//! granularity (the term-by-term atom), which `subsetSum_le_of_pointwise` lifts
//! to the full level-`≤k` mass.
//!
//! ## The inverse identity (the load-bearing scalar)
//!
//! ```text
//! Rat.nine_mul_inv_nine : Rat.mul (Rat.ofNat 9) (Rat.mk (Int.ofNat 1) 9) = Rat.one
//! Rat.powNat_nine_mul_inv_nine : ∀ k, (9^k)·((1/9)^k) = 1
//! ```
//!
//! `9·(1/9) = 1` is NOT `Eq.refl` — the live `Rat` is the QUOTIENT carrier and
//! `Rat.mul` is a binary `Quot.lift`, so it is a `Quot.sound` on the cross-
//! multiplied raw reps (the same idiom as `Rat.ofNat_mul`). The `k`-fold version
//! is a `Nat.rec` folding one `9·(1/9)=1` per step via `mul_mul_mul_comm`.
//!
//! ## The per-term level-restriction atom
//!
//! For a single Fourier coefficient `A := A(S)` with `|S| := setSizeNat n S ≤ k`,
//! the bare squared weight `A·A` is dominated by `9^k` times the NOISE-weighted
//! weight `levelWt(1/3) n S · (A·A) = (1/9)^{|S|}·A²`:
//!
//! ```text
//! BoolAnalysis.lowband_term_le_noise_term :
//!   ∀ (n k : Nat) (S : HCPoint n) (A : Rat),
//!     Nat.le (setSizeNat n S) k →
//!       Rat.le (Rat.mul A A)
//!              (Rat.mul (Rat.powNat (Rat.ofNat 9) k)
//!                       (Rat.mul (BoolAnalysis.levelWt rho_third n S) (Rat.mul A A)))
//! ```
//!
//! with `rho_third := Rat.mk (Int.ofNat 1) 3 = 1/3` (so `levelWt(1/3) n S =
//! (ρ²)^{|S|} = (1/9)^{|S|}` by the landed `levelWt_eq_powNat`).
//!
//! ### Why it is TRUE and refute-safe
//!
//! `levelWt(1/3) n S = (1/9)^{|S|}` ([`levelWt_eq_powNat`]). The bound reduces to
//! the per-coordinate scalar inequality (after clearing the nonnegative `A·A`):
//!
//! ```text
//!   1  ≤  9^k · (1/9)^{|S|}              for |S| ≤ k,
//! ```
//!
//! which holds because `9^k · (1/9)^{|S|} ≥ 9^k · (1/9)^k = (9·(1/9))^k = 1` (the
//! antitone step `(1/9)^{|S|} ≥ (1/9)^k` from `|S| ≤ k`, base `1/9 ≤ 1`, plus the
//! INVERSE identity `9^k·(1/9)^k = 1`). At `|S| = k` it is the equality `1 ≤ 1`;
//! at `|S| = 0` (`S = ∅`) it is `1 ≤ 9^k`; both edges are tight, neither refutes.
//! Dropping the `|S| ≤ k` hypothesis is FALSE (`|S| = k+1`, `A = 1`, `k = 0`:
//! `1 ≤ 9^0·(1/9)^1 = 1/9` is false), so the hypothesis is structurally
//! essential — the exact refute trap the campaign guards against.
//!
//! ## Soundness
//!
//! Every leaf is a CHECKED `Declaration::Theorem`, `ProofQuality::Constructive`,
//! with an empty admitted-axiom closure. No `sorry`/`add_decl_unchecked`/
//! `add_decl_structural`. No axiom is added or removed. The module is gated
//! behind `cfg(any(test, feature = "math-overlays"))`, matching its sibling
//! `boolean_analysis_kkl_halfpower`.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the level-restriction bridge.
struct BridgeLevelConsts {
    order: OrderConsts,
    nat: Expr,
    int: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_le: Expr,
    nat_mul: Expr,
    int_of_nat: Expr,
    int_mul: Expr,
    rat_mk: Expr,
    raw: Expr,
    raw_mk: Expr,
    raw_equiv: Expr,
    quot_mk: Expr,
    quot_sound: Expr,
    pow_nat: Expr,
    of_nat: Expr,
    hcpoint: Expr,
    level_wt: Expr,
    set_size_nat: Expr,
    // theorem leaves
    pow_nat_zero: Expr,
    pow_nat_succ: Expr,
    pow_nat_nonneg: Expr,
    pow_antitone: Expr,
    level_wt_eq_pow_nat: Expr,
    mul_le_right: Expr,
    mul_mul_mul_comm: Expr,
    one_mul: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
    congr_arg11: Expr,
}

impl BridgeLevelConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            int: k("Int"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_le: k("Nat.le"),
            nat_mul: k("Nat.mul"),
            int_of_nat: k("Int.ofNat"),
            int_mul: k("Int.mul"),
            rat_mk: k("Rat.mk"),
            raw: k("Rat.Raw"),
            raw_mk: k("Rat.Raw.mk"),
            raw_equiv: k("Rat.Raw.Equiv"),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![l1.clone()]),
            pow_nat: k("Rat.powNat"),
            of_nat: k("Rat.ofNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            level_wt: k("BoolAnalysis.levelWt"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            pow_nat_zero: k("Rat.powNat_zero"),
            pow_nat_succ: k("Rat.powNat_succ"),
            pow_nat_nonneg: k("Rat.powNat_nonneg"),
            pow_antitone: k("Rat.powNat_le_powNat_right_antitone"),
            level_wt_eq_pow_nat: k("BoolAnalysis.levelWt_eq_powNat"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            one_mul: k("Rat.one_mul"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg11: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn zero(&self) -> Expr {
        self.order.rat_zero.clone()
    }
    fn one(&self) -> Expr {
        self.order.rat_one.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn le0(&self, a: Expr) -> Expr {
        self.le(self.zero(), a)
    }
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    fn refl_rat(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat(), a])
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat(), a, b, h])
    }
    fn trans_rat(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat(), a, b, c, h1, h2])
    }
    /// `Eq.subst.{1} @Rat motive @a @b h_eq h_a : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat(), motive, a, b, h_eq, h_a],
        )
    }
    /// `@congrArg Rat Rat a b f h : f a = f b`.
    fn congr_rat(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg11.clone(),
            [self.rat(), self.rat(), a, b, f, h],
        )
    }

    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    /// `Rat.mk (Int.ofNat num) den`.
    fn rat_lit(&self, num: u64, den: u64) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(num)),
                self.nat_lit(den),
            ],
        )
    }
    fn rho_third(&self) -> Expr {
        self.rat_lit(1, 3)
    }
    /// `Rat.ofNat 9`.
    fn nine(&self) -> Expr {
        Expr::app(self.of_nat.clone(), self.nat_lit(9))
    }
    /// `1/9 = Rat.mk (Int.ofNat 1) 9`.
    fn inv_nine(&self) -> Expr {
        self.rat_lit(1, 9)
    }
    fn pow(&self, b: &Expr, e: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [b.clone(), e.clone()])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn set_size(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn level_wt_of(&self, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.level_wt.clone(), [rho.clone(), n.clone(), s.clone()])
    }
    fn nat_le_of(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a.clone(), b.clone()])
    }
    fn mul_le_r(&self, a: Expr, b: Expr, c: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, c, h_bc, h_0a])
    }
    fn pow_nonneg(&self, b: Expr, e: Expr, h: Expr) -> Expr {
        Expr::apps(self.pow_nat_nonneg.clone(), [b, e, h])
    }
    fn pow_antitone_of(&self, b: Expr, m: Expr, n: Expr, h0: Expr, h1: Expr, hmn: Expr) -> Expr {
        Expr::apps(self.pow_antitone.clone(), [b, m, n, h0, h1, hmn])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, c: Expr, d: Expr) -> Expr {
        Expr::apps(self.mul_mul_mul_comm.clone(), [a, b, c, d])
    }
    /// `Rat.one_mul a : 1·a = a`.
    fn one_mul_of(&self, a: Expr) -> Expr {
        Expr::app(self.one_mul.clone(), a)
    }
    /// `Rat.powNat_zero b : b^0 = 1`.
    fn pow_zero_of(&self, b: Expr) -> Expr {
        Expr::app(self.pow_nat_zero.clone(), b)
    }
    /// `Rat.powNat_succ b e : b^(e+1) = b · b^e`.
    fn pow_succ_of(&self, b: Expr, e: Expr) -> Expr {
        Expr::apps(self.pow_nat_succ.clone(), [b, e])
    }
}

impl Environment {
    /// Register the KKL hypercontractive-bridge LEVEL-RESTRICTION half. Idempotent.
    pub fn init_boolean_analysis_kkl_bridge_level(&mut self) -> Result<(), EnvError> {
        self.register_rat_nine_mul_inv_nine()?;
        self.register_rat_pow_nat_nine_mul_inv_nine()?;
        self.register_lowband_term_le_noise_term()?;
        Ok(())
    }

    /// `Rat.nine_mul_inv_nine : Rat.mul (Rat.ofNat 9) (Rat.mk (Int.ofNat 1) 9) = Rat.one`.
    ///
    /// The base scalar inverse `9·(1/9) = 1`. `Quot.sound` on the cross-multiplied
    /// raw reps (mirrors `Rat.ofNat_mul`). Constructive, empty closure. Idempotent.
    pub fn register_rat_nine_mul_inv_nine(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.nine_mul_inv_nine");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        self.register_rat_ofnat()?;
        self.register_int_ofnat_mul_proof()?;

        let c = BridgeLevelConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_base_inverse_type(&c),
            value: build_base_inverse_value(&c),
        })
    }

    /// `Rat.powNat_nine_mul_inv_nine : ∀ k : Nat, (9^k)·((1/9)^k) = 1`.
    ///
    /// `Nat.rec` on `k`, folding one base `9·(1/9)=1` per step. Constructive,
    /// empty admitted-axiom closure. Idempotent.
    pub fn register_rat_pow_nat_nine_mul_inv_nine(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_nine_mul_inv_nine");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_zero_theorem()?;
        self.register_rat_pow_nat_succ_theorem()?;
        self.register_rat_ofnat()?;
        self.register_rat_nine_mul_inv_nine()?;
        // The quotient Rat field surface (Rat.mul_assoc / Rat.mul_comm /
        // Rat.one_mul / Rat.mul_one / Rat.num projections) — registered as the
        // genuine Quot.ind theorems. mmmc's VALUE references mul_assoc/mul_comm.
        self.init_rat_field_inst()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BridgeLevelConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_pow_inverse_type(&c),
            value: build_pow_inverse_value(&c),
        })
    }

    /// `BoolAnalysis.lowband_term_le_noise_term`. The per-subset LEVEL
    /// RESTRICTION — step (A) of the §9.6 bridge at single-S granularity.
    /// Constructive, empty admitted-axiom closure. Idempotent.
    pub fn register_lowband_term_le_noise_term(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.lowband_term_le_noise_term");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_le()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_zero_theorem()?;
        self.register_rat_pow_nat_succ_theorem()?;
        self.register_rat_pow_nat_nonneg()?;
        self.register_rat_pow_nat_le_pow_nat_right_antitone()?;
        self.register_rat_pow_nat_nine_mul_inv_nine()?;
        self.register_levelwt_eq_pow_nat()?;
        self.register_level_wt()?;
        self.register_set_size_nat()?;
        self.register_rat_ofnat()?;
        self.register_rat_order_proofs()?;
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true (0≤1/9, 1/9≤1)
        self.register_rat_mul_assoc_proof()?; // Rat.mul_assoc (reassoc)
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_right, sq_nonneg
        self.init_boolean_analysis_hc_bounds()?; // zero_le_one
        self.init_rat_field_inst()?; // mul_one / one_mul / mul_comm

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BridgeLevelConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_term_type(&c),
            value: build_term_value(&c),
        })
    }
}

// ─────────────────────── base inverse 9·(1/9)=1 ─────────────────────────────

fn build_base_inverse_type(c: &BridgeLevelConsts) -> Expr {
    let lhs = c.mul(c.nine(), c.inv_nine());
    c.eq_rat(lhs, c.one())
}

fn build_base_inverse_value(c: &BridgeLevelConsts) -> Expr {
    // 9 ≡ Quot.mk (Raw.mk (ofNat 9) 1); 1/9 ≡ Quot.mk (Raw.mk (ofNat 1) 9).
    // Rat.mul ≡ Quot.mk (Raw.mk (num·num) (effDenom·effDenom)). For both reps
    // effDenom = the stored denom (nonzero), so the product rep is
    //   Raw.mk (ofNat 9 · ofNat 1) (effDenom(1) · effDenom(9)).
    // Rat.one ≡ Quot.mk (Raw.mk (ofNat 1) 1).
    // The Raw.Equiv obligation (cross-mult) reduces to an Int equality
    //   (ofNat 9 · ofNat 1) · denom(one) = (ofNat 1) · denom(prod)
    // i.e. (9·1)·1 = 1·(eff·eff). Both sides are Int.ofNat 9 after reduction;
    // we discharge with Eq.refl on the Int and let Quot.sound + defeq carry it.
    //
    // To stay robust to the exact effDenom reduction, we build the Quot.sound
    // with raw_l = Raw.mk (Int.mul (ofNat 9) (ofNat 1)) (Nat.mul 1 9) (the
    // product rep, DEFEQ to the LHS) and raw_r = Raw.mk (ofNat 1) 1 (Rat.one),
    // and provide the Equiv proof as Eq.refl on the reduced cross-product.
    let raw = c.raw.clone();
    let raw_equiv = c.raw_equiv.clone();
    let int_ = c.int.clone();

    let of9 = Expr::app(c.int_of_nat.clone(), c.nat_lit(9));
    let of1 = Expr::app(c.int_of_nat.clone(), c.nat_lit(1));
    let prod_num = Expr::apps(c.int_mul.clone(), [of9.clone(), of1.clone()]);
    let prod_den = Expr::apps(c.nat_mul.clone(), [c.nat_lit(1), c.nat_lit(9)]);

    let raw_l = Expr::apps(c.raw_mk.clone(), [prod_num.clone(), prod_den.clone()]);
    let raw_r = Expr::apps(c.raw_mk.clone(), [of1.clone(), c.nat_lit(1)]);

    // Equiv obligation: Rat.Raw.Equiv raw_l raw_r. It is (reducible) the Int
    // cross-product equality num_l · ofNat(den_r) = num_r · ofNat(den_l):
    //   (ofNat 9 · ofNat 1) · ofNat 1 = ofNat 1 · ofNat (1·9).
    // Both reduce to Int.ofNat 9, so Eq.refl on the LHS form discharges it
    // through Rat.Raw.Equiv's defeq. We construct the Equiv via Eq.refl at the
    // Int level and rely on Rat.Raw.Equiv unfolding to that equality.
    let equiv_ty = Expr::apps(c.raw_equiv.clone(), [raw_l.clone(), raw_r.clone()]);
    // The proof of the equiv is Eq.refl-shaped IF Rat.Raw.Equiv is a structural
    // Int equation; we let the kernel reduce it by providing Eq.refl at Int on
    // the canonical value. Use Eq.refl Int (Int.ofNat 9) and trust defeq.
    let _ = (equiv_ty, int_);
    let equiv_proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [c.int.clone(), Expr::app(c.int_of_nat.clone(), c.nat_lit(9))],
    );

    let quot_mk_l = Expr::apps(
        c.quot_mk.clone(),
        [raw.clone(), raw_equiv.clone(), raw_l.clone()],
    );
    let quot_mk_r = Expr::apps(
        c.quot_mk.clone(),
        [raw.clone(), raw_equiv.clone(), raw_r.clone()],
    );

    let sound = Expr::apps(
        c.quot_sound.clone(),
        [
            raw.clone(),
            raw_equiv.clone(),
            raw_l.clone(),
            raw_r,
            equiv_proof,
        ],
    );

    // LHS goal (9·(1/9)) is defeq to quot_mk_l; RHS (Rat.one) defeq to quot_mk_r.
    let lhs_goal = c.mul(c.nine(), c.inv_nine());
    let to_l = c.refl_rat(lhs_goal.clone());
    let from_r = c.refl_rat(c.one());
    let step1 = c.trans_rat(
        lhs_goal.clone(),
        quot_mk_l.clone(),
        quot_mk_r.clone(),
        to_l,
        sound,
    );
    c.trans_rat(lhs_goal, quot_mk_r, c.one(), step1, from_r)
}

// ────────────────────── k-fold inverse 9^k·(1/9)^k = 1 ──────────────────────

fn build_pow_inverse_type(c: &BridgeLevelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let lhs = c.mul(c.pow(&c.nine(), &k), c.pow(&c.inv_nine(), &k));
    let concl = c.eq_rat(lhs, c.one());
    b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl))
}

fn build_pow_inverse_value(c: &BridgeLevelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());

    // motive m := fun (t:Nat) => (9^t)·((1/9)^t) = 1
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.nat.clone());
        let lhs = c.mul(c.pow(&c.nine(), &t), c.pow(&c.inv_nine(), &t));
        let body = c.eq_rat(lhs, c.one());
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // base : (9^0)·((1/9)^0) = 1. Both powNat _ 0 = 1 (powNat_zero); product 1·1=1.
    //   chain: (9^0)·((1/9)^0) = 1·((1/9)^0)  [congr powNat_zero 9 on left]
    //                          = 1·1          [congr powNat_zero (1/9) on right]
    //                          = 1            [one_mul 1]
    let base = {
        let p9_0 = c.pow(&c.nine(), &c.nat_zero);
        let pi_0 = c.pow(&c.inv_nine(), &c.nat_zero);
        let h9 = c.pow_zero_of(c.nine()); // 9^0 = 1
        let hi = c.pow_zero_of(c.inv_nine()); // (1/9)^0 = 1
                                              // congr on left factor: (9^0)·((1/9)^0) = 1·((1/9)^0)
        let f_left = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (w_id, w) = d.fresh_local(c.rat());
            let body = c.mul(w, pi_0.clone());
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
        };
        let leg1 = c.congr_rat(p9_0.clone(), c.one(), f_left, h9);
        // congr on right factor: 1·((1/9)^0) = 1·1
        let f_right = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (w_id, w) = d.fresh_local(c.rat());
            let body = c.mul(c.one(), w);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
        };
        let leg2 = c.congr_rat(pi_0.clone(), c.one(), f_right, hi);
        // 1·1 = 1
        let leg3 = c.one_mul_of(c.one());
        // chain
        let e_lhs = c.mul(p9_0, pi_0.clone());
        let e_mid1 = c.mul(c.one(), pi_0);
        let e_mid2 = c.mul(c.one(), c.one());
        let t1 = c.trans_rat(e_lhs.clone(), e_mid1.clone(), e_mid2.clone(), leg1, leg2);
        c.trans_rat(e_lhs, e_mid2, c.one(), t1, leg3)
    };

    // step : ∀ m, motive m → motive (m+1).
    //   goal: (9^{m+1})·((1/9)^{m+1}) = 1.
    //   9^{m+1} = 9·9^m (powNat_succ); (1/9)^{m+1} = (1/9)·(1/9)^m.
    //   so LHS = (9·9^m)·((1/9)·(1/9)^m)
    //          = (9·(1/9))·(9^m·(1/9)^m)   [mul_mul_mul_comm 9 9^m (1/9) (1/9)^m]
    //          = 1·(9^m·(1/9)^m)           [congr left: 9·(1/9)=1]
    //          = 9^m·(1/9)^m               [one_mul]
    //          = 1                          [ih]
    let step = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = d.fresh_local(c.nat.clone());
        let ih_ty = {
            let lhs = c.mul(c.pow(&c.nine(), &m), c.pow(&c.inv_nine(), &m));
            c.eq_rat(lhs, c.one())
        };
        let (ih_id, ih) = d.fresh_local(ih_ty.clone());

        let p9m = c.pow(&c.nine(), &m);
        let pim = c.pow(&c.inv_nine(), &m);
        let m_succ = Expr::app(c.nat_succ.clone(), m.clone());
        let p9s = c.pow(&c.nine(), &m_succ); // 9^{m+1}
        let pis = c.pow(&c.inv_nine(), &m_succ); // (1/9)^{m+1}

        // h9s : 9^{m+1} = 9·9^m ; his : (1/9)^{m+1} = (1/9)·(1/9)^m
        let h9s = c.pow_succ_of(c.nine(), m.clone());
        let his = c.pow_succ_of(c.inv_nine(), m.clone());

        // goal LHS = p9s · pis. Rewrite to (9·9^m)·((1/9)·(1/9)^m).
        let prod_succ = c.mul(p9s.clone(), pis.clone());
        let prod_exp = c.mul(
            c.mul(c.nine(), p9m.clone()),
            c.mul(c.inv_nine(), pim.clone()),
        );
        // congr left factor: p9s·pis = (9·9^m)·pis
        let f_l = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (w_id, w) = e.fresh_local(c.rat());
            let body = c.mul(w, pis.clone());
            e.finish_child(e.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
        };
        let r_l = c.congr_rat(p9s.clone(), c.mul(c.nine(), p9m.clone()), f_l, h9s);
        // congr right factor: (9·9^m)·pis = (9·9^m)·((1/9)·(1/9)^m)
        let f_r = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (w_id, w) = e.fresh_local(c.rat());
            let body = c.mul(c.mul(c.nine(), p9m.clone()), w);
            e.finish_child(e.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
        };
        let r_r = c.congr_rat(pis.clone(), c.mul(c.inv_nine(), pim.clone()), f_r, his);
        let mid_a = c.mul(c.mul(c.nine(), p9m.clone()), pis.clone());
        let to_exp = c.trans_rat(prod_succ.clone(), mid_a, prod_exp.clone(), r_l, r_r);

        // mmmc : (9·9^m)·((1/9)·(1/9)^m) = (9·(1/9))·(9^m·(1/9)^m)
        let regroup = c.mmmc(c.nine(), p9m.clone(), c.inv_nine(), pim.clone());
        let regrouped = c.mul(
            c.mul(c.nine(), c.inv_nine()),
            c.mul(p9m.clone(), pim.clone()),
        );

        // congr left: (9·(1/9))·(9^m·(1/9)^m) = 1·(9^m·(1/9)^m)
        let h_base = Expr::const_(Name::from_string("Rat.nine_mul_inv_nine"), vec![]);
        let f_base = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (w_id, w) = e.fresh_local(c.rat());
            let body = c.mul(w, c.mul(p9m.clone(), pim.clone()));
            e.finish_child(e.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
        };
        let base_rewritten = c.congr_rat(c.mul(c.nine(), c.inv_nine()), c.one(), f_base, h_base);
        let one_prod = c.mul(c.one(), c.mul(p9m.clone(), pim.clone()));

        // one_mul : 1·(9^m·(1/9)^m) = 9^m·(1/9)^m
        let prod_m = c.mul(p9m.clone(), pim.clone());
        let h_one_mul = c.one_mul_of(prod_m.clone());

        // chain to prod_m, then ih to 1.
        let t1 = c.trans_rat(
            prod_succ.clone(),
            prod_exp.clone(),
            regrouped.clone(),
            to_exp,
            regroup,
        );
        let t2 = c.trans_rat(
            prod_succ.clone(),
            regrouped,
            one_prod.clone(),
            t1,
            base_rewritten,
        );
        let t3 = c.trans_rat(prod_succ.clone(), one_prod, prod_m.clone(), t2, h_one_mul);
        let proof = c.trans_rat(prod_succ, prod_m, c.one(), t3, ih);

        let val = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
        d.finish_child(d.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), val))
    };

    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let body = Expr::apps(nat_rec, [motive, base, step, k.clone()]);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
}

// ─────────────────────────── per-term atom ──────────────────────────────────

fn build_term_type(c: &BridgeLevelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (s_id, s) = b.fresh_local(c.hcpoint_of(&n));
    let (a_id, a) = b.fresh_local(c.rat());
    let hyp = c.nat_le_of(&c.set_size(&n, &s), &k);
    let (h_id, _) = b.fresh_local(hyp.clone());

    let aa = c.mul(a.clone(), a.clone());
    let lvl = c.level_wt_of(&c.rho_third(), &n, &s);
    let rhs = c.mul(c.pow(&c.nine(), &k), c.mul(lvl, aa.clone()));
    let concl = c.le(aa, rhs);

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(s_id, BinderInfo::Default, c.hcpoint_of(&n), e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn build_term_value(c: &BridgeLevelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (s_id, s) = b.fresh_local(c.hcpoint_of(&n));
    let (a_id, a) = b.fresh_local(c.rat());
    let hyp = c.nat_le_of(&c.set_size(&n, &s), &k);
    let (h_id, h) = b.fresh_local(hyp.clone());

    let rho = c.rho_third();
    let nine = c.nine();
    let inv9 = c.inv_nine();
    let size = c.set_size(&n, &s); // |S| : Nat
    let aa = c.mul(a.clone(), a.clone()); // A·A
    let lvl = c.level_wt_of(&rho, &n, &s); // levelWt(1/3) n S
                                           // wp := powNat ((1/3)·(1/3)) |S|  — DEFEQ to powNat (1/9) |S|.
    let rho_sq = c.mul(rho.clone(), rho.clone());
    let wp = c.pow(&rho_sq, &size);

    let p9k = c.pow(&nine, &k); // 9^k
    let pi9k = c.pow(&inv9, &k); // (1/9)^k
                                 // (1/9)^{|S|} as the antitone target (defeq to wp).
    let pi9s = c.pow(&inv9, &size);

    // ── nonnegativity facts ─────────────────────────────────────────────────
    // 0 ≤ 9^k  (powNat_nonneg with 0 ≤ 9).
    //   0 ≤ 9 := powNat_le? no — use Rat.sq_nonneg? Build 0 ≤ ofNat 9 directly:
    //   ofNat 9 ≥ 0 via Rat.ofNat_le_ofNat_of_le 0 9 (Nat.zero_le 9) since
    //   ofNat 0 ≡ Rat.zero (defeq). We instead obtain 0≤9^k from powNat_nonneg
    //   (0≤9). For 0≤9 reuse the antitone/monotone surface: ofNat is nonneg.
    let zero_le_nine = build_zero_le_ofnat(c, 9);
    let h_p9k_nn = c.pow_nonneg(nine.clone(), k.clone(), zero_le_nine.clone());

    // 0 ≤ A·A  (Rat.sq_nonneg a).
    let h_aa_nn = Expr::apps(
        Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]),
        [a.clone()],
    );

    // 0 ≤ 1/9, 1/9 ≤ 1  (for the antitone primitive).
    let zero_le_inv9 = build_zero_le_inv_nine(c);
    let inv9_le_one = build_inv_nine_le_one(c);

    // ── antitone: (1/9)^k ≤ (1/9)^{|S|}  for |S| ≤ k ────────────────────────
    //   powNat_le_powNat_right_antitone (1/9) |S| k (0≤1/9)(1/9≤1)(|S|≤k)
    //     : (1/9)^k ≤ (1/9)^{|S|}.
    let antitone = c.pow_antitone_of(
        inv9.clone(),
        size.clone(),
        k.clone(),
        zero_le_inv9,
        inv9_le_one,
        h.clone(),
    );

    // ── 9^k·(1/9)^k ≤ 9^k·(1/9)^{|S|}  (mul_le_mul_of_nonneg_left) ───────────
    //   we only have mul_le_mul_of_nonneg_right in this struct; use it on the
    //   RIGHT factor instead: build 1 ≤ 9^k·(1/9)^{|S|} via the RIGHT form.
    //   Restructure: multiply the antitone ((1/9)^k ≤ (1/9)^{|S|}) on the RIGHT
    //   by 9^k≥0 gives (1/9)^k·9^k ≤ (1/9)^{|S|}·9^k. That has 9^k on the right;
    //   we want it on the left to match the goal. Use commutation instead:
    //   prove 1 ≤ 9^k·(1/9)^{|S|} by:
    //     1 = 9^k·(1/9)^k                       [inverse, symm]
    //       ≤ 9^k·(1/9)^{|S|}                   [mul_le_left 9^k]
    //   mul_le_left is NOT in struct, so use the right-mult + commute trick.
    //
    // Use mul_le_mul_of_nonneg_right on antitone with multiplier 9^k:
    //   (1/9)^k·9^k ≤ (1/9)^{|S|}·9^k.
    let mul_r = c.mul_le_r(
        p9k.clone(),
        pi9k.clone(),
        pi9s.clone(),
        antitone,
        h_p9k_nn.clone(),
    );
    // mul_r : (1/9)^k·9^k ≤ (1/9)^{|S|}·9^k.

    // inverse (commuted): 1 = (1/9)^k·9^k.
    //   powNat_nine_mul_inv_nine k : 9^k·(1/9)^k = 1; commute to (1/9)^k·9^k = 1.
    let inv_id = Expr::apps(
        Expr::const_(Name::from_string("Rat.powNat_nine_mul_inv_nine"), vec![]),
        [k.clone()],
    );
    // commute: 9^k·(1/9)^k = (1/9)^k·9^k  (Rat.mul_comm).
    let comm_9 = Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
        [p9k.clone(), pi9k.clone()],
    );
    // (1/9)^k·9^k = 1  := trans (symm comm_9) inv_id.
    let prod_9k = c.mul(p9k.clone(), pi9k.clone());
    let prod_i9k = c.mul(pi9k.clone(), p9k.clone());
    let inv_comm = c.trans_rat(
        prod_i9k.clone(),
        prod_9k.clone(),
        c.one(),
        c.symm_rat(prod_9k.clone(), prod_i9k.clone(), comm_9),
        inv_id,
    );
    // transport mul_r's LHS ((1/9)^k·9^k) to 1: motive t := t ≤ (1/9)^{|S|}·9^k.
    let prod_i9s = c.mul(pi9s.clone(), p9k.clone());
    let motive_lhs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat());
        let body = c.le(t, prod_i9s.clone());
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    // subst (one_eq : 1 = (1/9)^k·9^k) : motive 1 → motive ((1/9)^k·9^k)?
    // We have mul_r : motive ((1/9)^k·9^k) and want motive 1. Use one_eq's symm:
    //   inv_comm : (1/9)^k·9^k = 1; subst inv_comm : motive ((1/9)^k·9^k) → motive 1.
    let one_le_prod = c.subst_rat(motive_lhs, prod_i9k.clone(), c.one(), inv_comm, mul_r);
    // one_le_prod : 1 ≤ (1/9)^{|S|}·9^k.

    // We want 1 ≤ 9^k·(1/9)^{|S|}. Commute the RHS.
    //   commute (1/9)^{|S|}·9^k = 9^k·(1/9)^{|S|}  (Rat.mul_comm).
    let comm_s = Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
        [pi9s.clone(), p9k.clone()],
    );
    let prod_9ks = c.mul(p9k.clone(), pi9s.clone());
    // subst comm_s : motive ((1/9)^{|S|}·9^k) → motive (9^k·(1/9)^{|S|}), motive t := 1 ≤ t.
    let motive_rhs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat());
        let body = c.le(c.one(), t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    let one_le_9ks = c.subst_rat(
        motive_rhs,
        prod_i9s.clone(),
        prod_9ks.clone(),
        comm_s,
        one_le_prod,
    );
    // one_le_9ks : 1 ≤ 9^k·(1/9)^{|S|}.

    // ── A² ≤ (9^k·(1/9)^{|S|})·A²   (mul_le_mul_of_nonneg_right A²) ──────────
    //   from 1 ≤ 9^k·(1/9)^{|S|}: mul_le_r aa 1 (9^k·(1/9)^{|S|}) (1≤…) (0≤A²)
    //     : 1·A² ≤ (9^k·(1/9)^{|S|})·A².
    let scaled = c.mul_le_r(aa.clone(), c.one(), prod_9ks.clone(), one_le_9ks, h_aa_nn);
    // scaled : 1·A² ≤ (9^k·(1/9)^{|S|})·A².

    // rewrite LHS 1·A² → A² via Rat.one_mul.
    let one_mul_aa = c.one_mul_of(aa.clone());
    let prod_rhs = c.mul(prod_9ks.clone(), aa.clone()); // (9^k·(1/9)^{|S|})·A²
    let motive_le_lhs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat());
        let body = c.le(t, prod_rhs.clone());
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    let one_mul_lhs = c.mul(c.one(), aa.clone());
    let aa_le = c.subst_rat(motive_le_lhs, one_mul_lhs, aa.clone(), one_mul_aa, scaled);
    // aa_le : A² ≤ (9^k·(1/9)^{|S|})·A².

    // ── reassoc RHS (9^k·(1/9)^{|S|})·A² → 9^k·((1/9)^{|S|}·A²) (mul_assoc) ──
    let mul_assoc = Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
        [p9k.clone(), pi9s.clone(), aa.clone()],
    );
    // mul_assoc : (9^k·(1/9)^{|S|})·A² = 9^k·((1/9)^{|S|}·A²).
    let rhs_assoc = c.mul(p9k.clone(), c.mul(pi9s.clone(), aa.clone()));
    let motive_le_rhs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat());
        let body = c.le(aa.clone(), t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    let aa_le_assoc = c.subst_rat(
        motive_le_rhs,
        prod_rhs.clone(),
        rhs_assoc.clone(),
        mul_assoc,
        aa_le,
    );
    // aa_le_assoc : A² ≤ 9^k·((1/9)^{|S|}·A²).

    // ── final: rewrite (1/9)^{|S|} → levelWt(1/3) n S via levelWt_eq_powNat ──
    //   levelWt_eq_powNat (1/3) n S : levelWt(1/3) n S = powNat((1/3)²) |S| = wp.
    //   (1/9)^{|S|} is DEFEQ to wp. We subst to convert the proof's (1/9)^{|S|}
    //   occurrence into levelWt. Build the equation lvl = pi9s by trans through
    //   wp (lvl = wp by lemma; wp = pi9s by refl/defeq).
    let lvl_eq_wp = Expr::apps(
        c.level_wt_eq_pow_nat.clone(),
        [rho.clone(), n.clone(), s.clone()],
    );
    // lvl = wp ; wp = pi9s (defeq, refl) ; so lvl = pi9s.
    let wp_eq_pi9s = c.refl_rat(wp.clone()); // wp ≡ pi9s defeq, refl at wp checks as wp = pi9s
    let lvl_eq_pi9s = c.trans_rat(lvl.clone(), wp.clone(), pi9s.clone(), lvl_eq_wp, wp_eq_pi9s);
    // subst (lvl_eq_pi9s : lvl = pi9s) needs motive a → motive b with a=lvl,b=pi9s.
    // We have proof with pi9s (motive pi9s) and want motive lvl. Use symm:
    //   pi9s = lvl (symm) then subst : motive pi9s → motive lvl.
    let pi9s_eq_lvl = c.symm_rat(lvl.clone(), pi9s.clone(), lvl_eq_pi9s);
    let motive_final = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat());
        let body = c.le(aa.clone(), c.mul(p9k.clone(), c.mul(t, aa.clone())));
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    let final_proof = c.subst_rat(
        motive_final,
        pi9s.clone(),
        lvl.clone(),
        pi9s_eq_lvl,
        aa_le_assoc,
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, final_proof);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(s_id, BinderInfo::Default, c.hcpoint_of(&n), e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

/// `0 ≤ Rat.ofNat v` via the `Rat.le_of_ble_eq_true` native-reduction idiom
/// (`Rat.ble 0 (ofNat v)` reduces to `true` on the concrete reps).
fn build_zero_le_ofnat(c: &BridgeLevelConsts, v: u64) -> Expr {
    let nine = Expr::app(c.of_nat.clone(), c.nat_lit(v));
    let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let eq_refl_bool = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_c, btrue],
    );
    Expr::apps(
        Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
        [c.zero(), nine, eq_refl_bool],
    )
}

/// `0 ≤ 1/9`. `1/9 = Rat.mk (ofNat 1) 9`. Built via `Rat.le_of_ble_eq_true`
/// (the boolean order `Rat.ble 0 (1/9)` native-reduces to `true` on the concrete
/// reps, so `Eq.refl Bool.true` discharges it).
fn build_zero_le_inv_nine(c: &BridgeLevelConsts) -> Expr {
    let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let eq_refl_bool = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_c, btrue],
    );
    Expr::apps(
        Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
        [c.zero(), c.inv_nine(), eq_refl_bool],
    )
}

/// `1/9 ≤ 1`. Same `Rat.le_of_ble_eq_true` native-reduction idiom.
fn build_inv_nine_le_one(c: &BridgeLevelConsts) -> Expr {
    let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let eq_refl_bool = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_c, btrue],
    );
    Expr::apps(
        Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
        [c.inv_nine(), c.one(), eq_refl_bool],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const LEMMAS: &[&str] = &[
        "Rat.nine_mul_inv_nine",
        "Rat.powNat_nine_mul_inv_nine",
        "BoolAnalysis.lowband_term_le_noise_term",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_bridge_level()
            .expect("init_boolean_analysis_kkl_bridge_level");
        env.init_boolean_analysis_kkl_bridge_level()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_bridge_level_all_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be empty (foundational-only)"
            );
        }
    }

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule). `refute_conjecture` must NOT
    /// refute the landed level-restriction atom. By-hand edge checks (the battery
    /// constructs |S| ∈ {0,…} and small A):
    /// - `|S| = k` ⟹ `A² ≤ 9^k·(1/9)^k·A² = A²` (equality, tight);
    /// - `|S| = 0` (S = ∅) ⟹ `A² ≤ 9^k·1·A² = 9^k·A²` (`9^k ≥ 1`);
    /// - `A = 0` ⟹ `0 ≤ 0`.
    ///
    /// Dropping the `|S| ≤ k` hypothesis is FALSE (`|S| = k+1`, `A = 1`, `k = 0`:
    /// `1 ≤ (1/9)`), so the hypothesis is structurally essential — `refute`
    /// returns `None` only because it cannot construct a `|S| > k` HCPoint here,
    /// but the proof is closed for the true conditional form.
    #[test]
    fn test_lowband_term_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.lowband_term_le_noise_term",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "lowband_term_le_noise_term is a TRUE conditional inequality; \
             it must NOT refute on the dictator/parity/constant battery"
        );
    }

    /// STEP-1 FORM PIN (mandatory sharp-KKL gate) for the per-coordinate SQUARED
    /// hypercontractive bound — the genuine §9.6 content this bridge-half exists
    /// to feed. The form (abstract scalar shadow, the exact reduced goal the dual
    /// `(4/3→2)` step emits after the level restriction and squaring):
    ///
    /// ```text
    ///   ∀ (k : Nat) (W Inf : Rat), 0 ≤ W → 0 ≤ Inf →
    ///     [the dual-bound hypothesis]  →  W·W ≤ (16·81^k)·((Inf·Inf)·Inf)
    /// ```
    ///
    /// with `W := W^{≤k}[D_i f]`, `Inf := Inf_i`, `C = 16·9^{2k} = 16·81^k` (from
    /// `(‖T_{1/3}g‖₂²)² ≤ 16·Inf³` and `W^{≤k} ≤ 9^k·‖T_{1/3}g‖₂²`). We refute-
    /// check the WEAKEST consistent unconditional scalar shape
    /// `0 ≤ W → 0 ≤ Inf → W ≤ 16·Inf` as a SANITY witness that the battery is
    /// live (it must NOT falsely refute a true conditional), and PIN the squared
    /// constant `16·81^k` by hand. The full squared bound is TRUE (obstruction
    /// report §2/§5) but is NOT provable from the landed FORWARD `hc24_at_third`:
    /// it needs the unbuilt dual `(4/3→2)` bound — see the module obstruction note.
    /// Tribes (NOT in the n≤4 battery) is the witness the squared route cannot be
    /// summed without a fatal Cauchy–Schwarz `√n`; the per-coordinate squared
    /// bound itself is sound, only its SUMMATION is dead — hence the `^{3/2}`
    /// carrier route (this layer) is required.
    #[test]
    fn test_squared_form_pin_sane() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let c = BridgeLevelConsts::new();
        // ∀ (W Inf : Rat), 0≤W → 0≤Inf → W ≤ 16·Inf   (a TRUE-on-battery sanity
        // form: with 0≤W,0≤Inf the battery's small witnesses keep it satisfiable;
        // this confirms the refute harness does not spuriously fire on the shape).
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(c.rat());
            let (inf_id, inf) = b.fresh_local(c.rat());
            let h0w = c.le0(w.clone());
            let (h0w_id, _) = b.fresh_local(h0w.clone());
            let h0i = c.le0(inf.clone());
            let (h0i_id, _) = b.fresh_local(h0i.clone());
            let sixteen = Expr::app(c.of_nat.clone(), c.nat_lit(16));
            let concl = c.le(w.clone(), c.mul(sixteen, inf.clone()));
            let e = b.mk_pi(h0i_id, BinderInfo::Default, h0i, concl);
            let e = b.mk_pi(h0w_id, BinderInfo::Default, h0w, e);
            let e = b.mk_pi(inf_id, BinderInfo::Default, c.rat(), e);
            b.finish(b.mk_pi(w_id, BinderInfo::Default, c.rat(), e))
        };
        // The shape W ≤ 16·Inf is NOT unconditionally true (W large, Inf small),
        // so the battery SHOULD find a counterexample — this asserts the harness
        // is live (a fired refutation), pinning that our refute gate works.
        assert!(
            refute_conjecture(&tc, &ty).is_some(),
            "the sanity shape W ≤ 16·Inf must be refutable (W=4,Inf=0), confirming \
             the refute harness is live for the squared-form pin"
        );
    }
}
