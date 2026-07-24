// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL STRUCTURAL bridge — the DOUBLE-COUNT pointwise atom (axiom-free).
//!
//! # Where this sits in the §9.6 bridge
//!
//! The genuine O'Donnell §9.6 per-coordinate bridge upper-bounds the low-degree
//! Fourier mass `M_{1..k}` by the influence-`^{3/2}` sum. The first, PURELY
//! COMBINATORIAL half is the spectral DOUBLE-COUNT
//!
//! ```text
//!   M_{1..k}  =  Σ_{1≤|S|≤k}            f̂(S)²
//!             ≤  Σ_{1≤|S|≤k}  |S| ·     f̂(S)²   =  Σ_i W^{≤k}[D_i f].
//! ```
//!
//! Each non-empty subset `S` of size `≤ k` contributes to exactly `|S|`
//! coordinate-derivative low-bands (`subsetSum_double_count` /
//! `total_influence_spectral`), so the degree-weighted band mass on the right is
//! `Σ_i W^{≤k}[D_i f]`. Because `|S| ≥ 1` on the non-empty band, the unweighted
//! term is dominated by the degree-weighted one TERMWISE — this is the substance
//! of this module: the per-subset atom that `subsetSum_le_of_pointwise` lifts.
//! It is INDEPENDENT of the (separately in-flight) per-coordinate dual
//! hypercontractive bound `‖T_{1/3}D_i f‖₂² ≤ 4·Inf^{3/2}` — pure Fourier /
//! influence combinatorics.
//!
//! ## The abstract scalar atom
//!
//! ```text
//! BoolAnalysis.lowband_dc_term :
//!   ∀ (b : Bool) (sz w : Rat),
//!     Rat.le Rat.zero w → (b = Bool.true → Rat.le Rat.one sz) →
//!       Rat.le (Rat.mul (ind b) w) (Rat.mul (ind b) (Rat.mul sz w))
//! ```
//!
//! i.e. for the band-mask bit `b`, the degree `sz := |S|` and the (nonneg)
//! Fourier weight `w := f̂(S)²`: the masked weight `ind(b)·w` is dominated by the
//! masked degree-weighted weight `ind(b)·(|S|·w)`, GIVEN that whenever the bit
//! fires (`b = true`) the degree is at least `1` (`1 ≤ sz`). `Bool.rec` on `b`:
//! - `b = false`: `ind false ≡ 0`, so both sides are `0·…`; `Rat.zero_mul`
//!   rewrites them to `0`, closed by `Rat.le_refl 0`. The `1 ≤ sz` hypothesis is
//!   not used (it would be vacuous here anyway).
//! - `b = true`: `ind true ≡ 1`, so the goal is `1·w ≤ 1·(sz·w)`. From the
//!   hypothesis `1 ≤ sz` (discharged with `Eq.refl true`) and `0 ≤ w`,
//!   `mul_le_mul_of_nonneg_right` gives `1·w ≤ sz·w`; `Rat.one_mul` rewrites the
//!   LHS to `w`, so `w ≤ sz·w`; `mul_le_mul_of_nonneg_left` (multiplier `1`,
//!   `0 ≤ 1`) lifts this to `1·w ≤ 1·(sz·w)`.
//!
//! ## The boolean conjunct-extraction helper
//!
//! ```text
//! Bool.and_left_eq_true : ∀ (a b : Bool), Bool.and a b = Bool.true → a = Bool.true
//! ```
//!
//! `Bool.rec` on `a`: `a = true` is `Eq.refl true`; `a = false` makes
//! `Bool.and false b ≡ Bool.false`, so the hypothesis is `false = true`, refuted
//! by `Bool.noConfusion`. This is the brick that turns "the band bit fired" into
//! "the `|S| ≥ 1` conjunct fired" at the consumer, so the degree bound `1 ≤ |S|`
//! can be derived.
//!
//! ## Soundness
//!
//! Every leaf is a CHECKED `Declaration::Theorem`, `ProofQuality::Constructive`,
//! with an empty admitted-axiom closure. No `sorry`/`add_decl_unchecked`/
//! `add_decl_structural`/`native_decide`. No axiom is added or removed. Gated
//! behind `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the structural double-count pointwise rung. Spellings are
/// byte-identical to the on-branch `OrderConsts` / `MassSplitConsts` carriers so
/// all terms stay def-eq to the infrastructure they reuse.
struct DcPointwiseConsts {
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    bool_false: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    ind: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    u0: Level,
    u1: Level,
}

impl DcPointwiseConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            ind: k("BoolAnalysis.ind"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
            u0: Level::zero(),
            u1: Level::succ(Level::zero()),
        }
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `LE.le Rat instLERat a b` — the `Rat`-order spelling shared with
    /// `OrderConsts.rat_le` and `subsetSum_le_of_pointwise`.
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    /// `@Eq Bool l r`.
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.bool_.clone(), l, r],
        )
    }
    /// `Eq.refl.{1} Bool x`.
    fn refl_bool(&self, x: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.u1.clone()]),
            [self.bool_.clone(), x],
        )
    }
    /// `Eq.symm.{1} Rat a b h : b = a`.
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h_a : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.u1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
}

impl Environment {
    /// Register the structural double-count pointwise rung. Idempotent.
    pub fn init_boolean_analysis_kkl_bridgestruct_pointwise(&mut self) -> Result<(), EnvError> {
        self.register_bool_and_left_eq_true()?;
        self.register_lowband_dc_term()?;
        Ok(())
    }

    /// `BoolAnalysis.lowband_dc_term : ∀ (b : Bool) (sz w : Rat),
    ///   Rat.le Rat.zero w → (b = Bool.true → Rat.le Rat.one sz) →
    ///     Rat.le (Rat.mul (ind b) w) (Rat.mul (ind b) (Rat.mul sz w))`.
    ///
    /// The DOUBLE-COUNT pointwise atom — see the module docs for the full proof
    /// (a `Bool.rec` on `b`). Kernel-checked, `Constructive`, empty admitted-axiom
    /// closure. Idempotent.
    pub fn register_lowband_dc_term(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.lowband_dc_term");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_rat()?;
        self.init_boolean_analysis()?; // ind
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat_field_inst()?; // Rat.one_mul, Rat.zero_mul
        self.register_rat_order_proofs()?; // Rat.le_refl, Rat.zero_lt_one, Rat.lt_iff_le_not_le
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_{left,right}

        let c = DcPointwiseConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_dc_term_type(&c),
            value: build_dc_term_value(&c),
        })
    }
}

fn build_dc_term_type(c: &DcPointwiseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (b_id, bit) = b.fresh_local(c.bool_.clone());
    let (sz_id, sz) = b.fresh_local(c.rat.clone());
    let (w_id, w) = b.fresh_local(c.rat.clone());

    // h_w : 0 ≤ w
    let h_w_ty = c.le(c.rat_zero.clone(), w.clone());
    let (hw_id, _) = b.fresh_local(h_w_ty.clone());
    // h_sz : b = true → 1 ≤ sz
    let h_sz_ty = Expr::pi(
        BinderInfo::Default,
        c.eq_bool(bit.clone(), c.bool_true.clone()),
        c.le(c.rat_one.clone(), sz.clone()),
    );
    let (hsz_id, _) = b.fresh_local(h_sz_ty.clone());

    let lhs = c.mul(c.ind_of(bit.clone()), w.clone());
    let rhs = c.mul(c.ind_of(bit.clone()), c.mul(sz.clone(), w.clone()));
    let concl = c.le(lhs, rhs);

    let e = b.mk_pi(hsz_id, BinderInfo::Default, h_sz_ty, concl);
    let e = b.mk_pi(hw_id, BinderInfo::Default, h_w_ty, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(sz_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(b.mk_pi(b_id, BinderInfo::Default, c.bool_.clone(), e))
}

fn build_dc_term_value(c: &DcPointwiseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (b_id, bit) = b.fresh_local(c.bool_.clone());
    let (sz_id, sz) = b.fresh_local(c.rat.clone());
    let (w_id, w) = b.fresh_local(c.rat.clone());

    let h_w_ty = c.le(c.rat_zero.clone(), w.clone());
    let (hw_id, hw) = b.fresh_local(h_w_ty.clone());
    let h_sz_ty = Expr::pi(
        BinderInfo::Default,
        c.eq_bool(bit.clone(), c.bool_true.clone()),
        c.le(c.rat_one.clone(), sz.clone()),
    );
    let (hsz_id, hsz) = b.fresh_local(h_sz_ty.clone());

    let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![c.u0.clone()]);
    let one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);
    let zero_mul = Expr::const_(Name::from_string("Rat.zero_mul"), vec![]);
    let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let mul_le_r = Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]);
    let mul_le_l = Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]);

    // goal_at z := ind z · w ≤ ind z · (sz · w)
    let goal_at = |z: Expr| {
        c.le(
            c.mul(c.ind_of(z.clone()), w.clone()),
            c.mul(c.ind_of(z), c.mul(sz.clone(), w.clone())),
        )
    };
    // hyp_at z := (z = true → 1 ≤ sz)  — the degree hypothesis at the recursed bit `z`.
    let hyp_at = |z: Expr| {
        Expr::pi(
            BinderInfo::Default,
            c.eq_bool(z, c.bool_true.clone()),
            c.le(c.rat_one.clone(), sz.clone()),
        )
    };

    // The recursion carries the degree hypothesis INTO the motive so the `z=true`
    // minor sees `hsz` specialized to `true` (without it, `hsz` keeps the free
    // outer `bit`, and `Eq.refl true : true = true` cannot discharge `bit = true`).
    //   motive : fun (z : Bool) => (z = true → 1 ≤ sz) → goal_at z
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.bool_.clone());
        let body = Expr::pi(BinderInfo::Default, hyp_at(z.clone()), goal_at(z.clone()));
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.bool_.clone(), body))
    };

    // ── false minor : (false = true → 1 ≤ sz) → goal_at false. ───────────────
    //   goal_at false ≡ 0·w ≤ 0·(sz·w).
    //   h0w : 0·w = 0  (zero_mul w)        — symm gives 0 = 0·w
    //   h0p : 0·(sz·w) = 0  (zero_mul (sz·w))
    //   refl : 0 ≤ 0  (le_refl 0)
    //   subst (motive_l t => 0 ≤ t)        along (symm h0p)        : 0 ≤ 0·(sz·w)
    //   subst (motive_r t => t ≤ 0·(sz·w)) along (symm h0w)        : 0·w ≤ 0·(sz·w)
    let false_minor = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hf_ty = hyp_at(c.bool_false.clone());
        let (hf_id, _hf) = d.fresh_local(hf_ty.clone());

        let zero = c.rat_zero.clone();
        let zero_w = c.mul(zero.clone(), w.clone());
        let sz_w = c.mul(sz.clone(), w.clone());
        let zero_p = c.mul(zero.clone(), sz_w.clone());

        let h0w = Expr::app(zero_mul.clone(), w.clone()); // 0·w = 0
        let h0p = Expr::app(zero_mul.clone(), sz_w.clone()); // 0·(sz·w) = 0
        let refl0 = Expr::app(le_refl.clone(), zero.clone()); // 0 ≤ 0

        // step1 : 0 ≤ 0·(sz·w)   (motive_l t := 0 ≤ t ; subst along symm h0p)
        let motive_l = {
            let mut g = EnvDeclBuilder::child_of(&d);
            let (t_id, t) = g.fresh_local(c.rat.clone());
            let body = c.le(zero.clone(), t);
            g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h0p_symm = c.symm_rat(zero_p.clone(), zero.clone(), h0p);
        let step1 = c.subst_rat(motive_l, zero.clone(), zero_p.clone(), h0p_symm, refl0);

        // step2 : 0·w ≤ 0·(sz·w)   (motive_r t := t ≤ 0·(sz·w) ; subst along symm h0w)
        let motive_r = {
            let mut g = EnvDeclBuilder::child_of(&d);
            let (t_id, t) = g.fresh_local(c.rat.clone());
            let body = c.le(t, zero_p.clone());
            g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h0w_symm = c.symm_rat(zero_w.clone(), zero.clone(), h0w);
        let step2 = c.subst_rat(motive_r, zero.clone(), zero_w.clone(), h0w_symm, step1);
        d.finish_child(d.mk_lam(hf_id, BinderInfo::Default, hf_ty, step2))
    };

    // ── true minor : (true = true → 1 ≤ sz) → goal_at true. ──────────────────
    //   goal_at true ≡ 1·w ≤ 1·(sz·w).
    //   h_1_sz : 1 ≤ sz  (hsz_t (Eq.refl true))      [hsz_t : true = true → 1 ≤ sz]
    //   m1 : 1·w ≤ sz·w   (mul_le_r w 1 sz h_1_sz hw)
    //   h1w : 1·w = w     (one_mul w)  — subst LHS 1·w → w gives w ≤ sz·w
    //   m2 : w ≤ sz·w
    //   m3 : 1·w ≤ 1·(sz·w)  (mul_le_l 1 w (sz·w) m2 (0≤1))
    let true_minor = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let ht_ty = hyp_at(c.bool_true.clone());
        let (ht_id, hsz_t) = d.fresh_local(ht_ty.clone());

        let one = c.rat_one.clone();
        let sz_w = c.mul(sz.clone(), w.clone());
        let one_w = c.mul(one.clone(), w.clone());

        // h_1_sz : 1 ≤ sz
        let h_1_sz = Expr::app(hsz_t, c.refl_bool(c.bool_true.clone()));

        // m1 : 1·w ≤ sz·w   (mul_le_mul_of_nonneg_right w 1 sz h_1_sz hw)
        let m1 = Expr::apps(
            mul_le_r,
            [w.clone(), one.clone(), sz.clone(), h_1_sz, hw.clone()],
        );

        // m2 : w ≤ sz·w   (subst LHS 1·w → w via one_mul w)
        let h1w = Expr::app(one_mul.clone(), w.clone()); // 1·w = w
        let motive_lhs = {
            let mut g = EnvDeclBuilder::child_of(&d);
            let (t_id, t) = g.fresh_local(c.rat.clone());
            let body = c.le(t, sz_w.clone());
            g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let m2 = c.subst_rat(motive_lhs, one_w.clone(), w.clone(), h1w, m1);

        // 0 ≤ 1
        let zero_le_one = build_zero_le_one(c);
        // m3 : 1·w ≤ 1·(sz·w)
        let m3 = Expr::apps(mul_le_l, [one.clone(), w.clone(), sz_w, m2, zero_le_one]);
        d.finish_child(d.mk_lam(ht_id, BinderInfo::Default, ht_ty, m3))
    };

    // @Bool.rec.{0} motive false_minor true_minor bit : (bit = true → 1 ≤ sz) → goal_at bit
    // then apply `hsz : bit = true → 1 ≤ sz` to land `goal_at bit`.
    let rec = Expr::apps(bool_rec0, [motive, false_minor, true_minor, bit.clone()]);
    let body = Expr::app(rec, hsz);

    let e = b.mk_lam(hsz_id, BinderInfo::Default, h_sz_ty, body);
    let e = b.mk_lam(hw_id, BinderInfo::Default, h_w_ty, e);
    let e = b.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(sz_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(b.mk_lam(b_id, BinderInfo::Default, c.bool_.clone(), e))
}

/// `Rat.le Rat.zero Rat.one`, via `Rat.zero_lt_one` + `Rat.lt_iff_le_not_le`:
/// `(lt_iff_le_not_le 0 1).mp zero_lt_one : (0 ≤ 1) ∧ ¬(1 ≤ 0)`, then `And.left`.
/// Mirrors `HcBoundsConsts::zero_le_one`; all leaves Constructive, empty closure.
fn build_zero_le_one(c: &DcPointwiseConsts) -> Expr {
    let zero = c.rat_zero.clone();
    let one = c.rat_one.clone();
    let lt_01 = Expr::apps(
        Expr::const_(Name::from_string("Rat.lt"), vec![]),
        [zero.clone(), one.clone()],
    );
    let le_01 = c.le(zero.clone(), one.clone());
    let le_10 = c.le(one.clone(), zero.clone());
    let not_le_10 = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), le_10);
    let and_prop = Expr::apps(
        Expr::const_(Name::from_string("And"), vec![]),
        [le_01.clone(), not_le_10.clone()],
    );
    // (lt_iff_le_not_le 0 1) : Iff (Rat.lt 0 1) ((0≤1) ∧ ¬(1≤0))
    let iff = Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
        [zero.clone(), one.clone()],
    );
    // Iff.mp : ∀ {a b : Prop}, (a ↔ b) → a → b
    let iff_mp = Expr::apps(
        Expr::const_(Name::from_string("Iff.mp"), vec![]),
        [lt_01.clone(), and_prop.clone(), iff],
    );
    let zero_lt_one = Expr::const_(Name::from_string("Rat.zero_lt_one"), vec![]);
    let and_pair = Expr::app(iff_mp, zero_lt_one);
    // And.left : ∀ {a b : Prop}, a ∧ b → a
    Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [le_01, not_le_10, and_pair],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const LEMMAS: &[&str] = &["BoolAnalysis.lowband_dc_term"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_bridgestruct_pointwise()
            .expect("init_boolean_analysis_kkl_bridgestruct_pointwise");
        env.init_boolean_analysis_kkl_bridgestruct_pointwise()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_bridgestruct_pointwise_all_constructive_theorems() {
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
}
