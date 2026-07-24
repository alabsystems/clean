// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut v3 SIZE assembly — the `dr²` cancellation identity
//! `BoolAnalysis.friedgut_dr_sq_cancel` (PLAN step A / "hcancel").
//!
//! ```text
//! BoolAnalysis.friedgut_dr_sq_cancel : ∀ (d : Nat) (K eps : Rat),
//!   Rat.lt Rat.zero K → Rat.lt Rat.zero eps →
//!     @Eq Rat (Rat.mul (Rat.mul m m) (Rat.mul dr dr)) (Rat.mul eps eps)
//! ```
//!
//! where `a := natCast (Nat.pow 9 d)`, `m := Rat.mul Rat.two (Rat.mul a K)`
//! (= `2·(a·K)`, byte-identical to `friedgut_low_budget_cancel`'s `big_den`),
//! and `dr := Rat.div eps m` (= `lowDr d K eps`, the LOW-band threshold root).
//!
//! i.e. `m²·dr² = eps²`. Since `m·m = (2·(a·K))² = 4·9^(2d)·K²` (a pure
//! commutative-monoid regrouping the SIZE conjunct performs separately), this is
//! the `eps²`-cancellation that the C-thr SIZE conjunct (`friedgut_size_conjunct`)
//! consumes: `influence_threshold_card_le` at `tau := dr²` gives `dr²·|J| ≤ K`;
//! multiplying through by `m·m` and rewriting `(m·m)·dr² = eps²` via THIS
//! identity converts the bound into `eps²·|J| ≤ (m·m)·K = 4·9^(2d)·K³`, which
//! `friedgut_size_poly_bound` caps by `eps²·2^(48·2^e)`, after which `eps² > 0`
//! cancels.
//!
//! Stating the identity in the `m·m` form (rather than the expanded
//! `4·9^(2d)·K²`) keeps this brick free of the `natCast 4 = Rat.two·Rat.two`
//! literal bridge (`Rat.two ≡ 1+1` is NOT def-eq to `natCast 2`), isolating the
//! pure division-cancellation core.
//!
//! # Proof (hand-built `Expr`, no tactics; constructive, EMPTY closure)
//!
//! The KEY fact is `dr·m = eps` (`Rat.div_mul_cancel_pos eps m hm_pos`, with
//! `0 < m` from `0 < a`, `0 < K`), whence `m·dr = eps` (`Rat.mul_comm`). Then:
//!
//! 1. `(m·m)·(dr·dr) = (m·dr)·(m·dr)`  — `Rat.mul_mul_mul_comm m m dr dr`.
//! 2. `(m·dr)·(m·dr) = eps·eps`  — `congrArg` twice along `m·dr = eps`.
//! 3. Chain 1 then 2.
//!
//! Positivity of `a := natCast(Nat.pow 9 d)` is re-derived exactly as in
//! `friedgut_low_budget_cancel` (`Nat.pow_le_pow_right` ⇒ `1 ≤ 9^d` ⇒
//! `natCast_ne_zero_of_pos` ⇒ `¬(a ≤ 0)` ⇒ `0 < a` via `lt_iff_le_not_le`).
//!
//! Every consumed declaration is a constructive `Declaration::Theorem`/reducible
//! `Definition` with an empty admitted-axiom closure, so this identity is
//! `ProofQuality::Constructive`. NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural` / `native_decide` / `unsafe`. No axiom added or removed.
//! Idempotent. Gated behind `cfg(any(test, feature = "math-overlays"))`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Carrier atoms for the `dr²` cancellation. Spellings byte-match
/// `friedgut_low_budget_cancel` (`Brick3Consts`).
struct DrSqConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_two: Expr,
    rat_mul: Expr,
    rat_div: Expr,
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    nat_pow: Expr,
    l1: Level,
}

impl DrSqConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_two: k("Rat.two"),
            rat_mul: k("Rat.mul"),
            rat_div: k("Rat.div"),
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            nat_pow: k("Nat.pow"),
            l1: Level::succ(Level::zero()),
        }
    }
    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [a, b])
    }
    /// `9^d := Nat.pow 9 d`.
    fn pow9_nat(&self, d: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(9), d.clone()])
    }
    /// `natCast m := Rat.mk (Int.ofNat m) 1` (byte-match the consumers).
    fn natcast(&self, m: &Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), m.clone()),
                self.nat_lit(1),
            ],
        )
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.le"), vec![]), [a, b])
    }
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    /// `congrArg.{1,1} Rat Rat a b f h : f a = f b`.
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a, b],
        )
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mul_mul_mul_comm(&self, a: Expr, b: Expr, cc: Expr, dd: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            [a, b, cc, dd],
        )
    }
    fn mul_pos(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_pos"), vec![]),
            [a, b, ha, hb],
        )
    }
    /// `Rat.div_mul_cancel_pos a b (0<b) : (a/b)·b = a`.
    fn div_mul_cancel_pos(&self, a: Expr, b: Expr, hpos: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.div_mul_cancel_pos"), vec![]),
            [a, b, hpos],
        )
    }
    /// `f := fun (z : Rat) => z · rhs`.
    fn lam_mul_right(&self, parent: &EnvDeclBuilder, rhs: Expr) -> Expr {
        let mut g = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = g.fresh_local(self.rat.clone());
        let body = self.mul(z, rhs);
        g.finish_child(g.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `f := fun (z : Rat) => lhs · z`.
    fn lam_mul_left(&self, parent: &EnvDeclBuilder, lhs: Expr) -> Expr {
        let mut g = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = g.fresh_local(self.rat.clone());
        let body = self.mul(lhs, z);
        g.finish_child(g.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
}

/// Build the `friedgut_dr_sq_cancel` type (`for_value=false`) / value.
fn dr_sq_build(c: &DrSqConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let (k_id, kk) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let a = c.natcast(&c.pow9_nat(&d)); // a := natCast(9^d)
    let a_k = c.mul(a.clone(), kk.clone()); // a·K
    let m = c.mul(c.rat_two.clone(), a_k.clone()); // m := 2·(a·K)  (= big_den)
    let dr = c.div(eps.clone(), m.clone()); // dr := eps/m  (= lowDr)
    let dr_dr = c.mul(dr.clone(), dr.clone()); // dr²
    let m_m = c.mul(m.clone(), m.clone()); // m²
    let lhs = c.mul(m_m.clone(), dr_dr.clone()); // (m·m)·(dr·dr)
    let eps_sq = c.mul(eps.clone(), eps.clone()); // eps²

    let hk_ty = c.lt(c.rat_zero.clone(), kk.clone()); // 0 < K
    let heps_ty = c.lt(c.rat_zero.clone(), eps.clone()); // 0 < eps
    let concl = c.eq_rat(lhs.clone(), eps_sq.clone());

    if !for_value {
        let (hk_id, _) = b.fresh_local(hk_ty.clone());
        let (heps_id, _) = b.fresh_local(heps_ty.clone());
        let e = b.mk_pi(heps_id, BinderInfo::Default, heps_ty, concl);
        let e = b.mk_pi(hk_id, BinderInfo::Default, hk_ty, e);
        let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_pi(k_id, BinderInfo::Default, c.rat.clone(), e);
        return b.finish(b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e));
    }

    // ── value ──
    let (hk_id, hk) = b.fresh_local(hk_ty.clone());
    let (heps_id, _heps) = b.fresh_local(heps_ty.clone());

    // ── 0 < a := natCast(9^d)  (re-derived as in friedgut_low_budget_cancel) ──
    let natcast_nonneg = Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]);
    let natcast_ne_zero = Expr::const_(Name::from_string("Rat.natCast_ne_zero_of_pos"), vec![]);
    let pow_le_pow_right = Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]);
    let le_antisymm = Expr::const_(Name::from_string("Rat.le_antisymm"), vec![]);
    let lt_iff = Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]);
    let iff_mpr = Expr::const_(Name::from_string("Iff.mpr"), vec![]);
    let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
    let not_c = Expr::const_(Name::from_string("Not"), vec![]);
    let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
    let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
    let nat_zero_le = Expr::const_(Name::from_string("Nat.zero_le"), vec![]);
    let zero_lt_two = Expr::const_(Name::from_string("Rat.zero_lt_two"), vec![]);

    let one = c.nat_lit(1);
    // 1 ≤ 9 := Nat.le.step^8 (Nat.le.refl 1).
    let mut h_1le9 = Expr::app(nat_le_refl.clone(), one.clone());
    {
        let mut cur = one.clone();
        for _ in 0..8 {
            let nxt = Expr::app(c.nat_succ.clone(), cur.clone());
            h_1le9 = Expr::apps(nat_le_step.clone(), [one.clone(), cur.clone(), h_1le9]);
            cur = nxt;
        }
    }
    let zero_le_d = Expr::app(nat_zero_le.clone(), d.clone());
    // 1 ≤ 9^d  (Nat.pow 9 0 ≡ 1 def-eq).
    let one_le_9pow = Expr::apps(
        pow_le_pow_right.clone(),
        [
            c.nat_lit(9),
            c.nat_zero.clone(),
            d.clone(),
            h_1le9,
            zero_le_d,
        ],
    );
    // 0 ≤ a.
    let h0a = Expr::app(natcast_nonneg.clone(), c.pow9_nat(&d));
    // a ≠ 0.
    let ha_ne = Expr::apps(natcast_ne_zero.clone(), [c.pow9_nat(&d), one_le_9pow]);
    // ¬(a ≤ 0) := fun hle => ha_ne (le_antisymm a 0 hle h0a).
    let not_a_le0 = {
        let mut g = EnvDeclBuilder::child_of(&b);
        let a_le0_ty = c.le(a.clone(), c.rat_zero.clone());
        let (hle_id, hle) = g.fresh_local(a_le0_ty.clone());
        let a_eq0 = Expr::apps(
            le_antisymm.clone(),
            [a.clone(), c.rat_zero.clone(), hle, h0a.clone()],
        );
        let body = Expr::app(ha_ne.clone(), a_eq0);
        g.finish_child(g.mk_lam(hle_id, BinderInfo::Default, a_le0_ty, body))
    };
    // ha_pos : 0 < a := Iff.mpr (lt_iff_le_not_le 0 a) (And.intro h0a not_a_le0).
    let lt0a = c.lt(c.rat_zero.clone(), a.clone());
    let le0a = c.le(c.rat_zero.clone(), a.clone());
    let not_le_a0 = Expr::app(not_c.clone(), c.le(a.clone(), c.rat_zero.clone()));
    let and_pair = Expr::apps(
        and_intro.clone(),
        [le0a.clone(), not_le_a0.clone(), h0a.clone(), not_a_le0],
    );
    let iff_la = Expr::apps(lt_iff.clone(), [c.rat_zero.clone(), a.clone()]);
    let and_ty = Expr::apps(
        Expr::const_(Name::from_string("And"), vec![]),
        [le0a, not_le_a0],
    );
    let ha_pos = Expr::apps(iff_mpr.clone(), [lt0a, and_ty, iff_la, and_pair]);

    // ── 0 < m := 2·(a·K) ──
    let h_ak_pos = c.mul_pos(a.clone(), kk.clone(), ha_pos.clone(), hk.clone());
    let hm_pos = c.mul_pos(
        c.rat_two.clone(),
        a_k.clone(),
        zero_lt_two.clone(),
        h_ak_pos,
    );

    // ── KEY: dr·m = eps, hence m·dr = eps ──
    let dr_m = c.mul(dr.clone(), m.clone()); // dr·m
    let m_dr = c.mul(m.clone(), dr.clone()); // m·dr
                                             // dr·m = eps  := Rat.div_mul_cancel_pos eps m hm_pos.
    let dr_m_eq_eps = c.div_mul_cancel_pos(eps.clone(), m.clone(), hm_pos);
    // m·dr = dr·m  := Rat.mul_comm m dr.
    let mdr_eq_drm = c.mul_comm(m.clone(), dr.clone());
    // m·dr = eps  := trans (m·dr = dr·m) (dr·m = eps).
    let mdr_eq_eps = c.trans_rat(
        m_dr.clone(),
        dr_m.clone(),
        eps.clone(),
        mdr_eq_drm,
        dr_m_eq_eps,
    );

    // ── (m·dr)·(m·dr) = eps·eps ──
    let mdr_mdr = c.mul(m_dr.clone(), m_dr.clone());
    let eps_mdr = c.mul(eps.clone(), m_dr.clone());
    //   s1 : (m·dr)·(m·dr) = eps·(m·dr)   congrArg (·(m·dr)) mdr_eq_eps.
    let s1 = c.congr_arg(
        m_dr.clone(),
        eps.clone(),
        c.lam_mul_right(&b, m_dr.clone()),
        mdr_eq_eps.clone(),
    );
    //   s2 : eps·(m·dr) = eps·eps   congrArg (eps·) mdr_eq_eps.
    let s2 = c.congr_arg(
        m_dr.clone(),
        eps.clone(),
        c.lam_mul_left(&b, eps.clone()),
        mdr_eq_eps.clone(),
    );
    // mdr_sq_eq_epssq : (m·dr)·(m·dr) = eps·eps.
    let mdr_sq_eq_epssq = c.trans_rat(mdr_mdr.clone(), eps_mdr.clone(), eps_sq.clone(), s1, s2);

    // ── (m·m)·(dr·dr) = (m·dr)·(m·dr)  := Rat.mul_mul_mul_comm m m dr dr ──
    let lhs_eq_mdrmdr = c.mul_mul_mul_comm(m.clone(), m.clone(), dr.clone(), dr.clone());

    // proof : (m·m)·(dr·dr) = (m·dr)·(m·dr) = eps·eps.
    let proof = c.trans_rat(
        lhs.clone(),
        mdr_mdr.clone(),
        eps_sq.clone(),
        lhs_eq_mdrmdr,
        mdr_sq_eq_epssq,
    );

    let e = b.mk_lam(heps_id, BinderInfo::Default, heps_ty, proof);
    let e = b.mk_lam(hk_id, BinderInfo::Default, hk_ty, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// `BoolAnalysis.friedgut_dr_sq_cancel :
    ///   ∀ (d : Nat) (K eps : Rat), 0 < K → 0 < eps →
    ///     (m·m)·(dr·dr) = eps·eps`
    ///
    /// where `a := natCast(Nat.pow 9 d)`, `m := 2·(a·K)`, `dr := eps/m`
    /// (= `lowDr d K eps`).
    ///
    /// The `eps²`-cancellation core for the C-thr SIZE conjunct (PLAN step A).
    /// The KEY fact `dr·m = eps` (`Rat.div_mul_cancel_pos`) collapses `m²·dr²` to
    /// `eps²` by pure commutative-monoid regrouping (`Rat.mul_mul_mul_comm` +
    /// `Rat.mul_comm`). Kernel-checked, `Constructive`, empty admitted-axiom
    /// closure. Idempotent. No axiom added or removed.
    pub fn register_friedgut_dr_sq_cancel(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_dr_sq_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_nat()?;
        self.init_algebra_rat_halves()?; // Rat.two, Rat.zero_lt_two
        self.init_rat_field_inst()?; // mul_comm
        self.init_rat_linear_order()?; // mul_pos, le_antisymm, lt_iff_le_not_le
        self.init_algebra_rat_div_mul_cancel()?; // div_mul_cancel_pos, Rat.div
        self.register_expect_one_theorems()?; // Rat.natCast_ne_zero_of_pos
        self.register_natcast_nonneg()?; // BoolAnalysis.natCast_nonneg
        self.register_nat_pow_le_pow_right_proof()?; // Nat.pow_le_pow_right
        self.register_rat_zero_lt_two()?;
        self.register_rat_mul_mul_mul_comm_theorem()?; // Rat.mul_mul_mul_comm
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = DrSqConsts::new();
        let ty = dr_sq_build(&c, false);
        let value = dr_sq_build(&c, true);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_friedgut_dr_sq_cancel_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_dr_sq_cancel()
            .expect("register_friedgut_dr_sq_cancel");
        env.register_friedgut_dr_sq_cancel().expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.friedgut_dr_sq_cancel");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|dp| dp.to_string())
                .collect::<Vec<_>>()
        );
    }
}
