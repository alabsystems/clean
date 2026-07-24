// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL half-power layer — Stage-A rational cores (axiom-free).
//!
//! # Why this module exists
//!
//! The sharp KKL max-influence retirement needs the `n`-FREE per-coordinate
//! charge `Σ_i Inf_i^{3/2} ≤ ε^{1/2}·I[f]`, whose per-coordinate step is the
//! half-power bound
//!
//! ```text
//!   0 ≤ x ≤ ε   ⟹   x^{3/2} ≤ ε^{1/2}·x.
//! ```
//!
//! `x^{3/2}` and `ε^{1/2}` are irrational in general, so the `Rat`-only overlay
//! cannot NAME the values. It CAN, however, name every INEQUALITY the charge
//! needs, because each one — both sides nonnegative — SQUARES to a purely
//! RATIONAL inequality provable on the existing `Rat` carrier with NO `√`:
//!
//! ```text
//!   (x^{3/2})² = x³ = (x·x)·x,      (ε^{1/2}·x)² = ε·x² = ε·(x·x),
//!   so   x^{3/2} ≤ ε^{1/2}·x   ⟺   (x·x)·x ≤ ε·(x·x).
//! ```
//!
//! The real-side half-power bound will be recovered, once the (separately
//! built) axiom-free `NNReal`/`sqrt` carrier exists, by the on-main squaring-
//! trick lemma `Rat.le_of_sq_le_sq : 0≤a → 0≤b → a·a ≤ b·b → a ≤ b` applied to
//! `a := x^{3/2}`, `b := ε^{1/2}·x`. The RATIONAL square `(x·x)·x ≤ ε·(x·x)`
//! discharged here IS that lemma's third premise. There is NO circularity: the
//! square is a closed `Rat` fact, proven without any sqrt.
//!
//! See `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` (Stage A) and the
//! obstruction report `designs/2026-06-18-kkl-root-free-obstruction.md`
//! (recommendation (a): the fractional-power carrier).
//!
//! # Bricks (all `Declaration::Theorem`, empty admitted-axiom closure)
//!
//! ```text
//! BoolAnalysis.cube_le_eps_sq_mul :                              -- the half-power shadow
//!   ∀ (x ε : Rat), Rat.le 0 x → Rat.le x ε →
//!     Rat.le (Rat.mul (Rat.mul x x) x) (Rat.mul ε (Rat.mul x x))
//!
//! BoolAnalysis.sq_le_sq_of_le_nonneg :                          -- forward sqrt-mono bridge
//!   ∀ (a b : Rat), Rat.le 0 a → Rat.le a b →
//!     Rat.le (Rat.mul a a) (Rat.mul b b)
//! ```
//!
//! `cube_le_eps_sq_mul` is the per-coordinate, `n`-free, root-free RATIONAL
//! shadow of the sharp `^{3/2}` charge. It is structurally DISTINCT from the
//! landed `sum_cube_le_eps_sq_mul_sum` (`Σg³ ≤ ε²·Σg`, the SUM-level cubic
//! charge that feeds the dead squared/Cauchy–Schwarz route): the RHS here is
//! `ε·x²` (one ε), the half-power square — not `ε²·g`.
//!
//! `sq_le_sq_of_le_nonneg` is the FORWARD direction of the sqrt-monotonicity
//! bridge (the on-main `Rat.le_of_sq_le_sq` is the reverse). Together they give
//! `0≤a → (a≤b ⟺ a·a ≤ b·b)` on nonnegatives — the rational engine that lifts
//! to `sqrt` monotone and `sqrt(x·y)=√x·√y` once the carrier exists.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms for the half-power rational shadows. Wraps `OrderConsts`
/// (the `Rat` field/order surface) plus the two monotonicity/`sq` leaves.
struct HalfPowerConsts {
    order: OrderConsts,
    mul_le_mul_left: Expr,
    mul_le_mul_right: Expr,
    mul_comm: Expr,
    sq_nonneg: Expr,
    le_trans: Expr,
}

impl HalfPowerConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            mul_le_mul_left: k("Rat.mul_le_mul_of_nonneg_left"),
            mul_le_mul_right: k("Rat.mul_le_mul_of_nonneg_right"),
            mul_comm: k("Rat.mul_comm"),
            sq_nonneg: k("Rat.sq_nonneg"),
            le_trans: k("Rat.le_trans"),
        }
    }

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn zero(&self) -> Expr {
        self.order.rat_zero.clone()
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
    /// `Rat.mul_le_mul_of_nonneg_left a b c (h_bc : b≤c) (h_0a : 0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, c: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(self.mul_le_mul_left.clone(), [a, b, c, h_bc, h_0a])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (h_bc : b≤c) (h_0a : 0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, c: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(self.mul_le_mul_right.clone(), [a, b, c, h_bc, h_0a])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nonneg_of(&self, a: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a)
    }
    /// `Rat.le_trans a b c (h_ab : a≤b) (h_bc : b≤c) : a ≤ c`.
    fn le_trans_of(&self, a: Expr, b: Expr, c: Expr, h_ab: Expr, h_bc: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, c, h_ab, h_bc])
    }
}

impl Environment {
    /// Register the KKL half-power Stage-A rational shadows. Idempotent.
    ///
    /// Registers `BoolAnalysis.cube_le_eps_sq_mul` and
    /// `BoolAnalysis.sq_le_sq_of_le_nonneg`, both constructive
    /// `Declaration::Theorem`s with empty admitted-axiom closure.
    pub fn init_boolean_analysis_kkl_halfpower(&mut self) -> Result<(), EnvError> {
        self.register_cube_le_eps_sq_mul()?;
        self.register_sq_le_sq_of_le_nonneg()?;
        Ok(())
    }

    /// `BoolAnalysis.cube_le_eps_sq_mul :
    ///   ∀ (x ε : Rat), 0 ≤ x → x ≤ ε → (x·x)·x ≤ ε·(x·x)`.
    ///
    /// The per-coordinate half-power shadow — the SQUARE of `x^{3/2} ≤ ε^{1/2}·x`
    /// for `0 ≤ x ≤ ε`. Constructive, empty admitted-axiom closure.
    ///
    /// Proof:
    /// - `h_xx : 0 ≤ x·x`        := `Rat.sq_nonneg x`
    /// - `step1 : (x·x)·x ≤ (x·x)·ε`
    ///       := `mul_le_mul_of_nonneg_left (a:=x·x) (b:=x) (c:=ε) h_le h_xx`
    /// - `comm : (x·x)·ε = ε·(x·x)` := `Rat.mul_comm (x·x) ε`
    /// - transport `step1` along `comm` with motive `fun t => (x·x)·x ≤ t`
    ///   (`Eq.subst`) ⟹ `(x·x)·x ≤ ε·(x·x)`.
    pub fn register_cube_le_eps_sq_mul(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.cube_le_eps_sq_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Constructive leaves (each a checked Theorem, empty closure).
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_*, Rat.sq_nonneg

        let c = HalfPowerConsts::new();

        // Type: ∀ x ε, 0≤x → x≤ε → (x·x)·x ≤ ε·(x·x).
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat());
            let (eps_id, eps) = b.fresh_local(c.rat());
            let h_nn = c.le0(x.clone());
            let (hnn_id, _) = b.fresh_local(h_nn.clone());
            let h_le = c.le(x.clone(), eps.clone());
            let (hle_id, _) = b.fresh_local(h_le.clone());

            let xx = c.mul(x.clone(), x.clone());
            let lhs = c.mul(xx.clone(), x.clone());
            let rhs = c.mul(eps.clone(), xx);
            let concl = c.le(lhs, rhs);

            let e = b.mk_pi(hle_id, BinderInfo::Default, h_le, concl);
            let e = b.mk_pi(hnn_id, BinderInfo::Default, h_nn, e);
            let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat(), e);
            b.finish(e)
        };

        // Value.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat());
            let (eps_id, eps) = b.fresh_local(c.rat());
            let h_nn = c.le0(x.clone());
            let (hnn_id, _hnn) = b.fresh_local(h_nn.clone());
            let h_le = c.le(x.clone(), eps.clone());
            let (hle_id, hle) = b.fresh_local(h_le.clone());

            let xx = c.mul(x.clone(), x.clone());

            // h_xx : 0 ≤ x·x
            let h_xx = c.sq_nonneg_of(x.clone());

            // step1 : (x·x)·x ≤ (x·x)·ε
            //   mul_le_mul_of_nonneg_left (a:=x·x) (b:=x) (c:=ε) (x≤ε) (0≤x·x)
            let step1 = c.mul_le_left(xx.clone(), x.clone(), eps.clone(), hle.clone(), h_xx);

            // comm : (x·x)·ε = ε·(x·x)
            let comm = c.mul_comm_of(xx.clone(), eps.clone());

            // transport along comm: motive t := (x·x)·x ≤ t
            let lhs = c.mul(xx.clone(), x.clone());
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let body = c.le(lhs.clone(), t);
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            let a = c.mul(xx.clone(), eps.clone()); // (x·x)·ε
            let bb = c.mul(eps.clone(), xx); // ε·(x·x)
            let body = c.order.subst(motive, a, bb, comm, step1);

            let e = b.mk_lam(hle_id, BinderInfo::Default, h_le, body);
            let e = b.mk_lam(hnn_id, BinderInfo::Default, h_nn, e);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
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

    /// `BoolAnalysis.sq_le_sq_of_le_nonneg :
    ///   ∀ (a b : Rat), 0 ≤ a → a ≤ b → a·a ≤ b·b`.
    ///
    /// The FORWARD direction of the nonneg sqrt-monotonicity bridge (companion
    /// to the on-main reverse `Rat.le_of_sq_le_sq`). Constructive, empty
    /// admitted-axiom closure.
    ///
    /// Proof (two monotonicity steps + transitivity, both products kept in the
    /// `a·_` / `_·b` shape so no commutation is needed):
    /// - `h0b : 0 ≤ b`     := `Rat.le_trans 0 a b (0≤a) (a≤b)`
    /// - `s1 : a·a ≤ a·b`  := `mul_le_mul_of_nonneg_left  (a:=a) (b:=a) (c:=b) (a≤b) (0≤a)`
    /// - `s2 : a·b ≤ b·b`  := `mul_le_mul_of_nonneg_right (a:=b) (b:=a) (c:=b) (a≤b) (0≤b)`
    /// - `Rat.le_trans (a·a) (a·b) (b·b) s1 s2 : a·a ≤ b·b`.
    pub fn register_sq_le_sq_of_le_nonneg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.sq_le_sq_of_le_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_*
        self.register_rat_le_trans_proof()?; // Rat.le_trans

        let c = HalfPowerConsts::new();

        // Type: ∀ a b, 0≤a → a≤b → a·a ≤ b·b.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat());
            let (bv_id, bv) = b.fresh_local(c.rat());
            let h_nn = c.le0(a.clone());
            let (hnn_id, _) = b.fresh_local(h_nn.clone());
            let h_le = c.le(a.clone(), bv.clone());
            let (hle_id, _) = b.fresh_local(h_le.clone());

            let lhs = c.mul(a.clone(), a.clone());
            let rhs = c.mul(bv.clone(), bv.clone());
            let concl = c.le(lhs, rhs);

            let e = b.mk_pi(hle_id, BinderInfo::Default, h_le, concl);
            let e = b.mk_pi(hnn_id, BinderInfo::Default, h_nn, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat());
            let (bv_id, bv) = b.fresh_local(c.rat());
            let h_nn = c.le0(a.clone());
            let (hnn_id, hnn) = b.fresh_local(h_nn.clone());
            let h_le = c.le(a.clone(), bv.clone());
            let (hle_id, hle) = b.fresh_local(h_le.clone());

            // h0b : 0 ≤ b
            let h0b = c.le_trans_of(c.zero(), a.clone(), bv.clone(), hnn.clone(), hle.clone());
            // s1 : a·a ≤ a·b   (left-mono with multiplier a)
            let s1 = c.mul_le_left(a.clone(), a.clone(), bv.clone(), hle.clone(), hnn);
            // s2 : a·b ≤ b·b   (right-mono with multiplier b)
            let s2 = c.mul_le_right(bv.clone(), a.clone(), bv.clone(), hle, h0b);
            // a·a ≤ b·b
            let body = c.le_trans_of(
                c.mul(a.clone(), a.clone()),
                c.mul(a.clone(), bv.clone()),
                c.mul(bv.clone(), bv.clone()),
                s1,
                s2,
            );

            let e = b.mk_lam(hle_id, BinderInfo::Default, h_le, body);
            let e = b.mk_lam(hnn_id, BinderInfo::Default, h_nn, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
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

    const LEMMAS: &[&str] = &[
        "BoolAnalysis.cube_le_eps_sq_mul",
        "BoolAnalysis.sq_le_sq_of_le_nonneg",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_halfpower()
            .expect("init_boolean_analysis_kkl_halfpower");
        env.init_boolean_analysis_kkl_halfpower()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_kkl_halfpower_all_constructive_theorems() {
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
    /// refute either bound. Both are TRUE conditional inequalities. By-hand
    /// edge-case checks:
    /// - `cube_le_eps_sq_mul` at `x=0` ⟹ `0 ≤ 0`; at `x=ε` ⟹ `ε³ ≤ ε³`
    ///   (equality); at `x=1,ε=1` ⟹ `1 ≤ 1`. The UNCONDITIONAL form (drop
    ///   `x≤ε`) is FALSE (`x=2,ε=1`: `8 ≤ 4`), so the hypothesis is essential.
    /// - `sq_le_sq_of_le_nonneg` at `a=b` ⟹ equality; at `a=0` ⟹ `0 ≤ b²`.
    ///   Dropping `0≤a` is FALSE (`a=-2,b=1`: `4 ≤ 1`).
    #[test]
    fn test_kkl_halfpower_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let info = env.get_const(&Name::from_string(name)).expect("registered");
            assert_eq!(
                refute_conjecture(&tc, &info.type_),
                None,
                "{name} is a TRUE conditional inequality; it must NOT refute on the \
                 dictator/parity/constant battery"
            );
        }
    }
}
