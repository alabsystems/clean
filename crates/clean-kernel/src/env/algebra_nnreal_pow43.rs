// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — rung 5 (partial): `0 ≤ cbrt x` and the `NNReal.pow43`
//! definition (`x^{4/3} := x · cbrt x`).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.zero_le_cbrt : ∀ x, NNReal.le (NNReal.ofRat 0 (le_refl 0))
//!                                         (NNReal.cbrt x)`.
//!   Mirrors `NNReal.zero_le_sqrtRat`: `NNReal.le (mk(const 0))(mk(cbrtSeq x))`
//!   ι-reduces (two `Quot.lift` steps) to `CauSeq.le (const 0)(cbrtSeq x)`,
//!   whose leaf at `(ε,n)` is (defeq) `0 < a_n + ε`; witness `N := 0`,
//!   `0 ≤ a_n` (`Rat.zero_le_cbrtDyadicApprox`) + `a_n < a_n+ε` close it.
//!
//! - `NNReal.pow43 : Rat → NNReal`
//!     `:= fun x => NNReal.mul (NNReal.cbrt x) (NNReal.cbrt x) (NNReal.cbrt x)?`
//!   No — `pow43 x := NNReal.mul (NNReal.ofRat x h?) (NNReal.cbrt x)`. Because
//!   `NNReal.ofRat` needs `0 ≤ x`, `pow43` carries that hypothesis:
//!     `NNReal.pow43 : (x : Rat) → Rat.le 0 x → NNReal`
//!     `:= fun x h => NNReal.mul (NNReal.ofRat x h) (NNReal.cbrt x)`.
//!   Reducible `Definition` (= `x^{4/3}` on `0 ≤ x < 1`).
//!
//! `Declaration::Theorem`/`Definition`, `ProofQuality::Constructive`, empty
//! admitted-axiom closure. NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.
//!
//! # Scope note (honest)
//!
//! The monotone law `cbrt x ≤ cbrt y` and the cube law `pow43³ = x⁴` are NOT in
//! this module: the former needs the radicand-monotone cube floor
//! `Rat.cbrtDyadicNum_mono` (a heavy `Nat.rec`+`Bool.rec` proof, the cube
//! analogue of the ~800-line `Rat.dyadicNum_mono`), and the latter needs
//! `NNReal.mul` commutativity/associativity, which are NOT yet registered as
//! kernel decls. Both are flagged as follow-ups rather than admitted as axioms.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for the pow43 rung.
pub(crate) struct Pow43Consts {
    nat: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    nat_le: Expr,
    rat_le_refl: Expr,
    rat_add_zero: Expr,
    rat_add_lt_add_left: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_cbrt_approx: Expr,
    rat_zero_le_cbrt_approx: Expr,
    nnrat_of_rat: Expr,
    nnreal: Expr,
    nnreal_le: Expr,
    nnreal_mul: Expr,
    nnreal_of_rat: Expr,
    nnreal_cbrt: Expr,
    eq_subst1: Expr,
    exists_intro: Expr,
}

impl Pow43Consts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_add: k("Rat.add"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            nat_le: k("Nat.le"),
            rat_le_refl: k("Rat.le_refl"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_cbrt_approx: k("Rat.cbrtDyadicApprox"),
            rat_zero_le_cbrt_approx: k("Rat.zero_le_cbrtDyadicApprox"),
            nnrat_of_rat: k("NNRat.ofRat"),
            nnreal: k("NNReal"),
            nnreal_le: k("NNReal.le"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_cbrt: k("NNReal.cbrt"),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1]),
        }
    }

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn approx(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_cbrt_approx.clone(), [x.clone(), n])
    }
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, c, h1, h2])
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `x < x+ε` from `0 < ε` (add_lt_add_left 0 ε x hpos transported along add_zero).
    fn x_lt_x_add_eps(&self, parent: &EnvDeclBuilder, x: &Expr, eps: &Expr, hpos: Expr) -> Expr {
        let h = self.add_lt_add_left(self.rat_zero.clone(), eps.clone(), x.clone(), hpos);
        let x_zero = self.add(x.clone(), self.rat_zero.clone());
        let x_eps = self.add(x.clone(), eps.clone());
        let e_az = self.add_zero(x.clone());
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.rat.clone());
            let body = self.lt(t, x_eps.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.subst(motive, x_zero, x.clone(), e_az, h)
    }
}

impl Environment {
    /// Register `NNReal.zero_le_cbrt` + `NNReal.pow43`. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_pow43(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_exists()?;
        self.init_nat()?;
        self.init_algebra_nnreal_cbrt_def()?; // NNReal.cbrt, cbrtSeq
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul
        self.init_algebra_nnreal_le()?; // NNReal.le
        self.init_algebra_nnreal_cbrt_seq()?; // Rat.cbrtDyadicApprox, zero_le_cbrtDyadicApprox
        self.init_rat_linear_order()?; // le_refl, lt_of...
        self.register_rat_add_lt_add_left()?;
        self.init_rat_field_inst()?; // add_zero
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_le_of_lt

        let c = Pow43Consts::new();
        self.register_zero_le_cbrt(&c)?;
        self.register_nnreal_pow43(&c)?;
        Ok(())
    }

    /// `NNReal.zero_le_cbrt : ∀ x, NNReal.le (NNReal.ofRat 0 (le_refl 0))
    ///                                       (NNReal.cbrt x)`.
    fn register_zero_le_cbrt(&mut self, c: &Pow43Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.zero_le_cbrt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let h0_zero = Expr::app(c.rat_le_refl.clone(), c.rat_zero.clone()); // 0 ≤ 0
        let of_zero = Expr::apps(
            c.nnreal_of_rat.clone(),
            [c.rat_zero.clone(), h0_zero.clone()],
        );

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let cx = Expr::app(c.nnreal_cbrt.clone(), x.clone());
            let concl = Expr::apps(c.nnreal_le.clone(), [of_zero.clone(), cx]);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), concl))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());

            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
            let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

            // pred N := ∀ n, N≤n → 0 < a_n + ε.
            let pred = |bb: &EnvDeclBuilder| -> Expr {
                let mut pn = EnvDeclBuilder::child_of(bb);
                let (cap_id, cap) = pn.fresh_local(c.nat.clone());
                let inner = {
                    let mut pi = EnvDeclBuilder::child_of(&pn);
                    let (n_id, n) = pi.fresh_local(c.nat.clone());
                    let hle_ty = c.nat_le(cap.clone(), n.clone());
                    let (hle_id, _hle) = pi.fresh_local(hle_ty.clone());
                    let a = c.approx(&x, n.clone());
                    let concl = c.lt(c.rat_zero.clone(), c.add(a.clone(), eps.clone()));
                    let e = pi.mk_pi(hle_id, BinderInfo::Default, hle_ty, concl);
                    let e = pi.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
                    pi.finish_child(e)
                };
                pn.finish_child(pn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner))
            };

            let witness = {
                let mut wb = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = wb.fresh_local(c.nat.clone());
                let hle_ty = c.nat_le(c.nat_zero.clone(), n.clone());
                let (hle_id, _hle) = wb.fresh_local(hle_ty.clone());
                let a = c.approx(&x, n.clone());
                let a_eps = c.add(a.clone(), eps.clone());
                let h0a = Expr::apps(c.rat_zero_le_cbrt_approx.clone(), [x.clone(), n.clone()]);
                let h_an_lt = c.x_lt_x_add_eps(&wb, &a, &eps, hpos.clone());
                let body = c.lt_of_le_of_lt(c.rat_zero.clone(), a.clone(), a_eps, h0a, h_an_lt);
                let e = wb.mk_lam(hle_id, BinderInfo::Default, hle_ty, body);
                let e = wb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
                wb.finish_child(e)
            };

            let intro = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), pred(&b), c.nat_zero.clone(), witness],
            );
            let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.pow43 : (x : Rat) → Rat.le 0 x → NNReal`
    ///   `:= fun x h => NNReal.mul (NNReal.ofRat x h) (NNReal.cbrt x)`.
    fn register_nnreal_pow43(&mut self, c: &Pow43Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.pow43");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let hnn = c.le(c.rat_zero.clone(), x.clone());
            let (h_id, _h) = b.fresh_local(hnn.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hnn, c.nnreal.clone());
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let hnn = c.le(c.rat_zero.clone(), x.clone());
            let (h_id, h) = b.fresh_local(hnn.clone());
            let ofx = Expr::apps(c.nnreal_of_rat.clone(), [x.clone(), h]);
            let cx = Expr::app(c.nnreal_cbrt.clone(), x.clone());
            let body = Expr::apps(c.nnreal_mul.clone(), [ofx, cx]);
            let e = b.mk_lam(h_id, BinderInfo::Default, hnn, body);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_pow43()
            .expect("init_algebra_nnreal_pow43");
        env.init_algebra_nnreal_pow43().expect("idempotent");
        env
    }

    #[test]
    fn test_pow43_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["NNReal.zero_le_cbrt", "NNReal.pow43"] {
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
    fn test_zero_le_cbrt_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.zero_le_cbrt");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }
}
