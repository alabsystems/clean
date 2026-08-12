// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami dual `(4/3, 4)` two-point base — STEP 2, the RATIONAL fourth-moment.
//!
//! # Where this sits
//!
//! The `n = 1` case of the dual hypercontractivity inequality
//! `‖T_{1/3} f‖₄⁴ ≤ ‖f‖_{4/3}⁴` is the two-point base (refute-checked TRUE):
//!
//! ```text
//!   ½·[(a + b/3)⁴ + (a − b/3)⁴] ≤ (½·[|a+b|^{4/3} + |a−b|^{4/3}])³.
//! ```
//!
//! The LHS is the fourth MOMENT of `T_{1/3} f` (with `f(±1) = a ± b`,
//! `T_{1/3} f(±1) = a ± b/3`). It is PURELY RATIONAL: the odd cross-terms of the
//! two binomials cancel, leaving
//!
//! ```text
//!   ½·[(a + b/3)⁴ + (a − b/3)⁴] = (a⁴ + (2/3)·(a²·b²)) + (1/81)·b⁴.
//! ```
//!
//! This module materialises that rational identity (`f4` for the 2-point case)
//! as a kernel-checked `Declaration::Theorem`, `ProofQuality::Constructive`,
//! empty admitted-axiom closure.
//!
//! # Proof shape (axiom-free)
//!
//! The landed `Rat.fourth_power_rho_even_pair` proves the ρ-even-pair
//! `(a + ρb)⁴ + (a − ρb)⁴ = (2·a⁴ + 2·(ρb)⁴) + coeff·(a²·(ρb)²)` (honest
//! `coeff := (2·2)+2·(2·2)` and `ρb := ρ·b`, all `pow4`/`sq` left-nested). We
//! instantiate at `ρ := 1/3 := Rat.mk 1 3`, multiply by `½ := Rat.mk 1 2`,
//! `Rat.left_distrib`-distribute, and collapse each of the three legs:
//!
//! - `a⁴` leg:  `½·(2·a⁴) = a⁴`        (assoc; `½·2 = mk 2 2`, bridge `mk 2 2 = 1`).
//! - `(ρb)⁴` leg: `½·(2·(ρb)⁴) = (1/81)·b⁴`  (regroup `(ρb)⁴ = ρ⁴·b⁴` via
//!   `mul_mul_mul_comm`; assoc-collapse scalar `½·2·ρ⁴ = mk 2 162`, bridge `= 1/81`).
//! - cross leg: `½·(coeff·(a²·(ρb)²)) = (2/3)·(a²·b²)`  (regroup `(ρb)² = ρ²·b²`;
//!   assoc-collapse scalar `½·coeff·ρ² = mk 12 18`, bridge `= 2/3`).
//!
//! The componentwise `Rat.mk` products ground-reduce (defeq); the three
//! lowest-terms bridges (`mk 2 2 = mk 1 1`, `mk 12 18 = mk 2 3`,
//! `mk 2 162 = mk 1 81`) are single `Quot.sound`s with an `Eq.refl Int`
//! cross-product witness (the `build_rat_64_quarter_bridge` template).
//!
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`; never an Axiom or
//! refl-over-circular-def. The target's truth is the genuine even-pair identity.

use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Concrete `Rat.mk`-literal + Quot.sound builders for the moment's coefficients.
struct MomentConsts {
    nat_zero: Expr,
    nat_succ: Expr,
    int: Expr,
    int_of_nat: Expr,
    rat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    raw: Expr,
    raw_mk: Expr,
    raw_equiv: Expr,
    quot_mk: Expr,
    quot_sound: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    eq1: Expr,
    eq_refl1: Expr,
    eq_trans1: Expr,
    congr_arg: Expr,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl MomentConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int: k("Int"),
            int_of_nat: k("Int.ofNat"),
            rat: k("Rat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            raw: k("Rat.Raw"),
            raw_mk: k("Rat.Raw.mk"),
            raw_equiv: k("Rat.Raw.Equiv"),
            quot_mk: kl("Quot.mk"),
            quot_sound: kl("Quot.sound"),
            #[cfg(test)]
            eq1: kl("Eq"),
            eq_refl1: kl("Eq.refl"),
            eq_trans1: kl("Eq.trans"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn nat_lit(&self, n: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    /// `Rat.mk (Int.ofNat num) den`.
    fn frac(&self, num: u64, den: u64) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(num)),
                self.nat_lit(den),
            ],
        )
    }
    fn half(&self) -> Expr {
        self.frac(1, 2)
    }
    fn one_third(&self) -> Expr {
        self.frac(1, 3)
    }
    #[cfg(test)]
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    #[cfg(test)]
    fn rat_eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    fn refl_rat(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), a])
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }

    /// A `Quot.sound`-bridge `mk pn pd = mk qn qd` for equal fractions
    /// (`pn·qd = qn·pd` as `Int.ofNat`, witnessed by `Eq.refl (Int.ofNat prod)`).
    /// `prod` is the common cross-product value `pn·qd = qn·pd`.
    fn frac_bridge(&self, pn: u64, pd: u64, qn: u64, qd: u64, prod: u64) -> Expr {
        let raw_l = Expr::apps(
            self.raw_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(pn)),
                self.nat_lit(pd),
            ],
        );
        let raw_r = Expr::apps(
            self.raw_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(qn)),
                self.nat_lit(qd),
            ],
        );
        let equiv_proof = Expr::apps(
            self.eq_refl1.clone(),
            [
                self.int.clone(),
                Expr::app(self.int_of_nat.clone(), self.nat_lit(prod)),
            ],
        );
        let sound = Expr::apps(
            self.quot_sound.clone(),
            [
                self.raw.clone(),
                self.raw_equiv.clone(),
                raw_l.clone(),
                raw_r.clone(),
                equiv_proof,
            ],
        );
        let mk_l = Expr::apps(
            self.quot_mk.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), raw_l],
        );
        let mk_r = Expr::apps(
            self.quot_mk.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), raw_r],
        );
        // frac(pn,pd) defeq mk_l ; frac(qn,qd) defeq mk_r.
        let lhs = self.frac(pn, pd);
        let rhs = self.frac(qn, qd);
        let to_l = self.refl_rat(lhs.clone());
        let from_r = self.refl_rat(rhs.clone());
        let s1 = self.trans_rat(lhs.clone(), mk_l, mk_r.clone(), to_l, sound);
        self.trans_rat(lhs, mk_r, rhs, s1, from_r)
    }

    /// `congrArg (fun z => Rat.mul fixed z) h : fixed·a = fixed·b` for `h : a = b`.
    fn cong_mul_right(
        &self,
        parent: &EnvDeclBuilder,
        fixed: &Expr,
        a: Expr,
        b: Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.rat.clone());
            let body = Expr::apps(self.rat_mul.clone(), [fixed.clone(), w]);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `congrArg (fun z => Rat.mul z fixed) h : a·fixed = b·fixed` for `h : a = b`.
    fn cong_mul_left(
        &self,
        parent: &EnvDeclBuilder,
        fixed: &Expr,
        a: Expr,
        b: Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.rat.clone());
            let body = Expr::apps(self.rat_mul.clone(), [w, fixed.clone()]);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
}

impl Environment {
    /// Initialize the two-point-base RATIONAL fourth-moment layer.
    ///
    /// Registers `Rat.two_point_fourth_moment` as a kernel-checked
    /// `Declaration::Theorem`. Idempotent. Depends on
    /// `init_boolean_analysis_two_point_bound` (the ρ-even-pair) + the Rat ring
    /// surface (`Rat.left_distrib`, `Rat.mul_assoc`, `Rat.mul_comm`,
    /// `Rat.mul_mul_mul_comm`, `Rat.one_mul`). No axiom is added or removed.
    pub fn init_boolean_analysis_two_point_base_moment(&mut self) -> Result<(), EnvError> {
        self.init_boolean_analysis_two_point_bound()?;

        let rc = RingConsts::new();
        let mc = MomentConsts::new();
        self.register_rat_two_point_fourth_moment(&rc, &mc)?;
        Ok(())
    }

    /// `Rat.two_point_fourth_moment : ∀ a b : Rat,
    ///   Rat.mul ½ ((a + ⅓·b)⁴ + (a − ⅓·b)⁴)
    ///     = (a⁴ + (2/3)·(a²·b²)) + (1/81)·b⁴`.
    fn register_rat_two_point_fourth_moment(
        &mut self,
        rc: &RingConsts,
        mc: &MomentConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.two_point_fourth_moment");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_two_point_fourth_moment(rc, mc);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `pow4 s := (s·s)·(s·s)` (matches `pow4_of` in the even-pair module).
fn pow4_of(rc: &RingConsts, s: &Expr) -> Expr {
    let sq = rc.mul(s.clone(), s.clone());
    rc.mul(sq.clone(), sq)
}

include!("boolean_analysis_two_point_base_moment_legs.rs");

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_two_point_base_moment()
            .expect("init_boolean_analysis_two_point_base_moment");
        env.init_boolean_analysis_two_point_base_moment()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_two_point_fourth_moment_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("Rat.two_point_fourth_moment");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("two_point_fourth_moment must kernel-check: {e:?}"));
    }

    #[test]
    fn test_two_point_fourth_moment_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("Rat.two_point_fourth_moment");
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
