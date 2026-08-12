// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — rung 7c (the squeeze `Equiv`) + rung 8b (THE KEYSTONE
//! IDENTITY `NNReal.sqrtRat x · NNReal.sqrtRat x = NNReal.ofRat x`).
//!
//! # The two rungs
//!
//! - **7c** `NNReal.dyadicApprox_sq_equiv_const :
//!     ∀ x (h0:0≤x)(h1:x<1),
//!       NNReal.CauSeq.Equiv (NNReal.CauSeq.mul (sqrtSeq x)(sqrtSeq x))
//!                           (NNReal.CauSeq.const (NNRat.ofRat x h0))`
//!   where `sqrtSeq x := NNReal.CauSeq.mk (Rat.dyadicApproxNN x)
//!   (NNReal.dyadicApprox_isCauchy x)` is the Cauchy carrier underneath
//!   `NNReal.sqrtRat x`. By the `NNRat.val`/`Subtype`/`NNReal.CauSeq.mul`/
//!   `NNReal.CauSeq.const` defeqs, the `Equiv` conjuncts at index `m` reduce to
//!   `a_m·a_m < x+ε` and `x < a_m·a_m+ε` for `a_m := Rat.dyadicApprox x m`, so
//!   the proof is built directly from the rung-7 squeeze bounds.
//!
//!   LOWER conjunct (`a_m·a_m < x+ε`, holds for ALL m): `a_m·a_m ≤ x`
//!   (`dyadicApprox_sq_le`) `< x+ε` (`x < x+ε`).
//!   UPPER conjunct (`x < a_m·a_m+ε`, for `m ≥ N := M+2` from
//!   `exists_inv_two_pow_lt ε ↦ M`): `x < a_m·a_m + 3·inv(2^m)`
//!   (`x_lt_dyadicApprox_sq_add_three_inv`) and `3·inv(2^m) < ε` (telescoped:
//!   `3·inv(2^m) ≤ 3·inv(2^{M+2}) ≤ inv(2^M) < ε` via `inv_two_pow_le_of_le` +
//!   `inv_two_pow_succ_add_self`), so `x < a_m·a_m + ε`.
//!
//! - **8b** `NNReal.sqrtRat_mul_self :
//!     ∀ x (h0:0≤x)(h1:x<1),
//!       NNReal.mul (NNReal.sqrtRat x)(NNReal.sqrtRat x) = NNReal.ofRat x h0`.
//!   `NNReal.mul (mk s)(mk s)` ι-reduces (two `Quot.lift` steps) to
//!   `Quot.mk Equiv (NNReal.CauSeq.mul s s)`, and `NNReal.ofRat x h0 =
//!   Quot.mk Equiv (NNReal.CauSeq.const (NNRat.ofRat x h0))`, so the goal is
//!   `Quot.sound` applied to rung 7c.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (closure ⊆ {Quot.sound, propext, Classical.choice} ∪ Eq builtins;
//! here exactly `{}` modulo `Quot.sound`, all foundational). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Universe note
//!
//! `Exists`/`Exists.intro`/`Exists.elim` over `Nat : Sort 1` are universe 1;
//! `Quot.sound`/`Eq` over `NNReal.CauSeq`/`NNReal : Sort 1` are universe 1.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

mod companions;
mod equiv;

/// Pre-resolved handles for the identity rung.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) struct IdentityConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_le: Expr,
    nat_le_refl: Expr,
    nat_le_step: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    rat_inv: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    rat_dyadic_approx: Expr,
    // Rat order bricks.
    rat_add_zero: Expr,
    rat_add_lt_add_left: Expr,
    rat_lt_of_le_of_lt: Expr,
    #[cfg(test)]
    rat_lt_of_lt_of_le: Expr,
    rat_lt_trans: Expr,
    rat_le_trans: Expr,
    rat_add_le_add: Expr,
    rat_le_refl: Expr,
    rat_eq_subst1: Expr,
    rat_eq_symm1: Expr,
    // squeeze lemmas.
    sq_le: Expr,
    x_lt_sq_add: Expr,
    // modulus + telescoping.
    exists_inv_two_pow_lt: Expr,
    inv_two_pow_le_of_le: Expr,
    inv_two_pow_succ_add_self: Expr,
    // carrier.
    #[cfg(test)]
    nnrat: Expr,
    nnrat_of_rat: Expr,
    nnreal: Expr,
    causeq: Expr,
    causeq_mk: Expr,
    causeq_mul: Expr,
    causeq_const: Expr,
    causeq_equiv: Expr,
    dyadic_approxnn: Expr,
    dyadic_iscauchy: Expr,
    nnreal_mul: Expr,
    #[cfg(test)]
    nnreal_mk: Expr,
    nnreal_of_rat: Expr,
    nnreal_sqrt: Expr,
    quot_sound: Expr,
    // logic.
    and_c: Expr,
    and_intro: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
}

impl IdentityConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            nat_le: k("Nat.le"),
            nat_le_refl: k("Nat.le.refl"),
            nat_le_step: k("Nat.le.step"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_add: k("Rat.add"),
            rat_inv: k("Rat.inv"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            rat_dyadic_approx: k("Rat.dyadicApprox"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            #[cfg(test)]
            rat_lt_of_lt_of_le: k("Rat.lt_of_lt_of_le"),
            rat_lt_trans: k("Rat.lt_trans"),
            rat_le_trans: k("Rat.le_trans"),
            rat_add_le_add: k("Rat.add_le_add"),
            rat_le_refl: k("Rat.le_refl"),
            rat_eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            rat_eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            sq_le: k("Rat.dyadicApprox_sq_le"),
            x_lt_sq_add: k("Rat.x_lt_dyadicApprox_sq_add_three_inv"),
            exists_inv_two_pow_lt: k("Rat.exists_inv_two_pow_lt"),
            inv_two_pow_le_of_le: k("Rat.inv_two_pow_le_of_le"),
            inv_two_pow_succ_add_self: k("Rat.inv_two_pow_succ_add_self"),
            #[cfg(test)]
            nnrat: k("NNRat"),
            nnrat_of_rat: k("NNRat.ofRat"),
            nnreal: k("NNReal"),
            causeq: k("NNReal.CauSeq"),
            causeq_mk: k("NNReal.CauSeq.mk"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            causeq_const: k("NNReal.CauSeq.const"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            dyadic_approxnn: k("Rat.dyadicApproxNN"),
            dyadic_iscauchy: k("NNReal.dyadicApprox_isCauchy"),
            nnreal_mul: k("NNReal.mul"),
            #[cfg(test)]
            nnreal_mk: k("NNReal.mk"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_sqrt: k("NNReal.sqrtRat"),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![l1.clone()]),
            and_c: k("And"),
            and_intro: k("And.intro"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![l1]),
        }
    }

    // ── small constructors ──
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn npow2(&self, n: Expr) -> Expr {
        Expr::apps(
            self.nat_pow.clone(),
            [self.succ(self.succ(self.nat_zero.clone())), n],
        )
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn inv_two_pow(&self, n: Expr) -> Expr {
        self.inv(self.ofnat(self.npow2(n)))
    }
    fn approx(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_approx.clone(), [x.clone(), n])
    }
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p, q, hp, hq])
    }
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, c, h1, h2])
    }
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn lt_of_lt_of_le(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_lt_of_le.clone(), [a, b, c, h1, h2])
    }
    fn lt_trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_trans.clone(), [a, b, c, h1, h2])
    }
    fn le_trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, c, h1, h2])
    }
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add.clone(), [a, b, cc, d, h1, h2])
    }
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b` (motive : Rat → Prop).
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.rat_eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@Eq.symm Rat a b h : b = a`.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    /// `inv_two_pow_le_of_le N n (N≤n) : inv(2^n) ≤ inv(2^N)`.
    fn inv_le_of_le(&self, big_n: Expr, n: Expr, h: Expr) -> Expr {
        Expr::apps(self.inv_two_pow_le_of_le.clone(), [big_n, n, h])
    }
    /// `inv_two_pow_succ_add_self k : inv(2^{k+1})+inv(2^{k+1}) = inv(2^k)`.
    fn succ_add_self(&self, k: Expr) -> Expr {
        Expr::app(self.inv_two_pow_succ_add_self.clone(), k)
    }

    /// The Cauchy sequence carrier underneath `NNReal.sqrtRat x`:
    /// `NNReal.CauSeq.mk (dyadicApproxNN x)(dyadicApprox_isCauchy x)`.
    fn sqrt_seq(&self, x: &Expr) -> Expr {
        let seq = Expr::app(self.dyadic_approxnn.clone(), x.clone());
        let hcau = Expr::app(self.dyadic_iscauchy.clone(), x.clone());
        Expr::apps(self.causeq_mk.clone(), [seq, hcau])
    }
    /// `NNReal.CauSeq.mul (sqrtSeq x)(sqrtSeq x)`.
    fn cmul(&self, x: &Expr) -> Expr {
        Expr::apps(
            self.causeq_mul.clone(),
            [self.sqrt_seq(x), self.sqrt_seq(x)],
        )
    }
    /// `NNReal.CauSeq.const (NNRat.ofRat x h0)`.
    fn cconst(&self, x: &Expr, h0: &Expr) -> Expr {
        let q = Expr::apps(self.nnrat_of_rat.clone(), [x.clone(), h0.clone()]);
        Expr::app(self.causeq_const.clone(), q)
    }
    /// `NNReal.CauSeq.Equiv f g`.
    fn equiv(&self, f: Expr, g: Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [f, g])
    }
}

impl Environment {
    /// Register rung 7c (`NNReal.dyadicApprox_sq_equiv_const`) and rung 8b
    /// (`NNReal.sqrtRat_mul_self`). Idempotent; axiom-free.
    pub fn init_algebra_nnreal_sqrt_identity(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_exists()?;
        self.init_nat()?;
        self.init_nat_succ_base()?; // Nat.le.refl, Nat.le.step
        self.init_quot(); // Quot.sound
                          // carrier + sqrtRat + mul + ofRat.
        self.init_algebra_nnreal_sqrt_def()?; // NNReal.sqrtRat, sqrtSeq pieces
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul, NNReal.CauSeq.mul
                                              // squeeze bounds.
        self.init_algebra_nnreal_sqrt_squeeze()?;
        // modulus + telescoping + double.
        self.init_algebra_rat_inv_dyadic_modulus()?; // exists_inv_two_pow_lt
        self.init_algebra_nnreal_sqrt_cauchy()?; // inv_two_pow_le_of_le
        self.init_algebra_nnreal_sqrt_cauchy_double()?; // inv_two_pow_succ_add_self
                                                        // Rat order toolkit used in the assembly.
        self.register_rat_add_lt_add_left()?; // add_lt_add_left
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_le_of_lt, lt_of_lt_of_le
        self.init_rat_linear_order()?; // le_trans, le_refl, lt_trans
        self.register_rat_add_le_add()?; // add_le_add

        self.init_algebra_nnreal_le()?; // NNReal.le, NNReal.CauSeq.le

        let c = IdentityConsts::new();
        self.register_dyadic_approx_sq_equiv_const(&c)?;
        self.register_sqrt_rat_mul_self(&c)?;
        self.register_zero_le_sqrt_rat(&c)?;
        Ok(())
    }

    /// Rung 8b — `NNReal.sqrtRat_mul_self`.
    fn register_sqrt_rat_mul_self(&mut self, c: &IdentityConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.sqrtRat_mul_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let equiv_thm = Expr::const_(
            Name::from_string("NNReal.dyadicApprox_sq_equiv_const"),
            vec![],
        );
        let eq_nn = |a: Expr, b: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [c.nnreal.clone(), a, b],
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let h1_ty = c.lt(x.clone(), c.rat_one.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let sx = Expr::app(c.nnreal_sqrt.clone(), x.clone());
            let lhs = Expr::apps(c.nnreal_mul.clone(), [sx.clone(), sx]);
            let rhs = Expr::apps(c.nnreal_of_rat.clone(), [x.clone(), h0.clone()]);
            let concl = eq_nn(lhs, rhs);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, concl);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let h1_ty = c.lt(x.clone(), c.rat_one.clone());
            let (h1_id, h1) = b.fresh_local(h1_ty.clone());

            // h_equiv : Equiv (cmul x)(cconst x h0).
            let h_equiv = Expr::apps(equiv_thm.clone(), [x.clone(), h0.clone(), h1.clone()]);
            // Quot.sound (cmul x)(cconst x h0) h_equiv :
            //   Quot.mk Equiv (cmul x) = Quot.mk Equiv (cconst x h0).
            //   LHS defeq NNReal.mul (sqrtRat x)(sqrtRat x); RHS defeq ofRat x h0.
            let body = Expr::apps(
                c.quot_sound.clone(),
                [
                    c.causeq.clone(),
                    c.causeq_equiv.clone(),
                    c.cmul(&x),
                    c.cconst(&x, &h0),
                    h_equiv,
                ],
            );
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, body);
            let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
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

    const THEOREMS: &[&str] = &[
        "NNReal.dyadicApprox_sq_equiv_const",
        "NNReal.sqrtRat_mul_self",
        "NNReal.zero_le_sqrtRat",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_identity()
            .expect("init_algebra_nnreal_sqrt_identity");
        env.init_algebra_nnreal_sqrt_identity().expect("idempotent");
        env
    }

    #[test]
    fn test_sqrt_identity_present_and_kernel_check() {
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
    fn test_sqrt_identity_constructive_empty_closure() {
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
