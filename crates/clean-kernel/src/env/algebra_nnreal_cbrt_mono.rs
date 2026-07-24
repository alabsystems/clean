// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — Stage B3 (4/n): cube dyadic numerator step bounds.
//!
//! # Why this module exists
//!
//! The Cauchy modulus for the scaled approximation `a_n = k_n/2^n` needs the
//! per-step increment pinned: `2·k_n ≤ k_{n+1} ≤ 2·k_n + 1`. These are the
//! purely STRUCTURAL facts
//!
//! ```text
//!   Rat.cbrtDyadicNum_two_mul_le_succ :
//!     ∀ x n, Nat.le (Nat.mul 2 (cbrtDyadicNum x n)) (cbrtDyadicNum x (succ n))
//!   Rat.cbrtDyadicNum_succ_le_two_mul_succ :
//!     ∀ x n, Nat.le (cbrtDyadicNum x (succ n)) (Nat.succ (Nat.mul 2 (cbrtDyadicNum x n)))
//! ```
//!
//! They need neither `0 ≤ x` nor `x < 1`: both digit branches produce a value
//! in `{2k, 2k+1}`, regardless of the (cube) digit test's CONTENT. The proof is
//! a dependent `Bool.rec.{0}` whose motive abstracts over the test result `z`,
//! so it is IDENTICAL in shape to the sqrt layer's (`algebra_nnreal_sqrt_mono.rs`)
//! — the only difference is the cube digit test fed to `Bool.rec`/`Eq.refl`.
//!
//! # Proof
//!
//! `cbrtDyadicNum x (succ n) ≡ @Bool.rec.{1} (fun _=>Nat) (2k) (2k+1) test` for
//! `k := cbrtDyadicNum x n`.
//!   * two_mul_le_succ: FALSE (`≡ 2k`) → `@Nat.le.refl (2k)`; TRUE (`≡ 2k+1 ≡
//!     succ 2k`) → `@Nat.le.step (2k)(2k)(refl)`.
//!   * succ_le_two_mul_succ: FALSE (`≡ 2k`) → `@Nat.le.step`; TRUE (`≡ succ 2k`)
//!     → `@Nat.le.refl (succ 2k)`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for the cube monotonicity step bounds.
pub(crate) struct CbrtMonoConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    nat_le: Expr,
    nat_le_refl: Expr,
    nat_le_step: Expr,
    rat: Expr,
    rat_cbrt_num: Expr,
    rat_ble: Expr,
    rat_ofnat: Expr,
    rat_mul: Expr,
    rat_cbrt_pow8: Expr,
    bool_ty: Expr,
    bool_true: Expr,
    bool_false: Expr,
    bool_rec_nat: Expr,
    bool_rec_prop: Expr,
    eq1: Expr,
    eq_refl1: Expr,
}

impl CbrtMonoConsts {
    pub(crate) fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_add: k("Nat.add"),
            nat_mul: k("Nat.mul"),
            nat_le: k("Nat.le"),
            nat_le_refl: k("Nat.le.refl"),
            nat_le_step: k("Nat.le.step"),
            rat: k("Rat"),
            rat_cbrt_num: k("Rat.cbrtDyadicNum"),
            rat_ble: k("Rat.ble"),
            rat_ofnat: k("Rat.ofNat"),
            rat_mul: k("Rat.mul"),
            rat_cbrt_pow8: k("Rat.cbrtDyadicPow8"),
            bool_ty: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            bool_rec_nat: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            bool_rec_prop: Expr::const_(Name::from_string("Bool.rec"), vec![l0]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [a, b])
    }
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }
    fn nle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn cnum(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_cbrt_num.clone(), [x.clone(), n])
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn pow8(&self, n: Expr) -> Expr {
        Expr::app(self.rat_cbrt_pow8.clone(), n)
    }
    /// `(ofNat m)³ := (ofNat m · ofNat m) · ofNat m`.
    fn cube_ofnat(&self, m: Expr) -> Expr {
        let r = self.rofnat(m);
        let sq = self.rmul(r.clone(), r.clone());
        self.rmul(sq, r)
    }
    fn eq_bool(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_ty.clone(), x, y])
    }
    fn refl_bool(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.bool_ty.clone(), x])
    }

    /// `cbrtDyadicNum x (succ n)`'s defining `Bool.rec` value at explicit `b`.
    fn bool_rec_num(&self, parent: &EnvDeclBuilder, kk: &Expr, b: Expr) -> Expr {
        let two_k = self.nmul(self.nat_lit(2), kk.clone());
        let two_k1 = self.nadd(two_k.clone(), self.nat_lit(1));
        let bmotive = {
            let mut bm = EnvDeclBuilder::child_of(parent);
            let (z_id, _z) = bm.fresh_local(self.bool_ty.clone());
            bm.finish_child(bm.mk_lam(
                z_id,
                BinderInfo::Default,
                self.bool_ty.clone(),
                self.nat.clone(),
            ))
        };
        Expr::apps(self.bool_rec_nat.clone(), [bmotive, two_k, two_k1, b])
    }

    /// The cube digit test `Rat.ble ((ofNat (2k+1))³) (x·8^{n+1})`.
    fn digit_test(&self, x: &Expr, kk: &Expr, n: &Expr) -> Expr {
        let two_k = self.nmul(self.nat_lit(2), kk.clone());
        let two_k1 = self.nadd(two_k, self.nat_lit(1));
        let lhs = self.cube_ofnat(two_k1);
        let rhs = self.rmul(x.clone(), self.pow8(self.succ(n.clone())));
        Expr::apps(self.rat_ble.clone(), [lhs, rhs])
    }
}

impl Environment {
    /// Register `Rat.cbrtDyadicNum_two_mul_le_succ` +
    /// `Rat.cbrtDyadicNum_succ_le_two_mul_succ`. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_cbrt_mono(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cbrt_dyadic()?; // cbrtDyadicNum, pow8, Rat.ble
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_le()?; // Nat.le, Nat.le.refl, Nat.le.step

        let c = CbrtMonoConsts::new();
        self.register_cbrt_dyadic_num_two_mul_le_succ(&c)?;
        self.register_cbrt_dyadic_num_succ_le_two_mul_succ(&c)
    }

    fn register_cbrt_dyadic_num_succ_le_two_mul_succ(
        &mut self,
        c: &CbrtMonoConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cbrtDyadicNum_succ_le_two_mul_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let succ_two_k = c.succ(c.nmul(c.nat_lit(2), c.cnum(&x, n.clone())));
            let concl = c.nle(c.cnum(&x, c.succ(n.clone())), succ_two_k);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());

            let kk = c.cnum(&x, n.clone());
            let two_k = c.nmul(c.nat_lit(2), kk.clone());
            let succ_two_k = c.succ(two_k.clone());
            let test = c.digit_test(&x, &kk, &n);

            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = mb.fresh_local(c.bool_ty.clone());
                let heq_ty = c.eq_bool(test.clone(), z.clone());
                let (heq_id, _heq) = mb.fresh_local(heq_ty.clone());
                let num_z = c.bool_rec_num(&mb, &kk, z.clone());
                let concl = c.nle(num_z, succ_two_k.clone());
                let body = mb.mk_pi(heq_id, BinderInfo::Default, heq_ty, concl);
                mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.bool_ty.clone(), body))
            };

            // FALSE: ≡ 2k, goal Nat.le (2k)(succ 2k) := @Nat.le.step (2k)(2k)(refl).
            let false_minor = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let heq_ty = c.eq_bool(test.clone(), c.bool_false.clone());
                let (heq_id, _heq) = fb.fresh_local(heq_ty.clone());
                let refl_2k = Expr::app(c.nat_le_refl.clone(), two_k.clone());
                let body = Expr::apps(
                    c.nat_le_step.clone(),
                    [two_k.clone(), two_k.clone(), refl_2k],
                );
                fb.finish_child(fb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body))
            };
            // TRUE: ≡ succ 2k, goal Nat.le (succ 2k)(succ 2k) := @Nat.le.refl (succ 2k).
            let true_minor = {
                let mut tb = EnvDeclBuilder::child_of(&b);
                let heq_ty = c.eq_bool(test.clone(), c.bool_true.clone());
                let (heq_id, _heq) = tb.fresh_local(heq_ty.clone());
                let body = Expr::app(c.nat_le_refl.clone(), succ_two_k.clone());
                tb.finish_child(tb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body))
            };

            let rec_app = Expr::apps(
                c.bool_rec_prop.clone(),
                [motive, false_minor, true_minor, test.clone()],
            );
            let applied = Expr::app(rec_app, c.refl_bool(test.clone()));

            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), applied);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    fn register_cbrt_dyadic_num_two_mul_le_succ(
        &mut self,
        c: &CbrtMonoConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cbrtDyadicNum_two_mul_le_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let two_k = c.nmul(c.nat_lit(2), c.cnum(&x, n.clone()));
            let concl = c.nle(two_k, c.cnum(&x, c.succ(n.clone())));
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());

            let kk = c.cnum(&x, n.clone());
            let two_k = c.nmul(c.nat_lit(2), kk.clone());
            let test = c.digit_test(&x, &kk, &n);

            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = mb.fresh_local(c.bool_ty.clone());
                let heq_ty = c.eq_bool(test.clone(), z.clone());
                let (heq_id, _heq) = mb.fresh_local(heq_ty.clone());
                let num_z = c.bool_rec_num(&mb, &kk, z.clone());
                let concl = c.nle(two_k.clone(), num_z);
                let body = mb.mk_pi(heq_id, BinderInfo::Default, heq_ty, concl);
                mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.bool_ty.clone(), body))
            };

            // FALSE: ≡ 2k, goal Nat.le (2k)(2k) := @Nat.le.refl (2k).
            let false_minor = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let heq_ty = c.eq_bool(test.clone(), c.bool_false.clone());
                let (heq_id, _heq) = fb.fresh_local(heq_ty.clone());
                let body = Expr::app(c.nat_le_refl.clone(), two_k.clone());
                fb.finish_child(fb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body))
            };
            // TRUE: ≡ succ 2k, goal Nat.le (2k)(succ 2k) := @Nat.le.step (2k)(2k)(refl).
            let true_minor = {
                let mut tb = EnvDeclBuilder::child_of(&b);
                let heq_ty = c.eq_bool(test.clone(), c.bool_true.clone());
                let (heq_id, _heq) = tb.fresh_local(heq_ty.clone());
                let refl_2k = Expr::app(c.nat_le_refl.clone(), two_k.clone());
                let body = Expr::apps(
                    c.nat_le_step.clone(),
                    [two_k.clone(), two_k.clone(), refl_2k],
                );
                tb.finish_child(tb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body))
            };

            let rec_app = Expr::apps(
                c.bool_rec_prop.clone(),
                [motive, false_minor, true_minor, test.clone()],
            );
            let applied = Expr::app(rec_app, c.refl_bool(test.clone()));

            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), applied);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
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

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cbrt_mono()
            .expect("init_algebra_nnreal_cbrt_mono");
        env.init_algebra_nnreal_cbrt_mono().expect("idempotent");
        env
    }

    const THMS: &[&str] = &[
        "Rat.cbrtDyadicNum_two_mul_le_succ",
        "Rat.cbrtDyadicNum_succ_le_two_mul_succ",
    ];

    #[test]
    fn test_cbrt_mono_kernel_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for nm in THMS {
            let name = Name::from_string(nm);
            let info = env.get_const(&name).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{nm} must be Theorem");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{nm} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_cbrt_mono_constructive_empty_closure() {
        let env = env();
        for nm in THMS {
            let name = Name::from_string(nm);
            assert_eq!(
                env.proof_quality(&name),
                Some(ProofQuality::Constructive),
                "{nm} must be Constructive"
            );
            assert!(
                env.axiom_deps(&name).expect("deps").is_empty(),
                "{nm} closure must be foundational-only: {:?}",
                env.axiom_deps(&name)
            );
        }
    }
}
