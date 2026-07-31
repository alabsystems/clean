// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `Rat.div_mul_cancel_pos` ((a/b)·b = a for b > 0).
//!
//! # Why this module exists
//!
//! `NNReal.IsCauchy_mul` runs the f/g Cauchy tails at tolerance
//! `δ = (ε/2)/B'` (B' the common bound + 1). The product-perturbation bound
//! delivers `… + (δ·B' + δ·B')`, and collapsing `δ·B' = ε/2` is exactly the
//! cancellation `(a/b)·b = a` instantiated at `a = ε/2`, `b = B'`. That fact is
//! genuinely absent from the live Rat surface; this module proves it (ZERO
//! axioms added):
//!
//! - `Rat.div_mul_cancel_pos : ∀ a b : Rat,
//!       Rat.lt Rat.zero b → @Eq Rat (Rat.mul (Rat.div a b) b) a`
//!
//! # Proof
//!
//! `Rat.div a b ≡ Rat.mul a (Rat.inv b)` (reducible), so the LHS is
//! `(a·b⁻¹)·b`. Then:
//! ```text
//!   (a·b⁻¹)·b = a·(b⁻¹·b)     [Rat.mul_assoc a b⁻¹ b]
//!   b⁻¹·b = b·b⁻¹ = 1         [Rat.mul_comm, Rat.mul_inv_cancel b h_ne]
//!   a·(b⁻¹·b) = a·1 = a       [congrArg, Rat.mul_one]
//! ```
//! The nonzero side-condition `h_ne : b = 0 → False` comes from `0 < b`:
//! `Iff.mp (lt_iff_le_not_le 0 b) hpos` gives `¬(b ≤ 0)`; from `heq : b = 0`,
//! `Eq.subst (motive t := b ≤ t) (Rat.le_refl b)` yields `b ≤ 0`, contradiction.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for `Rat.div_mul_cancel_pos`.
pub(crate) struct DivMulConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_div: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    rat_lt: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    mul_one: Expr,
    mul_inv_cancel: Expr,
    le_refl: Expr,
    lt_iff: Expr,
    and_c: Expr,
    and_right: Expr,
    not_c: Expr,
    iff_mp: Expr,
    #[cfg(test)]
    false_c: Expr,
    eq_c: Expr,
    #[cfg(test)]
    eq_symm: Expr,
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
}

impl DivMulConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_div: k("Rat.div"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
            rat_lt: k("Rat.lt"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            mul_one: k("Rat.mul_one"),
            mul_inv_cancel: k("Rat.mul_inv_cancel"),
            le_refl: k("Rat.le_refl"),
            lt_iff: k("Rat.lt_iff_le_not_le"),
            and_c: k("And"),
            and_right: k("And.right"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            #[cfg(test)]
            false_c: k("False"),
            eq_c: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            #[cfg(test)]
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]),
        }
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    /// Typeclass `LE.le Rat instLERat a b`.
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn not_(&self, p: Expr) -> Expr {
        Expr::app(self.not_c.clone(), p)
    }
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_c.clone(), [self.rat.clone(), a, b])
    }
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a)
    }
    fn mul_inv_cancel(&self, a: Expr, h_ne: Expr) -> Expr {
        Expr::apps(self.mul_inv_cancel.clone(), [a, h_ne])
    }
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.le_refl.clone(), a)
    }
    #[cfg(test)]
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@congrArg Rat Rat a a' f h : Eq Rat (f a)(f a')`.
    fn congr_arg(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
}

impl Environment {
    /// Register `Rat.div_mul_cancel_pos`. Idempotent.
    pub fn init_algebra_rat_div_mul_cancel(&mut self) -> Result<(), EnvError> {
        // mul_assoc, mul_comm, mul_one, mul_inv_cancel, inv, div; le_refl,
        // lt_iff_le_not_le; And/Not/Iff/False/Eq.
        self.init_algebra_rat_inv_pos()?;
        self.init_and()?;
        self.init_eq()?;

        let c = DivMulConsts::new();
        self.register_rat_div_mul_cancel_pos(&c)
    }

    fn register_rat_div_mul_cancel_pos(&mut self, c: &DivMulConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.div_mul_cancel_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = c.rat_zero.clone();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let hpos_ty = c.lt(zero.clone(), bv.clone());
            let (h_id, _h) = b.fresh_local(hpos_ty.clone());
            let concl = c.eq_ty(c.mul(c.div(a.clone(), bv.clone()), bv.clone()), a.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hpos_ty, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let hpos_ty = c.lt(zero.clone(), bv.clone());
            let (hp_id, hp) = b.fresh_local(hpos_ty.clone());

            let inv_b = c.inv(bv.clone());

            // h_ne : (b = 0) → False.
            let h_ne = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let heq_ty = c.eq_ty(bv.clone(), zero.clone());
                let (heq_id, heq) = bn.fresh_local(heq_ty.clone());

                // not_b_le_0 : ¬ (b ≤ 0)  := And.right (Iff.mp (lt_iff 0 b) hp).
                let le_0b = c.le(zero.clone(), bv.clone());
                let not_le_b0 = c.not_(c.le(bv.clone(), zero.clone()));
                let and_ty = Expr::apps(c.and_c.clone(), [le_0b.clone(), not_le_b0.clone()]);
                let iff = Expr::apps(c.lt_iff.clone(), [zero.clone(), bv.clone()]);
                let mp = Expr::apps(
                    c.iff_mp.clone(),
                    [c.lt(zero.clone(), bv.clone()), and_ty, iff, hp.clone()],
                );
                let not_b_le_0 = Expr::apps(c.and_right.clone(), [le_0b, not_le_b0.clone(), mp]);

                // b ≤ 0 from le_refl b and heq : b = 0 (subst RHS b → 0).
                //   motive t := b ≤ t.
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&bn);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.le(bv.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let b_le_0 = c.subst(motive, bv.clone(), zero.clone(), heq, c.le_refl(bv.clone()));
                let false_pf = Expr::app(not_b_le_0, b_le_0);
                let e = bn.mk_lam(heq_id, BinderInfo::Default, heq_ty, false_pf);
                bn.finish_child(e)
            };

            // chain: (a·b⁻¹)·b = a·(b⁻¹·b) = a·1 = a.
            // s1 : (a·b⁻¹)·b = a·(b⁻¹·b)  [mul_assoc a b⁻¹ b].
            let s1 = c.mul_assoc(a.clone(), inv_b.clone(), bv.clone());
            // inv_cancel : b·b⁻¹ = 1 ; comm : b⁻¹·b = b·b⁻¹ ; trans → b⁻¹·b = 1.
            let inv_cancel = c.mul_inv_cancel(bv.clone(), h_ne);
            let comm = c.mul_comm(inv_b.clone(), bv.clone()); // b⁻¹·b = b·b⁻¹
            let invb_b = c.mul(inv_b.clone(), bv.clone()); // b⁻¹·b
            let b_invb = c.mul(bv.clone(), inv_b.clone()); // b·b⁻¹
            let invb_b_eq_one =
                c.eq_trans(invb_b.clone(), b_invb, c.rat_one.clone(), comm, inv_cancel); // b⁻¹·b = 1
                                                                                         // s2 : a·(b⁻¹·b) = a·1  [congrArg (a··) invb_b_eq_one].
            let mul_a_fn = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = fb.fresh_local(c.rat.clone());
                let body = c.mul(a.clone(), t);
                fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let a_one = c.mul(a.clone(), c.rat_one.clone());
            let s2 = c.congr_arg(invb_b.clone(), c.rat_one.clone(), mul_a_fn, invb_b_eq_one);
            // s3 : a·1 = a  [mul_one a].
            let s3 = c.mul_one(a.clone());
            // chain s1 → s2 → s3.
            let a_invbb = c.mul(a.clone(), invb_b.clone()); // a·(b⁻¹·b)
            let ab_b = c.mul(c.mul(a.clone(), inv_b.clone()), bv.clone()); // (a·b⁻¹)·b
            let c1 = c.eq_trans(ab_b.clone(), a_invbb.clone(), a_one.clone(), s1, s2); // (a·b⁻¹)·b = a·1
            let body = c.eq_trans(ab_b, a_one, a.clone(), c1, s3); // (a·b⁻¹)·b = a

            let e = b.mk_lam(hp_id, BinderInfo::Default, hpos_ty, body);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
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

    #[test]
    fn test_div_mul_cancel_pos_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_div_mul_cancel()
            .expect("init_algebra_rat_div_mul_cancel");
        env.init_algebra_rat_div_mul_cancel().expect("idempotent");

        let nm = Name::from_string("Rat.div_mul_cancel_pos");
        let info = env.get_const(&nm).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.div_mul_cancel_pos must kernel-check");

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
