// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `Rat.mul_left_close`, the single-shared-factor product
//! perturbation bound that `NNReal.mul`'s `Quot.lift` respect obligation needs.
//!
//! # Statement
//!
//! ```text
//! Rat.mul_left_close :
//!   ∀ (a x y B d : Rat),
//!     Rat.le Rat.zero a → Rat.lt a B → Rat.lt Rat.zero d →
//!     Rat.le x (Rat.add y d) →
//!     Rat.lt (Rat.mul a x) (Rat.add (Rat.mul a y) (Rat.mul d B))
//! ```
//!
//! # Proof
//!
//! ```text
//!   a·x ≤ a·(y+d) = a·y + a·d     (mul_le_mul_of_nonneg_left, left_distrib)
//!   a·d = d·a < d·B               (mul_comm, mul_lt_mul_of_pos_left a<B, 0<d)
//!   ⟹ a·y + a·d < a·y + d·B       (Rat.add_lt_add_left)
//!   ⟹ a·x < a·y + d·B             (Rat.lt_of_le_of_lt).
//! ```
//!
//! Unlike `Rat.mul_lt_mul_add_of_bounds` (the two-factor product estimate with a
//! `d·B + d·B` budget) only ONE factor varies here, so the budget is a single
//! `d·B`. `NNReal.mul`'s per-argument respect proof — where the shared `Quot`
//! representative is the common factor — uses exactly this shape.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Rat.mul_left_close`. Idempotent.
    pub fn init_algebra_rat_mul_left_close(&mut self) -> Result<(), EnvError> {
        self.init_rat_field_inst()?; // left_distrib, mul_comm
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left
        self.init_boolean_analysis_order_toolkit_b1b()?; // mul_lt_mul_of_pos_left
        self.init_boolean_analysis_kkl_strictadd2()?; // add_lt_add_left, lt_of_le_of_lt
        self.init_eq()?;
        self.register_rat_mul_left_close()
    }

    #[allow(clippy::too_many_lines)]
    fn register_rat_mul_left_close(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_left_close");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let le_le = Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]);
        let inst_le = k("instLERat");
        let rat_add = k("Rat.add");
        let rat_mul = k("Rat.mul");
        let rat_lt = k("Rat.lt");
        let add = |a: Expr, b: Expr| Expr::apps(rat_add.clone(), [a, b]);
        let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
        let lt = |a: Expr, b: Expr| Expr::apps(rat_lt.clone(), [a, b]);
        let le = |a: Expr, b: Expr| Expr::apps(le_le.clone(), [rat.clone(), inst_le.clone(), a, b]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (x_id, x) = b.fresh_local(rat.clone());
            let (y_id, y) = b.fresh_local(rat.clone());
            let (bb_id, bb) = b.fresh_local(rat.clone());
            let (d_id, d) = b.fresh_local(rat.clone());
            let h0a = le(zero.clone(), a.clone());
            let ha_b = lt(a.clone(), bb.clone());
            let h0d = lt(zero.clone(), d.clone());
            let hxy = le(x.clone(), add(y.clone(), d.clone()));
            let (h0a_id, _) = b.fresh_local(h0a.clone());
            let (ha_b_id, _) = b.fresh_local(ha_b.clone());
            let (h0d_id, _) = b.fresh_local(h0d.clone());
            let (hxy_id, _) = b.fresh_local(hxy.clone());
            let concl = lt(
                mul(a.clone(), x.clone()),
                add(mul(a.clone(), y.clone()), mul(d.clone(), bb.clone())),
            );
            let e = b.mk_pi(hxy_id, BinderInfo::Default, hxy, concl);
            let e = b.mk_pi(h0d_id, BinderInfo::Default, h0d, e);
            let e = b.mk_pi(ha_b_id, BinderInfo::Default, ha_b, e);
            let e = b.mk_pi(h0a_id, BinderInfo::Default, h0a, e);
            let e = b.mk_pi(d_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(y_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (x_id, x) = b.fresh_local(rat.clone());
            let (y_id, y) = b.fresh_local(rat.clone());
            let (bb_id, bb) = b.fresh_local(rat.clone());
            let (d_id, d) = b.fresh_local(rat.clone());
            let h0a_ty = le(zero.clone(), a.clone());
            let (h0a_id, h0a) = b.fresh_local(h0a_ty.clone());
            let ha_b_ty = lt(a.clone(), bb.clone());
            let (ha_b_id, ha_b) = b.fresh_local(ha_b_ty.clone());
            let h0d_ty = lt(zero.clone(), d.clone());
            let (h0d_id, h0d) = b.fresh_local(h0d_ty.clone());
            let hxy_ty = le(x.clone(), add(y.clone(), d.clone()));
            let (hxy_id, hxy) = b.fresh_local(hxy_ty.clone());

            let yd = add(y.clone(), d.clone()); // y+d
            let ay = mul(a.clone(), y.clone()); // a·y
            let ad = mul(a.clone(), d.clone()); // a·d
            let da = mul(d.clone(), a.clone()); // d·a
            let db = mul(d.clone(), bb.clone()); // d·B

            // step1 : a·x ≤ a·(y+d)  := mul_le_mul_of_nonneg_left a x (y+d) hxy h0a.
            let mul_le_left = k("Rat.mul_le_mul_of_nonneg_left");
            let step1 = Expr::apps(mul_le_left, [a.clone(), x.clone(), yd.clone(), hxy, h0a]);
            // ld : a·(y+d) = a·y + a·d  := left_distrib a y d.
            let left_distrib = k("Rat.left_distrib");
            let ld = Expr::apps(left_distrib, [a.clone(), y.clone(), d.clone()]);
            // motive_a t := a·x ≤ t ; subst (a·(y+d)) → (a·y+a·d).
            let eq_subst = Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            );
            let ax = mul(a.clone(), x.clone());
            let motive_a = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(rat.clone());
                let body = le(ax.clone(), t);
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
            };
            let ay_ad = add(ay.clone(), ad.clone());
            let step_a = Expr::apps(
                eq_subst.clone(),
                [
                    rat.clone(),
                    motive_a,
                    mul(a.clone(), yd.clone()),
                    ay_ad.clone(),
                    ld,
                    step1,
                ],
            ); // a·x ≤ a·y + a·d

            // t1 : d·a < d·B  := mul_lt_mul_of_pos_left d a B ha_b h0d.
            let mul_lt_left = k("Rat.mul_lt_mul_of_pos_left");
            let t1 = Expr::apps(mul_lt_left, [d.clone(), a.clone(), bb.clone(), ha_b, h0d]);
            // mc : a·d = d·a  := mul_comm a d ; subst t1's LHS (d·a → a·d).
            let mul_comm = k("Rat.mul_comm");
            let mc = Expr::apps(mul_comm, [a.clone(), d.clone()]); // a·d = d·a
            let eq_symm = Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            );
            let mc_symm = Expr::apps(eq_symm, [rat.clone(), ad.clone(), da.clone(), mc]); // d·a = a·d
            let motive_f = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(rat.clone());
                let body = lt(t, db.clone());
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
            };
            let ad_lt_db = Expr::apps(
                eq_subst.clone(),
                [rat.clone(), motive_f, da.clone(), ad.clone(), mc_symm, t1],
            ); // a·d < d·B

            // step_i : a·y + a·d < a·y + d·B  := add_lt_add_left (a·d)(d·B)(a·y) ad_lt_db.
            //   add_lt_add_left a b c (h:a<b) : (c+a) < (c+b).
            let add_lt_add_left = k("Rat.add_lt_add_left");
            let step_i = Expr::apps(
                add_lt_add_left,
                [ad.clone(), db.clone(), ay.clone(), ad_lt_db],
            ); // a·y + a·d < a·y + d·B

            // final : a·x < a·y + d·B  := lt_of_le_of_lt (a·x)(a·y+a·d)(a·y+d·B) step_a step_i.
            let lt_of_le_of_lt = k("Rat.lt_of_le_of_lt");
            let ay_db = add(ay.clone(), db.clone());
            let body = Expr::apps(lt_of_le_of_lt, [ax, ay_ad, ay_db, step_a, step_i]);

            let e = b.mk_lam(hxy_id, BinderInfo::Default, hxy_ty, body);
            let e = b.mk_lam(h0d_id, BinderInfo::Default, h0d_ty, e);
            let e = b.mk_lam(ha_b_id, BinderInfo::Default, ha_b_ty, e);
            let e = b.mk_lam(h0a_id, BinderInfo::Default, h0a_ty, e);
            let e = b.mk_lam(d_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_lam(y_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), e);
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
    fn test_mul_left_close_kernel_check_and_closure() {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_mul_left_close()
            .expect("init_algebra_rat_mul_left_close");
        env.init_algebra_rat_mul_left_close().expect("idempotent");

        let nm = Name::from_string("Rat.mul_left_close");
        let info = env.get_const(&nm).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.mul_left_close must kernel-check");
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
