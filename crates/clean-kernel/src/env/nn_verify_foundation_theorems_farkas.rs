// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Foundation theorems for NN verification: Minkowski and Farkas (T08, T09).
//!
//! Registers the Minkowski sum soundness and Farkas certificate theorems.
//!
//! ## Theorems
//!
//! - **T08** `minkowski_add_sound`: Minkowski sum preserves containment
//! - **T09** `farkas_to_interval`: Farkas certificate yields linear bound
//!
//! ## Supporting definitions
//!
//! - `farkas_certificate_valid`: Farkas certificate validity predicate
//!
//! Part of #3151.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::nn_verify_foundation_theorems::FTConsts;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// T08: `minkowski_add_sound`
    ///
    /// ```text
    /// forall {n k1 k2 : Nat} (z1 : Zonotope n k1) (z2 : Zonotope n k2)
    ///        (x y : NNVec n),
    ///   Zonotope.contains z1 x ->
    ///   Zonotope.contains z2 y ->
    ///   Zonotope.contains (Zonotope.minkowski_add z1 z2) (NNVec.add x y)
    /// ```
    pub(super) fn register_minkowski_add_sound(&mut self, c: &FTConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.minkowski_add_sound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k1_id, k1) = b.fresh_local(c.nat.clone());
            let (k2_id, k2) = b.fresh_local(c.nat.clone());
            let zono_nk1 = c.zono_of(&n, &k1);
            let zono_nk2 = c.zono_of(&n, &k2);
            let vec_n = c.vec_of(&n);
            let (z1_id, z1) = b.fresh_local(zono_nk1.clone());
            let (z2_id, z2) = b.fresh_local(zono_nk2.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let (y_id, y) = b.fresh_local(vec_n.clone());
            let h1 = c.zono_contains(&n, &k1, &z1, &x);
            let h2 = c.zono_contains(&n, &k2, &z2, &y);
            let mink = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(c.zono_minkowski_add.clone(), n.clone()),
                            k1.clone(),
                        ),
                        k2.clone(),
                    ),
                    z1.clone(),
                ),
                z2.clone(),
            );
            let sum_xy = c.vec_add(&n, &x, &y);
            let k_sum = Expr::app(Expr::app(nat_add, k1), k2);
            let concl = c.zono_contains(&n, &k_sum, &mink, &sum_xy);
            let (h2_id, _) = b.fresh_local(h2.clone());
            let (h1_id, _) = b.fresh_local(h1.clone());
            let r = b.mk_pi(h2_id, BinderInfo::Default, h2, concl);
            let r = b.mk_pi(h1_id, BinderInfo::Default, h1, r);
            let r = b.mk_pi(y_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(z2_id, BinderInfo::Default, zono_nk2, r);
            let r = b.mk_pi(z1_id, BinderInfo::Default, zono_nk1, r);
            let r = b.mk_pi(k2_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(k1_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// Supporting definition: `farkas_certificate_valid`
    ///
    /// ```text
    /// (d : Nat) -> NNVec d -> Rat -> IntervalBounds d -> Prop
    /// ```
    pub(super) fn register_farkas_certificate_valid(
        &mut self,
        c: &FTConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.farkas_certificate_valid");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let vec_d = c.vec_of(&d);
            let ib_d = c.ib_of(&d);
            let (cv_id, _) = b.fresh_local(vec_d.clone());
            let (bound_id, _) = b.fresh_local(c.rat.clone());
            let (bnd_id, _) = b.fresh_local(ib_d.clone());
            let r = b.mk_pi(bnd_id, BinderInfo::Default, ib_d, c.prop.clone());
            let r = b.mk_pi(bound_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(cv_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// T09: `farkas_to_interval`
    ///
    /// ```text
    /// forall {d : Nat} (B : IntervalBounds d) (x : NNVec d) (cv : NNVec d)
    ///        (bound : Rat),
    ///   IntervalBounds.contains B x ->
    ///   farkas_certificate_valid d cv bound B ->
    ///   LE.le (NNVec.dot d cv x) bound
    /// ```
    pub(super) fn register_farkas_to_interval(&mut self, c: &FTConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.farkas_to_interval");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let farkas_valid = Expr::const_(
            Name::from_string("NNVerify.farkas_certificate_valid"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (bnd_id, bnd) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let (cv_id, cv) = b.fresh_local(vec_d.clone());
            let (bound_id, bound) = b.fresh_local(c.rat.clone());
            let h_contains = c.ib_contains_app(&d, &bnd, &x);
            // farkas_certificate_valid d cv bound B
            let h_farkas = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(farkas_valid, d.clone()), cv.clone()),
                    bound.clone(),
                ),
                bnd.clone(),
            );
            let dot = Expr::app(
                Expr::app(Expr::app(c.nn_vec_dot.clone(), d.clone()), cv.clone()),
                x.clone(),
            );
            let concl = c.rat_le(dot, bound);
            let (hf_id, _) = b.fresh_local(h_farkas.clone());
            let (hc_id, _) = b.fresh_local(h_contains.clone());
            let r = b.mk_pi(hf_id, BinderInfo::Default, h_farkas, concl);
            let r = b.mk_pi(hc_id, BinderInfo::Default, h_contains, r);
            let r = b.mk_pi(bound_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(cv_id, BinderInfo::Default, vec_d.clone(), r);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, r);
            let r = b.mk_pi(bnd_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::Environment;
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_foundation_theorems()
            .expect("init_nn_verify_foundation_theorems");
        env
    }

    fn assert_registered(env: &Environment, name: &str) {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }

    fn assert_type_checks_as_pi(env: &Environment, name: &str) {
        let expr = Expr::const_(Name::from_string(name), vec![]);
        let tc = TypeChecker::with_mode(env, env.mode());
        let ty = tc
            .infer_type(&expr)
            .unwrap_or_else(|err| panic!("{name} should type-check, got {err:?}"));
        assert!(
            matches!(ty.kind(), ExprKind::Pi(..)),
            "{name} type should be Pi, got {:?}",
            ty.kind(),
        );
    }

    fn assert_kind(env: &Environment, name: &str, expected: ConstantKind) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind, expected,
            "{name} should have kind {expected:?}, got {:?}",
            info.kind,
        );
    }

    #[test]
    fn test_minkowski_add_sound_registered() {
        assert_registered(&make_env(), "NNVerify.minkowski_add_sound");
    }

    #[test]
    fn test_minkowski_add_sound_type_checks() {
        assert_type_checks_as_pi(&make_env(), "NNVerify.minkowski_add_sound");
    }

    #[test]
    fn test_farkas_certificate_valid_registered() {
        assert_registered(&make_env(), "NNVerify.farkas_certificate_valid");
    }

    #[test]
    fn test_farkas_to_interval_registered() {
        assert_registered(&make_env(), "NNVerify.farkas_to_interval");
    }

    #[test]
    fn test_farkas_to_interval_type_checks() {
        assert_type_checks_as_pi(&make_env(), "NNVerify.farkas_to_interval");
    }

    #[test]
    fn test_all_farkas_minkowski_are_axioms() {
        let env = make_env();
        let axiom_names = [
            "NNVerify.minkowski_add_sound",
            "NNVerify.farkas_certificate_valid",
            "NNVerify.farkas_to_interval",
        ];
        for name in &axiom_names {
            assert_kind(&env, name, ConstantKind::Axiom);
        }
    }

    #[test]
    fn test_naming_convention() {
        let env = make_env();
        let names = [
            "NNVerify.minkowski_add_sound",
            "NNVerify.farkas_to_interval",
            "NNVerify.farkas_certificate_valid",
        ];
        for name in &names {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered with NNVerify. prefix",
            );
        }
    }
}
