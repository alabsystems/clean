// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level foundational NN verification operations.
//!
//! Registers the missing foundational operations needed across NN verification
//! developments:
//!
//! - `NNVerify.NNVec.l1_norm`
//! - `NNVerify.IntervalBounds.width`
//! - `NNVerify.NNMat.transpose`
//! - `NNVerify.Zonotope.minkowski_add`
//! - `NNVerify.NNVec.sub`
//!
//! Part of #3220.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared constants for NN verification foundation operations.
struct NNFoundationConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    nn_vec: Expr,
    nn_mat: Expr,
    interval_bounds: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    zonotope: Expr,
    rat_abs: Expr,
    rat_sub: Expr,
    fin_sum: Expr,
}

impl NNFoundationConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            interval_bounds: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            #[cfg(test)]
            zonotope: Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]),
            rat_abs: Expr::const_(Name::from_string("Rat.abs"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
        }
    }

    fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    fn mat_of(&self, m: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m.clone()), n.clone())
    }

    fn ib_of(&self, d: &Expr) -> Expr {
        Expr::app(self.interval_bounds.clone(), d.clone())
    }

    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn zono_of(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::app(Expr::app(self.zonotope.clone(), n.clone()), k.clone())
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    fn abs(&self, x: Expr) -> Expr {
        Expr::app(self.rat_abs.clone(), x)
    }

    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_sub.clone(), a), b)
    }

    fn sum(&self, n: &Expr, f: Expr) -> Expr {
        Expr::app(Expr::app(self.fin_sum.clone(), n.clone()), f)
    }
}

impl Environment {
    /// Preload the shared NN-verify base layers used by the deep gamma-crown
    /// harnesses.
    ///
    /// This keeps the hotspot initializers flatter by establishing the
    /// foundational arithmetic / type / proof layers up front before the
    /// module-specific registration passes run.
    pub(crate) fn init_nn_verify_shared_bootstrap(&mut self) -> Result<(), EnvError> {
        self.init_rat()?;
        self.init_fin()?;
        self.init_rat_ord()?;
        self.init_and()?;
        self.init_eq()?;
        self.init_exists()?;
        self.init_true_false()?;
        self.init_rat_arith()?;
        self.init_rat_abs()?;
        self.init_fin_sum()?;
        self.init_rat_linear_order()?;
        self.init_rat_field_inst()?;
        self.init_rat_ordered_field_axioms()?;
        self.init_rat_minmax()?;
        self.init_nat_preorder()?;
        self.init_nn_verify_types()?;
        self.init_nn_verify_types_ops()?;
        self.init_nn_verify_zonotope()?;
        self.init_nn_verify_rat_ordering()?;
        self.init_nn_verify_proofs()?;
        Ok(())
    }

    /// Initialize foundational NN verification operations.
    ///
    /// Depends on: `init_nn_verify_types()`, `init_nn_verify_types_ops()`,
    /// `init_nn_verify_zonotope()`, `init_rat_arith()`, `init_rat_abs()`,
    /// `init_fin_sum()`.
    pub(crate) fn init_nn_verify_foundation_types(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_foundation_types_init {
            return Ok(());
        }
        self.init_nn_verify_shared_bootstrap()?;

        let c = NNFoundationConsts::new();
        self.register_nn_vec_l1_norm(&c)?;
        self.register_interval_bounds_width(&c)?;
        self.register_nn_mat_transpose(&c)?;
        // `NNVerify.Zonotope.minkowski_add` is now a faithful reducible
        // `Declaration::Definition` (generator concatenation over the real
        // Zonotope carrier via the `Fin` index-split). Registered in
        // `nn_verify_zonotope_minkowski_define.rs`; supersedes the legacy axiom.
        self.register_zonotope_minkowski_add_define()?;
        self.register_nn_vec_sub(&c)?;

        self.nn_verify_foundation_types_init = true;
        Ok(())
    }

    /// `NNVerify.NNVec.l1_norm (n : Nat) (v : NNVec n) : Rat :=`
    /// `  Fin.sum n (fun i => Rat.abs (v i))`
    fn register_nn_vec_l1_norm(&mut self, c: &NNFoundationConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.NNVec.l1_norm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (v_id, _) = b.fresh_local(vec_n.clone());
            let r = b.mk_pi(v_id, BinderInfo::Default, vec_n, c.rat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        let val = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (v_id, v) = b.fresh_local(vec_n.clone());
            let fin_n = c.fin_of(&n);
            let summand = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let v_i = Expr::app(v.clone(), i);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), c.abs(v_i));
                ch.finish_child(r)
            };
            let body = c.sum(&n, summand);
            let e = b.mk_lam(v_id, BinderInfo::Default, vec_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    /// `NNVerify.IntervalBounds.width (d : Nat) (B : IntervalBounds d) : NNVec d :=`
    /// `  fun i => Rat.sub (B.upper i) (B.lower i)`
    fn register_interval_bounds_width(&mut self, c: &NNFoundationConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.IntervalBounds.width");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let vec_d = c.vec_of(&d);
            let (bounds_id, _) = b.fresh_local(ib_d.clone());
            let r = b.mk_pi(bounds_id, BinderInfo::Default, ib_d, vec_d);
            let r = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        let val = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let (bounds_id, bounds) = b.fresh_local(ib_d.clone());
            let lower = Expr::proj(
                Name::from_string("NNVerify.IntervalBounds"),
                0,
                bounds.clone(),
            );
            let upper = Expr::proj(
                Name::from_string("NNVerify.IntervalBounds"),
                1,
                bounds.clone(),
            );
            let fin_d = c.fin_of(&d);
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let upper_i = Expr::app(upper.clone(), i.clone());
                let lower_i = Expr::app(lower.clone(), i);
                let r = ch.mk_lam(
                    i_id,
                    BinderInfo::Default,
                    fin_d.clone(),
                    c.sub(upper_i, lower_i),
                );
                ch.finish_child(r)
            };
            let e = b.mk_lam(bounds_id, BinderInfo::Default, ib_d, body);
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    /// `NNVerify.NNMat.transpose (m n : Nat) (W : NNMat m n) : NNMat n m :=`
    /// `  fun i j => W j i`
    fn register_nn_mat_transpose(&mut self, c: &NNFoundationConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.NNMat.transpose");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let mat_nm = c.mat_of(&n, &m);
            let (w_id, _) = b.fresh_local(mat_mn.clone());
            let r = b.mk_pi(w_id, BinderInfo::Default, mat_mn, mat_nm);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        let val = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let fin_n = c.fin_of(&n);
            let fin_m = c.fin_of(&m);
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let inner = {
                    let mut ch2 = EnvDeclBuilder::child_of(&ch);
                    let (j_id, j) = ch2.fresh_local(fin_m.clone());
                    let w_ji = Expr::app(Expr::app(w.clone(), j), i.clone());
                    let r = ch2.mk_lam(j_id, BinderInfo::Default, fin_m.clone(), w_ji);
                    ch2.finish_child(r)
                };
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), inner);
                ch.finish_child(r)
            };
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    /// `NNVerify.NNVec.sub (n : Nat) (v w : NNVec n) : NNVec n :=`
    /// `  fun i => Rat.sub (v i) (w i)`
    fn register_nn_vec_sub(&mut self, c: &NNFoundationConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.NNVec.sub");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (v_id, _) = b.fresh_local(vec_n.clone());
            let (w_id, _) = b.fresh_local(vec_n.clone());
            let r = b.mk_pi(w_id, BinderInfo::Default, vec_n.clone(), vec_n.clone());
            let r = b.mk_pi(v_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        let val = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (v_id, v) = b.fresh_local(vec_n.clone());
            let (w_id, w) = b.fresh_local(vec_n.clone());
            let fin_n = c.fin_of(&n);
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let v_i = Expr::app(v.clone(), i.clone());
                let w_i = Expr::app(w.clone(), i);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), c.sub(v_i, w_i));
                ch.finish_child(r)
            };
            let e = b.mk_lam(w_id, BinderInfo::Default, vec_n.clone(), body);
            let e = b.mk_lam(v_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::expr::{Expr, ExprKind};
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_foundation_types()
            .expect("init_nn_verify_foundation_types");
        env
    }

    fn assert_registered(env: &Environment, name: &str) {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
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
            ty.kind()
        );
    }

    fn assert_kind(env: &Environment, name: &str, expected: ConstantKind) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind, expected,
            "{name} should have kind {expected:?}, got {:?}",
            info.kind
        );
    }

    #[test]
    fn test_l1_norm_registered() {
        assert_registered(&make_env(), "NNVerify.NNVec.l1_norm");
    }

    #[test]
    fn test_interval_width_registered() {
        assert_registered(&make_env(), "NNVerify.IntervalBounds.width");
    }

    #[test]
    fn test_transpose_registered() {
        assert_registered(&make_env(), "NNVerify.NNMat.transpose");
    }

    #[test]
    fn test_minkowski_add_registered() {
        assert_registered(&make_env(), "NNVerify.Zonotope.minkowski_add");
    }

    #[test]
    fn test_nn_vec_sub_registered() {
        assert_registered(&make_env(), "NNVerify.NNVec.sub");
    }

    #[test]
    fn test_l1_norm_type_checks() {
        assert_type_checks_as_pi(&make_env(), "NNVerify.NNVec.l1_norm");
    }

    #[test]
    fn test_interval_width_type_checks() {
        assert_type_checks_as_pi(&make_env(), "NNVerify.IntervalBounds.width");
    }

    #[test]
    fn test_transpose_type_checks() {
        assert_type_checks_as_pi(&make_env(), "NNVerify.NNMat.transpose");
    }

    #[test]
    fn test_minkowski_add_type_checks() {
        assert_type_checks_as_pi(&make_env(), "NNVerify.Zonotope.minkowski_add");
    }

    #[test]
    fn test_nn_vec_sub_type_checks() {
        assert_type_checks_as_pi(&make_env(), "NNVerify.NNVec.sub");
    }

    #[test]
    fn test_reducible_defs_have_definition_kind() {
        let env = make_env();
        assert_kind(&env, "NNVerify.NNVec.l1_norm", ConstantKind::Definition);
        assert_kind(
            &env,
            "NNVerify.IntervalBounds.width",
            ConstantKind::Definition,
        );
        assert_kind(&env, "NNVerify.NNMat.transpose", ConstantKind::Definition);
        assert_kind(&env, "NNVerify.NNVec.sub", ConstantKind::Definition);
    }

    #[test]
    fn test_minkowski_add_has_definition_kind() {
        // DELIBERATE: minkowski_add is now a faithful reducible Definition
        // (generator concatenation over the real Zonotope carrier via the Fin
        // index-split). See nn_verify_zonotope_minkowski_define.rs. Companion
        // `minkowski_add_sound` stays a true-and-unrefutable axiom (the
        // concatenated-ε witness).
        let env = make_env();
        assert_kind(
            &env,
            "NNVerify.Zonotope.minkowski_add",
            ConstantKind::Definition,
        );
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_foundation_types().expect("first init");
        env.init_nn_verify_foundation_types().expect("second init");
    }
}
