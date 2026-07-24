// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Monotonicity axioms for element-wise vector/matrix inequalities.
//!
//! These are mathematically sound axioms (not proved in-kernel) that
//! provide the lemmas needed by linarith for NN verification proofs.
//!
//! ## Axioms
//!
//! - `NNVerify.vec_le_trans`: a <= b -> b <= c -> a <= c
//! - `NNVerify.vec_le_add_mono`: a <= b -> c <= d -> a+c <= b+d
//! - `NNVerify.vec_le_smul_nonneg`: 0 <= s -> a <= b -> s*a <= s*b
//! - `NNVerify.mat_mulvec_le_mono`: A nonneg -> x <= y -> A*x <= A*y
//! - `NNVerify.abs_vec_le`: |x_i| <= b_i -> -b <= x <= b
//! - `NNVerify.interval_contains_vec_le`: contains B x -> lo <= x <= hi
//!
//! Part of #3181.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::nn_verify_elementwise::ElemConsts;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register all element-wise inequality axioms.
    pub(super) fn register_elementwise_axioms(&mut self, c: &ElemConsts) -> Result<(), EnvError> {
        self.register_vec_le_trans(c)?;
        self.register_vec_le_add_mono(c)?;
        self.register_vec_le_smul_nonneg(c)?;
        self.register_mat_mulvec_le_mono(c)?;
        self.register_abs_vec_le(c)?;
        self.register_interval_contains_vec_le(c)?;
        Ok(())
    }

    /// `NNVerify.vec_le_trans`:
    /// `{n} -> (a b c : NNVec n) -> vec_le a b -> vec_le b c -> vec_le a c`
    fn register_vec_le_trans(&mut self, c: &ElemConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (a_id, a) = b.fresh_local(vec_n.clone());
            let (bv_id, bv) = b.fresh_local(vec_n.clone());
            let (cv_id, cv) = b.fresh_local(vec_n.clone());
            let vle = c.vec_le_ref();
            let h_ab = Expr::app(
                Expr::app(Expr::app(vle.clone(), n.clone()), a.clone()),
                bv.clone(),
            );
            let h_bc = Expr::app(Expr::app(Expr::app(vle.clone(), n.clone()), bv), cv.clone());
            let goal = Expr::app(Expr::app(Expr::app(vle, n), a), cv);
            let (h2_id, _) = b.fresh_local(h_bc.clone());
            let (h1_id, _) = b.fresh_local(h_ab.clone());
            let r = b.mk_pi(h2_id, BinderInfo::Default, h_bc, goal);
            let r = b.mk_pi(h1_id, BinderInfo::Default, h_ab, r);
            let r = b.mk_pi(cv_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(bv_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.vec_le_trans"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `NNVerify.vec_le_add_mono`:
    /// `{n} -> (a b c d : NNVec n) -> vec_le a b -> vec_le c d`
    /// `-> vec_le (add a c) (add b d)`
    fn register_vec_le_add_mono(&mut self, c: &ElemConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (a_id, a) = b.fresh_local(vec_n.clone());
            let (bv_id, bv) = b.fresh_local(vec_n.clone());
            let (cv_id, cv) = b.fresh_local(vec_n.clone());
            let (dv_id, dv) = b.fresh_local(vec_n.clone());
            let vle = c.vec_le_ref();
            let vadd = c.nn_vec_add.clone();
            let h_ab = Expr::app(
                Expr::app(Expr::app(vle.clone(), n.clone()), a.clone()),
                bv.clone(),
            );
            let h_cd = Expr::app(
                Expr::app(Expr::app(vle.clone(), n.clone()), cv.clone()),
                dv.clone(),
            );
            let add_ac = Expr::app(Expr::app(Expr::app(vadd.clone(), n.clone()), a), cv);
            let add_bd = Expr::app(Expr::app(Expr::app(vadd, n.clone()), bv), dv);
            let goal = Expr::app(Expr::app(Expr::app(vle, n), add_ac), add_bd);
            let (h2_id, _) = b.fresh_local(h_cd.clone());
            let (h1_id, _) = b.fresh_local(h_ab.clone());
            let r = b.mk_pi(h2_id, BinderInfo::Default, h_cd, goal);
            let r = b.mk_pi(h1_id, BinderInfo::Default, h_ab, r);
            let r = b.mk_pi(dv_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(cv_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(bv_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.vec_le_add_mono"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `NNVerify.vec_le_smul_nonneg`:
    /// `{n} -> (s : Rat) -> (a b : NNVec n) ->`
    /// `  LE.le Rat.zero s -> vec_le a b -> vec_le (smul s a) (smul s b)`
    fn register_vec_le_smul_nonneg(&mut self, c: &ElemConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let (a_id, a) = b.fresh_local(vec_n.clone());
            let (bv_id, bv) = b.fresh_local(vec_n.clone());
            let vle = c.vec_le_ref();
            let h_s = c.rat_le(c.rat_zero.clone(), s.clone());
            let h_ab = Expr::app(
                Expr::app(Expr::app(vle.clone(), n.clone()), a.clone()),
                bv.clone(),
            );
            let smul_sa = Expr::app(
                Expr::app(Expr::app(c.nn_vec_smul.clone(), n.clone()), s.clone()),
                a,
            );
            let smul_sb = Expr::app(
                Expr::app(Expr::app(c.nn_vec_smul.clone(), n.clone()), s),
                bv,
            );
            let goal = Expr::app(Expr::app(Expr::app(vle, n), smul_sa), smul_sb);
            let (h2_id, _) = b.fresh_local(h_ab.clone());
            let (h1_id, _) = b.fresh_local(h_s.clone());
            let r = b.mk_pi(h2_id, BinderInfo::Default, h_ab, goal);
            let r = b.mk_pi(h1_id, BinderInfo::Default, h_s, r);
            let r = b.mk_pi(bv_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.vec_le_smul_nonneg"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `NNVerify.mat_mulvec_le_mono`:
    /// `{m n} -> (A : NNMat m n) -> (x y : NNVec n) ->`
    /// `  mat_nonneg A -> vec_le x y -> vec_le (mulVec A x) (mulVec A y)`
    fn register_mat_mulvec_le_mono(&mut self, c: &ElemConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let vec_n = c.vec_of(&n);
            let _vec_m = c.vec_of(&m);
            let (a_id, a) = b.fresh_local(mat_mn.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let (y_id, y) = b.fresh_local(vec_n.clone());
            let h_nn = Expr::app(
                Expr::app(Expr::app(c.mat_nonneg_ref(), m.clone()), n.clone()),
                a.clone(),
            );
            let vle = c.vec_le_ref();
            let h_xy = Expr::app(
                Expr::app(Expr::app(vle.clone(), n.clone()), x.clone()),
                y.clone(),
            );
            let mul_ax = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(c.nn_mat_mulvec.clone(), m.clone()), n.clone()),
                    a.clone(),
                ),
                x,
            );
            let mul_ay = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(c.nn_mat_mulvec.clone(), m.clone()), n),
                    a,
                ),
                y,
            );
            let goal = Expr::app(Expr::app(Expr::app(vle, m), mul_ax), mul_ay);
            let (h2_id, _) = b.fresh_local(h_xy.clone());
            let (h1_id, _) = b.fresh_local(h_nn.clone());
            let r = b.mk_pi(h2_id, BinderInfo::Default, h_xy, goal);
            let r = b.mk_pi(h1_id, BinderInfo::Default, h_nn, r);
            let r = b.mk_pi(y_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(a_id, BinderInfo::Default, mat_mn, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.mat_mulvec_le_mono"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `NNVerify.abs_vec_le`:
    /// `{n} -> (x b : NNVec n) ->`
    /// `  (forall i, |x i| <= b i) ->`
    /// `  And (vec_le (smul (-1) b) x) (vec_le x b)`
    fn register_abs_vec_le(&mut self, c: &ElemConsts) -> Result<(), EnvError> {
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let (bv_id, bv) = b.fresh_local(vec_n.clone());
            let fin_n = c.fin_of(&n);
            let hyp = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let abs_xi = Expr::app(c.rat_abs.clone(), Expr::app(x.clone(), i.clone()));
                let bi = Expr::app(bv.clone(), i);
                let le = c.rat_le(abs_xi, bi);
                let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), le);
                ch.finish_child(r)
            };
            let neg_one = Expr::app(c.rat_neg.clone(), rat_one);
            let neg_b = Expr::app(
                Expr::app(Expr::app(c.nn_vec_smul.clone(), n.clone()), neg_one),
                bv.clone(),
            );
            let vle = c.vec_le_ref();
            let left = Expr::app(
                Expr::app(Expr::app(vle.clone(), n.clone()), neg_b),
                x.clone(),
            );
            let right = Expr::app(Expr::app(Expr::app(vle, n.clone()), x), bv);
            let goal = Expr::app(Expr::app(c.and.clone(), left), right);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, goal);
            let r = b.mk_pi(bv_id, BinderInfo::Default, vec_n.clone(), r);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.abs_vec_le"),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `NNVerify.interval_contains_vec_le`:
    /// `{n} -> (B : IntervalBounds n) -> (x : NNVec n) ->`
    /// `  contains B x -> And (vec_le B.lower x) (vec_le x B.upper)`
    fn register_interval_contains_vec_le(&mut self, c: &ElemConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let ib_n = Expr::app(c.ib.clone(), n.clone());
            let vec_n = c.vec_of(&n);
            let (bv_id, bv) = b.fresh_local(ib_n.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let contains = Expr::app(
                Expr::app(Expr::app(c.ib_contains.clone(), n.clone()), bv.clone()),
                x.clone(),
            );
            let lower = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, bv.clone());
            let upper = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, bv);
            let vle = c.vec_le_ref();
            let left = Expr::app(
                Expr::app(Expr::app(vle.clone(), n.clone()), lower),
                x.clone(),
            );
            let right = Expr::app(Expr::app(Expr::app(vle, n), x), upper);
            let goal = Expr::app(Expr::app(c.and.clone(), left), right);
            let (h_id, _) = b.fresh_local(contains.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, contains, goal);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(bv_id, BinderInfo::Default, ib_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.interval_contains_vec_le"),
            level_params: vec![],
            type_: ty,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::env::Environment;
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_elementwise()
            .expect("init_nn_verify_elementwise");
        env
    }

    #[test]
    fn test_vec_le_trans_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.vec_le_trans"))
            .is_some());
    }

    #[test]
    fn test_vec_le_add_mono_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.vec_le_add_mono"))
            .is_some());
    }

    #[test]
    fn test_vec_le_smul_nonneg_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.vec_le_smul_nonneg"))
            .is_some());
    }

    #[test]
    fn test_mat_mulvec_le_mono_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.mat_mulvec_le_mono"))
            .is_some());
    }

    #[test]
    fn test_abs_vec_le_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.abs_vec_le"))
            .is_some());
    }

    #[test]
    fn test_interval_contains_vec_le_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.interval_contains_vec_le"))
            .is_some());
    }

    #[test]
    fn test_vec_le_trans_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let e = Expr::const_(Name::from_string("NNVerify.vec_le_trans"), vec![]);
        let ty = tc.infer_type(&e).expect("infer vec_le_trans type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_vec_le_add_mono_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let e = Expr::const_(Name::from_string("NNVerify.vec_le_add_mono"), vec![]);
        let ty = tc.infer_type(&e).expect("infer vec_le_add_mono type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_vec_le_smul_nonneg_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let e = Expr::const_(Name::from_string("NNVerify.vec_le_smul_nonneg"), vec![]);
        let ty = tc.infer_type(&e).expect("infer vec_le_smul_nonneg type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_mat_mulvec_le_mono_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let e = Expr::const_(Name::from_string("NNVerify.mat_mulvec_le_mono"), vec![]);
        let ty = tc.infer_type(&e).expect("infer mat_mulvec_le_mono type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_abs_vec_le_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let e = Expr::const_(Name::from_string("NNVerify.abs_vec_le"), vec![]);
        let ty = tc.infer_type(&e).expect("infer abs_vec_le type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_interval_contains_vec_le_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let e = Expr::const_(
            Name::from_string("NNVerify.interval_contains_vec_le"),
            vec![],
        );
        let ty = tc
            .infer_type(&e)
            .expect("infer interval_contains_vec_le type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_axioms_have_no_value() {
        let env = make_env();
        for name in &[
            "NNVerify.vec_le_trans",
            "NNVerify.vec_le_add_mono",
            "NNVerify.vec_le_smul_nonneg",
            "NNVerify.mat_mulvec_le_mono",
            "NNVerify.abs_vec_le",
            "NNVerify.interval_contains_vec_le",
        ] {
            let info = env.get_const(&Name::from_string(name)).expect(name);
            assert!(
                info.value.is_none(),
                "{} should be an axiom (no value)",
                name
            );
        }
    }

    #[test]
    fn test_axiom_naming_convention() {
        let env = make_env();
        let names = [
            "NNVerify.vec_le_trans",
            "NNVerify.vec_le_add_mono",
            "NNVerify.vec_le_smul_nonneg",
            "NNVerify.mat_mulvec_le_mono",
            "NNVerify.abs_vec_le",
            "NNVerify.interval_contains_vec_le",
        ];
        for name in &names {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{} should be registered with NNVerify. prefix",
                name,
            );
        }
    }
}
