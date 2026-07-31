// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Element-wise matrix/vector inequality definitions for linarith.
//!
//! Registers the element-wise comparison operations needed by NN
//! verification proofs to express component-wise bounds through
//! the linarith tactic.
//!
//! ## Definitions
//!
//! - `NNVerify.vec_le n a b := forall i : Fin n, LE.le (a i) (b i)`
//! - `NNVerify.mat_le m n A B := forall i j, LE.le (A i j) (B i j)`
//! - `NNVerify.vec_nonneg n a := forall i : Fin n, LE.le Rat.zero (a i)`
//! - `NNVerify.mat_nonneg m n A := forall i j, LE.le Rat.zero (A i j)`
//!
//! Axioms are in `nn_verify_elementwise_axioms.rs`.
//!
//! Part of #3181.

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Shared constants for element-wise inequality definitions and axioms.
#[cfg(test)]
pub(super) struct ElemConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) fin: Expr,
    pub(super) nn_vec: Expr,
    pub(super) nn_mat: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) rat_zero: Expr,
    pub(super) rat_neg: Expr,
    pub(super) rat_abs: Expr,
    pub(super) and: Expr,
    pub(super) prop: Expr,
    pub(super) ib: Expr,
    pub(super) ib_contains: Expr,
    pub(super) nn_vec_add: Expr,
    pub(super) nn_vec_smul: Expr,
    pub(super) nn_mat_mulvec: Expr,
}

#[cfg(test)]
impl ElemConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_neg: Expr::const_(Name::from_string("Rat.neg"), vec![]),
            rat_abs: Expr::const_(Name::from_string("Rat.abs"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            prop: Expr::prop(),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
            nn_vec_add: Expr::const_(Name::from_string("NNVerify.NNVec.add"), vec![]),
            nn_vec_smul: Expr::const_(Name::from_string("NNVerify.NNVec.smul"), vec![]),
            nn_mat_mulvec: Expr::const_(Name::from_string("NNVerify.NNMat.mulVec"), vec![]),
        }
    }

    /// `LE.le @Rat instLERat lhs rhs`
    #[cfg(test)]
    pub(super) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.rat.clone()),
                    self.inst_le_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    #[cfg(test)]
    pub(super) fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    #[cfg(test)]
    pub(super) fn mat_of(&self, m: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m.clone()), n.clone())
    }

    #[cfg(test)]
    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    #[cfg(test)]
    pub(super) fn vec_le_ref(&self) -> Expr {
        Expr::const_(Name::from_string("NNVerify.vec_le"), vec![])
    }

    #[cfg(test)]
    pub(super) fn mat_nonneg_ref(&self) -> Expr {
        Expr::const_(Name::from_string("NNVerify.mat_nonneg"), vec![])
    }
}

#[cfg(test)]
impl Environment {
    /// Initialize element-wise inequality operations and axioms.
    ///
    /// Depends on: `init_nn_verify_types_ops()`, `init_rat_abs()`,
    ///             `init_rat_ord()`, `init_and()`.
    #[cfg(test)]
    pub(crate) fn init_nn_verify_elementwise(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_elementwise_init {
            return Ok(());
        }
        self.init_nn_verify_types_ops()?;
        self.init_rat_abs()?;
        self.init_rat_ord()?;
        self.init_and()?;

        let c = ElemConsts::new();

        // Definitions
        self.register_vec_le(&c)?;
        self.register_mat_le(&c)?;
        self.register_vec_nonneg(&c)?;
        self.register_mat_nonneg(&c)?;

        // Axioms (in nn_verify_elementwise_axioms.rs)
        self.register_elementwise_axioms(&c)?;

        self.nn_verify_elementwise_init = true;
        Ok(())
    }

    /// `NNVerify.vec_le (n : Nat) (a b : NNVec n) : Prop :=`
    /// `  forall i : Fin n, LE.le @Rat instLERat (a i) (b i)`
    #[cfg(test)]
    fn register_vec_le(&mut self, c: &ElemConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (a_id, _) = b.fresh_local(vec_n.clone());
            let (bv_id, _) = b.fresh_local(vec_n.clone());
            let r = b.mk_pi(bv_id, BinderInfo::Default, vec_n.clone(), c.prop.clone());
            let r = b.mk_pi(a_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (a_id, a) = b.fresh_local(vec_n.clone());
            let (bv_id, bv) = b.fresh_local(vec_n.clone());
            let fin_n = c.fin_of(&n);
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let le = c.rat_le(Expr::app(a.clone(), i.clone()), Expr::app(bv.clone(), i));
                let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), le);
                ch.finish_child(r)
            };
            let e = b.mk_lam(bv_id, BinderInfo::Default, vec_n.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.vec_le"),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    /// `NNVerify.mat_le (m n : Nat) (A B : NNMat m n) : Prop :=`
    /// `  forall (i : Fin m) (j : Fin n), LE.le (A i j) (B i j)`
    #[cfg(test)]
    fn register_mat_le(&mut self, c: &ElemConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let (a_id, _) = b.fresh_local(mat_mn.clone());
            let (bv_id, _) = b.fresh_local(mat_mn.clone());
            let r = b.mk_pi(bv_id, BinderInfo::Default, mat_mn.clone(), c.prop.clone());
            let r = b.mk_pi(a_id, BinderInfo::Default, mat_mn, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let (a_id, a) = b.fresh_local(mat_mn.clone());
            let (bv_id, bv) = b.fresh_local(mat_mn.clone());
            let fin_m = c.fin_of(&m);
            let fin_n = c.fin_of(&n);
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_m.clone());
                let inner = {
                    let mut ch2 = EnvDeclBuilder::child_of(&ch);
                    let (j_id, j) = ch2.fresh_local(fin_n.clone());
                    let a_ij = Expr::app(Expr::app(a.clone(), i.clone()), j.clone());
                    let b_ij = Expr::app(Expr::app(bv.clone(), i.clone()), j);
                    let le = c.rat_le(a_ij, b_ij);
                    let r = ch2.mk_pi(j_id, BinderInfo::Default, fin_n.clone(), le);
                    ch2.finish_child(r)
                };
                let r = ch.mk_pi(i_id, BinderInfo::Default, fin_m.clone(), inner);
                ch.finish_child(r)
            };
            let e = b.mk_lam(bv_id, BinderInfo::Default, mat_mn.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.mat_le"),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    /// `NNVerify.vec_nonneg (n : Nat) (a : NNVec n) : Prop :=`
    /// `  forall i : Fin n, LE.le Rat.zero (a i)`
    #[cfg(test)]
    fn register_vec_nonneg(&mut self, c: &ElemConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (a_id, _) = b.fresh_local(vec_n.clone());
            let r = b.mk_pi(a_id, BinderInfo::Default, vec_n, c.prop.clone());
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (a_id, a) = b.fresh_local(vec_n.clone());
            let fin_n = c.fin_of(&n);
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let le = c.rat_le(c.rat_zero.clone(), Expr::app(a.clone(), i));
                let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), le);
                ch.finish_child(r)
            };
            let e = b.mk_lam(a_id, BinderInfo::Default, vec_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.vec_nonneg"),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    /// `NNVerify.mat_nonneg (m n : Nat) (A : NNMat m n) : Prop :=`
    /// `  forall (i : Fin m) (j : Fin n), LE.le Rat.zero (A i j)`
    #[cfg(test)]
    fn register_mat_nonneg(&mut self, c: &ElemConsts) -> Result<(), EnvError> {
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let (a_id, _) = b.fresh_local(mat_mn.clone());
            let r = b.mk_pi(a_id, BinderInfo::Default, mat_mn, c.prop.clone());
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let (a_id, a) = b.fresh_local(mat_mn.clone());
            let fin_m = c.fin_of(&m);
            let fin_n = c.fin_of(&n);
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_m.clone());
                let inner = {
                    let mut ch2 = EnvDeclBuilder::child_of(&ch);
                    let (j_id, j) = ch2.fresh_local(fin_n.clone());
                    let a_ij = Expr::app(Expr::app(a.clone(), i.clone()), j);
                    let le = c.rat_le(c.rat_zero.clone(), a_ij);
                    let r = ch2.mk_pi(j_id, BinderInfo::Default, fin_n.clone(), le);
                    ch2.finish_child(r)
                };
                let r = ch.mk_pi(i_id, BinderInfo::Default, fin_m.clone(), inner);
                ch.finish_child(r)
            };
            let e = b.mk_lam(a_id, BinderInfo::Default, mat_mn, body);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.mat_nonneg"),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
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
    fn test_vec_le_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.vec_le"))
            .is_some());
    }

    #[test]
    fn test_mat_le_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.mat_le"))
            .is_some());
    }

    #[test]
    fn test_vec_nonneg_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.vec_nonneg"))
            .is_some());
    }

    #[test]
    fn test_mat_nonneg_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.mat_nonneg"))
            .is_some());
    }

    #[test]
    fn test_vec_le_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let e = Expr::const_(Name::from_string("NNVerify.vec_le"), vec![]);
        let ty = tc.infer_type(&e).expect("infer vec_le type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_mat_le_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let e = Expr::const_(Name::from_string("NNVerify.mat_le"), vec![]);
        let ty = tc.infer_type(&e).expect("infer mat_le type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_vec_nonneg_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let e = Expr::const_(Name::from_string("NNVerify.vec_nonneg"), vec![]);
        let ty = tc.infer_type(&e).expect("infer vec_nonneg type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_mat_nonneg_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let e = Expr::const_(Name::from_string("NNVerify.mat_nonneg"), vec![]);
        let ty = tc.infer_type(&e).expect("infer mat_nonneg type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_definitions_are_reducible() {
        let env = make_env();
        for name in &[
            "NNVerify.vec_le",
            "NNVerify.mat_le",
            "NNVerify.vec_nonneg",
            "NNVerify.mat_nonneg",
        ] {
            let info = env.get_const(&Name::from_string(name)).expect(name);
            assert!(
                info.value.is_some(),
                "{} should have a definition value",
                name
            );
        }
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_elementwise().expect("first init");
        env.init_nn_verify_elementwise().expect("second init");
    }

    #[test]
    fn test_nn_verify_naming_convention() {
        let env = make_env();
        let names = [
            "NNVerify.vec_le",
            "NNVerify.mat_le",
            "NNVerify.vec_nonneg",
            "NNVerify.mat_nonneg",
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
