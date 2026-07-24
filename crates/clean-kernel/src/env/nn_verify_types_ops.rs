// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level Vec and Mat operations for NN verification proofs.
//!
//! Registers the vector/matrix operations needed by the NN verification
//! theorem pipeline (T80, T81, T71):
//!
//! - `NNVec.add n v w := fun i => Rat.add (v i) (w i)` (pointwise addition)
//! - `NNVec.smul n c v := fun i => Rat.mul c (v i)` (scalar multiplication)
//! - `NNVec.dot n v w := Fin.sum n (fun i => Rat.mul (v i) (w i))` (dot product)
//! - `NNMat.mulVec m n W x := fun j => Fin.sum n (fun i => Rat.mul (W j i) (x i))` (mat-vec multiply)
//!
//! Part of #3220.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared constants for NNVec/NNMat operation registration.
struct NNOpsConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    nn_vec: Expr,
    nn_mat: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    fin_sum: Expr,
}

impl NNOpsConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
        }
    }

    fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    fn mat_of(&self, m: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m.clone()), n.clone())
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    fn sum(&self, n: &Expr, f: Expr) -> Expr {
        Expr::app(Expr::app(self.fin_sum.clone(), n.clone()), f)
    }
}

impl Environment {
    /// Initialize NNVec/NNMat operations (add, smul, dot, mulVec).
    ///
    /// Depends on: `init_nn_verify_types()`, `init_rat_arith()`, `init_fin_sum()`.
    pub(crate) fn init_nn_verify_types_ops(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_types_ops_init {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_rat_arith()?;
        self.init_fin_sum()?;

        let c = NNOpsConsts::new();
        self.register_nn_vec_add(&c)?;
        self.register_nn_vec_smul(&c)?;
        self.register_nn_vec_dot(&c)?;
        self.register_nn_mat_mul_vec(&c)?;

        self.nn_verify_types_ops_init = true;
        Ok(())
    }

    /// `NNVec.add (n : Nat) (v w : NNVec n) : NNVec n := fun i => Rat.add (v i) (w i)`
    fn register_nn_vec_add(&mut self, c: &NNOpsConsts) -> Result<(), EnvError> {
        let nn_vec_add_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (v_id, _) = b.fresh_local(vec_n.clone());
            let (w_id, _) = b.fresh_local(vec_n.clone());
            let r = b.mk_pi(w_id, BinderInfo::Default, vec_n.clone(), vec_n.clone());
            let r = b.mk_pi(v_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let nn_vec_add_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (v_id, v) = b.fresh_local(vec_n.clone());
            let (w_id, w) = b.fresh_local(vec_n.clone());
            let fin_n = c.fin_of(&n);
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let vi = Expr::app(v.clone(), i.clone());
                let wi = Expr::app(w.clone(), i);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), c.add(vi, wi));
                ch.finish_child(r)
            };
            let e = b.mk_lam(w_id, BinderInfo::Default, vec_n.clone(), body);
            let e = b.mk_lam(v_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.NNVec.add"),
            level_params: vec![],
            type_: nn_vec_add_type,
            value: nn_vec_add_value,
            is_reducible: true,
        })
    }

    /// `NNVec.smul (n : Nat) (c : Rat) (v : NNVec n) : NNVec n := fun i => Rat.mul c (v i)`
    fn register_nn_vec_smul(&mut self, co: &NNOpsConsts) -> Result<(), EnvError> {
        let nn_vec_smul_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(co.nat.clone());
            let vec_n = co.vec_of(&n);
            let (c_id, _) = b.fresh_local(co.rat.clone());
            let (v_id, _) = b.fresh_local(vec_n.clone());
            let r = b.mk_pi(v_id, BinderInfo::Default, vec_n.clone(), vec_n.clone());
            let r = b.mk_pi(c_id, BinderInfo::Default, co.rat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, co.nat.clone(), r);
            b.finish(r)
        };
        let nn_vec_smul_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(co.nat.clone());
            let vec_n = co.vec_of(&n);
            let (sc_id, sc) = b.fresh_local(co.rat.clone());
            let (v_id, v) = b.fresh_local(vec_n.clone());
            let fin_n = co.fin_of(&n);
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let vi = Expr::app(v.clone(), i);
                let r = ch.mk_lam(
                    i_id,
                    BinderInfo::Default,
                    fin_n.clone(),
                    co.mul(sc.clone(), vi),
                );
                ch.finish_child(r)
            };
            let e = b.mk_lam(v_id, BinderInfo::Default, vec_n, body);
            let e = b.mk_lam(sc_id, BinderInfo::Default, co.rat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, co.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.NNVec.smul"),
            level_params: vec![],
            type_: nn_vec_smul_type,
            value: nn_vec_smul_value,
            is_reducible: true,
        })
    }

    /// `NNVec.dot (n : Nat) (v w : NNVec n) : Rat := Fin.sum n (fun i => Rat.mul (v i) (w i))`
    fn register_nn_vec_dot(&mut self, c: &NNOpsConsts) -> Result<(), EnvError> {
        let nn_vec_dot_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (v_id, _) = b.fresh_local(vec_n.clone());
            let (w_id, _) = b.fresh_local(vec_n.clone());
            let r = b.mk_pi(w_id, BinderInfo::Default, vec_n.clone(), c.rat.clone());
            let r = b.mk_pi(v_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let nn_vec_dot_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (v_id, v) = b.fresh_local(vec_n.clone());
            let (w_id, w) = b.fresh_local(vec_n.clone());
            let fin_n = c.fin_of(&n);
            let summand = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let vi = Expr::app(v.clone(), i.clone());
                let wi = Expr::app(w.clone(), i);
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), c.mul(vi, wi));
                ch.finish_child(r)
            };
            let body = c.sum(&n, summand);
            let e = b.mk_lam(w_id, BinderInfo::Default, vec_n.clone(), body);
            let e = b.mk_lam(v_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.NNVec.dot"),
            level_params: vec![],
            type_: nn_vec_dot_type,
            value: nn_vec_dot_value,
            is_reducible: true,
        })
    }

    /// `NNMat.mulVec (m n : Nat) (W : NNMat m n) (x : NNVec n) : NNVec m :=`
    /// `  fun j => Fin.sum n (fun i => Rat.mul (W j i) (x i))`
    fn register_nn_mat_mul_vec(&mut self, c: &NNOpsConsts) -> Result<(), EnvError> {
        let mul_vec_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let vec_n = c.vec_of(&n);
            let vec_m = c.vec_of(&m);
            let (w_id, _) = b.fresh_local(mat_mn.clone());
            let (x_id, _) = b.fresh_local(vec_n.clone());
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, vec_m);
            let r = b.mk_pi(w_id, BinderInfo::Default, mat_mn, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let mul_vec_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let vec_n = c.vec_of(&n);
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let fin_m = c.fin_of(&m);
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (j_id, j) = ch.fresh_local(fin_m.clone());
                let w_j = Expr::app(w.clone(), j.clone());
                let fin_n = c.fin_of(&n);
                // inner summand: fun i : Fin n => Rat.mul (W j i) (x i)
                let summand = {
                    let mut ch2 = EnvDeclBuilder::child_of(&ch);
                    let (i_id, i) = ch2.fresh_local(fin_n.clone());
                    let w_ji = Expr::app(w_j.clone(), i.clone());
                    let x_i = Expr::app(x.clone(), i);
                    let r = ch2.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), c.mul(w_ji, x_i));
                    ch2.finish_child(r)
                };
                let row_dot = c.sum(&n, summand);
                let r = ch.mk_lam(j_id, BinderInfo::Default, fin_m.clone(), row_dot);
                ch.finish_child(r)
            };
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, body);
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.NNMat.mulVec"),
            level_params: vec![],
            type_: mul_vec_type,
            value: mul_vec_value,
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
        env.init_nn_verify_types_ops()
            .expect("init_nn_verify_types_ops");
        env
    }

    #[test]
    fn test_nn_vec_add_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.NNVec.add"))
            .is_some());
    }

    #[test]
    fn test_nn_vec_smul_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.NNVec.smul"))
            .is_some());
    }

    #[test]
    fn test_nn_vec_dot_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.NNVec.dot"))
            .is_some());
    }

    #[test]
    fn test_nn_mat_mul_vec_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.NNMat.mulVec"))
            .is_some());
    }

    #[test]
    fn test_nn_vec_add_type_checks() {
        let env = make_env();
        let nn_vec_add = Expr::const_(Name::from_string("NNVerify.NNVec.add"), vec![]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc.infer_type(&nn_vec_add).expect("infer NNVec.add type");
        // NNVec.add : {n : Nat} -> NNVec n -> NNVec n -> NNVec n
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_nn_vec_smul_type_checks() {
        let env = make_env();
        let nn_vec_smul = Expr::const_(Name::from_string("NNVerify.NNVec.smul"), vec![]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc.infer_type(&nn_vec_smul).expect("infer NNVec.smul type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_nn_vec_dot_type_checks() {
        let env = make_env();
        let nn_vec_dot = Expr::const_(Name::from_string("NNVerify.NNVec.dot"), vec![]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc.infer_type(&nn_vec_dot).expect("infer NNVec.dot type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_nn_mat_mul_vec_type_checks() {
        let env = make_env();
        let mul_vec = Expr::const_(Name::from_string("NNVerify.NNMat.mulVec"), vec![]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc.infer_type(&mul_vec).expect("infer NNMat.mulVec type");
        // NNMat.mulVec : {m n : Nat} -> NNMat m n -> NNVec n -> NNVec m
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_types_ops().expect("first init");
        env.init_nn_verify_types_ops().expect("second init");
    }
}
