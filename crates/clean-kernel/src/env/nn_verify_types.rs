// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level definitions for NN verification formal proofs.
//!
//! Registers the foundational types needed to state and prove
//! NN verification theorems (T01-T84, T70-T72) in the kernel:
//!
//! - `NNVec n := Fin n -> Rat` (vector of rationals)
//! - `NNMat m n := Fin m -> Fin n -> Rat` (matrix of rationals)
//! - `IntervalBounds d` (structure with lower, upper, valid)
//! - `IntervalBounds.contains` (containment predicate)
//! - `IntervalBounds.subset` (subset relation)
//!
//! Part of #3220.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across all NN verify type definitions.
struct NNConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    type0: Expr,
    prop: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    and: Expr,
    nn_vec: Expr,
    ib: Expr,
}

impl NNConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
        }
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
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
}

impl Environment {
    /// Initialize NN verification formal types (NNVec, NNMat, IntervalBounds).
    ///
    /// Depends on: `init_rat()`, `init_fin()`, `init_rat_ord()`, `init_and()`.
    pub fn init_nn_verify_types(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_types_init {
            return Ok(());
        }
        self.init_rat()?;
        self.init_fin()?;
        self.init_rat_ord()?;
        self.init_and()?;

        let c = NNConsts::new();
        self.register_nn_vec(&c)?;
        self.register_nn_mat(&c)?;
        self.register_interval_bounds(&c)?;
        self.register_interval_contains(&c)?;
        self.register_interval_subset(&c)?;

        self.nn_verify_types_init = true;
        Ok(())
    }

    /// `NNVec (n : Nat) : Type := Fin n -> Rat`
    fn register_nn_vec(&mut self, c: &NNConsts) -> Result<(), EnvError> {
        let nn_vec_type = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
        let nn_vec_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fin_n = Expr::app(c.fin.clone(), n);
            let body = Expr::pi(BinderInfo::Default, fin_n, c.rat.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.NNVec"),
            level_params: vec![],
            type_: nn_vec_type,
            value: nn_vec_value,
            is_reducible: true,
        })
    }

    /// `NNMat (m n : Nat) : Type := Fin m -> Fin n -> Rat`
    fn register_nn_mat(&mut self, c: &NNConsts) -> Result<(), EnvError> {
        let nn_mat_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(c.nat.clone());
            let (n_id, _n) = b.fresh_local(c.nat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), c.type0.clone());
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let nn_mat_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fin_n = Expr::app(c.fin.clone(), n);
            let fin_m = Expr::app(c.fin.clone(), m);
            let inner = Expr::pi(BinderInfo::Default, fin_n, c.rat.clone());
            let body = Expr::pi(BinderInfo::Default, fin_m, inner);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.NNMat"),
            level_params: vec![],
            type_: nn_mat_type,
            value: nn_mat_value,
            is_reducible: true,
        })
    }

    /// `IntervalBounds d` structure with lower, upper, valid fields.
    fn register_interval_bounds(&mut self, c: &NNConsts) -> Result<(), EnvError> {
        let ib_type = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
        let ib_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let nn_vec_d = Expr::app(c.nn_vec.clone(), d.clone());
            let (lower_id, lower) = b.fresh_local(nn_vec_d.clone());
            let (upper_id, upper) = b.fresh_local(nn_vec_d.clone());
            let fin_d = Expr::app(c.fin.clone(), d.clone());
            let valid_body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let le_expr = c.rat_le(
                    Expr::app(lower.clone(), i.clone()),
                    Expr::app(upper.clone(), i),
                );
                let r = ch.mk_pi(i_id, BinderInfo::Default, fin_d.clone(), le_expr);
                ch.finish_child(r)
            };
            let (valid_id, _) = b.fresh_local(valid_body.clone());
            let result = Expr::app(c.ib.clone(), d.clone());
            let r = b.mk_pi(valid_id, BinderInfo::Default, valid_body, result);
            let r = b.mk_pi(upper_id, BinderInfo::Default, nn_vec_d.clone(), r);
            let r = b.mk_pi(lower_id, BinderInfo::Default, nn_vec_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };

        use crate::inductive::{Constructor, InductiveDecl, InductiveType};
        self.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("NNVerify.IntervalBounds"),
                type_: ib_type,
                constructors: vec![Constructor {
                    name: Name::from_string("NNVerify.IntervalBounds.mk"),
                    type_: ib_mk_type,
                }],
            }],
        })?;
        self.register_structure_fields(
            Name::from_string("NNVerify.IntervalBounds"),
            vec![
                Name::from_string("lower"),
                Name::from_string("upper"),
                Name::from_string("valid"),
            ],
        )
    }

    /// `IntervalBounds.contains B x := forall i, B.lower i <= x i /\ x i <= B.upper i`
    fn register_interval_contains(&mut self, c: &NNConsts) -> Result<(), EnvError> {
        let contains_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = Expr::app(c.ib.clone(), d.clone());
            let vec_d = Expr::app(c.nn_vec.clone(), d.clone());
            let (ib_id, _) = b.fresh_local(ib_d.clone());
            let (x_id, _) = b.fresh_local(vec_d.clone());
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_d, c.prop.clone());
            let r = b.mk_pi(ib_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let contains_value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = Expr::app(c.ib.clone(), d.clone());
            let vec_d = Expr::app(c.nn_vec.clone(), d.clone());
            let (ib_id, ib) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let lower = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, ib.clone());
            let upper = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, ib.clone());
            let fin_d = Expr::app(c.fin.clone(), d.clone());
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let x_i = Expr::app(x.clone(), i.clone());
                let conj = Expr::app(
                    Expr::app(
                        c.and.clone(),
                        c.rat_le(Expr::app(lower.clone(), i.clone()), x_i.clone()),
                    ),
                    c.rat_le(x_i, Expr::app(upper.clone(), i)),
                );
                let r = ch.mk_pi(i_id, BinderInfo::Default, fin_d.clone(), conj);
                ch.finish_child(r)
            };
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_d.clone(), body);
            let e = b.mk_lam(ib_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.IntervalBounds.contains"),
            level_params: vec![],
            type_: contains_type,
            value: contains_value,
            is_reducible: true,
        })
    }

    /// `IntervalBounds.subset B1 B2 := forall i, B2.lower i <= B1.lower i /\ B1.upper i <= B2.upper i`
    fn register_interval_subset(&mut self, c: &NNConsts) -> Result<(), EnvError> {
        let subset_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = Expr::app(c.ib.clone(), d.clone());
            let (b1_id, _) = b.fresh_local(ib_d.clone());
            let (b2_id, _) = b.fresh_local(ib_d.clone());
            let r = b.mk_pi(b2_id, BinderInfo::Default, ib_d.clone(), c.prop.clone());
            let r = b.mk_pi(b1_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let subset_value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = Expr::app(c.ib.clone(), d.clone());
            let (b1_id, b1) = b.fresh_local(ib_d.clone());
            let (b2_id, b2) = b.fresh_local(ib_d.clone());
            let b1_lo = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, b1.clone());
            let b1_hi = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, b1.clone());
            let b2_lo = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, b2.clone());
            let b2_hi = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, b2.clone());
            let fin_d = Expr::app(c.fin.clone(), d.clone());
            let body = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let conj = Expr::app(
                    Expr::app(
                        c.and.clone(),
                        c.rat_le(
                            Expr::app(b2_lo.clone(), i.clone()),
                            Expr::app(b1_lo.clone(), i.clone()),
                        ),
                    ),
                    c.rat_le(
                        Expr::app(b1_hi.clone(), i.clone()),
                        Expr::app(b2_hi.clone(), i),
                    ),
                );
                let r = ch.mk_pi(i_id, BinderInfo::Default, fin_d.clone(), conj);
                ch.finish_child(r)
            };
            let e = b.mk_lam(b2_id, BinderInfo::Default, ib_d.clone(), body);
            let e = b.mk_lam(b1_id, BinderInfo::Default, ib_d.clone(), e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.IntervalBounds.subset"),
            level_params: vec![],
            type_: subset_type,
            value: subset_value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_types().expect("init_nn_verify_types");
        env
    }

    #[test]
    fn test_nn_vec_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.NNVec"))
            .is_some());
    }

    #[test]
    fn test_nn_mat_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.NNMat"))
            .is_some());
    }

    #[test]
    fn test_interval_bounds_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.IntervalBounds"))
            .is_some());
        assert!(env
            .get_const(&Name::from_string("NNVerify.IntervalBounds.mk"))
            .is_some());
    }

    #[test]
    fn test_contains_and_subset_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.IntervalBounds.contains"))
            .is_some());
        assert!(env
            .get_const(&Name::from_string("NNVerify.IntervalBounds.subset"))
            .is_some());
    }

    #[test]
    fn test_nn_vec_type_checks() {
        let env = make_env();
        let nn_vec = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc.infer_type(&nn_vec).expect("infer NNVerify.NNVec type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_nn_mat_type_checks() {
        let env = make_env();
        let nn_mat = Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]);
        let tc = TypeChecker::with_mode(&env, env.mode());
        let ty = tc.infer_type(&nn_mat).expect("infer NNVerify.NNMat type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_types().expect("first init");
        env.init_nn_verify_types().expect("second init");
    }

    /// Verify all NN-specific types use the `NNVerify.` prefix.
    ///
    /// Part of #3206: naming consolidation for parallel worktree outputs.
    #[test]
    fn test_nn_verify_naming_convention() {
        let env = make_env();
        let nn_names = [
            "NNVerify.NNVec",
            "NNVerify.NNMat",
            "NNVerify.IntervalBounds",
            "NNVerify.IntervalBounds.mk",
            "NNVerify.IntervalBounds.contains",
            "NNVerify.IntervalBounds.subset",
        ];
        for name in &nn_names {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{} should be registered with NNVerify. prefix",
                name,
            );
        }
        // Verify old bare names are NOT registered
        let old_names = ["NNVec", "NNMat", "IntervalBounds"];
        for name in &old_names {
            assert!(
                env.get_const(&Name::from_string(name)).is_none(),
                "{} should NOT be registered (use NNVerify. prefix instead)",
                name,
            );
        }
    }
}
