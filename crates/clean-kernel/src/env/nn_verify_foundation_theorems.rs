// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Foundation theorems for NN verification (T01, T02, T04, T05).
//!
//! Registers the zonotope/interval soundness theorems that connect
//! zonotope, interval, and linear-transform abstractions.
//!
//! ## Theorems
//!
//! - **T01** `interval_hull_sound`: zonotope interval hull preserves containment
//! - **T02** `linear_transform_exact`: linear map preserves zonotope containment
//! - **T04** `interval_subset_width`: width monotonicity under subset
//! - **T05** `triangle_inequality`: l1 norm triangle inequality
//!
//! Also registers `linear_transform_zonotope` (supporting definition).
//! All axioms -- proof terms require real analysis beyond kernel scope.
//! Part of #3151.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for foundation theorem construction.
pub(super) struct FTConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) prop: Expr,
    pub(super) nn_vec: Expr,
    pub(super) nn_mat: Expr,
    pub(super) ib: Expr,
    pub(super) ib_contains: Expr,
    pub(super) ib_subset: Expr,
    pub(super) ib_width: Expr,
    pub(super) zonotope: Expr,
    pub(super) zono_contains: Expr,
    pub(super) zono_to_ibp: Expr,
    pub(super) zono_minkowski_add: Expr,
    pub(super) nn_vec_add: Expr,
    pub(super) nn_vec_dot: Expr,
    pub(super) nn_vec_l1_norm: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) rat_add: Expr,
    pub(super) fin: Expr,
    pub(super) linear_output: Expr,
}

impl FTConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
            ib_subset: Expr::const_(Name::from_string("NNVerify.IntervalBounds.subset"), vec![]),
            ib_width: Expr::const_(Name::from_string("NNVerify.IntervalBounds.width"), vec![]),
            zonotope: Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]),
            zono_contains: Expr::const_(Name::from_string("NNVerify.Zonotope.contains"), vec![]),
            zono_to_ibp: Expr::const_(Name::from_string("NNVerify.Zonotope.to_ibp"), vec![]),
            zono_minkowski_add: Expr::const_(
                Name::from_string("NNVerify.Zonotope.minkowski_add"),
                vec![],
            ),
            nn_vec_add: Expr::const_(Name::from_string("NNVerify.NNVec.add"), vec![]),
            nn_vec_dot: Expr::const_(Name::from_string("NNVerify.NNVec.dot"), vec![]),
            nn_vec_l1_norm: Expr::const_(Name::from_string("NNVerify.NNVec.l1_norm"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            linear_output: Expr::const_(Name::from_string("NNVerify.linear_output"), vec![]),
        }
    }

    pub(super) fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    pub(super) fn mat_of(&self, m: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m.clone()), n.clone())
    }

    pub(super) fn ib_of(&self, d: &Expr) -> Expr {
        Expr::app(self.ib.clone(), d.clone())
    }

    pub(super) fn zono_of(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::app(Expr::app(self.zonotope.clone(), n.clone()), k.clone())
    }

    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    pub(super) fn zono_contains(&self, n: &Expr, k: &Expr, z: &Expr, x: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(self.zono_contains.clone(), n.clone()), k.clone()),
                z.clone(),
            ),
            x.clone(),
        )
    }

    pub(super) fn ib_contains_app(&self, d: &Expr, b: &Expr, x: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_contains.clone(), d.clone()), b.clone()),
            x.clone(),
        )
    }

    pub(super) fn ib_subset_app(&self, d: &Expr, b1: &Expr, b2: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_subset.clone(), d.clone()), b1.clone()),
            b2.clone(),
        )
    }

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

    pub(super) fn add_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    pub(super) fn vec_add(&self, n: &Expr, v: &Expr, w: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.nn_vec_add.clone(), n.clone()), v.clone()),
            w.clone(),
        )
    }

    pub(super) fn l1_norm(&self, n: &Expr, v: &Expr) -> Expr {
        Expr::app(Expr::app(self.nn_vec_l1_norm.clone(), n.clone()), v.clone())
    }

    pub(super) fn ib_width(&self, d: &Expr, b: &Expr) -> Expr {
        Expr::app(Expr::app(self.ib_width.clone(), d.clone()), b.clone())
    }

    pub(super) fn zono_to_ibp_app(&self, n: &Expr, k: &Expr, z: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.zono_to_ibp.clone(), n.clone()), k.clone()),
            z.clone(),
        )
    }

    pub(super) fn linear_output_app(
        &self,
        m: &Expr,
        n: &Expr,
        w: &Expr,
        b: &Expr,
        x: &Expr,
    ) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(self.linear_output.clone(), m.clone()), n.clone()),
                    w.clone(),
                ),
                b.clone(),
            ),
            x.clone(),
        )
    }
}

impl Environment {
    /// Initialize foundation theorems (T01, T02, T04, T05, T08, T09).
    ///
    /// Depends on: `init_nn_verify_foundation_types()`,
    ///             `init_nn_verify_zonotope()`,
    ///             `init_nn_verify_ibp_linear()`.
    pub fn init_nn_verify_foundation_theorems(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_foundation_theorems_init {
            return Ok(());
        }
        self.init_nn_verify_shared_bootstrap()?;
        self.init_nn_verify_foundation_types()?;
        self.init_nn_verify_ibp_linear()?;

        let c = FTConsts::new();
        self.register_interval_hull_sound(&c)?;
        self.register_linear_transform_zonotope(&c)?;
        self.register_linear_transform_exact(&c)?;
        self.register_interval_subset_width(&c)?;
        self.register_triangle_inequality(&c)?;
        // T08, T09 + supporting defs registered in foundation_theorems_farkas
        self.register_minkowski_add_sound(&c)?;
        self.register_farkas_certificate_valid(&c)?;
        self.register_farkas_to_interval(&c)?;

        self.nn_verify_foundation_theorems_init = true;
        Ok(())
    }

    /// T01: `interval_hull_sound`
    fn register_interval_hull_sound(&mut self, c: &FTConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.interval_hull_sound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains(&n, &k, &z, &x);
            let to_ibp = c.zono_to_ibp_app(&n, &k, &z);
            let concl = c.ib_contains_app(&n, &to_ibp, &x);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(k_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// Supporting definition: `linear_transform_zonotope`
    fn register_linear_transform_zonotope(&mut self, c: &FTConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.linear_transform_zonotope");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let vec_m = c.vec_of(&m);
            let zono_nk = c.zono_of(&n, &k);
            let zono_mk = c.zono_of(&m, &k);
            let (w_id, _) = b.fresh_local(mat_mn.clone());
            let (bias_id, _) = b.fresh_local(vec_m.clone());
            let (z_id, _) = b.fresh_local(zono_nk.clone());
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, zono_mk);
            let r = b.mk_pi(bias_id, BinderInfo::Default, vec_m, r);
            let r = b.mk_pi(w_id, BinderInfo::Default, mat_mn, r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// T02: `linear_transform_exact`
    fn register_linear_transform_exact(&mut self, c: &FTConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.linear_transform_exact");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let lt_zono = Expr::const_(
            Name::from_string("NNVerify.linear_transform_zonotope"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let mat_mn = c.mat_of(&m, &n);
            let vec_m = c.vec_of(&m);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let (bias_id, bias) = b.fresh_local(vec_m.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains(&n, &k, &z, &x);
            let transformed = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(Expr::app(lt_zono, m.clone()), n.clone()),
                            k.clone(),
                        ),
                        w.clone(),
                    ),
                    bias.clone(),
                ),
                z.clone(),
            );
            let output = c.linear_output_app(&m, &n, &w, &bias, &x);
            let concl = c.zono_contains(&m, &k, &transformed, &output);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(bias_id, BinderInfo::Default, vec_m, r);
            let r = b.mk_pi(w_id, BinderInfo::Default, mat_mn, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(k_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// T04: `interval_subset_width`
    fn register_interval_subset_width(&mut self, c: &FTConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.interval_subset_width");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = c.ib_of(&d);
            let (b1_id, b1) = b.fresh_local(ib_d.clone());
            let (b2_id, b2) = b.fresh_local(ib_d.clone());
            let hyp = c.ib_subset_app(&d, &b1, &b2);
            let fin_d = c.fin_of(&d);
            let w1 = c.ib_width(&d, &b1);
            let w2 = c.ib_width(&d, &b2);
            let inner = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_d.clone());
                let w1_i = Expr::app(w1.clone(), i.clone());
                let w2_i = Expr::app(w2.clone(), i);
                let le = c.rat_le(w1_i, w2_i);
                let r = ch.mk_pi(i_id, BinderInfo::Default, fin_d.clone(), le);
                ch.finish_child(r)
            };
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, inner);
            let r = b.mk_pi(b2_id, BinderInfo::Default, ib_d.clone(), r);
            let r = b.mk_pi(b1_id, BinderInfo::Default, ib_d, r);
            let r = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// T05: `triangle_inequality`
    fn register_triangle_inequality(&mut self, c: &FTConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.triangle_inequality");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let vec_n = c.vec_of(&n);
            let (v_id, v) = b.fresh_local(vec_n.clone());
            let (w_id, w) = b.fresh_local(vec_n.clone());
            let sum = c.vec_add(&n, &v, &w);
            let lhs = c.l1_norm(&n, &sum);
            let rhs = c.add_rat(c.l1_norm(&n, &v), c.l1_norm(&n, &w));
            let concl = c.rat_le(lhs, rhs);
            let r = b.mk_pi(w_id, BinderInfo::Default, vec_n.clone(), concl);
            let r = b.mk_pi(v_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
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

    fn check(env: &Environment, name: &str, expected: ConstantKind) {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} missing"
        );
        let expr = Expr::const_(Name::from_string(name), vec![]);
        let tc = TypeChecker::with_mode(env, env.mode());
        let ty = tc
            .infer_type(&expr)
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        assert!(matches!(ty.kind(), ExprKind::Pi(..)), "{name} not Pi");
        let info = env.get_const(&Name::from_string(name)).unwrap();
        assert_eq!(info.kind, expected, "{name} kind mismatch");
    }

    #[test]
    fn test_zonotope_interval_theorems() {
        let env = make_env();
        let axioms = [
            "NNVerify.interval_hull_sound",
            "NNVerify.linear_transform_zonotope",
            "NNVerify.linear_transform_exact",
            "NNVerify.interval_subset_width",
            "NNVerify.triangle_inequality",
        ];
        for name in &axioms {
            check(&env, name, ConstantKind::Axiom);
        }
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_foundation_theorems().expect("first");
        env.init_nn_verify_foundation_theorems().expect("second");
    }
}
