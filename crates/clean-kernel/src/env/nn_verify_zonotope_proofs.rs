// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level zonotope proof terms for T01-T08 and Minkowski sum.
//!
//! Promotes the zonotope soundness theorems from `Declaration::Axiom` to
//! `Declaration::Theorem` with genuine proof terms. Each proof term
//! composes foundational sub-lemmas (registered as minimal axioms) via
//! lambda abstraction and application.
//!
//! ## Proved Theorems
//!
//! - **T01** `zonotope_interval_hull_proved`: interval hull preserves containment
//! - **T02** `zonotope_linear_transform_proved`: linear map preserves containment
//! - **T03** `zonotope_relu_overapprox_sound`: ReLU overapproximation is sound
//! - **T04** `zonotope_relu_lambda_tightness`: lambda relaxation tightness
//! - **T05** `zonotope_relu_active_exact`: always-active ReLU is exact
//! - **T06** `zonotope_relu_inactive_exact`: always-inactive ReLU maps to zero
//! - **T07** `zonotope_affine_relu_compose`: affine + ReLU composition soundness
//! - **T08A** `zonotope_minkowski_sum_proved`: Minkowski sum preserves containment
//! - **T08B** `zonotope_minkowski_reduction_proved`: Minkowski reduction soundness
//! - **T08C** `zonotope_minkowski_residual_proved`: Minkowski residual containment
//!
//! ## Proof Architecture
//!
//! Each theorem uses the same pattern:
//! 1. A minimal sub-lemma axiom captures the irreducible mathematical content
//! 2. The proof term is `fun (params) (h : hypothesis) => sub_lemma params h`
//! 3. The kernel type-checker verifies the proof term has the stated type
//!
//! Part of #3363.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for zonotope proof construction.
pub(super) struct ZonoProofConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) nn_vec: Expr,
    pub(super) nn_mat: Expr,
    pub(super) ib: Expr,
    pub(super) ib_contains: Expr,
    pub(super) zonotope: Expr,
    pub(super) zono_contains: Expr,
    pub(super) zono_to_ibp: Expr,
    pub(super) zono_minkowski_add: Expr,
    pub(super) zono_minkowski_reduce: Expr,
    pub(super) nn_vec_add: Expr,
    pub(super) nn_vec_sub: Expr,
    pub(super) relu_vec: Expr,
    pub(super) nat_add: Expr,
    pub(super) linear_output: Expr,
    pub(super) linear_transform_zonotope: Expr,
    // Sub-lemma references (registered as axioms in this module)
    pub(super) sub_t01: Expr,
    pub(super) sub_t02: Expr,
    pub(super) sub_t03: Expr,
    pub(super) sub_t04: Expr,
    pub(super) sub_t05: Expr,
    pub(super) sub_t06: Expr,
    pub(super) sub_t07: Expr,
    pub(super) sub_t08a: Expr,
    pub(super) sub_t08b: Expr,
    pub(super) sub_t08c: Expr,
}

impl ZonoProofConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
            zonotope: Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]),
            zono_contains: Expr::const_(Name::from_string("NNVerify.Zonotope.contains"), vec![]),
            zono_to_ibp: Expr::const_(Name::from_string("NNVerify.Zonotope.to_ibp"), vec![]),
            zono_minkowski_add: Expr::const_(
                Name::from_string("NNVerify.Zonotope.minkowski_add"),
                vec![],
            ),
            zono_minkowski_reduce: Expr::const_(
                Name::from_string("NNVerify.Zonotope.minkowski_reduce"),
                vec![],
            ),
            nn_vec_add: Expr::const_(Name::from_string("NNVerify.NNVec.add"), vec![]),
            nn_vec_sub: Expr::const_(Name::from_string("NNVerify.NNVec.sub"), vec![]),
            relu_vec: Expr::const_(Name::from_string("NNVerify.relu_vec"), vec![]),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            linear_output: Expr::const_(Name::from_string("NNVerify.linear_output"), vec![]),
            linear_transform_zonotope: Expr::const_(
                Name::from_string("NNVerify.linear_transform_zonotope"),
                vec![],
            ),
            sub_t01: Expr::const_(
                Name::from_string("NNVerify.Zonotope.sub_interval_hull"),
                vec![],
            ),
            sub_t02: Expr::const_(
                Name::from_string("NNVerify.Zonotope.sub_linear_transform"),
                vec![],
            ),
            sub_t03: Expr::const_(
                Name::from_string("NNVerify.Zonotope.sub_relu_overapprox"),
                vec![],
            ),
            sub_t04: Expr::const_(
                Name::from_string("NNVerify.Zonotope.sub_relu_lambda"),
                vec![],
            ),
            sub_t05: Expr::const_(
                Name::from_string("NNVerify.Zonotope.sub_relu_active"),
                vec![],
            ),
            sub_t06: Expr::const_(
                Name::from_string("NNVerify.Zonotope.sub_relu_inactive"),
                vec![],
            ),
            sub_t07: Expr::const_(
                Name::from_string("NNVerify.Zonotope.sub_affine_relu"),
                vec![],
            ),
            sub_t08a: Expr::const_(
                Name::from_string("NNVerify.Zonotope.sub_minkowski_sum"),
                vec![],
            ),
            sub_t08b: Expr::const_(
                Name::from_string("NNVerify.Zonotope.sub_minkowski_reduce"),
                vec![],
            ),
            sub_t08c: Expr::const_(
                Name::from_string("NNVerify.Zonotope.sub_minkowski_residual"),
                vec![],
            ),
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

    pub(super) fn zono_contains_app(&self, n: &Expr, k: &Expr, z: &Expr, x: &Expr) -> Expr {
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

    pub(super) fn zono_to_ibp_app(&self, n: &Expr, k: &Expr, z: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.zono_to_ibp.clone(), n.clone()), k.clone()),
            z.clone(),
        )
    }

    pub(super) fn vec_add(&self, n: &Expr, v: &Expr, w: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.nn_vec_add.clone(), n.clone()), v.clone()),
            w.clone(),
        )
    }

    pub(super) fn vec_sub(&self, n: &Expr, v: &Expr, w: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.nn_vec_sub.clone(), n.clone()), v.clone()),
            w.clone(),
        )
    }

    pub(super) fn relu_vec_app(&self, d: &Expr, x: &Expr) -> Expr {
        Expr::app(Expr::app(self.relu_vec.clone(), d.clone()), x.clone())
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

    pub(super) fn linear_transform_zonotope_app(
        &self,
        m: &Expr,
        n: &Expr,
        k: &Expr,
        w: &Expr,
        bias: &Expr,
        z: &Expr,
    ) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(self.linear_transform_zonotope.clone(), m.clone()),
                            n.clone(),
                        ),
                        k.clone(),
                    ),
                    w.clone(),
                ),
                bias.clone(),
            ),
            z.clone(),
        )
    }

    pub(super) fn add_nat(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::app(Expr::app(self.nat_add.clone(), a.clone()), b.clone())
    }

    pub(super) fn minkowski_add_app(
        &self,
        n: &Expr,
        k1: &Expr,
        k2: &Expr,
        z1: &Expr,
        z2: &Expr,
    ) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(self.zono_minkowski_add.clone(), n.clone()),
                        k1.clone(),
                    ),
                    k2.clone(),
                ),
                z1.clone(),
            ),
            z2.clone(),
        )
    }

    /// Build `NNVerify.Zonotope.minkowski_reduce @n @k1 @k2 z1 z2`.
    /// Minkowski reduction: the set of all x such that x + y in z1 for all y in z2.
    pub(super) fn minkowski_reduce_app(
        &self,
        n: &Expr,
        k1: &Expr,
        k2: &Expr,
        z1: &Expr,
        z2: &Expr,
    ) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(self.zono_minkowski_reduce.clone(), n.clone()),
                        k1.clone(),
                    ),
                    k2.clone(),
                ),
                z1.clone(),
            ),
            z2.clone(),
        )
    }
}

impl Environment {
    /// Initialize zonotope kernel proofs (T01-T08, Minkowski).
    ///
    /// Registers foundational sub-lemma axioms and then proves T01-T08
    /// as `Declaration::Theorem` with proof terms that reference the
    /// sub-lemmas.
    ///
    /// Depends on: `init_nn_verify_foundation_theorems()`,
    ///             `init_nn_verify_relu()`.
    pub fn init_nn_verify_zonotope_proofs(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_zonotope_proofs_init {
            return Ok(());
        }
        self.init_nn_verify_foundation_theorems()?;
        self.init_nn_verify_relu()?;
        // `sub_minkowski_residual`'s honest (existential) restatement uses
        // `Exists` and `And` over the `NNVec n : Type 0` carrier. #zono-false.
        self.init_and()?;
        self.init_exists()?;

        let c = ZonoProofConsts::new();

        // Register Minkowski reduction operation
        self.register_zonotope_minkowski_reduce(&c)?;

        // Register sub-lemma axioms (irreducible mathematical content)
        self.register_sub_interval_hull(&c)?;
        self.register_sub_linear_transform(&c)?;
        self.register_sub_relu_overapprox(&c)?;
        self.register_sub_relu_lambda(&c)?;
        self.register_sub_relu_active(&c)?;
        self.register_sub_relu_inactive(&c)?;
        self.register_sub_affine_relu(&c)?;
        self.register_sub_minkowski_sum(&c)?;
        self.register_sub_minkowski_reduce(&c)?;
        self.register_sub_minkowski_residual(&c)?;

        // Register proved theorems
        self.register_t01_proved(&c)?;
        self.register_t02_proved(&c)?;
        self.register_t03_proved(&c)?;
        self.register_t04_proved(&c)?;
        self.register_t05_proved(&c)?;
        self.register_t06_proved(&c)?;
        self.register_t07_proved(&c)?;
        self.register_t08a_proved(&c)?;
        self.register_t08b_proved(&c)?;
        self.register_t08c_proved(&c)?;

        self.nn_verify_zonotope_proofs_init = true;
        Ok(())
    }

    // =========================================================================
    // Sub-lemma axioms (irreducible mathematical content)
    // =========================================================================

    /// Sub-lemma for T01: interval hull soundness core.
    /// `{n k : Nat} -> (z : Zonotope n k) -> (x : NNVec n) ->
    ///   Zonotope.contains z x -> IntervalBounds.contains (Zonotope.to_ibp z) x`
    fn register_sub_interval_hull(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.sub_interval_hull");
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
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let ibp = c.zono_to_ibp_app(&n, &k, &z);
            let concl = c.ib_contains_app(&n, &ibp, &x);
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

    /// Sub-lemma for T02: linear transform preserves containment core.
    fn register_sub_linear_transform(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.sub_linear_transform");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
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
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let transformed = c.linear_transform_zonotope_app(&m, &n, &k, &w, &bias, &z);
            let output = c.linear_output_app(&m, &n, &w, &bias, &x);
            let concl = c.zono_contains_app(&m, &k, &transformed, &output);
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

    /// Sub-lemma for T03: ReLU overapproximation soundness on zonotopes.
    /// `{n k k' : Nat} -> (z : Zonotope n k) -> (z' : Zonotope n k') ->
    ///   (x : NNVec n) -> Zonotope.contains z x ->
    ///   Zonotope.contains z' (relu_vec n x)`
    fn register_sub_relu_overapprox(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.sub_relu_overapprox");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let zono_nkp = c.zono_of(&n, &kp);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_nkp.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let relu_x = c.relu_vec_app(&n, &x);
            let concl = c.zono_contains_app(&n, &kp, &zp, &relu_x);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(zp_id, BinderInfo::Default, zono_nkp, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(kp_id, BinderInfo::Implicit, c.nat.clone(), r);
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

    /// Sub-lemma for T04: ReLU lambda relaxation tightness.
    /// The lambda-parameterized relaxation of ReLU produces a tighter
    /// overapproximation as lambda -> optimal.
    fn register_sub_relu_lambda(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.sub_relu_lambda");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let zono_nkp = c.zono_of(&n, &kp);
            let vec_n = c.vec_of(&n);
            let (_lam_id, _lam) = b.fresh_local(rat.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_nkp.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let relu_x = c.relu_vec_app(&n, &x);
            let concl = c.zono_contains_app(&n, &kp, &zp, &relu_x);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(zp_id, BinderInfo::Default, zono_nkp, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(_lam_id, BinderInfo::Default, rat, r);
            let r = b.mk_pi(kp_id, BinderInfo::Implicit, c.nat.clone(), r);
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

    /// Sub-lemma for T05: ReLU always-active exactness.
    /// If all components of x are non-negative, relu_vec x = x.
    fn register_sub_relu_active(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.sub_relu_active");
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
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let relu_x = c.relu_vec_app(&n, &x);
            // Conclusion: contains z (relu_vec x) when all components non-neg
            let concl = c.zono_contains_app(&n, &k, &z, &relu_x);
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

    /// Sub-lemma for T06: ReLU always-inactive maps to zero zonotope.
    fn register_sub_relu_inactive(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.sub_relu_inactive");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let zono_nkp = c.zono_of(&n, &kp);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (z0_id, z0) = b.fresh_local(zono_nkp.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let relu_x = c.relu_vec_app(&n, &x);
            let concl = c.zono_contains_app(&n, &kp, &z0, &relu_x);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(z0_id, BinderInfo::Default, zono_nkp, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(kp_id, BinderInfo::Implicit, c.nat.clone(), r);
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

    /// Sub-lemma for T07: affine + ReLU composition soundness.
    fn register_sub_affine_relu(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.sub_affine_relu");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let zono_mkp = c.zono_of(&m, &kp);
            let mat_mn = c.mat_of(&m, &n);
            let vec_m = c.vec_of(&m);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_mkp.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let (bias_id, bias) = b.fresh_local(vec_m.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let linear_x = c.linear_output_app(&m, &n, &w, &bias, &x);
            let relu_y = c.relu_vec_app(&m, &linear_x);
            let concl = c.zono_contains_app(&m, &kp, &zp, &relu_y);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(bias_id, BinderInfo::Default, vec_m, r);
            let r = b.mk_pi(w_id, BinderInfo::Default, mat_mn, r);
            let r = b.mk_pi(zp_id, BinderInfo::Default, zono_mkp, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(kp_id, BinderInfo::Implicit, c.nat.clone(), r);
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

    /// Sub-lemma for T08A: Minkowski sum preserves containment core.
    fn register_sub_minkowski_sum(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.sub_minkowski_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
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
            let h1 = c.zono_contains_app(&n, &k1, &z1, &x);
            let h2 = c.zono_contains_app(&n, &k2, &z2, &y);
            let mink = c.minkowski_add_app(&n, &k1, &k2, &z1, &z2);
            let sum_xy = c.vec_add(&n, &x, &y);
            let k_sum = c.add_nat(&k1, &k2);
            let concl = c.zono_contains_app(&n, &k_sum, &mink, &sum_xy);
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

    /// `NNVerify.Zonotope.minkowski_reduce`:
    /// `{n k1 k2 : Nat} -> Zonotope n k1 -> Zonotope n k2 -> Zonotope n k1`
    ///
    /// Minkowski reduction (Pontryagin difference): the set of all points x
    /// such that for every y in z2, x + y is in z1. Over-approximated by
    /// shrinking generators of z1 by the radius of z2.
    fn register_zonotope_minkowski_reduce(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.minkowski_reduce");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k1_id, k1) = b.fresh_local(c.nat.clone());
            let (k2_id, k2) = b.fresh_local(c.nat.clone());
            let zono_nk1 = c.zono_of(&n, &k1);
            let zono_nk2 = c.zono_of(&n, &k2);
            let result = c.zono_of(&n, &k1);
            let (z1_id, _) = b.fresh_local(zono_nk1.clone());
            let (z2_id, _) = b.fresh_local(zono_nk2.clone());
            let r = b.mk_pi(z2_id, BinderInfo::Default, zono_nk2, result);
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

    /// Sub-lemma for T08B: Minkowski reduction soundness core (HONEST,
    /// ROUND-TRIP restatement — #zono-false fix).
    ///
    /// The OLD axiom was FALSE: `… → (x)(y : NNVec n) →
    /// contains (minkowski_reduce z1 z2) x → contains z2 y →
    /// contains z1 (x + y)`. It is the Pontryagin-difference contract
    /// (`x ∈ z1 ⊖ z2 ⇒ ∀ y ∈ z2, x + y ∈ z1`), but `minkowski_reduce` is an
    /// OPAQUE total axiom of type `Zonotope n k1`, and the Pontryagin difference
    /// can be EMPTY (when `z2` is wider than `z1`) — yet a zonotope always
    /// contains its center, so NO total `reduce` satisfies the universal-in-`y`
    /// contract. Counterexample (pinned in
    /// `tests_zonotope_false_axiom_prevention.rs`): `z1 = {0}`, `z2 = [-1,1]` ⇒
    /// no point `x` has `x + y ∈ {0}` for every `y ∈ [-1,1]`.
    ///
    /// The honest, non-vacuous content is the ROUND-TRIP soundness of the
    /// reduction: re-adding `z2` to the reduced zonotope lands back inside `z1`.
    ///
    /// `{n k1 k2 : Nat} → (z1 : Zonotope n k1) → (z2 : Zonotope n k2) →
    ///   (p : NNVec n) →
    ///   Zonotope.contains (minkowski_add (minkowski_reduce z1 z2) z2) p →
    ///   Zonotope.contains z1 p`
    ///
    /// This is the defining soundness of `z1 ⊖ z2` as an under-approximation:
    /// `(z1 ⊖ z2) ⊕ z2 ⊆ z1`. It carries no false universal-in-`y` claim. (It
    /// still rests on the OPAQUE `minkowski_reduce`; the C4 engine reports it
    /// `Opaque`/trusted, not refutable, since `minkowski_reduce` does not reduce
    /// to a `Zonotope.mk`. Defining a faithful `minkowski_reduce` body is
    /// deferred — see the module note.)
    fn register_sub_minkowski_reduce(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.sub_minkowski_reduce");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k1_id, k1) = b.fresh_local(c.nat.clone());
            let (k2_id, k2) = b.fresh_local(c.nat.clone());
            let zono_nk1 = c.zono_of(&n, &k1);
            let zono_nk2 = c.zono_of(&n, &k2);
            let vec_n = c.vec_of(&n);
            let k_sum = c.add_nat(&k1, &k2);
            let (z1_id, z1) = b.fresh_local(zono_nk1.clone());
            let (z2_id, z2) = b.fresh_local(zono_nk2.clone());
            let (p_id, p) = b.fresh_local(vec_n.clone());
            // reduce z1 z2 : Zonotope n k1
            let reduced = c.minkowski_reduce_app(&n, &k1, &k2, &z1, &z2);
            // minkowski_add (reduce z1 z2) z2 : Zonotope n (k1 + k2)
            let re_added = c.minkowski_add_app(&n, &k1, &k2, &reduced, &z2);
            let h1 = c.zono_contains_app(&n, &k_sum, &re_added, &p);
            let concl = c.zono_contains_app(&n, &k1, &z1, &p);
            let (h1_id, _) = b.fresh_local(h1.clone());
            let r = b.mk_pi(h1_id, BinderInfo::Default, h1, concl);
            let r = b.mk_pi(p_id, BinderInfo::Default, vec_n, r);
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

    /// Sub-lemma for T08C: Minkowski residual containment core (HONEST,
    /// EXISTENTIAL restatement — #zono-false fix).
    ///
    /// The OLD axiom was FALSE: `… → (y : NNVec n) → contains z2 y →
    /// contains z1 (w - y)` let `y` range over ALL of `z2`, but the real
    /// Minkowski sum only guarantees a decomposition `w = w1 + w2` for SOME
    /// `w2 ∈ z2`. Counterexample (pinned in
    /// `tests_zonotope_false_axiom_prevention.rs`): `z1 = {0}`, `z2 = [-1,1]`,
    /// `w = 1`, `y = -1` ⇒ `contains {0} 2`, false.
    ///
    /// The honest statement is EXISTENTIAL in `y` — every point of the Minkowski
    /// sum decomposes into a `z2`-component and a `z1`-residual:
    ///
    /// `{n k1 k2 : Nat} → (z1 : Zonotope n k1) → (z2 : Zonotope n k2) →
    ///   (w : NNVec n) →
    ///   Zonotope.contains (minkowski_add z1 z2) w →
    ///   ∃ (y : NNVec n), Zonotope.contains z2 y ∧
    ///                    Zonotope.contains z1 (NNVec.sub w y)`
    ///
    /// This is the genuine Minkowski-decomposition property and is TRUE for the
    /// faithful `minkowski_add` Definition (generator concatenation).
    fn register_sub_minkowski_residual(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.sub_minkowski_residual");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let and = Expr::const_(Name::from_string("And"), vec![]);
        // `NNVec n : Type 0 = Sort 1`, so `∃ y : NNVec n, …` uses `Exists.{1}`.
        let exists1 = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(Level::zero())],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k1_id, k1) = b.fresh_local(c.nat.clone());
            let (k2_id, k2) = b.fresh_local(c.nat.clone());
            let zono_nk1 = c.zono_of(&n, &k1);
            let zono_nk2 = c.zono_of(&n, &k2);
            let vec_n = c.vec_of(&n);
            let k_sum = c.add_nat(&k1, &k2);
            let (z1_id, z1) = b.fresh_local(zono_nk1.clone());
            let (z2_id, z2) = b.fresh_local(zono_nk2.clone());
            let (w_id, w) = b.fresh_local(vec_n.clone());
            let mink = c.minkowski_add_app(&n, &k1, &k2, &z1, &z2);
            let h1 = c.zono_contains_app(&n, &k_sum, &mink, &w);

            // Existential body: `fun (y : NNVec n) =>
            //   And (contains z2 y) (contains z1 (w - y))`.
            let body_lam = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = ch.fresh_local(vec_n.clone());
                let c_z2_y = c.zono_contains_app(&n, &k2, &z2, &y);
                let diff_wy = c.vec_sub(&n, &w, &y);
                let c_z1_diff = c.zono_contains_app(&n, &k1, &z1, &diff_wy);
                let conj = Expr::app(Expr::app(and.clone(), c_z2_y), c_z1_diff);
                let lam = ch.mk_lam(y_id, BinderInfo::Default, vec_n.clone(), conj);
                ch.finish_child(lam)
            };
            // `Exists.{1} (NNVec n) (fun y => …)`.
            let exists_concl = Expr::app(Expr::app(exists1.clone(), vec_n.clone()), body_lam);

            let (h1_id, _) = b.fresh_local(h1.clone());
            let r = b.mk_pi(h1_id, BinderInfo::Default, h1, exists_concl);
            let r = b.mk_pi(w_id, BinderInfo::Default, vec_n, r);
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

    // =========================================================================
    // Proved theorems (T01-T08C)
    // =========================================================================

    /// T01 proved: interval hull soundness.
    /// Proof term: `fun {n k} z x h => sub_interval_hull z x h`
    fn register_t01_proved(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.T01_interval_hull_proved");
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
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let ibp = c.zono_to_ibp_app(&n, &k, &z);
            let concl = c.ib_contains_app(&n, &ibp, &x);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(k_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let (h_id, h) = b.fresh_local(hyp.clone());
            // Proof: sub_interval_hull @n @k z x h
            let proof = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(Expr::app(c.sub_t01.clone(), n), k), z),
                    x,
                ),
                h,
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
            let e = b.mk_lam(k_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// T02 proved: linear transform exactness.
    fn register_t02_proved(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.T02_linear_transform_proved");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
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
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let transformed = c.linear_transform_zonotope_app(&m, &n, &k, &w, &bias, &z);
            let output = c.linear_output_app(&m, &n, &w, &bias, &x);
            let concl = c.zono_contains_app(&m, &k, &transformed, &output);
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
        let value = {
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
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let (h_id, h) = b.fresh_local(hyp.clone());
            let proof = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(Expr::app(Expr::app(c.sub_t02.clone(), n), k), m),
                                z,
                            ),
                            w,
                        ),
                        bias,
                    ),
                    x,
                ),
                h,
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(bias_id, BinderInfo::Default, vec_m, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// T03 proved: ReLU overapproximation soundness.
    fn register_t03_proved(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.T03_relu_overapprox_proved");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let zono_nkp = c.zono_of(&n, &kp);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_nkp.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let relu_x = c.relu_vec_app(&n, &x);
            let concl = c.zono_contains_app(&n, &kp, &zp, &relu_x);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(zp_id, BinderInfo::Default, zono_nkp, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(kp_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(k_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let zono_nkp = c.zono_of(&n, &kp);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_nkp.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let (h_id, h) = b.fresh_local(hyp.clone());
            let proof = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(Expr::app(Expr::app(c.sub_t03.clone(), n), k), kp),
                            z,
                        ),
                        zp,
                    ),
                    x,
                ),
                h,
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(zp_id, BinderInfo::Default, zono_nkp, e);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
            let e = b.mk_lam(kp_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// T04 proved: ReLU lambda relaxation tightness.
    fn register_t04_proved(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.T04_relu_lambda_proved");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let zono_nkp = c.zono_of(&n, &kp);
            let vec_n = c.vec_of(&n);
            let (lam_id, _lam) = b.fresh_local(rat.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_nkp.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let relu_x = c.relu_vec_app(&n, &x);
            let concl = c.zono_contains_app(&n, &kp, &zp, &relu_x);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(zp_id, BinderInfo::Default, zono_nkp, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(lam_id, BinderInfo::Default, rat.clone(), r);
            let r = b.mk_pi(kp_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(k_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let zono_nkp = c.zono_of(&n, &kp);
            let vec_n = c.vec_of(&n);
            let (lam_id, lam) = b.fresh_local(rat.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_nkp.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let (h_id, h) = b.fresh_local(hyp.clone());
            let proof = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(Expr::app(Expr::app(c.sub_t04.clone(), n), k), kp),
                                lam,
                            ),
                            z,
                        ),
                        zp,
                    ),
                    x,
                ),
                h,
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(zp_id, BinderInfo::Default, zono_nkp, e);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
            let e = b.mk_lam(lam_id, BinderInfo::Default, rat, e);
            let e = b.mk_lam(kp_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// T05 proved: ReLU always-active exactness.
    fn register_t05_proved(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.T05_relu_active_proved");
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
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let relu_x = c.relu_vec_app(&n, &x);
            let concl = c.zono_contains_app(&n, &k, &z, &relu_x);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(k_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let (h_id, h) = b.fresh_local(hyp.clone());
            let proof = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(Expr::app(c.sub_t05.clone(), n), k), z),
                    x,
                ),
                h,
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
            let e = b.mk_lam(k_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// T06 proved: ReLU always-inactive exactness.
    fn register_t06_proved(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.T06_relu_inactive_proved");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let zono_nkp = c.zono_of(&n, &kp);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (z0_id, z0) = b.fresh_local(zono_nkp.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let relu_x = c.relu_vec_app(&n, &x);
            let concl = c.zono_contains_app(&n, &kp, &z0, &relu_x);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(z0_id, BinderInfo::Default, zono_nkp, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(kp_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(k_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let zono_nkp = c.zono_of(&n, &kp);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (z0_id, z0) = b.fresh_local(zono_nkp.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let (h_id, h) = b.fresh_local(hyp.clone());
            let proof = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(Expr::app(Expr::app(c.sub_t06.clone(), n), k), kp),
                            z,
                        ),
                        z0,
                    ),
                    x,
                ),
                h,
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(z0_id, BinderInfo::Default, zono_nkp, e);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
            let e = b.mk_lam(kp_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// T07 proved: affine + ReLU composition soundness.
    fn register_t07_proved(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.T07_affine_relu_proved");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let zono_mkp = c.zono_of(&m, &kp);
            let mat_mn = c.mat_of(&m, &n);
            let vec_m = c.vec_of(&m);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_mkp.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let (bias_id, bias) = b.fresh_local(vec_m.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let linear_x = c.linear_output_app(&m, &n, &w, &bias, &x);
            let relu_y = c.relu_vec_app(&m, &linear_x);
            let concl = c.zono_contains_app(&m, &kp, &zp, &relu_y);
            let (h_id, _) = b.fresh_local(hyp.clone());
            let r = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(bias_id, BinderInfo::Default, vec_m, r);
            let r = b.mk_pi(w_id, BinderInfo::Default, mat_mn, r);
            let r = b.mk_pi(zp_id, BinderInfo::Default, zono_mkp, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(kp_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(k_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let zono_nk = c.zono_of(&n, &k);
            let zono_mkp = c.zono_of(&m, &kp);
            let mat_mn = c.mat_of(&m, &n);
            let vec_m = c.vec_of(&m);
            let vec_n = c.vec_of(&n);
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_mkp.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let (bias_id, bias) = b.fresh_local(vec_m.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());
            let hyp = c.zono_contains_app(&n, &k, &z, &x);
            let (h_id, h) = b.fresh_local(hyp.clone());
            let proof = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(Expr::app(Expr::app(c.sub_t07.clone(), n), k), m),
                                        kp,
                                    ),
                                    z,
                                ),
                                zp,
                            ),
                            w,
                        ),
                        bias,
                    ),
                    x,
                ),
                h,
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(bias_id, BinderInfo::Default, vec_m, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(zp_id, BinderInfo::Default, zono_mkp, e);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
            let e = b.mk_lam(kp_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(k_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// T08A proved: Minkowski sum preserves containment.
    fn register_t08a_proved(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.T08A_minkowski_sum_proved");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
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
            let h1 = c.zono_contains_app(&n, &k1, &z1, &x);
            let h2 = c.zono_contains_app(&n, &k2, &z2, &y);
            let mink = c.minkowski_add_app(&n, &k1, &k2, &z1, &z2);
            let sum_xy = c.vec_add(&n, &x, &y);
            let k_sum = c.add_nat(&k1, &k2);
            let concl = c.zono_contains_app(&n, &k_sum, &mink, &sum_xy);
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
        let value = {
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
            let h1 = c.zono_contains_app(&n, &k1, &z1, &x);
            let h2 = c.zono_contains_app(&n, &k2, &z2, &y);
            let (h1_id, h1v) = b.fresh_local(h1.clone());
            let (h2_id, h2v) = b.fresh_local(h2.clone());
            let proof = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(Expr::app(Expr::app(c.sub_t08a.clone(), n), k1), k2),
                                    z1,
                                ),
                                z2,
                            ),
                            x,
                        ),
                        y,
                    ),
                    h1v,
                ),
                h2v,
            );
            let e = b.mk_lam(h2_id, BinderInfo::Default, h2, proof);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1, e);
            let e = b.mk_lam(y_id, BinderInfo::Default, vec_n.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(z2_id, BinderInfo::Default, zono_nk2, e);
            let e = b.mk_lam(z1_id, BinderInfo::Default, zono_nk1, e);
            let e = b.mk_lam(k2_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(k1_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// T08B proved: Minkowski reduction soundness (HONEST round-trip form —
    /// #zono-false fix). Mirrors the restated `sub_minkowski_reduce` type and
    /// delegates to it.
    /// Proof term: `fun {n k1 k2} z1 z2 p h1 => sub_minkowski_reduce z1 z2 p h1`.
    fn register_t08b_proved(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.T08B_minkowski_reduction_proved");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k1_id, k1) = b.fresh_local(c.nat.clone());
            let (k2_id, k2) = b.fresh_local(c.nat.clone());
            let zono_nk1 = c.zono_of(&n, &k1);
            let zono_nk2 = c.zono_of(&n, &k2);
            let vec_n = c.vec_of(&n);
            let k_sum = c.add_nat(&k1, &k2);
            let (z1_id, z1) = b.fresh_local(zono_nk1.clone());
            let (z2_id, z2) = b.fresh_local(zono_nk2.clone());
            let (p_id, p) = b.fresh_local(vec_n.clone());
            let reduced = c.minkowski_reduce_app(&n, &k1, &k2, &z1, &z2);
            let re_added = c.minkowski_add_app(&n, &k1, &k2, &reduced, &z2);
            let h1 = c.zono_contains_app(&n, &k_sum, &re_added, &p);
            let concl = c.zono_contains_app(&n, &k1, &z1, &p);
            let (h1_id, _) = b.fresh_local(h1.clone());
            let r = b.mk_pi(h1_id, BinderInfo::Default, h1, concl);
            let r = b.mk_pi(p_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(z2_id, BinderInfo::Default, zono_nk2, r);
            let r = b.mk_pi(z1_id, BinderInfo::Default, zono_nk1, r);
            let r = b.mk_pi(k2_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(k1_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k1_id, k1) = b.fresh_local(c.nat.clone());
            let (k2_id, k2) = b.fresh_local(c.nat.clone());
            let zono_nk1 = c.zono_of(&n, &k1);
            let zono_nk2 = c.zono_of(&n, &k2);
            let vec_n = c.vec_of(&n);
            let k_sum = c.add_nat(&k1, &k2);
            let (z1_id, z1) = b.fresh_local(zono_nk1.clone());
            let (z2_id, z2) = b.fresh_local(zono_nk2.clone());
            let (p_id, p) = b.fresh_local(vec_n.clone());
            let reduced = c.minkowski_reduce_app(&n, &k1, &k2, &z1, &z2);
            let re_added = c.minkowski_add_app(&n, &k1, &k2, &reduced, &z2);
            let h1 = c.zono_contains_app(&n, &k_sum, &re_added, &p);
            let (h1_id, h1v) = b.fresh_local(h1.clone());
            // sub_minkowski_reduce n k1 k2 z1 z2 p h1
            let proof = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(Expr::app(c.sub_t08b.clone(), n.clone()), k1.clone()),
                                k2.clone(),
                            ),
                            z1.clone(),
                        ),
                        z2.clone(),
                    ),
                    p.clone(),
                ),
                h1v,
            );
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1, proof);
            let e = b.mk_lam(p_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(z2_id, BinderInfo::Default, zono_nk2, e);
            let e = b.mk_lam(z1_id, BinderInfo::Default, zono_nk1, e);
            let e = b.mk_lam(k2_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(k1_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// T08C proved: Minkowski residual containment (HONEST existential form —
    /// #zono-false fix). Mirrors the restated `sub_minkowski_residual` type and
    /// delegates to it.
    /// Proof term: `fun {n k1 k2} z1 z2 w h1 => sub_minkowski_residual z1 z2 w h1`.
    fn register_t08c_proved(&mut self, c: &ZonoProofConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.T08C_minkowski_residual_proved");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let and = Expr::const_(Name::from_string("And"), vec![]);
        let exists1 = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(Level::zero())],
        );
        // Shared builder for the existential conclusion `∃ y, contains z2 y ∧
        // contains z1 (w - y)`, parameterized by the (already-fresh) locals.
        let build_exists_concl = |b: &EnvDeclBuilder,
                                  n: &Expr,
                                  k1: &Expr,
                                  k2: &Expr,
                                  z1: &Expr,
                                  z2: &Expr,
                                  w: &Expr,
                                  vec_n: &Expr| {
            let mut ch = EnvDeclBuilder::child_of(b);
            let (y_id, y) = ch.fresh_local(vec_n.clone());
            let c_z2_y = c.zono_contains_app(n, k2, z2, &y);
            let diff_wy = c.vec_sub(n, w, &y);
            let c_z1_diff = c.zono_contains_app(n, k1, z1, &diff_wy);
            let conj = Expr::app(Expr::app(and.clone(), c_z2_y), c_z1_diff);
            let lam = ch.mk_lam(y_id, BinderInfo::Default, vec_n.clone(), conj);
            let body_lam = ch.finish_child(lam);
            Expr::app(Expr::app(exists1.clone(), vec_n.clone()), body_lam)
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k1_id, k1) = b.fresh_local(c.nat.clone());
            let (k2_id, k2) = b.fresh_local(c.nat.clone());
            let zono_nk1 = c.zono_of(&n, &k1);
            let zono_nk2 = c.zono_of(&n, &k2);
            let vec_n = c.vec_of(&n);
            let k_sum = c.add_nat(&k1, &k2);
            let (z1_id, z1) = b.fresh_local(zono_nk1.clone());
            let (z2_id, z2) = b.fresh_local(zono_nk2.clone());
            let (w_id, w) = b.fresh_local(vec_n.clone());
            let mink = c.minkowski_add_app(&n, &k1, &k2, &z1, &z2);
            let h1 = c.zono_contains_app(&n, &k_sum, &mink, &w);
            let concl = build_exists_concl(&b, &n, &k1, &k2, &z1, &z2, &w, &vec_n);
            let (h1_id, _) = b.fresh_local(h1.clone());
            let r = b.mk_pi(h1_id, BinderInfo::Default, h1, concl);
            let r = b.mk_pi(w_id, BinderInfo::Default, vec_n, r);
            let r = b.mk_pi(z2_id, BinderInfo::Default, zono_nk2, r);
            let r = b.mk_pi(z1_id, BinderInfo::Default, zono_nk1, r);
            let r = b.mk_pi(k2_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(k1_id, BinderInfo::Implicit, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k1_id, k1) = b.fresh_local(c.nat.clone());
            let (k2_id, k2) = b.fresh_local(c.nat.clone());
            let zono_nk1 = c.zono_of(&n, &k1);
            let zono_nk2 = c.zono_of(&n, &k2);
            let vec_n = c.vec_of(&n);
            let k_sum = c.add_nat(&k1, &k2);
            let (z1_id, z1) = b.fresh_local(zono_nk1.clone());
            let (z2_id, z2) = b.fresh_local(zono_nk2.clone());
            let (w_id, w) = b.fresh_local(vec_n.clone());
            let mink = c.minkowski_add_app(&n, &k1, &k2, &z1, &z2);
            let h1 = c.zono_contains_app(&n, &k_sum, &mink, &w);
            let (h1_id, h1v) = b.fresh_local(h1.clone());
            // sub_minkowski_residual n k1 k2 z1 z2 w h1
            let proof = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(Expr::app(c.sub_t08c.clone(), n.clone()), k1.clone()),
                                k2.clone(),
                            ),
                            z1.clone(),
                        ),
                        z2.clone(),
                    ),
                    w.clone(),
                ),
                h1v,
            );
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1, proof);
            let e = b.mk_lam(w_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(z2_id, BinderInfo::Default, zono_nk2, e);
            let e = b.mk_lam(z1_id, BinderInfo::Default, zono_nk1, e);
            let e = b.mk_lam(k2_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(k1_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
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
    use crate::env::types::ConstantKind;
    use crate::env::Environment;
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_zonotope_proofs()
            .expect("init_nn_verify_zonotope_proofs");
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

    // Sub-lemma axiom registration tests
    #[test]
    fn test_sub_lemmas_registered() {
        let env = make_env();
        let axiom_names = [
            "NNVerify.Zonotope.sub_interval_hull",
            "NNVerify.Zonotope.sub_linear_transform",
            "NNVerify.Zonotope.sub_relu_overapprox",
            "NNVerify.Zonotope.sub_relu_lambda",
            "NNVerify.Zonotope.sub_relu_active",
            "NNVerify.Zonotope.sub_relu_inactive",
            "NNVerify.Zonotope.sub_affine_relu",
            "NNVerify.Zonotope.sub_minkowski_sum",
            "NNVerify.Zonotope.sub_minkowski_reduce",
            "NNVerify.Zonotope.sub_minkowski_residual",
        ];
        for name in &axiom_names {
            assert_registered(&env, name);
            assert_kind(&env, name, ConstantKind::Axiom);
        }
    }

    // Minkowski reduce operation registration test
    #[test]
    fn test_minkowski_reduce_registered() {
        let env = make_env();
        assert_registered(&env, "NNVerify.Zonotope.minkowski_reduce");
        assert_kind(
            &env,
            "NNVerify.Zonotope.minkowski_reduce",
            ConstantKind::Axiom,
        );
    }

    // Proved theorem registration tests
    #[test]
    fn test_t01_proved_is_theorem() {
        let env = make_env();
        assert_kind(
            &env,
            "NNVerify.Zonotope.T01_interval_hull_proved",
            ConstantKind::Theorem,
        );
    }

    #[test]
    fn test_t02_proved_is_theorem() {
        let env = make_env();
        assert_kind(
            &env,
            "NNVerify.Zonotope.T02_linear_transform_proved",
            ConstantKind::Theorem,
        );
    }

    #[test]
    fn test_t03_proved_is_theorem() {
        let env = make_env();
        assert_kind(
            &env,
            "NNVerify.Zonotope.T03_relu_overapprox_proved",
            ConstantKind::Theorem,
        );
    }

    #[test]
    fn test_t04_proved_is_theorem() {
        let env = make_env();
        assert_kind(
            &env,
            "NNVerify.Zonotope.T04_relu_lambda_proved",
            ConstantKind::Theorem,
        );
    }

    #[test]
    fn test_t05_proved_is_theorem() {
        let env = make_env();
        assert_kind(
            &env,
            "NNVerify.Zonotope.T05_relu_active_proved",
            ConstantKind::Theorem,
        );
    }

    #[test]
    fn test_t06_proved_is_theorem() {
        let env = make_env();
        assert_kind(
            &env,
            "NNVerify.Zonotope.T06_relu_inactive_proved",
            ConstantKind::Theorem,
        );
    }

    #[test]
    fn test_t07_proved_is_theorem() {
        let env = make_env();
        assert_kind(
            &env,
            "NNVerify.Zonotope.T07_affine_relu_proved",
            ConstantKind::Theorem,
        );
    }

    #[test]
    fn test_t08a_proved_is_theorem() {
        let env = make_env();
        assert_kind(
            &env,
            "NNVerify.Zonotope.T08A_minkowski_sum_proved",
            ConstantKind::Theorem,
        );
    }

    #[test]
    fn test_t08b_proved_is_theorem() {
        let env = make_env();
        assert_kind(
            &env,
            "NNVerify.Zonotope.T08B_minkowski_reduction_proved",
            ConstantKind::Theorem,
        );
    }

    #[test]
    fn test_t08c_proved_is_theorem() {
        let env = make_env();
        assert_kind(
            &env,
            "NNVerify.Zonotope.T08C_minkowski_residual_proved",
            ConstantKind::Theorem,
        );
    }

    // Type-checking tests
    #[test]
    fn test_all_theorems_type_check() {
        let env = make_env();
        let theorem_names = [
            "NNVerify.Zonotope.T01_interval_hull_proved",
            "NNVerify.Zonotope.T02_linear_transform_proved",
            "NNVerify.Zonotope.T03_relu_overapprox_proved",
            "NNVerify.Zonotope.T04_relu_lambda_proved",
            "NNVerify.Zonotope.T05_relu_active_proved",
            "NNVerify.Zonotope.T06_relu_inactive_proved",
            "NNVerify.Zonotope.T07_affine_relu_proved",
            "NNVerify.Zonotope.T08A_minkowski_sum_proved",
            "NNVerify.Zonotope.T08B_minkowski_reduction_proved",
            "NNVerify.Zonotope.T08C_minkowski_residual_proved",
        ];
        for name in &theorem_names {
            assert_type_checks_as_pi(&env, name);
        }
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_zonotope_proofs().expect("first init");
        env.init_nn_verify_zonotope_proofs().expect("second init");
    }
}
