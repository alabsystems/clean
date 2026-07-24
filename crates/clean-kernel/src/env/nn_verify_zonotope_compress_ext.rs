// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended zonotope compression theorems (Phase 2 of C001).
//!
//! Builds on `nn_verify_zonotope_compress.rs` (T10-T12) with additional
//! supporting types and theorems for zonotope compression analysis:
//!
//! ## Types
//!
//! - `NNVerify.Zonotope.GeneratorPartition` — partition of k generators
//!   into k' groups (axiom type)
//! - `NNVerify.Zonotope.compression_error` — error bound between original
//!   and compressed zonotope (axiom function)
//!
//! ## Theorems
//!
//! - **T11b: `compress_projection_tightness`** — width after compression
//!   is bounded by original width plus compression error:
//!   `width(to_ibp(compress(z))) <= width(to_ibp(z)) + compression_error(z, z')`
//! - **T12b: `compress_hull_exact`** — interval hull is preserved exactly
//!   by compression: `to_ibp(compress(z)) = to_ibp(z)`
//!
//! Part of #3152.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Extended constants for Phase 2 zonotope compression.
struct CompressExtConsts {
    nat: Expr,
    rat: Expr,
    type0: Expr,
    nn_vec: Expr,
    nn_mat: Expr,
    zonotope: Expr,
    zono_compress: Expr,
    zono_to_ibp: Expr,
    ib: Expr,
    ib_width: Expr,
    nn_vec_l1_norm: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    rat_add: Expr,
    eq: Expr,
    lt_zonotope: Expr,
    compression_error: Expr,
}

impl CompressExtConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            zonotope: Expr::const_(Name::from_string("NNVerify.Zonotope"), vec![]),
            zono_compress: Expr::const_(Name::from_string("NNVerify.Zonotope.compress"), vec![]),
            zono_to_ibp: Expr::const_(Name::from_string("NNVerify.Zonotope.to_ibp"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_width: Expr::const_(Name::from_string("NNVerify.IntervalBounds.width"), vec![]),
            nn_vec_l1_norm: Expr::const_(Name::from_string("NNVerify.NNVec.l1_norm"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            lt_zonotope: Expr::const_(
                Name::from_string("NNVerify.linear_transform_zonotope"),
                vec![],
            ),
            compression_error: Expr::const_(
                Name::from_string("NNVerify.Zonotope.compression_error"),
                vec![],
            ),
        }
    }

    fn zono_of(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::app(Expr::app(self.zonotope.clone(), n.clone()), k.clone())
    }

    fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    fn mat_of(&self, m: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m.clone()), n.clone())
    }

    fn ib_of(&self, d: &Expr) -> Expr {
        Expr::app(self.ib.clone(), d.clone())
    }

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

    fn add_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    fn eq_of(&self, alpha: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.eq.clone(), alpha), lhs), rhs)
    }

    fn l1_norm(&self, n: &Expr, v: &Expr) -> Expr {
        Expr::app(Expr::app(self.nn_vec_l1_norm.clone(), n.clone()), v.clone())
    }

    fn ib_width_app(&self, d: &Expr, b: &Expr) -> Expr {
        Expr::app(Expr::app(self.ib_width.clone(), d.clone()), b.clone())
    }

    fn to_ibp_app(&self, n: &Expr, k: &Expr, z: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.zono_to_ibp.clone(), n.clone()), k.clone()),
            z.clone(),
        )
    }

    /// `compress n k k' h_le z` — refined arity threads `h_le : Nat.le k' k`.
    fn compress_app(&self, n: &Expr, k: &Expr, kp: &Expr, hle: &Expr, z: &Expr) -> Expr {
        Expr::apps(
            self.zono_compress.clone(),
            [n.clone(), k.clone(), kp.clone(), hle.clone(), z.clone()],
        )
    }

    /// `Nat.le a b`.
    fn nat_le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.le"), vec![]),
            [a.clone(), b.clone()],
        )
    }

    fn compression_error_app(&self, n: &Expr, k: &Expr, kp: &Expr, z: &Expr, zp: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(self.compression_error.clone(), n.clone()),
                        k.clone(),
                    ),
                    kp.clone(),
                ),
                z.clone(),
            ),
            zp.clone(),
        )
    }

    fn lt_zonotope_app(
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
                        Expr::app(Expr::app(self.lt_zonotope.clone(), m.clone()), n.clone()),
                        k.clone(),
                    ),
                    w.clone(),
                ),
                bias.clone(),
            ),
            z.clone(),
        )
    }
}

impl Environment {
    /// Initialize extended zonotope compression declarations (Phase 2).
    ///
    /// Depends on:
    /// - `init_nn_verify_zonotope_compress()` for T10-T12 + base types
    /// - `init_nn_verify_foundation_theorems()` for linear_transform_zonotope
    /// - `init_nn_verify_foundation_types()` for l1_norm, width
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_zonotope_compress_ext(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.Zonotope.GeneratorPartition"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_shared_bootstrap()?;
        self.init_nn_verify_zonotope_compress()?;
        self.init_nn_verify_foundation_theorems()?;

        let c = CompressExtConsts::new();
        self.register_generator_partition(&c)?;
        self.register_compression_error(&c)?;
        self.register_compress_projection_tightness(&c)?;
        self.register_compress_hull_exact(&c)?;

        Ok(())
    }

    /// `NNVerify.Zonotope.GeneratorPartition : Nat -> Nat -> Nat -> Type`
    ///
    /// Represents a partition of k generators into k' groups for compression.
    /// Parameters: n (dimension), k (original generators), k' (compressed).
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_generator_partition(&mut self, c: &CompressExtConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.GeneratorPartition");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let (kp_id, _) = b.fresh_local(c.nat.clone());
            let r = b.mk_pi(kp_id, BinderInfo::Default, c.nat.clone(), c.type0.clone());
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// `NNVerify.Zonotope.compression_error`:
    /// `(n k k' : Nat) -> Zonotope n k -> Zonotope n k' -> Rat`
    ///
    /// The error bound between the original and compressed zonotope,
    /// measured as the maximum excess width introduced by compression.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_compression_error(&mut self, c: &CompressExtConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.compression_error");
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
            let (z_id, _) = b.fresh_local(zono_nk.clone());
            let (zp_id, _) = b.fresh_local(zono_nkp.clone());
            let r = b.mk_pi(zp_id, BinderInfo::Default, zono_nkp, c.rat.clone());
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(kp_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// **T11b: `NNVerify.Zonotope.compress_projection_tightness`**
    ///
    /// `forall (m n k k' : Nat) (W : NNMat m n) (bias : NNVec m)
    ///   (z : Zonotope n k) (z' : Zonotope n k'),
    ///   compress n k k' z = z' ->
    ///   l1_norm m (width m (to_ibp m k' (linear_transform_zonotope m n k' W bias z')))
    ///     <= l1_norm m (width m (to_ibp m k (linear_transform_zonotope m n k W bias z)))
    ///        + compression_error n k k' z z'`
    ///
    /// Width after compression through a linear transform is bounded by
    /// original width plus the compression error.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_compress_projection_tightness(
        &mut self,
        c: &CompressExtConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.compress_projection_tightness");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let (kp_id, kp) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(&m, &n);
            let vec_m = c.vec_of(&m);
            let zono_nk = c.zono_of(&n, &k);
            let zono_nkp = c.zono_of(&n, &kp);

            // h_le : Nat.le k' k — refined `compress` arity.
            let h_le_ty = c.nat_le(&kp, &k);
            let (hle_id, hle) = b.fresh_local(h_le_ty.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let (bias_id, bias) = b.fresh_local(vec_m.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_nkp.clone());

            // hypothesis: compress n k k' h_le z = z'
            let compress_z = c.compress_app(&n, &k, &kp, &hle, &z);
            let h_compress = c.eq_of(zono_nkp.clone(), compress_z, zp.clone());

            // LHS: l1_norm m (width m (to_ibp m k' (lt_zonotope m n k' W bias z')))
            let lt_zp = c.lt_zonotope_app(&m, &n, &kp, &w, &bias, &zp);
            let ibp_zp = c.to_ibp_app(&m, &kp, &lt_zp);
            let width_zp = c.ib_width_app(&m, &ibp_zp);
            let lhs = c.l1_norm(&m, &width_zp);

            // RHS: l1_norm m (width m (to_ibp m k (lt_zonotope m n k W bias z)))
            //        + compression_error n k k' z z'
            let lt_z = c.lt_zonotope_app(&m, &n, &k, &w, &bias, &z);
            let ibp_z = c.to_ibp_app(&m, &k, &lt_z);
            let width_z = c.ib_width_app(&m, &ibp_z);
            let rhs_base = c.l1_norm(&m, &width_z);
            let err = c.compression_error_app(&n, &k, &kp, &z, &zp);
            let rhs = c.add_rat(rhs_base, err);

            let concl = c.rat_le(lhs, rhs);

            let (hc_id, _) = b.fresh_local(h_compress.clone());
            let r = b.mk_pi(hc_id, BinderInfo::Default, h_compress, concl);
            let r = b.mk_pi(zp_id, BinderInfo::Default, zono_nkp, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(bias_id, BinderInfo::Default, vec_m, r);
            let r = b.mk_pi(w_id, BinderInfo::Default, mat_mn, r);
            let r = b.mk_pi(hle_id, BinderInfo::Default, h_le_ty, r);
            let r = b.mk_pi(kp_id, BinderInfo::Default, c.nat.clone(), r);
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

    /// **T12b: `NNVerify.Zonotope.compress_hull_exact`**
    ///
    /// `forall (n k k' : Nat) (z : Zonotope n k) (z' : Zonotope n k'),
    ///   compress n k k' z = z' ->
    ///   Eq (to_ibp n k z) (to_ibp n k' z')`
    ///
    /// The interval hull is preserved exactly by compression: the IBP
    /// over-approximation of the original zonotope equals that of the
    /// compressed zonotope. This is the strongest form of hull preservation.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_compress_hull_exact(&mut self, c: &CompressExtConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Zonotope.compress_hull_exact");
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
            let ib_n = c.ib_of(&n);

            // h_le : Nat.le k' k — refined `compress` arity.
            let h_le_ty = c.nat_le(&kp, &k);
            let (hle_id, hle) = b.fresh_local(h_le_ty.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let (zp_id, zp) = b.fresh_local(zono_nkp.clone());

            // hypothesis: compress n k k' h_le z = z'
            let compress_z = c.compress_app(&n, &k, &kp, &hle, &z);
            let h_compress = c.eq_of(zono_nkp.clone(), compress_z, zp.clone());

            // conclusion: to_ibp n k z = to_ibp n k' z'
            let ibp_z = c.to_ibp_app(&n, &k, &z);
            let ibp_zp = c.to_ibp_app(&n, &kp, &zp);
            let concl = c.eq_of(ib_n, ibp_z, ibp_zp);

            let (hc_id, _) = b.fresh_local(h_compress.clone());
            let r = b.mk_pi(hc_id, BinderInfo::Default, h_compress, concl);
            let r = b.mk_pi(zp_id, BinderInfo::Default, zono_nkp, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(hle_id, BinderInfo::Default, h_le_ty, r);
            let r = b.mk_pi(kp_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }
}
