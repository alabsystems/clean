// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The LOWER cube squeeze `a_n³ ≤ x` (the cube floor never overshoots), the
//! cube analogue of the sqrt layer's `dyadicApprox_sq_le`.

use super::CbrtSqueezeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// `Rat.cbrtDyadicApprox_cube_le : ∀ x, 0≤x → ∀ n, a_n³ ≤ x`.
    ///
    /// `cbrtDyadicNum_cube_le x h0 n : (kn)³ ≤ x·8^n`. Multiply by `inv(8^n) ≥ 0`
    /// (right): `(kn)³·inv(8^n) ≤ (x·8^n)·inv(8^n)`. Rewrite RHS
    /// `(x·8^n)·inv(8^n) = x·(8^n·inv 8^n) = x·1 = x`; rewrite LHS by
    /// `cbrtDyadicApprox_cube_eq` (symm) to `a_n³`.
    pub(crate) fn register_cbrt_dyadic_approx_cube_le(
        &mut self,
        c: &CbrtSqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cbrtDyadicApprox_cube_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let cnum_cube_le = Expr::const_(Name::from_string("Rat.cbrtDyadicNum_cube_le"), vec![]);
        let cube_eq = Expr::const_(Name::from_string("Rat.cbrtDyadicApprox_cube_eq"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, _h0) = b.fresh_local(h0_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());
                let a = c.approx(&x, n.clone());
                let concl = c.le(c.cube(a), x.clone());
                ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
            };
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, inner);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());

                let kn = c.ofnat(c.cnum(&x, n.clone()));
                let cube_kn = c.cube(kn.clone()); // (kn·kn)·kn
                let pow8 = c.pow8(n.clone());
                let x_pow8 = c.mul(x.clone(), pow8.clone());
                let inv8 = c.inv(pow8.clone());

                // h_inv : (kn)³ ≤ x·8^n.
                let h_inv = Expr::apps(cnum_cube_le.clone(), [x.clone(), h0.clone(), n.clone()]);
                // h_mul : (kn)³·inv8 ≤ (x·8^n)·inv8.
                let h0_inv8 = c.zero_le_inv_pow8(&n);
                let h_mul = c.mul_le_right(
                    inv8.clone(),
                    cube_kn.clone(),
                    x_pow8.clone(),
                    h_inv,
                    h0_inv8,
                );

                // RHS: (x·8^n)·inv8 = x·(8^n·inv8) = x·1 = x.
                let e_assoc = c.mul_assoc(x.clone(), pow8.clone(), inv8.clone());
                let cancel = c.mul_inv_cancel(pow8.clone(), c.pow8_ne_zero(&n)); // 8^n·inv8 = 1
                let pow8_inv8 = c.mul(pow8.clone(), inv8.clone());
                let f_x = {
                    let mut d = EnvDeclBuilder::child_of(&ib);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.mul(x.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let e_congr = c.congr_arg(pow8_inv8.clone(), c.rat_one.clone(), f_x, cancel);
                let e_mulone = c.mul_one(x.clone());
                let x_pow8_inv8 = c.mul(x_pow8.clone(), inv8.clone());
                let x_times1 = c.mul(x.clone(), c.rat_one.clone());
                let x_times_cancel = c.mul(x.clone(), pow8_inv8.clone());
                let rhs_t1 = c.trans(
                    x_pow8_inv8.clone(),
                    x_times_cancel.clone(),
                    x_times1.clone(),
                    e_assoc,
                    e_congr,
                );
                let rhs_eq_x = c.trans(
                    x_pow8_inv8.clone(),
                    x_times1.clone(),
                    x.clone(),
                    rhs_t1,
                    e_mulone,
                );

                // Transport h_mul RHS → (kn)³·inv8 ≤ x.
                let cube_kn_inv8 = c.mul(cube_kn.clone(), inv8.clone());
                let motive_r = {
                    let mut d = EnvDeclBuilder::child_of(&ib);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(cube_kn_inv8.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let h_le_x = c.subst(motive_r, x_pow8_inv8.clone(), x.clone(), rhs_eq_x, h_mul);

                // LHS rewrite: a_n³ = (kn)³·inv8 (cube_eq); transport (symm) → a_n³ ≤ x.
                let a = c.approx(&x, n.clone());
                let cube_a = c.cube(a.clone());
                let h_cube_eq = Expr::apps(cube_eq.clone(), [x.clone(), n.clone()]); // a³ = cube_kn·inv8
                let h_cube_eq_symm = c.symm(cube_a.clone(), cube_kn_inv8.clone(), h_cube_eq); // cube_kn·inv8 = a³
                let motive_l = {
                    let mut d = EnvDeclBuilder::child_of(&ib);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(t, x.clone());
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let body = c.subst(
                    motive_l,
                    cube_kn_inv8.clone(),
                    cube_a.clone(),
                    h_cube_eq_symm,
                    h_le_x,
                );

                ib.finish_child(ib.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, inner);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
