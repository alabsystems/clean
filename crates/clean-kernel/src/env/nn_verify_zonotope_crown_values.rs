// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C010 Opaque definition value builders (Category A fix).
//!
//! Contains well-typed placeholder values for the 8 definition functions
//! that were upgraded from `Declaration::Axiom` to `Declaration::Opaque`.
//! Split from `nn_verify_zonotope_crown.rs` for file-size compliance.

use super::nn_verify_zonotope_crown::ZonotopeCrownConsts;
use super::nn_verify_zonotope_crown_defs as defs;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Build a zero IntervalBounds for dimension `dim_expr`.
    /// Returns `IntervalBounds.mk @dim (fun _ => 0) (fun _ => 0) (fun _ => le_refl 0)`.
    pub(super) fn build_zero_ib(
        b: &mut EnvDeclBuilder,
        _c: &ZonotopeCrownConsts,
        dim: &Expr,
    ) -> Expr {
        let ib_mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
        let fin_d = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), dim.clone());
        // lower = upper = fun (_ : Fin d) => Rat.zero
        let zero_vec = {
            let mut ch = EnvDeclBuilder::child_of(b);
            let (i_id, _) = ch.fresh_local(fin_d.clone());
            let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), rat_zero.clone());
            ch.finish_child(r)
        };
        // valid = fun (_ : Fin d) => Rat.le_refl Rat.zero
        let valid = {
            let mut ch = EnvDeclBuilder::child_of(b);
            let (i_id, _) = ch.fresh_local(fin_d.clone());
            let proof = Expr::app(le_refl, rat_zero);
            let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d, proof);
            ch.finish_child(r)
        };
        Expr::apps(ib_mk, [dim.clone(), zero_vec.clone(), zero_vec, valid])
    }

    /// `NNVerify.NNMat.mul` — matrix multiplication, Opaque definition.
    ///
    /// **Wave-5 demasquerade (Branch A, 2026-04-20).**
    /// Previously a reducible `Declaration::Definition` with an
    /// argument-discarding body returning the constant zero function. The
    /// reducible Definition status was solely there to let the type checker
    /// delta-unfold both sides of `A*(B*C) = (A*B)*C` to a common constant
    /// function, enabling a fake Eq.refl proof of `NNVerify.C010.mat_mul_assoc`
    /// (MASQUERADE per M1+M2+M4 of
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md`).
    ///
    /// Flipped to `Declaration::Opaque` (same body) to close the delta-reduction
    /// loophole. Opaques do not delta-unfold in `def_eq`, so no downstream
    /// theorem can rely on the zero-valued body silently. The paired theorem
    /// `mat_mul_assoc` was demoted to `Declaration::Axiom` in the same commit.
    pub(super) fn register_mat_mul(&mut self, c: &ZonotopeCrownConsts) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.NNMat.mul");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let ty = defs::build_mat_mul_type(c);
        // Value: fun (m n p : Nat) (_ : NNMat m n) (_ : NNMat n p) =>
        //   fun (i : Fin m) (j : Fin p) => Rat.zero
        // (Same placeholder body as before; Opaque prevents delta-unfolding.)
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m_var) = b.fresh_local(c.base.nat.clone());
            let (n_id, n_var) = b.fresh_local(c.base.nat.clone());
            let (p_id, p_var) = b.fresh_local(c.base.nat.clone());
            let mat_mn = c.base.mat_of(m_var.clone(), n_var.clone());
            let mat_np = c.base.mat_of(n_var, p_var.clone());
            let (a_id, _) = b.fresh_local(mat_mn.clone());
            let (bv_id, _) = b.fresh_local(mat_np.clone());
            let fin_m = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), m_var);
            let fin_p = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), p_var);
            let (i_id, _) = b.fresh_local(fin_m.clone());
            let (j_id, _) = b.fresh_local(fin_p.clone());
            let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
            let e = b.mk_lam(j_id, BinderInfo::Default, fin_p, rat_zero);
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_m, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, mat_np, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(p_id, BinderInfo::Default, c.base.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.base.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.NNMat.transpose` — matrix transpose, Opaque definition.
    /// Category A: definition-masquerading-as-axiom, upgraded to Opaque.
    pub(super) fn register_mat_transpose(
        &mut self,
        c: &ZonotopeCrownConsts,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.NNMat.transpose");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let ty = defs::build_mat_transpose_type(c);
        // Value: fun (m n : Nat) (_ : NNMat m n) => fun (i : Fin n) (j : Fin m) => Rat.zero
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m_var) = b.fresh_local(c.base.nat.clone());
            let (n_id, n_var) = b.fresh_local(c.base.nat.clone());
            let mat_mn = c.base.mat_of(m_var.clone(), n_var.clone());
            let (a_id, _) = b.fresh_local(mat_mn.clone());
            let fin_n = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), n_var);
            let fin_m = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), m_var);
            let (i_id, _) = b.fresh_local(fin_n.clone());
            let (j_id, _) = b.fresh_local(fin_m.clone());
            let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
            let e = b.mk_lam(j_id, BinderInfo::Default, fin_m, rat_zero);
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, e);
            let e = b.mk_lam(a_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.base.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.Zonotope.linear_propagate` — zonotope forward propagation.
    /// Category A: definition-masquerading-as-axiom, upgraded to Opaque.
    pub(super) fn register_zonotope_linear_propagate(
        &mut self,
        c: &ZonotopeCrownConsts,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.Zonotope.linear_propagate");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let ty = defs::build_zonotope_linear_propagate_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m_var) = b.fresh_local(c.base.nat.clone());
            let (n_id, n_var) = b.fresh_local(c.base.nat.clone());
            let mat_mn = c.base.mat_of(m_var.clone(), n_var.clone());
            let vec_m = c.base.vec_of(m_var.clone());
            let ib_n = c.base.ib_of(n_var);
            let (w_id, _) = b.fresh_local(mat_mn.clone());
            let (bias_id, _) = b.fresh_local(vec_m.clone());
            let (ib_id, _) = b.fresh_local(ib_n.clone());
            let body = Self::build_zero_ib(&mut b, c, &m_var);
            let e = b.mk_lam(ib_id, BinderInfo::Default, ib_n, body);
            let e = b.mk_lam(bias_id, BinderInfo::Default, vec_m, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.base.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.CROWN.backward_linear` — CROWN backward propagation.
    /// Category A: definition-masquerading-as-axiom, upgraded to Opaque.
    pub(super) fn register_crown_backward_linear(
        &mut self,
        c: &ZonotopeCrownConsts,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.CROWN.backward_linear");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let ty = defs::build_crown_backward_linear_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m_var) = b.fresh_local(c.base.nat.clone());
            let (n_id, n_var) = b.fresh_local(c.base.nat.clone());
            let mat_mn = c.base.mat_of(m_var.clone(), n_var.clone());
            let vec_m = c.base.vec_of(m_var.clone());
            let ib_n = c.base.ib_of(n_var);
            let (w_id, _) = b.fresh_local(mat_mn.clone());
            let (bias_id, _) = b.fresh_local(vec_m.clone());
            let (ib_id, _) = b.fresh_local(ib_n.clone());
            let body = Self::build_zero_ib(&mut b, c, &m_var);
            let e = b.mk_lam(ib_id, BinderInfo::Default, ib_n, body);
            let e = b.mk_lam(bias_id, BinderInfo::Default, vec_m, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.base.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.Zonotope.to_bounds` — convert zonotope to IntervalBounds.
    /// Category A: definition-masquerading-as-axiom, upgraded to Opaque.
    pub(super) fn register_zonotope_to_bounds(
        &mut self,
        c: &ZonotopeCrownConsts,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.Zonotope.to_bounds");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let ty = defs::build_zonotope_to_bounds_type(c);
        // Value: fun (n : Nat) (_ : NNVec n) (ib : IB n) => ib
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n_var) = b.fresh_local(c.base.nat.clone());
            let vec_n = c.base.vec_of(n_var.clone());
            let ib_n = c.base.ib_of(n_var);
            let (center_id, _) = b.fresh_local(vec_n.clone());
            let (ib_id, ib_var) = b.fresh_local(ib_n.clone());
            let e = b.mk_lam(ib_id, BinderInfo::Default, ib_n, ib_var);
            let e = b.mk_lam(center_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.CROWN.concretize_linear` — concretize CROWN bounds for k layers.
    /// Category A: definition-masquerading-as-axiom, upgraded to Opaque.
    pub(super) fn register_crown_concretize_linear(
        &mut self,
        c: &ZonotopeCrownConsts,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.CROWN.concretize_linear");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let ty = defs::build_crown_concretize_linear_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k_var) = b.fresh_local(c.base.nat.clone());
            let output_dim_ty = c.output_dim_ty();
            let (od_id, od_var) = b.fresh_local(output_dim_ty.clone());
            let weight_ty = c.weight_family_ty(&b, &od_var);
            let (w_id, _) = b.fresh_local(weight_ty.clone());
            let bias_ty = c.bias_family_ty(&b, &od_var);
            let (bias_id, _) = b.fresh_local(bias_ty.clone());
            let input_ty = c.base.ib_of(c.out_dim(&od_var, c.nat_zero.clone()));
            let (inp_id, _) = b.fresh_local(input_ty.clone());
            let dim_k = c.out_dim(&od_var, k_var);
            let body = Self::build_zero_ib(&mut b, c, &dim_k);
            let e = b.mk_lam(inp_id, BinderInfo::Default, input_ty, body);
            let e = b.mk_lam(bias_id, BinderInfo::Default, bias_ty, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, weight_ty, e);
            let e = b.mk_lam(od_id, BinderInfo::Default, output_dim_ty, e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.Zonotope.linear_propagate_network` — k-layer zonotope forward.
    /// Category A: definition-masquerading-as-axiom, upgraded to Opaque.
    pub(super) fn register_zonotope_linear_propagate_network(
        &mut self,
        c: &ZonotopeCrownConsts,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.Zonotope.linear_propagate_network");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let ty = defs::build_zonotope_linear_propagate_network_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k_var) = b.fresh_local(c.base.nat.clone());
            let output_dim_ty = c.output_dim_ty();
            let (od_id, od_var) = b.fresh_local(output_dim_ty.clone());
            let weight_ty = c.weight_family_ty(&b, &od_var);
            let (w_id, _) = b.fresh_local(weight_ty.clone());
            let bias_ty = c.bias_family_ty(&b, &od_var);
            let (bias_id, _) = b.fresh_local(bias_ty.clone());
            let input_ty = c.base.ib_of(c.out_dim(&od_var, c.nat_zero.clone()));
            let (inp_id, _) = b.fresh_local(input_ty.clone());
            let dim_k = c.out_dim(&od_var, k_var);
            let body = Self::build_zero_ib(&mut b, c, &dim_k);
            let e = b.mk_lam(inp_id, BinderInfo::Default, input_ty, body);
            let e = b.mk_lam(bias_id, BinderInfo::Default, bias_ty, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, weight_ty, e);
            let e = b.mk_lam(od_id, BinderInfo::Default, output_dim_ty, e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.C010.affine_combined` — combined affine computation.
    /// Registered as Declaration::Opaque whose body is
    /// `NNVerify.Zonotope.linear_propagate_network`. Wave-8 Branch A
    /// demotion 2026-04-20 (#3593): this was previously a reducible
    /// Declaration::Definition, which let `both_compute_exact_affine`
    /// close by `Eq.refl` via δ-unfolding the alias (M1 MASQUERADE).
    /// Opaques do not δ-unfold during `def_eq`, so flipping the kind
    /// (body unchanged) closes the loophole. The declaration is
    /// retained as Opaque for naming-compatibility with downstream code
    /// that references `NNVerify.C010.affine_combined`. See
    /// `reports/audit/2026-04-20-r10-wave8-masquerade-sweep.md`
    /// Finding 2.
    pub(super) fn register_affine_combined(
        &mut self,
        c: &ZonotopeCrownConsts,
    ) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C010.affine_combined");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let ty = defs::build_affine_combined_type(c);
        // Value: directly reference zonotope_linear_propagate_network
        // (same type, same semantics — affine_combined IS the zonotope
        // forward propagation for linear networks). Kind is Opaque so
        // the body does NOT δ-unfold during `def_eq`, preventing
        // downstream M1 MASQUERADES over this alias.
        let value = Expr::const_(
            Name::from_string("NNVerify.Zonotope.linear_propagate_network"),
            vec![],
        );
        self.add_decl(Declaration::Opaque {
            name: n,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
