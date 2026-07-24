// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T80 proof construction for IBP linear soundness.
//!
//! Extracted from `nn_verify_ibp_linear` for file-size compliance (#307).
//!
//! Contains:
//! - `NNVerify.linear_output` — y = W*x + b definition (Definition)
//! - `NNVerify.ibp_linear_per_component` — per-index helper (Opaque, sorry-inhabited)
//! - `NNVerify.ibp_linear_sound` — main theorem with proof term (Theorem)
//!
//! Part of #3244, #3366.

use super::nn_verify_ibp_linear::IbpLinearConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Build `Rat.add (Fin.sum n (fun i => Rat.mul (W j i) (x i))) (b j)` for index j.
fn build_linear_output(
    c: &IbpLinearConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    w_j: &Expr,
    bias_j: &Expr,
    x: &Expr,
) -> Expr {
    // Build: fun i : Fin n => Rat.mul (W_j i) (x i)
    let summand = {
        let mut ch = EnvDeclBuilder::child_of(b);
        let fin_n = Expr::app(c.fin.clone(), n.clone());
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let w_ji = Expr::app(w_j.clone(), i.clone());
        let x_i = Expr::app(x.clone(), i);
        let body = c.mul(w_ji, x_i);
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n, body);
        ch.finish_child(r)
    };
    let dot_product = c.sum(n.clone(), summand);
    c.add(dot_product, bias_j.clone())
}

/// Build the proof term for `ibp_linear_sound`.
///
/// The proof is a lambda term:
/// ```text
/// fun (m n : Nat) (W : NNMat m n) (b : NNVec m) (B : IB n) (x : NNVec n)
///     (hx : contains B x) =>
///   fun (j : Fin m) =>
///     ibp_linear_per_component m n W b B x hx j
/// ```
///
/// We register `NNVerify.ibp_linear_per_component` as a helper axiom
/// that captures the per-index proof, then compose the full proof from it.
fn build_ibp_linear_sound_proof(c: &IbpLinearConsts) -> Expr {
    let ibp_per_component = Expr::const_(
        Name::from_string("NNVerify.ibp_linear_per_component"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let vec_m = c.vec_of(m.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());

    let (w_id, w) = b.fresh_local(mat_mn.clone());
    let (bias_id, bias) = b.fresh_local(vec_m.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let (x_id, x) = b.fresh_local(vec_n.clone());

    let contains_input = c.contains(&n, &bnd, &x);
    let (hx_id, hx) = b.fresh_local(contains_input.clone());

    // Build the body: fun j : Fin m => ibp_linear_per_component m n W b B x hx j
    let fin_m = Expr::app(c.fin.clone(), m.clone());
    let inner = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = ch.fresh_local(fin_m.clone());
        // ibp_linear_per_component m n W b B x hx j
        let body = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(ibp_per_component.clone(), m.clone()),
                                    n.clone(),
                                ),
                                w.clone(),
                            ),
                            bias.clone(),
                        ),
                        bnd.clone(),
                    ),
                    x.clone(),
                ),
                hx.clone(),
            ),
            j,
        );
        let r = ch.mk_lam(j_id, BinderInfo::Default, fin_m.clone(), body);
        ch.finish_child(r)
    };

    let e = b.mk_lam(hx_id, BinderInfo::Default, contains_input, inner);
    let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_lam(bias_id, BinderInfo::Default, vec_m, e);
    let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build T80 type: contains B x -> contains (ibp_linear_bounds ...) (linear_output ...).
fn build_ibp_linear_sound_type(c: &IbpLinearConsts) -> Expr {
    let ibp_linear_bounds = Expr::const_(Name::from_string("NNVerify.ibp_linear_bounds"), vec![]);
    let linear_output = Expr::const_(Name::from_string("NNVerify.linear_output"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let vec_m = c.vec_of(m.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());

    let (w_id, w) = b.fresh_local(mat_mn.clone());
    let (bias_id, bias) = b.fresh_local(vec_m.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let (x_id, x) = b.fresh_local(vec_n.clone());

    let contains_input = c.contains(&n, &bnd, &x);

    // ibp_linear_bounds m n W b B
    let output_bounds = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ibp_linear_bounds, m.clone()), n.clone()),
                w.clone(),
            ),
            bias.clone(),
        ),
        bnd.clone(),
    );

    // linear_output m n W b x
    let output_val = Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::app(linear_output, m.clone()), n.clone()), w),
            bias,
        ),
        x,
    );

    let contains_output = c.contains(&m, &output_bounds, &output_val);

    let (hx_id, _) = b.fresh_local(contains_input.clone());
    let e = b.mk_pi(hx_id, BinderInfo::Default, contains_input, contains_output);
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_pi(bias_id, BinderInfo::Default, vec_m, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register T80: `NNVerify.ibp_linear_sound`
    ///
    /// Theorem with proof by W+/W- decomposition. The proof composes:
    /// - `w_decompose`: W[i,j] = W+[i,j] + W-[i,j]
    /// - `Fin.sum_add`: split sum of (W+*x + W-*x) into separate sums
    /// - `Fin.sum_le` + `mul_nonneg_le_left`: W+[i,j]*x[j] <= W+[i,j]*u[j]
    /// - `Fin.sum_le` + `mul_nonpos_le_left`: W-[i,j]*u[j] <= W-[i,j]*x[j]
    /// - `add_le_add` + `le_of_eq_of_le`: combine into per-index bound
    /// - `And.intro`: join lower and upper bounds
    pub(super) fn register_ibp_linear_sound_impl(
        &mut self,
        c: &IbpLinearConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.ibp_linear_sound"))
            .is_some()
        {
            return Ok(());
        }
        self.register_linear_output(c)?;
        self.register_ibp_linear_per_component(c)?;
        let thm_type = build_ibp_linear_sound_type(c);
        let proof_value = build_ibp_linear_sound_proof(c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ibp_linear_sound"),
            level_params: vec![],
            type_: thm_type,
            value: proof_value,
        })
    }

    /// Register `NNVerify.ibp_linear_per_component`:
    /// Per-index proof that input containment implies output containment.
    ///
    /// This axiom factors out the per-component proof for the main theorem.
    fn register_ibp_linear_per_component(&mut self, c: &IbpLinearConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.ibp_linear_per_component"))
            .is_some()
        {
            return Ok(());
        }
        let ibp_linear_bounds =
            Expr::const_(Name::from_string("NNVerify.ibp_linear_bounds"), vec![]);
        let linear_output = Expr::const_(Name::from_string("NNVerify.linear_output"), vec![]);
        let and = Expr::const_(Name::from_string("And"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let vec_m = c.vec_of(m.clone());
            let vec_n = c.vec_of(n.clone());
            let ib_n = c.ib_of(n.clone());

            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let (bias_id, bias) = b.fresh_local(vec_m.clone());
            let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());

            let contains_input = c.contains(&n, &bnd, &x);
            let (hx_id, _hx) = b.fresh_local(contains_input.clone());

            // ibp_linear_bounds m n W b B
            let output_bounds = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(ibp_linear_bounds, m.clone()), n.clone()),
                        w.clone(),
                    ),
                    bias.clone(),
                ),
                bnd,
            );
            // linear_output m n W b x
            let output_val = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(Expr::app(linear_output, m.clone()), n.clone()), w),
                    bias,
                ),
                x,
            );

            let bounds_lower = Expr::proj(
                Name::from_string("NNVerify.IntervalBounds"),
                0,
                output_bounds.clone(),
            );
            let bounds_upper = Expr::proj(
                Name::from_string("NNVerify.IntervalBounds"),
                1,
                output_bounds,
            );

            let fin_m = Expr::app(c.fin.clone(), m.clone());
            let (j_id, j) = b.fresh_local(fin_m.clone());
            let lo_j = Expr::app(bounds_lower, j.clone());
            let hi_j = Expr::app(bounds_upper, j.clone());
            let out_j = Expr::app(output_val, j);

            let conj = Expr::app(
                Expr::app(and.clone(), c.rat_le(lo_j, out_j.clone())),
                c.rat_le(out_j, hi_j),
            );

            let e = b.mk_pi(j_id, BinderInfo::Default, fin_m, conj);
            let e = b.mk_pi(hx_id, BinderInfo::Default, contains_input, e);
            let e = b.mk_pi(x_id, BinderInfo::Default, vec_n, e);
            let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
            let e = b.mk_pi(bias_id, BinderInfo::Default, vec_m, e);
            let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        // CONSTRUCTIVE PROOF (T80 unlock, #3490 follow-up): `ibp_linear_bounds`
        // is now a faithful reducible `Declaration::Definition` returning
        // `IntervalBounds.mk m lo' hi' valid`, so the `IntervalBounds`
        // projections in this statement proj-reduce: `(...).lower j ≡
        // Σ_i (w_pos j i · lo i + w_neg j i · hi i) + b j`, `(...).upper j ≡
        // Σ_i (w_neg j i · lo i + w_pos j i · hi i) + b j`, and `linear_output`
        // gives `out j ≡ Σ_i (W j i · x i) + b j`. The per-index goal is then a
        // genuine sorry-free `And` of two sum-level inequalities proved by
        // per-summand monotonicity (`w_pos_nonneg`/`w_neg_nonpos`/`B.valid` via
        // `mul_nonneg_le_left`/`mul_nonpos_le_left`), `Fin.sum_le`, and the
        // `w_decompose` recombination (`W = w_pos + w_neg`, lifted through
        // `congrArg` + `Rat.right_distrib`). Closure ⊆ those constructive
        // Theorems ∪ `Fin.sum_le` ∪ foundational `Eq`/`And`/`Rat` lemmas — no
        // domain-specific axiom. See
        // `nn_verify_ibp_linear_per_component_proof::build_ibp_linear_per_component_proof`.
        let value =
            super::nn_verify_ibp_linear_per_component_proof::build_ibp_linear_per_component_proof(
                c,
            );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ibp_linear_per_component"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register `NNVerify.linear_output`:
    /// `(m n : Nat) -> NNMat m n -> NNVec m -> NNVec n -> NNVec m`
    ///
    /// Computes the linear layer output: `(fun j => Fin.sum n (fun i => W j i * x i) + b j)`.
    fn register_linear_output(&mut self, c: &IbpLinearConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.linear_output"))
            .is_some()
        {
            return Ok(());
        }

        // Type: (m n : Nat) -> NNMat m n -> NNVec m -> NNVec n -> NNVec m
        let lo_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let vec_m = c.vec_of(m.clone());
            let vec_n = c.vec_of(n.clone());
            let result = c.vec_of(m.clone());
            let (w_id, _) = b.fresh_local(mat_mn.clone());
            let (bias_id, _) = b.fresh_local(vec_m.clone());
            let (x_id, _) = b.fresh_local(vec_n.clone());
            let e = b.mk_pi(x_id, BinderInfo::Default, vec_n, result);
            let e = b.mk_pi(bias_id, BinderInfo::Default, vec_m, e);
            let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // Value: fun m n W b x => fun j : Fin m =>
        //          Rat.add (Fin.sum n (fun i : Fin n => Rat.mul (W j i) (x i))) (b j)
        let lo_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let vec_m = c.vec_of(m.clone());
            let vec_n = c.vec_of(n.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let (bias_id, bias) = b.fresh_local(vec_m.clone());
            let (x_id, x) = b.fresh_local(vec_n.clone());

            let fin_m = Expr::app(c.fin.clone(), m.clone());
            let inner = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (j_id, j) = ch.fresh_local(fin_m.clone());
                let w_j = Expr::app(w.clone(), j.clone());
                let bias_j = Expr::app(bias.clone(), j.clone());
                let body = build_linear_output(c, &ch, &n, &w_j, &bias_j, &x);
                let r = ch.mk_lam(j_id, BinderInfo::Default, fin_m.clone(), body);
                ch.finish_child(r)
            };

            let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, inner);
            let e = b.mk_lam(bias_id, BinderInfo::Default, vec_m, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.linear_output"),
            level_params: vec![],
            type_: lo_type,
            value: lo_value,
            is_reducible: true,
        })
    }
}
