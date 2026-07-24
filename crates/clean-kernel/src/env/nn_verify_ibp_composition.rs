// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T82: IBP composition — layer chaining proof.
//!
//! Proves that IBP bounds compose: if linear layer f maps bounds B1 to B2,
//! and ReLU layer g maps B2 to B3, then g . f maps B1 to B3.
//!
//! This is the capstone of the IBP formalization — it chains T80 (linear)
//! and T81 (ReLU) into a complete single-layer pipeline proof.
//!
//! ## Theorem
//!
//! `NNVerify.ibp_composition`:
//! ```text
//! forall (m n : Nat) (W : NNMat m n) (b : NNVec m) (B : IB n) (x : NNVec n),
//!   contains B x ->
//!   contains (ibp_relu_bounds m (ibp_linear_bounds m n W b B))
//!            (relu_vec m (linear_output m n W b x))
//! ```
//!
//! ## Proof
//!
//! Pure function composition of T80 and T81:
//! ```text
//! fun m n W b B x hx =>
//!   ibp_relu_soundness m
//!     (ibp_linear_bounds m n W b B)
//!     (linear_output m n W b x)
//!     (ibp_linear_sound m n W b B x hx)
//! ```
//!
//! ## Axiom Budget
//!
//! Zero new axioms. The proof is fully constructive, composing
//! the constructive proofs of T80 and T81.
//!
//! Part of #3246.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared constants for T82 proof construction.
struct T82Consts {
    nat: Expr,
    nn_vec: Expr,
    nn_mat: Expr,
    ib: Expr,
    ib_contains: Expr,
    ibp_linear_bounds: Expr,
    linear_output: Expr,
    ibp_relu_bounds: Expr,
    relu_vec: Expr,
    ibp_linear_sound: Expr,
    ibp_relu_soundness: Expr,
}

impl T82Consts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
            ibp_linear_bounds: Expr::const_(
                Name::from_string("NNVerify.ibp_linear_bounds"),
                vec![],
            ),
            linear_output: Expr::const_(Name::from_string("NNVerify.linear_output"), vec![]),
            ibp_relu_bounds: Expr::const_(Name::from_string("NNVerify.ibp_relu_bounds"), vec![]),
            relu_vec: Expr::const_(Name::from_string("NNVerify.relu_vec"), vec![]),
            ibp_linear_sound: Expr::const_(Name::from_string("NNVerify.ibp_linear_sound"), vec![]),
            ibp_relu_soundness: Expr::const_(
                Name::from_string("NNVerify.ibp_relu_soundness"),
                vec![],
            ),
        }
    }

    fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    fn mat_of(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m), n)
    }

    fn ib_of(&self, d: Expr) -> Expr {
        Expr::app(self.ib.clone(), d)
    }

    fn contains(&self, d: &Expr, b: &Expr, x: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_contains.clone(), d.clone()), b.clone()),
            x.clone(),
        )
    }

    /// `ibp_linear_bounds m n W b B`
    fn apply_ibp_linear_bounds(&self, m: &Expr, n: &Expr, w: Expr, bias: Expr, bnd: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(self.ibp_linear_bounds.clone(), m.clone()),
                        n.clone(),
                    ),
                    w,
                ),
                bias,
            ),
            bnd,
        )
    }

    /// `linear_output m n W b x`
    fn apply_linear_output(&self, m: &Expr, n: &Expr, w: Expr, bias: Expr, x: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(self.linear_output.clone(), m.clone()), n.clone()),
                    w,
                ),
                bias,
            ),
            x,
        )
    }

    /// `ibp_linear_sound m n W b B x hx`
    fn apply_ibp_linear_sound(
        &self,
        m: &Expr,
        n: &Expr,
        w: Expr,
        bias: Expr,
        bnd: Expr,
        x: Expr,
        hx: Expr,
    ) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(self.ibp_linear_sound.clone(), m.clone()),
                                n.clone(),
                            ),
                            w,
                        ),
                        bias,
                    ),
                    bnd,
                ),
                x,
            ),
            hx,
        )
    }
}

/// Build the T82 theorem type:
/// ```text
/// forall (m n : Nat) (W : NNMat m n) (b : NNVec m) (B : IB n) (x : NNVec n),
///   contains B x ->
///   contains (ibp_relu_bounds m (ibp_linear_bounds m n W b B))
///            (relu_vec m (linear_output m n W b x))
/// ```
fn build_t82_type(c: &T82Consts) -> Expr {
    let mut db = EnvDeclBuilder::new();
    let (m_id, m) = db.fresh_local(c.nat.clone());
    let (n_id, n) = db.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let vec_m = c.vec_of(m.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());

    let (w_id, w) = db.fresh_local(mat_mn.clone());
    let (bias_id, bias) = db.fresh_local(vec_m.clone());
    let (bnd_id, bnd) = db.fresh_local(ib_n.clone());
    let (x_id, x) = db.fresh_local(vec_n.clone());

    let contains_input = c.contains(&n, &bnd, &x);
    let linear_bounds = c.apply_ibp_linear_bounds(&m, &n, w.clone(), bias.clone(), bnd.clone());
    let output_bounds = Expr::app(
        Expr::app(c.ibp_relu_bounds.clone(), m.clone()),
        linear_bounds,
    );
    let linear_out = c.apply_linear_output(&m, &n, w, bias, x);
    let relu_out = Expr::app(Expr::app(c.relu_vec.clone(), m.clone()), linear_out);
    let contains_output = c.contains(&m, &output_bounds, &relu_out);

    let (hx_id, _) = db.fresh_local(contains_input.clone());
    let e = db.mk_pi(hx_id, BinderInfo::Default, contains_input, contains_output);
    let e = db.mk_pi(x_id, BinderInfo::Default, vec_n, e);
    let e = db.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = db.mk_pi(bias_id, BinderInfo::Default, vec_m, e);
    let e = db.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
    let e = db.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = db.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    db.finish(e)
}

/// Build the T82 proof body (inner lambda term after parameter binding).
///
/// Composes T80 and T81: applies `ibp_relu_soundness` to the result
/// of `ibp_linear_sound`.
fn build_t82_body(c: &T82Consts, m: &Expr, n: &Expr, args: &T82ProofArgs) -> Expr {
    let linear_bounds =
        c.apply_ibp_linear_bounds(m, n, args.w.clone(), args.bias.clone(), args.bnd.clone());
    let linear_out = c.apply_linear_output(m, n, args.w.clone(), args.bias.clone(), args.x.clone());
    let t80_applied = c.apply_ibp_linear_sound(
        m,
        n,
        args.w.clone(),
        args.bias.clone(),
        args.bnd.clone(),
        args.x.clone(),
        args.hx.clone(),
    );
    // ibp_relu_soundness m linear_bounds linear_out t80_applied
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(c.ibp_relu_soundness.clone(), m.clone()),
                linear_bounds,
            ),
            linear_out,
        ),
        t80_applied,
    )
}

/// Proof-local variable references for T82.
struct T82ProofArgs {
    w: Expr,
    bias: Expr,
    bnd: Expr,
    x: Expr,
    hx: Expr,
}

/// Build the T82 proof term (function composition of T80 and T81).
fn build_t82_proof(c: &T82Consts) -> Expr {
    let mut db = EnvDeclBuilder::new();
    let (m_id, m) = db.fresh_local(c.nat.clone());
    let (n_id, n) = db.fresh_local(c.nat.clone());
    let mat_mn = c.mat_of(m.clone(), n.clone());
    let vec_m = c.vec_of(m.clone());
    let vec_n = c.vec_of(n.clone());
    let ib_n = c.ib_of(n.clone());

    let (w_id, w) = db.fresh_local(mat_mn.clone());
    let (bias_id, bias) = db.fresh_local(vec_m.clone());
    let (bnd_id, bnd) = db.fresh_local(ib_n.clone());
    let (x_id, x) = db.fresh_local(vec_n.clone());
    let contains_input = c.contains(&n, &bnd, &x);
    let (hx_id, hx) = db.fresh_local(contains_input.clone());

    let args = T82ProofArgs {
        w,
        bias,
        bnd,
        x,
        hx,
    };
    let body = build_t82_body(c, &m, &n, &args);

    let e = db.mk_lam(hx_id, BinderInfo::Default, contains_input, body);
    let e = db.mk_lam(x_id, BinderInfo::Default, vec_n, e);
    let e = db.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
    let e = db.mk_lam(bias_id, BinderInfo::Default, vec_m, e);
    let e = db.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
    let e = db.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = db.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    db.finish(e)
}

impl Environment {
    /// Initialize T82 (IBP composition — layer chaining proof).
    ///
    /// Depends on:
    /// - `init_nn_verify_ibp_linear()` (T80: linear layer soundness)
    /// - `init_nn_verify_relu()` (T81: ReLU soundness)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_ibp_composition_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_ibp_composition(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_ibp_composition_init {
            return Ok(());
        }
        self.init_nn_verify_ibp_linear()?;
        self.init_nn_verify_relu()?;

        self.register_ibp_composition()?;

        self.nn_verify_ibp_composition_init = true;
        Ok(())
    }

    /// Register `NNVerify.ibp_composition` as a `Declaration::Theorem`.
    ///
    /// T82: if linear layer maps bounds B to B', and ReLU maps B' to B'',
    /// then ReLU . linear maps B to B''.
    fn register_ibp_composition(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.ibp_composition"))
            .is_some()
        {
            return Ok(());
        }
        let c = T82Consts::new();
        let thm_type = build_t82_type(&c);
        let proof_value = build_t82_proof(&c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ibp_composition"),
            level_params: vec![],
            type_: thm_type,
            value: proof_value,
        })
    }
}
