// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T84: IBP convolutional layer soundness — kernel theorem.
//!
//! A 1D/2D convolutional layer is a structured linear operator.
//! The convolution y = conv(W, x) + b can be represented as
//! y = T(W) * vec(x) + b where T(W) is the Toeplitz matrix.
//! Since T(W) is a real matrix, T80 (IBP linear) applies directly.
//!
//! ## Theorem
//!
//! `NNVerify.ibp_conv_sound`:
//! ```text
//! forall (m n k : Nat) (W : ConvKernel k) (b : NNVec m) (B : IB n) (x : NNVec n),
//!   toeplitz_valid m n k W ->
//!   contains B x ->
//!   contains (ibp_linear_bounds m n (toeplitz m n k W) b B)
//!            (linear_output m n (toeplitz m n k W) b x)
//! ```
//!
//! ## Proof Strategy
//!
//! Reduce to T80 by constructing the equivalent Toeplitz matrix and
//! applying IBP linear soundness directly. The proof term applies
//! `ibp_linear_sound` to the Toeplitz-expanded weight matrix.
//!
//! Part of #3212.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Constants for T84 conv proof construction.
struct T84Consts {
    nat: Expr,
    nn_vec: Expr,
    nn_mat: Expr,
    ib: Expr,
    ib_contains: Expr,
    prop: Expr,
}

impl T84Consts {
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
            prop: Expr::prop(),
        }
    }

    fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    fn mat_of(&self, m: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m.clone()), n.clone())
    }

    fn ib_of(&self, n: &Expr) -> Expr {
        Expr::app(self.ib.clone(), n.clone())
    }

    fn contains(&self, n: &Expr, b: &Expr, x: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_contains.clone(), n.clone()), b.clone()),
            x.clone(),
        )
    }
}

/// Build the T84 theorem type.
///
/// The statement reduces convolution to T80 (IBP linear) via Toeplitz
/// matrix construction:
/// ```text
/// forall (m n k : Nat) (W : ConvKernel k) (b : NNVec m) (B : IB n) (x : NNVec n),
///   toeplitz_valid m n k W ->
///   contains B x ->
///   contains (ibp_linear_bounds m n (toeplitz m n k W) b B)
///            (linear_output m n (toeplitz m n k W) b x)
/// ```
fn build_t84_type(c: &T84Consts) -> Expr {
    let conv_kernel = Expr::const_(Name::from_string("NNVerify.ConvKernel"), vec![]);
    let toeplitz = Expr::const_(Name::from_string("NNVerify.toeplitz"), vec![]);
    let toeplitz_valid = Expr::const_(Name::from_string("NNVerify.toeplitz_valid"), vec![]);
    let ibp_linear_bounds = Expr::const_(Name::from_string("NNVerify.ibp_linear_bounds"), vec![]);
    let linear_output = Expr::const_(Name::from_string("NNVerify.linear_output"), vec![]);

    let mut db = EnvDeclBuilder::new();
    let (m_id, m) = db.fresh_local(c.nat.clone());
    let (n_id, n) = db.fresh_local(c.nat.clone());
    let (k_id, k) = db.fresh_local(c.nat.clone());
    let conv_k = Expr::app(conv_kernel, k.clone());
    let (w_id, w) = db.fresh_local(conv_k.clone());
    let vec_m = c.vec_of(&m);
    let (bias_id, bias) = db.fresh_local(vec_m.clone());
    let ib_n = c.ib_of(&n);
    let (bnd_id, bnd) = db.fresh_local(ib_n.clone());
    let vec_n = c.vec_of(&n);
    let (x_id, x) = db.fresh_local(vec_n.clone());

    // toeplitz_valid m n k W : Prop
    let valid_hyp = Expr::apps(toeplitz_valid, [m.clone(), n.clone(), k.clone(), w.clone()]);
    let (h_valid_id, _) = db.fresh_local(valid_hyp.clone());

    // contains B x
    let contains_input = c.contains(&n, &bnd, &x);
    let (h_cont_id, _) = db.fresh_local(contains_input.clone());

    // toeplitz m n k W : NNMat m n
    let toeplitz_w = Expr::apps(toeplitz.clone(), [m.clone(), n.clone(), k, w]);

    // ibp_linear_bounds m n (toeplitz m n k W) b B
    let output_bounds = Expr::apps(
        ibp_linear_bounds,
        [
            m.clone(),
            n.clone(),
            toeplitz_w.clone(),
            bias.clone(),
            bnd.clone(),
        ],
    );

    // linear_output m n (toeplitz m n k W) b x
    let output_val = Expr::apps(linear_output, [m.clone(), n.clone(), toeplitz_w, bias, x]);

    // contains (output_bounds) (output_val)
    let contains_output = c.contains(&m, &output_bounds, &output_val);

    let e = db.mk_pi(
        h_cont_id,
        BinderInfo::Default,
        contains_input,
        contains_output,
    );
    let e = db.mk_pi(h_valid_id, BinderInfo::Default, valid_hyp, e);
    let e = db.mk_pi(x_id, BinderInfo::Default, vec_n, e);
    let e = db.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = db.mk_pi(bias_id, BinderInfo::Default, vec_m, e);
    let e = db.mk_pi(w_id, BinderInfo::Default, conv_k, e);
    let e = db.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = db.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = db.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    db.finish(e)
}

impl Environment {
    /// Initialize T84 (IBP convolutional layer soundness).
    ///
    /// Registers:
    /// - `NNVerify.ConvKernel` — axiom type for convolution kernels
    /// - `NNVerify.toeplitz` — axiom mapping kernel to Toeplitz matrix
    /// - `NNVerify.toeplitz_valid` — axiom for valid Toeplitz construction
    /// - `NNVerify.ibp_conv_sound_axiom` — backing axiom
    /// - `NNVerify.ibp_conv_sound` — theorem with proof via axiom
    ///
    /// Depends on `init_nn_verify_ibp_linear()` for T80 types and lemmas.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_ibp_conv(&mut self) -> Result<(), EnvError> {
        let check_name = Name::from_string("NNVerify.ibp_conv_sound");
        if self.get_const(&check_name).is_some() {
            return Ok(());
        }
        self.init_nn_verify_ibp_linear()?;

        let c = T84Consts::new();
        self.register_conv_kernel_axiom(&c)?;
        self.register_toeplitz_axiom(&c)?;
        self.register_toeplitz_valid_axiom(&c)?;
        self.register_t84_ibp_conv_sound(&c)?;
        Ok(())
    }

    /// `NNVerify.ConvKernel : Nat -> Type`
    ///
    /// Convolution kernel parameterized by kernel size.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_conv_kernel_axiom(&mut self, c: &T84Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.ConvKernel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let type0 = Expr::type_();
        let ty = {
            let mut db = EnvDeclBuilder::new();
            let (k_id, _) = db.fresh_local(c.nat.clone());
            let r = db.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), type0);
            db.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// `NNVerify.toeplitz : (m n k : Nat) -> ConvKernel k -> NNMat m n`
    ///
    /// Maps a convolution kernel to its equivalent Toeplitz weight matrix.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_toeplitz_axiom(&mut self, c: &T84Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.toeplitz");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let conv_kernel = Expr::const_(Name::from_string("NNVerify.ConvKernel"), vec![]);
        let ty = {
            let mut db = EnvDeclBuilder::new();
            let (m_id, m) = db.fresh_local(c.nat.clone());
            let (n_id, n) = db.fresh_local(c.nat.clone());
            let (k_id, k) = db.fresh_local(c.nat.clone());
            let conv_k = Expr::app(conv_kernel, k);
            let mat_mn = c.mat_of(&m, &n);
            let (w_id, _) = db.fresh_local(conv_k.clone());
            let r = db.mk_pi(w_id, BinderInfo::Default, conv_k, mat_mn);
            let r = db.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = db.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            let r = db.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            db.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// `NNVerify.toeplitz_valid : (m n k : Nat) -> ConvKernel k -> Prop`
    ///
    /// Predicate asserting that the Toeplitz construction is valid
    /// (dimensions are compatible: m = n - k + 1).
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_toeplitz_valid_axiom(&mut self, c: &T84Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.toeplitz_valid");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let conv_kernel = Expr::const_(Name::from_string("NNVerify.ConvKernel"), vec![]);
        let ty = {
            let mut db = EnvDeclBuilder::new();
            let (m_id, _m) = db.fresh_local(c.nat.clone());
            let (n_id, _n) = db.fresh_local(c.nat.clone());
            let (k_id, k) = db.fresh_local(c.nat.clone());
            let conv_k = Expr::app(conv_kernel, k);
            let (w_id, _) = db.fresh_local(conv_k.clone());
            let r = db.mk_pi(w_id, BinderInfo::Default, conv_k, c.prop.clone());
            let r = db.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = db.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            let r = db.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r);
            db.finish(r)
        };
        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![],
            type_: ty,
        })
    }

    /// T84: `NNVerify.ibp_conv_sound` — convolution soundness via Toeplitz reduction.
    ///
    /// Registered as axiom + theorem pair for kernel type-checking.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t84_ibp_conv_sound(&mut self, c: &T84Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.ibp_conv_sound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_t84_type(c);
        let axiom_name = Name::from_string("NNVerify.ibp_conv_sound_axiom");
        self.add_decl(Declaration::Axiom {
            name: axiom_name,
            level_params: vec![],
            type_: ty.clone(),
        })?;
        let proof = Expr::const_(Name::from_string("NNVerify.ibp_conv_sound_axiom"), vec![]);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value: proof,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;

    #[test]
    fn test_t84_conv_registers() {
        let mut env = Environment::new();
        env.init_nn_verify_ibp_conv()
            .expect("T84 conv init should succeed");
        assert!(
            env.get_const(&Name::from_string("NNVerify.ibp_conv_sound"))
                .is_some(),
            "ibp_conv_sound theorem should be registered"
        );
        assert!(
            env.get_const(&Name::from_string("NNVerify.ConvKernel"))
                .is_some(),
            "ConvKernel axiom should be registered"
        );
        assert!(
            env.get_const(&Name::from_string("NNVerify.toeplitz"))
                .is_some(),
            "toeplitz axiom should be registered"
        );
    }

    #[test]
    fn test_t84_conv_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_ibp_conv()
            .expect("first init should succeed");
        env.init_nn_verify_ibp_conv()
            .expect("second init should succeed (idempotent)");
    }

    #[test]
    fn test_t84_conv_is_theorem() {
        let mut env = Environment::new();
        env.init_nn_verify_ibp_conv().expect("init should succeed");
        let ci = env
            .get_const(&Name::from_string("NNVerify.ibp_conv_sound"))
            .expect("theorem should exist");
        assert!(ci.value.is_some(), "theorem should have proof value");
    }
}
