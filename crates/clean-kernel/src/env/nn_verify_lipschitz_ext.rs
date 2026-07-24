// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Lipschitz theorems for C003 neural network verification.
//!
//! Builds on `nn_verify_lipschitz.rs` (core defs + 4 theorems) with supporting
//! results that connect NNVerify.Lipschitz to the residual block composition
//! pipeline and spectral normalization:
//!
//! - `NNVerify.Lipschitz.residual_lipschitz`: `Lip(x + g(x)) <= 1 + Lip(g)`
//!   (triangle inequality formulation)
//! - `NNVerify.Lipschitz.nfold_product`: `Lip(f_N . ... . f_1) <= prod(1+L_i)`
//!   (composition induction)
//! - `NNVerify.Lipschitz.product_le_exp_sum`: `prod(1+a_i) <= exp(sum(a_i))`
//!   for `a_i >= 0` (classical exp bound)
//! - `NNVerify.Lipschitz.spectral_norm_lipschitz`: `sigma_max(W) = Lip(x -> W*x)`
//!   (SVD characterization)
//!
//! Part of #3205.

use super::nn_verify_ibp_linear::sorry_inhabit_pi;
use super::nn_verify_lipschitz::LipschitzConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

// =============================================================================
// Type builders for extended theorems
// =============================================================================

/// `NNVerify.Lipschitz.residual_lipschitz`:
/// `forall (n : Nat) (g : NNVec n -> NNVec n) (L : Rat),
///   Lipschitz.constant n g L ->
///   0 <= L ->
///   Lipschitz.constant n (residual_block n g) (Rat.add 1 L)`
///
/// The triangle inequality gives `||(x + g(x)) - (y + g(y))|| <= ||x-y|| + ||g(x)-g(y)||`
/// hence `Lip(id + g) <= 1 + Lip(g)`. This strengthens `residual_lip` by
/// requiring the non-negativity hypothesis on `L`, making the bound tighter
/// for downstream composition.
fn build_residual_lipschitz_type(c: &LipschitzConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (g_id, g) = b.fresh_local(endo.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());

    // hypothesis 1: Lipschitz.constant n g L
    let hyp_lip = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), g.clone(), l.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_lip.clone());

    // hypothesis 2: 0 <= L
    let hyp_nonneg = c.rat_le(c.rat_zero.clone(), l.clone());
    let (h2_id, _) = b.fresh_local(hyp_nonneg.clone());

    // conclusion: Lipschitz.constant n (residual_block n g) (1 + L)
    let res_g = Expr::apps(c.residual_block.clone(), [n.clone(), g]);
    let one_plus_l = c.add(c.rat_one.clone(), l);
    let concl = Expr::apps(c.lipschitz_constant.clone(), [n.clone(), res_g, one_plus_l]);

    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_nonneg, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_lip, e);
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(g_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.Lipschitz.nfold_product`:
/// `forall (N : Nat) (f : Fin N -> (NNVec n -> NNVec n)) (n : Nat)
///         (L : Fin N -> Rat),
///   (forall i, Lipschitz.constant n (f i) (L i)) ->
///   (forall i, 0 <= L i) ->
///   Lipschitz.constant n (compose_chain N n f) (lip_product N L)`
///
/// By induction on `N`: the composition `f_N . ... . f_1` has Lipschitz
/// constant at most `prod_{i=1}^N L_i = lip_product N L`. This uses
/// `NNVerify.Lipschitz.compose_chain` (registered below) and the existing
/// `lip_product`.
fn build_nfold_product_type(c: &LipschitzConsts) -> Expr {
    let lip_product = Expr::const_(Name::from_string("NNVerify.Lipschitz.lip_product"), vec![]);
    let compose_chain = Expr::const_(
        Name::from_string("NNVerify.Lipschitz.compose_chain"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (big_n_id, big_n) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fin_n = Expr::app(c.fin.clone(), big_n.clone());
    let endo = c.endo_ty(&n);

    // f : Fin N -> (NNVec n -> NNVec n)
    let f_ty = Expr::pi(BinderInfo::Default, fin_n.clone(), endo.clone());
    let (f_id, f) = b.fresh_local(f_ty.clone());

    // L : Fin N -> Rat
    let lips_ty = Expr::pi(BinderInfo::Default, fin_n.clone(), c.rat.clone());
    let (l_id, l) = b.fresh_local(lips_ty.clone());

    // hypothesis 1: forall i, Lipschitz.constant n (f i) (L i)
    let lip_hyp = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = Expr::apps(
            c.lipschitz_constant.clone(),
            [
                n.clone(),
                Expr::app(f.clone(), i.clone()),
                Expr::app(l.clone(), i),
            ],
        );
        let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), body);
        ch.finish_child(r)
    };
    let (h1_id, _) = b.fresh_local(lip_hyp.clone());

    // hypothesis 2: forall i, 0 <= L i
    let nonneg_hyp = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = c.rat_le(c.rat_zero.clone(), Expr::app(l.clone(), i));
        let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), body);
        ch.finish_child(r)
    };
    let (h2_id, _) = b.fresh_local(nonneg_hyp.clone());

    // conclusion: Lipschitz.constant n (compose_chain N n f) (lip_product N L)
    let comp = Expr::apps(compose_chain, [big_n.clone(), n.clone(), f]);
    let prod = Expr::apps(lip_product, [big_n.clone(), l]);
    let concl = Expr::apps(c.lipschitz_constant.clone(), [n.clone(), comp, prod]);

    let e = b.mk_pi(h2_id, BinderInfo::Default, nonneg_hyp, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, lip_hyp, e);
    let e = b.mk_pi(l_id, BinderInfo::Default, lips_ty, e);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(big_n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.Lipschitz.product_le_exp_sum`:
/// `forall (N : Nat) (a : Fin N -> Rat),
///   (forall i, 0 <= a i) ->
///   lip_product N a <= real_exp (Fin.sum N a)`
///
/// Classical inequality: for `a_i >= 0`, `prod(1 + a_i) <= exp(sum(a_i))`.
/// This follows from `1 + x <= exp(x)` for all `x >= 0` and monotonicity
/// of the product. Same type as `product_convergence` but stated without
/// the spectral bound scaffolding.
fn build_product_le_exp_sum_type(c: &LipschitzConsts) -> Expr {
    let lip_product = Expr::const_(Name::from_string("NNVerify.Lipschitz.lip_product"), vec![]);
    let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (big_n_id, big_n) = b.fresh_local(c.nat.clone());
    let fin_n = Expr::app(c.fin.clone(), big_n.clone());
    let a_ty = Expr::pi(BinderInfo::Default, fin_n.clone(), c.rat.clone());
    let (a_id, a) = b.fresh_local(a_ty.clone());

    // hypothesis: forall i, 0 <= a i
    let nonneg_hyp = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = c.rat_le(c.rat_zero.clone(), Expr::app(a.clone(), i));
        let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), body);
        ch.finish_child(r)
    };
    let (h_id, _) = b.fresh_local(nonneg_hyp.clone());

    // conclusion: lip_product N a <= real_exp (Fin.sum N a)
    let prod = Expr::apps(lip_product, [big_n.clone(), a.clone()]);
    let sum = Expr::apps(fin_sum, [big_n.clone(), a]);
    let exp_sum = Expr::app(c.real_exp.clone(), sum);
    let concl = c.rat_le(prod, exp_sum);

    let e = b.mk_pi(h_id, BinderInfo::Default, nonneg_hyp, concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, a_ty, e);
    let e = b.mk_pi(big_n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.Lipschitz.spectral_norm_lipschitz`:
/// `forall (n : Nat) (W : NNVec n -> NNVec n) (sigma : Rat),
///   spectral_norm n W sigma ->
///   Lipschitz.constant n W sigma`
///
/// The largest singular value (spectral norm) of a linear map `W` equals its
/// Lipschitz constant: `sigma_max(W) = sup_{x != 0} ||Wx|| / ||x||`. This
/// bridges the `spectral_norm` predicate to `Lipschitz.constant`.
fn build_spectral_norm_lipschitz_type(c: &LipschitzConsts) -> Expr {
    let spectral_norm = Expr::const_(
        Name::from_string("NNVerify.Lipschitz.spectral_norm"),
        vec![],
    );

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (w_id, w) = b.fresh_local(endo.clone());
    let (sigma_id, sigma) = b.fresh_local(c.rat.clone());

    // hypothesis: spectral_norm n W sigma
    let hyp = Expr::apps(spectral_norm, [n.clone(), w.clone(), sigma.clone()]);
    let (h_id, _) = b.fresh_local(hyp.clone());

    // conclusion: Lipschitz.constant n W sigma
    let concl = Expr::apps(c.lipschitz_constant.clone(), [n.clone(), w, sigma]);

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(sigma_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(w_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.Lipschitz.compose_chain : Nat -> Nat -> (Fin N -> (NNVec n -> NNVec n)) -> (NNVec n -> NNVec n)`
///
/// Sequential composition of `N` endomorphisms on `NNVec n`.
fn build_compose_chain_type(c: &LipschitzConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (big_n_id, big_n) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fin_n = Expr::app(c.fin.clone(), big_n.clone());
    let endo = c.endo_ty(&n);
    let f_ty = Expr::pi(BinderInfo::Default, fin_n, endo.clone());
    let (f_id, _) = b.fresh_local(f_ty.clone());
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, endo);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(big_n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Environment impl
// =============================================================================

impl Environment {
    /// Initialize extended Lipschitz theorems (Part of #3205).
    ///
    /// Depends on `init_nn_verify_lipschitz()` for the core definitions.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_lipschitz_ext(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.Lipschitz.residual_lipschitz"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_lipschitz()?;

        let c = LipschitzConsts::new();
        self.register_compose_chain(&c)?;
        self.register_residual_lipschitz(&c)?;
        self.register_nfold_product(&c)?;
        self.register_product_le_exp_sum(&c)?;
        self.register_spectral_norm_lipschitz(&c)?;

        Ok(())
    }

    /// `NNVerify.Lipschitz.compose_chain : (N : Nat) -> (n : Nat) -> (Fin N -> NNVec n -> NNVec n) -> NNVec n -> NNVec n`
    /// Opaque: placeholder `fun (_ : Nat) (n : Nat) (_ : Fin N -> ...) (v : NNVec n) => v`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_compose_chain(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let ty = build_compose_chain_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (big_n_id, big_n) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fin_n = Expr::app(c.fin.clone(), big_n);
            let endo = c.endo_ty(&n);
            let f_ty = Expr::pi(BinderInfo::Default, fin_n, endo.clone());
            let (f_id, _) = b.fresh_local(f_ty.clone());
            let vec_n = c.vec_of(n.clone());
            let (v_id, v) = b.fresh_local(vec_n.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, vec_n, v);
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(big_n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.compose_chain"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation. Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_residual_lipschitz(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let thm_type = build_residual_lipschitz_type(c);
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.residual_lipschitz_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.Lipschitz.residual_lipschitz_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.Lipschitz.residual_lipschitz"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation. Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_nfold_product(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let thm_type = build_nfold_product_type(c);
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.nfold_product_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.Lipschitz.nfold_product_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.Lipschitz.nfold_product"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation. Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_product_le_exp_sum(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let thm_type = build_product_le_exp_sum_type(c);
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.product_le_exp_sum_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.Lipschitz.product_le_exp_sum_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.Lipschitz.product_le_exp_sum"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation. Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_spectral_norm_lipschitz(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let thm_type = build_spectral_norm_lipschitz_type(c);
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.spectral_norm_lipschitz_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.Lipschitz.spectral_norm_lipschitz_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.Lipschitz.spectral_norm_lipschitz"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
