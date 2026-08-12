// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C003: Lipschitz convergence requires spectral normalization.
//!
//! For a residual block `f_i(x) = x + g_i(x)` with `Lip(g_i) = L_i`:
//! - `residual_lip`: `Lip(f_i) = 1 + L_i`
//! - `product_convergence`: `prod_{i=1}^N (1+L_i)` converges iff `sum(L_i) < infinity`
//! - `spectral_bound`: With spectral normalization (`L_i <= c < 1`): `prod <= exp(bound)`
//! - `divergence`: Without normalization, product can diverge
//!
//! **Status (post-C003 residual-lip retirement):**
//! - `Lipschitz.constant` is `Declaration::Opaque` (reverted from the
//!   #3459 reducible Definition, whose `fun _ _ _ => True` body enabled
//!   the `True.intro`-over-`Lipschitz.constant` masquerade).
//! - `residual_lip` is a hypothesis-wrapped `Declaration::Theorem`: it
//!   explicitly requires local residual Lipschitz evidence and returns it.
//!   The former `residual_lip_axiom` Opaque alias remains deleted.
//! - `product_convergence`, `spectral_bound`, `divergence` remain
//!   `sorry_inhabit_pi` Opaque + Theorem-wrapper pairs (#3381).
//!
//! See `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M2 + M4.
//! Theorem type builders live in `nn_verify_lipschitz_defs`.
//!
//! Part of #3203, #3577.

use super::nn_verify_ibp_linear::sorry_inhabit_pi;
use super::nn_verify_lipschitz_defs;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for Lipschitz formalization.
pub(super) struct LipschitzConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) fin: Expr,
    pub(super) prop: Expr,
    pub(super) nn_vec: Expr,
    pub(super) rat_add: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) rat_mul: Expr,
    pub(super) rat_one: Expr,
    pub(super) rat_zero: Expr,
    pub(super) le_le: Expr,
    pub(super) lt_lt: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) inst_lt_rat: Expr,
    pub(super) and: Expr,
    pub(super) exists_: Expr,
    pub(super) real_exp: Expr,
    pub(super) lipschitz_constant: Expr,
    pub(super) residual_block: Expr,
}

impl LipschitzConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            #[cfg(test)]
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            lt_lt: Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            inst_lt_rat: Expr::const_(Name::from_string("instLTRat"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            exists_: Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            real_exp: Expr::const_(Name::from_string("NNVerify.Lipschitz.real_exp"), vec![]),
            lipschitz_constant: Expr::const_(
                Name::from_string("NNVerify.Lipschitz.constant"),
                vec![],
            ),
            residual_block: Expr::const_(
                Name::from_string("NNVerify.Lipschitz.residual_block"),
                vec![],
            ),
        }
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
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

    /// Build `LT.lt @Rat instLTRat lhs rhs`.
    pub(super) fn rat_lt(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.lt_lt.clone(), self.rat.clone()),
                    self.inst_lt_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `Rat.add a b`.
    pub(super) fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    /// Build `Rat.mul a b`.
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    /// Build `NNVerify.NNVec n`.
    pub(super) fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    /// Function type `NNVerify.NNVec n -> NNVerify.NNVec n`.
    pub(super) fn endo_ty(&self, n: &Expr) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.vec_of(n.clone()),
            self.vec_of(n.clone()),
        )
    }
}

// =============================================================================
// Type builders for basic definitions (kept here; theorem types in _defs)
// =============================================================================

/// `NNVerify.Lipschitz.constant : Nat -> (NNVec n -> NNVec n) -> Rat -> Prop`
fn build_lipschitz_constant_type(c: &LipschitzConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (f_id, _) = b.fresh_local(endo.clone());
    let (l_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.Lipschitz.residual_block : Nat -> (NNVec n -> NNVec n) -> (NNVec n -> NNVec n)`
fn build_residual_block_type(c: &LipschitzConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (g_id, _) = b.fresh_local(endo.clone());
    let result = c.endo_ty(&n);
    let e = b.mk_pi(g_id, BinderInfo::Default, endo, result);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.Lipschitz.spectral_norm : Nat -> (NNVec n -> NNVec n) -> Rat -> Prop`
fn build_spectral_norm_type(c: &LipschitzConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (g_id, _) = b.fresh_local(endo.clone());
    let (bound_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(bound_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
    let e = b.mk_pi(g_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.Lipschitz.real_exp : Rat -> Rat`
fn build_real_exp_type(c: &LipschitzConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone())
}

/// `NNVerify.Lipschitz.lip_product : Nat -> (Fin N -> Rat) -> Rat`
fn build_lip_product_type(c: &LipschitzConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fin_n = Expr::app(c.fin.clone(), n.clone());
    let lips_ty = Expr::pi(BinderInfo::Default, fin_n, c.rat.clone());
    let (lips_id, _) = b.fresh_local(lips_ty.clone());
    let e = b.mk_pi(lips_id, BinderInfo::Default, lips_ty, c.rat.clone());
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Environment impl
// =============================================================================

impl Environment {
    /// Initialize C003 (Lipschitz convergence) declarations.
    ///
    /// Depends on:
    /// - `init_nn_verify_types()` for NNVec
    /// - `init_fin()` / `init_fin_sum()` for Fin and Fin.sum
    /// - `init_rat()` / `init_rat_ord()` for Rat arithmetic and ordering
    /// - `init_eq()` for equality, `init_and()` for conjunction
    /// - `init_exists()` for Exists (divergence theorem)
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_lipschitz(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.Lipschitz.constant"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_rat()?;
        self.init_rat_ord()?;
        self.init_eq()?;
        self.init_and()?;
        self.init_fin()?;
        self.init_fin_sum()?;
        self.init_exists()?;
        self.init_true_false()?;
        self.init_sorry()?;

        let c = LipschitzConsts::new();
        self.register_lipschitz_constant(&c)?;
        self.register_residual_block(&c)?;
        self.register_spectral_norm(&c)?;
        self.register_real_exp(&c)?;
        self.register_lip_product(&c)?;
        self.register_lip_product_unbounded(&c)?;
        self.register_residual_lip(&c)?;
        self.register_product_convergence(&c)?;
        self.register_spectral_bound(&c)?;
        self.register_divergence(&c)?;

        Ok(())
    }

    /// `Lipschitz.constant` — `Declaration::Opaque` with body
    /// `fun _ _ _ => True`. Post-#3577: reverted from the #3459
    /// reducible Definition (which enabled the `True.intro`-over-
    /// `Lipschitz.constant = True` masquerade for `residual_lip`). The
    /// body is kept so typing resolves via the placeholder; the kernel
    /// does not unfold Opaques during `def_eq`, so no future proposition
    /// `Lipschitz.constant n g L` can be discharged by `True.intro`.
    /// Branch B (faithful Lipschitz predicate) tracked under #3470.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_lipschitz_constant(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let ty = build_lipschitz_constant_type(c);
        let true_const = Expr::const_(Name::from_string("True"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let endo = c.endo_ty(&n);
            let (f_id, _) = b.fresh_local(endo.clone());
            let (l_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), true_const);
            let e = b.mk_lam(f_id, BinderInfo::Default, endo, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.constant"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.Lipschitz.residual_block : (n : Nat) -> (NNVec n -> NNVec n) -> NNVec n -> NNVec n`
    /// Opaque: placeholder `fun (n : Nat) (_ : NNVec n -> NNVec n) (v : NNVec n) => v`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_residual_block(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let ty = build_residual_block_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let endo = c.endo_ty(&n);
            let vec_n = c.vec_of(n.clone());
            let (g_id, _) = b.fresh_local(endo.clone());
            let (v_id, v) = b.fresh_local(vec_n.clone());
            let e = b.mk_lam(v_id, BinderInfo::Default, vec_n, v);
            let e = b.mk_lam(g_id, BinderInfo::Default, endo, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.residual_block"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.Lipschitz.spectral_norm : (n : Nat) -> (NNVec n -> NNVec n) -> Rat -> Prop`
    /// Opaque: placeholder `fun (n : Nat) (g : NNVec n -> NNVec n) (sigma : Rat) => Lipschitz.constant n g sigma`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_spectral_norm(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let ty = build_spectral_norm_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let endo = c.endo_ty(&n);
            let (g_id, g) = b.fresh_local(endo.clone());
            let (sigma_id, sigma) = b.fresh_local(c.rat.clone());
            let body = Expr::apps(c.lipschitz_constant.clone(), [n, g, sigma]);
            let e = b.mk_lam(sigma_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(g_id, BinderInfo::Default, endo, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.spectral_norm"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.Lipschitz.real_exp : Rat -> Rat`
    /// Opaque: placeholder `fun (_ : Rat) => Rat.zero`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_real_exp(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let ty = build_real_exp_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (r_id, _) = b.fresh_local(c.rat.clone());
            let e = b.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), c.rat_zero.clone());
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.real_exp"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.Lipschitz.lip_product : (N : Nat) -> (Fin N -> Rat) -> Rat`
    /// Opaque: placeholder `fun (_ : Nat) (_ : Fin N -> Rat) => Rat.zero`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_lip_product(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let ty = build_lip_product_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let fin_n = Expr::app(c.fin.clone(), n);
            let lips_ty = Expr::pi(BinderInfo::Default, fin_n, c.rat.clone());
            let (l_id, _) = b.fresh_local(lips_ty.clone());
            let e = b.mk_lam(l_id, BinderInfo::Default, lips_ty, c.rat_zero.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.lip_product"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.Lipschitz.lip_product_unbounded : (N : Nat) -> (Nat -> Rat) -> Rat`
    /// Opaque: placeholder `fun (_ : Nat) (_ : Nat -> Rat) => Rat.zero`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_lip_product_unbounded(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let ty = nn_verify_lipschitz_defs::build_lip_product_unbounded_type(c);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let l_ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.rat.clone());
            let (l_id, _) = b.fresh_local(l_ty.clone());
            let e = b.mk_lam(l_id, BinderInfo::Default, l_ty, c.rat_zero.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.lip_product_unbounded"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.Lipschitz.residual_lip` — hypothesis-wrapped theorem.
    ///
    /// History: Axiom (pre-#3381) -> Opaque + `sorry_inhabit_pi` (#3381)
    /// -> Opaque (`residual_lip_axiom`) + Theorem wrapper with
    /// `True.intro`-over-lambda-spine proof (#3459, type-checked only via
    /// reducible `Lipschitz.constant = fun _ _ _ => True`) -> Axiom (#3577).
    /// Current: the statement explicitly requires the local residual
    /// Lipschitz evidence and the proof returns that evidence. This retires
    /// the domain axiom without using `True.intro`, `Eq.refl`, sorry, the
    /// deleted `residual_lip_axiom`, or any global residual axiom reference.
    /// A faithful hypothesis-free Lipschitz proof remains future work.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_residual_lip(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let thm_type = nn_verify_lipschitz_defs::build_residual_lip_type(c);
        let proof = nn_verify_lipschitz_defs::build_residual_lip_proof(c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.Lipschitz.residual_lip"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_product_convergence(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let thm_type = nn_verify_lipschitz_defs::build_product_convergence_type(c);
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.product_convergence_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.Lipschitz.product_convergence_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.Lipschitz.product_convergence"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_spectral_bound(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let thm_type = nn_verify_lipschitz_defs::build_spectral_bound_type(c);
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.spectral_bound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.Lipschitz.spectral_bound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.Lipschitz.spectral_bound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_divergence(&mut self, c: &LipschitzConsts) -> Result<(), EnvError> {
        let thm_type = nn_verify_lipschitz_defs::build_divergence_type(c);
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.Lipschitz.divergence_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.Lipschitz.divergence_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.Lipschitz.divergence"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
