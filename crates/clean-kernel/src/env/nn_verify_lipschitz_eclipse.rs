// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ECLipsE Lipschitz composition theorems (T30-T33, Phase 2 of C003).
//!
//! Builds on `nn_verify_lipschitz.rs` and `nn_verify_lipschitz_ext.rs` with
//! ECLipsE (Efficient Composition of Lipschitz Estimates) theorems for
//! transformer-style networks.
//!
//! ## Types
//! - `NetworkBlock` — network block with dimension (axiom type)
//!
//! ## Theorems
//! - **T30: `lipschitz_compose`** — `Lip(f . g) <= Lip(f) * Lip(g)`
//! - **T31: `eclipse_block_lipschitz`** — per-block monotonicity
//! - **T32: `eclipse_network_lipschitz`** — `L_total = prod L_i`
//! - **T33: `residual_lipschitz_sum`** — `L_block = 1 + L_attn + L_ffn`
//!
//! Part of #3152.

use super::nn_verify_ibp_linear::sorry_inhabit_pi;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Constants for ECLipsE-specific formalization.
struct EclipseConsts {
    nat: Expr,
    rat: Expr,
    type0: Expr,
    fin: Expr,
    nn_vec: Expr,
    lipschitz_constant: Expr,
    lip_product: Expr,
    compose_chain: Expr,
    residual_block: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    network_block: Expr,
    block_lipschitz: Expr,
}

impl EclipseConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            lipschitz_constant: Expr::const_(
                Name::from_string("NNVerify.Lipschitz.constant"),
                vec![],
            ),
            lip_product: Expr::const_(Name::from_string("NNVerify.Lipschitz.lip_product"), vec![]),
            compose_chain: Expr::const_(
                Name::from_string("NNVerify.Lipschitz.compose_chain"),
                vec![],
            ),
            residual_block: Expr::const_(
                Name::from_string("NNVerify.Lipschitz.residual_block"),
                vec![],
            ),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            network_block: Expr::const_(
                Name::from_string("NNVerify.Lipschitz.NetworkBlock"),
                vec![],
            ),
            block_lipschitz: Expr::const_(
                Name::from_string("NNVerify.Lipschitz.block_lipschitz"),
                vec![],
            ),
        }
    }

    fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    fn endo_ty(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.vec_of(n), self.vec_of(n))
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

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_add.clone(), a), b)
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
}

impl Environment {
    /// Initialize ECLipsE Lipschitz composition declarations (T30-T33).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_lipschitz_eclipse(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.Lipschitz.NetworkBlock"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_lipschitz_ext()?;
        let c = EclipseConsts::new();
        self.register_network_block(&c)?;
        self.register_block_lipschitz(&c)?;
        self.register_t30_lipschitz_compose(&c)?;
        self.register_t31_eclipse_block_lipschitz(&c)?;
        self.register_t32_eclipse_network_lipschitz(&c)?;
        self.register_t33_residual_lipschitz_sum(&c)?;
        Ok(())
    }

    /// `NNVerify.Lipschitz.NetworkBlock : Nat -> Type`
    /// Opaque: placeholder `fun (n : Nat) => NNVec n` (blocks are vector-typed)
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_network_block(&mut self, c: &EclipseConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Lipschitz.NetworkBlock");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _) = b.fresh_local(c.nat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), c.type0.clone());
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = Expr::app(c.nn_vec.clone(), n);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.Lipschitz.block_lipschitz : (n : Nat) -> NetworkBlock n -> Rat`
    /// Opaque: placeholder `fun (n : Nat) (_ : NetworkBlock n) => Rat.zero`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_block_lipschitz(&mut self, c: &EclipseConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Lipschitz.block_lipschitz");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let block_n = Expr::app(c.network_block.clone(), n.clone());
            let (blk_id, _) = b.fresh_local(block_n.clone());
            let r = b.mk_pi(blk_id, BinderInfo::Default, block_n, c.rat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let block_n = Expr::app(c.network_block.clone(), n);
            let (blk_id, _) = b.fresh_local(block_n.clone());
            let e = b.mk_lam(blk_id, BinderInfo::Default, block_n, c.rat_zero.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// T30: Lip(f . g) <= Lip(f) * Lip(g)
    ///
    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation. Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t30_lipschitz_compose(&mut self, c: &EclipseConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Lipschitz.lipschitz_compose");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_t30_type(c);
        let axiom_name = Name::from_string("NNVerify.Lipschitz.lipschitz_compose_axiom");
        let value = sorry_inhabit_pi(self, &ty);
        self.add_decl(Declaration::Opaque {
            name: axiom_name,
            level_params: vec![],
            type_: ty.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.Lipschitz.lipschitz_compose_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value: proof,
        })
    }

    /// T31: Per-block Lipschitz bound monotonicity (promotion to block bound).
    ///
    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation. Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t31_eclipse_block_lipschitz(&mut self, c: &EclipseConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Lipschitz.eclipse_block_lipschitz");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_t31_type(c);
        let axiom_name = Name::from_string("NNVerify.Lipschitz.eclipse_block_lipschitz_axiom");
        let value = sorry_inhabit_pi(self, &ty);
        self.add_decl(Declaration::Opaque {
            name: axiom_name,
            level_params: vec![],
            type_: ty.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.Lipschitz.eclipse_block_lipschitz_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value: proof,
        })
    }

    /// T32: L_total = prod L_i for N blocks via compose_chain and lip_product.
    ///
    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation. Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t32_eclipse_network_lipschitz(
        &mut self,
        c: &EclipseConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Lipschitz.eclipse_network_lipschitz");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_t32_type(c);
        let axiom_name = Name::from_string("NNVerify.Lipschitz.eclipse_network_lipschitz_axiom");
        let value = sorry_inhabit_pi(self, &ty);
        self.add_decl(Declaration::Opaque {
            name: axiom_name,
            level_params: vec![],
            type_: ty.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.Lipschitz.eclipse_network_lipschitz_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value: proof,
        })
    }

    /// T33: L_block = 1 + L_attn + L_ffn for transformer residual blocks.
    ///
    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation. Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t33_residual_lipschitz_sum(&mut self, c: &EclipseConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Lipschitz.residual_lipschitz_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_t33_type(c);
        let axiom_name = Name::from_string("NNVerify.Lipschitz.residual_lipschitz_sum_axiom");
        let value = sorry_inhabit_pi(self, &ty);
        self.add_decl(Declaration::Opaque {
            name: axiom_name,
            level_params: vec![],
            type_: ty.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.Lipschitz.residual_lipschitz_sum_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value: proof,
        })
    }
}

// =============================================================================
// Type builders for T30-T33 (extracted for readability)
// =============================================================================

/// Build T30 type: `Lip(f . g) <= Lip(f) * Lip(g)`.
fn build_t30_type(c: &EclipseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (f_id, f) = b.fresh_local(endo.clone());
    let (g_id, g) = b.fresh_local(endo.clone());
    let (lf_id, lf) = b.fresh_local(c.rat.clone());
    let (lg_id, lg) = b.fresh_local(c.rat.clone());
    let hyp_f = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), f.clone(), lf.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_f.clone());
    let hyp_g = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), g.clone(), lg.clone()],
    );
    let (h2_id, _) = b.fresh_local(hyp_g.clone());
    let hyp_lf = c.rat_le(c.rat_zero.clone(), lf.clone());
    let (h3_id, _) = b.fresh_local(hyp_lf.clone());
    let hyp_lg = c.rat_le(c.rat_zero.clone(), lg.clone());
    let (h4_id, _) = b.fresh_local(hyp_lg.clone());
    let vec_n = c.vec_of(&n);
    let comp = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(vec_n.clone());
        let r = ch.mk_lam(
            x_id,
            BinderInfo::Default,
            vec_n.clone(),
            Expr::app(f.clone(), Expr::app(g.clone(), x)),
        );
        ch.finish_child(r)
    };
    let concl = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), comp, c.mul(lf, lg)],
    );
    let r = b.mk_pi(h4_id, BinderInfo::Default, hyp_lg, concl);
    let r = b.mk_pi(h3_id, BinderInfo::Default, hyp_lf, r);
    let r = b.mk_pi(h2_id, BinderInfo::Default, hyp_g, r);
    let r = b.mk_pi(h1_id, BinderInfo::Default, hyp_f, r);
    let r = b.mk_pi(lg_id, BinderInfo::Default, c.rat.clone(), r);
    let r = b.mk_pi(lf_id, BinderInfo::Default, c.rat.clone(), r);
    let r = b.mk_pi(g_id, BinderInfo::Default, endo.clone(), r);
    let r = b.mk_pi(f_id, BinderInfo::Default, endo, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// Build T31 type: per-block Lipschitz bound monotonicity.
fn build_t31_type(c: &EclipseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let block_n = Expr::app(c.network_block.clone(), n.clone());
    let endo = c.endo_ty(&n);
    let (blk_id, blk) = b.fresh_local(block_n.clone());
    let (f_id, f) = b.fresh_local(endo.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());
    let block_lip = Expr::apps(c.block_lipschitz.clone(), [n.clone(), blk.clone()]);
    let hyp_lip = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), f.clone(), l.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_lip.clone());
    let hyp_le = c.rat_le(l, block_lip.clone());
    let (h2_id, _) = b.fresh_local(hyp_le.clone());
    let concl = Expr::apps(c.lipschitz_constant.clone(), [n.clone(), f, block_lip]);
    let r = b.mk_pi(h2_id, BinderInfo::Default, hyp_le, concl);
    let r = b.mk_pi(h1_id, BinderInfo::Default, hyp_lip, r);
    let r = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), r);
    let r = b.mk_pi(f_id, BinderInfo::Default, endo, r);
    let r = b.mk_pi(blk_id, BinderInfo::Default, block_n, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// Build T32 type: L_total = prod L_i for N blocks.
fn build_t32_type(c: &EclipseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (big_n_id, big_n) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fin_n = c.fin_of(&big_n);
    let endo = c.endo_ty(&n);
    let f_ty = Expr::pi(BinderInfo::Default, fin_n.clone(), endo.clone());
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let lips_ty = Expr::pi(BinderInfo::Default, fin_n.clone(), c.rat.clone());
    let (l_id, l) = b.fresh_local(lips_ty.clone());
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
    let nonneg_hyp = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = c.rat_le(c.rat_zero.clone(), Expr::app(l.clone(), i));
        let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), body);
        ch.finish_child(r)
    };
    let (h2_id, _) = b.fresh_local(nonneg_hyp.clone());
    let comp = Expr::apps(c.compose_chain.clone(), [big_n.clone(), n.clone(), f]);
    let prod = Expr::apps(c.lip_product.clone(), [big_n.clone(), l]);
    let concl = Expr::apps(c.lipschitz_constant.clone(), [n.clone(), comp, prod]);
    let r = b.mk_pi(h2_id, BinderInfo::Default, nonneg_hyp, concl);
    let r = b.mk_pi(h1_id, BinderInfo::Default, lip_hyp, r);
    let r = b.mk_pi(l_id, BinderInfo::Default, lips_ty, r);
    let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(big_n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// Build T33 type: L_block = 1 + L_attn + L_ffn for transformer residual blocks.
fn build_t33_type(c: &EclipseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (g_attn_id, g_attn) = b.fresh_local(endo.clone());
    let (g_ffn_id, g_ffn) = b.fresh_local(endo.clone());
    let (l_attn_id, l_attn) = b.fresh_local(c.rat.clone());
    let (l_ffn_id, l_ffn) = b.fresh_local(c.rat.clone());
    let hyp_attn = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), g_attn.clone(), l_attn.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_attn.clone());
    let hyp_ffn = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), g_ffn.clone(), l_ffn.clone()],
    );
    let (h2_id, _) = b.fresh_local(hyp_ffn.clone());
    let hyp_nn_attn = c.rat_le(c.rat_zero.clone(), l_attn.clone());
    let (h3_id, _) = b.fresh_local(hyp_nn_attn.clone());
    let hyp_nn_ffn = c.rat_le(c.rat_zero.clone(), l_ffn.clone());
    let (h4_id, _) = b.fresh_local(hyp_nn_ffn.clone());
    let res_attn = Expr::apps(c.residual_block.clone(), [n.clone(), g_attn]);
    let res_ffn = Expr::apps(c.residual_block.clone(), [n.clone(), g_ffn]);
    let vec_n = c.vec_of(&n);
    let full_block = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(vec_n.clone());
        let out = Expr::app(res_ffn.clone(), Expr::app(res_attn.clone(), x));
        let r = ch.mk_lam(x_id, BinderInfo::Default, vec_n.clone(), out);
        ch.finish_child(r)
    };
    let l_block = c.add(c.add(c.rat_one.clone(), l_attn), l_ffn);
    let concl = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), full_block, l_block],
    );
    let r = b.mk_pi(h4_id, BinderInfo::Default, hyp_nn_ffn, concl);
    let r = b.mk_pi(h3_id, BinderInfo::Default, hyp_nn_attn, r);
    let r = b.mk_pi(h2_id, BinderInfo::Default, hyp_ffn, r);
    let r = b.mk_pi(h1_id, BinderInfo::Default, hyp_attn, r);
    let r = b.mk_pi(l_ffn_id, BinderInfo::Default, c.rat.clone(), r);
    let r = b.mk_pi(l_attn_id, BinderInfo::Default, c.rat.clone(), r);
    let r = b.mk_pi(g_ffn_id, BinderInfo::Default, endo.clone(), r);
    let r = b.mk_pi(g_attn_id, BinderInfo::Default, endo, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}
