// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.FiberBundle cluster declarations (#1444).
//!
//! This module covers the migrated FiberBundle declarations from
//! `init_topology_fiber_bundle`:
//! - Topology.FiberBundle
//! - Topology.FiberBundle.proj
//! - Topology.FiberBundle.continuous_proj
//! - Topology.FiberBundle.fiber
//! - Topology.Trivialization
//! - Topology.Trivialization.baseSet
//! - Topology.Trivialization.baseSet_open
//! - Topology.Trivialization.toFun
//! - Topology.Trivialization.invFun
//! - Topology.Trivialization.proj_toFun
//! - Topology.IsTrivialBundle
//! - Topology.trivial_bundle
//! - Topology.IsBundleMap
//! - Topology.IsLocallyTrivial
//! - Topology.fiber_bundle_locally_trivial
//! - Topology.IsPullbackBundle
//! - Topology.bundle_fiber_homeomorphic

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.FiberBundle";
pub(crate) const DECL_COUNT: usize = 17;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.FiberBundle",
    "Topology.FiberBundle.proj",
    "Topology.FiberBundle.continuous_proj",
    "Topology.FiberBundle.fiber",
    "Topology.Trivialization",
    "Topology.Trivialization.baseSet",
    "Topology.Trivialization.baseSet_open",
    "Topology.Trivialization.toFun",
    "Topology.Trivialization.invFun",
    "Topology.Trivialization.proj_toFun",
    "Topology.IsTrivialBundle",
    "Topology.trivial_bundle",
    "Topology.IsBundleMap",
    "Topology.IsLocallyTrivial",
    "Topology.fiber_bundle_locally_trivial",
    "Topology.IsPullbackBundle",
    "Topology.bundle_fiber_homeomorphic",
];

struct FiberBundleCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl FiberBundleCtx {
    fn new() -> Self {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let prop = Expr::sort(Level::zero());
        Self {
            u,
            u_level,
            type_u,
            prop,
        }
    }

    fn topological_space(&self, e: Expr) -> Expr {
        Expr::app(
            Expr::const_(
                Name::from_string("TopologicalSpace"),
                vec![self.u_level.clone()],
            ),
            e,
        )
    }

    fn continuous(&self, e: Expr, b: Expr, ts_e: Expr, ts_b: Expr, f: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Topology.Continuous"),
                                vec![self.u_level.clone(), self.u_level.clone()],
                            ),
                            e,
                        ),
                        b,
                    ),
                    ts_e,
                ),
                ts_b,
            ),
            f,
        )
    }

    fn is_open(&self, b: Expr, ts_b: Expr, s: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("IsOpen"), vec![self.u_level.clone()]),
                    b,
                ),
                ts_b,
            ),
            s,
        )
    }

    fn prod(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Prod"),
                    vec![self.u_level.clone(), self.u_level.clone()],
                ),
                a,
            ),
            b,
        )
    }

    fn prod_fst(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Prod.fst"),
                    vec![self.u_level.clone(), self.u_level.clone()],
                ),
                a,
            ),
            b,
        )
    }

    fn eq(&self, ty: Expr, a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Eq"),
                        vec![Level::succ(self.u_level.clone())],
                    ),
                    ty,
                ),
                a,
            ),
            b,
        )
    }

    fn fiber_bundle_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.FiberBundle"),
            vec![self.u_level.clone()],
        )
    }

    fn trivialization_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Trivialization"),
            vec![self.u_level.clone()],
        )
    }

    fn triv_base_set_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Trivialization.baseSet"),
            vec![self.u_level.clone()],
        )
    }

    fn triv_to_fun_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Trivialization.toFun"),
            vec![self.u_level.clone()],
        )
    }

    fn fb_proj_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.FiberBundle.proj"),
            vec![self.u_level.clone()],
        )
    }

    fn is_locally_trivial_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.IsLocallyTrivial"),
            vec![self.u_level.clone()],
        )
    }

    /// Apply a 7-arg fiber bundle application: C E B F instE instB instF π
    #[allow(clippy::too_many_arguments)]
    fn fb_app7(
        &self,
        c: Expr,
        e: &Expr,
        b: &Expr,
        f: &Expr,
        ts_e: &Expr,
        ts_b: &Expr,
        ts_f: &Expr,
        pi: &Expr,
    ) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(Expr::app(c, e.clone()), b.clone()), f.clone()),
                        ts_e.clone(),
                    ),
                    ts_b.clone(),
                ),
                ts_f.clone(),
            ),
            pi.clone(),
        )
    }

    fn to_axiom_info(&self, name: &str, type_: Expr) -> ConstantInfo {
        ConstantInfo {
            name: Name::from_string(name),
            level_params: vec![self.u.clone()],
            type_,
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        }
    }
}

// ================================================================
// Declaration builders
// ================================================================

/// FiberBundle : {E B F : Type u} → [TopologicalSpace E] →
///   [TopologicalSpace B] → [TopologicalSpace F] → (E → B) → Type u
fn build_fiber_bundle(ctx: &FiberBundleCtx) -> ConstantInfo {
    // FiberBundle's full prefix is {E B F} [tsE] [tsB] [tsF] (π : E → B) → Type u
    let mut b2 = EnvDeclBuilder::new();
    let (e_id2, e2) = b2.fresh_local(ctx.type_u.clone());
    let (base_id2, base2) = b2.fresh_local(ctx.type_u.clone());
    let (fiber_id2, fiber2) = b2.fresh_local(ctx.type_u.clone());
    let (ts_e_id2, _) = b2.fresh_local(ctx.topological_space(e2.clone()));
    let (ts_b_id2, _) = b2.fresh_local(ctx.topological_space(base2.clone()));
    let (ts_f_id2, _) = b2.fresh_local(ctx.topological_space(fiber2.clone()));
    let pi_ty2 = Expr::pi(BinderInfo::Default, e2.clone(), base2.clone());
    let (pi_id2, _) = b2.fresh_local(pi_ty2.clone());
    let r = b2.mk_pi(pi_id2, BinderInfo::Default, pi_ty2, ctx.type_u.clone());
    let r = b2.mk_pi(
        ts_f_id2,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber2.clone()),
        r,
    );
    let r = b2.mk_pi(
        ts_b_id2,
        BinderInfo::InstImplicit,
        ctx.topological_space(base2.clone()),
        r,
    );
    let r = b2.mk_pi(
        ts_e_id2,
        BinderInfo::InstImplicit,
        ctx.topological_space(e2.clone()),
        r,
    );
    let r = b2.mk_pi(fiber_id2, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b2.mk_pi(base_id2, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b2.mk_pi(e_id2, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.FiberBundle", b2.finish(r))
}

/// FiberBundle.proj : {E B F : Type u} → [TopologicalSpace E] →
///   [TopologicalSpace B] → [TopologicalSpace F] → {π : E → B} →
///   FiberBundle π → (E → B)
fn build_proj(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, ts_e) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, ts_b) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, ts_f) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, pi) = b.fresh_local(pi_ty.clone());
    let fb_app = ctx.fb_app7(
        ctx.fiber_bundle_const(),
        &e,
        &base,
        &fiber,
        &ts_e,
        &ts_b,
        &ts_f,
        &pi,
    );
    let (fb_id, _) = b.fresh_local(fb_app.clone());
    let result = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let r = b.mk_pi(fb_id, BinderInfo::Default, fb_app, result);
    let r = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, r);
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.FiberBundle.proj", b.finish(r))
}

/// FiberBundle.continuous_proj : {E B F : Type u} → [...] →
///   {π : E → B} → (b : FiberBundle π) → Continuous (proj b)
fn build_continuous_proj(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, ts_e) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, ts_b) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, ts_f) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, pi) = b.fresh_local(pi_ty.clone());
    let fb_app = ctx.fb_app7(
        ctx.fiber_bundle_const(),
        &e,
        &base,
        &fiber,
        &ts_e,
        &ts_b,
        &ts_f,
        &pi,
    );
    let (fb_id, fb_var) = b.fresh_local(fb_app.clone());
    // proj b : apply FiberBundle.proj with all implicit args then b
    let proj_b = Expr::app(
        ctx.fb_app7(
            ctx.fb_proj_const(),
            &e,
            &base,
            &fiber,
            &ts_e,
            &ts_b,
            &ts_f,
            &pi,
        ),
        fb_var,
    );
    let result = ctx.continuous(e.clone(), base.clone(), ts_e.clone(), ts_b.clone(), proj_b);
    let r = b.mk_pi(fb_id, BinderInfo::Default, fb_app, result);
    let r = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, r);
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.FiberBundle.continuous_proj", b.finish(r))
}

/// FiberBundle.fiber : {E B F : Type u} → [...] →
///   {π : E → B} → FiberBundle π → B → Type u
fn build_fiber(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, ts_e) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, ts_b) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, ts_f) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, pi) = b.fresh_local(pi_ty.clone());
    let fb_app = ctx.fb_app7(
        ctx.fiber_bundle_const(),
        &e,
        &base,
        &fiber,
        &ts_e,
        &ts_b,
        &ts_f,
        &pi,
    );
    let (fb_id, _) = b.fresh_local(fb_app.clone());
    let (x_id, _) = b.fresh_local(base.clone());
    let r = b.mk_pi(x_id, BinderInfo::Default, base.clone(), ctx.type_u.clone());
    let r = b.mk_pi(fb_id, BinderInfo::Default, fb_app, r);
    let r = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, r);
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.FiberBundle.fiber", b.finish(r))
}

/// Trivialization : {E B F : Type u} → [TopologicalSpace E] →
///   [TopologicalSpace B] → [TopologicalSpace F] → (E → B) → Type u
fn build_trivialization(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, _) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, _) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, _) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, _) = b.fresh_local(pi_ty.clone());
    let r = b.mk_pi(pi_id, BinderInfo::Default, pi_ty, ctx.type_u.clone());
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.Trivialization", b.finish(r))
}

/// Trivialization.baseSet : {E B F : Type u} → [...] →
///   {π : E → B} → Trivialization π → (B → Prop)
fn build_triv_base_set(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, ts_e) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, ts_b) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, ts_f) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, pi) = b.fresh_local(pi_ty.clone());
    let triv_app = ctx.fb_app7(
        ctx.trivialization_const(),
        &e,
        &base,
        &fiber,
        &ts_e,
        &ts_b,
        &ts_f,
        &pi,
    );
    let (t_id, _) = b.fresh_local(triv_app.clone());
    let result = Expr::pi(BinderInfo::Default, base.clone(), ctx.prop.clone());
    let r = b.mk_pi(t_id, BinderInfo::Default, triv_app, result);
    let r = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, r);
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.Trivialization.baseSet", b.finish(r))
}

/// Trivialization.baseSet_open : {E B F : Type u} → [...] →
///   {π : E → B} → (t : Trivialization π) → IsOpen (baseSet t)
fn build_triv_base_set_open(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, ts_e) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, ts_b) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, ts_f) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, pi) = b.fresh_local(pi_ty.clone());
    let triv_app = ctx.fb_app7(
        ctx.trivialization_const(),
        &e,
        &base,
        &fiber,
        &ts_e,
        &ts_b,
        &ts_f,
        &pi,
    );
    let (t_id, t_var) = b.fresh_local(triv_app.clone());
    // baseSet t
    let base_set_t = Expr::app(
        ctx.fb_app7(
            ctx.triv_base_set_const(),
            &e,
            &base,
            &fiber,
            &ts_e,
            &ts_b,
            &ts_f,
            &pi,
        ),
        t_var,
    );
    let result = ctx.is_open(base.clone(), ts_b.clone(), base_set_t);
    let r = b.mk_pi(t_id, BinderInfo::Default, triv_app, result);
    let r = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, r);
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.Trivialization.baseSet_open", b.finish(r))
}

/// Trivialization.toFun : {E B F : Type u} → [...] →
///   {π : E → B} → Trivialization π → (E → B × F)
fn build_triv_to_fun(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, ts_e) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, ts_b) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, ts_f) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, pi) = b.fresh_local(pi_ty.clone());
    let triv_app = ctx.fb_app7(
        ctx.trivialization_const(),
        &e,
        &base,
        &fiber,
        &ts_e,
        &ts_b,
        &ts_f,
        &pi,
    );
    let (t_id, _) = b.fresh_local(triv_app.clone());
    let b_prod_f = ctx.prod(base.clone(), fiber.clone());
    let result = Expr::pi(BinderInfo::Default, e.clone(), b_prod_f);
    let r = b.mk_pi(t_id, BinderInfo::Default, triv_app, result);
    let r = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, r);
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.Trivialization.toFun", b.finish(r))
}

/// Trivialization.invFun : {E B F : Type u} → [...] →
///   {π : E → B} → Trivialization π → (B × F → E)
fn build_triv_inv_fun(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, ts_e) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, ts_b) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, ts_f) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, pi) = b.fresh_local(pi_ty.clone());
    let triv_app = ctx.fb_app7(
        ctx.trivialization_const(),
        &e,
        &base,
        &fiber,
        &ts_e,
        &ts_b,
        &ts_f,
        &pi,
    );
    let (t_id, _) = b.fresh_local(triv_app.clone());
    let b_prod_f = ctx.prod(base.clone(), fiber.clone());
    let result = Expr::pi(BinderInfo::Default, b_prod_f, e.clone());
    let r = b.mk_pi(t_id, BinderInfo::Default, triv_app, result);
    let r = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, r);
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.Trivialization.invFun", b.finish(r))
}

/// Trivialization.proj_toFun : {E B F : Type u} → [...] →
///   {π : E → B} → (t : Trivialization π) → (e : E) →
///   Eq (Prod.fst (toFun t e)) (π e)
fn build_triv_proj_to_fun(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, ts_e) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, ts_b) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, ts_f) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, pi) = b.fresh_local(pi_ty.clone());
    let triv_app = ctx.fb_app7(
        ctx.trivialization_const(),
        &e,
        &base,
        &fiber,
        &ts_e,
        &ts_b,
        &ts_f,
        &pi,
    );
    let (t_id, t_var) = b.fresh_local(triv_app.clone());
    let (arg_id, arg_var) = b.fresh_local(e.clone());
    // toFun t : E → B × F
    let to_fun_t = Expr::app(
        ctx.fb_app7(
            ctx.triv_to_fun_const(),
            &e,
            &base,
            &fiber,
            &ts_e,
            &ts_b,
            &ts_f,
            &pi,
        ),
        t_var,
    );
    // toFun t arg : B × F
    let to_fun_t_e = Expr::app(to_fun_t, arg_var.clone());
    // Prod.fst (toFun t arg) : B
    let fst_to_fun = Expr::app(ctx.prod_fst(base.clone(), fiber.clone()), to_fun_t_e);
    // π arg : B
    let pi_e = Expr::app(pi.clone(), arg_var);
    // Eq B (Prod.fst (toFun t e)) (π e)
    let result = ctx.eq(base.clone(), fst_to_fun, pi_e);
    let r = b.mk_pi(arg_id, BinderInfo::Default, e.clone(), result);
    let r = b.mk_pi(t_id, BinderInfo::Default, triv_app, r);
    let r = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, r);
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.Trivialization.proj_toFun", b.finish(r))
}

/// IsTrivialBundle : {E B F : Type u} → [...] →
///   {π : E → B} → FiberBundle π → Prop
fn build_is_trivial_bundle(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, ts_e) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, ts_b) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, ts_f) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, pi) = b.fresh_local(pi_ty.clone());
    let fb_app = ctx.fb_app7(
        ctx.fiber_bundle_const(),
        &e,
        &base,
        &fiber,
        &ts_e,
        &ts_b,
        &ts_f,
        &pi,
    );
    let (fb_id, _) = b.fresh_local(fb_app.clone());
    let r = b.mk_pi(fb_id, BinderInfo::Default, fb_app, ctx.prop.clone());
    let r = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, r);
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.IsTrivialBundle", b.finish(r))
}

/// trivial_bundle : {B F : Type u} → [TopologicalSpace B] →
///   [TopologicalSpace F] → Prop
fn build_trivial_bundle(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_b_id, _) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, _) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        ctx.prop.clone(),
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.trivial_bundle", b.finish(r))
}

/// IsBundleMap : {E₁ B₁ E₂ B₂ : Type u} → (E₁ → E₂) → (B₁ → B₂) → Prop
fn build_is_bundle_map(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e1_id, e1) = b.fresh_local(ctx.type_u.clone());
    let (b1_id, b1) = b.fresh_local(ctx.type_u.clone());
    let (e2_id, e2) = b.fresh_local(ctx.type_u.clone());
    let (b2_id, b2) = b.fresh_local(ctx.type_u.clone());
    let phi_ty = Expr::pi(BinderInfo::Default, e1.clone(), e2.clone());
    let (phi_id, _) = b.fresh_local(phi_ty.clone());
    let f_ty = Expr::pi(BinderInfo::Default, b1.clone(), b2.clone());
    let (f_id, _) = b.fresh_local(f_ty.clone());
    let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, ctx.prop.clone());
    let r = b.mk_pi(phi_id, BinderInfo::Default, phi_ty, r);
    let r = b.mk_pi(b2_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e2_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(b1_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e1_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.IsBundleMap", b.finish(r))
}

/// IsLocallyTrivial : {E B F : Type u} → [...] →
///   {π : E → B} → FiberBundle π → Prop
fn build_is_locally_trivial(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, ts_e) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, ts_b) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, ts_f) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, pi) = b.fresh_local(pi_ty.clone());
    let fb_app = ctx.fb_app7(
        ctx.fiber_bundle_const(),
        &e,
        &base,
        &fiber,
        &ts_e,
        &ts_b,
        &ts_f,
        &pi,
    );
    let (fb_id, _) = b.fresh_local(fb_app.clone());
    let r = b.mk_pi(fb_id, BinderInfo::Default, fb_app, ctx.prop.clone());
    let r = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, r);
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.IsLocallyTrivial", b.finish(r))
}

/// fiber_bundle_locally_trivial : {E B F : Type u} → [...] →
///   {π : E → B} → (b : FiberBundle π) → IsLocallyTrivial b
fn build_fiber_bundle_locally_trivial(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, ts_e) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, ts_b) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, ts_f) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, pi) = b.fresh_local(pi_ty.clone());
    let fb_app = ctx.fb_app7(
        ctx.fiber_bundle_const(),
        &e,
        &base,
        &fiber,
        &ts_e,
        &ts_b,
        &ts_f,
        &pi,
    );
    let (fb_id, fb_var) = b.fresh_local(fb_app.clone());
    let result = Expr::app(
        ctx.fb_app7(
            ctx.is_locally_trivial_const(),
            &e,
            &base,
            &fiber,
            &ts_e,
            &ts_b,
            &ts_f,
            &pi,
        ),
        fb_var,
    );
    let r = b.mk_pi(fb_id, BinderInfo::Default, fb_app, result);
    let r = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, r);
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.fiber_bundle_locally_trivial", b.finish(r))
}

/// IsPullbackBundle : {E B B' : Type u} → (f : B' → B) → Prop
fn build_is_pullback_bundle(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, _e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (bp_id, bp) = b.fresh_local(ctx.type_u.clone());
    let f_ty = Expr::pi(BinderInfo::Default, bp.clone(), base.clone());
    let (f_id, _) = b.fresh_local(f_ty.clone());
    let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, ctx.prop.clone());
    let r = b.mk_pi(bp_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.IsPullbackBundle", b.finish(r))
}

/// bundle_fiber_homeomorphic : {E B F : Type u} → [...] →
///   {π : E → B} → (b : FiberBundle π) → (x : B) → Prop
fn build_bundle_fiber_homeomorphic(ctx: &FiberBundleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (e_id, e) = b.fresh_local(ctx.type_u.clone());
    let (base_id, base) = b.fresh_local(ctx.type_u.clone());
    let (fiber_id, fiber) = b.fresh_local(ctx.type_u.clone());
    let (ts_e_id, ts_e) = b.fresh_local(ctx.topological_space(e.clone()));
    let (ts_b_id, ts_b) = b.fresh_local(ctx.topological_space(base.clone()));
    let (ts_f_id, ts_f) = b.fresh_local(ctx.topological_space(fiber.clone()));
    let pi_ty = Expr::pi(BinderInfo::Default, e.clone(), base.clone());
    let (pi_id, pi) = b.fresh_local(pi_ty.clone());
    let fb_app = ctx.fb_app7(
        ctx.fiber_bundle_const(),
        &e,
        &base,
        &fiber,
        &ts_e,
        &ts_b,
        &ts_f,
        &pi,
    );
    let (fb_id, _) = b.fresh_local(fb_app.clone());
    let (x_id, _) = b.fresh_local(base.clone());
    let r = b.mk_pi(x_id, BinderInfo::Default, base.clone(), ctx.prop.clone());
    let r = b.mk_pi(fb_id, BinderInfo::Default, fb_app, r);
    let r = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, r);
    let r = b.mk_pi(
        ts_f_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(fiber.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_b_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(base.clone()),
        r,
    );
    let r = b.mk_pi(
        ts_e_id,
        BinderInfo::InstImplicit,
        ctx.topological_space(e.clone()),
        r,
    );
    let r = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.bundle_fiber_homeomorphic", b.finish(r))
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = FiberBundleCtx::new();
    let p = vec![
        build_fiber_bundle(&ctx),
        build_proj(&ctx),
        build_continuous_proj(&ctx),
        build_fiber(&ctx),
        build_trivialization(&ctx),
        build_triv_base_set(&ctx),
        build_triv_base_set_open(&ctx),
        build_triv_to_fun(&ctx),
        build_triv_inv_fun(&ctx),
        build_triv_proj_to_fun(&ctx),
        build_is_trivial_bundle(&ctx),
        build_trivial_bundle(&ctx),
        build_is_bundle_map(&ctx),
        build_is_locally_trivial(&ctx),
        build_fiber_bundle_locally_trivial(&ctx),
        build_is_pullback_bundle(&ctx),
        build_bundle_fiber_homeomorphic(&ctx),
    ];
    debug_assert_eq!(p.len(), DECL_COUNT, "payload size mismatch for {NAMESPACE}");
    debug_assert_eq!(
        p.iter().map(|c| c.name.to_string()).collect::<Vec<_>>(),
        DECL_NAMES.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
        "payload names mismatch for {NAMESPACE}"
    );
    p
}
