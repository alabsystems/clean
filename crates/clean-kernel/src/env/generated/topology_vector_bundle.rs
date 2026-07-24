// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.VectorBundle namespace (#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.VectorBundle";
pub(crate) const DECL_COUNT: usize = 19;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.VectorBundle",
    "Topology.VectorBundle.toFiberBundle",
    "Topology.VectorBundle.zero_section",
    "Topology.VectorBundle.zero_section_continuous",
    "Topology.VectorBundle.section",
    "Topology.VectorBundle.rank",
    "Topology.VectorBundle.trivial",
    "Topology.VectorBundle.direct_sum",
    "Topology.VectorBundle.tensor_product",
    "Topology.VectorBundle.dual",
    "Topology.VectorBundle.pullback",
    "Topology.VectorBundle.tangent_bundle",
    "Topology.VectorBundle.cotangent_bundle",
    "Topology.VectorBundle.section_zero",
    "Topology.VectorBundle.isomorphism",
    "Topology.VectorBundle.hom_bundle",
    "Topology.VectorBundle.exterior_power",
    "Topology.VectorBundle.proj_is_surjective",
    "Topology.VectorBundle.fiber_nonempty",
];

struct VbCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl VbCtx {
    fn new() -> Self {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        Self {
            type_u: Expr::sort(Level::succ(u_level.clone())),
            prop: Expr::sort(Level::zero()),
            u,
            u_level,
        }
    }

    fn topological_space(&self, x: Expr) -> Expr {
        Expr::app(
            Expr::const_(
                Name::from_string("TopologicalSpace"),
                vec![self.u_level.clone()],
            ),
            x,
        )
    }

    fn semiring(&self, x: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Semiring"), vec![self.u_level.clone()]),
            x,
        )
    }

    fn add_comm_group(&self, x: Expr) -> Expr {
        Expr::app(
            Expr::const_(
                Name::from_string("AddCommGroup"),
                vec![self.u_level.clone()],
            ),
            x,
        )
    }

    fn vector_bundle(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.VectorBundle"),
            vec![self.u_level.clone()],
        )
    }

    fn fiber_bundle(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.FiberBundle"),
            vec![self.u_level.clone()],
        )
    }

    fn continuous(&self, dom: Expr, cod: Expr, ts_dom: Expr, ts_cod: Expr, f: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Topology.Continuous"),
                vec![self.u_level.clone(), self.u_level.clone()],
            ),
            [dom, cod, ts_dom, ts_cod, f],
        )
    }

    fn nat_type(&self) -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }

    fn to_axiom(&self, name: &str, type_: Expr) -> ConstantInfo {
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

    /// Bind the standard 10-parameter VectorBundle context:
    /// {R : Type u} → {E : Type u} → {B : Type u} → {F : Type u} →
    /// [Semiring R] → [TS E] → [TS B] → [TS F] → [AddCommGroup F] →
    /// {π : E → B}
    ///
    /// Returns (builder, ids, vars) for the 10 bindings.
    fn bind_full_vb_context(&self) -> (EnvDeclBuilder, VbBindingIds, VbBindingVars) {
        let mut b = EnvDeclBuilder::new();
        let (r_id, r_ty) = b.fresh_local(self.type_u.clone());
        let (e_id, e_ty) = b.fresh_local(self.type_u.clone());
        let (base_id, base_ty) = b.fresh_local(self.type_u.clone());
        let (fiber_id, fiber_ty) = b.fresh_local(self.type_u.clone());
        let inst_r_ty = self.semiring(r_ty.clone());
        let (inst_r_id, inst_r) = b.fresh_local(inst_r_ty.clone());
        let inst_e_ty = self.topological_space(e_ty.clone());
        let (inst_e_id, inst_e) = b.fresh_local(inst_e_ty.clone());
        let inst_base_ty = self.topological_space(base_ty.clone());
        let (inst_base_id, inst_base) = b.fresh_local(inst_base_ty.clone());
        let inst_f_ty = self.topological_space(fiber_ty.clone());
        let (inst_f_id, inst_f) = b.fresh_local(inst_f_ty.clone());
        let inst_fg_ty = self.add_comm_group(fiber_ty.clone());
        let (inst_fg_id, inst_fg) = b.fresh_local(inst_fg_ty.clone());
        let pi_ty = Expr::pi(BinderInfo::Default, e_ty.clone(), base_ty.clone());
        let (pi_id, pi_var) = b.fresh_local(pi_ty.clone());

        let ids = VbBindingIds {
            r_id,
            e_id,
            base_id,
            fiber_id,
            inst_r_id,
            inst_e_id,
            inst_base_id,
            inst_f_id,
            inst_fg_id,
            pi_id,
            inst_r_ty,
            inst_e_ty,
            inst_base_ty,
            inst_f_ty,
            inst_fg_ty,
            pi_ty,
        };
        let vars = VbBindingVars {
            r_ty,
            e_ty,
            base_ty,
            fiber_ty,
            inst_r,
            inst_e,
            inst_base,
            inst_f,
            inst_fg,
            pi_var,
        };
        (b, ids, vars)
    }

    /// Wrap body with full 10-parameter VectorBundle binding chain.
    fn wrap_full_vb_pi(&self, b: &mut EnvDeclBuilder, ids: &VbBindingIds, body: Expr) -> Expr {
        let e = b.mk_pi(ids.pi_id, BinderInfo::Implicit, ids.pi_ty.clone(), body);
        let e = b.mk_pi(
            ids.inst_fg_id,
            BinderInfo::InstImplicit,
            ids.inst_fg_ty.clone(),
            e,
        );
        let e = b.mk_pi(
            ids.inst_f_id,
            BinderInfo::InstImplicit,
            ids.inst_f_ty.clone(),
            e,
        );
        let e = b.mk_pi(
            ids.inst_base_id,
            BinderInfo::InstImplicit,
            ids.inst_base_ty.clone(),
            e,
        );
        let e = b.mk_pi(
            ids.inst_e_id,
            BinderInfo::InstImplicit,
            ids.inst_e_ty.clone(),
            e,
        );
        let e = b.mk_pi(
            ids.inst_r_id,
            BinderInfo::InstImplicit,
            ids.inst_r_ty.clone(),
            e,
        );
        let e = b.mk_pi(ids.fiber_id, BinderInfo::Implicit, self.type_u.clone(), e);
        let e = b.mk_pi(ids.base_id, BinderInfo::Implicit, self.type_u.clone(), e);
        let e = b.mk_pi(ids.e_id, BinderInfo::Implicit, self.type_u.clone(), e);
        b.mk_pi(ids.r_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// Build VectorBundle R E B F instR instE instB instF instFG π application.
    fn mk_vb_app(&self, v: &VbBindingVars) -> Expr {
        Expr::apps(
            self.vector_bundle(),
            [
                v.r_ty.clone(),
                v.e_ty.clone(),
                v.base_ty.clone(),
                v.fiber_ty.clone(),
                v.inst_r.clone(),
                v.inst_e.clone(),
                v.inst_base.clone(),
                v.inst_f.clone(),
                v.inst_fg.clone(),
                v.pi_var.clone(),
            ],
        )
    }

    /// Build FiberBundle E B F instE instB instF π application.
    fn mk_fb_app(&self, v: &VbBindingVars) -> Expr {
        Expr::apps(
            self.fiber_bundle(),
            [
                v.e_ty.clone(),
                v.base_ty.clone(),
                v.fiber_ty.clone(),
                v.inst_e.clone(),
                v.inst_base.clone(),
                v.inst_f.clone(),
                v.pi_var.clone(),
            ],
        )
    }
}

#[derive(Clone)]
struct VbBindingIds {
    r_id: FVarId,
    e_id: FVarId,
    base_id: FVarId,
    fiber_id: FVarId,
    inst_r_id: FVarId,
    inst_e_id: FVarId,
    inst_base_id: FVarId,
    inst_f_id: FVarId,
    inst_fg_id: FVarId,
    pi_id: FVarId,
    inst_r_ty: Expr,
    inst_e_ty: Expr,
    inst_base_ty: Expr,
    inst_f_ty: Expr,
    inst_fg_ty: Expr,
    pi_ty: Expr,
}

struct VbBindingVars {
    r_ty: Expr,
    e_ty: Expr,
    base_ty: Expr,
    fiber_ty: Expr,
    inst_r: Expr,
    inst_e: Expr,
    inst_base: Expr,
    inst_f: Expr,
    inst_fg: Expr,
    pi_var: Expr,
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = VbCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    // 1. Topology.VectorBundle : {R E B F : Type u} →
    //    [Semiring R] → [TS E] → [TS B] → [TS F] → [AddCommGroup F] →
    //    (E → B) → Type u
    {
        let (mut b, ids, _vars) = ctx.bind_full_vb_context();
        let body = ctx.type_u.clone();
        // π is already bound as the last implicit; need to make it Default for the main type
        // Actually, the original code binds π as Default for VectorBundle itself.
        // But bind_full_vb_context binds π as Implicit. For VectorBundle, π is a Default param.
        // Let me build VectorBundle type manually instead.
        drop(b);
        let mut b = EnvDeclBuilder::new();
        let (r_id, r_ty) = b.fresh_local(ctx.type_u.clone());
        let (e_id, e_ty) = b.fresh_local(ctx.type_u.clone());
        let (base_id, base_ty) = b.fresh_local(ctx.type_u.clone());
        let (fiber_id, fiber_ty) = b.fresh_local(ctx.type_u.clone());
        let inst_r_ty = ctx.semiring(r_ty.clone());
        let (inst_r_id, _) = b.fresh_local(inst_r_ty.clone());
        let inst_e_ty = ctx.topological_space(e_ty.clone());
        let (inst_e_id, _) = b.fresh_local(inst_e_ty.clone());
        let inst_base_ty = ctx.topological_space(base_ty.clone());
        let (inst_base_id, _) = b.fresh_local(inst_base_ty.clone());
        let inst_f_ty = ctx.topological_space(fiber_ty.clone());
        let (inst_f_id, _) = b.fresh_local(inst_f_ty.clone());
        let inst_fg_ty = ctx.add_comm_group(fiber_ty.clone());
        let (inst_fg_id, _) = b.fresh_local(inst_fg_ty.clone());
        let pi_ty = Expr::pi(BinderInfo::Default, e_ty.clone(), base_ty.clone());
        let (pi_id, _) = b.fresh_local(pi_ty.clone());

        let e = ctx.type_u.clone();
        let e = b.mk_pi(pi_id, BinderInfo::Default, pi_ty, e);
        let e = b.mk_pi(inst_fg_id, BinderInfo::InstImplicit, inst_fg_ty, e);
        let e = b.mk_pi(inst_f_id, BinderInfo::InstImplicit, inst_f_ty, e);
        let e = b.mk_pi(inst_base_id, BinderInfo::InstImplicit, inst_base_ty, e);
        let e = b.mk_pi(inst_e_id, BinderInfo::InstImplicit, inst_e_ty, e);
        let e = b.mk_pi(inst_r_id, BinderInfo::InstImplicit, inst_r_ty, e);
        let e = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(r_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.VectorBundle", b.finish(e)));
    }

    // 2. Topology.VectorBundle.toFiberBundle : {R E B F : Type u} → [...] →
    //    {π : E → B} → VectorBundle R π → FiberBundle π
    {
        let (mut b, ids, vars) = ctx.bind_full_vb_context();
        let vb_ty = ctx.mk_vb_app(&vars);
        let (vb_id, _vb) = b.fresh_local(vb_ty.clone());
        let result = ctx.mk_fb_app(&vars);
        let e = b.mk_pi(vb_id, BinderInfo::Default, vb_ty, result);
        let e = ctx.wrap_full_vb_pi(&mut b, &ids, e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.toFiberBundle", b.finish(e)));
    }

    // 3. Topology.VectorBundle.zero_section : {R E B F : Type u} → [...] →
    //    {π : E → B} → VectorBundle R π → (B → E)
    {
        let (mut b, ids, vars) = ctx.bind_full_vb_context();
        let vb_ty = ctx.mk_vb_app(&vars);
        let (vb_id, _vb) = b.fresh_local(vb_ty.clone());
        let result = Expr::pi(BinderInfo::Default, vars.base_ty.clone(), vars.e_ty.clone());
        let e = b.mk_pi(vb_id, BinderInfo::Default, vb_ty, result);
        let e = ctx.wrap_full_vb_pi(&mut b, &ids, e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.zero_section", b.finish(e)));
    }

    // 4. Topology.VectorBundle.zero_section_continuous : {R E B F : Type u} → [...] →
    //    {π : E → B} → (vb : VectorBundle R π) → Continuous (zero_section vb)
    {
        let (mut b, ids, vars) = ctx.bind_full_vb_context();
        let vb_ty = ctx.mk_vb_app(&vars);
        let (vb_id, vb) = b.fresh_local(vb_ty.clone());
        let zero_sec_vb = Expr::apps(
            Expr::const_(
                Name::from_string("Topology.VectorBundle.zero_section"),
                vec![ctx.u_level.clone()],
            ),
            [
                vars.r_ty.clone(),
                vars.e_ty.clone(),
                vars.base_ty.clone(),
                vars.fiber_ty.clone(),
                vars.inst_r.clone(),
                vars.inst_e.clone(),
                vars.inst_base.clone(),
                vars.inst_f.clone(),
                vars.inst_fg.clone(),
                vars.pi_var.clone(),
                vb,
            ],
        );
        let result = ctx.continuous(
            vars.base_ty.clone(),
            vars.e_ty.clone(),
            vars.inst_base.clone(),
            vars.inst_e.clone(),
            zero_sec_vb,
        );
        let e = b.mk_pi(vb_id, BinderInfo::Default, vb_ty, result);
        let e = ctx.wrap_full_vb_pi(&mut b, &ids, e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.zero_section_continuous", b.finish(e)));
    }

    // 5. Topology.VectorBundle.section : {R E B F : Type u} → [...] →
    //    {π : E → B} → VectorBundle R π → Type u
    {
        let (mut b, ids, vars) = ctx.bind_full_vb_context();
        let vb_ty = ctx.mk_vb_app(&vars);
        let (vb_id, _vb) = b.fresh_local(vb_ty.clone());
        let e = b.mk_pi(vb_id, BinderInfo::Default, vb_ty, ctx.type_u.clone());
        let e = ctx.wrap_full_vb_pi(&mut b, &ids, e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.section", b.finish(e)));
    }

    // 6. Topology.VectorBundle.rank : {R E B F : Type u} → [...] →
    //    {π : E → B} → VectorBundle R π → Nat
    {
        let (mut b, ids, vars) = ctx.bind_full_vb_context();
        let vb_ty = ctx.mk_vb_app(&vars);
        let (vb_id, _vb) = b.fresh_local(vb_ty.clone());
        let e = b.mk_pi(vb_id, BinderInfo::Default, vb_ty, ctx.nat_type());
        let e = ctx.wrap_full_vb_pi(&mut b, &ids, e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.rank", b.finish(e)));
    }

    // 7. Topology.VectorBundle.trivial : {R B F : Type u} → [Semiring R] →
    //    [TS B] → [TS F] → [AddCommGroup F] →
    //    VectorBundle R (Prod.fst : B × F → B)
    {
        let mut b = EnvDeclBuilder::new();
        let (r_id, r_ty) = b.fresh_local(ctx.type_u.clone());
        let (base_id, base_ty) = b.fresh_local(ctx.type_u.clone());
        let (fiber_id, fiber_ty) = b.fresh_local(ctx.type_u.clone());
        let inst_r_ty = ctx.semiring(r_ty.clone());
        let (inst_r_id, inst_r) = b.fresh_local(inst_r_ty.clone());
        let inst_base_ty = ctx.topological_space(base_ty.clone());
        let (inst_base_id, inst_base) = b.fresh_local(inst_base_ty.clone());
        let inst_f_ty = ctx.topological_space(fiber_ty.clone());
        let (inst_f_id, inst_f) = b.fresh_local(inst_f_ty.clone());
        let inst_fg_ty = ctx.add_comm_group(fiber_ty.clone());
        let (inst_fg_id, inst_fg) = b.fresh_local(inst_fg_ty.clone());

        // B × F
        let prod_bf = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Prod"),
                    vec![ctx.u_level.clone(), ctx.u_level.clone()],
                ),
                base_ty.clone(),
            ),
            fiber_ty.clone(),
        );
        // Prod.fst : B × F → B
        let fst_bf = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Prod.fst"),
                    vec![ctx.u_level.clone(), ctx.u_level.clone()],
                ),
                base_ty.clone(),
            ),
            fiber_ty.clone(),
        );
        // TopologicalSpace (B × F) via product topology
        let prod_ts = Expr::app(
            Expr::const_(
                Name::from_string("Topology.Product.topological_space"),
                vec![ctx.u_level.clone()],
            ),
            inst_base.clone(),
        );
        // VectorBundle R (B × F) B F instR prod_ts instB instF instFG (Prod.fst)
        let body = Expr::apps(
            ctx.vector_bundle(),
            [
                r_ty, prod_bf, base_ty, fiber_ty, inst_r, prod_ts, inst_base, inst_f, inst_fg,
                fst_bf,
            ],
        );
        let e = b.mk_pi(inst_fg_id, BinderInfo::InstImplicit, inst_fg_ty, body);
        let e = b.mk_pi(inst_f_id, BinderInfo::InstImplicit, inst_f_ty, e);
        let e = b.mk_pi(inst_base_id, BinderInfo::InstImplicit, inst_base_ty, e);
        let e = b.mk_pi(inst_r_id, BinderInfo::InstImplicit, inst_r_ty, e);
        let e = b.mk_pi(fiber_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(r_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.trivial", b.finish(e)));
    }

    // 8. Topology.VectorBundle.direct_sum : {R E₁ E₂ B F₁ F₂ : Type u} → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (r_id, _) = b.fresh_local(ctx.type_u.clone());
        let (e1_id, _) = b.fresh_local(ctx.type_u.clone());
        let (e2_id, _) = b.fresh_local(ctx.type_u.clone());
        let (base_id, _) = b.fresh_local(ctx.type_u.clone());
        let (f1_id, _) = b.fresh_local(ctx.type_u.clone());
        let (f2_id, _) = b.fresh_local(ctx.type_u.clone());
        let e = ctx.type_u.clone();
        let e = b.mk_pi(f2_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(f1_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(e2_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(e1_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(r_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.direct_sum", b.finish(e)));
    }

    // 9. Topology.VectorBundle.tensor_product : {R E₁ E₂ B F₁ F₂ : Type u} → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (r_id, _) = b.fresh_local(ctx.type_u.clone());
        let (e1_id, _) = b.fresh_local(ctx.type_u.clone());
        let (e2_id, _) = b.fresh_local(ctx.type_u.clone());
        let (base_id, _) = b.fresh_local(ctx.type_u.clone());
        let (f1_id, _) = b.fresh_local(ctx.type_u.clone());
        let (f2_id, _) = b.fresh_local(ctx.type_u.clone());
        let e = ctx.type_u.clone();
        let e = b.mk_pi(f2_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(f1_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(e2_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(e1_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(r_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.tensor_product", b.finish(e)));
    }

    // 10. Topology.VectorBundle.dual : {R E B F : Type u} → [...] →
    //     {π : E → B} → VectorBundle R π → Type u
    {
        let (mut b, ids, vars) = ctx.bind_full_vb_context();
        let vb_ty = ctx.mk_vb_app(&vars);
        let (vb_id, _vb) = b.fresh_local(vb_ty.clone());
        let e = b.mk_pi(vb_id, BinderInfo::Default, vb_ty, ctx.type_u.clone());
        let e = ctx.wrap_full_vb_pi(&mut b, &ids, e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.dual", b.finish(e)));
    }

    // 11. Topology.VectorBundle.pullback : {R E B B' F : Type u} → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (r_id, _) = b.fresh_local(ctx.type_u.clone());
        let (e_id, _) = b.fresh_local(ctx.type_u.clone());
        let (base_id, _) = b.fresh_local(ctx.type_u.clone());
        let (bp_id, _) = b.fresh_local(ctx.type_u.clone());
        let (f_id, _) = b.fresh_local(ctx.type_u.clone());
        let e = ctx.type_u.clone();
        let e = b.mk_pi(f_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(bp_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(r_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.pullback", b.finish(e)));
    }

    // 12. Topology.VectorBundle.tangent_bundle : (M : Type u) → [TS M] → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(ctx.type_u.clone());
        let ts_m_ty = ctx.topological_space(m);
        let (ts_id, _) = b.fresh_local(ts_m_ty.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_m_ty, ctx.type_u.clone());
        let e = b.mk_pi(m_id, BinderInfo::Default, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.tangent_bundle", b.finish(e)));
    }

    // 13. Topology.VectorBundle.cotangent_bundle : (M : Type u) → [TS M] → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(ctx.type_u.clone());
        let ts_m_ty = ctx.topological_space(m);
        let (ts_id, _) = b.fresh_local(ts_m_ty.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_m_ty, ctx.type_u.clone());
        let e = b.mk_pi(m_id, BinderInfo::Default, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.cotangent_bundle", b.finish(e)));
    }

    // 14. Topology.VectorBundle.section_zero : {R E B F : Type u} → [...] →
    //     {π : E → B} → (vb : VectorBundle R π) → section vb
    {
        let (mut b, ids, vars) = ctx.bind_full_vb_context();
        let vb_ty = ctx.mk_vb_app(&vars);
        let (vb_id, vb) = b.fresh_local(vb_ty.clone());
        let section_vb = Expr::apps(
            Expr::const_(
                Name::from_string("Topology.VectorBundle.section"),
                vec![ctx.u_level.clone()],
            ),
            [
                vars.r_ty.clone(),
                vars.e_ty.clone(),
                vars.base_ty.clone(),
                vars.fiber_ty.clone(),
                vars.inst_r.clone(),
                vars.inst_e.clone(),
                vars.inst_base.clone(),
                vars.inst_f.clone(),
                vars.inst_fg.clone(),
                vars.pi_var.clone(),
                vb,
            ],
        );
        let e = b.mk_pi(vb_id, BinderInfo::Default, vb_ty, section_vb);
        let e = ctx.wrap_full_vb_pi(&mut b, &ids, e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.section_zero", b.finish(e)));
    }

    // 15. Topology.VectorBundle.isomorphism : {R E₁ E₂ B F : Type u} → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (r_id, _) = b.fresh_local(ctx.type_u.clone());
        let (e1_id, _) = b.fresh_local(ctx.type_u.clone());
        let (e2_id, _) = b.fresh_local(ctx.type_u.clone());
        let (base_id, _) = b.fresh_local(ctx.type_u.clone());
        let (f_id, _) = b.fresh_local(ctx.type_u.clone());
        let e = ctx.type_u.clone();
        let e = b.mk_pi(f_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(e2_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(e1_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(r_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.isomorphism", b.finish(e)));
    }

    // 16. Topology.VectorBundle.hom_bundle : {R E₁ E₂ B F₁ F₂ : Type u} → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (r_id, _) = b.fresh_local(ctx.type_u.clone());
        let (e1_id, _) = b.fresh_local(ctx.type_u.clone());
        let (e2_id, _) = b.fresh_local(ctx.type_u.clone());
        let (base_id, _) = b.fresh_local(ctx.type_u.clone());
        let (f1_id, _) = b.fresh_local(ctx.type_u.clone());
        let (f2_id, _) = b.fresh_local(ctx.type_u.clone());
        let e = ctx.type_u.clone();
        let e = b.mk_pi(f2_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(f1_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(base_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(e2_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(e1_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(r_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.hom_bundle", b.finish(e)));
    }

    // 17. Topology.VectorBundle.exterior_power : {R E B F : Type u} → [...] →
    //     {π : E → B} → VectorBundle R π → Nat → Type u
    {
        let (mut b, ids, vars) = ctx.bind_full_vb_context();
        let vb_ty = ctx.mk_vb_app(&vars);
        let (vb_id, _vb) = b.fresh_local(vb_ty.clone());
        let (k_id, _k) = b.fresh_local(ctx.nat_type());
        let e = b.mk_pi(
            k_id,
            BinderInfo::Default,
            ctx.nat_type(),
            ctx.type_u.clone(),
        );
        let e = b.mk_pi(vb_id, BinderInfo::Default, vb_ty, e);
        let e = ctx.wrap_full_vb_pi(&mut b, &ids, e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.exterior_power", b.finish(e)));
    }

    // 18. Topology.VectorBundle.proj_is_surjective : {R E B F : Type u} → [...] →
    //     {π : E → B} → VectorBundle R π → Prop
    {
        let (mut b, ids, vars) = ctx.bind_full_vb_context();
        let vb_ty = ctx.mk_vb_app(&vars);
        let (vb_id, _vb) = b.fresh_local(vb_ty.clone());
        let e = b.mk_pi(vb_id, BinderInfo::Default, vb_ty, ctx.prop.clone());
        let e = ctx.wrap_full_vb_pi(&mut b, &ids, e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.proj_is_surjective", b.finish(e)));
    }

    // 19. Topology.VectorBundle.fiber_nonempty : {R E B F : Type u} → [...] →
    //     {π : E → B} → VectorBundle R π → (b : B) → Nonempty F
    {
        let (mut b, ids, vars) = ctx.bind_full_vb_context();
        let vb_ty = ctx.mk_vb_app(&vars);
        let (vb_id, _vb) = b.fresh_local(vb_ty.clone());
        let (base_pt_id, _base_pt) = b.fresh_local(vars.base_ty.clone());
        let nonempty_f = Expr::app(
            Expr::const_(
                Name::from_string("Nonempty"),
                vec![Level::succ(ctx.u_level.clone())],
            ),
            vars.fiber_ty.clone(),
        );
        let e = b.mk_pi(
            base_pt_id,
            BinderInfo::Default,
            vars.base_ty.clone(),
            nonempty_f,
        );
        let e = b.mk_pi(vb_id, BinderInfo::Default, vb_ty, e);
        let e = ctx.wrap_full_vb_pi(&mut b, &ids, e);
        decls.push(ctx.to_axiom("Topology.VectorBundle.fiber_nonempty", b.finish(e)));
    }

    assert_eq!(decls.len(), DECL_COUNT);
    decls
}
