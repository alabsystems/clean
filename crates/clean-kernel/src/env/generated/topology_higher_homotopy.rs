// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.HigherHomotopy namespace (#1444).
//!
//! Migrates 18 unconditional declarations from `init_topology_higher_homotopy`
//! in `topology.rs`, eliminating 172 raw `Expr::bvar` call sites.
//!
//! Three conditional declarations (`pi_one_eq_fundamental_group`,
//! `contractible_trivial`, `homotopy_equiv_iso`) remain inline in the init
//! function because they depend on runtime `has_topology_*` guards.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.HigherHomotopy";
pub(crate) const DECL_COUNT: usize = 18;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Sphere",
    "Topology.Sphere.basepoint",
    "Topology.Sphere.topological_space",
    "Topology.BasedMap",
    "Topology.BasedMap.eval",
    "Topology.BasedMap.preserves_basepoint",
    "Topology.BasedHomotopy",
    "Topology.HigherHomotopyGroup",
    "Topology.HigherHomotopyGroup.class",
    "Topology.HigherHomotopyGroup.class_eq",
    "Topology.HigherHomotopyGroup.mul",
    "Topology.HigherHomotopyGroup.one",
    "Topology.HigherHomotopyGroup.inv",
    "Topology.HigherHomotopyGroup.mul_assoc",
    "Topology.HigherHomotopyGroup.one_mul",
    "Topology.HigherHomotopyGroup.mul_one",
    "Topology.HigherHomotopyGroup.mul_inv",
    "Topology.HigherHomotopyGroup.mul_comm",
];

/// Context for building higher homotopy group declarations.
///
/// Most declarations live at universe `u`; Sphere-related types live at
/// universe `0` (fixed dimension).
struct HomotopyCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    type_0: Expr,
    prop: Expr,
}

impl HomotopyCtx {
    fn new() -> Self {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        Self {
            type_u: Expr::sort(Level::succ(u_level.clone())),
            type_0: Expr::sort(Level::succ(Level::zero())),
            prop: Expr::sort(Level::zero()),
            u,
            u_level,
        }
    }

    fn nat_const(&self) -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }

    fn nat_zero(&self) -> Expr {
        Expr::const_(Name::from_string("Nat.zero"), vec![])
    }

    fn nat_one(&self) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            self.nat_zero(),
        )
    }

    fn nat_lt(&self) -> Expr {
        Expr::const_(Name::from_string("Nat.lt"), vec![])
    }

    fn topological_space(&self, lvl: Level, x: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]),
            x,
        )
    }

    fn sphere(&self, n: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Topology.Sphere"), vec![]),
            n,
        )
    }

    fn sphere_basepoint(&self, n: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Topology.Sphere.basepoint"), vec![]),
            n,
        )
    }

    fn based_map(&self, alpha: Expr, inst: Expr, n: Expr, x0: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.BasedMap"),
                            vec![self.u_level.clone()],
                        ),
                        alpha,
                    ),
                    inst,
                ),
                n,
            ),
            x0,
        )
    }

    fn based_map_eval(&self, alpha: Expr, inst: Expr, n: Expr, x0: Expr, f: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Topology.BasedMap.eval"),
                                vec![self.u_level.clone()],
                            ),
                            alpha,
                        ),
                        inst,
                    ),
                    n,
                ),
                x0,
            ),
            f,
        )
    }

    fn based_homotopy(&self, alpha: Expr, inst: Expr, n: Expr, x0: Expr, f: Expr, g: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(
                                    Name::from_string("Topology.BasedHomotopy"),
                                    vec![self.u_level.clone()],
                                ),
                                alpha,
                            ),
                            inst,
                        ),
                        n,
                    ),
                    x0,
                ),
                f,
            ),
            g,
        )
    }

    fn higher_homotopy_group(&self, alpha: Expr, inst: Expr, n: Expr, x0: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.HigherHomotopyGroup"),
                            vec![self.u_level.clone()],
                        ),
                        alpha,
                    ),
                    inst,
                ),
                n,
            ),
            x0,
        )
    }

    fn hhg_class(&self, alpha: Expr, inst: Expr, n: Expr, x0: Expr, f: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Topology.HigherHomotopyGroup.class"),
                                vec![self.u_level.clone()],
                            ),
                            alpha,
                        ),
                        inst,
                    ),
                    n,
                ),
                x0,
            ),
            f,
        )
    }

    fn eq_const(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("Eq"), vec![lvl])
    }

    fn mk_eq(&self, lvl: Level, ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.eq_const(lvl), ty), lhs), rhs)
    }

    fn axiom_no_level(&self, name: &str, type_: Expr) -> ConstantInfo {
        ConstantInfo {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        }
    }

    fn axiom_u(&self, name: &str, type_: Expr) -> ConstantInfo {
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

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = HomotopyCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    // ================================================================
    // 1. Topology.Sphere : ℕ → Type 0
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, _n) = b.fresh_local(ctx.nat_const());
        let ty = b.mk_pi(
            n_id,
            BinderInfo::Default,
            ctx.nat_const(),
            ctx.type_0.clone(),
        );
        decls.push(ctx.axiom_no_level("Topology.Sphere", ty));
    }

    // ================================================================
    // 2. Topology.Sphere.basepoint : {n : ℕ} → Sphere n
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let sphere_n = ctx.sphere(n);
        let ty = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), sphere_n);
        decls.push(ctx.axiom_no_level("Topology.Sphere.basepoint", ty));
    }

    // ================================================================
    // 3. Topology.Sphere.topological_space : {n : ℕ} → TopologicalSpace (Sphere n)
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let sphere_n = ctx.sphere(n);
        let ts_sphere = ctx.topological_space(Level::zero(), sphere_n);
        let ty = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), ts_sphere);
        decls.push(ctx.axiom_no_level("Topology.Sphere.topological_space", ty));
    }

    // ================================================================
    // 4. Topology.BasedMap : {α : Type u} → [TopologicalSpace α] → ℕ → α → Type u
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, _inst) = b.fresh_local(ts_ty.clone());
        let (n_id, _n) = b.fresh_local(ctx.nat_const());
        let (x0_id, _x0) = b.fresh_local(alpha.clone());
        let e = b.mk_pi(
            x0_id,
            BinderInfo::Default,
            alpha.clone(),
            ctx.type_u.clone(),
        );
        let e = b.mk_pi(n_id, BinderInfo::Default, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.BasedMap", ty));
    }

    // ================================================================
    // 5. Topology.BasedMap.eval : {α : Type u} → [TopologicalSpace α] →
    //    {n : ℕ} → {x₀ : α} → BasedMap n x₀ → Sphere n → α
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let bm_ty = ctx.based_map(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let (f_id, _f) = b.fresh_local(bm_ty.clone());
        let sphere_n = ctx.sphere(n.clone());
        let (s_id, _s) = b.fresh_local(sphere_n.clone());
        let e = b.mk_pi(s_id, BinderInfo::Default, sphere_n, alpha.clone());
        let e = b.mk_pi(f_id, BinderInfo::Default, bm_ty, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.BasedMap.eval", ty));
    }

    // ================================================================
    // 6. Topology.BasedMap.preserves_basepoint : {α : Type u} → [TopologicalSpace α] →
    //    {n : ℕ} → {x₀ : α} → (f : BasedMap n x₀) →
    //    Eq α (BasedMap.eval f (Sphere.basepoint n)) x₀
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let bm_ty = ctx.based_map(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let (f_id, f) = b.fresh_local(bm_ty.clone());

        // f.eval applied to sphere basepoint
        let f_eval = ctx.based_map_eval(alpha.clone(), inst.clone(), n.clone(), x0.clone(), f);
        let basepoint = ctx.sphere_basepoint(n.clone());
        let f_at_basepoint = Expr::app(f_eval, basepoint);

        // Eq at universe u+1 (since α : Type u)
        let eq_expr = ctx.mk_eq(
            Level::succ(ctx.u_level.clone()),
            alpha.clone(),
            f_at_basepoint,
            x0.clone(),
        );

        let e = b.mk_pi(f_id, BinderInfo::Default, bm_ty, eq_expr);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.BasedMap.preserves_basepoint", ty));
    }

    // ================================================================
    // 7. Topology.BasedHomotopy : {α : Type u} → [TopologicalSpace α] →
    //    {n : ℕ} → {x₀ : α} → BasedMap n x₀ → BasedMap n x₀ → Type u
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let bm_ty = ctx.based_map(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let (f_id, _f) = b.fresh_local(bm_ty.clone());
        let (g_id, _g) = b.fresh_local(bm_ty.clone());
        let e = b.mk_pi(g_id, BinderInfo::Default, bm_ty.clone(), ctx.type_u.clone());
        let e = b.mk_pi(f_id, BinderInfo::Default, bm_ty, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.BasedHomotopy", ty));
    }

    // ================================================================
    // 8. Topology.HigherHomotopyGroup : {α : Type u} → [TopologicalSpace α] →
    //    ℕ → α → Type u
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, _inst) = b.fresh_local(ts_ty.clone());
        let (n_id, _n) = b.fresh_local(ctx.nat_const());
        let (x0_id, _x0) = b.fresh_local(alpha.clone());
        let e = b.mk_pi(
            x0_id,
            BinderInfo::Default,
            alpha.clone(),
            ctx.type_u.clone(),
        );
        let e = b.mk_pi(n_id, BinderInfo::Default, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.HigherHomotopyGroup", ty));
    }

    // ================================================================
    // 9. Topology.HigherHomotopyGroup.class : {α : Type u} → [TopologicalSpace α] →
    //    {n : ℕ} → {x₀ : α} → BasedMap n x₀ → HigherHomotopyGroup n x₀
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let bm_ty = ctx.based_map(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let (f_id, _f) = b.fresh_local(bm_ty.clone());
        let hhg_ty = ctx.higher_homotopy_group(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let e = b.mk_pi(f_id, BinderInfo::Default, bm_ty, hhg_ty);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.HigherHomotopyGroup.class", ty));
    }

    // ================================================================
    // 10. Topology.HigherHomotopyGroup.class_eq : {α : Type u} → [TopologicalSpace α] →
    //     {n : ℕ} → {x₀ : α} → {f g : BasedMap n x₀} →
    //     BasedHomotopy f g → Eq (HigherHomotopyGroup n x₀) (class f) (class g)
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let bm_ty = ctx.based_map(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let (f_id, f) = b.fresh_local(bm_ty.clone());
        let (g_id, g) = b.fresh_local(bm_ty.clone());
        let homotopy_ty = ctx.based_homotopy(
            alpha.clone(),
            inst.clone(),
            n.clone(),
            x0.clone(),
            f.clone(),
            g.clone(),
        );
        let (h_id, _h) = b.fresh_local(homotopy_ty.clone());

        let hhg_type =
            ctx.higher_homotopy_group(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let class_f = ctx.hhg_class(alpha.clone(), inst.clone(), n.clone(), x0.clone(), f);
        let class_g = ctx.hhg_class(alpha.clone(), inst.clone(), n.clone(), x0.clone(), g);
        let eq_expr = ctx.mk_eq(Level::succ(ctx.u_level.clone()), hhg_type, class_f, class_g);

        let e = b.mk_pi(h_id, BinderInfo::Default, homotopy_ty, eq_expr);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, bm_ty.clone(), e);
        let e = b.mk_pi(f_id, BinderInfo::Implicit, bm_ty, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.HigherHomotopyGroup.class_eq", ty));
    }

    // ================================================================
    // 11. Topology.HigherHomotopyGroup.mul : {α : Type u} → [TopologicalSpace α] →
    //     {n : ℕ} → (0 < n) → {x₀ : α} → πₙ → πₙ → πₙ
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let lt_n = Expr::app(Expr::app(ctx.nat_lt(), ctx.nat_zero()), n.clone());
        let (hn_id, _hn) = b.fresh_local(lt_n.clone());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let hhg = ctx.higher_homotopy_group(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let (a_id, _a) = b.fresh_local(hhg.clone());
        let (b_id2, _b_val) = b.fresh_local(hhg.clone());
        let e = b.mk_pi(b_id2, BinderInfo::Default, hhg.clone(), hhg.clone());
        let e = b.mk_pi(a_id, BinderInfo::Default, hhg, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(hn_id, BinderInfo::Default, lt_n, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.HigherHomotopyGroup.mul", ty));
    }

    // ================================================================
    // 12. Topology.HigherHomotopyGroup.one : {α : Type u} → [TopologicalSpace α] →
    //     {n : ℕ} → (0 < n) → {x₀ : α} → πₙ
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let lt_n = Expr::app(Expr::app(ctx.nat_lt(), ctx.nat_zero()), n.clone());
        let (hn_id, _hn) = b.fresh_local(lt_n.clone());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let hhg = ctx.higher_homotopy_group(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), hhg);
        let e = b.mk_pi(hn_id, BinderInfo::Default, lt_n, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.HigherHomotopyGroup.one", ty));
    }

    // ================================================================
    // 13. Topology.HigherHomotopyGroup.inv : {α : Type u} → [TopologicalSpace α] →
    //     {n : ℕ} → (0 < n) → {x₀ : α} → πₙ → πₙ
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let lt_n = Expr::app(Expr::app(ctx.nat_lt(), ctx.nat_zero()), n.clone());
        let (hn_id, _hn) = b.fresh_local(lt_n.clone());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let hhg = ctx.higher_homotopy_group(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let (a_id, _a) = b.fresh_local(hhg.clone());
        let e = b.mk_pi(a_id, BinderInfo::Default, hhg.clone(), hhg);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(hn_id, BinderInfo::Default, lt_n, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.HigherHomotopyGroup.inv", ty));
    }

    // ================================================================
    // 14. mul_assoc : {α} → [TS α] → {n} → (0 < n) → {x₀} → (a b c : πₙ) → Prop
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let lt_n = Expr::app(Expr::app(ctx.nat_lt(), ctx.nat_zero()), n.clone());
        let (hn_id, _hn) = b.fresh_local(lt_n.clone());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let hhg = ctx.higher_homotopy_group(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let (a_id, _a) = b.fresh_local(hhg.clone());
        let (b_id2, _b_val) = b.fresh_local(hhg.clone());
        let (c_id, _c) = b.fresh_local(hhg.clone());
        let e = b.mk_pi(c_id, BinderInfo::Default, hhg.clone(), ctx.prop.clone());
        let e = b.mk_pi(b_id2, BinderInfo::Default, hhg.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, hhg, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(hn_id, BinderInfo::Default, lt_n, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.HigherHomotopyGroup.mul_assoc", ty));
    }

    // ================================================================
    // 15. one_mul : {α} → [TS α] → {n} → (0 < n) → {x₀} → (a : πₙ) → Prop
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let lt_n = Expr::app(Expr::app(ctx.nat_lt(), ctx.nat_zero()), n.clone());
        let (hn_id, _hn) = b.fresh_local(lt_n.clone());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let hhg = ctx.higher_homotopy_group(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let (a_id, _a) = b.fresh_local(hhg.clone());
        let e = b.mk_pi(a_id, BinderInfo::Default, hhg, ctx.prop.clone());
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(hn_id, BinderInfo::Default, lt_n, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.HigherHomotopyGroup.one_mul", ty));
    }

    // ================================================================
    // 16. mul_one : same shape as one_mul
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let lt_n = Expr::app(Expr::app(ctx.nat_lt(), ctx.nat_zero()), n.clone());
        let (hn_id, _hn) = b.fresh_local(lt_n.clone());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let hhg = ctx.higher_homotopy_group(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let (a_id, _a) = b.fresh_local(hhg.clone());
        let e = b.mk_pi(a_id, BinderInfo::Default, hhg, ctx.prop.clone());
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(hn_id, BinderInfo::Default, lt_n, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.HigherHomotopyGroup.mul_one", ty));
    }

    // ================================================================
    // 17. mul_inv : same shape as one_mul
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let lt_n = Expr::app(Expr::app(ctx.nat_lt(), ctx.nat_zero()), n.clone());
        let (hn_id, _hn) = b.fresh_local(lt_n.clone());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let hhg = ctx.higher_homotopy_group(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let (a_id, _a) = b.fresh_local(hhg.clone());
        let e = b.mk_pi(a_id, BinderInfo::Default, hhg, ctx.prop.clone());
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(hn_id, BinderInfo::Default, lt_n, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.HigherHomotopyGroup.mul_inv", ty));
    }

    // ================================================================
    // 18. mul_comm : {α} → [TS α] → {n} → (1 < n) → {x₀} → (a b : πₙ) → Prop
    //     Note: condition is n > 1 (abelian for n ≥ 2)
    // ================================================================
    {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = ctx.topological_space(ctx.u_level.clone(), alpha.clone());
        let (ts_id, inst) = b.fresh_local(ts_ty.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let lt_1_n = Expr::app(Expr::app(ctx.nat_lt(), ctx.nat_one()), n.clone());
        let (hn_id, _hn) = b.fresh_local(lt_1_n.clone());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let hhg = ctx.higher_homotopy_group(alpha.clone(), inst.clone(), n.clone(), x0.clone());
        let (a_id, _a) = b.fresh_local(hhg.clone());
        let (b_id2, _b_val) = b.fresh_local(hhg.clone());
        let e = b.mk_pi(b_id2, BinderInfo::Default, hhg.clone(), ctx.prop.clone());
        let e = b.mk_pi(a_id, BinderInfo::Default, hhg, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(hn_id, BinderInfo::Default, lt_1_n, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.axiom_u("Topology.HigherHomotopyGroup.mul_comm", ty));
    }

    debug_assert_eq!(
        decls.len(),
        DECL_COUNT,
        "payload size mismatch for {NAMESPACE}"
    );
    debug_assert_eq!(
        decls.iter().map(|c| c.name.to_string()).collect::<Vec<_>>(),
        DECL_NAMES.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
        "payload names mismatch for {NAMESPACE}"
    );

    decls
}
