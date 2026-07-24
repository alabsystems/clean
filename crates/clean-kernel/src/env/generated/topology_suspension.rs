// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.Suspension namespace (#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Suspension";
pub(crate) const DECL_COUNT: usize = 22;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Suspension",
    "Topology.Suspension.north",
    "Topology.Suspension.south",
    "Topology.Suspension.merid",
    "Topology.Suspension.topological_space",
    "Topology.Cone",
    "Topology.Cone.apex",
    "Topology.Cone.base_incl",
    "Topology.Cone.path_to_apex",
    "Topology.Cone.topological_space",
    "Topology.Cone.contractible",
    "Topology.Suspension.map",
    "Topology.Suspension.map_north",
    "Topology.Suspension.map_south",
    "Topology.Suspension.map_continuous",
    "Topology.Suspension.sphere_succ",
    "Topology.Suspension.freudenthal",
    "Topology.Suspension.join_cones",
    "Topology.Suspension.rec",
    "Topology.Cone.rec",
    "Topology.Suspension.map_id",
    "Topology.Suspension.map_comp",
];

struct SuspCtx {
    u: Name,
    v: Name,
    w: Name,
    u_level: Level,
    v_level: Level,
    w_level: Level,
    type_u: Expr,
    type_v: Expr,
    type_w: Expr,
    prop: Expr,
}

impl SuspCtx {
    fn new() -> Self {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let w = Name::from_string("w");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let w_level = Level::param(w.clone());
        Self {
            type_u: Expr::sort(Level::succ(u_level.clone())),
            type_v: Expr::sort(Level::succ(v_level.clone())),
            type_w: Expr::sort(Level::succ(w_level.clone())),
            prop: Expr::sort(Level::zero()),
            u,
            v,
            w,
            u_level,
            v_level,
            w_level,
        }
    }

    fn suspension(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("Topology.Suspension"), vec![lvl])
    }

    fn suspension_north(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("Topology.Suspension.north"), vec![lvl])
    }

    fn suspension_south(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("Topology.Suspension.south"), vec![lvl])
    }

    fn suspension_map(&self, lvl1: Level, lvl2: Level) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Suspension.map"),
            vec![lvl1, lvl2],
        )
    }

    fn cone(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("Topology.Cone"), vec![lvl])
    }

    fn cone_apex(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("Topology.Cone.apex"), vec![lvl])
    }

    fn cone_base_incl(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("Topology.Cone.base_incl"), vec![lvl])
    }

    fn topological_space(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl])
    }

    fn eq_const(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("Eq"), vec![lvl])
    }

    fn continuous(&self, lvl1: Level, lvl2: Level) -> Expr {
        Expr::const_(Name::from_string("Topology.Continuous"), vec![lvl1, lvl2])
    }

    fn nat_type(&self) -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }

    fn nat_succ(&self) -> Expr {
        Expr::const_(Name::from_string("Nat.succ"), vec![])
    }

    fn sphere(&self) -> Expr {
        Expr::const_(Name::from_string("Topology.Sphere"), vec![])
    }

    fn to_axiom_u(&self, name: &str, type_: Expr) -> ConstantInfo {
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

    fn to_axiom_uv(&self, name: &str, type_: Expr) -> ConstantInfo {
        ConstantInfo {
            name: Name::from_string(name),
            level_params: vec![self.u.clone(), self.v.clone()],
            type_,
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        }
    }

    fn to_axiom_uvw(&self, name: &str, type_: Expr) -> ConstantInfo {
        ConstantInfo {
            name: Name::from_string(name),
            level_params: vec![self.u.clone(), self.v.clone(), self.w.clone()],
            type_,
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        }
    }

    fn to_axiom_empty(&self, name: &str, type_: Expr) -> ConstantInfo {
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
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = SuspCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    // 1. Topology.Suspension : Type u → Type u
    {
        let ty = Expr::pi(BinderInfo::Default, ctx.type_u.clone(), ctx.type_u.clone());
        decls.push(ctx.to_axiom_u("Topology.Suspension", ty));
    }

    // 2. Topology.Suspension.north : {α : Type u} → Suspension α
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let body = Expr::app(ctx.suspension(ctx.u_level.clone()), a);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), body);
        decls.push(ctx.to_axiom_u("Topology.Suspension.north", b.finish(e)));
    }

    // 3. Topology.Suspension.south : {α : Type u} → Suspension α
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let body = Expr::app(ctx.suspension(ctx.u_level.clone()), a);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), body);
        decls.push(ctx.to_axiom_u("Topology.Suspension.south", b.finish(e)));
    }

    // 4. Topology.Suspension.merid : {α : Type u} → α → Eq (Suspension α) north south
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let (x_id, _x) = b.fresh_local(a.clone());
        let susp_a = Expr::app(ctx.suspension(ctx.u_level.clone()), a.clone());
        let north = Expr::app(ctx.suspension_north(ctx.u_level.clone()), a.clone());
        let south = Expr::app(ctx.suspension_south(ctx.u_level.clone()), a.clone());
        let body = Expr::app(
            Expr::app(
                Expr::app(ctx.eq_const(Level::succ(ctx.u_level.clone())), susp_a),
                north,
            ),
            south,
        );
        let e = b.mk_pi(x_id, BinderInfo::Default, a.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_u("Topology.Suspension.merid", b.finish(e)));
    }

    // 5. Topology.Suspension.topological_space : {α : Type u} → [TS α] → TS (Suspension α)
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let ts_a_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), a.clone());
        let (ts_id, _ts) = b.fresh_local(ts_a_ty.clone());
        let susp_a = Expr::app(ctx.suspension(ctx.u_level.clone()), a);
        let body = Expr::app(ctx.topological_space(ctx.u_level.clone()), susp_a);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_a_ty, body);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_u("Topology.Suspension.topological_space", b.finish(e)));
    }

    // 6. Topology.Cone : Type u → Type u
    {
        let ty = Expr::pi(BinderInfo::Default, ctx.type_u.clone(), ctx.type_u.clone());
        decls.push(ctx.to_axiom_u("Topology.Cone", ty));
    }

    // 7. Topology.Cone.apex : {α : Type u} → Cone α
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let body = Expr::app(ctx.cone(ctx.u_level.clone()), a);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), body);
        decls.push(ctx.to_axiom_u("Topology.Cone.apex", b.finish(e)));
    }

    // 8. Topology.Cone.base_incl : {α : Type u} → α → Cone α
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let (x_id, _x) = b.fresh_local(a.clone());
        let body = Expr::app(ctx.cone(ctx.u_level.clone()), a.clone());
        let e = b.mk_pi(x_id, BinderInfo::Default, a.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_u("Topology.Cone.base_incl", b.finish(e)));
    }

    // 9. Topology.Cone.path_to_apex : {α : Type u} → (x : α) → Eq (Cone α) (base_incl x) apex
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let (x_id, x) = b.fresh_local(a.clone());
        let cone_a = Expr::app(ctx.cone(ctx.u_level.clone()), a.clone());
        let base_incl_x = Expr::app(
            Expr::app(ctx.cone_base_incl(ctx.u_level.clone()), a.clone()),
            x,
        );
        let apex = Expr::app(ctx.cone_apex(ctx.u_level.clone()), a.clone());
        let body = Expr::app(
            Expr::app(
                Expr::app(ctx.eq_const(Level::succ(ctx.u_level.clone())), cone_a),
                base_incl_x,
            ),
            apex,
        );
        let e = b.mk_pi(x_id, BinderInfo::Default, a.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_u("Topology.Cone.path_to_apex", b.finish(e)));
    }

    // 10. Topology.Cone.topological_space : {α : Type u} → [TS α] → TS (Cone α)
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let ts_a_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), a.clone());
        let (ts_id, _ts) = b.fresh_local(ts_a_ty.clone());
        let cone_a = Expr::app(ctx.cone(ctx.u_level.clone()), a);
        let body = Expr::app(ctx.topological_space(ctx.u_level.clone()), cone_a);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_a_ty, body);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_u("Topology.Cone.topological_space", b.finish(e)));
    }

    // 11. Topology.Cone.contractible : {α : Type u} → [TS α] → Contractible (Cone α)
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let ts_a_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), a.clone());
        let (ts_id, ts) = b.fresh_local(ts_a_ty.clone());
        let cone_a = Expr::app(ctx.cone(ctx.u_level.clone()), a.clone());
        let cone_ts_inst = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Topology.Cone.topological_space"),
                    vec![ctx.u_level.clone()],
                ),
                a,
            ),
            ts,
        );
        let body = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Topology.Contractible"),
                    vec![ctx.u_level.clone()],
                ),
                cone_a,
            ),
            cone_ts_inst,
        );
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_a_ty, body);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_u("Topology.Cone.contractible", b.finish(e)));
    }

    // 12. Topology.Suspension.map : {α : Type u} → {β : Type v} → (α → β) → Σα → Σβ
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let (bt_id, bt) = b.fresh_local(ctx.type_v.clone());
        let f_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (p_id, _p) = c.fresh_local(a.clone());
            let r = c.mk_pi(p_id, BinderInfo::Default, a.clone(), bt.clone());
            c.finish_child(r)
        };
        let (f_id, _f) = b.fresh_local(f_ty.clone());
        let (s_id, _s) = b.fresh_local(Expr::app(ctx.suspension(ctx.u_level.clone()), a.clone()));
        let body = Expr::app(ctx.suspension(ctx.v_level.clone()), bt.clone());
        let e = b.mk_pi(
            s_id,
            BinderInfo::Default,
            Expr::app(ctx.suspension(ctx.u_level.clone()), a.clone()),
            body,
        );
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(bt_id, BinderInfo::Implicit, ctx.type_v.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_uv("Topology.Suspension.map", b.finish(e)));
    }

    // 13. Topology.Suspension.map_north : {α : Type u} → {β : Type v} →
    //     (f : α → β) → Eq (Σβ) (map f north) north
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let (bt_id, bt) = b.fresh_local(ctx.type_v.clone());
        let f_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (p_id, _p) = c.fresh_local(a.clone());
            let r = c.mk_pi(p_id, BinderInfo::Default, a.clone(), bt.clone());
            c.finish_child(r)
        };
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let susp_bt = Expr::app(ctx.suspension(ctx.v_level.clone()), bt.clone());
        let north_a = Expr::app(ctx.suspension_north(ctx.u_level.clone()), a.clone());
        let map_f_north = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        ctx.suspension_map(ctx.u_level.clone(), ctx.v_level.clone()),
                        a.clone(),
                    ),
                    bt.clone(),
                ),
                f,
            ),
            north_a,
        );
        let north_bt = Expr::app(ctx.suspension_north(ctx.v_level.clone()), bt.clone());
        let body = Expr::app(
            Expr::app(
                Expr::app(ctx.eq_const(Level::succ(ctx.v_level.clone())), susp_bt),
                map_f_north,
            ),
            north_bt,
        );
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, body);
        let e = b.mk_pi(bt_id, BinderInfo::Implicit, ctx.type_v.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_uv("Topology.Suspension.map_north", b.finish(e)));
    }

    // 14. Topology.Suspension.map_south : {α : Type u} → {β : Type v} →
    //     (f : α → β) → Eq (Σβ) (map f south) south
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let (bt_id, bt) = b.fresh_local(ctx.type_v.clone());
        let f_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (p_id, _p) = c.fresh_local(a.clone());
            let r = c.mk_pi(p_id, BinderInfo::Default, a.clone(), bt.clone());
            c.finish_child(r)
        };
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let susp_bt = Expr::app(ctx.suspension(ctx.v_level.clone()), bt.clone());
        let south_a = Expr::app(ctx.suspension_south(ctx.u_level.clone()), a.clone());
        let map_f_south = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        ctx.suspension_map(ctx.u_level.clone(), ctx.v_level.clone()),
                        a.clone(),
                    ),
                    bt.clone(),
                ),
                f,
            ),
            south_a,
        );
        let south_bt = Expr::app(ctx.suspension_south(ctx.v_level.clone()), bt.clone());
        let body = Expr::app(
            Expr::app(
                Expr::app(ctx.eq_const(Level::succ(ctx.v_level.clone())), susp_bt),
                map_f_south,
            ),
            south_bt,
        );
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, body);
        let e = b.mk_pi(bt_id, BinderInfo::Implicit, ctx.type_v.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_uv("Topology.Suspension.map_south", b.finish(e)));
    }

    // 15. Topology.Suspension.map_continuous : {α : Type u} → {β : Type v} →
    //     [TS α] → [TS β] → (f : α → β) → Continuous f → Continuous (map f)
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let (bt_id, bt) = b.fresh_local(ctx.type_v.clone());
        let ts_a_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), a.clone());
        let (tsa_id, tsa) = b.fresh_local(ts_a_ty.clone());
        let ts_b_ty = Expr::app(ctx.topological_space(ctx.v_level.clone()), bt.clone());
        let (tsb_id, tsb) = b.fresh_local(ts_b_ty.clone());
        let f_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (p_id, _p) = c.fresh_local(a.clone());
            let r = c.mk_pi(p_id, BinderInfo::Default, a.clone(), bt.clone());
            c.finish_child(r)
        };
        let (f_id, f) = b.fresh_local(f_ty.clone());
        // hf : Continuous α β tsa tsb f
        let cont_f = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            ctx.continuous(ctx.u_level.clone(), ctx.v_level.clone()),
                            a.clone(),
                        ),
                        bt.clone(),
                    ),
                    tsa.clone(),
                ),
                tsb.clone(),
            ),
            f.clone(),
        );
        let (hf_id, _hf) = b.fresh_local(cont_f.clone());
        // Continuous (Suspension α) (Suspension β) susp_inst_α susp_inst_β (Suspension.map f)
        let susp_a = Expr::app(ctx.suspension(ctx.u_level.clone()), a.clone());
        let susp_bt = Expr::app(ctx.suspension(ctx.v_level.clone()), bt.clone());
        let susp_ts_a = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Topology.Suspension.topological_space"),
                    vec![ctx.u_level.clone()],
                ),
                a.clone(),
            ),
            tsa,
        );
        let susp_ts_b = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Topology.Suspension.topological_space"),
                    vec![ctx.v_level.clone()],
                ),
                bt.clone(),
            ),
            tsb,
        );
        let susp_map_f = Expr::app(
            Expr::app(
                Expr::app(
                    ctx.suspension_map(ctx.u_level.clone(), ctx.v_level.clone()),
                    a.clone(),
                ),
                bt.clone(),
            ),
            f,
        );
        let body = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            ctx.continuous(ctx.u_level.clone(), ctx.v_level.clone()),
                            susp_a,
                        ),
                        susp_bt,
                    ),
                    susp_ts_a,
                ),
                susp_ts_b,
            ),
            susp_map_f,
        );
        let e = b.mk_pi(hf_id, BinderInfo::Default, cont_f, body);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(tsb_id, BinderInfo::InstImplicit, ts_b_ty, e);
        let e = b.mk_pi(tsa_id, BinderInfo::InstImplicit, ts_a_ty, e);
        let e = b.mk_pi(bt_id, BinderInfo::Implicit, ctx.type_v.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_uv("Topology.Suspension.map_continuous", b.finish(e)));
    }

    // 16. Topology.Suspension.sphere_succ : (n : Nat) →
    //     ∃ (f : Suspension (Sphere n) → Sphere (n+1))
    //       (g : Sphere (n+1) → Suspension (Sphere n)),
    //       Homeomorphism (Suspension (Sphere n)) (Sphere (n+1)) f g
    //
    // The classical `Σ Sⁿ ≃ Sⁿ⁺¹`. `Topology.Homeomorphism` is a Prop over
    // {α β} [TS α] [TS β] (f : α → β) (g : β → α), so the equivalence is stated
    // as the existence of a homeomorphism pair (f, g). The instance arguments
    // are the genuine registered instances:
    //   TS (Suspension (Sphere n)) := Suspension.topological_space
    //                                   (Sphere n) (Sphere.topological_space n)
    //   TS (Sphere (n+1))          := Sphere.topological_space (n+1)
    // HISTORY: this record previously applied `Homeomorphism` to `n : Nat` in
    // both instance positions ("placeholder for instances") and omitted f/g —
    // ill-typed, tolerated only while the overlay lane loaded via
    // `extend_constants_unchecked`. Pillar-1 G4 (commit f184e058) routed the
    // lane through `extend_constants_checked` (infer_sort on every record),
    // which rejects the placeholder form and fail-closed the whole
    // Suspension/Cone/KTheory init chain. `Exists` is registered before this
    // overlay loads (init_topology_suspension → init_topology_contractible →
    // init_exists).
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_type());
        let sphere_n = Expr::app(ctx.sphere(), n.clone());
        let susp_sphere_n = Expr::app(ctx.suspension(Level::zero()), sphere_n.clone());
        let n_plus_1 = Expr::app(ctx.nat_succ(), n.clone());
        let sphere_n_plus_1 = Expr::app(ctx.sphere(), n_plus_1.clone());

        let sphere_ts = Expr::const_(
            Name::from_string("Topology.Sphere.topological_space"),
            vec![],
        );
        let inst_susp_sphere_n = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Topology.Suspension.topological_space"),
                    vec![Level::zero()],
                ),
                sphere_n.clone(),
            ),
            Expr::app(sphere_ts.clone(), n.clone()),
        );
        let inst_sphere_n_plus_1 = Expr::app(sphere_ts, n_plus_1.clone());

        let f_ty = Expr::arrow(susp_sphere_n.clone(), sphere_n_plus_1.clone());
        let g_ty = Expr::arrow(sphere_n_plus_1.clone(), susp_sphere_n.clone());
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let (g_id, g) = b.fresh_local(g_ty.clone());

        let homeo_f_g = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(
                                    Name::from_string("Topology.Homeomorphism"),
                                    vec![Level::zero(), Level::zero()],
                                ),
                                susp_sphere_n,
                            ),
                            sphere_n_plus_1,
                        ),
                        inst_susp_sphere_n,
                    ),
                    inst_sphere_n_plus_1,
                ),
                f,
            ),
            g,
        );

        // Exists.{1} : {α : Sort 1} → (α → Prop) → Prop; both map types live
        // in Type 0 = Sort 1.
        let exists_1 = Expr::const_(
            Name::from_string("Exists"),
            vec![Level::succ(Level::zero())],
        );
        let exists_g = Expr::app(
            Expr::app(exists_1.clone(), g_ty.clone()),
            b.mk_lam(g_id, BinderInfo::Default, g_ty, homeo_f_g),
        );
        let exists_f_g = Expr::app(
            Expr::app(exists_1, f_ty.clone()),
            b.mk_lam(f_id, BinderInfo::Default, f_ty, exists_g),
        );
        let e = b.mk_pi(n_id, BinderInfo::Default, ctx.nat_type(), exists_f_g);
        decls.push(ctx.to_axiom_empty("Topology.Suspension.sphere_succ", b.finish(e)));
    }

    // 17. Topology.Suspension.freudenthal : {α : Type u} → [TS α] →
    //     (x₀ : α) → (n : Nat) → HigherHomotopyGroup n x₀ → HigherHomotopyGroup (n+1) north
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let ts_a_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), a.clone());
        let (ts_id, ts) = b.fresh_local(ts_a_ty.clone());
        let (x0_id, x0) = b.fresh_local(a.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_type());
        let higher_homotopy_group = Expr::const_(
            Name::from_string("Topology.HigherHomotopyGroup"),
            vec![ctx.u_level.clone()],
        );
        // HigherHomotopyGroup α ts n x₀
        let hhg_n_x0 = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(higher_homotopy_group.clone(), a.clone()),
                    ts.clone(),
                ),
                n.clone(),
            ),
            x0,
        );
        let (h_id, _h) = b.fresh_local(hhg_n_x0.clone());
        // HigherHomotopyGroup (Suspension α) susp_ts (n+1) north
        let susp_a = Expr::app(ctx.suspension(ctx.u_level.clone()), a.clone());
        let north_susp = Expr::app(ctx.suspension_north(ctx.u_level.clone()), a.clone());
        let n_plus_1 = Expr::app(ctx.nat_succ(), n);
        let susp_top_space = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Topology.Suspension.topological_space"),
                    vec![ctx.u_level.clone()],
                ),
                a.clone(),
            ),
            ts,
        );
        let body = Expr::app(
            Expr::app(
                Expr::app(Expr::app(higher_homotopy_group, susp_a), susp_top_space),
                n_plus_1,
            ),
            north_susp,
        );
        let e = b.mk_pi(h_id, BinderInfo::Default, hhg_n_x0, body);
        let e = b.mk_pi(n_id, BinderInfo::Default, ctx.nat_type(), e);
        let e = b.mk_pi(x0_id, BinderInfo::Default, a.clone(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_a_ty, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_u("Topology.Suspension.freudenthal", b.finish(e)));
    }

    // 18. Topology.Suspension.join_cones : {α : Type u} → [TS α] → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let ts_a_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), a);
        let (ts_id, _ts) = b.fresh_local(ts_a_ty.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_a_ty, ctx.prop.clone());
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_u("Topology.Suspension.join_cones", b.finish(e)));
    }

    // 19. Topology.Suspension.rec : {α : Type u} → {β : Type v} →
    //     (north_val : β) → (south_val : β) →
    //     (merid_val : α → north_val = south_val) →
    //     Suspension α → β
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let (bt_id, bt) = b.fresh_local(ctx.type_v.clone());
        let (nv_id, nv) = b.fresh_local(bt.clone());
        let (sv_id, sv) = b.fresh_local(bt.clone());
        // merid_val : α → Eq β nv sv
        let merid_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (p_id, _p) = c.fresh_local(a.clone());
            let eq_nv_sv = Expr::app(
                Expr::app(
                    Expr::app(ctx.eq_const(Level::succ(ctx.v_level.clone())), bt.clone()),
                    nv.clone(),
                ),
                sv.clone(),
            );
            let r = c.mk_pi(p_id, BinderInfo::Default, a.clone(), eq_nv_sv);
            c.finish_child(r)
        };
        let (mv_id, _mv) = b.fresh_local(merid_ty.clone());
        let susp_a = Expr::app(ctx.suspension(ctx.u_level.clone()), a.clone());
        let (s_id, _s) = b.fresh_local(susp_a.clone());
        let e = b.mk_pi(s_id, BinderInfo::Default, susp_a, bt.clone());
        let e = b.mk_pi(mv_id, BinderInfo::Default, merid_ty, e);
        let e = b.mk_pi(sv_id, BinderInfo::Default, bt.clone(), e);
        let e = b.mk_pi(nv_id, BinderInfo::Default, bt.clone(), e);
        let e = b.mk_pi(bt_id, BinderInfo::Implicit, ctx.type_v.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_uv("Topology.Suspension.rec", b.finish(e)));
    }

    // 20. Topology.Cone.rec : {α : Type u} → {β : Type v} →
    //     (apex_val : β) → (base_val : α → β) →
    //     (path_val : ∀ x, base_val x = apex_val) →
    //     Cone α → β
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let (bt_id, bt) = b.fresh_local(ctx.type_v.clone());
        let (av_id, av) = b.fresh_local(bt.clone());
        // base_val : α → β
        let bv_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (p_id, _p) = c.fresh_local(a.clone());
            let r = c.mk_pi(p_id, BinderInfo::Default, a.clone(), bt.clone());
            c.finish_child(r)
        };
        let (bv_id, bv) = b.fresh_local(bv_ty.clone());
        // path_val : ∀ (x : α), Eq β (base_val x) apex_val
        let pv_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = c.fresh_local(a.clone());
            let eq_body = Expr::app(
                Expr::app(
                    Expr::app(ctx.eq_const(Level::succ(ctx.v_level.clone())), bt.clone()),
                    Expr::app(bv.clone(), x),
                ),
                av.clone(),
            );
            let r = c.mk_pi(x_id, BinderInfo::Default, a.clone(), eq_body);
            c.finish_child(r)
        };
        let (pv_id, _pv) = b.fresh_local(pv_ty.clone());
        let cone_a = Expr::app(ctx.cone(ctx.u_level.clone()), a.clone());
        let (c_id, _c) = b.fresh_local(cone_a.clone());
        let e = b.mk_pi(c_id, BinderInfo::Default, cone_a, bt.clone());
        let e = b.mk_pi(pv_id, BinderInfo::Default, pv_ty, e);
        let e = b.mk_pi(bv_id, BinderInfo::Default, bv_ty, e);
        let e = b.mk_pi(av_id, BinderInfo::Default, bt.clone(), e);
        let e = b.mk_pi(bt_id, BinderInfo::Implicit, ctx.type_v.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_uv("Topology.Cone.rec", b.finish(e)));
    }

    // 21. Topology.Suspension.map_id : {α : Type u} → Prop
    {
        let ty = Expr::pi(BinderInfo::Implicit, ctx.type_u.clone(), ctx.prop.clone());
        decls.push(ctx.to_axiom_u("Topology.Suspension.map_id", ty));
    }

    // 22. Topology.Suspension.map_comp : {α : Type u} → {β : Type v} → {γ : Type w} →
    //     (f : α → β) → (g : β → γ) → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(ctx.type_u.clone());
        let (bt_id, bt) = b.fresh_local(ctx.type_v.clone());
        let (gm_id, gm) = b.fresh_local(ctx.type_w.clone());
        let f_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (p_id, _p) = c.fresh_local(a.clone());
            let r = c.mk_pi(p_id, BinderInfo::Default, a.clone(), bt.clone());
            c.finish_child(r)
        };
        let (f_id, _f) = b.fresh_local(f_ty.clone());
        let g_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (p_id, _p) = c.fresh_local(bt.clone());
            let r = c.mk_pi(p_id, BinderInfo::Default, bt.clone(), gm.clone());
            c.finish_child(r)
        };
        let (g_id, _g) = b.fresh_local(g_ty.clone());
        let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, ctx.prop.clone());
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(gm_id, BinderInfo::Implicit, ctx.type_w.clone(), e);
        let e = b.mk_pi(bt_id, BinderInfo::Implicit, ctx.type_v.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_uvw("Topology.Suspension.map_comp", b.finish(e)));
    }

    assert_eq!(decls.len(), DECL_COUNT);
    decls
}
