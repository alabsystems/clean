// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.Cobordism namespace (#1444).
//!
//! Migrated from 37 inline `add_decl` calls in `topology_algebraic2.rs`.
//! Uses `EnvDeclBuilder` for structured types; eliminates manual de Bruijn
//! index arithmetic from the cobordism declarations.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Cobordism";
pub(crate) const DECL_COUNT: usize = 40;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    // Part 1: Basic cobordism structures
    "Topology.Cobordism.Manifold",
    "Topology.Cobordism.boundary",
    "Topology.Cobordism.Cobordant",
    "Topology.Cobordism.cobordant_refl",
    "Topology.Cobordism.cobordant_symm",
    "Topology.Cobordism.cobordant_trans",
    "Topology.Cobordism.Cobordism",
    // Part 2: Cobordism groups
    "Topology.Cobordism.CobordismGroup",
    "Topology.Cobordism.OrientedCobordismGroup",
    "Topology.Cobordism.FramedCobordismGroup",
    "Topology.Cobordism.SpinCobordismGroup",
    "Topology.Cobordism.cobordism_class",
    "Topology.Cobordism.disjoint_union",
    "Topology.Cobordism.empty_manifold",
    // Part 3: Thom spaces and Pontryagin-Thom
    "Topology.Cobordism.ThomSpace",
    "Topology.Cobordism.thom_class",
    "Topology.Cobordism.thom_isomorphism",
    "Topology.Cobordism.pontryagin_thom",
    "Topology.Cobordism.pontryagin_thom_iso",
    // Part 4: Cobordism ring structure
    "Topology.Cobordism.CobordismRing",
    "Topology.Cobordism.OrientedCobordismRing",
    "Topology.Cobordism.ring_product",
    "Topology.Cobordism.thom_structure_theorem",
    // Part 5: h-Cobordism and surgery
    "Topology.Cobordism.hCobordism",
    "Topology.Cobordism.h_cobordism_theorem",
    "Topology.Cobordism.Surgery",
    "Topology.Cobordism.perform_surgery",
    "Topology.Cobordism.surgery_cobordant",
    // Part 6: Characteristic numbers
    "Topology.Cobordism.StiefelWhitneyNumber",
    "Topology.Cobordism.PontryaginNumber",
    "Topology.Cobordism.characteristic_cobordism_invariant",
    // Part 7: Bordism spectra
    "Topology.Cobordism.MOSpectrum",
    "Topology.Cobordism.MSOSpectrum",
    "Topology.Cobordism.MUSpectrum",
    "Topology.Cobordism.spectrum_homology",
    "Topology.Cobordism.MO_homology_cobordism",
    // Part 8: Complex cobordism and formal groups
    "Topology.Cobordism.ComplexCobordismGroup",
    "Topology.Cobordism.FormalGroupLaw",
    "Topology.Cobordism.MU_formal_group",
    "Topology.Cobordism.quillen_theorem",
];

struct CobCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl CobCtx {
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

    fn nat_const(&self) -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }

    fn int_const(&self) -> Expr {
        Expr::const_(Name::from_string("Int"), vec![])
    }

    fn manifold(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Cobordism.Manifold"),
            vec![self.u_level.clone()],
        )
    }

    fn cobordant(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Cobordism.Cobordant"),
            vec![self.u_level.clone()],
        )
    }

    fn cobordism_group(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Cobordism.CobordismGroup"),
            vec![self.u_level.clone()],
        )
    }

    fn framed_cobordism_group(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Cobordism.FramedCobordismGroup"),
            vec![self.u_level.clone()],
        )
    }

    fn thom_space(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Cobordism.ThomSpace"),
            vec![self.u_level.clone()],
        )
    }

    fn cobordism_ring(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Cobordism.CobordismRing"),
            vec![self.u_level.clone()],
        )
    }

    fn formal_group_law(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Cobordism.FormalGroupLaw"),
            vec![self.u_level.clone()],
        )
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

    fn to_prop_axiom(&self, name: &str, levels: Vec<Name>) -> ConstantInfo {
        ConstantInfo {
            name: Name::from_string(name),
            level_params: levels,
            type_: self.prop.clone(),
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        }
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = CobCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    let nat_to_type_u = Expr::pi(BinderInfo::Default, ctx.nat_const(), ctx.type_u.clone());

    // ================================================================
    // Part 1: Basic cobordism structures
    // ================================================================

    // Manifold : Nat → Type u
    decls.push(ctx.to_axiom("Topology.Cobordism.Manifold", nat_to_type_u.clone()));

    // boundary : {n : Nat} → Manifold n → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m_id, _m) = b.fresh_local(mn.clone());
        let r = b.mk_pi(m_id, BinderInfo::Default, mn, ctx.type_u.clone());
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.boundary", b.finish(r)));
    }

    // Cobordant : {n : Nat} → Manifold n → Manifold n → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m1_id, _m1) = b.fresh_local(mn.clone());
        let (m2_id, _m2) = b.fresh_local(mn.clone());
        let r = b.mk_pi(m2_id, BinderInfo::Default, mn.clone(), ctx.prop.clone());
        let r = b.mk_pi(m1_id, BinderInfo::Default, mn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.Cobordant", b.finish(r)));
    }

    // cobordant_refl : {n : Nat} → (M : Manifold n) → Cobordant n M M
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m_id, m) = b.fresh_local(mn.clone());
        let body = Expr::app(
            Expr::app(Expr::app(ctx.cobordant(), n.clone()), m.clone()),
            m.clone(),
        );
        let r = b.mk_pi(m_id, BinderInfo::Default, mn, body);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.cobordant_refl", b.finish(r)));
    }

    // cobordant_symm : {n : Nat} → {M : Manifold n} → {N : Manifold n} → Prop → Prop
    // (simplified: Cobordant M N → Cobordant N M, but types are placeholder Prop)
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, _n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), _n.clone());
        let (m_id, _m) = b.fresh_local(mn.clone());
        let (nn_id, _nn) = b.fresh_local(mn.clone());
        let (h_id, _h) = b.fresh_local(ctx.prop.clone());
        let r = b.mk_pi(
            h_id,
            BinderInfo::Default,
            ctx.prop.clone(),
            ctx.prop.clone(),
        );
        let r = b.mk_pi(nn_id, BinderInfo::Implicit, mn.clone(), r);
        let r = b.mk_pi(m_id, BinderInfo::Implicit, mn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.cobordant_symm", b.finish(r)));
    }

    // cobordant_trans : {n : Nat} → {M N P : Manifold n} → Prop → Prop → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, _n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), _n.clone());
        let (m_id, _m) = b.fresh_local(mn.clone());
        let (nn_id, _nn) = b.fresh_local(mn.clone());
        let (p_id, _p) = b.fresh_local(mn.clone());
        let (h1_id, _h1) = b.fresh_local(ctx.prop.clone());
        let (h2_id, _h2) = b.fresh_local(ctx.prop.clone());
        let r = b.mk_pi(
            h2_id,
            BinderInfo::Default,
            ctx.prop.clone(),
            ctx.prop.clone(),
        );
        let r = b.mk_pi(h1_id, BinderInfo::Default, ctx.prop.clone(), r);
        let r = b.mk_pi(p_id, BinderInfo::Implicit, mn.clone(), r);
        let r = b.mk_pi(nn_id, BinderInfo::Implicit, mn.clone(), r);
        let r = b.mk_pi(m_id, BinderInfo::Implicit, mn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.cobordant_trans", b.finish(r)));
    }

    // Cobordism : {n : Nat} → Manifold n → Manifold n → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m1_id, _m1) = b.fresh_local(mn.clone());
        let (m2_id, _m2) = b.fresh_local(mn.clone());
        let r = b.mk_pi(m2_id, BinderInfo::Default, mn.clone(), ctx.type_u.clone());
        let r = b.mk_pi(m1_id, BinderInfo::Default, mn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.Cobordism", b.finish(r)));
    }

    // ================================================================
    // Part 2: Cobordism groups
    // ================================================================

    // CobordismGroup, OrientedCobordismGroup, FramedCobordismGroup, SpinCobordismGroup : Nat → Type u
    for name in [
        "Topology.Cobordism.CobordismGroup",
        "Topology.Cobordism.OrientedCobordismGroup",
        "Topology.Cobordism.FramedCobordismGroup",
        "Topology.Cobordism.SpinCobordismGroup",
    ] {
        decls.push(ctx.to_axiom(name, nat_to_type_u.clone()));
    }

    // cobordism_class : {n : Nat} → Manifold n → CobordismGroup n
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m_id, _m) = b.fresh_local(mn.clone());
        let body = Expr::app(ctx.cobordism_group(), n.clone());
        let r = b.mk_pi(m_id, BinderInfo::Default, mn, body);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.cobordism_class", b.finish(r)));
    }

    // disjoint_union : {n : Nat} → Manifold n → Manifold n → Manifold n
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m1_id, _m1) = b.fresh_local(mn.clone());
        let (m2_id, _m2) = b.fresh_local(mn.clone());
        let r = b.mk_pi(m2_id, BinderInfo::Default, mn.clone(), mn.clone());
        let r = b.mk_pi(m1_id, BinderInfo::Default, mn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.disjoint_union", b.finish(r)));
    }

    // empty_manifold : {n : Nat} → Manifold n
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), mn);
        decls.push(ctx.to_axiom("Topology.Cobordism.empty_manifold", b.finish(r)));
    }

    // ================================================================
    // Part 3: Thom spaces and Pontryagin-Thom
    // ================================================================

    // ThomSpace : {n : Nat} → Type u → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, _n) = b.fresh_local(ctx.nat_const());
        let (e_id, _e) = b.fresh_local(ctx.type_u.clone());
        let r = b.mk_pi(
            e_id,
            BinderInfo::Default,
            ctx.type_u.clone(),
            ctx.type_u.clone(),
        );
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.ThomSpace", b.finish(r)));
    }

    // thom_class : {n : Nat} → {E : Type u} → ThomSpace n E → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let (e_id, e) = b.fresh_local(ctx.type_u.clone());
        let ts = Expr::app(Expr::app(ctx.thom_space(), n.clone()), e.clone());
        let (t_id, _t) = b.fresh_local(ts.clone());
        let r = b.mk_pi(t_id, BinderInfo::Default, ts, ctx.type_u.clone());
        let r = b.mk_pi(e_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.thom_class", b.finish(r)));
    }

    // thom_isomorphism : {k n : Nat} → {B E : Type u} → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (k_id, _k) = b.fresh_local(ctx.nat_const());
        let (n_id, _n) = b.fresh_local(ctx.nat_const());
        let (bb_id, _bb) = b.fresh_local(ctx.type_u.clone());
        let (e_id, _e) = b.fresh_local(ctx.type_u.clone());
        let r = b.mk_pi(
            e_id,
            BinderInfo::Implicit,
            ctx.type_u.clone(),
            ctx.prop.clone(),
        );
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        let r = b.mk_pi(k_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.thom_isomorphism", b.finish(r)));
    }

    // pontryagin_thom : {n : Nat} → FramedCobordismGroup n → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let fcg = Expr::app(ctx.framed_cobordism_group(), n.clone());
        let (f_id, _f) = b.fresh_local(fcg.clone());
        let r = b.mk_pi(f_id, BinderInfo::Default, fcg, ctx.type_u.clone());
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.pontryagin_thom", b.finish(r)));
    }

    // pontryagin_thom_iso : {n : Nat} → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, _n) = b.fresh_local(ctx.nat_const());
        let r = b.mk_pi(
            n_id,
            BinderInfo::Implicit,
            ctx.nat_const(),
            ctx.prop.clone(),
        );
        decls.push(ctx.to_axiom("Topology.Cobordism.pontryagin_thom_iso", b.finish(r)));
    }

    // ================================================================
    // Part 4: Cobordism ring structure
    // ================================================================

    // CobordismRing, OrientedCobordismRing : Type u
    decls.push(ctx.to_axiom("Topology.Cobordism.CobordismRing", ctx.type_u.clone()));
    decls.push(ctx.to_axiom(
        "Topology.Cobordism.OrientedCobordismRing",
        ctx.type_u.clone(),
    ));

    // ring_product : CobordismRing → CobordismRing → CobordismRing
    {
        let cr = ctx.cobordism_ring();
        let type_ = Expr::pi(
            BinderInfo::Default,
            cr.clone(),
            Expr::pi(BinderInfo::Default, cr.clone(), cr),
        );
        decls.push(ctx.to_axiom("Topology.Cobordism.ring_product", type_));
    }

    // thom_structure_theorem : Prop (no level params)
    decls.push(ctx.to_prop_axiom("Topology.Cobordism.thom_structure_theorem", vec![]));

    // ================================================================
    // Part 5: h-Cobordism and surgery
    // ================================================================

    // hCobordism : {n : Nat} → Manifold n → Manifold n → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m1_id, _m1) = b.fresh_local(mn.clone());
        let (m2_id, _m2) = b.fresh_local(mn.clone());
        let r = b.mk_pi(m2_id, BinderInfo::Default, mn.clone(), ctx.type_u.clone());
        let r = b.mk_pi(m1_id, BinderInfo::Default, mn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.hCobordism", b.finish(r)));
    }

    // h_cobordism_theorem : {n : Nat} → {M : Manifold n} → {N : Manifold n} → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m_id, _m) = b.fresh_local(mn.clone());
        let (nn_id, _nn) = b.fresh_local(mn.clone());
        let r = b.mk_pi(nn_id, BinderInfo::Implicit, mn.clone(), ctx.prop.clone());
        let r = b.mk_pi(m_id, BinderInfo::Implicit, mn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.h_cobordism_theorem", b.finish(r)));
    }

    // Surgery : {n : Nat} → Manifold n → Nat → Nat → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m_id, _m) = b.fresh_local(mn.clone());
        let (p_id, _p) = b.fresh_local(ctx.nat_const());
        let (q_id, _q) = b.fresh_local(ctx.nat_const());
        let r = b.mk_pi(
            q_id,
            BinderInfo::Default,
            ctx.nat_const(),
            ctx.type_u.clone(),
        );
        let r = b.mk_pi(p_id, BinderInfo::Default, ctx.nat_const(), r);
        let r = b.mk_pi(m_id, BinderInfo::Default, mn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.Surgery", b.finish(r)));
    }

    // perform_surgery : {n : Nat} → {M : Manifold n} → {p q : Nat} → Type u → Manifold n
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m_id, _m) = b.fresh_local(mn.clone());
        let (p_id, _p) = b.fresh_local(ctx.nat_const());
        let (q_id, _q) = b.fresh_local(ctx.nat_const());
        let (s_id, _s) = b.fresh_local(ctx.type_u.clone());
        let r = b.mk_pi(s_id, BinderInfo::Default, ctx.type_u.clone(), mn.clone());
        let r = b.mk_pi(q_id, BinderInfo::Implicit, ctx.nat_const(), r);
        let r = b.mk_pi(p_id, BinderInfo::Implicit, ctx.nat_const(), r);
        let r = b.mk_pi(m_id, BinderInfo::Implicit, mn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.perform_surgery", b.finish(r)));
    }

    // surgery_cobordant : {n : Nat} → {M : Manifold n} → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m_id, _m) = b.fresh_local(mn.clone());
        let r = b.mk_pi(m_id, BinderInfo::Implicit, mn, ctx.prop.clone());
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.surgery_cobordant", b.finish(r)));
    }

    // ================================================================
    // Part 6: Characteristic numbers
    // ================================================================

    // StiefelWhitneyNumber : {n : Nat} → Manifold n → Type u → Nat
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m_id, _m) = b.fresh_local(mn.clone());
        let (l_id, _l) = b.fresh_local(ctx.type_u.clone());
        let r = b.mk_pi(
            l_id,
            BinderInfo::Default,
            ctx.type_u.clone(),
            ctx.nat_const(),
        );
        let r = b.mk_pi(m_id, BinderInfo::Default, mn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.StiefelWhitneyNumber", b.finish(r)));
    }

    // PontryaginNumber : {n : Nat} → Manifold n → Type u → Int
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m_id, _m) = b.fresh_local(mn.clone());
        let (l_id, _l) = b.fresh_local(ctx.type_u.clone());
        let r = b.mk_pi(
            l_id,
            BinderInfo::Default,
            ctx.type_u.clone(),
            ctx.int_const(),
        );
        let r = b.mk_pi(m_id, BinderInfo::Default, mn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom("Topology.Cobordism.PontryaginNumber", b.finish(r)));
    }

    // characteristic_cobordism_invariant : {n : Nat} → {M N : Manifold n} → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let mn = Expr::app(ctx.manifold(), n.clone());
        let (m_id, _m) = b.fresh_local(mn.clone());
        let (nn_id, _nn) = b.fresh_local(mn.clone());
        let r = b.mk_pi(nn_id, BinderInfo::Implicit, mn.clone(), ctx.prop.clone());
        let r = b.mk_pi(m_id, BinderInfo::Implicit, mn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        decls.push(ctx.to_axiom(
            "Topology.Cobordism.characteristic_cobordism_invariant",
            b.finish(r),
        ));
    }

    // ================================================================
    // Part 7: Bordism spectra
    // ================================================================

    // MOSpectrum, MSOSpectrum, MUSpectrum : Type u
    for name in [
        "Topology.Cobordism.MOSpectrum",
        "Topology.Cobordism.MSOSpectrum",
        "Topology.Cobordism.MUSpectrum",
    ] {
        decls.push(ctx.to_axiom(name, ctx.type_u.clone()));
    }

    // spectrum_homology : Type u → Type u → Nat → Type u
    {
        let type_ = Expr::pi(
            BinderInfo::Default,
            ctx.type_u.clone(),
            Expr::pi(
                BinderInfo::Default,
                ctx.type_u.clone(),
                Expr::pi(BinderInfo::Default, ctx.nat_const(), ctx.type_u.clone()),
            ),
        );
        decls.push(ctx.to_axiom("Topology.Cobordism.spectrum_homology", type_));
    }

    // MO_homology_cobordism : {n : Nat} → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, _n) = b.fresh_local(ctx.nat_const());
        let r = b.mk_pi(
            n_id,
            BinderInfo::Implicit,
            ctx.nat_const(),
            ctx.prop.clone(),
        );
        decls.push(ctx.to_axiom("Topology.Cobordism.MO_homology_cobordism", b.finish(r)));
    }

    // ================================================================
    // Part 8: Complex cobordism and formal groups
    // ================================================================

    // ComplexCobordismGroup : Nat → Type u
    decls.push(ctx.to_axiom("Topology.Cobordism.ComplexCobordismGroup", nat_to_type_u));

    // FormalGroupLaw : Type u
    decls.push(ctx.to_axiom("Topology.Cobordism.FormalGroupLaw", ctx.type_u.clone()));

    // MU_formal_group : FormalGroupLaw
    decls.push(ctx.to_axiom("Topology.Cobordism.MU_formal_group", ctx.formal_group_law()));

    // quillen_theorem : Prop (no level params)
    decls.push(ctx.to_prop_axiom("Topology.Cobordism.quillen_theorem", vec![]));

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
