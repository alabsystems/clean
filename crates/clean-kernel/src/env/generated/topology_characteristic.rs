// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.Characteristic namespace (#1444).
//!
//! Migrated from 47 inline `add_decl` calls in `topology_algebraic2.rs`.
//! Uses `EnvDeclBuilder` for structured types; eliminates manual de Bruijn
//! index arithmetic from the characteristic class declarations.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Characteristic";
pub(crate) const DECL_COUNT: usize = 50;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    // Part 1: Cohomology rings
    "Topology.Characteristic.CohomologyRing",
    "Topology.Characteristic.Z2CohomologyRing",
    // Part 2: Stiefel-Whitney classes
    "Topology.Characteristic.RealVectorBundle",
    "Topology.Characteristic.stiefel_whitney",
    "Topology.Characteristic.total_stiefel_whitney",
    "Topology.Characteristic.sw_zero",
    "Topology.Characteristic.sw_vanishes_above_rank",
    "Topology.Characteristic.sw_naturality",
    "Topology.Characteristic.whitney_sum_formula",
    // Part 3: Chern classes
    "Topology.Characteristic.ComplexVectorBundle",
    "Topology.Characteristic.chern",
    "Topology.Characteristic.total_chern",
    "Topology.Characteristic.chern_zero",
    "Topology.Characteristic.chern_vanishes_above_rank",
    "Topology.Characteristic.chern_naturality",
    "Topology.Characteristic.chern_whitney_sum",
    "Topology.Characteristic.first_chern_line_bundle",
    // Part 4: Pontryagin classes
    "Topology.Characteristic.pontryagin",
    "Topology.Characteristic.total_pontryagin",
    "Topology.Characteristic.pontryagin_via_chern",
    "Topology.Characteristic.pontryagin_naturality",
    // Part 5: Euler class
    "Topology.Characteristic.OrientedBundle",
    "Topology.Characteristic.euler",
    "Topology.Characteristic.euler_square_pontryagin",
    "Topology.Characteristic.euler_mod2_sw",
    "Topology.Characteristic.euler_self_intersection",
    // Part 6: Chern character and Todd class
    "Topology.Characteristic.chern_character",
    "Topology.Characteristic.chern_character_additive",
    "Topology.Characteristic.chern_character_multiplicative",
    "Topology.Characteristic.todd",
    "Topology.Characteristic.hirzebruch_riemann_roch",
    // Part 7: Wu classes
    "Topology.Characteristic.wu",
    "Topology.Characteristic.wu_formula",
    // Part 8: Classifying spaces
    "Topology.Characteristic.BO",
    "Topology.Characteristic.BU",
    "Topology.Characteristic.BSO",
    "Topology.Characteristic.universal_real_bundle",
    "Topology.Characteristic.universal_complex_bundle",
    "Topology.Characteristic.classifying_map",
    "Topology.Characteristic.pullback_universal",
    // Part 9: Splitting principle
    "Topology.Characteristic.FlagBundle",
    "Topology.Characteristic.splitting_principle",
    "Topology.Characteristic.flag_injection",
    // Part 10: A-hat genus and index theory
    "Topology.Characteristic.a_hat",
    "Topology.Characteristic.l_genus",
    "Topology.Characteristic.atiyah_singer",
    "Topology.Characteristic.hirzebruch_signature",
    // Part 11: Thom isomorphism and Gysin
    "Topology.Characteristic.thom_isomorphism",
    "Topology.Characteristic.gysin_sequence",
    "Topology.Characteristic.euler_gysin",
];

struct CharCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl CharCtx {
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

    fn cohomology_ring(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Characteristic.CohomologyRing"),
            vec![self.u_level.clone()],
        )
    }

    fn z2_cohomology_ring(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Characteristic.Z2CohomologyRing"),
            vec![self.u_level.clone()],
        )
    }

    fn real_bundle(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Characteristic.RealVectorBundle"),
            vec![self.u_level.clone()],
        )
    }

    fn complex_bundle(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Characteristic.ComplexVectorBundle"),
            vec![self.u_level.clone()],
        )
    }

    fn oriented_bundle(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Characteristic.OrientedBundle"),
            vec![self.u_level.clone()],
        )
    }

    fn bo(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Characteristic.BO"),
            vec![self.u_level.clone()],
        )
    }

    fn bu(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Characteristic.BU"),
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

    /// {X : Type u} → {n : Nat} → Bundle X n → Nat → Target X
    fn build_class_type(&self, bundle: Expr, target: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (n_id, n) = b.fresh_local(self.nat_const());
        let bxn = Expr::app(Expr::app(bundle, x.clone()), n.clone());
        let (e_id, _e) = b.fresh_local(bxn.clone());
        let (i_id, _i) = b.fresh_local(self.nat_const());
        let body = Expr::app(target, x.clone());
        let r = b.mk_pi(i_id, BinderInfo::Default, self.nat_const(), body);
        let r = b.mk_pi(e_id, BinderInfo::Default, bxn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, self.nat_const(), r);
        let r = b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(r)
    }

    /// {X : Type u} → {n : Nat} → Bundle X n → Target X
    fn build_total_class_type(&self, bundle: Expr, target: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (n_id, n) = b.fresh_local(self.nat_const());
        let bxn = Expr::app(Expr::app(bundle, x.clone()), n.clone());
        let (e_id, _e) = b.fresh_local(bxn.clone());
        let body = Expr::app(target, x.clone());
        let r = b.mk_pi(e_id, BinderInfo::Default, bxn, body);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, self.nat_const(), r);
        let r = b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(r)
    }

    /// {X : Type u} → {n : Nat} → Bundle X n → Type u
    fn build_bundle_to_type(&self, bundle: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (n_id, n) = b.fresh_local(self.nat_const());
        let bxn = Expr::app(Expr::app(bundle, x.clone()), n.clone());
        let (e_id, _e) = b.fresh_local(bxn.clone());
        let r = b.mk_pi(e_id, BinderInfo::Default, bxn, self.type_u.clone());
        let r = b.mk_pi(n_id, BinderInfo::Implicit, self.nat_const(), r);
        let r = b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(r)
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = CharCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    // Shared type shapes
    let type_u_to_type_u = Expr::pi(BinderInfo::Default, ctx.type_u.clone(), ctx.type_u.clone());
    let type_u_nat_type_u = Expr::pi(
        BinderInfo::Default,
        ctx.type_u.clone(),
        Expr::pi(BinderInfo::Default, ctx.nat_const(), ctx.type_u.clone()),
    );
    let nat_to_type_u = Expr::pi(BinderInfo::Default, ctx.nat_const(), ctx.type_u.clone());

    // Part 1: Cohomology rings
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.CohomologyRing",
        type_u_to_type_u.clone(),
    ));
    decls.push(ctx.to_axiom("Topology.Characteristic.Z2CohomologyRing", type_u_to_type_u));

    // Part 2: Stiefel-Whitney classes
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.RealVectorBundle",
        type_u_nat_type_u.clone(),
    ));
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.stiefel_whitney",
        ctx.build_class_type(ctx.real_bundle(), ctx.z2_cohomology_ring()),
    ));
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.total_stiefel_whitney",
        ctx.build_total_class_type(ctx.real_bundle(), ctx.z2_cohomology_ring()),
    ));
    for name in [
        "Topology.Characteristic.sw_zero",
        "Topology.Characteristic.sw_vanishes_above_rank",
        "Topology.Characteristic.sw_naturality",
        "Topology.Characteristic.whitney_sum_formula",
    ] {
        decls.push(ctx.to_prop_axiom(name, vec![ctx.u.clone()]));
    }

    // Part 3: Chern classes
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.ComplexVectorBundle",
        type_u_nat_type_u.clone(),
    ));
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.chern",
        ctx.build_class_type(ctx.complex_bundle(), ctx.cohomology_ring()),
    ));
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.total_chern",
        ctx.build_total_class_type(ctx.complex_bundle(), ctx.cohomology_ring()),
    ));
    for name in [
        "Topology.Characteristic.chern_zero",
        "Topology.Characteristic.chern_vanishes_above_rank",
        "Topology.Characteristic.chern_naturality",
        "Topology.Characteristic.chern_whitney_sum",
    ] {
        decls.push(ctx.to_prop_axiom(name, vec![ctx.u.clone()]));
    }
    decls.push(ctx.to_prop_axiom("Topology.Characteristic.first_chern_line_bundle", vec![]));

    // Part 4: Pontryagin classes
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.pontryagin",
        ctx.build_class_type(ctx.real_bundle(), ctx.cohomology_ring()),
    ));
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.total_pontryagin",
        ctx.build_total_class_type(ctx.real_bundle(), ctx.cohomology_ring()),
    ));
    for name in [
        "Topology.Characteristic.pontryagin_via_chern",
        "Topology.Characteristic.pontryagin_naturality",
    ] {
        decls.push(ctx.to_prop_axiom(name, vec![ctx.u.clone()]));
    }

    // Part 5: Euler class
    decls.push(ctx.to_axiom("Topology.Characteristic.OrientedBundle", type_u_nat_type_u));
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.euler",
        ctx.build_total_class_type(ctx.oriented_bundle(), ctx.cohomology_ring()),
    ));
    for name in [
        "Topology.Characteristic.euler_square_pontryagin",
        "Topology.Characteristic.euler_mod2_sw",
    ] {
        decls.push(ctx.to_prop_axiom(name, vec![ctx.u.clone()]));
    }
    decls.push(ctx.to_prop_axiom("Topology.Characteristic.euler_self_intersection", vec![]));

    // Part 6: Chern character and Todd class
    let chern_char_type = ctx.build_total_class_type(ctx.complex_bundle(), ctx.cohomology_ring());
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.chern_character",
        chern_char_type.clone(),
    ));
    for name in [
        "Topology.Characteristic.chern_character_additive",
        "Topology.Characteristic.chern_character_multiplicative",
    ] {
        decls.push(ctx.to_prop_axiom(name, vec![ctx.u.clone()]));
    }
    decls.push(ctx.to_axiom("Topology.Characteristic.todd", chern_char_type));
    decls.push(ctx.to_prop_axiom("Topology.Characteristic.hirzebruch_riemann_roch", vec![]));

    // Part 7: Wu classes
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.wu",
        ctx.build_class_type(ctx.real_bundle(), ctx.z2_cohomology_ring()),
    ));
    decls.push(ctx.to_prop_axiom("Topology.Characteristic.wu_formula", vec![ctx.u.clone()]));

    // Part 8: Classifying spaces
    for name in [
        "Topology.Characteristic.BO",
        "Topology.Characteristic.BU",
        "Topology.Characteristic.BSO",
    ] {
        decls.push(ctx.to_axiom(name, nat_to_type_u.clone()));
    }

    // universal_real_bundle : (n : Nat) → RealVectorBundle (BO n) n
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let bo_n = Expr::app(ctx.bo(), n.clone());
        let body = Expr::app(Expr::app(ctx.real_bundle(), bo_n), n.clone());
        let r = b.mk_pi(n_id, BinderInfo::Default, ctx.nat_const(), body);
        decls.push(ctx.to_axiom("Topology.Characteristic.universal_real_bundle", b.finish(r)));
    }

    // universal_complex_bundle : (n : Nat) → ComplexVectorBundle (BU n) n
    {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let bu_n = Expr::app(ctx.bu(), n.clone());
        let body = Expr::app(Expr::app(ctx.complex_bundle(), bu_n), n.clone());
        let r = b.mk_pi(n_id, BinderInfo::Default, ctx.nat_const(), body);
        decls.push(ctx.to_axiom(
            "Topology.Characteristic.universal_complex_bundle",
            b.finish(r),
        ));
    }

    // classifying_map : {X : Type u} → {n : Nat} → RealVectorBundle X n → X → BO n
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(ctx.type_u.clone());
        let (n_id, n) = b.fresh_local(ctx.nat_const());
        let bxn = Expr::app(Expr::app(ctx.real_bundle(), x.clone()), n.clone());
        let (e_id, _e) = b.fresh_local(bxn.clone());
        let (pt_id, _pt) = b.fresh_local(x.clone());
        let bo_n = Expr::app(ctx.bo(), n.clone());
        let r = b.mk_pi(pt_id, BinderInfo::Default, x.clone(), bo_n);
        let r = b.mk_pi(e_id, BinderInfo::Default, bxn, r);
        let r = b.mk_pi(n_id, BinderInfo::Implicit, ctx.nat_const(), r);
        let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
        decls.push(ctx.to_axiom("Topology.Characteristic.classifying_map", b.finish(r)));
    }

    decls.push(ctx.to_prop_axiom("Topology.Characteristic.pullback_universal", vec![]));

    // Part 9: Splitting principle
    decls.push(ctx.to_axiom(
        "Topology.Characteristic.FlagBundle",
        ctx.build_bundle_to_type(ctx.complex_bundle()),
    ));
    for name in [
        "Topology.Characteristic.splitting_principle",
        "Topology.Characteristic.flag_injection",
    ] {
        decls.push(ctx.to_prop_axiom(name, vec![]));
    }

    // Part 10: A-hat genus and index theory
    let a_hat_type = ctx.build_total_class_type(ctx.real_bundle(), ctx.cohomology_ring());
    decls.push(ctx.to_axiom("Topology.Characteristic.a_hat", a_hat_type.clone()));
    decls.push(ctx.to_axiom("Topology.Characteristic.l_genus", a_hat_type));
    for name in [
        "Topology.Characteristic.atiyah_singer",
        "Topology.Characteristic.hirzebruch_signature",
    ] {
        decls.push(ctx.to_prop_axiom(name, vec![]));
    }

    // Part 11: Thom isomorphism and Gysin
    for name in [
        "Topology.Characteristic.thom_isomorphism",
        "Topology.Characteristic.gysin_sequence",
        "Topology.Characteristic.euler_gysin",
    ] {
        decls.push(ctx.to_prop_axiom(name, vec![]));
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
