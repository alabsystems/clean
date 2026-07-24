// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.Scheme namespace (#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Scheme";
pub(crate) const DECL_COUNT: usize = 35;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Scheme.Scheme",
    "Topology.Scheme.Spec",
    "Topology.Scheme.morphism",
    "Topology.Scheme.id",
    "Topology.Scheme.comp",
    "Topology.Scheme.is_isomorphism",
    "Topology.Scheme.open_immersion",
    "Topology.Scheme.closed_immersion",
    "Topology.Scheme.underlying_space",
    "Topology.Scheme.structure_sheaf",
    "Topology.Scheme.affine_open_cover",
    "Topology.Scheme.separated",
    "Topology.Scheme.quasi_compact",
    "Topology.Scheme.quasi_separated",
    "Topology.Scheme.noetherian",
    "Topology.Scheme.integral",
    "Topology.Scheme.reduced",
    "Topology.Scheme.normal",
    "Topology.Scheme.global_sections",
    "Topology.Scheme.pullback",
    "Topology.Scheme.fiber_product",
    "Topology.Scheme.proper",
    "Topology.Scheme.smooth",
    "Topology.Scheme.etale",
    "Topology.Scheme.flat",
    "Topology.Scheme.finite_type",
    "Topology.Scheme.coherent_sheaf",
    "Topology.Scheme.invertible_sheaf",
    "Topology.Scheme.line_bundle",
    "Topology.Scheme.divisor",
    "Topology.Scheme.cartier_divisor",
    "Topology.Scheme.picard_group",
    "Topology.Scheme.scheme_gluing",
    "Topology.Scheme.spec_adjoint_global_sections",
    "Topology.Scheme.base_change",
];

struct SchemeCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl SchemeCtx {
    fn new() -> Self {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        Self {
            u,
            u_level: u_level.clone(),
            type_u: Expr::sort(Level::succ(u_level)),
            prop: Expr::sort(Level::zero()),
        }
    }

    fn scheme_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Scheme.Scheme"),
            vec![self.u_level.clone()],
        )
    }

    fn morphism_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Scheme.morphism"),
            vec![self.u_level.clone()],
        )
    }

    fn morphism_app(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(Expr::app(self.morphism_const(), x), y)
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

    // Spec : {R : Type u} → [CommRing R] → Scheme
    fn build_spec_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (r_id, r) = b.fresh_local(self.type_u.clone());
        let comm_ring_r = Expr::app(
            Expr::const_(Name::from_string("CommRing"), vec![self.u_level.clone()]),
            r,
        );
        let (cr_id, _) = b.fresh_local(comm_ring_r.clone());
        let r = b.mk_pi(
            cr_id,
            BinderInfo::InstImplicit,
            comm_ring_r,
            self.scheme_const(),
        );
        b.finish(b.mk_pi(r_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // morphism : Scheme → Scheme → Type u
    fn build_morphism_type(&self) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.scheme_const(),
            Expr::pi(
                BinderInfo::Default,
                self.scheme_const(),
                self.type_u.clone(),
            ),
        )
    }

    // id : (X : Scheme) → morphism X X → Prop
    fn build_id_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.scheme_const());
        let morph_xx = self.morphism_app(x.clone(), x);
        let (m_id, _) = b.fresh_local(morph_xx.clone());
        let r = b.mk_pi(m_id, BinderInfo::Default, morph_xx, self.prop.clone());
        b.finish(b.mk_pi(x_id, BinderInfo::Default, self.scheme_const(), r))
    }

    // comp : (X Y Z : Scheme) → morphism X Y → morphism Y Z → morphism X Z
    fn build_comp_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.scheme_const());
        let (y_id, y) = b.fresh_local(self.scheme_const());
        let (z_id, z) = b.fresh_local(self.scheme_const());
        let morph_xy = self.morphism_app(x.clone(), y.clone());
        let morph_yz = self.morphism_app(y, z.clone());
        let morph_xz = self.morphism_app(x, z);
        let (fxy_id, _) = b.fresh_local(morph_xy.clone());
        let (fyz_id, _) = b.fresh_local(morph_yz.clone());
        let r = b.mk_pi(fyz_id, BinderInfo::Default, morph_yz, morph_xz);
        let r = b.mk_pi(fxy_id, BinderInfo::Default, morph_xy, r);
        let r = b.mk_pi(z_id, BinderInfo::Default, self.scheme_const(), r);
        let r = b.mk_pi(y_id, BinderInfo::Default, self.scheme_const(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Default, self.scheme_const(), r))
    }

    // is_isomorphism / open_immersion / closed_immersion :
    //   (X Y : Scheme) → morphism X Y → Prop
    fn build_morphism_predicate_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.scheme_const());
        let (y_id, y) = b.fresh_local(self.scheme_const());
        let morph_xy = self.morphism_app(x, y);
        let (m_id, _) = b.fresh_local(morph_xy.clone());
        let r = b.mk_pi(m_id, BinderInfo::Default, morph_xy, self.prop.clone());
        let r = b.mk_pi(y_id, BinderInfo::Default, self.scheme_const(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Default, self.scheme_const(), r))
    }

    // Scheme → Type u (underlying_space, structure_sheaf, global_sections, picard_group)
    fn build_scheme_to_type(&self) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.scheme_const(),
            self.type_u.clone(),
        )
    }

    // Scheme → Prop (affine_open_cover, separated, ..., divisor, cartier_divisor)
    fn build_scheme_prop(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.scheme_const(), self.prop.clone())
    }

    // Scheme → Scheme → Scheme → Scheme (pullback, fiber_product)
    fn build_triple_scheme_type(&self) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.scheme_const(),
            Expr::pi(
                BinderInfo::Default,
                self.scheme_const(),
                Expr::pi(
                    BinderInfo::Default,
                    self.scheme_const(),
                    self.scheme_const(),
                ),
            ),
        )
    }

    // Scheme → Type u → Prop (coherent_sheaf, invertible_sheaf, line_bundle)
    fn build_scheme_type_prop(&self) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.scheme_const(),
            Expr::pi(BinderInfo::Default, self.type_u.clone(), self.prop.clone()),
        )
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = SchemeCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    // 1. Scheme : Type u
    decls.push(ctx.to_axiom("Topology.Scheme.Scheme", ctx.type_u.clone()));

    // 2. Spec
    decls.push(ctx.to_axiom("Topology.Scheme.Spec", ctx.build_spec_type()));

    // 3. morphism
    decls.push(ctx.to_axiom("Topology.Scheme.morphism", ctx.build_morphism_type()));

    // 4. id
    decls.push(ctx.to_axiom("Topology.Scheme.id", ctx.build_id_type()));

    // 5. comp
    decls.push(ctx.to_axiom("Topology.Scheme.comp", ctx.build_comp_type()));

    // 6-8. is_isomorphism, open_immersion, closed_immersion
    let morph_pred = ctx.build_morphism_predicate_type();
    decls.push(ctx.to_axiom("Topology.Scheme.is_isomorphism", morph_pred.clone()));
    decls.push(ctx.to_axiom("Topology.Scheme.open_immersion", morph_pred.clone()));
    decls.push(ctx.to_axiom("Topology.Scheme.closed_immersion", morph_pred.clone()));

    // 9-10. underlying_space, structure_sheaf (Scheme → Type u)
    let scheme_to_type = ctx.build_scheme_to_type();
    decls.push(ctx.to_axiom("Topology.Scheme.underlying_space", scheme_to_type.clone()));
    decls.push(ctx.to_axiom("Topology.Scheme.structure_sheaf", scheme_to_type.clone()));

    // 11. affine_open_cover (Scheme → Prop)
    let scheme_prop = ctx.build_scheme_prop();
    decls.push(ctx.to_axiom("Topology.Scheme.affine_open_cover", scheme_prop.clone()));

    // 12-18. separation properties
    for name in [
        "Topology.Scheme.separated",
        "Topology.Scheme.quasi_compact",
        "Topology.Scheme.quasi_separated",
        "Topology.Scheme.noetherian",
        "Topology.Scheme.integral",
        "Topology.Scheme.reduced",
        "Topology.Scheme.normal",
    ] {
        decls.push(ctx.to_axiom(name, scheme_prop.clone()));
    }

    // 19. global_sections (Scheme → Type u)
    decls.push(ctx.to_axiom("Topology.Scheme.global_sections", scheme_to_type.clone()));

    // 20-21. pullback, fiber_product (Scheme → Scheme → Scheme → Scheme)
    let triple = ctx.build_triple_scheme_type();
    decls.push(ctx.to_axiom("Topology.Scheme.pullback", triple.clone()));
    decls.push(ctx.to_axiom("Topology.Scheme.fiber_product", triple));

    // 22-26. morphism properties (proper, smooth, etale, flat, finite_type)
    for name in [
        "Topology.Scheme.proper",
        "Topology.Scheme.smooth",
        "Topology.Scheme.etale",
        "Topology.Scheme.flat",
        "Topology.Scheme.finite_type",
    ] {
        decls.push(ctx.to_axiom(name, morph_pred.clone()));
    }

    // 27-29. coherent_sheaf, invertible_sheaf, line_bundle (Scheme → Type u → Prop)
    let scheme_type_prop = ctx.build_scheme_type_prop();
    decls.push(ctx.to_axiom("Topology.Scheme.coherent_sheaf", scheme_type_prop.clone()));
    decls.push(ctx.to_axiom("Topology.Scheme.invertible_sheaf", scheme_type_prop.clone()));
    decls.push(ctx.to_axiom("Topology.Scheme.line_bundle", scheme_type_prop));

    // 30-31. divisor, cartier_divisor (Scheme → Prop)
    decls.push(ctx.to_axiom("Topology.Scheme.divisor", scheme_prop.clone()));
    decls.push(ctx.to_axiom("Topology.Scheme.cartier_divisor", scheme_prop));

    // 32. picard_group (Scheme → Type u)
    decls.push(ctx.to_axiom("Topology.Scheme.picard_group", scheme_to_type));

    // 33-35. scheme_gluing, spec_adjoint_global_sections, base_change (Prop)
    decls.push(ctx.to_axiom("Topology.Scheme.scheme_gluing", ctx.prop.clone()));
    decls.push(ctx.to_axiom(
        "Topology.Scheme.spec_adjoint_global_sections",
        ctx.prop.clone(),
    ));
    decls.push(ctx.to_axiom("Topology.Scheme.base_change", ctx.prop.clone()));

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
