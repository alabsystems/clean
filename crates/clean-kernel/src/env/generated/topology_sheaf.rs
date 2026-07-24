// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.Sheaf namespace (#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Sheaf";
pub(crate) const DECL_COUNT: usize = 40;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Sheaf.Presheaf",
    "Topology.Sheaf.sections",
    "Topology.Sheaf.restriction",
    "Topology.Sheaf.Sheaf",
    "Topology.Sheaf.to_presheaf",
    "Topology.Sheaf.gluing",
    "Topology.Sheaf.locality",
    "Topology.Sheaf.Stalk",
    "Topology.Sheaf.germ",
    "Topology.Sheaf.sheafify",
    "Topology.Sheaf.sheafify_unit",
    "Topology.Sheaf.sheafify_universal",
    "Topology.Sheaf.GlobalSections",
    "Topology.Sheaf.constant_sheaf",
    "Topology.Sheaf.skyscraper",
    "Topology.Sheaf.direct_image",
    "Topology.Sheaf.inverse_image",
    "Topology.Sheaf.adjunction",
    "Topology.Sheaf.SheafHom",
    "Topology.Sheaf.kernel",
    "Topology.Sheaf.cokernel",
    "Topology.Sheaf.image",
    "Topology.Sheaf.exact_sequence",
    "Topology.Sheaf.SheafCohomology",
    "Topology.Sheaf.h0_global_sections",
    "Topology.Sheaf.long_exact_sequence",
    "Topology.Sheaf.CechCohomology",
    "Topology.Sheaf.cech_sheaf_comparison",
    "Topology.Sheaf.flasque",
    "Topology.Sheaf.flasque_acyclic",
    "Topology.Sheaf.soft",
    "Topology.Sheaf.fine",
    "Topology.Sheaf.fine_soft",
    "Topology.Sheaf.soft_acyclic",
    "Topology.Sheaf.RingedSpace",
    "Topology.Sheaf.structure_sheaf",
    "Topology.Sheaf.LocallyRingedSpace",
    "Topology.Sheaf.stalk_local",
    "Topology.Sheaf.locally_free",
    "Topology.Sheaf.rank",
];

struct SheafCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl SheafCtx {
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

    fn nat_const(&self) -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }

    fn presheaf_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Sheaf.Presheaf"),
            vec![self.u_level.clone()],
        )
    }

    fn sheaf_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Sheaf.Sheaf"),
            vec![self.u_level.clone()],
        )
    }

    fn ringed_space_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Sheaf.RingedSpace"),
            vec![self.u_level.clone()],
        )
    }

    fn locally_ringed_space_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Sheaf.LocallyRingedSpace"),
            vec![self.u_level.clone()],
        )
    }

    fn presheaf_app(&self, x: Expr, c: Expr) -> Expr {
        Expr::app(Expr::app(self.presheaf_const(), x), c)
    }

    fn sheaf_app(&self, x: Expr, c: Expr) -> Expr {
        Expr::app(Expr::app(self.sheaf_const(), x), c)
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

    // Presheaf : Type u → Type u → Type u
    fn build_presheaf_type(&self) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.type_u.clone(),
            Expr::pi(
                BinderInfo::Default,
                self.type_u.clone(),
                self.type_u.clone(),
            ),
        )
    }

    // sections : {X : Type u} → {C : Type u} → Presheaf X C → Type u → Type u
    fn build_sections_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let pf = self.presheaf_app(x, c);
        let (pf_id, _) = b.fresh_local(pf.clone());
        let (open_id, _) = b.fresh_local(self.type_u.clone());
        let r = b.mk_pi(
            open_id,
            BinderInfo::Default,
            self.type_u.clone(),
            self.type_u.clone(),
        );
        let r = b.mk_pi(pf_id, BinderInfo::Default, pf, r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // restriction : {X} → {C} → {F : Presheaf X C} → {U} → {V} → (V ⊆ U) → Type u
    fn build_restriction_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let pf = self.presheaf_app(x, c);
        let (pf_id, _) = b.fresh_local(pf.clone());
        let (u_var_id, _) = b.fresh_local(self.type_u.clone());
        let (v_var_id, _) = b.fresh_local(self.type_u.clone());
        let (sub_id, _) = b.fresh_local(self.prop.clone());
        let r = b.mk_pi(
            sub_id,
            BinderInfo::Default,
            self.prop.clone(),
            self.type_u.clone(),
        );
        let r = b.mk_pi(v_var_id, BinderInfo::Implicit, self.type_u.clone(), r);
        let r = b.mk_pi(u_var_id, BinderInfo::Implicit, self.type_u.clone(), r);
        let r = b.mk_pi(pf_id, BinderInfo::Implicit, pf, r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // Sheaf : Type u → Type u → Type u
    fn build_sheaf_type(&self) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.type_u.clone(),
            Expr::pi(
                BinderInfo::Default,
                self.type_u.clone(),
                self.type_u.clone(),
            ),
        )
    }

    // {X} → {C} → Sheaf X C → <ret> (pattern for to_presheaf, GlobalSections, etc.)
    fn build_sheaf_to_ret(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let sh = self.sheaf_app(x, c);
        let (sh_id, _) = b.fresh_local(sh.clone());
        let r = b.mk_pi(sh_id, BinderInfo::Default, sh, ret);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // {X} → {C} → Sheaf X C → Prop (gluing, locality, flasque, soft, fine, locally_free)
    fn build_sheaf_predicate_type(&self) -> Expr {
        self.build_sheaf_to_ret(self.prop.clone())
    }

    // Stalk : {X} → {C} → Sheaf X C → X → C (= Type u)
    fn build_stalk_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let sh = self.sheaf_app(x.clone(), c);
        let (sh_id, _) = b.fresh_local(sh.clone());
        let (pt_id, _) = b.fresh_local(x.clone());
        let r = b.mk_pi(pt_id, BinderInfo::Default, x, self.type_u.clone());
        let r = b.mk_pi(sh_id, BinderInfo::Default, sh, r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // germ : {X} → {C} → {F : Sheaf X C} → {U} → sections F U → {x : X} → (x ∈ U) → Type u
    fn build_germ_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let sh = self.sheaf_app(x.clone(), c);
        let (sh_id, _) = b.fresh_local(sh.clone());
        let (u_var_id, _) = b.fresh_local(self.type_u.clone());
        let (s_id, _) = b.fresh_local(self.type_u.clone());
        let (pt_id, _) = b.fresh_local(x.clone());
        let (mem_id, _) = b.fresh_local(self.prop.clone());
        let r = b.mk_pi(
            mem_id,
            BinderInfo::Default,
            self.prop.clone(),
            self.type_u.clone(),
        );
        let r = b.mk_pi(pt_id, BinderInfo::Implicit, x, r);
        let r = b.mk_pi(s_id, BinderInfo::Default, self.type_u.clone(), r);
        let r = b.mk_pi(u_var_id, BinderInfo::Implicit, self.type_u.clone(), r);
        let r = b.mk_pi(sh_id, BinderInfo::Implicit, sh, r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // sheafify / sheafify_unit / sheafify_universal : {X} → {C} → Presheaf X C → <ret>
    fn build_presheaf_to_ret(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let pf = self.presheaf_app(x.clone(), c.clone());
        let (pf_id, _) = b.fresh_local(pf.clone());
        let r = b.mk_pi(pf_id, BinderInfo::Default, pf, ret);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // sheafify : {X} → {C} → Presheaf X C → Sheaf X C
    fn build_sheafify_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let pf = self.presheaf_app(x.clone(), c.clone());
        let sh = self.sheaf_app(x, c);
        let (pf_id, _) = b.fresh_local(pf.clone());
        let r = b.mk_pi(pf_id, BinderInfo::Default, pf, sh);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // constant_sheaf : {X} → {C} → C → Sheaf X C
    fn build_constant_sheaf_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let sh = self.sheaf_app(x, c.clone());
        let (val_id, _) = b.fresh_local(c.clone());
        let r = b.mk_pi(val_id, BinderInfo::Default, c, sh);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // skyscraper : {X} → {C} → C → X → Sheaf X C
    fn build_skyscraper_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let sh = self.sheaf_app(x.clone(), c.clone());
        let (val_id, _) = b.fresh_local(c.clone());
        let (pt_id, _) = b.fresh_local(x.clone());
        let r = b.mk_pi(pt_id, BinderInfo::Default, x, sh);
        let r = b.mk_pi(val_id, BinderInfo::Default, c, r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // direct_image : {X} → {Y} → {C} → Prop → Sheaf X C → Sheaf Y C
    fn build_direct_image_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (y_id, y) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let sh_x = self.sheaf_app(x, c.clone());
        let sh_y = self.sheaf_app(y, c);
        let (f_id, _) = b.fresh_local(self.prop.clone());
        let (sx_id, _) = b.fresh_local(sh_x.clone());
        let r = b.mk_pi(sx_id, BinderInfo::Default, sh_x, sh_y);
        let r = b.mk_pi(f_id, BinderInfo::Default, self.prop.clone(), r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        let r = b.mk_pi(y_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // inverse_image : {X} → {Y} → {C} → Prop → Sheaf Y C → Sheaf X C
    fn build_inverse_image_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (y_id, y) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let sh_y = self.sheaf_app(y, c.clone());
        let sh_x = self.sheaf_app(x, c);
        let (f_id, _) = b.fresh_local(self.prop.clone());
        let (sy_id, _) = b.fresh_local(sh_y.clone());
        let r = b.mk_pi(sy_id, BinderInfo::Default, sh_y, sh_x);
        let r = b.mk_pi(f_id, BinderInfo::Default, self.prop.clone(), r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        let r = b.mk_pi(y_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // SheafHom : {X} → {C} → Sheaf X C → Sheaf X C → Type u
    fn build_sheaf_hom_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let sh = self.sheaf_app(x, c);
        let (f_id, _) = b.fresh_local(sh.clone());
        let (g_id, _) = b.fresh_local(sh.clone());
        let r = b.mk_pi(g_id, BinderInfo::Default, sh.clone(), self.type_u.clone());
        let r = b.mk_pi(f_id, BinderInfo::Default, sh, r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // kernel/cokernel/image : {X} → {C} → {F : Sheaf} → {G : Sheaf} → morphism → Sheaf X C
    fn build_sheaf_morphism_to_sheaf_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let sh = self.sheaf_app(x, c);
        let (f_id, _) = b.fresh_local(sh.clone());
        let (g_id, _) = b.fresh_local(sh.clone());
        let (morph_id, _) = b.fresh_local(self.type_u.clone());
        let r = b.mk_pi(
            morph_id,
            BinderInfo::Default,
            self.type_u.clone(),
            sh.clone(),
        );
        let r = b.mk_pi(g_id, BinderInfo::Implicit, sh.clone(), r);
        let r = b.mk_pi(f_id, BinderInfo::Implicit, sh, r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // SheafCohomology : {X} → {C} → Sheaf X C → Nat → Type u
    fn build_cohomology_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let sh = self.sheaf_app(x, c);
        let (sh_id, _) = b.fresh_local(sh.clone());
        let (n_id, _) = b.fresh_local(self.nat_const());
        let r = b.mk_pi(
            n_id,
            BinderInfo::Default,
            self.nat_const(),
            self.type_u.clone(),
        );
        let r = b.mk_pi(sh_id, BinderInfo::Default, sh, r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // CechCohomology : {X} → {C} → Sheaf X C → Type u (cover) → Nat → Type u
    fn build_cech_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let sh = self.sheaf_app(x, c);
        let (sh_id, _) = b.fresh_local(sh.clone());
        let (cover_id, _) = b.fresh_local(self.type_u.clone());
        let (n_id, _) = b.fresh_local(self.nat_const());
        let r = b.mk_pi(
            n_id,
            BinderInfo::Default,
            self.nat_const(),
            self.type_u.clone(),
        );
        let r = b.mk_pi(cover_id, BinderInfo::Default, self.type_u.clone(), r);
        let r = b.mk_pi(sh_id, BinderInfo::Default, sh, r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // structure_sheaf : RingedSpace → Type u
    fn build_structure_sheaf_type(&self) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.ringed_space_const(),
            self.type_u.clone(),
        )
    }

    // stalk_local : LocallyRingedSpace → Prop
    fn build_stalk_local_type(&self) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.locally_ringed_space_const(),
            self.prop.clone(),
        )
    }

    // rank : {X} → {C} → {F : Sheaf X C} → (locally_free F) → Nat
    fn build_rank_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (c_id, c) = b.fresh_local(self.type_u.clone());
        let sh = self.sheaf_app(x, c);
        let (sh_id, _) = b.fresh_local(sh.clone());
        let (lf_id, _) = b.fresh_local(self.prop.clone());
        let r = b.mk_pi(
            lf_id,
            BinderInfo::Default,
            self.prop.clone(),
            self.nat_const(),
        );
        let r = b.mk_pi(sh_id, BinderInfo::Implicit, sh, r);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    // GlobalSections : {X} → {C} → Sheaf X C → Type u
    fn build_global_sections_type(&self) -> Expr {
        self.build_sheaf_to_ret(self.type_u.clone())
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = SheafCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    // 1. Presheaf : Type u → Type u → Type u
    decls.push(ctx.to_axiom("Topology.Sheaf.Presheaf", ctx.build_presheaf_type()));

    // 2. sections
    decls.push(ctx.to_axiom("Topology.Sheaf.sections", ctx.build_sections_type()));

    // 3. restriction
    decls.push(ctx.to_axiom("Topology.Sheaf.restriction", ctx.build_restriction_type()));

    // 4. Sheaf : Type u → Type u → Type u
    decls.push(ctx.to_axiom("Topology.Sheaf.Sheaf", ctx.build_sheaf_type()));

    // 5. to_presheaf : {X} → {C} → Sheaf X C → Presheaf X C
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(ctx.type_u.clone());
        let (c_id, c) = b.fresh_local(ctx.type_u.clone());
        let sh = ctx.sheaf_app(x.clone(), c.clone());
        let pf = ctx.presheaf_app(x, c);
        let (sh_id, _) = b.fresh_local(sh.clone());
        let r = b.mk_pi(sh_id, BinderInfo::Default, sh, pf);
        let r = b.mk_pi(c_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
        let ty = b.finish(b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r));
        decls.push(ctx.to_axiom("Topology.Sheaf.to_presheaf", ty));
    }

    // 6. gluing, 7. locality (sheaf predicates)
    let sheaf_pred = ctx.build_sheaf_predicate_type();
    decls.push(ctx.to_axiom("Topology.Sheaf.gluing", sheaf_pred.clone()));
    decls.push(ctx.to_axiom("Topology.Sheaf.locality", sheaf_pred.clone()));

    // 8. Stalk
    decls.push(ctx.to_axiom("Topology.Sheaf.Stalk", ctx.build_stalk_type()));

    // 9. germ
    decls.push(ctx.to_axiom("Topology.Sheaf.germ", ctx.build_germ_type()));

    // 10. sheafify
    decls.push(ctx.to_axiom("Topology.Sheaf.sheafify", ctx.build_sheafify_type()));

    // 11. sheafify_unit, 12. sheafify_universal (Presheaf → Prop)
    let presheaf_prop = ctx.build_presheaf_to_ret(ctx.prop.clone());
    decls.push(ctx.to_axiom("Topology.Sheaf.sheafify_unit", presheaf_prop.clone()));
    decls.push(ctx.to_axiom("Topology.Sheaf.sheafify_universal", presheaf_prop));

    // 13. GlobalSections
    decls.push(ctx.to_axiom(
        "Topology.Sheaf.GlobalSections",
        ctx.build_global_sections_type(),
    ));

    // 14. constant_sheaf
    decls.push(ctx.to_axiom(
        "Topology.Sheaf.constant_sheaf",
        ctx.build_constant_sheaf_type(),
    ));

    // 15. skyscraper
    decls.push(ctx.to_axiom("Topology.Sheaf.skyscraper", ctx.build_skyscraper_type()));

    // 16. direct_image
    decls.push(ctx.to_axiom("Topology.Sheaf.direct_image", ctx.build_direct_image_type()));

    // 17. inverse_image
    decls.push(ctx.to_axiom(
        "Topology.Sheaf.inverse_image",
        ctx.build_inverse_image_type(),
    ));

    // 18. adjunction (Prop)
    decls.push(ctx.to_axiom("Topology.Sheaf.adjunction", ctx.prop.clone()));

    // 19. SheafHom
    decls.push(ctx.to_axiom("Topology.Sheaf.SheafHom", ctx.build_sheaf_hom_type()));

    // 20-22. kernel, cokernel, image
    let morph_to_sheaf = ctx.build_sheaf_morphism_to_sheaf_type();
    decls.push(ctx.to_axiom("Topology.Sheaf.kernel", morph_to_sheaf.clone()));
    decls.push(ctx.to_axiom("Topology.Sheaf.cokernel", morph_to_sheaf.clone()));
    decls.push(ctx.to_axiom("Topology.Sheaf.image", morph_to_sheaf));

    // 23. exact_sequence (Prop)
    decls.push(ctx.to_axiom("Topology.Sheaf.exact_sequence", ctx.prop.clone()));

    // 24. SheafCohomology
    decls.push(ctx.to_axiom(
        "Topology.Sheaf.SheafCohomology",
        ctx.build_cohomology_type(),
    ));

    // 25. h0_global_sections, 26. long_exact_sequence (Prop)
    decls.push(ctx.to_axiom("Topology.Sheaf.h0_global_sections", ctx.prop.clone()));
    decls.push(ctx.to_axiom("Topology.Sheaf.long_exact_sequence", ctx.prop.clone()));

    // 27. CechCohomology
    decls.push(ctx.to_axiom("Topology.Sheaf.CechCohomology", ctx.build_cech_type()));

    // 28. cech_sheaf_comparison (Prop)
    decls.push(ctx.to_axiom("Topology.Sheaf.cech_sheaf_comparison", ctx.prop.clone()));

    // 29. flasque, 30. flasque_acyclic
    decls.push(ctx.to_axiom("Topology.Sheaf.flasque", sheaf_pred.clone()));
    decls.push(ctx.to_axiom("Topology.Sheaf.flasque_acyclic", ctx.prop.clone()));

    // 31. soft, 32. fine (sheaf predicates)
    decls.push(ctx.to_axiom("Topology.Sheaf.soft", sheaf_pred.clone()));
    decls.push(ctx.to_axiom("Topology.Sheaf.fine", sheaf_pred));

    // 33. fine_soft, 34. soft_acyclic (Prop)
    decls.push(ctx.to_axiom("Topology.Sheaf.fine_soft", ctx.prop.clone()));
    decls.push(ctx.to_axiom("Topology.Sheaf.soft_acyclic", ctx.prop.clone()));

    // 35. RingedSpace : Type u
    decls.push(ctx.to_axiom("Topology.Sheaf.RingedSpace", ctx.type_u.clone()));

    // 36. structure_sheaf : RingedSpace → Type u
    decls.push(ctx.to_axiom(
        "Topology.Sheaf.structure_sheaf",
        ctx.build_structure_sheaf_type(),
    ));

    // 37. LocallyRingedSpace : Type u
    decls.push(ctx.to_axiom("Topology.Sheaf.LocallyRingedSpace", ctx.type_u.clone()));

    // 38. stalk_local : LocallyRingedSpace → Prop
    decls.push(ctx.to_axiom("Topology.Sheaf.stalk_local", ctx.build_stalk_local_type()));

    // 39. locally_free (sheaf predicate)
    decls.push(ctx.to_axiom(
        "Topology.Sheaf.locally_free",
        ctx.build_sheaf_to_ret(ctx.prop.clone()),
    ));

    // 40. rank
    decls.push(ctx.to_axiom("Topology.Sheaf.rank", ctx.build_rank_type()));

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
