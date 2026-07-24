// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WF recursion combinators: InvImage, invImage, measure, sizeOfWFRel, Nat.lt_wfRel.
//!
//! Split from `wf_recursion_support` for file-size compliance.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::wf_recursion_support::mk_rel_type;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Define `InvImage` and the `InvImage.wf` axiom.
    ///
    /// ```text
    /// def InvImage {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β)
    ///   : α → α → Prop := fun a₁ a₂ => r (f a₁) (f a₂)
    /// axiom InvImage.wf : ... → WellFounded r → WellFounded (InvImage r f)
    /// ```
    pub(super) fn init_inv_image(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let sort_v = Expr::from_kind(ExprKind::Sort(v_level.clone()));

        let inv_image_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let r_type = mk_rel_type(&b, &beta);
            let (r_id, _) = b.fresh_local(r_type.clone());
            let f_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, _) = s.fresh_local(alpha.clone());
                let t = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), beta.clone());
                s.finish_child(t)
            };
            let (f_id, _) = b.fresh_local(f_type.clone());
            let result_type = mk_rel_type(&b, &alpha);
            let t = b.mk_pi(f_id, BinderInfo::Default, f_type, result_type);
            let t = b.mk_pi(r_id, BinderInfo::Default, r_type, t);
            let t = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), t);
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        let inv_image_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let r_type = mk_rel_type(&b, &beta);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let f_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, _) = s.fresh_local(alpha.clone());
                let t = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), beta.clone());
                s.finish_child(t)
            };
            let (f_id, f) = b.fresh_local(f_type.clone());
            let (a1_id, a1) = b.fresh_local(alpha.clone());
            let (a2_id, a2) = b.fresh_local(alpha.clone());
            let body = Expr::app(
                Expr::app(r.clone(), Expr::app(f.clone(), a1)),
                Expr::app(f, a2),
            );
            let t = b.mk_lam(a2_id, BinderInfo::Default, alpha.clone(), body);
            let t = b.mk_lam(a1_id, BinderInfo::Default, alpha, t);
            let t = b.mk_lam(f_id, BinderInfo::Default, f_type, t);
            let t = b.mk_lam(r_id, BinderInfo::Default, r_type, t);
            let t = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), t);
            let t = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("InvImage"),
            level_params: vec![u.clone(), v.clone()],
            type_: inv_image_type,
            value: inv_image_value,
            is_reducible: true,
        })?;

        // InvImage.wf axiom
        self.init_inv_image_wf(&u, &v, &u_level, &v_level, &sort_u, &sort_v)
    }

    /// `InvImage.wf` axiom: transporting well-foundedness across a function.
    fn init_inv_image_wf(
        &mut self,
        u: &Name,
        v: &Name,
        u_level: &Level,
        v_level: &Level,
        sort_u: &Expr,
        sort_v: &Expr,
    ) -> Result<(), EnvError> {
        let wf_beta_const = Expr::const_(Name::from_string("WellFounded"), vec![v_level.clone()]);
        let inv_image_const = Expr::const_(
            Name::from_string("InvImage"),
            vec![u_level.clone(), v_level.clone()],
        );

        let inv_image_wf_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let r_type = mk_rel_type(&b, &beta);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let f_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, _) = s.fresh_local(alpha.clone());
                let t = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), beta.clone());
                s.finish_child(t)
            };
            let (f_id, f) = b.fresh_local(f_type.clone());
            let wf_r = Expr::app(Expr::app(wf_beta_const, beta.clone()), r.clone());
            let (hwf_id, _) = b.fresh_local(wf_r.clone());
            let inv_r_f = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(inv_image_const, alpha.clone()), beta),
                    r,
                ),
                f,
            );
            let wf_u_const = Expr::const_(Name::from_string("WellFounded"), vec![u_level.clone()]);
            let result_type = Expr::app(Expr::app(wf_u_const, alpha), inv_r_f);
            let t = b.mk_pi(hwf_id, BinderInfo::Default, wf_r, result_type);
            let t = b.mk_pi(f_id, BinderInfo::Default, f_type, t);
            let t = b.mk_pi(r_id, BinderInfo::Implicit, r_type, t);
            let t = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), t);
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("InvImage.wf"),
            level_params: vec![u.clone(), v.clone()],
            type_: inv_image_wf_type,
        })
    }

    /// Define `Nat.lt_wfRel : WellFoundedRelation Nat` (axiom-backed).
    pub(super) fn init_nat_lt_wfrel(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_lt_const = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let wf_nat_const = Expr::const_(
            Name::from_string("WellFounded"),
            vec![Level::succ(Level::zero())],
        );
        let nat_lt_wf_name = Name::from_string("Nat.lt_wfRel.proof");

        let nat_lt_wf_type = Expr::app(Expr::app(wf_nat_const, nat.clone()), nat_lt_const.clone());
        self.add_decl(Declaration::Axiom {
            name: nat_lt_wf_name.clone(),
            level_params: vec![],
            type_: nat_lt_wf_type,
        })?;

        let wfr_nat = Expr::const_(
            Name::from_string("WellFoundedRelation"),
            vec![Level::succ(Level::zero())],
        );
        let wfr_mk = Expr::const_(
            Name::from_string("WellFoundedRelation.mk"),
            vec![Level::succ(Level::zero())],
        );
        let value = Expr::app(
            Expr::app(Expr::app(wfr_mk, nat.clone()), nat_lt_const),
            Expr::const_(nat_lt_wf_name, vec![]),
        );
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Nat.lt_wfRel"),
            level_params: vec![],
            type_: Expr::app(wfr_nat, nat),
            value,
            is_reducible: true,
        })
    }

    /// Define the `invImage` combinator.
    pub(super) fn init_inv_image_combinator(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let sort_v = Expr::from_kind(ExprKind::Sort(v_level.clone()));
        let wfr_name = Name::from_string("WellFoundedRelation");
        let wfr_u = Expr::const_(wfr_name.clone(), vec![u_level.clone()]);
        let inv_image_const = Expr::const_(
            Name::from_string("InvImage"),
            vec![u_level.clone(), v_level.clone()],
        );

        let inv_image_fn_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let f_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, _) = s.fresh_local(alpha.clone());
                let t = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), beta.clone());
                s.finish_child(t)
            };
            let (f_id, _) = b.fresh_local(f_type.clone());
            let wfr_beta = Expr::app(Expr::const_(wfr_name.clone(), vec![v_level.clone()]), beta);
            let (h_id, _) = b.fresh_local(wfr_beta.clone());
            let result = Expr::app(wfr_u.clone(), alpha);
            let t = b.mk_pi(h_id, BinderInfo::Default, wfr_beta, result);
            let t = b.mk_pi(f_id, BinderInfo::Default, f_type, t);
            let t = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), t);
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        let inv_image_fn_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let f_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, _) = s.fresh_local(alpha.clone());
                let t = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), beta.clone());
                s.finish_child(t)
            };
            let (f_id, f) = b.fresh_local(f_type.clone());
            let wfr_beta = Expr::app(
                Expr::const_(wfr_name.clone(), vec![v_level.clone()]),
                beta.clone(),
            );
            let (h_id, h) = b.fresh_local(wfr_beta.clone());
            let h_rel = Expr::proj(wfr_name.clone(), 0, h.clone());
            let h_wf = Expr::proj(wfr_name.clone(), 1, h);

            let inv_img = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(inv_image_const, alpha.clone()), beta.clone()),
                    h_rel.clone(),
                ),
                f.clone(),
            );
            let inv_wf_const = Expr::const_(
                Name::from_string("InvImage.wf"),
                vec![u_level.clone(), v_level],
            );
            let inv_wf = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(inv_wf_const, alpha.clone()), beta),
                        h_rel,
                    ),
                    f,
                ),
                h_wf,
            );
            let wfr_mk = Expr::const_(
                Name::from_string("WellFoundedRelation.mk"),
                vec![u_level.clone()],
            );
            let body = Expr::app(Expr::app(Expr::app(wfr_mk, alpha.clone()), inv_img), inv_wf);
            let t = b.mk_lam(h_id, BinderInfo::Default, wfr_beta, body);
            let t = b.mk_lam(f_id, BinderInfo::Default, f_type, t);
            let t = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v, t);
            let t = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u, t);
            b.finish(t)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("invImage"),
            level_params: vec![u, v],
            type_: inv_image_fn_type,
            value: inv_image_fn_value,
            is_reducible: true,
        })
    }

    /// Define `measure {α : Sort u} (f : α → Nat) : WellFoundedRelation α`.
    pub(super) fn init_measure(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let wfr_u = Expr::const_(
            Name::from_string("WellFoundedRelation"),
            vec![u_level.clone()],
        );

        let measure_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let f_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, _) = s.fresh_local(alpha.clone());
                let t = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), nat.clone());
                s.finish_child(t)
            };
            let (f_id, _) = b.fresh_local(f_type.clone());
            let result = Expr::app(wfr_u, alpha);
            let t = b.mk_pi(f_id, BinderInfo::Default, f_type, result);
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        let measure_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let f_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, _) = s.fresh_local(alpha.clone());
                let t = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), nat.clone());
                s.finish_child(t)
            };
            let (f_id, f) = b.fresh_local(f_type.clone());
            let inv_image_fn = Expr::const_(
                Name::from_string("invImage"),
                vec![u_level, Level::succ(Level::zero())],
            );
            let nat_lt_wfrel = Expr::const_(Name::from_string("Nat.lt_wfRel"), vec![]);
            let body = Expr::app(
                Expr::app(Expr::app(Expr::app(inv_image_fn, alpha.clone()), nat), f),
                nat_lt_wfrel,
            );
            let t = b.mk_lam(f_id, BinderInfo::Default, f_type, body);
            let t = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u, t);
            b.finish(t)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("measure"),
            level_params: vec![u],
            type_: measure_type,
            value: measure_value,
            is_reducible: true,
        })
    }

    /// Define `sizeOfWFRel {α : Sort u} [SizeOf α] : WellFoundedRelation α`.
    pub(super) fn init_sizeof_wfrel(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let sizeof_const = Expr::const_(Name::from_string("SizeOf"), vec![u_level.clone()]);
        let wfr_u = Expr::const_(
            Name::from_string("WellFoundedRelation"),
            vec![u_level.clone()],
        );

        let sizeof_wfrel_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let sizeof_alpha = Expr::app(sizeof_const.clone(), alpha.clone());
            let (inst_id, _) = b.fresh_local(sizeof_alpha.clone());
            let result = Expr::app(wfr_u, alpha);
            let t = b.mk_pi(inst_id, BinderInfo::InstImplicit, sizeof_alpha, result);
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        let sizeof_wfrel_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let sizeof_alpha = Expr::app(sizeof_const, alpha.clone());
            let (inst_id, inst) = b.fresh_local(sizeof_alpha.clone());
            let sizeof_fn = Expr::proj(Name::from_string("SizeOf"), 0, inst);
            let measure_const = Expr::const_(Name::from_string("measure"), vec![u_level]);
            let body = Expr::app(Expr::app(measure_const, alpha), sizeof_fn);
            let t = b.mk_lam(inst_id, BinderInfo::InstImplicit, sizeof_alpha, body);
            let t = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u, t);
            b.finish(t)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("sizeOfWFRel"),
            level_params: vec![u],
            type_: sizeof_wfrel_type,
            value: sizeof_wfrel_value,
            is_reducible: true,
        })
    }
}
