// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Well-founded recursion support types for the equation compiler.
//!
//! Defines the typeclasses and combinators that Lean 4's equation compiler
//! uses when compiling functions with `termination_by` annotations:
//!
//! - `WellFoundedRelation` — typeclass bundling a relation with its WF proof
//! - `SizeOf` — typeclass for computing structural sizes (termination measures)
//! - `InvImage` — transporting well-foundedness across functions
//! - `invImage`, `measure`, `sizeOfWFRel` — convenience combinators
//! - `Nat.lt_wfRel` — the canonical WF relation on Nat
//! - `Acc.inv` — extract sub-accessibility from an Acc proof (Part 2)
//! - `WellFounded.fixFEq` — the unfolding equation for fixF (Part 2)
//! - `WellFounded.recursion` — alias for WellFounded.fix (Part 2)
//!
//! Reference: Lean 4 `Init/WF.lean` and `Init/SizeOf.lean`.

mod combinators;
mod fix_support;

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Build a binary relation type `α → α → Prop` as a child of a builder.
#[cfg(test)]
pub(super) fn mk_rel_type(b: &EnvDeclBuilder, alpha: &Expr) -> Expr {
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let mut s = EnvDeclBuilder::child_of(b);
    let (x_id, _) = s.fresh_local(alpha.clone());
    let (y_id, _) = s.fresh_local(alpha.clone());
    let t = prop;
    let t = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), t);
    let t = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), t);
    s.finish_child(t)
}

#[cfg(test)]
impl Environment {
    /// Initialize well-founded recursion support types.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.wf_recursion_support_init == true`
    /// ENSURES: Idempotent
    #[cfg(test)]
    pub(crate) fn init_wf_recursion_support(&mut self) -> Result<(), EnvError> {
        if self.wf_recursion_support_init {
            return Ok(());
        }
        self.init_well_founded()?;
        self.init_nat()?;
        self.init_lt()?;

        self.init_well_founded_relation()?;
        self.init_sizeof()?;
        self.init_inv_image()?;
        self.init_nat_lt_wfrel()?;
        self.init_inv_image_combinator()?;
        self.init_measure()?;
        self.init_sizeof_wfrel()?;

        // Part 2: Equation compiler support
        self.init_acc_inv()?;
        self.init_eq()?; // Needed for fixFEq's Eq type
        self.init_fix_f_eq()?;
        self.init_wf_recursion()?;

        self.wf_recursion_support_init = true;
        Ok(())
    }

    /// Check if WF recursion support has been initialized.
    #[cfg(test)]
    pub(crate) fn has_wf_recursion_support(&self) -> bool {
        self.wf_recursion_support_init
    }

    /// Define the `WellFoundedRelation` typeclass inductive and projections.
    ///
    /// ```text
    /// class WellFoundedRelation (α : Sort u) : Sort (max 1 u) where
    ///   rel : α → α → Prop
    ///   wf  : WellFounded rel
    /// ```
    /// Define the `WellFoundedRelation` inductive type.
    #[cfg(test)]
    fn init_well_founded_relation(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let wf_const = Expr::const_(Name::from_string("WellFounded"), vec![u_level.clone()]);
        let wfr_name = Name::from_string("WellFoundedRelation");
        let wfr_const = Expr::const_(wfr_name.clone(), vec![u_level.clone()]);
        // Sort (max 1 u) — field `rel : α → α → Prop` has sort `max(u, 1)`.
        let max_1_u = Level::max(Level::succ(Level::zero()), u_level);

        let wfr_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(sort_u.clone());
            let t = Expr::from_kind(ExprKind::Sort(max_1_u));
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };
        let wfr_ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let rel_type = mk_rel_type(&b, &alpha);
            let (rel_id, rel) = b.fresh_local(rel_type.clone());
            let wf_rel = Expr::app(Expr::app(wf_const, alpha.clone()), rel);
            let (wf_id, _) = b.fresh_local(wf_rel.clone());
            let result = Expr::app(wfr_const, alpha);
            let t = b.mk_pi(wf_id, BinderInfo::Default, wf_rel, result);
            let t = b.mk_pi(rel_id, BinderInfo::Default, rel_type, t);
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u, t);
            b.finish(t)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: wfr_name.clone(),
                type_: wfr_type,
                constructors: vec![Constructor {
                    name: Name::from_string("WellFoundedRelation.mk"),
                    type_: wfr_ctor_type,
                }],
            }],
        })?;
        self.register_structure_fields(
            wfr_name,
            vec![Name::from_string("rel"), Name::from_string("wf")],
        )?;
        self.init_wfr_projections(&u)
    }

    /// `WellFoundedRelation.rel` and `.wf` projection definitions.
    #[cfg(test)]
    fn init_wfr_projections(&mut self, u: &Name) -> Result<(), EnvError> {
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let wf_const = Expr::const_(Name::from_string("WellFounded"), vec![u_level]);
        let wfr_name = Name::from_string("WellFoundedRelation");
        let wfr_const = Expr::const_(wfr_name.clone(), vec![Level::param(u.clone())]);

        // .rel projection
        let (rel_ty, rel_val) = {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (aid, a) = b.fresh_local(sort_u.clone());
                let wa = Expr::app(wfr_const.clone(), a.clone());
                let (iid, _) = b.fresh_local(wa.clone());
                let rt = mk_rel_type(&b, &a);
                let t = b.mk_pi(iid, BinderInfo::InstImplicit, wa, rt);
                let t = b.mk_pi(aid, BinderInfo::Implicit, sort_u.clone(), t);
                b.finish(t)
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (aid, a) = b.fresh_local(sort_u.clone());
                let wa = Expr::app(wfr_const.clone(), a);
                let (iid, i) = b.fresh_local(wa.clone());
                let body = Expr::proj(wfr_name.clone(), 0, i);
                let t = b.mk_lam(iid, BinderInfo::InstImplicit, wa, body);
                let t = b.mk_lam(aid, BinderInfo::Implicit, sort_u.clone(), t);
                b.finish(t)
            };
            (ty, val)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("WellFoundedRelation.rel"),
            level_params: vec![u.clone()],
            type_: rel_ty,
            value: rel_val,
            is_reducible: true,
        })?;

        // .wf projection
        let (wf_ty, wf_val) = {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (aid, a) = b.fresh_local(sort_u.clone());
                let wa = Expr::app(wfr_const.clone(), a.clone());
                let (iid, i) = b.fresh_local(wa.clone());
                let rp = Expr::proj(wfr_name.clone(), 0, i);
                let wt = Expr::app(Expr::app(wf_const, a), rp);
                let t = b.mk_pi(iid, BinderInfo::InstImplicit, wa, wt);
                let t = b.mk_pi(aid, BinderInfo::Implicit, sort_u.clone(), t);
                b.finish(t)
            };
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (aid, a) = b.fresh_local(sort_u.clone());
                let wa = Expr::app(wfr_const, a);
                let (iid, i) = b.fresh_local(wa.clone());
                let body = Expr::proj(wfr_name, 1, i);
                let t = b.mk_lam(iid, BinderInfo::InstImplicit, wa, body);
                let t = b.mk_lam(aid, BinderInfo::Implicit, sort_u, t);
                b.finish(t)
            };
            (ty, val)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("WellFoundedRelation.wf"),
            level_params: vec![u.clone()],
            type_: wf_ty,
            value: wf_val,
            is_reducible: true,
        })
    }

    /// Define the `SizeOf` inductive type.
    #[cfg(test)]
    fn init_sizeof(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let sizeof_name = Name::from_string("SizeOf");
        let sizeof_const = Expr::const_(sizeof_name.clone(), vec![u_level.clone()]);
        let max_1_u = Level::max(Level::succ(Level::zero()), u_level);

        let sizeof_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(sort_u.clone());
            let t = Expr::from_kind(ExprKind::Sort(max_1_u));
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };
        let sizeof_ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let field_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, _) = s.fresh_local(alpha.clone());
                let t = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), nat.clone());
                s.finish_child(t)
            };
            let (field_id, _) = b.fresh_local(field_type.clone());
            let result = Expr::app(sizeof_const.clone(), alpha);
            let t = b.mk_pi(field_id, BinderInfo::Default, field_type, result);
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u, t);
            b.finish(t)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: sizeof_name.clone(),
                type_: sizeof_type,
                constructors: vec![Constructor {
                    name: Name::from_string("SizeOf.mk"),
                    type_: sizeof_ctor_type,
                }],
            }],
        })?;
        self.register_structure_fields(sizeof_name, vec![Name::from_string("sizeOf")])?;
        self.init_sizeof_projection(&u, &sizeof_const, &nat)
    }

    /// `SizeOf.sizeOf` projection and the exported `sizeOf` alias.
    #[cfg(test)]
    fn init_sizeof_projection(
        &mut self,
        u: &Name,
        sizeof_const: &Expr,
        nat: &Expr,
    ) -> Result<(), EnvError> {
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let sizeof_name = Name::from_string("SizeOf");

        let proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(sort_u.clone());
            let sa = Expr::app(sizeof_const.clone(), a.clone());
            let (iid, _) = b.fresh_local(sa.clone());
            let (xid, _) = b.fresh_local(a.clone());
            let t = nat.clone();
            let t = b.mk_pi(xid, BinderInfo::Default, a, t);
            let t = b.mk_pi(iid, BinderInfo::InstImplicit, sa, t);
            let t = b.mk_pi(aid, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };
        let proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(sort_u.clone());
            let sa = Expr::app(sizeof_const.clone(), a);
            let (iid, i) = b.fresh_local(sa.clone());
            let body = Expr::proj(sizeof_name, 0, i);
            let t = b.mk_lam(iid, BinderInfo::InstImplicit, sa, body);
            let t = b.mk_lam(aid, BinderInfo::Implicit, sort_u, t);
            b.finish(t)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("SizeOf.sizeOf"),
            level_params: vec![u.clone()],
            type_: proj_type.clone(),
            value: proj_value.clone(),
            is_reducible: true,
        })?;
        self.add_decl(Declaration::Definition {
            name: Name::from_string("sizeOf"),
            level_params: vec![u.clone()],
            type_: proj_type,
            value: proj_value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests;
