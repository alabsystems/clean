// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WellFounded and Acc (accessibility) definitions for Environment
//!
//! Defines the Acc inductive type, WellFounded structure, and the
//! fixF/fix fixed-point combinators via Acc.rec.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize WellFounded relation definition
    /// WellFounded is a predicate on relations stating there are no infinite descending chains
    /// structure WellFounded {α : Sort u} (r : α → α → Prop) : Prop where
    ///   intro :: (apply : ∀ a, Acc r a)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.well_founded_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_well_founded(&mut self) -> Result<(), EnvError> {
        if self.well_founded_init {
            return Ok(());
        }

        // Dependencies: we need Acc (accessibility predicate)
        // First define Acc
        // inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
        //   | intro (x : α) (h : ∀ y, r y x → Acc r y) : Acc r x

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));

        let acc_name = Name::from_string("Acc");
        let acc_const = Expr::const_(acc_name.clone(), vec![u_level.clone()]);
        let wf_name = Name::from_string("WellFounded");
        let wf_const = Expr::const_(wf_name.clone(), vec![u_level.clone()]);
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // Helper: build r_type (α → α → Prop) as a child of a builder that has α
        let mk_r_type = |b: &EnvDeclBuilder, alpha: &Expr| -> Expr {
            let mut s = EnvDeclBuilder::child_of(b);
            let (x_id, _) = s.fresh_local(alpha.clone());
            let (y_id, _) = s.fresh_local(alpha.clone());
            let r = prop.clone();
            let r = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), r);
            let r = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
            s.finish_child(r)
        };

        // Acc {α : Sort u} (r : α → α → Prop) : α → Prop
        let acc_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let r_type = mk_r_type(&b, &alpha);
            let (r_id, _) = b.fresh_local(r_type.clone());
            let (a_id, _) = b.fresh_local(alpha.clone());
            let r = prop.clone();
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(r_id, BinderInfo::Default, r_type, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        // Acc.intro : {α} → (r) → (x : α) → (h : ∀ y, r y x → Acc r y) → Acc r x
        let acc_ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let r_type = mk_r_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            // h : ∀ y, r y x → Acc r y
            let h_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = s.fresh_local(alpha.clone());
                let r_y_x = Expr::app(Expr::app(r.clone(), y.clone()), x.clone());
                let acc_r_y = Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone());
                let acc_r_y = Expr::app(acc_r_y, y);
                // r y x → Acc r y (use nested child for the implication)
                let mut s2 = EnvDeclBuilder::child_of(&s);
                let (hyp_id, _) = s2.fresh_local(r_y_x.clone());
                let inner = s2.mk_pi(hyp_id, BinderInfo::Default, r_y_x, acc_r_y);
                let inner = s2.finish_child(inner);
                let r2 = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), inner);
                s.finish_child(r2)
            };
            let (h_id, _) = b.fresh_local(h_type.clone());
            // Result: Acc r x
            let result = Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone());
            let result = Expr::app(result, x);
            let r2 = b.mk_pi(h_id, BinderInfo::Default, h_type, result);
            let r2 = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r2);
            let r2 = b.mk_pi(r_id, BinderInfo::Default, r_type, r2);
            let r2 = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r2);
            b.finish(r2)
        };

        let acc_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: acc_name.clone(),
                type_: acc_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Acc.intro"),
                    type_: acc_ctor_type,
                }],
            }],
        };

        self.add_inductive(acc_ind)?;

        // WellFounded {α : Sort u} (r : α → α → Prop) : Prop
        // Field: apply : ∀ a, Acc r a
        let wf_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let r_type = mk_r_type(&b, &alpha);
            let (r_id, _) = b.fresh_local(r_type.clone());
            let r2 = prop.clone();
            let r2 = b.mk_pi(r_id, BinderInfo::Default, r_type, r2);
            let r2 = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r2);
            b.finish(r2)
        };

        let wf_ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let r_type = mk_r_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            // apply : ∀ a, Acc r a
            let apply_type = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = s.fresh_local(alpha.clone());
                let acc_r_a = Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone());
                let acc_r_a = Expr::app(acc_r_a, a);
                let r2 = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), acc_r_a);
                s.finish_child(r2)
            };
            let (apply_id, _) = b.fresh_local(apply_type.clone());
            // Result: WellFounded r
            let result = Expr::app(Expr::app(wf_const.clone(), alpha.clone()), r);
            let r2 = b.mk_pi(apply_id, BinderInfo::Default, apply_type, result);
            let r2 = b.mk_pi(r_id, BinderInfo::Default, r_type, r2);
            let r2 = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r2);
            b.finish(r2)
        };

        let wf_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: wf_name.clone(),
                type_: wf_type,
                constructors: vec![Constructor {
                    name: Name::from_string("WellFounded.intro"),
                    type_: wf_ctor_type,
                }],
            }],
        };

        self.add_inductive(wf_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            wf_name.clone(),
            vec![Name::from_string("apply")], // 0
        )?;

        // WellFounded.apply: {α} → (r) → [inst : WellFounded r] → ∀ a, Acc r a
        let apply_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let r_type = mk_r_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let wf_r = Expr::app(Expr::app(wf_const.clone(), alpha.clone()), r.clone());
            let (inst_id, _) = b.fresh_local(wf_r.clone());
            // ∀ a, Acc r a
            let (a_id, a) = b.fresh_local(alpha.clone());
            let acc_r_a = Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r);
            let acc_r_a = Expr::app(acc_r_a, a);
            let r2 = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), acc_r_a);
            let r2 = b.mk_pi(inst_id, BinderInfo::InstImplicit, wf_r, r2);
            let r2 = b.mk_pi(r_id, BinderInfo::Default, r_type, r2);
            let r2 = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r2);
            b.finish(r2)
        };

        let apply_proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let r_type = mk_r_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let wf_r = Expr::app(Expr::app(wf_const.clone(), alpha.clone()), r);
            let (inst_id, inst) = b.fresh_local(wf_r.clone());
            let body = Expr::proj(wf_name.clone(), 0, inst);
            let r2 = b.mk_lam(inst_id, BinderInfo::InstImplicit, wf_r, body);
            let r2 = b.mk_lam(r_id, BinderInfo::Default, r_type, r2);
            let r2 = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r2);
            b.finish(r2)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("WellFounded.apply"),
            level_params: vec![u.clone()],
            type_: apply_proj_type,
            value: apply_proj_value,
            is_reducible: true,
        })?;

        // ====================================================================
        // WellFounded.fixF — core fixed-point combinator via Acc.rec
        //
        // def WellFounded.fixF.{u, v} {α : Sort u} {r : α → α → Prop}
        //   {C : α → Sort v}
        //   (F : (x : α) → ((y : α) → r y x → C y) → C x)
        //   (x : α) (a : Acc r x) : C x :=
        //   @Acc.rec α r (fun x' _ => C x') (fun x₁ _ ih => F x₁ ih) x a
        //
        // WellFounded.fix — wrapper using WellFounded proof
        //
        // def WellFounded.fix.{u, v} {α : Sort u} {C : α → Sort v}
        //   {r : α → α → Prop}
        //   (hwf : WellFounded r)
        //   (F : (x : α) → ((y : α) → r y x → C y) → C x)
        //   (x : α) : C x :=
        //   WellFounded.fixF F x (hwf.apply x)
        // ====================================================================

        let v = Name::from_string("v");
        let v_level = Level::param(v.clone());
        let sort_v = Expr::from_kind(ExprKind::Sort(v_level.clone()));
        let acc_rec_const = Expr::const_(
            Name::from_string("Acc.rec"),
            vec![v_level.clone(), u_level.clone()],
        );
        let fix_f_name = Name::from_string("WellFounded.fixF");

        // Helper: build ∀ (y : α), r y x → target y
        // Used for h_type (target = Acc α r), ih_type (target = C), F's arg type
        let mk_forall_r_implies =
            |parent: &EnvDeclBuilder, alpha: &Expr, r: &Expr, x: &Expr, target: &Expr| -> Expr {
                let mut s = EnvDeclBuilder::child_of(parent);
                let (y_id, y) = s.fresh_local(alpha.clone());
                let r_y_x = Expr::app(Expr::app(r.clone(), y.clone()), x.clone());
                let target_y = Expr::app(target.clone(), y.clone());
                let inner = {
                    let mut s2 = EnvDeclBuilder::child_of(&s);
                    let (hyp_id, _) = s2.fresh_local(r_y_x.clone());
                    let t = s2.mk_pi(hyp_id, BinderInfo::Default, r_y_x, target_y);
                    s2.finish_child(t)
                };
                let t = s.mk_pi(y_id, BinderInfo::Default, alpha.clone(), inner);
                s.finish_child(t)
            };

        // Helper: build C type (α → Sort v) as child of builder with alpha
        let mk_c_type = |parent: &EnvDeclBuilder, alpha: &Expr| -> Expr {
            let mut s = EnvDeclBuilder::child_of(parent);
            let (a_id, _) = s.fresh_local(alpha.clone());
            let t = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), sort_v.clone());
            s.finish_child(t)
        };

        // Helper: build F type ((x : α) → ((y : α) → r y x → C y) → C x)
        let mk_step_type = |parent: &EnvDeclBuilder, alpha: &Expr, r: &Expr, c: &Expr| -> Expr {
            let mut s = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = s.fresh_local(alpha.clone());
            let rec_arg = mk_forall_r_implies(&s, alpha, r, &x, c);
            let c_x = Expr::app(c.clone(), x.clone());
            let inner = {
                let mut s2 = EnvDeclBuilder::child_of(&s);
                let (rec_id, _) = s2.fresh_local(rec_arg.clone());
                let t = s2.mk_pi(rec_id, BinderInfo::Default, rec_arg, c_x);
                s2.finish_child(t)
            };
            let t = s.mk_pi(x_id, BinderInfo::Default, alpha.clone(), inner);
            s.finish_child(t)
        };

        // --- WellFounded.fixF type ---
        // {α : Sort u} → {r : α → α → Prop} → {C : α → Sort v} →
        //   ((x : α) → ((y : α) → r y x → C y) → C x) →
        //   (x : α) → Acc r x → C x
        let fix_f_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let r_type = mk_r_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let c_type = mk_c_type(&b, &alpha);
            let (c_id, c) = b.fresh_local(c_type.clone());
            let f_type = mk_step_type(&b, &alpha, &r, &c);
            let (f_id, _) = b.fresh_local(f_type.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let acc_r_x = Expr::app(
                Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone()),
                x.clone(),
            );
            let (a_id, _) = b.fresh_local(acc_r_x.clone());
            let c_x = Expr::app(c, x);
            let t = b.mk_pi(a_id, BinderInfo::Default, acc_r_x, c_x);
            let t = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), t);
            let t = b.mk_pi(f_id, BinderInfo::Default, f_type, t);
            let t = b.mk_pi(c_id, BinderInfo::Implicit, c_type, t);
            let t = b.mk_pi(r_id, BinderInfo::Implicit, r_type, t);
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        // --- WellFounded.fixF value ---
        // fun {α} {r} {C} F x a =>
        //   @Acc.rec.{v,u} α r (fun x' _ => C x') (fun x₁ _ ih => F x₁ ih) x a
        let fix_f_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let r_type = mk_r_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let c_type = mk_c_type(&b, &alpha);
            let (c_id, c) = b.fresh_local(c_type.clone());
            let f_type = mk_step_type(&b, &alpha, &r, &c);
            let (f_id, f_var) = b.fresh_local(f_type.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let acc_alpha_r = Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone());
            let acc_r_x = Expr::app(acc_alpha_r.clone(), x.clone());
            let (a_id, a) = b.fresh_local(acc_r_x.clone());

            // motive: fun (x' : α) (_ : Acc r x') => C x'
            let motive = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x2_id, x2) = s.fresh_local(alpha.clone());
                let acc_r_x2 = Expr::app(acc_alpha_r.clone(), x2.clone());
                let (unused_id, _) = s.fresh_local(acc_r_x2.clone());
                let c_x2 = Expr::app(c.clone(), x2.clone());
                let t = s.mk_lam(unused_id, BinderInfo::Default, acc_r_x2, c_x2);
                let t = s.mk_lam(x2_id, BinderInfo::Default, alpha.clone(), t);
                s.finish_child(t)
            };

            // step: fun (x₁ : α) (_ : ∀ y, r y x₁ → Acc r y)
            //           (ih : ∀ y, r y x₁ → C y) => F x₁ ih
            let step = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x1_id, x1) = s.fresh_local(alpha.clone());
                let h_type = mk_forall_r_implies(&s, &alpha, &r, &x1, &acc_alpha_r);
                let (h_id, _) = s.fresh_local(h_type.clone());
                let ih_type = mk_forall_r_implies(&s, &alpha, &r, &x1, &c);
                let (ih_id, ih) = s.fresh_local(ih_type.clone());
                let body = Expr::app(Expr::app(f_var.clone(), x1.clone()), ih);
                let t = s.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
                let t = s.mk_lam(h_id, BinderInfo::Default, h_type, t);
                let t = s.mk_lam(x1_id, BinderInfo::Default, alpha.clone(), t);
                s.finish_child(t)
            };

            // @Acc.rec.{v,u} α r motive step x a
            let body = Expr::app(acc_rec_const.clone(), alpha.clone());
            let body = Expr::app(body, r.clone());
            let body = Expr::app(body, motive);
            let body = Expr::app(body, step);
            let body = Expr::app(body, x.clone());
            let body = Expr::app(body, a);

            let t = b.mk_lam(a_id, BinderInfo::Default, acc_r_x, body);
            let t = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), t);
            let t = b.mk_lam(f_id, BinderInfo::Default, f_type, t);
            let t = b.mk_lam(c_id, BinderInfo::Implicit, c_type, t);
            let t = b.mk_lam(r_id, BinderInfo::Implicit, r_type, t);
            let t = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): Clean seeds `WellFounded.fixF`/`fix` as REDUCIBLE
        // definitions, so import-lane whnf digs into `Acc.rec` where genuine
        // v4.31 (Init.WF) keeps them folded under its unfolding hints — the
        // `PFun.fixInduction` family then rejects on a
        // proof-irrelevance-modulo-congruence core (`Exists (Part.Dom …)` vs
        // stuck `Proj(Part, 0, Acc.rec …)`; adversarially verified NOT a
        // kernel gap). Import-suppressed so the genuine v4.31 declarations
        // import with their true hints; Acc/WellFounded inductives + intro/
        // apply stay in both lanes (Nat.lt_wf needs them).
        if !self.suppress_lossy_structure_stubs {
            self.add_decl(Declaration::Definition {
                name: fix_f_name.clone(),
                level_params: vec![u.clone(), v.clone()],
                type_: fix_f_type,
                value: fix_f_value,
                is_reducible: true,
            })?;
        }

        // --- WellFounded.fix type ---
        // {α : Sort u} → {C : α → Sort v} → {r : α → α → Prop} →
        //   WellFounded r →
        //   ((x : α) → ((y : α) → r y x → C y) → C x) →
        //   (x : α) → C x
        let fix_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let c_type = mk_c_type(&b, &alpha);
            let (c_id, c) = b.fresh_local(c_type.clone());
            let r_type = mk_r_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let wf_r = Expr::app(Expr::app(wf_const.clone(), alpha.clone()), r.clone());
            let (hwf_id, _) = b.fresh_local(wf_r.clone());
            let f_type = mk_step_type(&b, &alpha, &r, &c);
            let (f_id, _) = b.fresh_local(f_type.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let c_x = Expr::app(c, x);
            let t = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), c_x);
            let t = b.mk_pi(f_id, BinderInfo::Default, f_type, t);
            let t = b.mk_pi(hwf_id, BinderInfo::Default, wf_r, t);
            let t = b.mk_pi(r_id, BinderInfo::Implicit, r_type, t);
            let t = b.mk_pi(c_id, BinderInfo::Implicit, c_type, t);
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        // --- WellFounded.fix value ---
        // fun {α} {C} {r} hwf F x =>
        //   fixF.{u,v} α r C F x (proj(WellFounded, 0, hwf) x)
        let fix_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let c_type = mk_c_type(&b, &alpha);
            let (c_id, c) = b.fresh_local(c_type.clone());
            let r_type = mk_r_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let wf_r = Expr::app(Expr::app(wf_const.clone(), alpha.clone()), r.clone());
            let (hwf_id, hwf) = b.fresh_local(wf_r.clone());
            let f_type = mk_step_type(&b, &alpha, &r, &c);
            let (f_id, f_var) = b.fresh_local(f_type.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());

            // acc_proof = proj(WellFounded, 0, hwf) applied to x
            let acc_proof = Expr::app(Expr::proj(wf_name.clone(), 0, hwf), x.clone());

            // WellFounded.fixF.{u,v} α r C F x acc_proof
            let fix_f_const =
                Expr::const_(fix_f_name.clone(), vec![u_level.clone(), v_level.clone()]);
            let body = Expr::app(fix_f_const, alpha.clone());
            let body = Expr::app(body, r.clone());
            let body = Expr::app(body, c.clone());
            let body = Expr::app(body, f_var);
            let body = Expr::app(body, x.clone());
            let body = Expr::app(body, acc_proof);

            let t = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), body);
            let t = b.mk_lam(f_id, BinderInfo::Default, f_type, t);
            let t = b.mk_lam(hwf_id, BinderInfo::Default, wf_r, t);
            let t = b.mk_lam(r_id, BinderInfo::Implicit, r_type, t);
            let t = b.mk_lam(c_id, BinderInfo::Implicit, c_type, t);
            let t = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        // IMPORT MODE: `WellFounded.fix` delegates to the gated `fixF` — it
        // rides the same gate (see above).
        if !self.suppress_lossy_structure_stubs {
            self.add_decl(Declaration::Definition {
                name: Name::from_string("WellFounded.fix"),
                level_params: vec![u.clone(), v.clone()],
                type_: fix_type,
                value: fix_value,
                is_reducible: true,
            })?;
        }

        self.well_founded_init = true;
        Ok(())
    }

    /// Check if WellFounded has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.well_founded_init == true`
    #[cfg(test)]
    pub(crate) fn has_well_founded(&self) -> bool {
        self.well_founded_init
    }
}
