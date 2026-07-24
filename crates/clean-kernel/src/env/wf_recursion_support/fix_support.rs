// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WF recursion Part 2: Acc helpers, fixFEq, and equation compiler support.
//!
//! - `Acc.inv` — extract sub-accessibility from an `Acc` proof
//! - `WellFounded.fixFEq` — the definitional unfolding equation for `fixF`
//! - `WellFounded.recursion` — alias for `WellFounded.fix`
//!
//! Reference: Lean 4 `Init/WF.lean` lines 60-120.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::wf_recursion_support::mk_rel_type;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Build `∀ (y : α), r y x → T y` as a child expression.
fn mk_forall_r_implies(
    parent: &EnvDeclBuilder,
    alpha: &Expr,
    r: &Expr,
    x: &Expr,
    target: &Expr,
) -> Expr {
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
}

/// Build `C` type `(α → Sort v)` as a child expression.
fn mk_c_type(parent: &EnvDeclBuilder, alpha: &Expr, sort_v: &Expr) -> Expr {
    let mut s = EnvDeclBuilder::child_of(parent);
    let (a_id, _) = s.fresh_local(alpha.clone());
    let t = s.mk_pi(a_id, BinderInfo::Default, alpha.clone(), sort_v.clone());
    s.finish_child(t)
}

/// Build `F` type `((x : α) → ((y : α) → r y x → C y) → C x)`.
fn mk_step_type(parent: &EnvDeclBuilder, alpha: &Expr, r: &Expr, c: &Expr) -> Expr {
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
}

impl Environment {
    /// `Acc.inv` — given `Acc r x` and `r y x`, produce `Acc r y`.
    ///
    /// Implemented via `@Acc.rec` with motive `fun x' _ => ∀ y, r y x' → Acc r y`.
    /// The step function just returns the sub-accessibility field `h`.
    pub(super) fn init_acc_inv(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let acc_const = Expr::const_(Name::from_string("Acc"), vec![u_level.clone()]);

        let inv_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let r_type = mk_rel_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let acc_r_x = Expr::app(
                Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone()),
                x.clone(),
            );
            let (h_id, _) = b.fresh_local(acc_r_x.clone());
            let (y_id, y) = b.fresh_local(alpha.clone());
            let r_y_x = Expr::app(Expr::app(r.clone(), y.clone()), x);
            let (hr_id, _) = b.fresh_local(r_y_x.clone());
            let acc_r_y = Expr::app(
                Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone()),
                y,
            );
            let t = b.mk_pi(hr_id, BinderInfo::Default, r_y_x, acc_r_y);
            let t = b.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), t);
            let t = b.mk_pi(h_id, BinderInfo::Default, acc_r_x, t);
            let t = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), t);
            let t = b.mk_pi(r_id, BinderInfo::Implicit, r_type, t);
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        let inv_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let r_type = mk_rel_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let acc_r_x = Expr::app(
                Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone()),
                x.clone(),
            );
            let (h_id, h) = b.fresh_local(acc_r_x.clone());
            let (y_id, y) = b.fresh_local(alpha.clone());
            let r_y_x = Expr::app(Expr::app(r.clone(), y.clone()), x.clone());
            let (hr_id, hr) = b.fresh_local(r_y_x.clone());

            // Motive: fun (x' : α) (_ : Acc r x') => ∀ y, r y x' → Acc r y
            let motive = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x2_id, x2) = s.fresh_local(alpha.clone());
                let acc_r_x2 = Expr::app(
                    Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone()),
                    x2.clone(),
                );
                let (unused_id, _) = s.fresh_local(acc_r_x2.clone());
                let inner = mk_forall_r_implies(
                    &s,
                    &alpha,
                    &r,
                    &x2,
                    &Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone()),
                );
                let t = s.mk_lam(unused_id, BinderInfo::Default, acc_r_x2, inner);
                let t = s.mk_lam(x2_id, BinderInfo::Default, alpha.clone(), t);
                s.finish_child(t)
            };

            // Step: fun x₁ h₂ _ih => h₂  (extract the sub-accessibility field)
            let step = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x1_id, x1) = s.fresh_local(alpha.clone());
                let h_field_type = mk_forall_r_implies(
                    &s,
                    &alpha,
                    &r,
                    &x1,
                    &Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone()),
                );
                let (h2_id, h2) = s.fresh_local(h_field_type.clone());
                // ih type: ∀ y, r y x₁ → (∀ y', r y' y → Acc r y')
                let acc_alpha_r = Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone());
                let ih_type = {
                    let mut s2 = EnvDeclBuilder::child_of(&s);
                    let (y2_id, y2) = s2.fresh_local(alpha.clone());
                    let r_y2_x1 = Expr::app(Expr::app(r.clone(), y2.clone()), x1.clone());
                    let motive_y = mk_forall_r_implies(&s2, &alpha, &r, &y2, &acc_alpha_r);
                    let inner = {
                        let mut s3 = EnvDeclBuilder::child_of(&s2);
                        let (hyp_id, _) = s3.fresh_local(r_y2_x1.clone());
                        let t = s3.mk_pi(hyp_id, BinderInfo::Default, r_y2_x1, motive_y);
                        s3.finish_child(t)
                    };
                    let t = s2.mk_pi(y2_id, BinderInfo::Default, alpha.clone(), inner);
                    s2.finish_child(t)
                };
                let (ih_id, _) = s.fresh_local(ih_type.clone());
                let t = s.mk_lam(ih_id, BinderInfo::Default, ih_type, h2);
                let t = s.mk_lam(h2_id, BinderInfo::Default, h_field_type, t);
                let t = s.mk_lam(x1_id, BinderInfo::Default, alpha.clone(), t);
                s.finish_child(t)
            };

            // @Acc.rec.{0, u} α r motive step x h y hr
            // Motive returns Prop (Sort 0), so first universe param is 0.
            let acc_rec = Expr::const_(
                Name::from_string("Acc.rec"),
                vec![Level::zero(), u_level.clone()],
            );
            let body = Expr::app(acc_rec, alpha.clone());
            let body = Expr::app(body, r.clone());
            let body = Expr::app(body, motive);
            let body = Expr::app(body, step);
            let body = Expr::app(body, x);
            let body = Expr::app(body, h);
            let body = Expr::app(body, y);
            let body = Expr::app(body, hr);

            let t = b.mk_lam(hr_id, BinderInfo::Default, r_y_x, body);
            let t = b.mk_lam(y_id, BinderInfo::Implicit, alpha.clone(), t);
            let t = b.mk_lam(h_id, BinderInfo::Default, acc_r_x, t);
            let t = b.mk_lam(x_id, BinderInfo::Implicit, alpha.clone(), t);
            let t = b.mk_lam(r_id, BinderInfo::Implicit, r_type, t);
            let t = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Acc.inv"),
            level_params: vec![u],
            type_: inv_type,
            value: inv_value,
            is_reducible: true,
        })
    }

    /// `WellFounded.fixFEq` — the unfolding equation for `fixF`.
    ///
    /// States: `fixF F x acx = F x (fun y p => fixF F y (Acc.inv acx p))`
    ///
    /// Discharged (Track GG) to a genuine `Declaration::Theorem` with an
    /// axiom-free proof term. The proof is `@Acc.rec` on the accessibility
    /// witness `acx` with the dependent motive
    /// `fun x' a' => fixF F x' a' = F x' (fun y p => fixF F y (Acc.inv a' p))`;
    /// the single `Acc.intro` minor premise closes by `Eq.refl` because both
    /// sides iota-reduce (via the `Acc.rec` reduction rule that backs both
    /// `fixF` and `Acc.inv`) to the common value
    /// `F x1 (fun y p => fixF F y (h1 y p))`.
    ///
    /// `axiom_deps(WellFounded.fixFEq)` is EMPTY: the proof references only
    /// `Acc.rec` (kernel recursor), `WellFounded.fixF`, `Acc.inv`, `Acc.intro`,
    /// and `Eq`/`Eq.refl` — all axiom-free Definitions / inductives.
    pub(super) fn init_fix_f_eq(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let sort_v = Expr::from_kind(ExprKind::Sort(v_level.clone()));
        let acc_const = Expr::const_(Name::from_string("Acc"), vec![u_level.clone()]);
        let fix_f_const = Expr::const_(
            Name::from_string("WellFounded.fixF"),
            vec![u_level.clone(), v_level.clone()],
        );
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![v_level.clone()]);

        // Build `fixF F a b` for accessibility witness `acc_arg` at point `pt`.
        let mk_fix_f =
            |alpha: &Expr, r: &Expr, c: &Expr, f_var: &Expr, pt: &Expr, acc_arg: &Expr| {
                let e = Expr::app(fix_f_const.clone(), alpha.clone());
                let e = Expr::app(e, r.clone());
                let e = Expr::app(e, c.clone());
                let e = Expr::app(e, f_var.clone());
                let e = Expr::app(e, pt.clone());
                Expr::app(e, acc_arg.clone())
            };

        // Build the recursion argument
        //   `fun (y : α) (p : r y pt) => fixF F y (Acc.inv α r pt acc_pt y p)`
        // for a given point `pt` and its accessibility witness `acc_pt`.
        let mk_rec_arg = |parent: &EnvDeclBuilder,
                          alpha: &Expr,
                          r: &Expr,
                          c: &Expr,
                          f_var: &Expr,
                          pt: &Expr,
                          acc_pt: &Expr| {
            let mut s = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = s.fresh_local(alpha.clone());
            let r_y_pt = Expr::app(Expr::app(r.clone(), y.clone()), pt.clone());
            let (p_id, p) = s.fresh_local(r_y_pt.clone());
            let acc_inv = Expr::const_(Name::from_string("Acc.inv"), vec![u_level.clone()]);
            let inv = Expr::app(acc_inv, alpha.clone());
            let inv = Expr::app(inv, r.clone());
            let inv = Expr::app(inv, pt.clone());
            let inv = Expr::app(inv, acc_pt.clone());
            let inv = Expr::app(inv, y.clone());
            let inv = Expr::app(inv, p);
            let fix_y = mk_fix_f(alpha, r, c, f_var, &y, &inv);
            let t = s.mk_lam(p_id, BinderInfo::Default, r_y_pt, fix_y);
            let t = s.mk_lam(y_id, BinderInfo::Default, alpha.clone(), t);
            s.finish_child(t)
        };

        // Build `∀ (y : α), r y x → Acc r y` as a child expression — the
        // `Acc.intro` field type for point `x`.
        let mk_h_field_type = |parent: &EnvDeclBuilder, alpha: &Expr, r: &Expr, x: &Expr| {
            let acc_alpha_r = Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone());
            mk_forall_r_implies(parent, alpha, r, x, &acc_alpha_r)
        };

        let fix_f_eq_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let r_type = mk_rel_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let c_type = mk_c_type(&b, &alpha, &sort_v);
            let (c_id, c) = b.fresh_local(c_type.clone());
            let f_type = mk_step_type(&b, &alpha, &r, &c);
            let (f_id, f_var) = b.fresh_local(f_type.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let acc_r_x = Expr::app(
                Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone()),
                x.clone(),
            );
            let (acx_id, acx) = b.fresh_local(acc_r_x.clone());

            // LHS: fixF F x acx
            let lhs = mk_fix_f(&alpha, &r, &c, &f_var, &x, &acx);

            // RHS: F x (fun y p => fixF F y (Acc.inv acx p))
            let rec_arg = mk_rec_arg(&b, &alpha, &r, &c, &f_var, &x, &acx);
            let rhs = Expr::app(Expr::app(f_var, x.clone()), rec_arg);

            let c_x = Expr::app(c, x);
            let result = Expr::app(Expr::app(Expr::app(eq_const.clone(), c_x), lhs), rhs);

            let t = b.mk_pi(acx_id, BinderInfo::Default, acc_r_x, result);
            let t = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), t);
            let t = b.mk_pi(f_id, BinderInfo::Default, f_type, t);
            let t = b.mk_pi(c_id, BinderInfo::Implicit, c_type, t);
            let t = b.mk_pi(r_id, BinderInfo::Implicit, r_type, t);
            let t = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), t);
            b.finish(t)
        };

        // --- proof value ---
        // fun {α} {r} {C} F x acx =>
        //   @Acc.rec.{0,u} α r MOTIVE STEP x acx
        // MOTIVE x' a' := fixF F x' a' = F x' (fun y p => fixF F y (Acc.inv a' p))
        // STEP x1 h1 _ih := @Eq.refl (C x1) (F x1 (fun y p => fixF F y (h1 y p)))
        let fix_f_eq_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let r_type = mk_rel_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let c_type = mk_c_type(&b, &alpha, &sort_v);
            let (c_id, c) = b.fresh_local(c_type.clone());
            let f_type = mk_step_type(&b, &alpha, &r, &c);
            let (f_id, f_var) = b.fresh_local(f_type.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let acc_alpha_r = Expr::app(Expr::app(acc_const.clone(), alpha.clone()), r.clone());
            let acc_r_x = Expr::app(acc_alpha_r.clone(), x.clone());
            let (acx_id, acx) = b.fresh_local(acc_r_x.clone());

            // MOTIVE: fun (x' : α) (a' : Acc r x') =>
            //   @Eq (C x') (fixF F x' a')
            //              (F x' (fun y p => fixF F y (Acc.inv α r x' a' y p)))
            let motive = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x2_id, x2) = s.fresh_local(alpha.clone());
                let acc_r_x2 = Expr::app(acc_alpha_r.clone(), x2.clone());
                let (a2_id, a2) = s.fresh_local(acc_r_x2.clone());
                let lhs = mk_fix_f(&alpha, &r, &c, &f_var, &x2, &a2);
                let rec_arg = mk_rec_arg(&s, &alpha, &r, &c, &f_var, &x2, &a2);
                let rhs = Expr::app(Expr::app(f_var.clone(), x2.clone()), rec_arg);
                let c_x2 = Expr::app(c.clone(), x2.clone());
                let eq_app = Expr::app(Expr::app(Expr::app(eq_const.clone(), c_x2), lhs), rhs);
                let t = s.mk_lam(a2_id, BinderInfo::Default, acc_r_x2, eq_app);
                let t = s.mk_lam(x2_id, BinderInfo::Default, alpha.clone(), t);
                s.finish_child(t)
            };

            // STEP: fun (x1 : α) (h1 : ∀ y, r y x1 → Acc r y)
            //           (_ih : ∀ y (p : r y x1), MOTIVE y (h1 y p)) =>
            //   @Eq.refl (C x1) (F x1 (fun y p => fixF F y (h1 y p)))
            let step = {
                let mut s = EnvDeclBuilder::child_of(&b);
                let (x1_id, x1) = s.fresh_local(alpha.clone());
                let h1_type = mk_h_field_type(&s, &alpha, &r, &x1);
                let (h1_id, h1) = s.fresh_local(h1_type.clone());

                // _ih type: ∀ (y : α) (p : r y x1), MOTIVE y (h1 y p)
                // We do not use `_ih`; build its precise type so `Acc.rec`'s
                // minor-premise shape is satisfied.
                let ih_type = {
                    let mut s2 = EnvDeclBuilder::child_of(&s);
                    let (y_id, y) = s2.fresh_local(alpha.clone());
                    let r_y_x1 = Expr::app(Expr::app(r.clone(), y.clone()), x1.clone());
                    // h1 y p : Acc r y — but the motive is evaluated at (y, h1 y p).
                    let inner = {
                        let mut s3 = EnvDeclBuilder::child_of(&s2);
                        let (p_id, p) = s3.fresh_local(r_y_x1.clone());
                        // acc_y := h1 y p
                        let acc_y = Expr::app(Expr::app(h1.clone(), y.clone()), p);
                        let lhs = mk_fix_f(&alpha, &r, &c, &f_var, &y, &acc_y);
                        let rec_arg = mk_rec_arg(&s3, &alpha, &r, &c, &f_var, &y, &acc_y);
                        let rhs = Expr::app(Expr::app(f_var.clone(), y.clone()), rec_arg);
                        let c_y = Expr::app(c.clone(), y.clone());
                        let eq_app =
                            Expr::app(Expr::app(Expr::app(eq_const.clone(), c_y), lhs), rhs);
                        let t = s3.mk_pi(p_id, BinderInfo::Default, r_y_x1, eq_app);
                        s3.finish_child(t)
                    };
                    let t = s2.mk_pi(y_id, BinderInfo::Default, alpha.clone(), inner);
                    s2.finish_child(t)
                };
                let (ih_id, _ih) = s.fresh_local(ih_type.clone());

                // common value: F x1 (fun y p => fixF F y (h1 y p))
                let common_rec_arg = {
                    let mut s2 = EnvDeclBuilder::child_of(&s);
                    let (y_id, y) = s2.fresh_local(alpha.clone());
                    let r_y_x1 = Expr::app(Expr::app(r.clone(), y.clone()), x1.clone());
                    let (p_id, p) = s2.fresh_local(r_y_x1.clone());
                    let acc_y = Expr::app(Expr::app(h1.clone(), y.clone()), p);
                    let fix_y = mk_fix_f(&alpha, &r, &c, &f_var, &y, &acc_y);
                    let t = s2.mk_lam(p_id, BinderInfo::Default, r_y_x1, fix_y);
                    let t = s2.mk_lam(y_id, BinderInfo::Default, alpha.clone(), t);
                    s2.finish_child(t)
                };
                let common = Expr::app(Expr::app(f_var.clone(), x1.clone()), common_rec_arg);
                let c_x1 = Expr::app(c.clone(), x1.clone());
                let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![v_level.clone()]);
                let refl_proof = Expr::app(Expr::app(eq_refl, c_x1), common);

                let t = s.mk_lam(ih_id, BinderInfo::Default, ih_type, refl_proof);
                let t = s.mk_lam(h1_id, BinderInfo::Default, h1_type, t);
                let t = s.mk_lam(x1_id, BinderInfo::Default, alpha.clone(), t);
                s.finish_child(t)
            };

            // @Acc.rec.{0, u} α r MOTIVE STEP x acx
            // Motive returns Prop (an `Eq`), so the recursor's first universe
            // (the motive's level) is 0.
            let acc_rec = Expr::const_(
                Name::from_string("Acc.rec"),
                vec![Level::zero(), u_level.clone()],
            );
            let body = Expr::app(acc_rec, alpha.clone());
            let body = Expr::app(body, r.clone());
            let body = Expr::app(body, motive);
            let body = Expr::app(body, step);
            let body = Expr::app(body, x.clone());
            let body = Expr::app(body, acx.clone());

            let t = b.mk_lam(acx_id, BinderInfo::Default, acc_r_x, body);
            let t = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), t);
            let t = b.mk_lam(f_id, BinderInfo::Default, f_type, t);
            let t = b.mk_lam(c_id, BinderInfo::Implicit, c_type, t);
            let t = b.mk_lam(r_id, BinderInfo::Implicit, r_type, t);
            let t = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u, t);
            b.finish(t)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("WellFounded.fixFEq"),
            level_params: vec![u, v],
            type_: fix_f_eq_type,
            value: fix_f_eq_value,
        })
    }

    /// `WellFounded.recursion` — alias for `WellFounded.fix`.
    ///
    /// Some equation compiler paths reference this name instead of `fix`.
    pub(super) fn init_wf_recursion(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level.clone()));
        let sort_v = Expr::from_kind(ExprKind::Sort(v_level.clone()));
        let wf_const = Expr::const_(Name::from_string("WellFounded"), vec![u_level.clone()]);
        let fix_const = Expr::const_(
            Name::from_string("WellFounded.fix"),
            vec![u_level.clone(), v_level.clone()],
        );

        let recursion_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let c_type = mk_c_type(&b, &alpha, &sort_v);
            let (c_id, c) = b.fresh_local(c_type.clone());
            let r_type = mk_rel_type(&b, &alpha);
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

        let recursion_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let c_type = mk_c_type(&b, &alpha, &sort_v);
            let (c_id, c) = b.fresh_local(c_type.clone());
            let r_type = mk_rel_type(&b, &alpha);
            let (r_id, r) = b.fresh_local(r_type.clone());
            let wf_r = Expr::app(Expr::app(wf_const, alpha.clone()), r.clone());
            let (hwf_id, hwf) = b.fresh_local(wf_r.clone());
            let f_type = mk_step_type(&b, &alpha, &r, &c);
            let (f_id, f_var) = b.fresh_local(f_type.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());

            let body = Expr::app(fix_const, alpha.clone());
            let body = Expr::app(body, c.clone());
            let body = Expr::app(body, r.clone());
            let body = Expr::app(body, hwf);
            let body = Expr::app(body, f_var);
            let body = Expr::app(body, x);

            let t = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), body);
            let t = b.mk_lam(f_id, BinderInfo::Default, f_type, t);
            let t = b.mk_lam(hwf_id, BinderInfo::Default, wf_r, t);
            let t = b.mk_lam(r_id, BinderInfo::Implicit, r_type, t);
            let t = b.mk_lam(c_id, BinderInfo::Implicit, c_type, t);
            let t = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u, t);
            b.finish(t)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("WellFounded.recursion"),
            level_params: vec![u, v],
            type_: recursion_type,
            value: recursion_value,
            is_reducible: true,
        })
    }
}
