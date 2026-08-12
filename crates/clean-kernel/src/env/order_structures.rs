// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Order hierarchy typeclasses for Environment
//!
//! This module contains order hierarchy init_* and has_* functions:
//! - Trans (transitivity)
//! - Preorder
//! - PartialOrder
//! - LinearOrder
//!
//! Standalone relation property typeclasses (Reflexive, Antisymm, Irrefl, Asymm)
//! are in order_relation_props.rs.
//!
//! Split for #307.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Lean's universe arguments for a `Trans` instance over `Prop`-valued relations
/// on a `Type 0` carrier.
///
/// `Trans.{u, v, w, u_1, u_2, u_3}` orders the three RELATION sorts first
/// (`Prop` = `Sort 0` here) and the three CARRIER sorts last (`Type 0` =
/// `Sort 1`). Every in-kernel `Trans`/`Trans.mk` application must spell the six
/// levels in that order — see [`Environment::init_trans`].
pub(crate) fn prop_rel_trans_levels() -> Vec<Level> {
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    vec![
        zero.clone(),
        zero.clone(),
        zero,
        one.clone(),
        one.clone(),
        one,
    ]
}

impl Environment {
    /// Register Lean's `outParam` reducible identity when it is not already in
    /// scope.
    ///
    /// ```text
    /// @[reducible] def outParam.{u} (α : Sort u) : Sort u := α
    /// ```
    ///
    /// `Trans`'s third relation is an `outParam` in Lean (`Init/Prelude.lean`),
    /// and the marker is load-bearing: `Trans.trans h₁ h₂` only synthesizes
    /// because the instance *determines* `t` rather than having to match a `t`
    /// the caller already fixed (`clean-elab/src/tc_outparam.rs` reads the
    /// marker straight off the class type). The kernel prelude previously had no
    /// `outParam` constant at all, so the wrapper could not be spelled.
    ///
    /// Idempotent via `get_const`, so this is safe to call from every
    /// `init_*` that needs the wrapper. The declaration is byte-for-byte Lean's,
    /// so the `.olean` import collides on a type-EQUAL name (no new row in
    /// `data/prelude_collision_census.json`).
    fn init_out_param(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("outParam");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::from_kind(ExprKind::Sort(u_level));

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _alpha) = b.fresh_local(sort_u.clone());
            let body = b.mk_pi(
                alpha_id,
                BinderInfo::Default,
                sort_u.clone(),
                sort_u.clone(),
            );
            b.finish(body)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let body = b.mk_lam(alpha_id, BinderInfo::Default, sort_u.clone(), alpha);
            b.finish(body)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![u],
            type_,
            value,
            is_reducible: true,
        })
    }

    /// Initialize Trans typeclass for transitivity of relations (Lean 4 form)
    ///
    /// Lean 4 definition (Init/Prelude.lean:1314):
    /// ```text
    /// class Trans (r : α → β → Sort u) (s : β → γ → Sort v) (t : outParam (α → γ → Sort w))
    /// ```
    ///
    /// Kernel form with all auto-bound implicits — this is what we register,
    /// spelling for spelling:
    /// - `Trans.{u, v, w, u_1, u_2, u_3} :`
    ///     `{α : Sort u_1} → {β : Sort u_2} → {γ : Sort u_3} →`
    ///     `(r : α → β → Sort u) → (s : β → γ → Sort v) →`
    ///     `(t : outParam (α → γ → Sort w)) → Sort (max 1 u u_1 u_2 u_3 v w)`
    ///
    /// # WS17 / lossy-stub retirement
    ///
    /// This used to be a **3-universe, `Prop`-valued, `outParam`-less**
    /// simplification ("all current use cases have Prop-valued relations"). That
    /// was a lossy stub, and `.olean` import is first-registered-wins
    /// (`clean-olean/src/import/load_register.rs`) — so the stub permanently
    /// SHADOWED Lean's real `Trans`. Everything downstream then saw a class the
    /// user never wrote:
    ///
    /// * olean bodies referencing `Trans.trans.{6 levels}` raised
    ///   `LevelCountMismatch { expected: 3, got: 6 }`;
    /// * every imported `Trans` instance was typed against the discarded
    ///   6-universe class, so none of them re-checked;
    /// * `Trans.trans h₁ h₂` therefore failed *directly*, not only inside
    ///   `calc` — including on `Nat ≤` and on `List.Sublist`.
    ///
    /// Registering Lean's actual shape retires that: the collision is now
    /// type-EQUAL, so it no longer discards anything. Suppression
    /// (`suppress_lossy_structure_stubs`) is NOT the fix here — it only helps
    /// the `.olean`-verification lane, while `clean check` builds its
    /// environment with `Environment::with_prelude()` (flag off) and would
    /// simply lose `Trans` entirely in the no-import case.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.trans_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_trans(&mut self) -> Result<(), EnvError> {
        if self.trans_init {
            return Ok(());
        }
        // Import-verification mode still skips the stub. It is now Lean-faithful,
        // so this is no longer load-bearing for fidelity — but registering
        // strictly fewer trusted constants on the import path can only make the
        // kernel check the REAL declaration, so the suppression stays.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }

        // Initialize Eq for Prop
        self.init_eq()?;
        // `outParam` is part of `Trans`'s Lean-faithful type.
        self.init_out_param()?;

        // Lean's universe-parameter ORDER for `Trans` is
        // [u, v, w, u_1, u_2, u_3] — the three relation sorts first, then the
        // three auto-bound carrier sorts. Imported terms spell
        // `Trans.{l1,…,l6}` positionally, so this order is load-bearing.
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let w = Name::from_string("w");
        let u1 = Name::from_string("u_1");
        let u2 = Name::from_string("u_2");
        let u3 = Name::from_string("u_3");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let w_level = Level::param(w.clone());
        let u1_level = Level::param(u1.clone());
        let u2_level = Level::param(u2.clone());
        let u3_level = Level::param(u3.clone());
        let sort_u1 = Expr::from_kind(ExprKind::Sort(u1_level.clone()));
        let sort_u2 = Expr::from_kind(ExprKind::Sort(u2_level.clone()));
        let sort_u3 = Expr::from_kind(ExprKind::Sort(u3_level.clone()));

        // `Sort (max 1 u u_1 u_2 u_3 v w)` — the class universe Lean computes
        // for this structure (verified against `Init.olean`, v4.30.0-rc2).
        let trans_sort = {
            let mut s = Level::succ(Level::zero());
            for l in [
                &u_level, &u1_level, &u2_level, &u3_level, &v_level, &w_level,
            ] {
                s = Level::max(s, l.clone());
            }
            Expr::from_kind(ExprKind::Sort(s))
        };

        let trans_levels = vec![
            u_level.clone(),
            v_level.clone(),
            w_level.clone(),
            u1_level.clone(),
            u2_level.clone(),
            u3_level.clone(),
        ];

        // Helper: build a `Sort`-valued binary relation type (x → y → Sort s)
        let rel_type = |x: &Expr, y: &Expr, s: &Level| {
            Expr::arrow(
                x.clone(),
                Expr::arrow(y.clone(), Expr::from_kind(ExprKind::Sort(s.clone()))),
            )
        };
        // `t`'s binder domain, wrapped in Lean's `outParam` marker. Its universe
        // is the sort of `α → γ → Sort w`, i.e. `max (w+1) u_1 u_3`
        // (`imax` collapses because `w+1` is never zero).
        let out_param_rel = |x: &Expr, y: &Expr, xs: &Level, ys: &Level| {
            let lvl = Level::max(
                Level::max(Level::succ(w_level.clone()), xs.clone()),
                ys.clone(),
            );
            Expr::app(
                Expr::const_(Name::from_string("outParam"), vec![lvl]),
                rel_type(x, y, &w_level),
            )
        };

        // Helper: apply a binary relation to two arguments
        let rel_app =
            |r: &Expr, a: &Expr, b: &Expr| Expr::app(Expr::app(r.clone(), a.clone()), b.clone());

        // Helper: build Trans.{u1,u2,u3} α β γ r s t
        let trans_app = |alpha: &Expr, beta: &Expr, gamma: &Expr, r: &Expr, s: &Expr, t: &Expr| {
            let c = Expr::const_(Name::from_string("Trans"), trans_levels.clone());
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(Expr::app(c, alpha.clone()), beta.clone()),
                            gamma.clone(),
                        ),
                        r.clone(),
                    ),
                    s.clone(),
                ),
                t.clone(),
            )
        };

        // Trans.{u, v, w, u_1, u_2, u_3} :
        //   {α : Sort u_1} → {β : Sort u_2} → {γ : Sort u_3} →
        //   (r : α → β → Sort u) → (s : β → γ → Sort v) →
        //   (t : outParam (α → γ → Sort w)) → Sort (max 1 u u_1 u_2 u_3 v w)
        //
        // Built with EnvDeclBuilder (#1444) — no manual bvar arithmetic.
        let trans_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u1.clone());
            let (beta_id, beta) = b.fresh_local(sort_u2.clone());
            let (gamma_id, gamma) = b.fresh_local(sort_u3.clone());
            let (r_id, _r) = b.fresh_local(rel_type(&alpha, &beta, &u_level));
            let (s_id, _s) = b.fresh_local(rel_type(&beta, &gamma, &v_level));
            let (t_id, _t) = b.fresh_local(out_param_rel(&alpha, &gamma, &u1_level, &u3_level));

            let body = trans_sort.clone();
            let body = b.mk_pi(
                t_id,
                BinderInfo::Default,
                out_param_rel(&alpha, &gamma, &u1_level, &u3_level),
                body,
            );
            let body = b.mk_pi(
                s_id,
                BinderInfo::Default,
                rel_type(&beta, &gamma, &v_level),
                body,
            );
            let body = b.mk_pi(
                r_id,
                BinderInfo::Default,
                rel_type(&alpha, &beta, &u_level),
                body,
            );
            let body = b.mk_pi(gamma_id, BinderInfo::Implicit, sort_u3.clone(), body);
            let body = b.mk_pi(beta_id, BinderInfo::Implicit, sort_u2.clone(), body);
            let body = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u1.clone(), body);
            b.finish(body)
        };

        // Trans.mk.{u, v, w, u_1, u_2, u_3} :
        //   {α : Sort u_1} → {β : Sort u_2} → {γ : Sort u_3} →
        //   {r : α → β → Sort u} → {s : β → γ → Sort v} →
        //   {t : outParam (α → γ → Sort w)} →
        //   (∀ {a : α} {b : β} {c : γ}, r a b → s b c → t a c) →
        //   Trans r s t
        //
        // Built with EnvDeclBuilder (#1444) — no manual bvar arithmetic.
        let trans_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u1.clone());
            let (beta_id, beta) = b.fresh_local(sort_u2.clone());
            let (gamma_id, gamma) = b.fresh_local(sort_u3.clone());
            let (r_id, r) = b.fresh_local(rel_type(&alpha, &beta, &u_level));
            let (s_id, s) = b.fresh_local(rel_type(&beta, &gamma, &v_level));
            let (t_id, t) = b.fresh_local(out_param_rel(&alpha, &gamma, &u1_level, &u3_level));

            // proof field: ∀ {a : α} {b : β} {c : γ}, r a b → s b c → t a c
            let proof_type = {
                let mut pb = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = pb.fresh_local(alpha.clone());
                let (bv_id, bv) = pb.fresh_local(beta.clone());
                let (c_id, c) = pb.fresh_local(gamma.clone());
                let (hab_id, _) = pb.fresh_local(rel_app(&r, &a, &bv));
                let (hbc_id, _) = pb.fresh_local(rel_app(&s, &bv, &c));

                let body = rel_app(&t, &a, &c);
                let body = pb.mk_pi(hbc_id, BinderInfo::Default, rel_app(&s, &bv, &c), body);
                let body = pb.mk_pi(hab_id, BinderInfo::Default, rel_app(&r, &a, &bv), body);
                let body = pb.mk_pi(c_id, BinderInfo::Implicit, gamma.clone(), body);
                let body = pb.mk_pi(bv_id, BinderInfo::Implicit, beta.clone(), body);
                let body = pb.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), body);
                pb.finish_child(body)
            };

            let (proof_id, _) = b.fresh_local(proof_type.clone());

            let result = trans_app(&alpha, &beta, &gamma, &r, &s, &t);
            let body = b.mk_pi(proof_id, BinderInfo::Default, proof_type, result);
            let body = b.mk_pi(
                t_id,
                BinderInfo::Implicit,
                out_param_rel(&alpha, &gamma, &u1_level, &u3_level),
                body,
            );
            let body = b.mk_pi(
                s_id,
                BinderInfo::Implicit,
                rel_type(&beta, &gamma, &v_level),
                body,
            );
            let body = b.mk_pi(
                r_id,
                BinderInfo::Implicit,
                rel_type(&alpha, &beta, &u_level),
                body,
            );
            let body = b.mk_pi(gamma_id, BinderInfo::Implicit, sort_u3.clone(), body);
            let body = b.mk_pi(beta_id, BinderInfo::Implicit, sort_u2.clone(), body);
            let body = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u1.clone(), body);
            b.finish(body)
        };

        let trans_ind = InductiveDecl {
            level_params: vec![
                u.clone(),
                v.clone(),
                w.clone(),
                u1.clone(),
                u2.clone(),
                u3.clone(),
            ],
            num_params: 6, // α, β, γ, r, s, t are parameters
            types: vec![InductiveType {
                name: Name::from_string("Trans"),
                type_: trans_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Trans.mk"),
                    type_: trans_mk_type,
                }],
            }],
        };

        self.add_inductive(trans_ind)?;

        // Register `Trans` as a type class with `t` (index 5) as an OUT-param —
        // exactly the class-extension payload Lean serializes for it
        // (`clean-olean/src/import/tests_class_ext_import.rs` pins
        // `find_class(&decoded, "Trans").out_params == vec![5]`). Without this
        // the elaborator never searched `Trans r s ?t` goals at all.
        self.register_class(KernelClassInfo {
            name: Name::from_string("Trans"),
            num_params: 6,
            out_params: vec![5],
            semi_out_params: vec![],
        });

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            Name::from_string("Trans"),
            vec![Name::from_string("trans")],
        )?;

        // Trans.trans.{u, v, w, u_1, u_2, u_3} :
        //   {α : Sort u_1} → {β : Sort u_2} → {γ : Sort u_3} →
        //   {r : α → β → Sort u} → {s : β → γ → Sort v} →
        //   {t : outParam (α → γ → Sort w)} →
        //   [Trans r s t] →
        //   {a : α} → {b : β} → {c : γ} → r a b → s b c → t a c
        //
        // Built with EnvDeclBuilder (#1444) — no manual bvar arithmetic.
        let (trans_field_type, trans_field_value) = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u1.clone());
            let (beta_id, beta) = b.fresh_local(sort_u2.clone());
            let (gamma_id, gamma) = b.fresh_local(sort_u3.clone());
            let (r_id, r) = b.fresh_local(rel_type(&alpha, &beta, &u_level));
            let (s_id, s) = b.fresh_local(rel_type(&beta, &gamma, &v_level));
            let (t_id, t) = b.fresh_local(out_param_rel(&alpha, &gamma, &u1_level, &u3_level));
            let inst_type = trans_app(&alpha, &beta, &gamma, &r, &s, &t);
            let (inst_id, _inst) = b.fresh_local(inst_type.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (bv_id, bv) = b.fresh_local(beta.clone());
            let (c_id, c) = b.fresh_local(gamma.clone());
            let (hab_id, _) = b.fresh_local(rel_app(&r, &a, &bv));
            let (hbc_id, _) = b.fresh_local(rel_app(&s, &bv, &c));

            // Type: close binders inside-out with mk_pi
            let ty = rel_app(&t, &a, &c);
            let ty = b.mk_pi(hbc_id, BinderInfo::Default, rel_app(&s, &bv, &c), ty);
            let ty = b.mk_pi(hab_id, BinderInfo::Default, rel_app(&r, &a, &bv), ty);
            let ty = b.mk_pi(c_id, BinderInfo::Implicit, gamma.clone(), ty);
            let ty = b.mk_pi(bv_id, BinderInfo::Implicit, beta.clone(), ty);
            let ty = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), ty);
            let ty = b.mk_pi(inst_id, BinderInfo::InstImplicit, inst_type.clone(), ty);
            let ty = b.mk_pi(
                t_id,
                BinderInfo::Implicit,
                out_param_rel(&alpha, &gamma, &u1_level, &u3_level),
                ty,
            );
            let ty = b.mk_pi(
                s_id,
                BinderInfo::Implicit,
                rel_type(&beta, &gamma, &v_level),
                ty,
            );
            let ty = b.mk_pi(
                r_id,
                BinderInfo::Implicit,
                rel_type(&alpha, &beta, &u_level),
                ty,
            );
            let ty = b.mk_pi(gamma_id, BinderInfo::Implicit, sort_u3.clone(), ty);
            let ty = b.mk_pi(beta_id, BinderInfo::Implicit, sort_u2.clone(), ty);
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u1.clone(), ty);
            let ty = b.finish(ty);

            // Value: λ {α β γ r s t} [inst] => proj("Trans", 0, inst)
            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(sort_u1.clone());
            let (vbe_id, vbeta) = vb.fresh_local(sort_u2.clone());
            let (vg_id, vgamma) = vb.fresh_local(sort_u3.clone());
            let (vr_id, vr) = vb.fresh_local(rel_type(&va, &vbeta, &u_level));
            let (vs_id, vs) = vb.fresh_local(rel_type(&vbeta, &vgamma, &v_level));
            let (vt_id, vt) = vb.fresh_local(out_param_rel(&va, &vgamma, &u1_level, &u3_level));
            let vinst_type = trans_app(&va, &vbeta, &vgamma, &vr, &vs, &vt);
            let (vinst_id, vinst) = vb.fresh_local(vinst_type.clone());

            let val = Expr::proj(Name::from_string("Trans"), 0, vinst);
            let val = vb.mk_lam(vinst_id, BinderInfo::InstImplicit, vinst_type, val);
            let val = vb.mk_lam(
                vt_id,
                BinderInfo::Implicit,
                out_param_rel(&va, &vgamma, &u1_level, &u3_level),
                val,
            );
            let val = vb.mk_lam(
                vs_id,
                BinderInfo::Implicit,
                rel_type(&vbeta, &vgamma, &v_level),
                val,
            );
            let val = vb.mk_lam(
                vr_id,
                BinderInfo::Implicit,
                rel_type(&va, &vbeta, &u_level),
                val,
            );
            let val = vb.mk_lam(vg_id, BinderInfo::Implicit, sort_u3.clone(), val);
            let val = vb.mk_lam(vbe_id, BinderInfo::Implicit, sort_u2.clone(), val);
            let val = vb.mk_lam(va_id, BinderInfo::Implicit, sort_u1.clone(), val);
            let val = vb.finish(val);

            (ty, val)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Trans.trans"),
            level_params: vec![
                u.clone(),
                v.clone(),
                w.clone(),
                u1.clone(),
                u2.clone(),
                u3.clone(),
            ],
            type_: trans_field_type,
            value: trans_field_value,
            is_reducible: true,
        })?;

        self.trans_init = true;
        Ok(())
    }

    /// Check if Trans typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.trans_init == true`
    #[cfg(test)]
    pub(crate) fn has_trans(&self) -> bool {
        self.trans_init
    }

    /// Initialize Preorder typeclass
    ///
    /// Preorder is a typeclass combining LE, LT with reflexivity and transitivity:
    /// - Preorder : Type u → Type u
    /// - Preorder.mk : {α : Type u} → [LE α] → [LT α] →
    ///                 (le_refl : ∀ a, a ≤ a) →
    ///                 (le_trans : ∀ a b c, a ≤ b → b ≤ c → a ≤ c) →
    ///                 Preorder α
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.preorder_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_preorder(&mut self) -> Result<(), EnvError> {
        if self.preorder_init {
            return Ok(());
        }
        // WS17: this hand-rolled `Preorder.mk` carries only 4 fields (it drops
        // Lean's trailing auto-param field `lt_iff_le_not_ge`), so seeding it
        // shadows the real 5-field Mathlib `Preorder` on import. In import-
        // verification mode skip the stub so the genuine structure registers.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }

        // Initialize dependencies
        self.init_le()?;
        self.init_lt()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

        // Preorder : Type u → Type u
        // Built with EnvDeclBuilder (#1444).
        let preorder_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let body = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
            let body = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(body)
        };

        // Helper: LE.le {α} [inst] a b
        let le_le = |alpha: &Expr, inst: &Expr, a: &Expr, b: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("LE.le"), vec![u_level.clone()]),
                            alpha.clone(),
                        ),
                        inst.clone(),
                    ),
                    a.clone(),
                ),
                b.clone(),
            )
        };

        let le_const_app = |alpha: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("LE"), vec![u_level.clone()]),
                alpha.clone(),
            )
        };
        let lt_const_app = |alpha: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("LT"), vec![u_level.clone()]),
                alpha.clone(),
            )
        };
        let preorder_const_app = |alpha: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("Preorder"), vec![u_level.clone()]),
                alpha.clone(),
            )
        };

        // Preorder.mk : {α : Type u} → [le : LE α] → [lt : LT α] →
        //               (le_refl : ∀ a : α, LE.le a a) →
        //               (le_trans : ∀ a b c : α, LE.le a b → LE.le b c → LE.le a c) →
        //               Preorder α
        //
        // Built with EnvDeclBuilder (#1444) — no manual bvar arithmetic.
        let preorder_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (le_id, le_inst) = b.fresh_local(le_const_app(&alpha));
            let (lt_id, _lt_inst) = b.fresh_local(lt_const_app(&alpha));

            // le_refl : ∀ a : α, LE.le a a
            let le_refl_type = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = cb.fresh_local(alpha.clone());
                let body = le_le(&alpha, &le_inst, &a, &a);
                let body = cb.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                cb.finish_child(body)
            };
            let (le_refl_id, _) = b.fresh_local(le_refl_type.clone());

            // le_trans : ∀ a b c : α, LE.le a b → LE.le b c → LE.le a c
            let le_trans_type = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = cb.fresh_local(alpha.clone());
                let (bv_id, bv) = cb.fresh_local(alpha.clone());
                let (c_id, c) = cb.fresh_local(alpha.clone());
                let (hab_id, _) = cb.fresh_local(le_le(&alpha, &le_inst, &a, &bv));
                let (hbc_id, _) = cb.fresh_local(le_le(&alpha, &le_inst, &bv, &c));

                let body = le_le(&alpha, &le_inst, &a, &c);
                let body = cb.mk_pi(
                    hbc_id,
                    BinderInfo::Default,
                    le_le(&alpha, &le_inst, &bv, &c),
                    body,
                );
                let body = cb.mk_pi(
                    hab_id,
                    BinderInfo::Default,
                    le_le(&alpha, &le_inst, &a, &bv),
                    body,
                );
                let body = cb.mk_pi(c_id, BinderInfo::Default, alpha.clone(), body);
                let body = cb.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), body);
                let body = cb.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                cb.finish_child(body)
            };
            let (le_trans_id, _) = b.fresh_local(le_trans_type.clone());

            let result = preorder_const_app(&alpha);
            let body = b.mk_pi(le_trans_id, BinderInfo::Default, le_trans_type, result);
            let body = b.mk_pi(le_refl_id, BinderInfo::Default, le_refl_type, body);
            let body = b.mk_pi(lt_id, BinderInfo::InstImplicit, lt_const_app(&alpha), body);
            let body = b.mk_pi(le_id, BinderInfo::InstImplicit, le_const_app(&alpha), body);
            let body = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(body)
        };

        let preorder_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1, // Only α is a parameter
            types: vec![InductiveType {
                name: Name::from_string("Preorder"),
                type_: preorder_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Preorder.mk"),
                    type_: preorder_mk_type,
                }],
            }],
        };

        self.add_inductive(preorder_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            Name::from_string("Preorder"),
            vec![
                Name::from_string("toLE"),
                Name::from_string("toLT"),
                Name::from_string("le_refl"),
                Name::from_string("le_trans"),
            ],
        )?;

        // Preorder.toLE : {α : Type u} → [Preorder α] → LE α
        // Built with EnvDeclBuilder (#1444).
        let (to_le_type, to_le_value) = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) = b.fresh_local(preorder_const_app(&alpha));

            let ty = le_const_app(&alpha);
            let ty = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                preorder_const_app(&alpha),
                ty,
            );
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), ty);
            let ty = b.finish(ty);

            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(type_u.clone());
            let (vi_id, vi) = vb.fresh_local(preorder_const_app(&va));
            let val = Expr::proj(Name::from_string("Preorder"), 0, vi);
            let val = vb.mk_lam(
                vi_id,
                BinderInfo::InstImplicit,
                preorder_const_app(&va),
                val,
            );
            let val = vb.mk_lam(va_id, BinderInfo::Implicit, type_u.clone(), val);
            let val = vb.finish(val);

            (ty, val)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Preorder.toLE"),
            level_params: vec![u.clone()],
            type_: to_le_type,
            value: to_le_value,
            is_reducible: true,
        })?;

        // Preorder.toLT : {α : Type u} → [Preorder α] → LT α
        // Built with EnvDeclBuilder (#1444).
        let (to_lt_type, to_lt_value) = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) = b.fresh_local(preorder_const_app(&alpha));

            let ty = lt_const_app(&alpha);
            let ty = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                preorder_const_app(&alpha),
                ty,
            );
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), ty);
            let ty = b.finish(ty);

            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(type_u.clone());
            let (vi_id, vi) = vb.fresh_local(preorder_const_app(&va));
            let val = Expr::proj(Name::from_string("Preorder"), 1, vi);
            let val = vb.mk_lam(
                vi_id,
                BinderInfo::InstImplicit,
                preorder_const_app(&va),
                val,
            );
            let val = vb.mk_lam(va_id, BinderInfo::Implicit, type_u.clone(), val);
            let val = vb.finish(val);

            (ty, val)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Preorder.toLT"),
            level_params: vec![u.clone()],
            type_: to_lt_type,
            value: to_lt_value,
            is_reducible: true,
        })?;

        // Preorder.le_refl : {α : Type u} → [inst : Preorder α] → ∀ a, a ≤ a
        // Built with EnvDeclBuilder (#1444).
        let (le_refl_type, le_refl_value) = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(preorder_const_app(&alpha));
            let (a_id, a) = b.fresh_local(alpha.clone());

            // LE.le via Preorder.toLE
            let le_inst_from_preorder = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Preorder.toLE"), vec![u_level.clone()]),
                    alpha.clone(),
                ),
                inst.clone(),
            );
            let ty = le_le(&alpha, &le_inst_from_preorder, &a, &a);
            let ty = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), ty);
            let ty = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                preorder_const_app(&alpha),
                ty,
            );
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), ty);
            let ty = b.finish(ty);

            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(type_u.clone());
            let (vi_id, vi) = vb.fresh_local(preorder_const_app(&va));
            let val = Expr::proj(Name::from_string("Preorder"), 2, vi);
            let val = vb.mk_lam(
                vi_id,
                BinderInfo::InstImplicit,
                preorder_const_app(&va),
                val,
            );
            let val = vb.mk_lam(va_id, BinderInfo::Implicit, type_u.clone(), val);
            let val = vb.finish(val);

            (ty, val)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Preorder.le_refl"),
            level_params: vec![u.clone()],
            type_: le_refl_type,
            value: le_refl_value,
            is_reducible: true,
        })?;

        self.preorder_init = true;
        Ok(())
    }

    /// Check if Preorder typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.preorder_init == true`
    #[cfg(test)]
    pub(crate) fn has_preorder(&self) -> bool {
        self.preorder_init
    }

    /// Initialize PartialOrder typeclass
    ///
    /// PartialOrder extends Preorder with antisymmetry:
    /// - PartialOrder : Type u → Type u
    /// - PartialOrder.mk : {α : Type u} → [Preorder α] →
    ///                     (le_antisymm : ∀ a b, a ≤ b → b ≤ a → a = b) →
    ///                     PartialOrder α
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.partial_order_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_partial_order(&mut self) -> Result<(), EnvError> {
        if self.partial_order_init {
            return Ok(());
        }
        // WS17: lossy `extends`-structure stub — suppress in import mode so the
        // real Mathlib `PartialOrder` registers with its full field telescope.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }

        // Initialize dependencies
        self.init_preorder()?;
        self.init_eq()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

        // PartialOrder : Type u → Type u
        // Built with EnvDeclBuilder (#1444).
        let partial_order_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let body = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
            let body = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(body)
        };

        let preorder_const_app = |alpha: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("Preorder"), vec![u_level.clone()]),
                alpha.clone(),
            )
        };
        let partial_order_const_app = |alpha: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("PartialOrder"), vec![u_level.clone()]),
                alpha.clone(),
            )
        };

        // Helper: LE.le via Preorder.toLE
        let preorder_le = |alpha: &Expr, preorder_inst: &Expr, a: &Expr, b: &Expr| {
            let le_inst = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Preorder.toLE"), vec![u_level.clone()]),
                    alpha.clone(),
                ),
                preorder_inst.clone(),
            );
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("LE.le"), vec![u_level.clone()]),
                            alpha.clone(),
                        ),
                        le_inst,
                    ),
                    a.clone(),
                ),
                b.clone(),
            )
        };

        // Helper: Eq.{succ u} α a b — α : Type u = Sort(succ u), so Eq needs {succ u}
        let eq_app = |alpha: &Expr, a: &Expr, b: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]),
                        alpha.clone(),
                    ),
                    a.clone(),
                ),
                b.clone(),
            )
        };

        // PartialOrder.mk : {α : Type u} → [pre : Preorder α] →
        //                   (le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b) →
        //                   PartialOrder α
        //
        // Built with EnvDeclBuilder (#1444) — no manual bvar arithmetic.
        let partial_order_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (pre_id, pre_inst) = b.fresh_local(preorder_const_app(&alpha));

            // le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b
            let le_antisymm_type = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = cb.fresh_local(alpha.clone());
                let (bv_id, bv) = cb.fresh_local(alpha.clone());
                let (hab_id, _) = cb.fresh_local(preorder_le(&alpha, &pre_inst, &a, &bv));
                let (hba_id, _) = cb.fresh_local(preorder_le(&alpha, &pre_inst, &bv, &a));

                let body = eq_app(&alpha, &a, &bv);
                let body = cb.mk_pi(
                    hba_id,
                    BinderInfo::Default,
                    preorder_le(&alpha, &pre_inst, &bv, &a),
                    body,
                );
                let body = cb.mk_pi(
                    hab_id,
                    BinderInfo::Default,
                    preorder_le(&alpha, &pre_inst, &a, &bv),
                    body,
                );
                let body = cb.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), body);
                let body = cb.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                cb.finish_child(body)
            };
            let (antisymm_id, _) = b.fresh_local(le_antisymm_type.clone());

            let result = partial_order_const_app(&alpha);
            let body = b.mk_pi(antisymm_id, BinderInfo::Default, le_antisymm_type, result);
            let body = b.mk_pi(
                pre_id,
                BinderInfo::InstImplicit,
                preorder_const_app(&alpha),
                body,
            );
            let body = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(body)
        };

        let partial_order_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1, // Only α is a parameter
            types: vec![InductiveType {
                name: Name::from_string("PartialOrder"),
                type_: partial_order_type,
                constructors: vec![Constructor {
                    name: Name::from_string("PartialOrder.mk"),
                    type_: partial_order_mk_type,
                }],
            }],
        };

        self.add_inductive(partial_order_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            Name::from_string("PartialOrder"),
            vec![
                Name::from_string("toPreorder"),
                Name::from_string("le_antisymm"),
            ],
        )?;

        // PartialOrder.toPreorder : {α : Type u} → [PartialOrder α] → Preorder α
        // Built with EnvDeclBuilder (#1444).
        let (to_preorder_type, to_preorder_value) = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) = b.fresh_local(partial_order_const_app(&alpha));

            let ty = preorder_const_app(&alpha);
            let ty = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                partial_order_const_app(&alpha),
                ty,
            );
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), ty);
            let ty = b.finish(ty);

            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(type_u.clone());
            let (vi_id, vi) = vb.fresh_local(partial_order_const_app(&va));
            let val = Expr::proj(Name::from_string("PartialOrder"), 0, vi);
            let val = vb.mk_lam(
                vi_id,
                BinderInfo::InstImplicit,
                partial_order_const_app(&va),
                val,
            );
            let val = vb.mk_lam(va_id, BinderInfo::Implicit, type_u.clone(), val);
            let val = vb.finish(val);

            (ty, val)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("PartialOrder.toPreorder"),
            level_params: vec![u.clone()],
            type_: to_preorder_type,
            value: to_preorder_value,
            is_reducible: true,
        })?;

        self.partial_order_init = true;
        Ok(())
    }

    /// Check if PartialOrder typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.partial_order_init == true`
    #[cfg(test)]
    pub(crate) fn has_partial_order(&self) -> bool {
        self.partial_order_init
    }

    /// Initialize LinearOrder typeclass
    ///
    /// LinearOrder extends PartialOrder with totality:
    /// - LinearOrder : Type u → Type u
    /// - LinearOrder.mk : {α : Type u} → [PartialOrder α] →
    ///                    (le_total : ∀ a b : α, a ≤ b ∨ b ≤ a) →
    ///                    LinearOrder α
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.linear_order_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_linear_order(&mut self) -> Result<(), EnvError> {
        if self.linear_order_init {
            return Ok(());
        }
        // WS17: lossy `extends`-structure stub — suppress in import mode so the
        // real Mathlib `LinearOrder` registers with its full field telescope.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }

        // Initialize dependencies
        self.init_partial_order()?;
        self.init_classical()?; // For Or (needed by le_total)

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));

        // LinearOrder : Type u → Type u
        // Built with EnvDeclBuilder (#1444).
        let linear_order_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _) = b.fresh_local(type_u.clone());
            let body = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
            let body = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(body)
        };

        let partial_order_const_app = |alpha: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("PartialOrder"), vec![u_level.clone()]),
                alpha.clone(),
            )
        };
        let linear_order_const_app = |alpha: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("LinearOrder"), vec![u_level.clone()]),
                alpha.clone(),
            )
        };

        // Helper: LE.le via PartialOrder.toPreorder.toLE
        let partial_order_le = |alpha: &Expr, po_inst: &Expr, a: &Expr, b: &Expr| {
            let preorder_inst = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("PartialOrder.toPreorder"),
                        vec![u_level.clone()],
                    ),
                    alpha.clone(),
                ),
                po_inst.clone(),
            );
            let le_inst = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Preorder.toLE"), vec![u_level.clone()]),
                    alpha.clone(),
                ),
                preorder_inst,
            );
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("LE.le"), vec![u_level.clone()]),
                            alpha.clone(),
                        ),
                        le_inst,
                    ),
                    a.clone(),
                ),
                b.clone(),
            )
        };

        let or_const = Expr::const_(Name::from_string("Or"), vec![]);

        // LinearOrder.mk : {α : Type u} → [po : PartialOrder α] →
        //                  (le_total : ∀ a b : α, a ≤ b ∨ b ≤ a) →
        //                  LinearOrder α
        //
        // Built with EnvDeclBuilder (#1444) — no manual bvar arithmetic.
        let linear_order_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (po_id, po_inst) = b.fresh_local(partial_order_const_app(&alpha));

            // le_total : ∀ a b : α, Or (a ≤ b) (b ≤ a)
            let le_total_type = {
                let mut cb = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = cb.fresh_local(alpha.clone());
                let (bv_id, bv) = cb.fresh_local(alpha.clone());

                let body = Expr::app(
                    Expr::app(
                        or_const.clone(),
                        partial_order_le(&alpha, &po_inst, &a, &bv),
                    ),
                    partial_order_le(&alpha, &po_inst, &bv, &a),
                );
                let body = cb.mk_pi(bv_id, BinderInfo::Default, alpha.clone(), body);
                let body = cb.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                cb.finish_child(body)
            };
            let (total_id, _) = b.fresh_local(le_total_type.clone());

            let result = linear_order_const_app(&alpha);
            let body = b.mk_pi(total_id, BinderInfo::Default, le_total_type, result);
            let body = b.mk_pi(
                po_id,
                BinderInfo::InstImplicit,
                partial_order_const_app(&alpha),
                body,
            );
            let body = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(body)
        };

        let linear_order_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1, // Only α is a parameter
            types: vec![InductiveType {
                name: Name::from_string("LinearOrder"),
                type_: linear_order_type,
                constructors: vec![Constructor {
                    name: Name::from_string("LinearOrder.mk"),
                    type_: linear_order_mk_type,
                }],
            }],
        };

        self.add_inductive(linear_order_ind)?;

        // Register structure fields for Expr::proj support
        self.register_structure_fields(
            Name::from_string("LinearOrder"),
            vec![
                Name::from_string("toPartialOrder"),
                Name::from_string("le_total"),
            ],
        )?;

        // LinearOrder.toPartialOrder : {α : Type u} → [LinearOrder α] → PartialOrder α
        // Built with EnvDeclBuilder (#1444).
        let (to_po_type, to_po_value) = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) = b.fresh_local(linear_order_const_app(&alpha));

            let ty = partial_order_const_app(&alpha);
            let ty = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                linear_order_const_app(&alpha),
                ty,
            );
            let ty = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), ty);
            let ty = b.finish(ty);

            let mut vb = EnvDeclBuilder::new();
            let (va_id, va) = vb.fresh_local(type_u.clone());
            let (vi_id, vi) = vb.fresh_local(linear_order_const_app(&va));
            let val = Expr::proj(Name::from_string("LinearOrder"), 0, vi);
            let val = vb.mk_lam(
                vi_id,
                BinderInfo::InstImplicit,
                linear_order_const_app(&va),
                val,
            );
            let val = vb.mk_lam(va_id, BinderInfo::Implicit, type_u.clone(), val);
            let val = vb.finish(val);

            (ty, val)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("LinearOrder.toPartialOrder"),
            level_params: vec![u.clone()],
            type_: to_po_type,
            value: to_po_value,
            is_reducible: true,
        })?;

        self.linear_order_init = true;
        Ok(())
    }

    /// Check if LinearOrder typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.linear_order_init == true`
    #[cfg(test)]
    pub(crate) fn has_linear_order(&self) -> bool {
        self.linear_order_init
    }
}
