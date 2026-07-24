// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage B1: the nonneg-rational base `NNRat`.
//!
//! # Why this module exists
//!
//! The sharp KKL max-influence retirement needs the `n`-free per-coordinate
//! charge `Σ_i Inf_i^{3/2} ≤ ε^{1/2}·I[f]`, whose RHS uses `sqrt`, which is
//! irrational in general. The plan
//! (`designs/2026-06-18-kkl-real-sqrt-layer-plan.md`, Stage B) builds an
//! AXIOM-FREE nonneg-real carrier `NNReal` as Cauchy sequences of *nonneg*
//! rationals, quotiented by `Quot` — exactly as Lean/Mathlib builds ℝ from
//! Cauchy sequences over ℚ. The terms of those sequences live in this module's
//! nonneg-rational base type `NNRat`.
//!
//! `NNRat` is the subtype `{ x : Rat // Rat.le Rat.zero x }`. Building it on the
//! existing `Subtype` inductive (`init_subtype`) keeps the construction
//! entirely inside the checked `self.add_decl` path: every declaration here is
//! a `Definition` or a `Declaration::Theorem` with a kernel-checked proof, and
//! every theorem's transitive admitted-axiom closure is empty (foundational
//! only). NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # What B1 registers
//!
//! Carrier + guard:
//! - `NNRat : Type 0`           := `@Subtype.{1} Rat (fun x => Rat.le Rat.zero x)`
//! - `NNRat.ofRat : (x : Rat) → Rat.le Rat.zero x → NNRat`  (the guarded ctor)
//! - `NNRat.val : NNRat → Rat`  (the underlying rational)
//! - `NNRat.property : (q : NNRat) → Rat.le Rat.zero (NNRat.val q)`  (nonneg)
//! - `NNRat.zero : NNRat`, `NNRat.one : NNRat`
//!
//! Arithmetic (nonneg-preserving):
//! - `NNRat.add : NNRat → NNRat → NNRat`
//! - `NNRat.mul : NNRat → NNRat → NNRat`
//!
//! Soundness / well-definedness theorems (each constructive, empty closure):
//! - `NNRat.val_ofRat  : NNRat.val (NNRat.ofRat x h) = x`
//! - `NNRat.val_add    : NNRat.val (NNRat.add p q) = Rat.add (NNRat.val p) (NNRat.val q)`
//! - `NNRat.val_mul    : NNRat.val (NNRat.mul p q) = Rat.mul (NNRat.val p) (NNRat.val q)`
//!
//! The `val_*` theorems are the load-bearing facts: they let every nonneg-real
//! inequality SQUARE down through `NNRat.val` to a purely rational inequality on
//! the live `Rat` carrier (the non-circularity insight of the plan's §2 — the
//! bridge is the on-main `Rat.le_of_sq_le_sq`). Because `NNRat.add` / `NNRat.mul`
//! push through `Rat.add` / `Rat.mul` on the `.val` component, `val_add` /
//! `val_mul` hold by `Eq.refl` (the `Subtype.val` projection of a `Subtype.mk`
//! reduces definitionally).

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved constant handles + small smart-constructors for the `NNRat`
/// nonneg-rational base. Wraps `OrderConsts` (the `Rat` order/arith surface).
pub(crate) struct NNRatConsts {
    /// `Rat` order/arith surface (`Rat`, `Rat.zero`, `Rat.add`, `Rat.mul`, …).
    order: OrderConsts,
    /// `Rat.le` (the RAW order relation — defeq to `LE.le Rat instLERat`, and the
    /// shape used by `Rat.mul_nonneg` / `Rat.add_le_add`).
    rat_le: Expr,
    rat_one: Expr,
    // Subtype machinery at level 1 (Rat : Type 0 = Sort 1).
    subtype: Expr,
    subtype_mk: Expr,
    subtype_val: Expr,
    subtype_property: Expr,
    // Rat lemmas used by the nonneg-preservation proofs.
    rat_mul_nonneg: Expr,
    rat_add_le_add: Expr,
    rat_zero_add: Expr,
    rat_le_refl: Expr,
    rat_le_of_sq_le_sq: Expr,
    // Eq.{1} over Rat, for the val_* soundness theorems.
    eq_rat: Expr,
    eq_refl_rat: Expr,
}

impl NNRatConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            rat_le: k("Rat.le"),
            rat_one: k("Rat.one"),
            subtype: Expr::const_(Name::from_string("Subtype"), vec![lvl1.clone()]),
            subtype_mk: Expr::const_(Name::from_string("Subtype.mk"), vec![lvl1.clone()]),
            subtype_val: Expr::const_(Name::from_string("Subtype.val"), vec![lvl1.clone()]),
            subtype_property: Expr::const_(
                Name::from_string("Subtype.property"),
                vec![lvl1.clone()],
            ),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            rat_add_le_add: k("Rat.add_le_add"),
            rat_zero_add: k("Rat.zero_add"),
            rat_le_refl: k("Rat.le_refl"),
            rat_le_of_sq_le_sq: k("Rat.le_of_sq_le_sq"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_refl_rat: Expr::const_(Name::from_string("Eq.refl"), vec![lvl1]),
        }
    }

    // ── Rat-level smart-constructors ────────────────────────────────────────

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn zero(&self) -> Expr {
        self.order.rat_zero.clone()
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        self.order.add(a, b)
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    /// `Rat.le a b` (raw relation).
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    /// `Rat.le Rat.zero a` — the nonneg predicate, applied.
    fn nonneg(&self, a: Expr) -> Expr {
        self.le(self.zero(), a)
    }
    /// `@Eq.{1} Rat a b`.
    fn eq_rat_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat(), a, b])
    }
    /// `@Eq.refl.{1} Rat a : Eq Rat a a`.
    fn refl_rat(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl_rat.clone(), [self.rat(), a])
    }

    // ── Subtype / predicate smart-constructors ──────────────────────────────

    /// `nnPred := fun x : Rat => Rat.le Rat.zero x` — the nonneg predicate, as a
    /// fresh closed lambda (built under `parent` so its FVar range is disjoint).
    fn nn_pred(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = ch.fresh_local(self.rat());
        let body = self.nonneg(x);
        let lam = ch.mk_lam(x_id, BinderInfo::Default, self.rat(), body);
        ch.finish_child(lam)
    }

    /// `NNRat` type as an Expr := `@Subtype.{1} Rat nnPred`.
    fn nnrat_ty(&self, parent: &EnvDeclBuilder) -> Expr {
        Expr::apps(self.subtype.clone(), [self.rat(), self.nn_pred(parent)])
    }

    /// `@Subtype.mk.{1} Rat nnPred val hval : NNRat`.
    fn subtype_mk_of(&self, parent: &EnvDeclBuilder, val: Expr, hval: Expr) -> Expr {
        Expr::apps(
            self.subtype_mk.clone(),
            [self.rat(), self.nn_pred(parent), val, hval],
        )
    }

    /// `@Subtype.val.{1} Rat nnPred q : Rat`.
    fn subtype_val_of(&self, parent: &EnvDeclBuilder, q: Expr) -> Expr {
        Expr::apps(
            self.subtype_val.clone(),
            [self.rat(), self.nn_pred(parent), q],
        )
    }

    /// `@Subtype.property.{1} Rat nnPred q : Rat.le Rat.zero (Subtype.val q)`.
    fn subtype_property_of(&self, parent: &EnvDeclBuilder, q: Expr) -> Expr {
        Expr::apps(
            self.subtype_property.clone(),
            [self.rat(), self.nn_pred(parent), q],
        )
    }

    /// `Rat.mul_nonneg a b ha hb : Rat.le 0 (a·b)`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_nonneg.clone(), [a, b, ha, hb])
    }

    /// `Rat.add_le_add a b c d (h1 : a≤b)(h2 : c≤d) : (a+c) ≤ (b+d)`.
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add.clone(), [a, b, cc, d, h1, h2])
    }

    /// `Rat.zero_add a : Eq (Rat.add Rat.zero a) a`.
    fn zero_add(&self, a: Expr) -> Expr {
        Expr::app(self.rat_zero_add.clone(), a)
    }

    /// `Rat.le_of_sq_le_sq a b (ha : 0≤a)(hb : 0≤b)(hsq : a·a ≤ b·b) : a ≤ b`.
    fn le_of_sq_le_sq(&self, a: Expr, b: Expr, ha: Expr, hb: Expr, hsq: Expr) -> Expr {
        Expr::apps(self.rat_le_of_sq_le_sq.clone(), [a, b, ha, hb, hsq])
    }

    /// `Eq.subst.{1} Rat motive a b h_eq h_motive_a : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_motive_a: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_motive_a)
    }
}

impl Environment {
    /// Register the Stage-B1 nonneg-rational base `NNRat` + its guarded
    /// constructor, projections, the `zero`/`one` points, the nonneg-preserving
    /// `add`/`mul`, and the three `val_*` soundness theorems. Idempotent.
    pub fn init_algebra_nnreal_nnrat(&mut self) -> Result<(), EnvError> {
        self.ensure_nnrat_deps()?;
        let c = NNRatConsts::new();
        self.register_nnrat_carrier(&c)?;
        self.register_nnrat_arith(&c)?;
        self.register_nnrat_soundness(&c)?;
        self.register_nnrat_order(&c)?;
        Ok(())
    }

    /// Ensure every `Rat`/`Subtype` prerequisite `NNRat` needs is present.
    fn ensure_nnrat_deps(&mut self) -> Result<(), EnvError> {
        self.init_subtype()?;
        // `Rat.mul_nonneg`, `Rat.add_le_add`, `Rat.zero_add`, `Rat.le_refl`,
        // plus the whole constructive Rat field/order surface.
        self.init_boolean_analysis_order_toolkit()?;
        self.register_rat_add_le_add()?;
        // `Rat.le_refl`, `Rat.zero_lt_one`, `Rat.lt_iff_le_not_le`,
        // `Rat.mul_nonneg`, `Rat.mul_pos`, plus `init_iff`/`init_and`/`init_or`
        // (needed for the `0 ≤ 1` extraction from `Rat.lt_iff_le_not_le`).
        self.register_rat_order_proofs()?;
        // `Rat.le_of_sq_le_sq` — the squaring-trick bridge (lifted to NNRat).
        self.init_boolean_analysis_order_toolkit_b1d()?;
        Ok(())
    }

    /// B1a. Carrier + guard: `NNRat`, `NNRat.val`, `NNRat.ofRat`,
    /// `NNRat.property`, `NNRat.zero`, `NNRat.one`.
    fn register_nnrat_carrier(&mut self, c: &NNRatConsts) -> Result<(), EnvError> {
        // NNRat : Type 0 := @Subtype.{1} Rat (fun x => Rat.le 0 x)
        if self.get_const(&Name::from_string("NNRat")).is_none() {
            let nnrat_ty_sort =
                Expr::from_kind(crate::expr::ExprKind::Sort(Level::succ(Level::zero())));
            let value = {
                let b = EnvDeclBuilder::new();
                c.nnrat_ty(&b)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNRat"),
                level_params: vec![],
                type_: nnrat_ty_sort,
                value,
                is_reducible: true,
            })?;
        }

        let nnrat = Expr::const_(Name::from_string("NNRat"), vec![]);

        // NNRat.val : NNRat → Rat := fun q => @Subtype.val Rat nnPred q
        if self.get_const(&Name::from_string("NNRat.val")).is_none() {
            let ty = Expr::pi(BinderInfo::Default, nnrat.clone(), c.rat());
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (q_id, q) = b.fresh_local(nnrat.clone());
                let body = c.subtype_val_of(&b, q);
                let e = b.mk_lam(q_id, BinderInfo::Default, nnrat.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNRat.val"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // NNRat.ofRat : (x : Rat) → Rat.le 0 x → NNRat
        //             := fun x h => @Subtype.mk Rat nnPred x h
        if self.get_const(&Name::from_string("NNRat.ofRat")).is_none() {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(c.rat());
                let hnn = c.nonneg(x.clone());
                let (h_id, _h) = b.fresh_local(hnn.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hnn, nnrat.clone());
                let e = b.mk_pi(x_id, BinderInfo::Default, c.rat(), e);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(c.rat());
                let hnn = c.nonneg(x.clone());
                let (h_id, h) = b.fresh_local(hnn.clone());
                let body = c.subtype_mk_of(&b, x.clone(), h);
                let e = b.mk_lam(h_id, BinderInfo::Default, hnn, body);
                let e = b.mk_lam(x_id, BinderInfo::Default, c.rat(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNRat.ofRat"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // NNRat.property : (q : NNRat) → Rat.le 0 (NNRat.val q)
        //               := fun q => @Subtype.property Rat nnPred q
        if self
            .get_const(&Name::from_string("NNRat.property"))
            .is_none()
        {
            let nnrat_val = Expr::const_(Name::from_string("NNRat.val"), vec![]);
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (q_id, q) = b.fresh_local(nnrat.clone());
                let val_q = Expr::app(nnrat_val.clone(), q.clone());
                let concl = c.nonneg(val_q);
                let e = b.mk_pi(q_id, BinderInfo::Default, nnrat.clone(), concl);
                b.finish(e)
            };
            // Subtype.property q : nnPred (Subtype.val q) ≡ Rat.le 0 (Subtype.val q).
            // Since NNRat.val q ≡ Subtype.val q (NNRat.val unfolds), this is the
            // stated type up to defeq.
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (q_id, q) = b.fresh_local(nnrat.clone());
                let body = c.subtype_property_of(&b, q);
                let e = b.mk_lam(q_id, BinderInfo::Default, nnrat.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNRat.property"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // NNRat.zero : NNRat := NNRat.ofRat Rat.zero (Rat.le_refl Rat.zero)
        if self.get_const(&Name::from_string("NNRat.zero")).is_none() {
            let of_rat = Expr::const_(Name::from_string("NNRat.ofRat"), vec![]);
            // 0 ≤ 0 via Rat.le_refl Rat.zero.
            let h00 = Expr::app(c.rat_le_refl.clone(), c.zero());
            let value = Expr::apps(of_rat, [c.zero(), h00]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNRat.zero"),
                level_params: vec![],
                type_: nnrat.clone(),
                value,
                is_reducible: true,
            })?;
        }

        // NNRat.one : NNRat := NNRat.ofRat Rat.one h_0_le_1
        //   where h_0_le_1 : 0 ≤ 1 is the registered `Rat.zero_le_one`.
        if self.get_const(&Name::from_string("NNRat.one")).is_none() {
            self.register_rat_zero_le_one_nnrat()?;
            let of_rat = Expr::const_(Name::from_string("NNRat.ofRat"), vec![]);
            let h01 = Expr::const_(Name::from_string("Rat.zero_le_one"), vec![]);
            let value = Expr::apps(of_rat, [c.rat_one.clone(), h01]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNRat.one"),
                level_params: vec![],
                type_: nnrat,
                value,
                is_reducible: true,
            })?;
        }

        Ok(())
    }

    /// `Rat.zero_le_one : Rat.le Rat.zero Rat.one`.
    ///
    /// Proof: the on-main `Rat.zero_lt_one : Rat.lt Rat.zero Rat.one` gives the
    /// strict inequality; `Rat.lt_iff_le_not_le : Rat.lt a b ↔ (a≤b ∧ ¬b≤a)`
    /// then extracts the `≤` part via `Iff.mp` + `And.left` (the exact pattern
    /// used in `algebra_rat_abs_proof.rs`). Both inputs are kernel-checked
    /// constructive theorems with empty closure, so `Rat.zero_le_one` is too.
    fn register_rat_zero_le_one_nnrat(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_le_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = NNRatConsts::new();
        let zero = c.zero();
        let one = c.rat_one.clone();
        let ty = c.le(zero.clone(), one.clone());

        // le_0_1 : Rat.le 0 1 ; not_le_1_0 : ¬ Rat.le 1 0.
        let le_0_1 = c.le(zero.clone(), one.clone());
        let not_le_1_0 = Expr::app(
            Expr::const_(Name::from_string("Not"), vec![]),
            c.le(one.clone(), zero.clone()),
        );
        // lt_0_1 : Rat.lt 0 1 (the goal type of Rat.zero_lt_one).
        let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
        let lt_0_1 = Expr::apps(rat_lt, [zero.clone(), one.clone()]);
        // And (0≤1) (¬1≤0).
        let and_le_notle = Expr::apps(
            Expr::const_(Name::from_string("And"), vec![]),
            [le_0_1.clone(), not_le_1_0.clone()],
        );
        // Iff.mp (Rat.lt_iff_le_not_le 0 1) (Rat.zero_lt_one) : And (0≤1)(¬1≤0).
        let iff_mp = Expr::apps(
            Expr::const_(Name::from_string("Iff.mp"), vec![]),
            [
                lt_0_1,
                and_le_notle,
                Expr::apps(
                    Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
                    [zero.clone(), one.clone()],
                ),
                Expr::const_(Name::from_string("Rat.zero_lt_one"), vec![]),
            ],
        );
        // And.left _ _ iff_mp : Rat.le 0 1.
        let value = Expr::apps(
            Expr::const_(Name::from_string("And.left"), vec![]),
            [le_0_1, not_le_1_0, iff_mp],
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// B1b. Arithmetic: `NNRat.add`, `NNRat.mul` (nonneg-preserving).
    fn register_nnrat_arith(&mut self, c: &NNRatConsts) -> Result<(), EnvError> {
        let nnrat = Expr::const_(Name::from_string("NNRat"), vec![]);
        let nnrat_val = Expr::const_(Name::from_string("NNRat.val"), vec![]);
        let val = |q: Expr| Expr::app(nnrat_val.clone(), q);

        // NNRat.mul : NNRat → NNRat → NNRat
        //   := fun p q => Subtype.mk (val p · val q)
        //                            (Rat.mul_nonneg (val p)(val q)(prop p)(prop q))
        if self.get_const(&Name::from_string("NNRat.mul")).is_none() {
            let ty = Expr::pi(
                BinderInfo::Default,
                nnrat.clone(),
                Expr::pi(BinderInfo::Default, nnrat.clone(), nnrat.clone()),
            );
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(nnrat.clone());
                let (q_id, q) = b.fresh_local(nnrat.clone());
                let vp = val(p.clone());
                let vq = val(q.clone());
                let hp = c.subtype_property_of(&b, p.clone());
                let hq = c.subtype_property_of(&b, q.clone());
                let prod = c.rmul(vp.clone(), vq.clone());
                let hprod = c.mul_nonneg(vp, vq, hp, hq);
                let body = c.subtype_mk_of(&b, prod, hprod);
                let e = b.mk_lam(q_id, BinderInfo::Default, nnrat.clone(), body);
                let e = b.mk_lam(p_id, BinderInfo::Default, nnrat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNRat.mul"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // NNRat.add : NNRat → NNRat → NNRat
        //   := fun p q => Subtype.mk (val p + val q) hadd
        //   where hadd : 0 ≤ val p + val q is obtained from
        //     Rat.add_le_add 0 (val p) 0 (val q) (prop p)(prop q) : 0+0 ≤ vp+vq
        //   transported along (Rat.zero_add 0 : 0+0 = 0).
        if self.get_const(&Name::from_string("NNRat.add")).is_none() {
            let ty = Expr::pi(
                BinderInfo::Default,
                nnrat.clone(),
                Expr::pi(BinderInfo::Default, nnrat.clone(), nnrat.clone()),
            );
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(nnrat.clone());
                let (q_id, q) = b.fresh_local(nnrat.clone());
                let vp = val(p.clone());
                let vq = val(q.clone());
                let hp = c.subtype_property_of(&b, p.clone());
                let hq = c.subtype_property_of(&b, q.clone());
                let sum = c.radd(vp.clone(), vq.clone());

                // step : 0+0 ≤ vp+vq
                let step = c.add_le_add(c.zero(), vp.clone(), c.zero(), vq.clone(), hp, hq);
                // comm : 0+0 = 0   (Rat.zero_add Rat.zero)
                let zz_eq_z = c.zero_add(c.zero());
                // transport step along comm: motive t := t ≤ vp+vq
                let motive = {
                    let mut m = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = m.fresh_local(c.rat());
                    let body = c.le(t, sum.clone());
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
                };
                let zz = c.radd(c.zero(), c.zero());
                let hadd = c.subst(motive, zz, c.zero(), zz_eq_z, step);

                let body = c.subtype_mk_of(&b, sum, hadd);
                let e = b.mk_lam(q_id, BinderInfo::Default, nnrat.clone(), body);
                let e = b.mk_lam(p_id, BinderInfo::Default, nnrat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNRat.add"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        Ok(())
    }

    /// B1c. Soundness theorems: the `.val` projection commutes with `ofRat`,
    /// `add`, `mul`. Each holds by `Eq.refl` (the `Subtype.val`/`Subtype.mk`
    /// projection reduces definitionally). All `Declaration::Theorem`,
    /// constructive, empty closure.
    fn register_nnrat_soundness(&mut self, c: &NNRatConsts) -> Result<(), EnvError> {
        let nnrat = Expr::const_(Name::from_string("NNRat"), vec![]);
        let nnrat_val = Expr::const_(Name::from_string("NNRat.val"), vec![]);
        let nnrat_of = Expr::const_(Name::from_string("NNRat.ofRat"), vec![]);
        let nnrat_add = Expr::const_(Name::from_string("NNRat.add"), vec![]);
        let nnrat_mul = Expr::const_(Name::from_string("NNRat.mul"), vec![]);
        let val = |q: Expr| Expr::app(nnrat_val.clone(), q);

        // NNRat.val_ofRat : ∀ (x : Rat)(h : 0≤x), NNRat.val (NNRat.ofRat x h) = x
        if self
            .get_const(&Name::from_string("NNRat.val_ofRat"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(c.rat());
                let hnn = c.nonneg(x.clone());
                let (h_id, h) = b.fresh_local(hnn.clone());
                let lhs = val(Expr::apps(nnrat_of.clone(), [x.clone(), h]));
                let concl = c.eq_rat_ty(lhs, x.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hnn, concl);
                let e = b.mk_pi(x_id, BinderInfo::Default, c.rat(), e);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(c.rat());
                let hnn = c.nonneg(x.clone());
                let (h_id, _h) = b.fresh_local(hnn.clone());
                // NNRat.val (NNRat.ofRat x h) ≡ x, so Eq.refl x.
                let body = c.refl_rat(x.clone());
                let e = b.mk_lam(h_id, BinderInfo::Default, hnn, body);
                let e = b.mk_lam(x_id, BinderInfo::Default, c.rat(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("NNRat.val_ofRat"),
                level_params: vec![],
                type_: ty,
                value,
            })?;
        }

        // NNRat.val_mul : ∀ p q, NNRat.val (NNRat.mul p q) = Rat.mul (val p)(val q)
        if self
            .get_const(&Name::from_string("NNRat.val_mul"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(nnrat.clone());
                let (q_id, q) = b.fresh_local(nnrat.clone());
                let lhs = val(Expr::apps(nnrat_mul.clone(), [p.clone(), q.clone()]));
                let rhs = c.rmul(val(p.clone()), val(q.clone()));
                let concl = c.eq_rat_ty(lhs, rhs);
                let e = b.mk_pi(q_id, BinderInfo::Default, nnrat.clone(), concl);
                let e = b.mk_pi(p_id, BinderInfo::Default, nnrat.clone(), e);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(nnrat.clone());
                let (q_id, q) = b.fresh_local(nnrat.clone());
                let rhs = c.rmul(val(p.clone()), val(q.clone()));
                let body = c.refl_rat(rhs);
                let e = b.mk_lam(q_id, BinderInfo::Default, nnrat.clone(), body);
                let e = b.mk_lam(p_id, BinderInfo::Default, nnrat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("NNRat.val_mul"),
                level_params: vec![],
                type_: ty,
                value,
            })?;
        }

        // NNRat.val_add : ∀ p q, NNRat.val (NNRat.add p q) = Rat.add (val p)(val q)
        if self
            .get_const(&Name::from_string("NNRat.val_add"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(nnrat.clone());
                let (q_id, q) = b.fresh_local(nnrat.clone());
                let lhs = val(Expr::apps(nnrat_add.clone(), [p.clone(), q.clone()]));
                let rhs = c.radd(val(p.clone()), val(q.clone()));
                let concl = c.eq_rat_ty(lhs, rhs);
                let e = b.mk_pi(q_id, BinderInfo::Default, nnrat.clone(), concl);
                let e = b.mk_pi(p_id, BinderInfo::Default, nnrat.clone(), e);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(nnrat.clone());
                let (q_id, q) = b.fresh_local(nnrat.clone());
                let rhs = c.radd(val(p.clone()), val(q.clone()));
                let body = c.refl_rat(rhs);
                let e = b.mk_lam(q_id, BinderInfo::Default, nnrat.clone(), body);
                let e = b.mk_lam(p_id, BinderInfo::Default, nnrat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("NNRat.val_add"),
                level_params: vec![],
                type_: ty,
                value,
            })?;
        }

        Ok(())
    }

    /// B1d. Order + the squaring bridge:
    /// - `NNRat.le : NNRat → NNRat → Prop := fun p q => Rat.le (val p)(val q)`
    /// - `NNRat.le_of_sq_le_sq : ∀ p q, NNRat.le (mul p p)(mul q q) → NNRat.le p q`
    ///
    /// `NNRat.le_of_sq_le_sq` is the nonneg-real squaring trick lifted to the
    /// nonneg-rational base: an order fact about squares descends to an order
    /// fact about the roots, via the on-main `Rat.le_of_sq_le_sq` (which uses
    /// only `Classical.em` — foundational). Closure stays foundational.
    fn register_nnrat_order(&mut self, c: &NNRatConsts) -> Result<(), EnvError> {
        let nnrat = Expr::const_(Name::from_string("NNRat"), vec![]);
        let nnrat_val = Expr::const_(Name::from_string("NNRat.val"), vec![]);
        let nnrat_mul = Expr::const_(Name::from_string("NNRat.mul"), vec![]);
        let nnrat_prop = Expr::const_(Name::from_string("NNRat.property"), vec![]);
        let nnrat_le = Expr::const_(Name::from_string("NNRat.le"), vec![]);
        let val = |q: Expr| Expr::app(nnrat_val.clone(), q);
        let mul = |p: Expr, q: Expr| Expr::apps(nnrat_mul.clone(), [p, q]);
        let prop = |q: Expr| Expr::app(nnrat_prop.clone(), q);

        // NNRat.le : NNRat → NNRat → Prop := fun p q => Rat.le (val p)(val q)
        if self.get_const(&Name::from_string("NNRat.le")).is_none() {
            let prop_sort = Expr::from_kind(crate::expr::ExprKind::Sort(Level::zero()));
            let ty = Expr::pi(
                BinderInfo::Default,
                nnrat.clone(),
                Expr::pi(BinderInfo::Default, nnrat.clone(), prop_sort),
            );
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(nnrat.clone());
                let (q_id, q) = b.fresh_local(nnrat.clone());
                let body = c.le(val(p.clone()), val(q.clone()));
                let e = b.mk_lam(q_id, BinderInfo::Default, nnrat.clone(), body);
                let e = b.mk_lam(p_id, BinderInfo::Default, nnrat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNRat.le"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // NNRat.le_of_sq_le_sq : ∀ p q, NNRat.le (mul p p)(mul q q) → NNRat.le p q
        if self
            .get_const(&Name::from_string("NNRat.le_of_sq_le_sq"))
            .is_none()
        {
            // val_mul handle: NNRat.val_mul p q : val (mul p q) = (val p)·(val q).
            let val_mul_const = Expr::const_(Name::from_string("NNRat.val_mul"), vec![]);
            let val_mul = |p: Expr, q: Expr| Expr::apps(val_mul_const.clone(), [p, q]);

            let le_nn = |p: Expr, q: Expr| Expr::apps(nnrat_le.clone(), [p, q]);

            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(nnrat.clone());
                let (q_id, q) = b.fresh_local(nnrat.clone());
                let hyp = le_nn(mul(p.clone(), p.clone()), mul(q.clone(), q.clone()));
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let concl = le_nn(p.clone(), q.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
                let e = b.mk_pi(q_id, BinderInfo::Default, nnrat.clone(), e);
                let e = b.mk_pi(p_id, BinderInfo::Default, nnrat.clone(), e);
                b.finish(e)
            };

            let value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(nnrat.clone());
                let (q_id, q) = b.fresh_local(nnrat.clone());
                let hyp = le_nn(mul(p.clone(), p.clone()), mul(q.clone(), q.clone()));
                let (h_id, h) = b.fresh_local(hyp.clone());

                let vp = val(p.clone());
                let vq = val(q.clone());

                // hyp : NNRat.le (mul p p)(mul q q)
                //     ≡ Rat.le (val (mul p p)) (val (mul q q))   [NNRat.le unfolds]
                // We need: Rat.le (vp·vp) (vq·vq).
                // emp : val (mul p p) = vp·vp   (NNRat.val_mul p p)
                let emp = val_mul(p.clone(), p.clone());
                // emq : val (mul q q) = vq·vq   (NNRat.val_mul q q)
                let emq = val_mul(q.clone(), q.clone());

                let vmpp = val(mul(p.clone(), p.clone()));
                let vmqq = val(mul(q.clone(), q.clone()));
                let vp_vp = c.rmul(vp.clone(), vp.clone());
                let vq_vq = c.rmul(vq.clone(), vq.clone());

                // Step 1: rewrite the LEFT side of `h` via emp.
                //   motiveL t := Rat.le t (val (mul q q))
                let motive_l = {
                    let mut m = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = m.fresh_local(c.rat());
                    let body = c.le(t, vmqq.clone());
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
                };
                // h1 : Rat.le (vp·vp) (val (mul q q))
                let h1 = c.subst(motive_l, vmpp.clone(), vp_vp.clone(), emp, h);

                // Step 2: rewrite the RIGHT side of `h1` via emq.
                //   motiveR t := Rat.le (vp·vp) t
                let motive_r = {
                    let mut m = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = m.fresh_local(c.rat());
                    let body = c.le(vp_vp.clone(), t);
                    m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
                };
                // h2 : Rat.le (vp·vp) (vq·vq)
                let h2 = c.subst(motive_r, vmqq.clone(), vq_vq.clone(), emq, h1);

                // Conclude Rat.le vp vq via Rat.le_of_sq_le_sq, with the nonneg
                // witnesses NNRat.property p / q.  Result is defeq to
                // `NNRat.le p q`.
                let body =
                    c.le_of_sq_le_sq(vp.clone(), vq.clone(), prop(p.clone()), prop(q.clone()), h2);

                let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
                let e = b.mk_lam(q_id, BinderInfo::Default, nnrat.clone(), e);
                let e = b.mk_lam(p_id, BinderInfo::Default, nnrat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("NNRat.le_of_sq_le_sq"),
                level_params: vec![],
                type_: ty,
                value,
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const DEFS: &[&str] = &[
        "NNRat",
        "NNRat.val",
        "NNRat.ofRat",
        "NNRat.property",
        "NNRat.zero",
        "NNRat.one",
        "NNRat.add",
        "NNRat.mul",
        "NNRat.le",
    ];

    const THEOREMS: &[&str] = &[
        "Rat.zero_le_one",
        "NNRat.val_ofRat",
        "NNRat.val_add",
        "NNRat.val_mul",
        "NNRat.le_of_sq_le_sq",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_nnrat()
            .expect("init_algebra_nnreal_nnrat");
        env.init_algebra_nnreal_nnrat().expect("idempotent");
        env
    }

    #[test]
    fn test_nnrat_all_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in DEFS.iter().chain(THEOREMS.iter()) {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_nnrat_theorems_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be empty (foundational-only): {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
