// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.8 core's `ite`/implication simp lemmas and `forall_congr` (G39,
//! ledger (109)), as real kernel-checked theorems (NO `sorry`, NO axiom beyond
//! the foundational `propext`). The `Iff` lemmas are built here; the
//! `Eq`-concluding ones (`not_false_eq_true`, `not_true_eq_false`,
//! `forall_congr`, `implies_true`, `false_implies`) in `logic_simp_congr.rs`, which
//! [`Environment::register_simp_logic_iff_lemmas`] calls.
//!
//! Each statement is pinned Lean's (`#check @<name>`). The telescope is Lean
//! v4.30.0-rc2's where it differs from 4.8.0's (only `ite_eq_*_iff`, by binder
//! order): `.olean` import is first-registered-wins, so the prelude's spelling
//! must be the imported one (`data/prelude_collision_ratchet.json`).
//!
//! ```text
//! ite_eq_left_iff.{u}  : {α : Sort u} → {P : Prop} → [Decidable P] → {a b : α} →
//!                        (if P then a else b) = a ↔ (¬P → b = a)
//! ite_eq_right_iff.{u} : {α : Sort u} → {P : Prop} → [Decidable P] → {a b : α} →
//!                        (if P then a else b) = b ↔ (P → a = b)
//! not_false_eq_true    : (¬False) = True
//! not_true_eq_false    : (¬True) = False
//! implies_true.{u}     : (α : Sort u) → (α → True) = True
//! false_implies       : (p : Prop) → (False → p) = True
//! ne_eq.{u_1}         : {α : Sort u_1} → (a b : α) → (a ≠ b) = ¬(a = b)
//! imp_false            : {a : Prop} → (a → False) ↔ ¬a
//! Decidable.not_not    : {p : Prop} → [Decidable p] → ¬¬p ↔ p
//! forall_congr.{u}     : {α : Sort u} → {p q : α → Prop} →
//!                        (∀ a, p a = q a) → (∀ a, p a) = (∀ a, q a)
//! ```
//!
//! All but `forall_congr` are `@[simp]` in Lean 4.8 (checked with `getSimpTheorems`
//! against the pinned binary); `forall_congr` is what Clean's simp uses to
//! carry a rewrite under a `∀`/`→` binder (`simp/proof.rs`
//! `mk_forall_congr`), and without it a prelude-only simp under a binder
//! claimed a definitional change the kernel then refused. Lean's
//! `implies_congr` is NOT registered: nothing in Clean calls it.
//!
//! Proofs dispatch on the `Decidable` instance with `Decidable.rec` (as
//! `if_pos`/`if_neg` do, `logic_ite_lemmas.rs`), so each `ite` branch
//! ι-reduces; `absurd` discharges the impossible branch. Axiom closures of
//! the four `Iff` lemmas built here: empty. The five in
//! `logic_simp_congr.rs` are built with `propext`, so theirs is `{propext}`
//! (FOUNDATIONAL).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;

pub(super) fn konst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

pub(super) fn not(p: Expr) -> Expr {
    Expr::app(konst("Not"), p)
}

pub(super) fn arrow(dom: Expr, cod: Expr) -> Expr {
    // `cod` is closed over the new binder: lift nothing, it has no loose bvar
    // at index 0 by construction (every caller passes fvar-built terms).
    Expr::pi(BinderInfo::Default, dom, cod)
}

fn iff(a: Expr, b: Expr) -> Expr {
    Expr::apps(konst("Iff"), [a, b])
}

pub(super) fn iff_intro(a: Expr, b: Expr, mp: Expr, mpr: Expr) -> Expr {
    Expr::apps(konst("Iff.intro"), [a, b, mp, mpr])
}

/// `@absurd.{0} a b h1 h2 : b` for `h1 : a`, `h2 : ¬a`, `b : Prop`.
fn absurd_prop(a: Expr, b: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("absurd"), vec![Level::zero()]),
        [a, b, h1, h2],
    )
}

/// `@Decidable.rec.{0} c motive false_minor true_minor inst`.
fn dec_rec(c: Expr, motive: Expr, false_minor: Expr, true_minor: Expr, inst: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Decidable.rec"), vec![Level::zero()]),
        [c, motive, false_minor, true_minor, inst],
    )
}

impl Environment {
    /// Register `ite_eq_left_iff`, `ite_eq_right_iff`, `imp_false`,
    /// `Decidable.not_not`, `not_false_eq_true`, `not_true_eq_false` and
    /// `forall_congr`, `implies_true`, `false_implies` and `ne_eq`. Idempotent: a name already
    /// present (an imported Lean constant, or an earlier call) is left alone.
    pub(crate) fn register_simp_logic_iff_lemmas(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_true_false()?;
        self.init_iff()?;
        self.init_propext()?;
        self.init_decidable()?;
        self.init_ite()?;
        let missing = |env: &Environment, n: &str| env.get_const(&Name::from_string(n)).is_none();
        if missing(self, "imp_false") {
            self.register_imp_false()?;
        }
        if missing(self, "Decidable.not_not") {
            self.register_decidable_not_not()?;
        }
        for left in [true, false] {
            let name = if left {
                "ite_eq_left_iff"
            } else {
                "ite_eq_right_iff"
            };
            if missing(self, name) {
                self.register_ite_eq_side_iff(left)?;
            }
        }
        for value in [false, true] {
            let name = if value {
                "not_true_eq_false"
            } else {
                "not_false_eq_true"
            };
            if missing(self, name) {
                self.register_not_const_eq(value)?;
            }
        }
        for false_domain in [false, true] {
            let name = if false_domain {
                "false_implies"
            } else {
                "implies_true"
            };
            if missing(self, name) {
                self.register_implication_true(false_domain)?;
            }
        }
        if missing(self, "ne_eq") {
            self.register_ne_eq()?;
        }
        if missing(self, "forall_congr") && self.get_const(&Name::from_string("Eq.mp")).is_some() {
            self.register_forall_congr()?;
        }
        Ok(())
    }

    /// `imp_false : {a : Prop} → (a → False) ↔ ¬a` — `Iff.intro id id`, since
    /// `¬a` unfolds to `a → False`.
    fn register_imp_false(&mut self) -> Result<(), EnvError> {
        let prop = Expr::sort(Level::zero());
        let false_ = konst("False");
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(prop.clone());
            let concl = iff(arrow(a.clone(), false_.clone()), not(a));
            b.finish(b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), concl))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(prop.clone());
            let imp = arrow(a.clone(), false_.clone());
            let (h1_id, h1) = b.fresh_local(imp.clone());
            let mp = b.mk_lam(h1_id, BinderInfo::Default, imp.clone(), h1);
            let (h2_id, h2) = b.fresh_local(not(a.clone()));
            let mpr = b.mk_lam(h2_id, BinderInfo::Default, not(a.clone()), h2);
            let body = iff_intro(imp, not(a), mp, mpr);
            b.finish(b.mk_lam(a_id, BinderInfo::Implicit, prop, body))
        };
        // SOUNDNESS: checked `add_decl`; axiom closure empty.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("imp_false"),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Decidable.not_not : {p : Prop} → [Decidable p] → ¬¬p ↔ p`.
    ///
    /// mp: `fun hnn => Decidable.rec (fun _ => p) (fun hnp => absurd hnp hnn)
    /// (fun hp => hp) inst`; mpr: `fun hp hnp => hnp hp`.
    fn register_decidable_not_not(&mut self) -> Result<(), EnvError> {
        let prop = Expr::sort(Level::zero());
        let dec = |p: &Expr| Expr::app(konst("Decidable"), p.clone());
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let (i_id, _inst) = b.fresh_local(dec(&p));
            let concl = iff(not(not(p.clone())), p.clone());
            let r = b.mk_pi(i_id, BinderInfo::InstImplicit, dec(&p), concl);
            b.finish(b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), r))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let (i_id, inst) = b.fresh_local(dec(&p));
            let nnp = not(not(p.clone()));
            let (hnn_id, hnn) = b.fresh_local(nnp.clone());
            let (w_id, _w) = b.fresh_local(dec(&p));
            let motive = b.mk_lam(w_id, BinderInfo::Default, dec(&p), p.clone());
            let (hnp_id, hnp) = b.fresh_local(not(p.clone()));
            let false_minor = b.mk_lam(
                hnp_id,
                BinderInfo::Default,
                not(p.clone()),
                absurd_prop(not(p.clone()), p.clone(), hnp, hnn),
            );
            let (hp_id, hp) = b.fresh_local(p.clone());
            let true_minor = b.mk_lam(hp_id, BinderInfo::Default, p.clone(), hp);
            let mp_body = dec_rec(p.clone(), motive, false_minor, true_minor, inst);
            let mp = b.mk_lam(hnn_id, BinderInfo::Default, nnp.clone(), mp_body);
            let (hp2_id, hp2) = b.fresh_local(p.clone());
            let (hnp2_id, hnp2) = b.fresh_local(not(p.clone()));
            let inner = b.mk_lam(
                hnp2_id,
                BinderInfo::Default,
                not(p.clone()),
                Expr::app(hnp2, hp2),
            );
            let mpr = b.mk_lam(hp2_id, BinderInfo::Default, p.clone(), inner);
            let body = iff_intro(nnp, p.clone(), mp, mpr);
            let r = b.mk_lam(i_id, BinderInfo::InstImplicit, dec(&p), body);
            b.finish(b.mk_lam(p_id, BinderInfo::Implicit, prop, r))
        };
        // SOUNDNESS: checked `add_decl`; axiom closure empty.
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Decidable.not_not"),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `ite_eq_left_iff` (`left`) / `ite_eq_right_iff` (`!left`).
    ///
    /// With `L := @ite α P w a b = s` (`s = a` for left, `b` for right) and
    /// `R := ¬P → b = a` (left) / `P → a = b` (right), both directions are a
    /// `Decidable.rec` on the instance whose motive keeps `w` free, so each
    /// minor sees the ι-reduced `ite`.
    fn register_ite_eq_side_iff(&mut self, left: bool) -> Result<(), EnvError> {
        let u = Name::from_string("u_1");
        let lu = Level::param(u.clone());
        let sort_u = Expr::sort(lu.clone());
        let prop = Expr::sort(Level::zero());
        let eq = |alpha: &Expr, l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![lu.clone()]),
                [alpha.clone(), l, r],
            )
        };
        let refl = |alpha: &Expr, x: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![lu.clone()]),
                [alpha.clone(), x],
            )
        };
        let ite = |alpha: &Expr, p: &Expr, w: Expr, a: &Expr, bv: &Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("ite"), vec![lu.clone()]),
                [alpha.clone(), p.clone(), w, a.clone(), bv.clone()],
            )
        };
        let dec = |p: &Expr| Expr::app(konst("Decidable"), p.clone());
        // The telescope prefix {α} {p} [inst] {x y : α} — Lean v4.30.0-rc2's
        // order (`#check @ite_eq_left_iff`), which the prelude must match
        // because `.olean` import is first-registered-wins
        // (`data/prelude_collision_ratchet.json`); Lean 4.8.0's
        // `{α} {a b : α} {P} [inst]` is the same statement in another binder
        // order. Shared by type and value: the five locals in this order.
        let prefix = |b: &mut EnvDeclBuilder| -> [(FVarId, Expr, Expr); 5] {
            let (al_id, alpha) = b.fresh_local(sort_u.clone());
            let (p_id, p) = b.fresh_local(prop.clone());
            let (i_id, inst) = b.fresh_local(dec(&p));
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (b_id, bv) = b.fresh_local(alpha.clone());
            [
                (al_id, alpha.clone(), sort_u.clone()),
                (p_id, p.clone(), prop.clone()),
                (i_id, inst, dec(&p)),
                (a_id, a, alpha.clone()),
                (b_id, bv, alpha),
            ]
        };
        const INFOS: [BinderInfo; 5] = [
            BinderInfo::Implicit,
            BinderInfo::Implicit,
            BinderInfo::InstImplicit,
            BinderInfo::Implicit,
            BinderInfo::Implicit,
        ];
        let close =
            |b: &EnvDeclBuilder, locals: &[(FVarId, Expr, Expr); 5], body: Expr, as_pi: bool| {
                locals
                    .iter()
                    .zip(INFOS)
                    .rev()
                    .fold(body, |acc, ((id, _, ty), bi)| {
                        if as_pi {
                            b.mk_pi(*id, bi, ty.clone(), acc)
                        } else {
                            b.mk_lam(*id, bi, ty.clone(), acc)
                        }
                    })
            };
        // L(w) and R over the prefix locals.
        let side = |a: &Expr, bv: &Expr| if left { a.clone() } else { bv.clone() };
        let lhs_at = |alpha: &Expr, p: &Expr, w: Expr, a: &Expr, bv: &Expr| {
            eq(alpha, ite(alpha, p, w, a, bv), side(a, bv))
        };
        let rhs_prop = |alpha: &Expr, p: &Expr, a: &Expr, bv: &Expr| {
            if left {
                arrow(not(p.clone()), eq(alpha, bv.clone(), a.clone()))
            } else {
                arrow(p.clone(), eq(alpha, a.clone(), bv.clone()))
            }
        };

        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let locals = prefix(&mut b);
            let [alpha, p, inst, a, bv] = locals.clone().map(|(_, e, _)| e);
            let concl = iff(
                lhs_at(&alpha, &p, inst, &a, &bv),
                rhs_prop(&alpha, &p, &a, &bv),
            );
            b.finish(close(&b, &locals, concl, true))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let locals = prefix(&mut b);
            let [alpha, p, inst, a, bv] = locals.clone().map(|(_, e, _)| e);
            let l_inst = lhs_at(&alpha, &p, inst.clone(), &a, &bv);
            let r_prop = rhs_prop(&alpha, &p, &a, &bv);
            let not_p = not(p.clone());

            // mp : L(inst) → R, by `Decidable.rec` with motive
            //   fun w => L(w) → R.
            let mp = {
                let (w_id, w) = b.fresh_local(dec(&p));
                let motive_body = arrow(lhs_at(&alpha, &p, w, &a, &bv), r_prop.clone());
                let motive = b.mk_lam(w_id, BinderInfo::Default, dec(&p), motive_body);
                // isFalse hnp: `ite` is `b`. L = (b = side), R needs it.
                let (hnp_id, hnp) = b.fresh_local(not_p.clone());
                let l_false = eq(&alpha, bv.clone(), side(&a, &bv));
                let (h_id, h) = b.fresh_local(l_false.clone());
                let false_body = if left {
                    // R = ¬P → b = a; h : b = a.
                    let (x_id, _x) = b.fresh_local(not_p.clone());
                    b.mk_lam(x_id, BinderInfo::Default, not_p.clone(), h)
                } else {
                    // R = P → a = b; contradiction with hnp.
                    let (hp_id, hp) = b.fresh_local(p.clone());
                    let goal = eq(&alpha, a.clone(), bv.clone());
                    let r = absurd_prop(p.clone(), goal, hp, hnp.clone());
                    b.mk_lam(hp_id, BinderInfo::Default, p.clone(), r)
                };
                let false_body = b.mk_lam(h_id, BinderInfo::Default, l_false, false_body);
                let false_minor = b.mk_lam(hnp_id, BinderInfo::Default, not_p.clone(), false_body);
                // isTrue hp: `ite` is `a`. L = (a = side).
                let (hp_id, hp) = b.fresh_local(p.clone());
                let l_true = eq(&alpha, a.clone(), side(&a, &bv));
                let (h_id, h) = b.fresh_local(l_true.clone());
                let true_body = if left {
                    // R = ¬P → b = a; contradiction with hp.
                    let (x_id, x) = b.fresh_local(not_p.clone());
                    let goal = eq(&alpha, bv.clone(), a.clone());
                    let r = absurd_prop(p.clone(), goal, hp.clone(), x);
                    b.mk_lam(x_id, BinderInfo::Default, not_p.clone(), r)
                } else {
                    // R = P → a = b; h : a = b.
                    let (x_id, _x) = b.fresh_local(p.clone());
                    b.mk_lam(x_id, BinderInfo::Default, p.clone(), h)
                };
                let true_body = b.mk_lam(h_id, BinderInfo::Default, l_true, true_body);
                let true_minor = b.mk_lam(hp_id, BinderInfo::Default, p.clone(), true_body);
                dec_rec(p.clone(), motive, false_minor, true_minor, inst.clone())
            };

            // mpr : R → L(inst), by `Decidable.rec` with motive fun w => L(w).
            let mpr = {
                let (hr_id, hr) = b.fresh_local(r_prop.clone());
                let (w_id, w) = b.fresh_local(dec(&p));
                let motive_body = lhs_at(&alpha, &p, w, &a, &bv);
                let motive = b.mk_lam(w_id, BinderInfo::Default, dec(&p), motive_body);
                // isFalse hnp: goal `b = side`.
                let (hnp_id, hnp) = b.fresh_local(not_p.clone());
                let false_proof = if left {
                    Expr::app(hr.clone(), hnp) // hr hnp : b = a
                } else {
                    refl(&alpha, bv.clone()) // b = b
                };
                let false_minor = b.mk_lam(hnp_id, BinderInfo::Default, not_p.clone(), false_proof);
                // isTrue hp: goal `a = side`.
                let (hp_id, hp) = b.fresh_local(p.clone());
                let true_proof = if left {
                    refl(&alpha, a.clone()) // a = a
                } else {
                    Expr::app(hr.clone(), hp) // hr hp : a = b
                };
                let true_minor = b.mk_lam(hp_id, BinderInfo::Default, p.clone(), true_proof);
                let body = dec_rec(p.clone(), motive, false_minor, true_minor, inst.clone());
                b.mk_lam(hr_id, BinderInfo::Default, r_prop.clone(), body)
            };

            let body = iff_intro(l_inst, r_prop, mp, mpr);
            b.finish(close(&b, &locals, body, false))
        };
        // SOUNDNESS: checked `add_decl`; axiom closure empty (`Decidable.rec`,
        // `absurd`, `Eq.refl`, `Iff.intro`).
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(if left {
                "ite_eq_left_iff"
            } else {
                "ite_eq_right_iff"
            }),
            level_params: vec![u],
            type_,
            value,
        })
    }
}

#[cfg(test)]
#[path = "logic_simp_iff_tests.rs"]
mod tests;
