// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat totality / trichotomy family promoted from Axiom to constructive Theorem.
//!
//! Unlike `Int` (whose total order is irreducibly blocked by #2422), on `Nat`
//! totality and trichotomy are constructively provable by induction. This
//! module registers the following previously-`Declaration::Axiom` stubs as
//! sorry-free `Declaration::Theorem`s with empty domain-specific axiom closures
//! (`⊆ FOUNDATIONAL_AXIOMS`), kernel-typechecked:
//!
//! - `Nat.lt_or_eq_of_le`  (prerequisite; legacy stub in `order_lemmas.rs`)
//! - `Nat.lt_trichotomy`   (legacy stub in `order_lemmas_succ.rs`)
//! - `Nat.not_lt`          (legacy stub in `order_lemmas.rs::init_nat_not_lt_le`)
//! - `Nat.not_le`          (legacy stub in `order_lemmas.rs::init_nat_not_lt_le`)
//! - `Nat.lt_asymm`        (legacy stub in `order.rs::init_nat_lt_asymm`)
//! - `Nat.lt_of_le_of_ne`  (legacy stub in `order_lemmas.rs::init_nat_lt_of_le_of_ne`)
//!
//! # Proof backbone (all reused, all constructive Theorems with empty closures)
//!
//! - `Nat.le_or_lt : ∀ a b, Or (Nat.le a b) (Nat.lt b a)` — proven by double
//!   induction in `algebra_nat_mul_cancel_proof.rs` (`register_nat_le_or_lt`).
//!   We trigger its registration via `register_nat_mul_left_cancel_succ_proof`.
//!   This is the key that makes Nat totality tractable.
//! - `Nat.le_trans`, `Nat.le_antisymm`, `Nat.lt_irrefl` — constructive Theorems
//!   (`order_nat_le_trans_proof.rs`, `order_nat_le_antisymm_proof.rs`,
//!   `nat_lt_irrefl_proof.rs`).
//! - `Nat.le_refl`, `Nat.succ_le_succ`, `Nat.le_of_lt` — constructive Theorems
//!   (`nat_top_level_ordering_proof.rs`).
//!
//! `Nat.lt a b` is the reducible Definition `fun x y => Nat.le (Nat.succ x) y`,
//! and `instLENat` / `instLTNat` are reducible wrappers, so the typeclass forms
//! `LE.le @Nat instLENat …` / `LT.lt @Nat instLTNat …` are definitionally equal
//! to the raw `Nat.le` / `Nat.le (Nat.succ …)` forms produced by the proof
//! terms. The kernel accepts each proof against its declared (typeclass-shaped
//! or raw, matching the legacy Axiom) type up to that definitional equality.
//!
//! None of the proof terms reference trust markers (`sorry`, `sorryAx`, …) or
//! any `Declaration::Axiom`, so `env.axiom_deps(name)` is empty for each target
//! and `env.proof_quality(name) == ProofQuality::Constructive`.
//!
//! Tracking: Nat totality/trichotomy demotion (part of #3551).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::order::{nat_le_tc, nat_lt_tc};
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Reusable constant expressions for the Nat totality proofs.
struct NatTotalityConsts {
    nat: Expr,
    succ: Expr,
    le: Expr,
    le_refl_ctor: Expr,
    le_rec: Expr,
    le_trans_thm: Expr,
    lt_irrefl_thm: Expr,
    succ_le_succ_thm: Expr,
    le_of_lt_thm: Expr,
    le_or_lt_thm: Expr,
    lt_or_eq_thm: Expr,
    or_const: Expr,
    or_inl: Expr,
    or_inr: Expr,
    or_rec: Expr,
    iff_intro: Expr,
    eq_const: Expr,
    eq_refl: Expr,
    eq_subst: Expr,
    false_const: Expr,
    false_elim: Expr,
}

impl NatTotalityConsts {
    fn new() -> Self {
        // `Eq` over `Nat : Sort 1` uses level 1.
        let lvl1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            le_refl_ctor: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            le_rec: Expr::const_(Name::from_string("Nat.le.rec"), vec![]),
            le_trans_thm: Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
            lt_irrefl_thm: Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]),
            succ_le_succ_thm: Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
            le_of_lt_thm: Expr::const_(Name::from_string("Nat.le_of_lt"), vec![]),
            le_or_lt_thm: Expr::const_(Name::from_string("Nat.le_or_lt"), vec![]),
            lt_or_eq_thm: Expr::const_(Name::from_string("Nat.lt_or_eq_of_le"), vec![]),
            or_const: Expr::const_(Name::from_string("Or"), vec![]),
            or_inl: Expr::const_(Name::from_string("Or.inl"), vec![]),
            or_inr: Expr::const_(Name::from_string("Or.inr"), vec![]),
            // `Or.rec` eliminating into Prop carries a single Prop motive level.
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            iff_intro: Expr::const_(Name::from_string("Iff.intro"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1]),
            false_const: Expr::const_(Name::from_string("False"), vec![]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        }
    }

    fn succ_of(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }

    /// Raw `Nat.le lhs rhs`.
    fn le_of(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.le.clone(), [lhs, rhs])
    }

    /// Raw `Nat.lt lhs rhs`, written as its reducible expansion
    /// `Nat.le (Nat.succ lhs) rhs`.
    fn lt_raw(&self, lhs: Expr, rhs: Expr) -> Expr {
        self.le_of(self.succ_of(lhs), rhs)
    }

    /// `Nat.lt lhs rhs` via the `Nat.lt` constant (used where the canonical
    /// `Nat.lt_trichotomy` shape requires the named relation).
    fn lt_named(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.lt"), vec![]),
            [lhs, rhs],
        )
    }

    /// `Eq Nat lhs rhs` (level 1).
    fn eq_of(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.nat.clone(), lhs, rhs])
    }

    /// `Or a b`.
    fn or_of(&self, a: Expr, bb: Expr) -> Expr {
        Expr::apps(self.or_const.clone(), [a, bb])
    }

    /// `@Nat.le.refl n : Nat.le n n`.
    fn le_refl_app(&self, n: Expr) -> Expr {
        Expr::app(self.le_refl_ctor.clone(), n)
    }

    /// `@Nat.le_trans a b c hab hbc : Nat.le a c`.
    fn le_trans(&self, a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.le_trans_thm.clone(), [a, b, c, hab, hbc])
    }

    /// `@Nat.lt_irrefl a h : False` (`h : Nat.lt a a`).
    fn lt_irrefl(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.lt_irrefl_thm.clone(), [a, h])
    }

    /// `@Nat.le_of_lt a b h : Nat.le a b` (`h : Nat.lt a b`, typeclass form).
    fn le_of_lt(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.le_of_lt_thm.clone(), [a, b, h])
    }

    /// `@Nat.le_or_lt a b : Or (Nat.le a b) (Nat.lt b a)`.
    fn le_or_lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.le_or_lt_thm.clone(), [a, b])
    }

    /// `@Or.inl la lb h`.
    fn or_inl(&self, la: Expr, lb: Expr, h: Expr) -> Expr {
        Expr::apps(self.or_inl.clone(), [la, lb, h])
    }

    /// `@Or.inr la lb h`.
    fn or_inr(&self, la: Expr, lb: Expr, h: Expr) -> Expr {
        Expr::apps(self.or_inr.clone(), [la, lb, h])
    }

    /// `@False.elim C h : C`.
    fn false_elim(&self, c: Expr, h: Expr) -> Expr {
        Expr::apps(self.false_elim.clone(), [c, h])
    }
}

impl Environment {
    /// Register the Nat totality / trichotomy family as constructive
    /// `Declaration::Theorem`s.
    ///
    /// Registers (in dependency order, each idempotent on `get_const`):
    /// `Nat.lt_or_eq_of_le`, `Nat.lt_trichotomy`, `Nat.not_lt`, `Nat.not_le`,
    /// `Nat.lt_asymm`, `Nat.lt_of_le_of_ne`. `Nat.le_total` is reused from the
    /// existing `register_nat_le_total_proof` (#3599).
    ///
    /// Called from the legacy `init_nat_*` axiom sites (each `get_const`-guarded)
    /// so the Theorem form wins.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment.
    /// ENSURES: On success, each target is a `Declaration::Theorem` with
    ///          `proof_quality == Constructive`.
    /// ENSURES: Idempotent — each registration guards on `get_const`.
    pub(crate) fn init_nat_totality_proofs(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate — the
        // totality proofs here are constructed through `Nat.le_or_lt` /
        // `Nat.zero_le` from the import-gated mul-cancel web
        // (algebra_nat_mul_cancel_proof.rs), which is stated over the gated
        // Nat.add/Nat.mul seeds. The guarded axiom fallbacks in the callers
        // (init_nat_lt_asymm / init_nat_lt_trichotomy) become the upgradeable
        // value-less form the olean import discharges with the genuine
        // theorems. Default lane byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Supporting symbols.
        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_eq()?;
        self.init_iff()?;
        self.init_or()?;
        self.init_true_false()?; // False, False.elim

        // Constructive backbone lemmas.
        self.init_nat_top_level_ordering()?; // Nat.le_refl, succ_le_succ, le_of_lt
        self.register_nat_le_trans_proof()?;
        self.register_nat_le_antisymm_proof()?;
        self.register_nat_lt_irrefl_theorem()?;
        // Registers the constructive `Nat.le_or_lt` (and `Nat.zero_le`).
        self.register_nat_mul_left_cancel_succ_proof()?;

        let c = NatTotalityConsts::new();

        // `Nat.le_total` is registered as a constructive `Declaration::Theorem`
        // by the existing `register_nat_le_total_proof` (#3599, lives in
        // `order_nat_le_total_proof.rs`); reuse it rather than re-deriving it
        // here. Idempotent and a no-op if already present.
        self.register_nat_le_total_proof()?;

        // Prerequisite, then the six remaining targets.
        self.register_nat_lt_or_eq_of_le_proof(&c)?;
        self.register_nat_lt_trichotomy_proof(&c)?;
        self.register_nat_not_lt_proof(&c)?;
        self.register_nat_not_le_proof(&c)?;
        self.register_nat_lt_asymm_proof(&c)?;
        self.register_nat_lt_of_le_of_ne_proof(&c)?;

        Ok(())
    }

    /// `Nat.lt_or_eq_of_le : ∀ a b, Nat.le a b → Or (Nat.lt a b) (Eq a b)`
    /// (typeclass form: `LE.le … → Or (LT.lt …) (Eq …)`).
    ///
    /// Induction on `h : Nat.le a b` via `Nat.le.rec` (parameter `a`) with
    /// motive `fun (t : Nat) (_ : Nat.le a t) => Or (Nat.lt a t) (Eq a t)`:
    /// - refl case (`t = a`): `Or.inr … (Eq.refl a)` — proves `Eq a a`.
    /// - step case (`t → succ m`, `ih : Or (Nat.lt a m) (Eq a m)`): the goal
    ///   `Or (Nat.lt a (succ m)) (Eq a (succ m))` has left component
    ///   `Nat.lt a (succ m) ≡ Nat.le (succ a) (succ m)`. Case on `ih`:
    ///   - `Or.inl (hlt : Nat.le (succ a) m)`: `Nat.le.step` lifts it to
    ///     `Nat.le (succ a) (succ m)`, so `Or.inl …`.
    ///   - `Or.inr (heq : Eq a m)`: transport `Nat.le.refl (succ a)` along
    ///     `a = m` via `Eq.subst (motive := fun x => Nat.le (succ a) (succ x))`
    ///     to obtain `Nat.le (succ a) (succ m)`, so `Or.inl …`.
    fn register_nat_lt_or_eq_of_le_proof(&mut self, c: &NatTotalityConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_or_eq_of_le");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        let le_step_ctor = Expr::const_(Name::from_string("Nat.le.step"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let h_type = nat_le_tc(a.clone(), bb.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());

        // Type: ∀ a b, LE.le a b → Or (LT.lt a b) (Eq a b)
        let type_ = {
            let concl = c.or_of(
                nat_lt_tc(a.clone(), bb.clone()),
                c.eq_of(a.clone(), bb.clone()),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (t : Nat) (_ : Nat.le a t) => Or (Nat.lt a t) (Eq a t)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let le_a_t = c.le_of(a.clone(), t.clone());
            let (ht_id, _ht) = mb.fresh_local(le_a_t.clone());
            let body = c.or_of(
                c.lt_raw(a.clone(), t.clone()),
                c.eq_of(a.clone(), t.clone()),
            );
            let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_a_t, body);
            let lam_t = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), lam_h);
            mb.finish_child(lam_t)
        };

        // refl minor: Or.inr (Nat.lt a a) (Eq a a) (Eq.refl a) : Or (Nat.lt a a) (Eq a a)
        let minor_refl = {
            let lt_a_a = c.lt_raw(a.clone(), a.clone());
            let eq_a_a = c.eq_of(a.clone(), a.clone());
            let refl = Expr::apps(c.eq_refl.clone(), [c.nat.clone(), a.clone()]);
            c.or_inr(lt_a_a, eq_a_a, refl)
        };

        // step minor: fun {m} (_ : Nat.le a m) (ih : Or (Nat.lt a m) (Eq a m)) =>
        //   Or.rec on ih into Or (Nat.lt a (succ m)) (Eq a (succ m))
        let minor_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (m_id, m) = sb.fresh_local(c.nat.clone());
            let le_a_m = c.le_of(a.clone(), m.clone());
            let (hm_id, _hm) = sb.fresh_local(le_a_m.clone());

            let lt_a_m = c.lt_raw(a.clone(), m.clone()); // Nat.le (succ a) m
            let eq_a_m = c.eq_of(a.clone(), m.clone());
            let ih_type = c.or_of(lt_a_m.clone(), eq_a_m.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());

            let succ_m = c.succ_of(m.clone());
            let goal_left = c.lt_raw(a.clone(), succ_m.clone()); // Nat.le (succ a) (succ m)
            let goal_right = c.eq_of(a.clone(), succ_m.clone());
            let goal = c.or_of(goal_left.clone(), goal_right.clone());

            // const Or.rec motive: fun (_ : Or (Nat.lt a m) (Eq a m)) => goal
            let or_motive = {
                let mut om = EnvDeclBuilder::child_of(&sb);
                let or_ab = c.or_of(lt_a_m.clone(), eq_a_m.clone());
                let (hh_id, _hh) = om.fresh_local(or_ab.clone());
                let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ab, goal.clone());
                om.finish_child(lam)
            };

            // inl: fun (hlt : Nat.le (succ a) m) =>
            //   Or.inl … (Nat.le.step (succ a) m hlt) : Nat.le (succ a) (succ m)
            let case_inl = {
                let mut ic = EnvDeclBuilder::child_of(&sb);
                let (hlt_id, hlt) = ic.fresh_local(lt_a_m.clone());
                let succ_a = c.succ_of(a.clone());
                // Nat.le.step (succ a) m hlt : Nat.le (succ a) (succ m)
                let lifted = Expr::apps(le_step_ctor.clone(), [succ_a, m.clone(), hlt]);
                let body = c.or_inl(goal_left.clone(), goal_right.clone(), lifted);
                let lam = ic.mk_lam(hlt_id, BinderInfo::Default, lt_a_m.clone(), body);
                ic.finish_child(lam)
            };

            // inr: fun (heq : Eq a m) =>
            //   Or.inl … (Eq.subst (fun x => Nat.le (succ a) (succ x)) a m heq
            //                       (Nat.le.refl (succ a)))
            let case_inr = {
                let mut rc = EnvDeclBuilder::child_of(&sb);
                let (heq_id, heq) = rc.fresh_local(eq_a_m.clone());
                let succ_a = c.succ_of(a.clone());
                // subst motive: fun (x : Nat) => Nat.le (succ a) (succ x)
                let subst_motive = {
                    let mut mb = EnvDeclBuilder::child_of(&rc);
                    let (x_id, x) = mb.fresh_local(c.nat.clone());
                    let body = c.le_of(succ_a.clone(), c.succ_of(x));
                    let lam = mb.mk_lam(x_id, BinderInfo::Default, c.nat.clone(), body);
                    mb.finish_child(lam)
                };
                // Nat.le.refl (succ a) : Nat.le (succ a) (succ a) ≡ motive a
                let refl_le = c.le_refl_app(succ_a.clone());
                // Eq.subst Nat motive a m heq refl_le : motive m = Nat.le (succ a) (succ m)
                let lifted = Expr::apps(
                    c.eq_subst.clone(),
                    [
                        c.nat.clone(),
                        subst_motive,
                        a.clone(),
                        m.clone(),
                        heq,
                        refl_le,
                    ],
                );
                let body = c.or_inl(goal_left.clone(), goal_right.clone(), lifted);
                let lam = rc.mk_lam(heq_id, BinderInfo::Default, eq_a_m.clone(), body);
                rc.finish_child(lam)
            };

            let or_rec_app = Expr::apps(
                c.or_rec.clone(),
                [lt_a_m, eq_a_m, or_motive, case_inl, case_inr, ih.clone()],
            );

            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, or_rec_app);
            let lam_hm = sb.mk_lam(hm_id, BinderInfo::Default, le_a_m, lam_ih);
            let lam_m = sb.mk_lam(m_id, BinderInfo::Implicit, c.nat.clone(), lam_hm);
            sb.finish_child(lam_m)
        };

        // value: fun a b h => @Nat.le.rec a motive minor_refl minor_step b h
        let value = {
            let rec_app = Expr::apps(
                c.le_rec.clone(),
                [
                    a.clone(),
                    motive,
                    minor_refl,
                    minor_step,
                    bb.clone(),
                    h.clone(),
                ],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, rec_app);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.le.rec` / `Or.rec` / `Eq.subst` term.
        // Depends only on the constructive `Nat.le.refl` / `Nat.le.step`
        // (kernel constructors) and `Eq.refl` / `Eq.subst` (kernel built-ins).
        // No `sorry`, no self-reference, no domain-axiom dependency. Replaces
        // the prior `Declaration::Axiom` registered in `order_lemmas.rs`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.lt_trichotomy : ∀ a b, Or (Nat.lt a b) (Or (Eq a b) (Nat.lt b a))`
    /// (canonical shape: raw `Nat.lt`, `Eq` at level 1).
    ///
    /// `Or.rec` on `Nat.le_or_lt a b : Or (Nat.le a b) (Nat.lt b a)`:
    /// - `Or.inr (h : b < a)`: inner-right `Or.inr … (Or.inr … h)`.
    /// - `Or.inl (h : a ≤ b)`: `Or.rec` on `Nat.lt_or_eq_of_le a b h`:
    ///   - `Or.inl (hlt : a < b)`: outer-left `Or.inl … hlt`.
    ///   - `Or.inr (heq : a = b)`: inner-left `Or.inr … (Or.inl … heq)`.
    fn register_nat_lt_trichotomy_proof(&mut self, c: &NatTotalityConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_trichotomy");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        let tri_left = c.lt_named(a.clone(), bb.clone()); // Nat.lt a b
        let tri_eq = c.eq_of(a.clone(), bb.clone()); // Eq a b
        let tri_lt_ba = c.lt_named(bb.clone(), a.clone()); // Nat.lt b a
        let tri_inner = c.or_of(tri_eq.clone(), tri_lt_ba.clone());
        let goal = c.or_of(tri_left.clone(), tri_inner.clone());

        // Type: ∀ a b, Or (Nat.lt a b) (Or (Eq a b) (Nat.lt b a))
        let type_ = {
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), goal.clone());
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // Outer Or.rec over Nat.le_or_lt a b : Or (Nat.le a b) (Nat.lt b a).
        let src_left = c.le_of(a.clone(), bb.clone()); // a ≤ b
        let src_right = c.lt_raw(bb.clone(), a.clone()); // b < a

        let outer_motive = {
            let mut om = EnvDeclBuilder::child_of(&b);
            let or_ab = c.or_of(src_left.clone(), src_right.clone());
            let (hh_id, _hh) = om.fresh_local(or_ab.clone());
            let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ab, goal.clone());
            om.finish_child(lam)
        };

        // inl case (h : a ≤ b): Or.rec on Nat.lt_or_eq_of_le a b h.
        let outer_inl = {
            let mut ic = EnvDeclBuilder::child_of(&b);
            let (h_id, h) = ic.fresh_local(src_left.clone());

            // Nat.lt_or_eq_of_le a b h : Or (Nat.lt a b) (Eq a b) (typeclass lt,
            // defeq to raw Nat.lt a b).
            let in_left = c.lt_raw(a.clone(), bb.clone()); // Nat.le (succ a) b ≡ Nat.lt a b
            let in_right = c.eq_of(a.clone(), bb.clone());

            let inner_motive = {
                let mut om = EnvDeclBuilder::child_of(&ic);
                let or_ab = c.or_of(in_left.clone(), in_right.clone());
                let (hh_id, _hh) = om.fresh_local(or_ab.clone());
                let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ab, goal.clone());
                om.finish_child(lam)
            };
            // inner inl (hlt : a < b): Or.inl (Nat.lt a b) (Or (Eq a b) (Nat.lt b a)) hlt
            let inner_inl = {
                let mut iic = EnvDeclBuilder::child_of(&ic);
                let (hlt_id, hlt) = iic.fresh_local(in_left.clone());
                let body = c.or_inl(tri_left.clone(), tri_inner.clone(), hlt);
                let lam = iic.mk_lam(hlt_id, BinderInfo::Default, in_left.clone(), body);
                iic.finish_child(lam)
            };
            // inner inr (heq : a = b):
            //   Or.inr (Nat.lt a b) (Or (Eq a b) (Nat.lt b a))
            //     (Or.inl (Eq a b) (Nat.lt b a) heq)
            let inner_inr = {
                let mut iic = EnvDeclBuilder::child_of(&ic);
                let (heq_id, heq) = iic.fresh_local(in_right.clone());
                let inner = c.or_inl(tri_eq.clone(), tri_lt_ba.clone(), heq);
                let body = c.or_inr(tri_left.clone(), tri_inner.clone(), inner);
                let lam = iic.mk_lam(heq_id, BinderInfo::Default, in_right.clone(), body);
                iic.finish_child(lam)
            };

            let lt_or_eq = Expr::apps(c.lt_or_eq_thm.clone(), [a.clone(), bb.clone(), h]);
            let inner_rec = Expr::apps(
                c.or_rec.clone(),
                [
                    in_left,
                    in_right,
                    inner_motive,
                    inner_inl,
                    inner_inr,
                    lt_or_eq,
                ],
            );
            let lam = ic.mk_lam(h_id, BinderInfo::Default, src_left.clone(), inner_rec);
            ic.finish_child(lam)
        };

        // inr case (h : b < a):
        //   Or.inr (Nat.lt a b) (Or (Eq a b) (Nat.lt b a))
        //     (Or.inr (Eq a b) (Nat.lt b a) h)
        let outer_inr = {
            let mut rc = EnvDeclBuilder::child_of(&b);
            let (h_id, h) = rc.fresh_local(src_right.clone());
            // h : Nat.le (succ b) a ≡ Nat.lt b a, accepted by defeq for tri_lt_ba.
            let inner = c.or_inr(tri_eq.clone(), tri_lt_ba.clone(), h);
            let body = c.or_inr(tri_left.clone(), tri_inner.clone(), inner);
            let lam = rc.mk_lam(h_id, BinderInfo::Default, src_right.clone(), body);
            rc.finish_child(lam)
        };

        let value = {
            let major = c.le_or_lt(a.clone(), bb.clone());
            let or_rec_app = Expr::apps(
                c.or_rec.clone(),
                [
                    src_left,
                    src_right,
                    outer_motive,
                    outer_inl,
                    outer_inr,
                    major,
                ],
            );
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), or_rec_app);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked nested `Or.rec` term. Depends only on the
        // constructive `Nat.le_or_lt` and `Nat.lt_or_eq_of_le`. Replaces the
        // legacy `Declaration::Axiom` in `order_lemmas_succ.rs`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.not_lt : ∀ a b, Iff (Nat.lt a b → False) (Nat.le b a)` (tc form).
    ///
    /// `Iff.intro`:
    /// - mp `(Nat.lt a b → False) → Nat.le b a`: `Or.rec` on
    ///   `Nat.le_or_lt b a : Or (Nat.le b a) (Nat.lt a b)`; `inl` returns the
    ///   evidence, `inr (h : a < b)` feeds `h` to the hypothesis → `False.elim`.
    /// - mpr `Nat.le b a → Nat.lt a b → False`:
    ///   `Nat.lt_irrefl a (Nat.le_trans (succ a) b a hlt hle)`.
    fn register_nat_not_lt_proof(&mut self, c: &NatTotalityConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.not_lt");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        let lt_ab_tc = nat_lt_tc(a.clone(), bb.clone());
        let not_lt_ab = Expr::pi(BinderInfo::Default, lt_ab_tc.clone(), c.false_const.clone());
        let le_ba_tc = nat_le_tc(bb.clone(), a.clone());

        // Type: ∀ a b, Iff (Nat.lt a b → False) (Nat.le b a)
        let type_ = {
            let body = Expr::apps(
                Expr::const_(Name::from_string("Iff"), vec![]),
                [not_lt_ab.clone(), le_ba_tc.clone()],
            );
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // mp: fun (hnlt : Nat.lt a b → False) =>
        //   Or.rec on Nat.le_or_lt b a : Or (Nat.le b a) (Nat.lt a b)
        let mp = {
            let mut mc = EnvDeclBuilder::child_of(&b);
            let (hnlt_id, hnlt) = mc.fresh_local(not_lt_ab.clone());

            let src_left = c.le_of(bb.clone(), a.clone()); // b ≤ a
            let src_right = c.lt_raw(a.clone(), bb.clone()); // a < b
            let goal = c.le_of(bb.clone(), a.clone()); // b ≤ a

            let or_motive = {
                let mut om = EnvDeclBuilder::child_of(&mc);
                let or_ab = c.or_of(src_left.clone(), src_right.clone());
                let (hh_id, _hh) = om.fresh_local(or_ab.clone());
                let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ab, goal.clone());
                om.finish_child(lam)
            };
            let case_inl = {
                let mut ic = EnvDeclBuilder::child_of(&mc);
                let (h_id, h) = ic.fresh_local(src_left.clone());
                let lam = ic.mk_lam(h_id, BinderInfo::Default, src_left.clone(), h);
                ic.finish_child(lam)
            };
            let case_inr = {
                let mut rc = EnvDeclBuilder::child_of(&mc);
                let (h_id, h) = rc.fresh_local(src_right.clone());
                // hnlt h : False (h : Nat.lt a b, accepted by defeq).
                let absurd = Expr::app(hnlt.clone(), h);
                let body = c.false_elim(goal.clone(), absurd);
                let lam = rc.mk_lam(h_id, BinderInfo::Default, src_right.clone(), body);
                rc.finish_child(lam)
            };

            let major = c.le_or_lt(bb.clone(), a.clone());
            let or_rec_app = Expr::apps(
                c.or_rec.clone(),
                [src_left, src_right, or_motive, case_inl, case_inr, major],
            );
            let lam = mc.mk_lam(hnlt_id, BinderInfo::Default, not_lt_ab.clone(), or_rec_app);
            mc.finish_child(lam)
        };

        // mpr: fun (hle : Nat.le b a) (hlt : Nat.lt a b) =>
        //   Nat.lt_irrefl a (Nat.le_trans (succ a) b a hlt hle)
        let mpr = {
            let mut pc = EnvDeclBuilder::child_of(&b);
            let (hle_id, hle) = pc.fresh_local(le_ba_tc.clone());
            let (hlt_id, hlt) = pc.fresh_local(lt_ab_tc.clone());
            let succ_a = c.succ_of(a.clone());
            // Nat.le_trans (succ a) b a hlt hle : Nat.le (succ a) a ≡ Nat.lt a a
            let chained = c.le_trans(succ_a, bb.clone(), a.clone(), hlt, hle);
            let body = c.lt_irrefl(a.clone(), chained);
            let lam_hlt = pc.mk_lam(hlt_id, BinderInfo::Default, lt_ab_tc.clone(), body);
            let lam_hle = pc.mk_lam(hle_id, BinderInfo::Default, le_ba_tc.clone(), lam_hlt);
            pc.finish_child(lam_hle)
        };

        let value = {
            let intro = Expr::apps(
                c.iff_intro.clone(),
                [not_lt_ab.clone(), le_ba_tc.clone(), mp, mpr],
            );
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), intro);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Iff.intro` term; depends only on the
        // constructive `Nat.le_or_lt`, `Nat.le_trans`, `Nat.lt_irrefl`, and
        // `False.elim`. Replaces the legacy `Declaration::Axiom` in
        // `order_lemmas.rs::init_nat_not_lt_le`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.not_le : ∀ a b, Iff (Nat.le a b → False) (Nat.lt b a)` (tc form).
    ///
    /// `Iff.intro`:
    /// - mp `(Nat.le a b → False) → Nat.lt b a`: `Or.rec` on
    ///   `Nat.le_or_lt a b : Or (Nat.le a b) (Nat.lt b a)`; `inl (h : a ≤ b)`
    ///   feeds the hypothesis → `False.elim`, `inr` returns the evidence.
    /// - mpr `Nat.lt b a → Nat.le a b → False`:
    ///   `Nat.lt_irrefl b (Nat.le_trans (succ b) a b hlt hle)`.
    fn register_nat_not_le_proof(&mut self, c: &NatTotalityConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.not_le");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        let le_ab_tc = nat_le_tc(a.clone(), bb.clone());
        let not_le_ab = Expr::pi(BinderInfo::Default, le_ab_tc.clone(), c.false_const.clone());
        let lt_ba_tc = nat_lt_tc(bb.clone(), a.clone());

        // Type: ∀ a b, Iff (Nat.le a b → False) (Nat.lt b a)
        let type_ = {
            let body = Expr::apps(
                Expr::const_(Name::from_string("Iff"), vec![]),
                [not_le_ab.clone(), lt_ba_tc.clone()],
            );
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // mp: fun (hnle : Nat.le a b → False) =>
        //   Or.rec on Nat.le_or_lt a b : Or (Nat.le a b) (Nat.lt b a)
        let mp = {
            let mut mc = EnvDeclBuilder::child_of(&b);
            let (hnle_id, hnle) = mc.fresh_local(not_le_ab.clone());

            let src_left = c.le_of(a.clone(), bb.clone()); // a ≤ b
            let src_right = c.lt_raw(bb.clone(), a.clone()); // b < a
            let goal = c.lt_raw(bb.clone(), a.clone()); // Nat.lt b a (raw)

            let or_motive = {
                let mut om = EnvDeclBuilder::child_of(&mc);
                let or_ab = c.or_of(src_left.clone(), src_right.clone());
                let (hh_id, _hh) = om.fresh_local(or_ab.clone());
                let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ab, goal.clone());
                om.finish_child(lam)
            };
            let case_inl = {
                let mut ic = EnvDeclBuilder::child_of(&mc);
                let (h_id, h) = ic.fresh_local(src_left.clone());
                // hnle h : False (h : Nat.le a b).
                let absurd = Expr::app(hnle.clone(), h);
                let body = c.false_elim(goal.clone(), absurd);
                let lam = ic.mk_lam(h_id, BinderInfo::Default, src_left.clone(), body);
                ic.finish_child(lam)
            };
            let case_inr = {
                let mut rc = EnvDeclBuilder::child_of(&mc);
                let (h_id, h) = rc.fresh_local(src_right.clone());
                let lam = rc.mk_lam(h_id, BinderInfo::Default, src_right.clone(), h);
                rc.finish_child(lam)
            };

            let major = c.le_or_lt(a.clone(), bb.clone());
            let or_rec_app = Expr::apps(
                c.or_rec.clone(),
                [src_left, src_right, or_motive, case_inl, case_inr, major],
            );
            let lam = mc.mk_lam(hnle_id, BinderInfo::Default, not_le_ab.clone(), or_rec_app);
            mc.finish_child(lam)
        };

        // mpr: fun (hlt : Nat.lt b a) (hle : Nat.le a b) =>
        //   Nat.lt_irrefl b (Nat.le_trans (succ b) a b hlt hle)
        let mpr = {
            let mut pc = EnvDeclBuilder::child_of(&b);
            let (hlt_id, hlt) = pc.fresh_local(lt_ba_tc.clone());
            let (hle_id, hle) = pc.fresh_local(le_ab_tc.clone());
            let succ_b = c.succ_of(bb.clone());
            // Nat.le_trans (succ b) a b hlt hle : Nat.le (succ b) b ≡ Nat.lt b b
            let chained = c.le_trans(succ_b, a.clone(), bb.clone(), hlt, hle);
            let body = c.lt_irrefl(bb.clone(), chained);
            let lam_hle = pc.mk_lam(hle_id, BinderInfo::Default, le_ab_tc.clone(), body);
            let lam_hlt = pc.mk_lam(hlt_id, BinderInfo::Default, lt_ba_tc.clone(), lam_hle);
            pc.finish_child(lam_hlt)
        };

        let value = {
            let intro = Expr::apps(
                c.iff_intro.clone(),
                [not_le_ab.clone(), lt_ba_tc.clone(), mp, mpr],
            );
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), intro);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Iff.intro` term; depends only on the
        // constructive `Nat.le_or_lt`, `Nat.le_trans`, `Nat.lt_irrefl`, and
        // `False.elim`. Replaces the legacy `Declaration::Axiom` in
        // `order_lemmas.rs::init_nat_not_lt_le`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.lt_asymm : ∀ a b, Nat.lt a b → Nat.lt b a → False` (tc form).
    ///
    /// From `hab : Nat.le (succ a) b` and `hba : Nat.lt b a`, obtain
    /// `Nat.le b a` via `Nat.le_of_lt b a hba`, then
    /// `Nat.le_trans (succ a) b a hab (Nat.le_of_lt …) : Nat.le (succ a) a ≡
    /// Nat.lt a a`, contradicted by `Nat.lt_irrefl a`.
    fn register_nat_lt_asymm_proof(&mut self, c: &NatTotalityConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_asymm");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        // Match the legacy Axiom's raw `Nat.lt` shape (defeq to the typeclass
        // form, which the proof term also satisfies).
        let hab_type = c.lt_named(a.clone(), bb.clone());
        let (hab_id, hab) = b.fresh_local(hab_type.clone());
        let hba_type = c.lt_named(bb.clone(), a.clone());
        let (hba_id, hba) = b.fresh_local(hba_type.clone());

        // Type: ∀ a b, Nat.lt a b → Nat.lt b a → False
        let type_ = {
            let e = b.mk_pi(
                hba_id,
                BinderInfo::Default,
                hba_type.clone(),
                c.false_const.clone(),
            );
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_type.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let succ_a = c.succ_of(a.clone());
            // Nat.le_of_lt b a hba : Nat.le b a
            let le_ba = c.le_of_lt(bb.clone(), a.clone(), hba.clone());
            // Nat.le_trans (succ a) b a hab le_ba : Nat.le (succ a) a ≡ Nat.lt a a
            let lt_aa = c.le_trans(succ_a, bb.clone(), a.clone(), hab.clone(), le_ba);
            // Nat.lt_irrefl a lt_aa : False
            let body = c.lt_irrefl(a.clone(), lt_aa);
            let e = b.mk_lam(hba_id, BinderInfo::Default, hba_type, body);
            let e = b.mk_lam(hab_id, BinderInfo::Default, hab_type, e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked term; depends only on the constructive
        // `Nat.le_of_lt`, `Nat.le_trans`, `Nat.lt_irrefl`. Replaces the legacy
        // `Declaration::Axiom` in `order.rs::init_nat_lt_asymm`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.lt_of_le_of_ne : ∀ a b, Nat.le a b → (Eq a b → False) → Nat.lt a b`
    /// (tc form).
    ///
    /// `Or.rec` on `Nat.lt_or_eq_of_le a b hle : Or (Nat.lt a b) (Eq a b)`:
    /// - `Or.inl (h : a < b)`: return `h`.
    /// - `Or.inr (h : a = b)`: `hne h : False` → `False.elim`.
    fn register_nat_lt_of_le_of_ne_proof(&mut self, c: &NatTotalityConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.lt_of_le_of_ne");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let hle_type = nat_le_tc(a.clone(), bb.clone());
        let (hle_id, hle) = b.fresh_local(hle_type.clone());
        let eq_ab = c.eq_of(a.clone(), bb.clone());
        let ne_type = Expr::pi(BinderInfo::Default, eq_ab.clone(), c.false_const.clone());
        let (hne_id, hne) = b.fresh_local(ne_type.clone());

        let goal = nat_lt_tc(a.clone(), bb.clone());

        // Type: ∀ a b, Nat.le a b → (Eq a b → False) → Nat.lt a b
        let type_ = {
            let e = b.mk_pi(hne_id, BinderInfo::Default, ne_type.clone(), goal.clone());
            let e = b.mk_pi(hle_id, BinderInfo::Default, hle_type.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // Or.rec over Nat.lt_or_eq_of_le a b hle : Or (Nat.lt a b) (Eq a b).
        let src_left = c.lt_raw(a.clone(), bb.clone()); // Nat.le (succ a) b ≡ Nat.lt a b
        let src_right = c.eq_of(a.clone(), bb.clone());

        let or_motive = {
            let mut om = EnvDeclBuilder::child_of(&b);
            let or_ab = c.or_of(src_left.clone(), src_right.clone());
            let (hh_id, _hh) = om.fresh_local(or_ab.clone());
            let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ab, goal.clone());
            om.finish_child(lam)
        };
        let case_inl = {
            let mut ic = EnvDeclBuilder::child_of(&b);
            let (h_id, h) = ic.fresh_local(src_left.clone());
            // h : Nat.lt a b (raw), goal Nat.lt a b (tc) — defeq.
            let lam = ic.mk_lam(h_id, BinderInfo::Default, src_left.clone(), h);
            ic.finish_child(lam)
        };
        let case_inr = {
            let mut rc = EnvDeclBuilder::child_of(&b);
            let (h_id, h) = rc.fresh_local(src_right.clone());
            let absurd = Expr::app(hne.clone(), h);
            let body = c.false_elim(goal.clone(), absurd);
            let lam = rc.mk_lam(h_id, BinderInfo::Default, src_right.clone(), body);
            rc.finish_child(lam)
        };

        let value = {
            let major = Expr::apps(c.lt_or_eq_thm.clone(), [a.clone(), bb.clone(), hle.clone()]);
            let or_rec_app = Expr::apps(
                c.or_rec.clone(),
                [src_left, src_right, or_motive, case_inl, case_inr, major],
            );
            let e = b.mk_lam(hne_id, BinderInfo::Default, ne_type, or_rec_app);
            let e = b.mk_lam(hle_id, BinderInfo::Default, hle_type, e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Or.rec` term; depends only on the
        // constructive `Nat.lt_or_eq_of_le` and `False.elim`. Replaces the
        // legacy `Declaration::Axiom` in
        // `order_lemmas.rs::init_nat_lt_of_le_of_ne`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn build_env() -> Environment {
        let mut env = Environment::new();
        env.init_nat_totality_proofs()
            .expect("Nat totality proofs register");
        env
    }

    /// Every demoted target plus the prerequisite is a constructive Theorem,
    /// type-checks, and has an empty domain-axiom closure.
    #[test]
    fn test_nat_totality_family_constructive() {
        let env = build_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for target in [
            "Nat.lt_or_eq_of_le",
            "Nat.le_total",
            "Nat.lt_trichotomy",
            "Nat.not_lt",
            "Nat.not_le",
            "Nat.lt_asymm",
            "Nat.lt_of_le_of_ne",
        ] {
            let info = env
                .get_const(&Name::from_string(target))
                .unwrap_or_else(|| panic!("{target} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{target} must be a Theorem, not an Axiom"
            );
            assert!(info.value.is_some(), "{target} must retain its proof value");

            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(target), vec![]))
                .unwrap_or_else(|e| panic!("{target} should type-check: {e:?}"));

            let deps = env
                .axiom_deps(&Name::from_string(target))
                .unwrap_or_else(|| panic!("{target} axiom_deps should compute"));
            assert!(
                deps.is_empty(),
                "{target} must have an empty domain-axiom closure, got {deps:?}"
            );

            assert_eq!(
                env.proof_quality(&Name::from_string(target))
                    .unwrap_or_else(|| panic!("{target} proof quality should compute")),
                ProofQuality::Constructive,
                "{target} must be Constructive"
            );
        }
    }

    /// MB milestone-1 (BitVec→CIC, Tier-0): the kernel core of an 8-bit `bvult`
    /// antisymmetry refutation. A QF_BV obligation `(bvult a b) ∧ (bvult b a)`
    /// reconstructs — over the BitVec-as-Nat carrier — to the closed CIC term
    /// `@Nat.lt_asymm a b h0 h1 : False`, with `h0 : Nat.lt a b` and
    /// `h1 : Nat.lt b a`. The kernel accepts it, and it carries ZERO trusted
    /// axioms: `Nat.lt_asymm` resolves to the constructive Theorem (not the
    /// guarded `Declaration::Axiom` at order.rs:517-522), whose own domain-axiom
    /// closure is empty. This is the zero-new-TCB core that MB builds on — the
    /// refutation needs no bit-blasting bridge at all.
    #[test]
    fn bv_ult_antisymmetry_nat_refutation_kernel_checks() {
        use crate::expr::BinderInfo;
        use crate::tc::LocalContext;

        let mut env = Environment::new();
        env.init_nat_lt_asymm()
            .expect("Nat.lt_asymm must initialize");

        // Load-bearing for the zero-TCB claim: the refutation routes through the
        // CONSTRUCTIVE Theorem form, never the guarded axiom — otherwise the
        // supposedly-Certified term would silently carry an axiom.
        let info = env
            .get_const(&Name::from_string("Nat.lt_asymm"))
            .expect("Nat.lt_asymm registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Nat.lt_asymm must be the constructive Theorem, not the axiom"
        );
        assert!(
            env.axiom_deps(&Name::from_string("Nat.lt_asymm"))
                .expect("axiom_deps should compute")
                .is_empty(),
            "Nat.lt_asymm must have an empty domain-axiom closure (zero new TCB)"
        );

        // 8-bit BitVec carriers a = 3, b = 7 (values mod 2^8). The bvult atoms
        // map to Nat.lt over the carriers; trust-certify owns that (sound,
        // existing-tier) translation. Here we prove the Nat-side refutation.
        let a = Expr::nat_lit(3);
        let b = Expr::nat_lit(7);
        let nat_lt = |x: &Expr, y: &Expr| {
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("Nat.lt"), vec![]), x.clone()),
                y.clone(),
            )
        };

        let mut ctx = LocalContext::new();
        // h0 : Nat.lt a b   (from bvult a b)
        let h0 = ctx.push(Name::from_string("h0"), nat_lt(&a, &b), BinderInfo::Default);
        // h1 : Nat.lt b a   (from bvult b a)
        let h1 = ctx.push(Name::from_string("h1"), nat_lt(&b, &a), BinderInfo::Default);

        // @Nat.lt_asymm a b h0 h1 : False
        let term = Expr::apps(
            Expr::const_(Name::from_string("Nat.lt_asymm"), vec![]),
            [a, b, Expr::fvar(h0), Expr::fvar(h1)],
        );
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        let tc = TypeChecker::with_context(&env, ctx);
        tc.check_type(&term, &false_const).expect(
            "the bvult-antisymmetry refutation must kernel-check to False (zero trusted axioms)",
        );
    }

    /// Re-running registration is a no-op (idempotent).
    #[test]
    fn test_nat_totality_idempotent() {
        let mut env = Environment::new();
        env.init_nat_totality_proofs().expect("first registration");
        env.init_nat_totality_proofs()
            .expect("idempotent re-registration");
        assert_eq!(
            env.get_const(&Name::from_string("Nat.le_total"))
                .expect("Nat.le_total present")
                .kind,
            ConstantKind::Theorem
        );
    }
}
