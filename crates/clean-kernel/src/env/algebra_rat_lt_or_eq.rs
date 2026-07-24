// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rational order trichotomy splitter `Rat.lt_or_eq_of_le`.
//!
//! # Why this module exists
//!
//! The final scalar core of the verified per-coordinate squared dual-HC chain
//! (`GLUE-5` of the spectral-glue assembly) cancels a common left factor `P²`
//! across a `≤`. The cancellation lemma `Rat.le_of_mul_le_mul_left_pos` requires
//! a STRICTLY POSITIVE factor; from a nonnegativity fact `0 ≤ P` one needs the
//! case split `0 < P ∨ P = 0` (when `P = 0` both sides are `0` and the bound is
//! trivial; when `0 < P` the factor cancels). The forward / strict order lemmas
//! and `Rat.le_total` / `Rat.le_antisymm` / `Rat.lt_iff_le_not_le` exist on the
//! branch, but the order trichotomy splitter is absent. This module lands it as a
//! clean, reusable, general-purpose `Rat` lemma:
//!
//! ```text
//! Rat.lt_or_eq_of_le :
//!   ∀ (a b : Rat), Rat.le a b → Or (Rat.lt a b) (Eq Rat a b)
//! ```
//!
//! # Proof shape (constructive, decidability of `Rat.ble`)
//!
//! Given `h : a ≤ b`, eliminate the boolean `Rat.ble b a` with a `Bool.rec`
//! whose motive carries the discriminant equation
//! `m := fun (v : Bool) => Eq Bool (Rat.ble b a) v → Or (Rat.lt a b) (Eq a b)`,
//! seeded by `Eq.refl Bool (Rat.ble b a)`:
//!
//!   - `Rat.ble b a = false` (`heq`): then `b ≤ a` is impossible, so `a < b`.
//!     `hnotba : Not (b ≤ a) := fun hba =>`
//!       `Bool.noConfusion (Eq.trans (Eq.symm (Rat.ble_eq_true_of_le b a hba)) heq)`
//!       (`Rat.ble b a = true` contradicts `Rat.ble b a = false` ⇒ `true = false`).
//!     `a < b := Iff.mpr (Rat.lt_iff_le_not_le a b) (And.intro h hnotba)`; `Or.inl`.
//!   - `Rat.ble b a = true` (`heq`): `b ≤ a := Rat.le_of_ble_eq_true b a heq`, so
//!     `a = b := Rat.le_antisymm a b h hba`; `Or.inr`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (every leaf — `Rat.ble_eq_true_of_le`, `Rat.le_of_ble_eq_true`,
//! `Rat.lt_iff_le_not_le`, `Rat.le_antisymm`, `Bool.noConfusion`, `Bool.rec`,
//! `Iff.mpr` / `And.intro` / `Or.inl` / `Or.inr` / `Eq` built-ins — is
//! foundational-only). NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `Rat.lt_or_eq_of_le`.
struct LtOrEqConsts {
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    bool_false: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_ble: Expr,
    ble_eq_true_of_le: Expr,
    le_of_ble_eq_true: Expr,
    lt_iff_le_not_le: Expr,
    le_antisymm: Expr,
    not_c: Expr,
    false_c: Expr,
    and_c: Expr,
    and_intro: Expr,
    or_c: Expr,
    or_inl: Expr,
    or_inr: Expr,
    iff_mpr: Expr,
    no_confusion: Expr,
    bool_rec: Expr,
    eq_bool: Expr,
    eq_rat: Expr,
    eq_refl_bool: Expr,
    eq_symm_bool: Expr,
    eq_trans_bool: Expr,
}

impl LtOrEqConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_ble: k("Rat.ble"),
            ble_eq_true_of_le: k("Rat.ble_eq_true_of_le"),
            le_of_ble_eq_true: k("Rat.le_of_ble_eq_true"),
            lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            le_antisymm: k("Rat.le_antisymm"),
            not_c: k("Not"),
            false_c: k("False"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            or_c: k("Or"),
            or_inl: k("Or.inl"),
            or_inr: k("Or.inr"),
            iff_mpr: k("Iff.mpr"),
            // `Bool.noConfusion` proving a Prop goal (`False`) carries one Sort
            // universe param; here the motive lands in `Prop = Sort 0`.
            no_confusion: Expr::const_(Name::from_string("Bool.noConfusion"), vec![Level::zero()]),
            // `Bool.rec` into a Prop motive carries no extra universe in this
            // kernel's encoding (mirrors the minmax Prop discriminator).
            bool_rec: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            eq_bool: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl_bool: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm_bool: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans_bool: Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
        }
    }

    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    /// `Rat.ble a b : Bool`.
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_ble.clone(), [a, b])
    }
    /// `Not P`.
    fn not_(&self, p: Expr) -> Expr {
        Expr::app(self.not_c.clone(), p)
    }
    /// `And P Q`.
    fn and_(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    /// `Or P Q`.
    fn or_(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.or_c.clone(), [p, q])
    }
    /// `Eq Bool x y`.
    fn eqb(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq_bool.clone(), [self.bool_.clone(), x, y])
    }
    /// `Eq Rat x y`.
    fn eqr(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), x, y])
    }
    /// `@Eq.refl Bool v`.
    fn refl_bool(&self, v: Expr) -> Expr {
        Expr::apps(self.eq_refl_bool.clone(), [self.bool_.clone(), v])
    }
    /// `@Eq.symm Bool x y h`.
    fn symm_bool(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm_bool.clone(), [self.bool_.clone(), x, y, h])
    }
    /// `@Eq.trans Bool x y z h1 h2`.
    fn trans_bool(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans_bool.clone(),
            [self.bool_.clone(), x, y, z, h1, h2],
        )
    }
    /// `Rat.ble_eq_true_of_le a b (h : a ≤ b) : Eq Bool (Rat.ble a b) true`.
    fn ble_true_of_le(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.ble_eq_true_of_le.clone(), [a, b, h])
    }
    /// `Rat.le_of_ble_eq_true a b (h : Rat.ble a b = true) : a ≤ b`.
    fn le_of_ble(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.le_of_ble_eq_true.clone(), [a, b, h])
    }
    /// `Rat.lt_iff_le_not_le a b : Iff (a < b) (And (a ≤ b) (Not (b ≤ a)))`.
    fn lt_iff(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.lt_iff_le_not_le.clone(), [a, b])
    }
    /// `Rat.le_antisymm a b (a≤b)(b≤a) : Eq Rat a b`.
    fn le_antisymm(&self, a: Expr, b: Expr, hab: Expr, hba: Expr) -> Expr {
        Expr::apps(self.le_antisymm.clone(), [a, b, hab, hba])
    }
    /// `@And.intro P Q hp hq`.
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p, q, hp, hq])
    }
    /// `@Or.inl P Q hp`.
    fn or_inl(&self, p: Expr, q: Expr, hp: Expr) -> Expr {
        Expr::apps(self.or_inl.clone(), [p, q, hp])
    }
    /// `@Or.inr P Q hq`.
    fn or_inr(&self, p: Expr, q: Expr, hq: Expr) -> Expr {
        Expr::apps(self.or_inr.clone(), [p, q, hq])
    }
    /// `@Iff.mpr lhs rhs hiff hrhs`.
    fn iff_mpr(&self, lhs: Expr, rhs: Expr, hiff: Expr, hrhs: Expr) -> Expr {
        Expr::apps(self.iff_mpr.clone(), [lhs, rhs, hiff, hrhs])
    }
    /// `@Bool.noConfusion.{0} False x y (h : Eq Bool x y) : False`
    /// (when `x`, `y` are distinct constructors, `noConfusionType` δ-reduces to
    /// `False → False`, so `noConfusion` applied to the contradictory `h` yields
    /// `False`).
    fn no_confusion_false(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.no_confusion.clone(), [self.false_c.clone(), x, y, h])
    }
}

impl Environment {
    /// Register `Rat.lt_or_eq_of_le`. Idempotent; kernel-checked,
    /// `Constructive`, empty domain-axiom closure.
    ///
    /// `∀ a b, a ≤ b → Or (a < b) (a = b)`. See the module docs for the proof.
    pub fn register_rat_lt_or_eq_of_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lt_or_eq_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_and()?;
        self.init_or()?;
        self.init_iff()?;
        self.init_bool()?;
        // Rat.ble, Rat.ble_eq_true_of_le, Rat.le_of_ble_eq_true.
        self.register_rat_minmax_proofs()?;
        // Rat.lt_iff_le_not_le, Rat.le (order surface).
        self.register_rat_order_proofs()?;
        // Rat.le_antisymm.
        self.init_algebra_rat_inv_dyadic()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = LtOrEqConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_lt_or_eq(&c, false),
            value: build_lt_or_eq(&c, true),
        })
    }
}

/// Build the type (`for_value = false`, all binders Pi) or proof value
/// (`for_value = true`, all binders Lam + conclusion replaced by the proof term).
fn build_lt_or_eq(c: &LtOrEqConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());

    let h_ty = c.le(a.clone(), bv.clone()); // a ≤ b
    let lt_ab = c.lt(a.clone(), bv.clone()); // a < b
    let eq_ab = c.eqr(a.clone(), bv.clone()); // a = b
    let goal = c.or_(lt_ab.clone(), eq_ab.clone()); // Or (a<b) (a=b)

    let (h_id, h) = b.fresh_local(h_ty.clone());

    let tail = if for_value {
        build_lt_or_eq_proof(c, &b, &a, &bv, &lt_ab, &eq_ab, &goal, h)
    } else {
        goal
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, h_id, h_ty, tail);
    let e = bind(&b, bv_id, c.rat.clone(), e);
    let e = bind(&b, a_id, c.rat.clone(), e);
    b.finish(e)
}

/// The proof term of `Or (a<b) (a=b)` given `h : a ≤ b`, via `Bool.rec` on
/// `Rat.ble b a` with a discriminant-carrying motive seeded by `Eq.refl`.
#[allow(clippy::too_many_arguments)]
fn build_lt_or_eq_proof(
    c: &LtOrEqConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
    lt_ab: &Expr,
    eq_ab: &Expr,
    goal: &Expr,
    h: Expr, // a ≤ b
) -> Expr {
    let ble_ba = c.ble(bv.clone(), a.clone()); // Rat.ble b a

    // motive : fun (v : Bool) => Eq Bool (Rat.ble b a) v → goal.
    let motive = {
        let mut m = EnvDeclBuilder::child_of(parent);
        let (v_id, v) = m.fresh_local(c.bool_.clone());
        let disc = c.eqb(ble_ba.clone(), v.clone());
        let body = {
            let mut mm = EnvDeclBuilder::child_of(&m);
            let (hd_id, _hd) = mm.fresh_local(disc.clone());
            mm.finish_child(mm.mk_pi(hd_id, BinderInfo::Default, disc.clone(), goal.clone()))
        };
        m.finish_child(m.mk_lam(v_id, BinderInfo::Default, c.bool_.clone(), body))
    };

    // Minor for `Rat.ble b a = false`:
    //   fun (heq : Rat.ble b a = false) => Or.inl (a<b via lt_iff_le_not_le).
    let minor_false = {
        let mut m = EnvDeclBuilder::child_of(parent);
        let disc_f = c.eqb(ble_ba.clone(), c.bool_false.clone());
        let (heq_id, heq) = m.fresh_local(disc_f.clone());

        // hnotba : Not (b ≤ a) := fun (hba : b ≤ a) =>
        //   Bool.noConfusion (trans (symm (ble_eq_true_of_le b a hba)) heq : true = false).
        let le_ba = c.le(bv.clone(), a.clone());
        let hnotba = {
            let mut nb = EnvDeclBuilder::child_of(&m);
            let (hba_id, hba) = nb.fresh_local(le_ba.clone());
            // ble_eq_true_of_le b a hba : Rat.ble b a = true
            let ble_true = c.ble_true_of_le(bv.clone(), a.clone(), hba);
            // symm : true = Rat.ble b a
            let symm_bt = c.symm_bool(ble_ba.clone(), c.bool_true.clone(), ble_true);
            // trans (true = ble) (ble = false) : true = false
            let true_eq_false = c.trans_bool(
                c.bool_true.clone(),
                ble_ba.clone(),
                c.bool_false.clone(),
                symm_bt,
                heq.clone(),
            );
            let false_pf =
                c.no_confusion_false(c.bool_true.clone(), c.bool_false.clone(), true_eq_false);
            nb.finish_child(nb.mk_lam(hba_id, BinderInfo::Default, le_ba.clone(), false_pf))
        };

        // a < b := Iff.mpr (lt_iff a b) (And.intro h hnotba).
        let le_ab = c.le(a.clone(), bv.clone());
        let not_le_ba = c.not_(le_ba.clone());
        let and_pf = c.and_intro(le_ab.clone(), not_le_ba.clone(), h.clone(), hnotba);
        let rhs_and = c.and_(le_ab, not_le_ba);
        let lt_pf = c.iff_mpr(
            lt_ab.clone(),
            rhs_and,
            c.lt_iff(a.clone(), bv.clone()),
            and_pf,
        );
        let inl = c.or_inl(lt_ab.clone(), eq_ab.clone(), lt_pf);
        m.finish_child(m.mk_lam(heq_id, BinderInfo::Default, disc_f, inl))
    };

    // Minor for `Rat.ble b a = true`:
    //   fun (heq : Rat.ble b a = true) => Or.inr (a=b via le_antisymm a b h (le_of_ble b a heq)).
    let minor_true = {
        let mut m = EnvDeclBuilder::child_of(parent);
        let disc_t = c.eqb(ble_ba.clone(), c.bool_true.clone());
        let (heq_id, heq) = m.fresh_local(disc_t.clone());
        // b ≤ a := le_of_ble_eq_true b a heq.
        let hba = c.le_of_ble(bv.clone(), a.clone(), heq);
        // a = b := le_antisymm a b h hba.
        let eq_pf = c.le_antisymm(a.clone(), bv.clone(), h.clone(), hba);
        let inr = c.or_inr(lt_ab.clone(), eq_ab.clone(), eq_pf);
        m.finish_child(m.mk_lam(heq_id, BinderInfo::Default, disc_t, inr))
    };

    // @Bool.rec.{0} motive minor_false minor_true (Rat.ble b a) (Eq.refl Bool (Rat.ble b a)).
    let rec = Expr::apps(
        c.bool_rec.clone(),
        [motive, minor_false, minor_true, ble_ba.clone()],
    );
    Expr::app(rec, c.refl_bool(ble_ba))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_rat_lt_or_eq_of_le()
            .expect("register_rat_lt_or_eq_of_le");
        env.register_rat_lt_or_eq_of_le().expect("idempotent");
        env
    }

    /// The trichotomy splitter is a kernel-checked, `Constructive`, empty-closure
    /// Theorem.
    #[test]
    fn test_rat_lt_or_eq_of_le_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("Rat.lt_or_eq_of_le");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }
}
