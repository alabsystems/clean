// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Computation rules for `Nat.min` — the row that made the ORDER lemmas
//! usable.
//!
//! `Nat.min_le_left` / `Nat.min_le_right` / `Nat.le_min` have been present for
//! a long time, but with no way to *compute* a `Nat.min` they cannot finish a
//! proof: z4's `saturate_sound` had to carry a local `satmin` for exactly this
//! reason, and z4's own `PBFinal.lean` fails on it. This module adds:
//!
//! ```text
//! Nat.min_eq_left  : ∀ {a b : Nat}, a ≤ b → min a b = a
//! Nat.min_eq_right : ∀ {a b : Nat}, b ≤ a → min a b = b
//! Nat.min_def      : ∀ {n m : Nat}, min n m = if n ≤ m then n else m
//! ```
//!
//! Each statement is pinned Lean v4.30.0-rc2's exactly: implicit arguments,
//! `min` as `@Min.min Nat instMinNat`, `≤` as `@LE.le Nat instLENat`, and
//! `min_def`'s decision procedure `Nat.decLe n m` (not the instance
//! `instDecidableNatLe`, which unfolds to it). Until 2026-09-30 they were
//! stated with explicit arguments over the bare `Nat.min` / `Nat.le`; the
//! proofs below are unchanged and still work over the bare functions, which
//! the notation δ-reduces to.
//!
//! # Why a bridging lemma, and not a reshaped `Nat.min`
//!
//! `Nat.min a b` is `Nat.ble`-shaped here —
//! `@Bool.rec (fun _ => Nat) b a (Nat.ble a b)` (`order_ord.rs`) — so
//! `Nat.min a b = if a ≤ b then a else b` is NOT `rfl`: the two sides are
//! headed by `Bool.rec` and `Decidable.rec` respectively, and the checker says
//! so (`rigid head/arity mismatch: Bool.rec vs Decidable.rec`).
//!
//! Reshaping `Nat.min` to an `ite` was considered and REJECTED, for three
//! measured reasons:
//!
//! 1. It is not a local edit. `Nat.min` sits in `init_nat_minmax`, which runs
//!    long before `Decidable`/`ite`/`Nat.decLe` are seeded; making it
//!    `ite`-shaped would drag the whole decidability cluster into an early
//!    prelude phase, and `Nat.decLe` itself is built FROM `Nat.ble`.
//! 2. Every existing `Nat.min`/`Nat.max` proof (`order_lemmas_minmax_proofs.rs`,
//!    the `Int` min/max family, the NN-verify and ULP lemmas) is written
//!    against the `Bool.rec` shape and reduces by `Nat.ble`'s ι-rules. A
//!    reshape re-opens all of them.
//! 3. `ite`-shaped is not more computable: `ite` δ-unfolds to
//!    `Decidable.casesOn`, and the `Decidable (Nat.le a b)` instance is itself
//!    a `Bool.rec` on `Nat.ble a b`. The ground reduction path is the same
//!    length; only the head constant differs.
//!
//! So the bridge is the fix, and `Nat.min_def` is the bridge stated once. Note
//! that `min_eq_left`/`min_eq_right` — not `min_def` — are what a proof
//! actually cites; `min_def` exists for parity with Lean 4 and for `simp`.
//!
//! # Proof shapes
//!
//! * `min_eq_left`: `congrArg` the `Bool.rec` body along
//!   `Nat.ble_eq_true_of_le a b h : Nat.ble a b = true`; the right-hand side
//!   ι-reduces to `a`.
//! * `min_eq_right`: `Bool.rec` on `Nat.ble a b` with the equation threaded
//!   through the motive (the `Nat.decLe` dispatcher's own trick). The `false`
//!   leaf is `rfl`; the `true` leaf gets `Nat.le a b` from
//!   `Nat.le_of_ble_eq_true` and closes with `Nat.le_antisymm`.
//! * `min_def`: `Decidable.rec` on the very instance the `ite` carries. The
//!   `isTrue` leaf is `min_eq_left`; the `isFalse` leaf runs the same threaded
//!   `Bool.rec`, refuting its `true` branch with the negation in hand.
//!
//! No `sorry`, no new axiom: only `Bool`/`Decidable` recursors, `Eq`
//! built-ins, `congrArg`, `False.elim` and the already-constructive
//! `Nat.ble_eq_true_of_le`, `Nat.le_of_ble_eq_true`, `Nat.le_antisymm`.

use super::decl_builder::EnvDeclBuilder;
use super::lean_nat_spelling::LeanNat;
use super::nat_floor_order_lemmas::FloorConsts;
use super::order::nat_le_tc;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// The `Bool`- and `Decidable`-side constants the `min` bridge needs, on top
/// of [`FloorConsts`].
struct MinConsts {
    bool_ty: Expr,
    btrue: Expr,
    bfalse: Expr,
    /// `Bool.rec.{0}` (Prop motives) and `Bool.rec.{1}` (`Nat`-valued motives).
    bool_rec0: Expr,
    bool_rec1: Expr,
    /// `fun _ : Bool => Nat` — the motive `Nat.min`'s own body uses.
    bool_nat_motive: Expr,
    ble: Expr,
    min: Expr,
    /// `@Eq.{1}` / `@Eq.refl.{1}` at `Bool`.
    eq_bool: Expr,
    eq_refl_bool: Expr,
    /// `@congrArg.{1,1} Bool Nat`.
    congr_arg_bool_nat: Expr,
}

impl MinConsts {
    fn new() -> Self {
        let n = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let l1 = Level::succ(Level::zero());
        let bool_ty = n("Bool");
        let nat = n("Nat");
        Self {
            bool_nat_motive: Expr::lam(BinderInfo::Default, bool_ty.clone(), nat),
            btrue: n("Bool.true"),
            bfalse: n("Bool.false"),
            bool_rec0: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            bool_rec1: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            ble: n("Nat.ble"),
            min: n("Nat.min"),
            eq_bool: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl_bool: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            congr_arg_bool_nat: Expr::apps(
                Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
                [
                    bool_ty.clone(),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ],
            ),
            bool_ty,
        }
    }

    /// `@Nat.ble a b : Bool`
    fn ble_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.ble.clone(), [a, b])
    }
    /// `@Nat.min a b : Nat`
    fn min_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.min.clone(), [a, b])
    }
    /// `@Bool.rec.{1} (fun _ => Nat) b a x` — `Nat.min a b`'s body, open in
    /// the boolean test. At `x := Nat.ble a b` it IS `Nat.min a b` (δ); at
    /// `Bool.true` it ι-reduces to `a`, at `Bool.false` to `b`.
    fn branch_at(&self, a: Expr, b: Expr, x: Expr) -> Expr {
        Expr::apps(
            self.bool_rec1.clone(),
            [self.bool_nat_motive.clone(), b, a, x],
        )
    }
    /// `@Eq.{1} Bool lhs rhs : Prop`
    fn eq_bool_of(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq_bool.clone(), [self.bool_ty.clone(), lhs, rhs])
    }
    /// `@Eq.refl.{1} Bool x`
    fn refl_bool(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl_bool.clone(), [self.bool_ty.clone(), x])
    }
}

/// `dom → cod`, a non-dependent arrow (see `nat_floor_order_lemmas::arrow`).
fn arrow(dom: Expr, cod: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, dom, cod)
}

impl Environment {
    /// Register `Nat.min_eq_left`, `Nat.min_eq_right` and `Nat.min_def` as
    /// kernel-checked theorems. Idempotent per-lemma.
    ///
    /// # Errors
    ///
    /// Propagates any `EnvError` from a dependency initializer or from
    /// `add_decl`'s kernel check of a proof term.
    pub(crate) fn init_nat_floor_min_lemmas(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode gate — `Nat.min` and `Nat.ble` are themselves
        // import-gated seeds (`order_ord.rs`, `order_nat_cmp.rs`), and
        // `instDecidableNatLe` is suppressed with them. The genuine Lean
        // lemmas import through the checked path instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }

        self.init_nat()?;
        self.init_eq()?;
        self.init_le()?;
        self.init_bool()?;
        self.init_true_false()?;
        self.init_nat_cmp()?; // Nat.ble
        self.init_nat_minmax()?; // Nat.min
        self.register_nat_ble_le_lemmas()?; // the Nat.ble ↔ Nat.le bridge
        self.register_nat_le_trans_proof()?;
        self.register_nat_lt_irrefl_theorem()?;
        self.register_nat_le_antisymm_proof()?; // Nat.le_antisymm
        self.init_decidable()?;
        self.init_ite()?;
        self.init_nat_decidable_ord()?; // instDecidableNatLe := Nat.decLe
        self.init_nat_minmax_inst()?; // instMinNat, the `min` Lean states over

        let c = FloorConsts::new();
        let m = MinConsts::new();
        self.register_nat_min_eq_left(&c, &m)?;
        self.register_nat_min_eq_right(&c, &m)?;
        self.register_nat_min_def(&c, &m)?;
        Ok(())
    }

    /// `theorem Nat.min_eq_left (a b : Nat) (h : Nat.le a b)
    ///   : @Eq Nat (Nat.min a b) a`
    fn register_nat_min_eq_left(&mut self, c: &FloorConsts, m: &MinConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.min_eq_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ble_eq_true_of_le = FloorConsts::const_("Nat.ble_eq_true_of_le");

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bv_id, bv) = b.fresh_local(c.nat.clone());
        let h_ty = LeanNat::le(a.clone(), bv.clone());
        let (h_id, h) = b.fresh_local(h_ty.clone());

        let type_ = {
            let concl = LeanNat::eq(LeanNat::min(a.clone(), bv.clone()), a.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty.clone(), concl);
            let e = b.mk_pi(bv_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        // f : fun (x : Bool) => @Bool.rec (fun _ => Nat) b a x
        let f = {
            let mut fb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = fb.fresh_local(m.bool_ty.clone());
            let body = m.branch_at(a.clone(), bv.clone(), x);
            fb.finish_child(fb.mk_lam(x_id, BinderInfo::Default, m.bool_ty.clone(), body))
        };

        let value = {
            // hb : @Eq Bool (Nat.ble a b) Bool.true
            let hb = Expr::apps(ble_eq_true_of_le, [a.clone(), bv.clone(), h.clone()]);
            // congrArg f hb : f (Nat.ble a b) = f Bool.true, i.e. Nat.min a b = a
            let body = Expr::apps(
                m.congr_arg_bool_nat.clone(),
                [m.ble_of(a.clone(), bv.clone()), m.btrue.clone(), f, hb],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = b.mk_lam(bv_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem Nat.min_eq_right (a b : Nat) (h : Nat.le b a)
    ///   : @Eq Nat (Nat.min a b) b`
    ///
    /// `b ≤ a` does NOT decide `Nat.ble a b` (they can be equal), so this is a
    /// genuine case split: the `false` leaf is `rfl` and the `true` leaf
    /// derives `a = b` by antisymmetry.
    fn register_nat_min_eq_right(
        &mut self,
        c: &FloorConsts,
        m: &MinConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.min_eq_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let le_of_ble_eq_true = FloorConsts::const_("Nat.le_of_ble_eq_true");
        let le_antisymm = FloorConsts::const_("Nat.le_antisymm");

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bv_id, bv) = b.fresh_local(c.nat.clone());
        let h_ty = LeanNat::le(bv.clone(), a.clone());
        let (h_id, h) = b.fresh_local(h_ty.clone());

        let type_ = {
            let concl = LeanNat::eq(LeanNat::min(a.clone(), bv.clone()), bv.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty.clone(), concl);
            let e = b.mk_pi(bv_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        let test = m.ble_of(a.clone(), bv.clone());

        // motive : fun (x : Bool) =>
        //   @Eq Bool (Nat.ble a b) x → @Eq Nat (branch_at x) b
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = mb.fresh_local(m.bool_ty.clone());
            let hyp = m.eq_bool_of(test.clone(), x.clone());
            let concl = c.eq_of(m.branch_at(a.clone(), bv.clone(), x), bv.clone());
            let pi = arrow(hyp, concl);
            mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, m.bool_ty.clone(), pi))
        };

        // false leaf: `branch_at Bool.false ≡ b`.
        let fmin = {
            let mut fb = EnvDeclBuilder::child_of(&b);
            let hyp = m.eq_bool_of(test.clone(), m.bfalse.clone());
            let (he_id, _he) = fb.fresh_local(hyp.clone());
            let body = c.refl(bv.clone());
            fb.finish_child(fb.mk_lam(he_id, BinderInfo::Default, hyp, body))
        };

        // true leaf: `branch_at Bool.true ≡ a`, and `a ≤ b` + `b ≤ a` gives `a = b`.
        let tmin = {
            let mut tb = EnvDeclBuilder::child_of(&b);
            let hyp = m.eq_bool_of(test.clone(), m.btrue.clone());
            let (he_id, he) = tb.fresh_local(hyp.clone());
            let a_le_b = Expr::apps(le_of_ble_eq_true, [a.clone(), bv.clone(), he]);
            let body = Expr::apps(le_antisymm, [a.clone(), bv.clone(), a_le_b, h.clone()]);
            tb.finish_child(tb.mk_lam(he_id, BinderInfo::Default, hyp, body))
        };

        let value = {
            let rec = Expr::apps(m.bool_rec0.clone(), [motive, fmin, tmin, test.clone()]);
            let body = Expr::app(rec, m.refl_bool(test));
            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = b.mk_lam(bv_id, BinderInfo::Implicit, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `theorem Nat.min_def {n m : Nat}
    ///   : @Eq Nat (@Min.min Nat instMinNat n m)
    ///       (@ite Nat (@LE.le Nat instLENat n m) (Nat.decLe n m) n m)`
    ///
    /// Lean's statement, exactly (pinned v4.30.0-rc2). The proof eliminates
    /// the checked alias `instDecidableNatLe a b`, which unfolds to the
    /// registered `Nat.decLe a b` instance, over the bare `Nat.min`.
    fn register_nat_min_def(&mut self, c: &FloorConsts, m: &MinConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.min_def");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let le_of_ble_eq_true = FloorConsts::const_("Nat.le_of_ble_eq_true");
        let min_eq_left = FloorConsts::const_("Nat.min_eq_left");
        let inst_dec_le = FloorConsts::const_("instDecidableNatLe");
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![Level::zero()]);
        let ite = Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]);
        let decidable = FloorConsts::const_("Decidable");
        let false_c = FloorConsts::const_("False");

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bv_id, bv) = b.fresh_local(c.nat.clone());

        // `p` is the PROPOSITION the elaborated `if a ≤ b` carries.
        let p = nat_le_tc(a.clone(), bv.clone());
        let inst = Expr::apps(inst_dec_le, [a.clone(), bv.clone()]);
        let ite_of = |d: Expr| {
            Expr::apps(
                ite.clone(),
                [c.nat.clone(), p.clone(), d, a.clone(), bv.clone()],
            )
        };

        let type_ = {
            let dec_le = Expr::apps(FloorConsts::const_("Nat.decLe"), [a.clone(), bv.clone()]);
            let concl = LeanNat::eq(LeanNat::min(a.clone(), bv.clone()), ite_of(dec_le));
            let e = b.mk_pi(bv_id, BinderInfo::Implicit, c.nat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

        // motive : fun (d : Decidable p) => @Eq Nat (Nat.min a b) (ite … d a b)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let dec_p = Expr::app(decidable.clone(), p.clone());
            let (d_id, d) = mb.fresh_local(dec_p.clone());
            let body = c.eq_of(m.min_of(a.clone(), bv.clone()), ite_of(d));
            mb.finish_child(mb.mk_lam(d_id, BinderInfo::Default, dec_p, body))
        };

        // isFalse leaf: `ite … (Decidable.isFalse hn) a b ≡ b`, so the goal is
        // `Nat.min a b = b` — proved by the same threaded `Bool.rec`, with the
        // `true` branch refuted by `hn`.
        let fmin = {
            let mut fb = EnvDeclBuilder::child_of(&b);
            let hn_ty = arrow(p.clone(), false_c.clone());
            let (hn_id, hn) = fb.fresh_local(hn_ty.clone());
            let test = m.ble_of(a.clone(), bv.clone());

            let inner_motive = {
                let mut ib = EnvDeclBuilder::child_of(&fb);
                let (x_id, x) = ib.fresh_local(m.bool_ty.clone());
                let hyp = m.eq_bool_of(test.clone(), x.clone());
                let concl = c.eq_of(m.branch_at(a.clone(), bv.clone(), x), bv.clone());
                let pi = arrow(hyp, concl);
                ib.finish_child(ib.mk_lam(x_id, BinderInfo::Default, m.bool_ty.clone(), pi))
            };
            let inner_false = {
                let mut ifb = EnvDeclBuilder::child_of(&fb);
                let hyp = m.eq_bool_of(test.clone(), m.bfalse.clone());
                let (he_id, _he) = ifb.fresh_local(hyp.clone());
                let body = c.refl(bv.clone());
                ifb.finish_child(ifb.mk_lam(he_id, BinderInfo::Default, hyp, body))
            };
            let inner_true = {
                let mut itb = EnvDeclBuilder::child_of(&fb);
                let hyp = m.eq_bool_of(test.clone(), m.btrue.clone());
                let (he_id, he) = itb.fresh_local(hyp.clone());
                let a_le_b = Expr::apps(le_of_ble_eq_true.clone(), [a.clone(), bv.clone(), he]);
                let falsity = Expr::app(hn.clone(), a_le_b);
                let goal = c.eq_of(
                    m.branch_at(a.clone(), bv.clone(), m.btrue.clone()),
                    bv.clone(),
                );
                let body = c.false_elim(goal, falsity);
                itb.finish_child(itb.mk_lam(he_id, BinderInfo::Default, hyp, body))
            };
            let rec = Expr::apps(
                m.bool_rec0.clone(),
                [inner_motive, inner_false, inner_true, test.clone()],
            );
            let body = Expr::app(rec, m.refl_bool(test));
            fb.finish_child(fb.mk_lam(hn_id, BinderInfo::Default, hn_ty, body))
        };

        // isTrue leaf: `ite … (Decidable.isTrue hp) a b ≡ a`, which is
        // `Nat.min_eq_left` (its raw `Nat.le a b` hypothesis is def-eq to `p`).
        let tmin = {
            let mut tb = EnvDeclBuilder::child_of(&b);
            let (hp_id, hp) = tb.fresh_local(p.clone());
            let body = Expr::apps(min_eq_left, [a.clone(), bv.clone(), hp]);
            tb.finish_child(tb.mk_lam(hp_id, BinderInfo::Default, p.clone(), body))
        };

        let value = {
            let body = Expr::apps(dec_rec, [p.clone(), motive, fmin, tmin, inst]);
            let e = b.mk_lam(bv_id, BinderInfo::Implicit, c.nat.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };

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
    use crate::env::ConstantKind;
    use crate::tc::TypeChecker;

    fn numeral(c: &FloorConsts, k: u32) -> Expr {
        let mut e = c.zero.clone();
        for _ in 0..k {
            e = c.succ_of(e);
        }
        e
    }

    /// All three `min` computation rules are in the DEFAULT prelude, are
    /// `Declaration::Theorem`s that kept their proof values, and rest on no
    /// axiom.
    #[test]
    fn nat_min_computation_rules_are_axiom_free_theorems_in_the_prelude() {
        let env = Environment::with_prelude();
        for short in ["Nat.min_eq_left", "Nat.min_eq_right", "Nat.min_def"] {
            let info = env
                .get_const(&Name::from_string(short))
                .unwrap_or_else(|| panic!("{short} must be in the default prelude"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{short} must be a Theorem"
            );
            assert!(info.value.is_some(), "{short} must retain its proof value");
            let deps = env
                .axiom_deps(&Name::from_string(short))
                .unwrap_or_else(|| panic!("{short}: axiom_deps None"));
            assert!(deps.is_empty(), "{short} rests on {deps:?}");
        }
    }

    /// ANTI-VACUITY / CONTROL, in one test: `Nat.min_def`'s own statement is
    /// NOT closed by `rfl` (the `Bool.rec` vs `Decidable.rec` rigid mismatch
    /// this module exists for), and IS closed by `Nat.min_def`.
    ///
    /// If the first half ever starts passing, `Nat.min` has been reshaped and
    /// this module is dead weight — that is exactly what this arm is here to
    /// catch.
    #[test]
    fn nat_min_def_is_load_bearing_not_rfl() {
        let env = Environment::with_prelude();
        let c = FloorConsts::new();
        let m = MinConsts::new();
        let stmt = env
            .get_const(&Name::from_string("Nat.min_def"))
            .expect("Nat.min_def must be registered")
            .type_
            .clone();
        let tc = TypeChecker::with_mode(&env, env.mode());

        // fun (a b : Nat) => @Eq.refl Nat (Nat.min a b)
        let by_rfl = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nat.clone());
            let (bv_id, bv) = b.fresh_local(c.nat.clone());
            let body = c.refl(m.min_of(a, bv));
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e))
        };
        assert!(
            tc.check_type(&by_rfl, &stmt).is_err(),
            "`Nat.min a b = if a <= b then a else b` must NOT be rfl here — \
             Nat.min is Nat.ble-shaped, the ite is Decidable-shaped"
        );

        tc.check_type(&FloorConsts::const_("Nat.min_def"), &stmt)
            .expect("Nat.min_def must prove its own statement");
    }

    /// ANTI-VACUITY: ground instances of both computation rules, at a pair
    /// where the two disagree (`min 2 5 = 2`, `min 5 2 = 2`).
    #[test]
    fn nat_min_eq_ground_instances_check() {
        let env = Environment::with_prelude();
        let c = FloorConsts::new();
        let m = MinConsts::new();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let n2 = numeral(&c, 2);
        let n5 = numeral(&c, 5);
        // 2 <= 5 : Nat.le.step 2 4 (Nat.le.step 2 3 (Nat.le.step 2 2 (Nat.le.refl 2)))
        let le_refl = FloorConsts::const_("Nat.le.refl");
        let le_step = FloorConsts::const_("Nat.le.step");
        let mut h = Expr::app(le_refl, n2.clone());
        for k in 2..5 {
            h = Expr::apps(le_step.clone(), [n2.clone(), numeral(&c, k), h]);
        }

        // Nat.min_eq_left 2 5 (2<=5) : Nat.min 2 5 = 2
        let stmt_l = c.eq_of(m.min_of(n2.clone(), n5.clone()), n2.clone());
        let proof_l = Expr::apps(
            FloorConsts::const_("Nat.min_eq_left"),
            [n2.clone(), n5.clone(), h.clone()],
        );
        tc.check_type(&proof_l, &stmt_l)
            .expect("Nat.min_eq_left 2 5 must check against `Nat.min 2 5 = 2`");

        // Nat.min_eq_right 5 2 (2<=5) : Nat.min 5 2 = 2
        let stmt_r = c.eq_of(m.min_of(n5.clone(), n2.clone()), n2.clone());
        let proof_r = Expr::apps(FloorConsts::const_("Nat.min_eq_right"), [n5, n2, h]);
        tc.check_type(&proof_r, &stmt_r)
            .expect("Nat.min_eq_right 5 2 must check against `Nat.min 5 2 = 2`");
    }

    /// The import-verification prelude does NOT gain these: `Nat.min`,
    /// `Nat.ble` and `instDecidableNatLe` are all import-gated seeds.
    #[test]
    fn import_prelude_withholds_the_min_rules() {
        let env = Environment::try_with_prelude_for_import().expect("import prelude must build");
        for short in ["Nat.min_eq_left", "Nat.min_eq_right", "Nat.min_def"] {
            assert!(
                env.get_const(&Name::from_string(short)).is_none(),
                "{short} must NOT be seeded in the import prelude"
            );
        }
    }
}
