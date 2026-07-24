// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive demotions of the *remaining* `Nat.sub` ordering lemmas from
//! `Declaration::Axiom` to kernel-checked `Declaration::Theorem`s with empty
//! domain-axiom closures (#3604, kernel-soundness `Nat.sub`-order vein).
//!
//! The earlier `Nat.sub_le` (and its helper `Nat.pred_le`) were already demoted
//! in `nat_arith_order_proof.rs`. This module covers the four that were still
//! `Declaration::Axiom` stubs in `order_arith.rs::init_nat_sub_ord`:
//!
//! - `Nat.sub_self`         : `∀ a, Eq (a - a) 0`
//! - `Nat.sub_le_sub_right` : `∀ a b c, Nat.le a b → Nat.le (a - c) (b - c)`
//! - `Nat.sub_le_sub_left`  : `∀ a b c, Nat.le b c → Nat.le (a - c) (a - b)`
//! - `Nat.sub_lt`           : `∀ a b, Nat.lt 0 a → Nat.lt 0 b → Nat.lt (a - b) a`
//!
//! Each legacy axiom site in `order_arith.rs` is guarded by a `get_const`
//! check so that once these `Declaration::Theorem`s are registered the legacy
//! `Declaration::Axiom` registration becomes an idempotent no-op; the Theorem
//! form therefore wins on every init path.
//!
//! # Prerequisite lemmas (each itself an empty-closure `Declaration::Theorem`)
//!
//! - `Nat.succ_sub_succ`    : `∀ m n, Eq (Nat.succ m - Nat.succ n) (m - n)`
//! - `Nat.pred_le_pred`     : `∀ a b, Nat.le a b → Nat.le (Nat.pred a) (Nat.pred b)`
//! - `Nat.succ_pred_of_pos` : `∀ a, Nat.lt 0 a → Eq (Nat.succ (Nat.pred a)) a`
//!
//! `Nat.pred_le` is *not* redefined here — it is reused from
//! `nat_arith_order_proof.rs` (already registered on every init path).
//!
//! # Key definitional-equality facts (from `data_types_nat.rs`)
//!
//! `Nat.sub m n := Nat.rec m (λ _ ih => Nat.pred ih) n` (recurses on the
//! *second* argument) and `Nat.pred n := Nat.rec 0 (λ k _ => k) n`, so:
//!
//! - `a - 0 ≡ a` and `a - Nat.succ k ≡ Nat.pred (a - k)`.
//! - `Nat.pred 0 ≡ 0` and `Nat.pred (Nat.succ k) ≡ k`.
//! - `a - Nat.succ 0 ≡ Nat.pred a` (a special case of the above).
//! - `Nat.lt x y ≡ Nat.le (Nat.succ x) y`.
//!
//! # Proof strategy
//!
//! 1. **`Nat.succ_sub_succ`** — `Nat.rec` on `n`. Base (`n = 0`): both sides
//!    reduce to `m` (`succ m - succ 0 ≡ pred (succ m) ≡ m` and `m - 0 ≡ m`),
//!    so `@Eq.refl Nat m`. Step (`n = succ j`): `congrArg Nat.pred` applied to
//!    the IH `succ m - succ j = m - j` proves `pred (succ m - succ j) =
//!    pred (m - j)`, which is defeq to `succ m - succ (succ j) = m - succ j`.
//!
//! 2. **`Nat.pred_le_pred`** — `Nat.le.rec` on `h : a ≤ b` (index `a` fixed),
//!    motive `fun t _ => Nat.le (pred a) (pred t)`. Refl: `Nat.le.refl (pred a)`.
//!    Step (`t → succ t`): goal `pred a ≤ pred (succ t) ≡ pred a ≤ t`, proved
//!    by `Nat.le_trans (pred a) (pred t) t ih (Nat.pred_le t)`.
//!
//! 3. **`Nat.succ_pred_of_pos`** — `Nat.le.rec` on `h : Nat.succ 0 ≤ a`
//!    (`= Nat.lt 0 a`), index `Nat.succ 0` fixed, motive
//!    `fun t _ => Eq (succ (pred t)) t`. Refl (`t = succ 0`):
//!    `succ (pred (succ 0)) ≡ succ 0`, so `@Eq.refl Nat (succ 0)`. Step
//!    (`t → succ t`): `succ (pred (succ t)) ≡ succ t`, so `@Eq.refl Nat (succ t)`.
//!
//! 4. **`Nat.sub_self`** — `Nat.rec` on `a`. Base: `0 - 0 ≡ 0`, `@Eq.refl Nat 0`.
//!    Step (`a = succ k`): `Eq.trans` of `Nat.succ_sub_succ k k :
//!    succ k - succ k = k - k` with the IH `k - k = 0`.
//!
//! 5. **`Nat.sub_le_sub_right`** — `Nat.rec` on `c`, motive
//!    `fun t => Nat.le (a - t) (b - t)`. Base: `a - 0 ≡ a`, `b - 0 ≡ b`, so the
//!    motive at 0 is `Nat.le a b = h`. Step (`c = succ k`): goal
//!    `pred (a - k) ≤ pred (b - k)` via `Nat.pred_le_pred (a-k) (b-k) ih`.
//!
//! 6. **`Nat.sub_le_sub_left`** — `Nat.le.rec` on `h : b ≤ c` (index `b`
//!    fixed), motive `fun t _ => Nat.le (a - t) (a - b)`. Refl:
//!    `Nat.le.refl (a - b)`. Step (`t → succ t`): goal
//!    `pred (a - t) ≤ (a - b)` via
//!    `Nat.le_trans (pred (a-t)) (a-t) (a-b) (Nat.pred_le (a-t)) ih`.
//!
//! 7. **`Nat.sub_lt`** — `h1 : Nat.le (succ 0) a`, `h2 : Nat.le (succ 0) b`.
//!    Goal `Nat.lt (a - b) a ≡ Nat.le (succ (a - b)) a`. Compose, via
//!    `Nat.le_trans (succ (a-b)) (succ (pred a)) a`:
//!    - `X = Nat.succ_le_succ (a-b) (pred a) (Nat.sub_le_sub_left a (succ 0) b h2)`
//!      `: Nat.le (succ (a-b)) (succ (pred a))` — using `a - succ 0 ≡ pred a`.
//!    - `Y = @Eq.subst Nat (fun z => Nat.le (succ (pred a)) z) (succ (pred a)) a`
//!      `(Nat.succ_pred_of_pos a h1) (Nat.le.refl (succ (pred a)))`
//!      `: Nat.le (succ (pred a)) a`.
//!
//! Tracking: #3604.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::ConstantKind;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Kernel constants reused across the remaining `Nat.sub`-order proof terms.
struct NatSubOrderConsts {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    sub: Expr,
    pred: Expr,
    /// `Nat.rec.{0}` — `Prop`-valued motive.
    nat_rec: Expr,
    le: Expr,
    le_refl_ctor: Expr,
    le_rec: Expr,
    le_trans_thm: Expr,
    succ_le_succ_thm: Expr,
    pred_le_thm: Expr,
    pred_le_pred_thm: Expr,
    succ_sub_succ_thm: Expr,
    succ_pred_of_pos_thm: Expr,
    sub_le_sub_left_thm: Expr,
    /// `Eq.{1}` (`Nat : Sort 1`).
    eq: Expr,
    /// `Eq.refl.{1}`.
    eq_refl: Expr,
    /// `Eq.trans.{1}`.
    eq_trans: Expr,
    /// `Eq.subst.{1}`.
    eq_subst: Expr,
    /// `congrArg.{1,1}`.
    congr_arg: Expr,
}

impl NatSubOrderConsts {
    fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            sub: Expr::const_(Name::from_string("Nat.sub"), vec![]),
            pred: Expr::const_(Name::from_string("Nat.pred"), vec![]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            le_refl_ctor: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            le_rec: Expr::const_(Name::from_string("Nat.le.rec"), vec![]),
            le_trans_thm: Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
            succ_le_succ_thm: Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
            pred_le_thm: Expr::const_(Name::from_string("Nat.pred_le"), vec![]),
            pred_le_pred_thm: Expr::const_(Name::from_string("Nat.pred_le_pred"), vec![]),
            succ_sub_succ_thm: Expr::const_(Name::from_string("Nat.succ_sub_succ"), vec![]),
            succ_pred_of_pos_thm: Expr::const_(Name::from_string("Nat.succ_pred_of_pos"), vec![]),
            sub_le_sub_left_thm: Expr::const_(Name::from_string("Nat.sub_le_sub_left"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]),
        }
    }

    fn sub_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.sub.clone(), [x, y])
    }

    fn pred_of(&self, x: Expr) -> Expr {
        Expr::app(self.pred.clone(), x)
    }

    fn succ_of(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }

    fn le_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.le.clone(), [x, y])
    }

    /// `Eq Nat x y` (`Nat : Sort 1`).
    fn eq_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.nat.clone(), x, y])
    }

    /// `@Nat.le.refl n : Nat.le n n`.
    fn le_refl_app(&self, n: Expr) -> Expr {
        Expr::app(self.le_refl_ctor.clone(), n)
    }

    /// `Nat.le_trans a b c hab hbc : Nat.le a c`.
    fn le_trans(&self, a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.le_trans_thm.clone(), [a, b, c, hab, hbc])
    }

    /// `@Eq.refl Nat x : Eq Nat x x`.
    fn eq_refl_app(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.nat.clone(), x])
    }
}

impl Environment {
    /// Register the remaining `Nat.sub` ordering lemmas (and their helper
    /// lemmas) as constructive `Declaration::Theorem`s (#3604).
    ///
    /// Registers (in dependency order, each idempotent on `get_const`):
    ///
    /// - `Nat.succ_sub_succ`, `Nat.pred_le_pred`, `Nat.succ_pred_of_pos` (helpers)
    /// - `Nat.sub_self`, `Nat.sub_le_sub_right`, `Nat.sub_le_sub_left`, `Nat.sub_lt`
    ///
    /// Must be called *before* the legacy axiom registration sites in
    /// `init_nat_sub_ord` so the Theorem form wins; those sites carry a
    /// `get_const` guard and become no-ops once the Theorem is registered here.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment.
    /// ENSURES: On success, the four lemmas above are `Declaration::Theorem`s
    ///          with `proof_quality == Constructive` and empty axiom closures.
    /// ENSURES: Idempotent.
    pub(crate) fn register_nat_sub_order_remaining_proofs(&mut self) -> Result<(), EnvError> {
        self.init_nat()?; // Nat, Nat.zero, Nat.succ, Nat.sub, Nat.pred, Nat.rec
        self.init_le()?; // Nat.le, Nat.le.refl, Nat.le.step, Nat.le.rec
                         // Constructive support: `Nat.succ_le_succ`, `Nat.le_refl`.
        self.init_nat_top_level_ordering()?;
        // Constructive `Nat.le_trans`.
        self.register_nat_le_trans_proof()?;
        // Constructive `Nat.pred_le`, `Nat.sub_le` (and arith-order family).
        self.register_nat_arith_order_proofs()?;

        let c = NatSubOrderConsts::new();
        self.register_nat_succ_sub_succ(&c)?;
        self.register_nat_pred_le_pred(&c)?;
        self.register_nat_succ_pred_of_pos(&c)?;
        self.register_nat_sub_self(&c)?;
        // IMPORT MODE (v4.31 retarget): the two `sub_le_sub_*` statements are
        // transposed-binder drifted vs v4.31 (`(k)` before `h`, explicit
        // bounds, raw Nat.le) — suppressed so the genuine olean lemmas import
        // (closure-checked). The rest of this constructive family is
        // v4.31-compatible and stays in both lanes.
        if !self.suppress_lossy_structure_stubs {
            self.register_nat_sub_le_sub_right(&c)?;
            self.register_nat_sub_le_sub_left(&c)?;
            // `Nat.sub_lt`'s proof value applies `Nat.sub_le_sub_left`, so it
            // rides the same import-mode gate (genuine olean form imports).
            self.register_nat_sub_lt(&c)?;
        }
        Ok(())
    }

    /// `Nat.succ_sub_succ : ∀ m n, Eq (Nat.succ m - Nat.succ n) (m - n)`.
    fn register_nat_succ_sub_succ(&mut self, c: &NatSubOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.succ_sub_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let (n_id, n) = b.fresh_local(c.nat.clone());

        // Type: ∀ m n, Eq (succ m - succ n) (m - n)
        let type_ = {
            let concl = c.eq_of(
                c.sub_of(c.succ_of(m.clone()), c.succ_of(n.clone())),
                c.sub_of(m.clone(), n.clone()),
            );
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Eq (succ m - succ t) (m - t)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.eq_of(
                c.sub_of(c.succ_of(m.clone()), c.succ_of(t.clone())),
                c.sub_of(m.clone(), t.clone()),
            );
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base (t = 0): `succ m - succ 0 ≡ pred (succ m) ≡ m` and `m - 0 ≡ m`,
        // so `@Eq.refl Nat m : Eq Nat m m`.
        let base = c.eq_refl_app(m.clone());
        // step: fun (j : Nat) (ih : Eq (succ m - succ j) (m - j)) =>
        //   @congrArg Nat Nat (succ m - succ j) (m - j) Nat.pred ih
        //     : Eq (pred (succ m - succ j)) (pred (m - j))
        //     ≡ Eq (succ m - succ (succ j)) (m - succ j)
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = sb.fresh_local(c.nat.clone());
            let lhs = c.sub_of(c.succ_of(m.clone()), c.succ_of(j.clone()));
            let rhs = c.sub_of(m.clone(), j.clone());
            let ih_type = c.eq_of(lhs.clone(), rhs.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let body = Expr::apps(
                c.congr_arg.clone(),
                [c.nat.clone(), c.nat.clone(), lhs, rhs, c.pred.clone(), ih],
            );
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_j = sb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_j)
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n.clone()]);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term over `Nat.sub`/`Nat.pred`
        // (reducible Definitions). Uses only the foundational `Eq.refl` and
        // `congrArg`. No `Declaration::Axiom`, no `sorry`, no self-reference.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.pred_le_pred : ∀ a b, Nat.le a b → Nat.le (Nat.pred a) (Nat.pred b)`.
    fn register_nat_pred_le_pred(&mut self, c: &NatSubOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.pred_le_pred");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let h_type = c.le_of(a.clone(), bb.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());

        // Type: ∀ a b, Nat.le a b → Nat.le (pred a) (pred b)
        let type_ = {
            let concl = c.le_of(c.pred_of(a.clone()), c.pred_of(bb.clone()));
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let pred_a = c.pred_of(a.clone());

        // motive: fun (t : Nat) (_ : Nat.le a t) => Nat.le (pred a) (pred t)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let le_a_t = c.le_of(a.clone(), t.clone());
            let (ht_id, _ht) = mb.fresh_local(le_a_t.clone());
            let body = c.le_of(pred_a.clone(), c.pred_of(t.clone()));
            let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_a_t, body);
            let lam_t = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), lam_h);
            mb.finish_child(lam_t)
        };
        // refl minor: `Nat.le.refl (pred a)` (`pred a ≤ pred a`).
        let minor_refl = c.le_refl_app(pred_a.clone());
        // step minor: fun {t} (_ : Nat.le a t) (ih : Nat.le (pred a) (pred t)) =>
        //   Nat.le_trans (pred a) (pred t) t ih (Nat.pred_le t)
        //     : Nat.le (pred a) t ≡ Nat.le (pred a) (pred (succ t))
        let minor_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = sb.fresh_local(c.nat.clone());
            let le_a_t = c.le_of(a.clone(), t.clone());
            let (ht_id, _ht) = sb.fresh_local(le_a_t.clone());
            let pred_t = c.pred_of(t.clone());
            let ih_type = c.le_of(pred_a.clone(), pred_t.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let pred_le_t = Expr::app(c.pred_le_thm.clone(), t.clone());
            let body = c.le_trans(pred_a.clone(), pred_t, t.clone(), ih, pred_le_t);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_a_t, lam_ih);
            let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, c.nat.clone(), lam_h);
            sb.finish_child(lam_t)
        };

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

        // SOUNDNESS: kernel-checked `Nat.le.rec` term. Uses only the
        // constructive `Nat.le_trans` and `Nat.pred_le` plus the `Nat.le.refl`
        // constructor. No `Declaration::Axiom`, no `sorry`, no self-reference.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.succ_pred_of_pos : ∀ a, Nat.lt 0 a → Eq (Nat.succ (Nat.pred a)) a`.
    ///
    /// `Nat.lt 0 a ≡ Nat.le (Nat.succ 0) a`.
    fn register_nat_succ_pred_of_pos(&mut self, c: &NatSubOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.succ_pred_of_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let one = c.succ_of(c.zero.clone());

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        // h : Nat.le (succ 0) a (the unfolded `Nat.lt 0 a`).
        let h_type = c.le_of(one.clone(), a.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());

        // Type: ∀ a, Nat.lt 0 a → Eq (succ (pred a)) a
        let type_ = {
            let concl = c.eq_of(c.succ_of(c.pred_of(a.clone())), a.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (t : Nat) (_ : Nat.le (succ 0) t) => Eq (succ (pred t)) t
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let le_one_t = c.le_of(one.clone(), t.clone());
            let (ht_id, _ht) = mb.fresh_local(le_one_t.clone());
            let body = c.eq_of(c.succ_of(c.pred_of(t.clone())), t.clone());
            let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_one_t, body);
            let lam_t = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), lam_h);
            mb.finish_child(lam_t)
        };
        // refl minor (t = succ 0): `succ (pred (succ 0)) ≡ succ 0`, so
        // `@Eq.refl Nat (succ 0)`.
        let minor_refl = c.eq_refl_app(one.clone());
        // step minor: fun {t} (_ : Nat.le (succ 0) t) (_ih : ...) =>
        //   `@Eq.refl Nat (succ t)` : Eq (succ t) (succ t)
        //     ≡ Eq (succ (pred (succ t))) (succ t)  (since `pred (succ t) ≡ t`)
        let minor_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = sb.fresh_local(c.nat.clone());
            let le_one_t = c.le_of(one.clone(), t.clone());
            let (ht_id, _ht) = sb.fresh_local(le_one_t.clone());
            let ih_type = c.eq_of(c.succ_of(c.pred_of(t.clone())), t.clone());
            let (ih_id, _ih) = sb.fresh_local(ih_type.clone());
            let body = c.eq_refl_app(c.succ_of(t.clone()));
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_one_t, lam_ih);
            let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, c.nat.clone(), lam_h);
            sb.finish_child(lam_t)
        };

        let value = {
            let rec_app = Expr::apps(
                c.le_rec.clone(),
                [
                    one.clone(),
                    motive,
                    minor_refl,
                    minor_step,
                    a.clone(),
                    h.clone(),
                ],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, rec_app);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.le.rec` term over `Nat.pred` (reducible
        // Definition). Uses only the foundational `Eq.refl`. No
        // `Declaration::Axiom`, no `sorry`, no self-reference.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.sub_self : ∀ a, Eq (Nat.sub a a) Nat.zero`.
    fn register_nat_sub_self(&mut self, c: &NatSubOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.sub_self");
        if self.is_theorem_sub_remaining(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());

        // Type: ∀ a, Eq (a - a) 0
        let type_ = {
            let concl = c.eq_of(c.sub_of(a.clone(), a.clone()), c.zero.clone());
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Eq (t - t) 0
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.eq_of(c.sub_of(t.clone(), t.clone()), c.zero.clone());
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base (t = 0): `0 - 0 ≡ 0`, so `@Eq.refl Nat 0 : Eq Nat 0 0`.
        let base = c.eq_refl_app(c.zero.clone());
        // step: fun (k : Nat) (ih : Eq (k - k) 0) =>
        //   @Eq.trans Nat (succ k - succ k) (k - k) 0
        //     (Nat.succ_sub_succ k k)   : Eq (succ k - succ k) (k - k)
        //     ih                        : Eq (k - k) 0
        //     : Eq (succ k - succ k) 0
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let sub_k_k = c.sub_of(k.clone(), k.clone());
            let ih_type = c.eq_of(sub_k_k.clone(), c.zero.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let succ_k = c.succ_of(k.clone());
            let sub_sk_sk = c.sub_of(succ_k.clone(), succ_k.clone());
            let succ_sub_succ_k_k = Expr::apps(c.succ_sub_succ_thm.clone(), [k.clone(), k.clone()]);
            let body = Expr::apps(
                c.eq_trans.clone(),
                [
                    c.nat.clone(),
                    sub_sk_sk,
                    sub_k_k,
                    c.zero.clone(),
                    succ_sub_succ_k_k,
                    ih,
                ],
            );
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, a.clone()]);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), rec_app);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term. Uses only the foundational
        // `Eq.refl`/`Eq.trans` and the constructive `Nat.succ_sub_succ`.
        // Replaces the legacy `Declaration::Axiom` in
        // `order_arith.rs::init_nat_sub_ord`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.sub_le_sub_right : ∀ a b c, Nat.le a b → Nat.le (a - c) (b - c)`.
    fn register_nat_sub_le_sub_right(&mut self, c: &NatSubOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.sub_le_sub_right");
        if self.is_theorem_sub_remaining(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());
        let h_type = c.le_of(a.clone(), bb.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());

        // Type: ∀ a b c, Nat.le a b → Nat.le (a - c) (b - c)
        let type_ = {
            let concl = c.le_of(
                c.sub_of(a.clone(), cc.clone()),
                c.sub_of(bb.clone(), cc.clone()),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Nat.le (a - t) (b - t)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.le_of(
                c.sub_of(a.clone(), t.clone()),
                c.sub_of(bb.clone(), t.clone()),
            );
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base (t = 0): `a - 0 ≡ a`, `b - 0 ≡ b`, so motive at 0 is `Nat.le a b` = h.
        let base = h.clone();
        // step: fun (k : Nat) (ih : Nat.le (a-k) (b-k)) =>
        //   Nat.pred_le_pred (a-k) (b-k) ih
        //     : Nat.le (pred (a-k)) (pred (b-k))
        //     ≡ Nat.le (a - succ k) (b - succ k)
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let sub_a_k = c.sub_of(a.clone(), k.clone());
            let sub_b_k = c.sub_of(bb.clone(), k.clone());
            let ih_type = c.le_of(sub_a_k.clone(), sub_b_k.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let body = Expr::apps(c.pred_le_pred_thm.clone(), [sub_a_k, sub_b_k, ih]);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, cc.clone()]);
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, rec_app);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term over `Nat.sub` (reducible
        // Definition). Uses only the constructive `Nat.pred_le_pred`. Replaces
        // the legacy `Declaration::Axiom` in `order_arith.rs::init_nat_sub_ord`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.sub_le_sub_left : ∀ a b c, Nat.le b c → Nat.le (a - c) (a - b)`.
    fn register_nat_sub_le_sub_left(&mut self, c: &NatSubOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.sub_le_sub_left");
        if self.is_theorem_sub_remaining(&name) {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());
        let h_type = c.le_of(bb.clone(), cc.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());

        // Type: ∀ a b c, Nat.le b c → Nat.le (a - c) (a - b)
        let type_ = {
            let concl = c.le_of(
                c.sub_of(a.clone(), cc.clone()),
                c.sub_of(a.clone(), bb.clone()),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let sub_a_b = c.sub_of(a.clone(), bb.clone());

        // motive: fun (t : Nat) (_ : Nat.le b t) => Nat.le (a - t) (a - b)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let le_b_t = c.le_of(bb.clone(), t.clone());
            let (ht_id, _ht) = mb.fresh_local(le_b_t.clone());
            let body = c.le_of(c.sub_of(a.clone(), t.clone()), sub_a_b.clone());
            let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_b_t, body);
            let lam_t = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), lam_h);
            mb.finish_child(lam_t)
        };
        // refl minor: `Nat.le.refl (a - b)` (`a - b ≤ a - b`).
        let minor_refl = c.le_refl_app(sub_a_b.clone());
        // step minor: fun {t} (_ : Nat.le b t) (ih : Nat.le (a-t) (a-b)) =>
        //   Nat.le_trans (pred (a-t)) (a-t) (a-b) (Nat.pred_le (a-t)) ih
        //     : Nat.le (pred (a-t)) (a-b) ≡ Nat.le (a - succ t) (a-b)
        let minor_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = sb.fresh_local(c.nat.clone());
            let le_b_t = c.le_of(bb.clone(), t.clone());
            let (ht_id, _ht) = sb.fresh_local(le_b_t.clone());
            let sub_a_t = c.sub_of(a.clone(), t.clone());
            let ih_type = c.le_of(sub_a_t.clone(), sub_a_b.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let pred_sub_a_t = c.pred_of(sub_a_t.clone());
            let pred_le = Expr::app(c.pred_le_thm.clone(), sub_a_t.clone());
            let body = c.le_trans(pred_sub_a_t, sub_a_t, sub_a_b.clone(), pred_le, ih);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_b_t, lam_ih);
            let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, c.nat.clone(), lam_h);
            sb.finish_child(lam_t)
        };

        let value = {
            let rec_app = Expr::apps(
                c.le_rec.clone(),
                [
                    bb.clone(),
                    motive,
                    minor_refl,
                    minor_step,
                    cc.clone(),
                    h.clone(),
                ],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, rec_app);
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.le.rec` term over `Nat.sub`/`Nat.pred`
        // (reducible Definitions). Uses only the constructive `Nat.le_trans`
        // and `Nat.pred_le`. Replaces the legacy `Declaration::Axiom` in
        // `order_arith.rs::init_nat_sub_ord`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.sub_lt : ∀ a b, Nat.lt 0 a → Nat.lt 0 b → Nat.lt (a - b) a`.
    ///
    /// `Nat.lt x y ≡ Nat.le (Nat.succ x) y`, so `h1 : Nat.le (succ 0) a`,
    /// `h2 : Nat.le (succ 0) b`, and the goal is `Nat.le (succ (a - b)) a`.
    fn register_nat_sub_lt(&mut self, c: &NatSubOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.sub_lt");
        if self.is_theorem_sub_remaining(&name) {
            return Ok(());
        }

        let one = c.succ_of(c.zero.clone());

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        // h1 : Nat.lt 0 a ≡ Nat.le (succ 0) a
        let h1_type = c.le_of(one.clone(), a.clone());
        let (h1_id, h1) = b.fresh_local(h1_type.clone());
        // h2 : Nat.lt 0 b ≡ Nat.le (succ 0) b
        let h2_type = c.le_of(one.clone(), bb.clone());
        let (h2_id, h2) = b.fresh_local(h2_type.clone());

        // Type: ∀ a b, Nat.lt 0 a → Nat.lt 0 b → Nat.lt (a - b) a
        // (`Nat.lt x y ≡ Nat.le (succ x) y`).
        let type_ = {
            let concl = c.le_of(c.succ_of(c.sub_of(a.clone(), bb.clone())), a.clone());
            let e = b.mk_pi(h2_id, BinderInfo::Default, h2_type.clone(), concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_type.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value: Nat.le_trans (succ (a-b)) (succ (pred a)) a X Y where
        //   X = Nat.succ_le_succ (a-b) (pred a)
        //         (Nat.sub_le_sub_left a (succ 0) b h2)
        //       : Nat.le (succ (a-b)) (succ (pred a))
        //   Y = @Eq.subst Nat (fun z => Nat.le (succ (pred a)) z) (succ (pred a)) a
        //         (Nat.succ_pred_of_pos a h1) (Nat.le.refl (succ (pred a)))
        //       : Nat.le (succ (pred a)) a
        let value = {
            let sub_a_b = c.sub_of(a.clone(), bb.clone());
            let succ_sub_a_b = c.succ_of(sub_a_b.clone());
            let pred_a = c.pred_of(a.clone());
            let succ_pred_a = c.succ_of(pred_a.clone());

            // Nat.sub_le_sub_left a (succ 0) b h2 : Nat.le (a - b) (a - succ 0)
            //   ≡ Nat.le (a - b) (pred a)
            let sub_le_sub_left_app = Expr::apps(
                c.sub_le_sub_left_thm.clone(),
                [a.clone(), one.clone(), bb.clone(), h2.clone()],
            );
            // X : Nat.le (succ (a-b)) (succ (pred a))
            let x_term = Expr::apps(
                c.succ_le_succ_thm.clone(),
                [sub_a_b.clone(), pred_a.clone(), sub_le_sub_left_app],
            );

            // motive: fun (z : Nat) => Nat.le (succ (pred a)) z
            let subst_motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = mb.fresh_local(c.nat.clone());
                let body = c.le_of(succ_pred_a.clone(), z);
                let lam = mb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                mb.finish_child(lam)
            };
            // Nat.succ_pred_of_pos a h1 : Eq (succ (pred a)) a
            let succ_pred_eq = Expr::apps(c.succ_pred_of_pos_thm.clone(), [a.clone(), h1.clone()]);
            // Nat.le.refl (succ (pred a)) : Nat.le (succ (pred a)) (succ (pred a))
            let refl_motive = c.le_refl_app(succ_pred_a.clone());
            // Y : Nat.le (succ (pred a)) a
            let y_term = Expr::apps(
                c.eq_subst.clone(),
                [
                    c.nat.clone(),
                    subst_motive,
                    succ_pred_a.clone(),
                    a.clone(),
                    succ_pred_eq,
                    refl_motive,
                ],
            );

            // Nat.le_trans (succ (a-b)) (succ (pred a)) a X Y : Nat.le (succ (a-b)) a
            let body = c.le_trans(succ_sub_a_b, succ_pred_a, a.clone(), x_term, y_term);
            let e = b.mk_lam(h2_id, BinderInfo::Default, h2_type, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_type, e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked composition of the constructive
        // `Nat.sub_le_sub_left`, `Nat.succ_le_succ`, `Nat.succ_pred_of_pos`,
        // `Nat.le_trans`, the `Nat.le.refl` constructor, and the foundational
        // `Eq.subst`. Replaces the legacy `Declaration::Axiom` in
        // `order_arith.rs::init_nat_sub_ord`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Whether `name` is already registered as a `Declaration::Theorem`.
    fn is_theorem_sub_remaining(&self, name: &Name) -> bool {
        matches!(
            self.get_const(name).map(|i| i.kind),
            Some(ConstantKind::Theorem)
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    /// Build an environment with the `Nat.sub` ordering family registered.
    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nat_sub_ord()
            .expect("init_nat_sub_ord must succeed");
        env
    }

    /// The four demoted targets plus their three prerequisite helper lemmas.
    const DEMOTED_AND_HELPERS: &[&str] = &[
        // Targets demoted this session.
        "Nat.sub_self",
        "Nat.sub_lt",
        "Nat.sub_le_sub_left",
        "Nat.sub_le_sub_right",
        // New prerequisite helpers (each itself a constructive Theorem).
        "Nat.succ_sub_succ",
        "Nat.pred_le_pred",
        "Nat.succ_pred_of_pos",
    ];

    #[test]
    fn test_nat_sub_remaining_registered_as_theorems() {
        let env = make_env();
        for name in DEMOTED_AND_HELPERS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} must be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} must be a Declaration::Theorem, got {:?}",
                info.kind
            );
            assert!(
                info.value.is_some(),
                "{name} must carry a proof term (not structural/unchecked)"
            );
        }
    }

    #[test]
    fn test_nat_sub_remaining_proof_terms_typecheck() {
        let env = make_env();
        let tc = TypeChecker::new(&env);
        for name in DEMOTED_AND_HELPERS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} must be registered"));
            let value = info
                .value
                .as_ref()
                .unwrap_or_else(|| panic!("{name} must have a value"));
            let inferred = tc
                .infer_type(value)
                .unwrap_or_else(|e| panic!("{name} proof term must typecheck: {e:?}"));
            // The inferred type of the proof term must be definitionally equal
            // to the declared type.
            assert!(
                tc.is_def_eq(&inferred, &info.type_),
                "{name} inferred type must match declared type",
            );
        }
    }

    #[test]
    fn test_nat_sub_remaining_axiom_deps_empty() {
        let env = make_env();
        for name in DEMOTED_AND_HELPERS {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} must be registered"));
            assert!(
                deps.is_empty(),
                "{name} must have an EMPTY domain-axiom closure, found: {deps:?}"
            );
        }
    }

    #[test]
    fn test_nat_sub_remaining_proof_quality_constructive() {
        let env = make_env();
        for name in DEMOTED_AND_HELPERS {
            match env.proof_quality(&Name::from_string(name)) {
                Some(ProofQuality::Constructive) => {}
                Some(ProofQuality::AxiomDependent { axioms, .. }) => {
                    panic!("{name} is AxiomDependent, not Constructive. Domain axioms: {axioms:?}")
                }
                other => panic!("{name} must be ProofQuality::Constructive, got {other:?}"),
            }
        }
    }

    #[test]
    fn test_nat_sub_remaining_idempotent() {
        let mut env = Environment::new();
        env.init_nat_sub_ord().expect("first init");
        // A second registration pass must be a no-op (Theorem already present).
        env.register_nat_sub_order_remaining_proofs()
            .expect("second registration must be idempotent");
        for name in DEMOTED_AND_HELPERS {
            assert_eq!(
                env.get_const(&Name::from_string(name))
                    .unwrap_or_else(|| panic!("{name} must be registered"))
                    .kind,
                ConstantKind::Theorem,
                "{name} must remain a Theorem after idempotent re-registration",
            );
        }
    }
}
