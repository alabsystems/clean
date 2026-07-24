// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive demotion of `Nat.mul_left_cancel_succ` (the last major Nat
//! cancellation axiom) and the multiplicative-monotonicity helpers it needs.
//!
//! Previously `Nat.mul_left_cancel_succ` was registered as a
//! `Declaration::Axiom` in `data_types_nat_lemmas.rs`. This module replaces it
//! with a genuine kernel-checked `Declaration::Theorem` whose transitive
//! axiom closure is empty, by building up the standard order-theoretic route:
//!
//! ```text
//! Nat.zero_le                 : ∀ n, Nat.le 0 n
//! Nat.le_add_right            : ∀ n k, Nat.le n (Nat.add n k)
//! Nat.mul_le_mul_left         : ∀ k a b, Nat.le a b → Nat.le (k*a) (k*b)
//! Nat.le_or_lt                : ∀ a b, Or (Nat.le a b) (Nat.lt b a)
//! Nat.mul_lt_mul_left_succ    : ∀ n a b, Nat.lt a b → Nat.lt ((succ n)*a) ((succ n)*b)
//! Nat.le_of_mul_le_mul_left_succ : ∀ n a b, Nat.le ((succ n)*a) ((succ n)*b) → Nat.le a b
//! Nat.mul_left_cancel_succ    : ∀ n a b, Eq ((succ n)*a) ((succ n)*b) → Eq a b
//! ```
//!
//! Each lemma is a sorry-free term built only from `Nat`-recursors,
//! `Nat.le` constructors / recursor, `Or` constructors / recursor, `Eq`
//! built-ins, `False.elim`, and the already-constructive `Nat.le_refl`,
//! `Nat.le_trans`, `Nat.le_antisymm`, `Nat.lt_irrefl`, `Nat.succ_le_succ`
//! theorems. None of these are `Declaration::Axiom`, so every registered
//! theorem here has `proof_quality == Constructive` and empty `axiom_deps`.
//!
//! Tracks #3604 (cancellation-law demotion); closes the multiplicative
//! left-cancellation blocker noted alongside `Nat.add_left_cancel`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants reused across the cancellation proofs.
struct NatMulCancelConsts {
    nat: Expr,
    zero: Expr,
    succ: Expr,
    add: Expr,
    mul: Expr,
    nat_rec: Expr,
    le: Expr,
    le_refl_ctor: Expr,
    le_step_ctor: Expr,
    le_rec: Expr,
    le_trans_thm: Expr,
    le_antisymm_thm: Expr,
    succ_le_succ_thm: Expr,
    lt_irrefl_thm: Expr,
    or_const: Expr,
    or_inl: Expr,
    or_inr: Expr,
    or_rec: Expr,
    eq_const: Expr,
    eq_subst: Expr,
    false_const: Expr,
    false_elim: Expr,
}

impl NatMulCancelConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            // `Nat.rec.{0}` — Prop motive.
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            le_refl_ctor: Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            le_step_ctor: Expr::const_(Name::from_string("Nat.le.step"), vec![]),
            le_rec: Expr::const_(Name::from_string("Nat.le.rec"), vec![]),
            le_trans_thm: Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
            le_antisymm_thm: Expr::const_(Name::from_string("Nat.le_antisymm"), vec![]),
            succ_le_succ_thm: Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
            lt_irrefl_thm: Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]),
            or_const: Expr::const_(Name::from_string("Or"), vec![]),
            or_inl: Expr::const_(Name::from_string("Or.inl"), vec![]),
            or_inr: Expr::const_(Name::from_string("Or.inr"), vec![]),
            // `Or.rec` eliminating into Prop carries a single Prop motive level.
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            eq_const: Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1]),
            false_const: Expr::const_(Name::from_string("False"), vec![]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        }
    }

    fn succ_of(&self, x: Expr) -> Expr {
        Expr::app(self.succ.clone(), x)
    }

    fn add_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.add.clone(), [x, y])
    }

    fn mul_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.mul.clone(), [x, y])
    }

    fn le_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.le.clone(), [x, y])
    }

    /// `Nat.lt x y`, written in its reducible expansion `Nat.le (Nat.succ x) y`.
    fn lt_of(&self, x: Expr, y: Expr) -> Expr {
        self.le_of(self.succ_of(x), y)
    }

    fn eq_of(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq_const.clone(), [self.nat.clone(), x, y])
    }

    fn or_of(&self, a: Expr, bb: Expr) -> Expr {
        Expr::apps(self.or_const.clone(), [a, bb])
    }

    /// `@Nat.le.step n m h : Nat.le n (Nat.succ m)`.
    fn le_step(&self, n: Expr, m: Expr, h: Expr) -> Expr {
        Expr::apps(self.le_step_ctor.clone(), [n, m, h])
    }

    /// `@Nat.le.refl n : Nat.le n n`.
    fn le_refl_ctor_app(&self, n: Expr) -> Expr {
        Expr::app(self.le_refl_ctor.clone(), n)
    }

    /// `Nat.le_trans a b c hab hbc : Nat.le a c` (raw `Nat.le`, accepted by defeq).
    fn le_trans(&self, a: Expr, b: Expr, c: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.le_trans_thm.clone(), [a, b, c, hab, hbc])
    }

    /// `Nat.succ_le_succ n m h : Nat.le (succ n) (succ m)`.
    fn succ_le_succ(&self, n: Expr, m: Expr, h: Expr) -> Expr {
        Expr::apps(self.succ_le_succ_thm.clone(), [n, m, h])
    }
}

impl Environment {
    /// Register every supporting lemma and finally demote
    /// `Nat.mul_left_cancel_succ` to a constructive `Declaration::Theorem`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_nat()`, `self.init_le()`, `self.init_lt()`,
    ///           `self.init_eq()`, `self.init_or()`, `self.init_true_false()`
    ///           provide the supporting symbols.
    /// ENSURES: On success, `Nat.mul_left_cancel_succ` and all helper lemmas are
    ///          `Declaration::Theorem`s with `proof_quality == Constructive`.
    /// ENSURES: Idempotent — each registration guards on `get_const`.
    pub(crate) fn register_nat_mul_left_cancel_succ_proof(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate — this whole
        // lemma family (Nat.zero_le, Nat.le_add_right, Nat.mul_le_mul_left,
        // Nat.le_or_lt, Nat.mul_left_cancel_succ, …) is stated over the
        // import-gated Nat.add/Nat.mul seeds (see data_types_nat.rs::init_nat);
        // the genuine olean lemmas import through the checked path instead.
        // Default lane byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Nat.mul_left_cancel_succ");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;
        self.init_eq()?;
        self.init_or()?;
        self.init_true_false()?;
        self.init_nat_top_level_ordering()?; // Nat.succ_le_succ, Nat.le_refl
        self.register_nat_le_trans_proof()?;
        self.register_nat_le_antisymm_proof()?;
        self.register_nat_lt_irrefl_theorem()?;

        let c = NatMulCancelConsts::new();

        self.register_nat_zero_le(&c)?;
        self.register_nat_le_add_right(&c)?;
        self.register_nat_mul_le_mul_left(&c)?;
        self.register_nat_le_or_lt(&c)?;
        self.register_nat_mul_lt_mul_left_succ(&c)?;
        self.register_nat_le_of_mul_le_mul_left_succ(&c)?;
        self.register_nat_mul_left_cancel_succ_theorem(&c)
    }

    /// `Nat.zero_le : ∀ n : Nat, Nat.le Nat.zero n`.
    ///
    /// Induction on `n` via `Nat.rec.{0}` with motive `fun t => Nat.le 0 t`.
    /// Base: `Nat.le.refl 0`. Step: `Nat.le.step 0 k ih`.
    fn register_nat_zero_le(&mut self, c: &NatMulCancelConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.zero_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());

        let type_ = {
            let body = c.le_of(c.zero.clone(), n.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Nat.le 0 t
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.le_of(c.zero.clone(), t);
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base: Nat.le.refl 0 : Nat.le 0 0
        let base = c.le_refl_ctor_app(c.zero.clone());
        // step: fun (k : Nat) (ih : Nat.le 0 k) => Nat.le.step 0 k ih
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(c.nat.clone());
            let ih_type = c.le_of(c.zero.clone(), k.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let body = c.le_step(c.zero.clone(), k, ih);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, n.clone()]);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec_app);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term, no axiom/self-reference.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.le_add_right : ∀ n k : Nat, Nat.le n (Nat.add n k)`.
    ///
    /// Induction on `k` via `Nat.rec.{0}` with motive `fun t => Nat.le n (n + t)`.
    /// Base (`t = 0`): `n + 0 ≡ n`, witnessed by `Nat.le.refl n`.
    /// Step (`t = succ j`): `n + succ j ≡ succ (n + j)`, so `Nat.le.step n (n+j) ih`.
    fn register_nat_le_add_right(&mut self, c: &NatMulCancelConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_add_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (k_id, k) = b.fresh_local(c.nat.clone());

        let type_ = {
            let body = c.le_of(n.clone(), c.add_of(n.clone(), k.clone()));
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (t : Nat) => Nat.le n (Nat.add n t)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let body = c.le_of(n.clone(), c.add_of(n.clone(), t));
            let lam = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), body);
            mb.finish_child(lam)
        };
        // base: Nat.le.refl n : Nat.le n n ≡ Nat.le n (Nat.add n 0)
        let base = c.le_refl_ctor_app(n.clone());
        // step: fun (j : Nat) (ih : Nat.le n (n + j)) =>
        //         Nat.le.step n (n + j) ih : Nat.le n (succ (n + j)) ≡ Nat.le n (n + succ j)
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = sb.fresh_local(c.nat.clone());
            let n_plus_j = c.add_of(n.clone(), j.clone());
            let ih_type = c.le_of(n.clone(), n_plus_j.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let body = c.le_step(n.clone(), n_plus_j, ih);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, body);
            let lam_j = sb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_j)
        };

        let value = {
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, k.clone()]);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), rec_app);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Nat.rec` term, no axiom/self-reference.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.mul_le_mul_left : ∀ a b c : Nat, Nat.le a b → Nat.le (Nat.mul c a) (Nat.mul c b)`.
    ///
    /// Matches the canonical signature previously registered as a
    /// `Declaration::Axiom` in `order_arith.rs::init_nat_mul_ord` (binders
    /// `a b c`, hypothesis `a ≤ b`, multiplier `c`). Induction on `h : Nat.le a b`
    /// via `Nat.le.rec` (parameter `a`) with motive
    /// `fun (t : Nat) (_ : Nat.le a t) => Nat.le (c*a) (c*t)`.
    /// - refl case (`t = a`): `Nat.le.refl (c*a)`.
    /// - step case (`t → succ t`, `ih : c*a ≤ c*t`): the motive target reduces
    ///   (`c * succ t ≡ Nat.add (c*t) c`) to `c*a ≤ (c*t) + c`. Built from
    ///   `Nat.le_trans (c*a) (c*t) ((c*t)+c) ih (Nat.le_add_right (c*t) c)`.
    pub(crate) fn register_nat_mul_le_mul_left_proof(&mut self) -> Result<(), EnvError> {
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate — stated over
        // the import-gated Nat.add/Nat.mul seeds (see
        // register_nat_mul_left_cancel_succ_proof above).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Nat.mul_le_mul_left");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        self.init_nat()?;
        self.init_le()?;
        self.init_nat_top_level_ordering()?; // Nat.succ_le_succ, Nat.le_refl
        self.register_nat_le_trans_proof()?;
        let c = NatMulCancelConsts::new();
        self.register_nat_zero_le(&c)?;
        self.register_nat_le_add_right(&c)?;
        self.register_nat_mul_le_mul_left(&c)
    }

    fn register_nat_mul_le_mul_left(&mut self, c: &NatMulCancelConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_le_mul_left");
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        let le_add_right = Expr::const_(Name::from_string("Nat.le_add_right"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let (cc_id, cc) = b.fresh_local(c.nat.clone());
        let h_type = c.le_of(a.clone(), bb.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());

        let type_ = {
            let concl = c.le_of(
                c.mul_of(cc.clone(), a.clone()),
                c.mul_of(cc.clone(), bb.clone()),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let mul_c_a = c.mul_of(cc.clone(), a.clone());

        // motive: fun (t : Nat) (_ : Nat.le a t) => Nat.le (c*a) (c*t)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nat.clone());
            let le_a_t = c.le_of(a.clone(), t.clone());
            let (ht_id, _ht) = mb.fresh_local(le_a_t.clone());
            let body = c.le_of(mul_c_a.clone(), c.mul_of(cc.clone(), t.clone()));
            let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_a_t, body);
            let lam_t = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), lam_h);
            mb.finish_child(lam_t)
        };
        // refl minor: Nat.le.refl (c*a)
        let minor_refl = c.le_refl_ctor_app(mul_c_a.clone());
        // step minor: fun {t} (_ : Nat.le a t) (ih : Nat.le (c*a) (c*t)) =>
        //   Nat.le_trans (c*a) (c*t) (Nat.add (c*t) c) ih (Nat.le_add_right (c*t) c)
        // The result type `Nat.le (c*a) (Nat.add (c*t) c)` is defeq to the
        // motive target `Nat.le (c*a) (c * succ t)`.
        let minor_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = sb.fresh_local(c.nat.clone());
            let le_a_t = c.le_of(a.clone(), t.clone());
            let (ht_id, _ht) = sb.fresh_local(le_a_t.clone());
            let mul_c_t = c.mul_of(cc.clone(), t.clone());
            let ih_type = c.le_of(mul_c_a.clone(), mul_c_t.clone());
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let mul_c_t_plus_c = c.add_of(mul_c_t.clone(), cc.clone());
            let le_add = Expr::apps(le_add_right.clone(), [mul_c_t.clone(), cc.clone()]);
            let body = c.le_trans(mul_c_a.clone(), mul_c_t, mul_c_t_plus_c, ih, le_add);
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
            let e = b.mk_lam(cc_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: Real kernel-checked proof term (#3604). Replaces the legacy
        // `Declaration::Axiom` registered in `order_arith.rs::init_nat_mul_ord`.
        // `Nat.le.rec` induction on `h : a ≤ b`; refl case `Nat.le.refl (c*a)`,
        // step case chains the IH with `Nat.le_add_right` via `Nat.le_trans`.
        // No `sorry`, no self-reference; depends only on the constructive
        // `Nat.le_trans` and `Nat.le_add_right`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.le_or_lt : ∀ a b : Nat, Or (Nat.le a b) (Nat.lt b a)`.
    ///
    /// (`Nat.lt b a ≡ Nat.le (succ b) a`.) Induction on `a` via `Nat.rec.{0}`
    /// with motive `fun (s : Nat) => ∀ b, Or (Nat.le s b) (Nat.le (succ b) s)`.
    /// - base (`a = 0`): `fun b => Or.inl (Nat.zero_le b)`.
    /// - step (`a = succ s`, `ih : ∀ b, Or (s ≤ b) (succ b ≤ s)`): given `b`,
    ///   case on `b` via `Nat.casesOn`:
    ///   - `b = 0`: `Or.inr (Nat.succ_le_succ 0 s (Nat.zero_le s))`
    ///     proving `Nat.le (succ 0) (succ s)`.
    ///   - `b = succ j`: from `ih j : Or (s ≤ j) (succ j ≤ s)` map each side by
    ///     `Nat.succ_le_succ` into `Or (succ s ≤ succ j) (succ (succ j) ≤ succ s)`.
    fn register_nat_le_or_lt(&mut self, c: &NatMulCancelConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_or_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let zero_le = Expr::const_(Name::from_string("Nat.zero_le"), vec![]);
        let nat_cases_on = Expr::const_(Name::from_string("Nat.casesOn"), vec![Level::zero()]);

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());

        let type_ = {
            let body = c.or_of(
                c.le_of(a.clone(), bb.clone()),
                c.lt_of(bb.clone(), a.clone()),
            );
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // motive: fun (s : Nat) => ∀ (y : Nat), Or (Nat.le s y) (Nat.le (succ y) s)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (s_id, s) = mb.fresh_local(c.nat.clone());
            let inner = {
                let mut yb = EnvDeclBuilder::child_of(&mb);
                let (y_id, y) = yb.fresh_local(c.nat.clone());
                let body = yb.or_disj(c, &s, &y);
                let pi = yb.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), body);
                yb.finish_child(pi)
            };
            let lam = mb.mk_lam(s_id, BinderInfo::Default, c.nat.clone(), inner);
            mb.finish_child(lam)
        };

        // base (a = 0): fun (y : Nat) => Or.inl (Nat.le 0 y) (Nat.le (succ y) 0) (Nat.zero_le y)
        let base = {
            let mut zb = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = zb.fresh_local(c.nat.clone());
            let le_zero_y = c.le_of(c.zero.clone(), y.clone());
            let lt_y_zero = c.lt_of(y.clone(), c.zero.clone());
            let zero_le_y = Expr::app(zero_le.clone(), y.clone());
            let body = Expr::apps(c.or_inl.clone(), [le_zero_y, lt_y_zero, zero_le_y]);
            let lam = zb.mk_lam(y_id, BinderInfo::Default, c.nat.clone(), body);
            zb.finish_child(lam)
        };

        // step (a = succ s): fun (s : Nat) (ih : ∀ y, Or (s ≤ y) (succ y ≤ s)) (y : Nat) =>
        //   Nat.casesOn (motive := fun w => Or (succ s ≤ w) (succ w ≤ succ s)) y
        //     (zero_case) (succ_case) ...
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (s_id, s) = sb.fresh_local(c.nat.clone());
            // ih : ∀ y, Or (Nat.le s y) (Nat.le (succ y) s)
            let ih_type = {
                let mut ib = EnvDeclBuilder::child_of(&sb);
                let (y_id, y) = ib.fresh_local(c.nat.clone());
                let body = ib.or_disj(c, &s, &y);
                let pi = ib.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), body);
                ib.finish_child(pi)
            };
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let (y_id, y) = sb.fresh_local(c.nat.clone());
            let succ_s = c.succ_of(s.clone());

            // cases motive: fun (w : Nat) => Or (Nat.le (succ s) w) (Nat.le (succ w) (succ s))
            let cases_motive = {
                let mut cm = EnvDeclBuilder::child_of(&sb);
                let (w_id, w) = cm.fresh_local(c.nat.clone());
                let body = c.or_of(
                    c.le_of(succ_s.clone(), w.clone()),
                    c.lt_of(w.clone(), succ_s.clone()),
                );
                let lam = cm.mk_lam(w_id, BinderInfo::Default, c.nat.clone(), body);
                cm.finish_child(lam)
            };

            // zero case (w = 0): Or (succ s ≤ 0) (succ 0 ≤ succ s).
            //   Right: Nat.succ_le_succ 0 s (Nat.zero_le s) : Nat.le (succ 0) (succ s).
            let zero_case = {
                let left = c.le_of(succ_s.clone(), c.zero.clone());
                let right = c.lt_of(c.zero.clone(), succ_s.clone());
                let zero_le_s = Expr::app(zero_le.clone(), s.clone());
                let succ0_le_succs = c.succ_le_succ(c.zero.clone(), s.clone(), zero_le_s);
                Expr::apps(c.or_inr.clone(), [left, right, succ0_le_succs])
            };

            // succ case (w = succ j): fun (j : Nat) =>
            //   Or.rec on (ih j : Or (s ≤ j) (succ j ≤ s)) into
            //     Or (succ s ≤ succ j) (succ (succ j) ≤ succ s)
            let succ_case = {
                let mut cb = EnvDeclBuilder::child_of(&sb);
                let (j_id, j) = cb.fresh_local(c.nat.clone());
                let succ_j = c.succ_of(j.clone());

                let a_prop = c.le_of(s.clone(), j.clone()); // s ≤ j
                let b_prop = c.lt_of(j.clone(), s.clone()); // succ j ≤ s

                let goal_left = c.le_of(succ_s.clone(), succ_j.clone()); // succ s ≤ succ j
                let goal_right = c.lt_of(succ_j.clone(), succ_s.clone()); // succ (succ j) ≤ succ s
                let goal = c.or_of(goal_left.clone(), goal_right.clone());

                // const motive for Or.rec: fun (_ : Or a_prop b_prop) => goal
                let or_motive = {
                    let mut om = EnvDeclBuilder::child_of(&cb);
                    let or_ab = c.or_of(a_prop.clone(), b_prop.clone());
                    let (hh_id, _hh) = om.fresh_local(or_ab.clone());
                    let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ab, goal.clone());
                    om.finish_child(lam)
                };
                // inl case: fun (h : s ≤ j) =>
                //   Or.inl (succ s ≤ succ j) (...) (Nat.succ_le_succ s j h)
                let case_inl = {
                    let mut ic = EnvDeclBuilder::child_of(&cb);
                    let (h_id, h) = ic.fresh_local(a_prop.clone());
                    let lifted = c.succ_le_succ(s.clone(), j.clone(), h);
                    let body = Expr::apps(
                        c.or_inl.clone(),
                        [goal_left.clone(), goal_right.clone(), lifted],
                    );
                    let lam = ic.mk_lam(h_id, BinderInfo::Default, a_prop.clone(), body);
                    ic.finish_child(lam)
                };
                // inr case: fun (h : succ j ≤ s) =>
                //   Or.inr (...) (succ (succ j) ≤ succ s) (Nat.succ_le_succ (succ j) s h)
                let case_inr = {
                    let mut rc = EnvDeclBuilder::child_of(&cb);
                    let (h_id, h) = rc.fresh_local(b_prop.clone());
                    let lifted = c.succ_le_succ(succ_j.clone(), s.clone(), h);
                    let body = Expr::apps(
                        c.or_inr.clone(),
                        [goal_left.clone(), goal_right.clone(), lifted],
                    );
                    let lam = rc.mk_lam(h_id, BinderInfo::Default, b_prop.clone(), body);
                    rc.finish_child(lam)
                };

                let ih_j = Expr::app(ih.clone(), j.clone());
                let or_rec_app = Expr::apps(
                    c.or_rec.clone(),
                    [a_prop, b_prop, or_motive, case_inl, case_inr, ih_j],
                );
                let lam_j = cb.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), or_rec_app);
                cb.finish_child(lam_j)
            };

            // Lean-faithful casesOn order: motive, major, then minors.
            let cases = Expr::apps(
                nat_cases_on.clone(),
                [cases_motive, y.clone(), zero_case, succ_case],
            );
            let lam_y = sb.mk_lam(y_id, BinderInfo::Default, c.nat.clone(), cases);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, lam_y);
            let lam_s = sb.mk_lam(s_id, BinderInfo::Default, c.nat.clone(), lam_ih);
            sb.finish_child(lam_s)
        };

        let value = {
            // @Nat.rec.{0} motive base step a b
            let rec_app = Expr::apps(c.nat_rec.clone(), [motive, base, step, a.clone()]);
            let applied = Expr::app(rec_app, bb.clone());
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), applied);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked nested `Nat.rec` / `Nat.casesOn` / `Or.rec`
        // term; depends only on the constructive `Nat.zero_le` and
        // `Nat.succ_le_succ`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.mul_lt_mul_left_succ : ∀ n a b : Nat, Nat.lt a b → Nat.lt ((succ n)*a) ((succ n)*b)`.
    ///
    /// `Nat.lt x y ≡ Nat.le (succ x) y`. Write `k = succ n`. The hypothesis is
    /// `Nat.le (succ a) b`; the goal is `Nat.le (succ (k*a)) (k*b)`.
    /// - `mono : Nat.le (k * succ a) (k * b)` via `Nat.mul_le_mul_left k (succ a) b h`.
    /// - `k * succ a ≡ Nat.add (k*a) k`, and `Nat.add (k*a) k = Nat.add (k*a) (succ n)
    ///   ≡ succ (Nat.add (k*a) n)`.
    /// - `bump : Nat.le (succ (k*a)) (k * succ a)` built from
    ///   `Nat.succ_le_succ (k*a) (Nat.add (k*a) n) (Nat.le_add_right (k*a) n)`
    ///   whose type `Nat.le (succ (k*a)) (succ (Nat.add (k*a) n))` is defeq to
    ///   `Nat.le (succ (k*a)) (k * succ a)`.
    /// - `Nat.le_trans (succ (k*a)) (k * succ a) (k*b) bump mono`.
    fn register_nat_mul_lt_mul_left_succ(
        &mut self,
        c: &NatMulCancelConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_lt_mul_left_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let mul_le_mul_left = Expr::const_(Name::from_string("Nat.mul_le_mul_left"), vec![]);
        let le_add_right = Expr::const_(Name::from_string("Nat.le_add_right"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let h_type = c.lt_of(a.clone(), bb.clone()); // Nat.le (succ a) b
        let (h_id, h) = b.fresh_local(h_type.clone());

        let k = c.succ_of(n.clone());

        let type_ = {
            let concl = c.lt_of(
                c.mul_of(k.clone(), a.clone()),
                c.mul_of(k.clone(), bb.clone()),
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let k_mul_a = c.mul_of(k.clone(), a.clone());
        let succ_a = c.succ_of(a.clone());
        let k_mul_succ_a = c.mul_of(k.clone(), succ_a.clone());
        let k_mul_b = c.mul_of(k.clone(), bb.clone());

        // mono : Nat.le (k * succ a) (k * b)
        //   = Nat.mul_le_mul_left (succ a) b k (h : Nat.le (succ a) b)
        // (canonical signature: ∀ a b c, a ≤ b → c*a ≤ c*b)
        let mono = Expr::apps(
            mul_le_mul_left.clone(),
            [succ_a.clone(), bb.clone(), k.clone(), h.clone()],
        );

        // bump : Nat.le (succ (k*a)) (k * succ a)
        //   Built from Nat.succ_le_succ (k*a) (Nat.add (k*a) n) (Nat.le_add_right (k*a) n);
        //   result type Nat.le (succ (k*a)) (succ (Nat.add (k*a) n)) is defeq to
        //   Nat.le (succ (k*a)) (k * succ a) since
        //   k * succ a ≡ Nat.add (k*a) k ≡ Nat.add (k*a) (succ n) ≡ succ (Nat.add (k*a) n).
        let k_mul_a_plus_n = c.add_of(k_mul_a.clone(), n.clone());
        let le_add = Expr::apps(le_add_right.clone(), [k_mul_a.clone(), n.clone()]);
        let bump = c.succ_le_succ(k_mul_a.clone(), k_mul_a_plus_n, le_add);

        // Nat.le_trans (succ (k*a)) (k * succ a) (k*b) bump mono : Nat.le (succ (k*a)) (k*b)
        let succ_k_mul_a = c.succ_of(k_mul_a.clone());
        let body = c.le_trans(succ_k_mul_a, k_mul_succ_a, k_mul_b, bump, mono);

        let value = {
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, body);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked term; depends only on the constructive
        // `Nat.mul_le_mul_left`, `Nat.le_add_right`, `Nat.succ_le_succ`,
        // `Nat.le_trans`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.le_of_mul_le_mul_left_succ :
    ///     ∀ n a b : Nat, Nat.le ((succ n)*a) ((succ n)*b) → Nat.le a b`.
    ///
    /// Write `k = succ n`. Case on `Nat.le_or_lt a b`:
    /// - `Or.inl (h : a ≤ b)`: return `h`.
    /// - `Or.inr (h : b < a)`: strict mono `Nat.mul_lt_mul_left_succ n b a h`
    ///   gives `Nat.lt (k*b) (k*a)` i.e. `Nat.le (succ (k*b)) (k*a)`. With the
    ///   hypothesis `hle : Nat.le (k*a) (k*b)`, `Nat.le_trans` yields
    ///   `Nat.le (succ (k*b)) (k*b)` i.e. `Nat.lt (k*b) (k*b)`, contradicted by
    ///   `Nat.lt_irrefl (k*b)`; `False.elim` discharges the goal `Nat.le a b`.
    fn register_nat_le_of_mul_le_mul_left_succ(
        &mut self,
        c: &NatMulCancelConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_of_mul_le_mul_left_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let le_or_lt = Expr::const_(Name::from_string("Nat.le_or_lt"), vec![]);
        let mul_lt_mul = Expr::const_(Name::from_string("Nat.mul_lt_mul_left_succ"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let k = c.succ_of(n.clone());
        let k_mul_a = c.mul_of(k.clone(), a.clone());
        let k_mul_b = c.mul_of(k.clone(), bb.clone());
        let hle_type = c.le_of(k_mul_a.clone(), k_mul_b.clone());
        let (hle_id, hle) = b.fresh_local(hle_type.clone());

        let goal = c.le_of(a.clone(), bb.clone());

        let type_ = {
            let e = b.mk_pi(hle_id, BinderInfo::Default, hle_type.clone(), goal.clone());
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let a_prop = c.le_of(a.clone(), bb.clone()); // a ≤ b
        let b_prop = c.lt_of(bb.clone(), a.clone()); // b < a ≡ succ b ≤ a

        // const motive: fun (_ : Or (a ≤ b) (b < a)) => Nat.le a b
        let or_motive = {
            let mut om = EnvDeclBuilder::child_of(&b);
            let or_ab = c.or_of(a_prop.clone(), b_prop.clone());
            let (hh_id, _hh) = om.fresh_local(or_ab.clone());
            let lam = om.mk_lam(hh_id, BinderInfo::Default, or_ab, goal.clone());
            om.finish_child(lam)
        };
        // inl case: fun (h : a ≤ b) => h
        let case_inl = {
            let mut ic = EnvDeclBuilder::child_of(&b);
            let (h_id, h) = ic.fresh_local(a_prop.clone());
            let lam = ic.mk_lam(h_id, BinderInfo::Default, a_prop.clone(), h);
            ic.finish_child(lam)
        };
        // inr case: fun (h : b < a) => False.elim (Nat.le a b) (contradiction)
        let case_inr = {
            let mut rc = EnvDeclBuilder::child_of(&b);
            let (h_id, h) = rc.fresh_local(b_prop.clone());
            // strict : Nat.lt (k*b) (k*a) ≡ Nat.le (succ (k*b)) (k*a)
            let strict = Expr::apps(mul_lt_mul.clone(), [n.clone(), bb.clone(), a.clone(), h]);
            // Nat.le_trans (succ (k*b)) (k*a) (k*b) strict hle : Nat.le (succ (k*b)) (k*b)
            //   ≡ Nat.lt (k*b) (k*b)
            let succ_k_mul_b = c.succ_of(k_mul_b.clone());
            let lt_self = c.le_trans(
                succ_k_mul_b,
                k_mul_a.clone(),
                k_mul_b.clone(),
                strict,
                hle.clone(),
            );
            // Nat.lt_irrefl (k*b) lt_self : False
            let absurd = Expr::apps(c.lt_irrefl_thm.clone(), [k_mul_b.clone(), lt_self]);
            // False.elim (Nat.le a b) absurd : Nat.le a b
            let body = Expr::apps(c.false_elim.clone(), [goal.clone(), absurd]);
            let lam = rc.mk_lam(h_id, BinderInfo::Default, b_prop.clone(), body);
            rc.finish_child(lam)
        };

        let major = Expr::apps(le_or_lt.clone(), [a.clone(), bb.clone()]);
        let or_rec_app = Expr::apps(
            c.or_rec.clone(),
            [a_prop, b_prop, or_motive, case_inl, case_inr, major],
        );

        let value = {
            let e = b.mk_lam(hle_id, BinderInfo::Default, hle_type, or_rec_app);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: kernel-checked `Or.rec` term; depends only on the
        // constructive `Nat.le_or_lt`, `Nat.mul_lt_mul_left_succ`,
        // `Nat.le_trans`, `Nat.lt_irrefl`, and `False.elim`.
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// `Nat.mul_left_cancel_succ :
    ///     ∀ n a b : Nat, Eq ((succ n)*a) ((succ n)*b) → Eq a b`.
    ///
    /// Write `k = succ n`. From `H : k*a = k*b` build `Nat.le (k*a) (k*b)` and
    /// `Nat.le (k*b) (k*a)` by `Eq.subst` transport of `Nat.le.refl (k*a)`, then
    /// run `Nat.le_of_mul_le_mul_left_succ` in both directions and close with
    /// `Nat.le_antisymm`.
    fn register_nat_mul_left_cancel_succ_theorem(
        &mut self,
        c: &NatMulCancelConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.mul_left_cancel_succ");
        // Replace the legacy Axiom if present, but no-op if already a Theorem.
        if matches!(
            self.get_const(&name).map(|i| i.kind),
            Some(crate::env::types::ConstantKind::Theorem)
        ) {
            return Ok(());
        }

        let le_of_mul = Expr::const_(Name::from_string("Nat.le_of_mul_le_mul_left_succ"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let k = c.succ_of(n.clone());
        let k_mul_a = c.mul_of(k.clone(), a.clone());
        let k_mul_b = c.mul_of(k.clone(), bb.clone());
        let h_type = c.eq_of(k_mul_a.clone(), k_mul_b.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());

        let type_ = {
            let concl = c.eq_of(a.clone(), bb.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // le_ab_prod : Nat.le (k*a) (k*b)
        //   = Eq.subst (motive := fun z => Nat.le (k*a) z) (k*a) (k*b) H (Nat.le.refl (k*a))
        let le_ab_prod = {
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = mb.fresh_local(c.nat.clone());
                let body = c.le_of(k_mul_a.clone(), z);
                let lam = mb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                mb.finish_child(lam)
            };
            let refl_le = c.le_refl_ctor_app(k_mul_a.clone());
            Expr::apps(
                c.eq_subst.clone(),
                [
                    c.nat.clone(),
                    motive,
                    k_mul_a.clone(),
                    k_mul_b.clone(),
                    h.clone(),
                    refl_le,
                ],
            )
        };
        // le_ba_prod : Nat.le (k*b) (k*a)
        //   = Eq.subst (motive := fun z => Nat.le z (k*a)) (k*a) (k*b) H (Nat.le.refl (k*a))
        let le_ba_prod = {
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = mb.fresh_local(c.nat.clone());
                let body = c.le_of(z, k_mul_a.clone());
                let lam = mb.mk_lam(z_id, BinderInfo::Default, c.nat.clone(), body);
                mb.finish_child(lam)
            };
            let refl_le = c.le_refl_ctor_app(k_mul_a.clone());
            Expr::apps(
                c.eq_subst.clone(),
                [
                    c.nat.clone(),
                    motive,
                    k_mul_a.clone(),
                    k_mul_b.clone(),
                    h.clone(),
                    refl_le,
                ],
            )
        };

        // a ≤ b and b ≤ a via the cancellation lemma.
        let a_le_b = Expr::apps(
            le_of_mul.clone(),
            [n.clone(), a.clone(), bb.clone(), le_ab_prod],
        );
        let b_le_a = Expr::apps(
            le_of_mul.clone(),
            [n.clone(), bb.clone(), a.clone(), le_ba_prod],
        );

        // Nat.le_antisymm a b (a ≤ b) (b ≤ a) : Eq a b
        let body = Expr::apps(
            c.le_antisymm_thm.clone(),
            [a.clone(), bb.clone(), a_le_b, b_le_a],
        );

        let value = {
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, body);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: Real kernel-checked proof term (#3604). Replaces the legacy
        // `Declaration::Axiom` registration in `data_types_nat_lemmas.rs`. From
        // the product equality `H : (succ n)*a = (succ n)*b`, `Eq.subst`
        // transports `Nat.le.refl` into both product inequalities, the
        // constructive `Nat.le_of_mul_le_mul_left_succ` cancels the positive
        // multiplier in each direction, and `Nat.le_antisymm` concludes `a = b`.
        // No `sorry`, no self-reference, no domain-axiom dependency (every
        // helper is constructive).
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

impl EnvDeclBuilder {
    /// `Or (Nat.le s y) (Nat.le (succ y) s)` — the `Nat.le_or_lt` disjunction
    /// body, reused by the motive and the induction hypothesis type.
    fn or_disj(&self, c: &NatMulCancelConsts, s: &Expr, y: &Expr) -> Expr {
        c.or_of(c.le_of(s.clone(), y.clone()), c.lt_of(y.clone(), s.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    fn build_env() -> Environment {
        let mut env = Environment::new();
        env.register_nat_mul_left_cancel_succ_proof()
            .expect("registration should succeed");
        env
    }

    /// Every registered lemma type-checks and is a Theorem with empty axiom
    /// closure (Constructive).
    #[test]
    fn test_nat_mul_cancel_all_lemmas_constructive() {
        let env = build_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for target in [
            "Nat.zero_le",
            "Nat.le_add_right",
            "Nat.mul_le_mul_left",
            "Nat.le_or_lt",
            "Nat.mul_lt_mul_left_succ",
            "Nat.le_of_mul_le_mul_left_succ",
            "Nat.mul_left_cancel_succ",
        ] {
            let info = env
                .get_const(&Name::from_string(target))
                .unwrap_or_else(|| panic!("{target} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{target} must be a Theorem"
            );
            assert!(info.value.is_some(), "{target} must retain its proof value");

            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(target), vec![]))
                .unwrap_or_else(|err| panic!("{target} should type-check: {err:?}"));

            let deps = env
                .axiom_deps(&Name::from_string(target))
                .unwrap_or_else(|| panic!("{target} axiom_deps should be Some"));
            let domain_deps: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
            assert!(
                domain_deps.is_empty(),
                "{target} must have empty axiom closure, got {:?}",
                domain_deps
            );
            assert_eq!(
                env.proof_quality(&Name::from_string(target))
                    .unwrap_or_else(|| panic!("{target} proof quality should compute")),
                ProofQuality::Constructive,
                "{target} must be Constructive"
            );
        }
    }

    /// `Nat.mul_left_cancel_succ` is no longer an Axiom; the registration is
    /// idempotent.
    #[test]
    fn test_nat_mul_left_cancel_succ_registered_as_theorem() {
        let mut env = build_env();
        env.register_nat_mul_left_cancel_succ_proof()
            .expect("idempotent re-registration");
        let info = env
            .get_const(&Name::from_string("Nat.mul_left_cancel_succ"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }

    /// After peeling four λ binders (n, a, b, H), the cancellation proof root is
    /// `Nat.le_antisymm` — guards against an `Eq.refl` / axiom-reference
    /// masquerade.
    #[test]
    fn test_nat_mul_left_cancel_succ_proof_uses_le_antisymm() {
        let env = build_env();
        let info = env
            .get_const(&Name::from_string("Nat.mul_left_cancel_succ"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut cur = value.clone();
        for _ in 0..4 {
            cur = match cur.kind() {
                ExprKind::Lam(_, _, body) => (**body).clone(),
                k => panic!("expected λ binder, got {:?}", k),
            };
        }
        let mut head = cur;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(name, _) => assert_eq!(
                name.to_string(),
                "Nat.le_antisymm",
                "cancellation proof root must be Nat.le_antisymm"
            ),
            k => panic!("expected Const(Nat.le_antisymm, ..), got {:?}", k),
        }
    }

    /// `Nat.mul_le_mul_left`'s proof root (after λ peeling) is `Nat.le.rec`,
    /// proving the monotonicity helper is built by induction rather than
    /// trivially.
    #[test]
    fn test_nat_mul_le_mul_left_proof_uses_le_rec() {
        let env = build_env();
        let info = env
            .get_const(&Name::from_string("Nat.mul_le_mul_left"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem has value");
        let mut cur = value.clone();
        for _ in 0..4 {
            cur = match cur.kind() {
                ExprKind::Lam(_, _, body) => (**body).clone(),
                k => panic!("expected λ binder, got {:?}", k),
            };
        }
        let mut head = cur;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(name, _) => assert_eq!(
                name.to_string(),
                "Nat.le.rec",
                "Nat.mul_le_mul_left proof root must be Nat.le.rec"
            ),
            k => panic!("expected Const(Nat.le.rec, ..), got {:?}", k),
        }
    }
}
