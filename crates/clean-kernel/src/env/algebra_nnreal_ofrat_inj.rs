// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the `NNReal → Rat` value-recovery bridge.
//!
//! # Why this module exists (the M1 cross-back)
//!
//! `algebra_nnreal_le.rs` lands the FORWARD `ofRat` order bridge
//! (`NNReal.ofRat_le_ofRat : Rat.le a b → NNReal.le (ofRat a)(ofRat b)`) and
//! names the unbuilt blocker for the REVERSE: an Archimedean
//! `le_of_forall_lt_add` AT THE RAT LEVEL. The §10.6 M1 norm identity needs to
//! cross a materialised `NNReal` equation BACK to a `Rat` equation. A total
//! `NNReal.toRat` is UNSOUND (it would have to pick a representative); the sound
//! route is `ofRat` INJECTIVITY, which is exactly what the reverse order bridge
//! buys us.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.le_of_forall_lt_add : ∀ a b : Rat,
//!       (∀ e : Rat, Rat.lt Rat.zero e → Rat.lt a (Rat.add b e)) → Rat.le a b`
//!   — the Archimedean reverse. Proof by `Classical.em (a ≤ b)` + `Rat.le_total`
//!   (the same constructive contradiction skeleton as `Rat.le_of_cube_le_cube`):
//!   in the `b < a` corner, instantiate the hypothesis at `e := a − b > 0`
//!   (`Rat.sub_pos_of_lt`), obtaining `a < b + (a − b)`; rewrite `b + (a − b) = a`
//!   (`Rat.add_comm` + `Rat.sub_add_cancel`) to get `a < a`, which
//!   `Rat.lt_iff_le_not_le` + `Rat.le_refl` reject.
//!
//! - `NNReal.ofRat_inj : ∀ (a b : Rat)(ha : 0 ≤ a)(hb : 0 ≤ b),
//!       Eq NNReal (NNReal.ofRat a ha)(NNReal.ofRat b hb) → Eq Rat a b`
//!   — `ofRat` injectivity. From the `NNReal` equation, transport
//!   `NNReal.le.refl` along it (both directions) to get `NNReal.le (ofRat a)(ofRat b)`
//!   AND `NNReal.le (ofRat b)(ofRat a)`. The reverse order bridge below extracts
//!   `Rat.le a b` and `Rat.le b a` from these, then `Rat.le_antisymm` concludes
//!   `Eq Rat a b`.
//!
//!   The extraction `NNReal.le (ofRat a)(ofRat b) → Rat.le a b` is the
//!   `NNReal`-to-`Rat` half: `NNReal.le (ofRat a)(ofRat b)` ι-reduces (Quot.lift
//!   computation over the two constant `Quot.mk` sequences) to
//!   `∀ ε>0, ∃ N, ∀ n≥N, a < b + ε`; `nnle_ofrat_to_forall` strips the `∃N ∀n`
//!   wrapper (the body is `n`-independent) to the `∀ ε>0, a < b + ε` hypothesis
//!   of `Rat.le_of_forall_lt_add`.
//!
//! Each theorem is `Declaration::Theorem`, `ProofQuality::Constructive`, with an
//! empty admitted-axiom closure (foundational only). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`. FORBIDDEN here: a total
//! `NNReal.toRat`, `Rat.dist`, `Real`/`Real.sqrt`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the `ofRat` injectivity bridge.
pub(crate) struct OfRatInjConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_sub: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    // Rat order lemmas (all foundational-only).
    rat_le_total: Expr,
    rat_le_refl: Expr,
    rat_le_antisymm: Expr,
    rat_lt_iff: Expr,
    rat_add_comm: Expr,
    rat_sub_add_cancel: Expr,
    rat_sub_pos_of_lt: Expr,
    rat_le_of_forall_lt_add: Expr,
    // Logic.
    and_c: Expr,
    and_intro: Expr,
    and_right: Expr,
    iff_mp: Expr,
    iff_mpr: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    not_c: Expr,
    classical_em: Expr,
    false_c: Expr,
    false_elim0: Expr,
    or_c: Expr,
    or_rec0: Expr,
    // Nat / Exists (existential stripping of the reduced `NNReal.le` body).
    nat: Expr,
    nat_le: Expr,
    nat_le_refl: Expr,
    exists_elim: Expr,
    // NNReal carrier.
    nnreal: Expr,
    nnreal_le: Expr,
    nnreal_of_rat: Expr,
    nnreal_le_refl: Expr,
    // Eq.{1}.
    eq1: Expr,
    eq_subst1: Expr,
}

impl OfRatInjConsts {
    pub(crate) fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_add: k("Rat.add"),
            rat_sub: k("Rat.sub"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_le_total: k("Rat.le_total"),
            rat_le_refl: k("Rat.le_refl"),
            rat_le_antisymm: k("Rat.le_antisymm"),
            rat_lt_iff: k("Rat.lt_iff_le_not_le"),
            rat_add_comm: k("Rat.add_comm"),
            rat_sub_add_cancel: k("Rat.sub_add_cancel"),
            rat_sub_pos_of_lt: k("Rat.sub_pos_of_lt"),
            rat_le_of_forall_lt_add: k("Rat.le_of_forall_lt_add"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_right: k("And.right"),
            iff_mp: k("Iff.mp"),
            iff_mpr: k("Iff.mpr"),
            #[cfg(test)]
            not_c: k("Not"),
            classical_em: k("Classical.em"),
            false_c: k("False"),
            false_elim0: Expr::const_(Name::from_string("False.elim"), vec![l0]),
            or_c: k("Or"),
            or_rec0: k("Or.rec"),
            nat: k("Nat"),
            nat_le: k("Nat.le"),
            nat_le_refl: k("Nat.le.refl"),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![l1.clone()]),
            nnreal: k("NNReal"),
            nnreal_le: k("NNReal.le"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_le_refl: k("NNReal.le.refl"),
            eq1: kl("Eq"),
            eq_subst1: kl("Eq.subst"),
        }
    }

    // ── Rat term constructors ────────────────────────────────────────────────
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nonneg(&self, a: Expr) -> Expr {
        self.le(self.rat_zero.clone(), a)
    }

    // ── Logic constructors ───────────────────────────────────────────────────
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p, q, hp, hq])
    }
    fn and_right(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_right.clone(), [p, q, h])
    }
    fn iff_mp(&self, lhs: Expr, rhs: Expr, hiff: Expr, h: Expr) -> Expr {
        Expr::apps(self.iff_mp.clone(), [lhs, rhs, hiff, h])
    }
    fn iff_mpr(&self, lhs: Expr, rhs: Expr, hiff: Expr, h: Expr) -> Expr {
        Expr::apps(self.iff_mpr.clone(), [lhs, rhs, hiff, h])
    }
    fn lt_iff(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt_iff.clone(), [a, b])
    }
    /// `Not P` as a `Pi P False` (matches `Classical.em`'s negative branch shape).
    fn not_pi(&self, parent: &EnvDeclBuilder, p: Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (x_id, _) = ch.fresh_local(p.clone());
        ch.finish_child(ch.mk_pi(x_id, BinderInfo::Default, p, self.false_c.clone()))
    }
    fn false_elim(&self, goal: Expr, h_false: Expr) -> Expr {
        Expr::apps(self.false_elim0.clone(), [goal, h_false])
    }
    fn le_total(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le_total.clone(), [a, b])
    }
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    /// `@Or.rec.{0} p q (fun _ => goal) h_left h_right h_or : goal` — non-dependent
    /// case split (`goal` is a `Prop`).
    fn or_elim(
        &self,
        parent: &EnvDeclBuilder,
        p: Expr,
        q: Expr,
        goal: Expr,
        h_or: Expr,
        h_left: Expr,
        h_right: Expr,
    ) -> Expr {
        let or_ty = Expr::apps(self.or_c.clone(), [p.clone(), q.clone()]);
        let motive = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let (h_id, _) = ch.fresh_local(or_ty.clone());
            ch.finish_child(ch.mk_lam(h_id, BinderInfo::Default, or_ty, goal))
        };
        Expr::apps(self.or_rec0.clone(), [p, q, motive, h_left, h_right, h_or])
    }

    // ── Eq.{1} over Rat / NNReal ─────────────────────────────────────────────
    fn rat_eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    fn nn_eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nnreal.clone(), a, b])
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h : motive b`.
    fn rat_subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@Eq.subst.{1} NNReal motive a b h_eq h : motive b`.
    fn nn_subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a, b, h_eq, h],
        )
    }

    // ── NNReal constructors ──────────────────────────────────────────────────
    fn ofrat(&self, x: &Expr, h: &Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x.clone(), h.clone()])
    }
    fn nnle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a, b])
    }

    // ── Nat / Exists (existential stripping) ─────────────────────────────────
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `Nat.le.refl n : Nat.le n n`.
    fn nat_le_refl(&self, n: Expr) -> Expr {
        Expr::app(self.nat_le_refl.clone(), n)
    }
    /// `@Exists.elim.{1} Nat p goal h_ex f : goal`.
    fn exists_elim_nat(&self, p: Expr, goal: Expr, h_ex: Expr, f: Expr) -> Expr {
        Expr::apps(
            self.exists_elim.clone(),
            [self.nat.clone(), p, goal, h_ex, f],
        )
    }

    /// The reduced `∃N`-predicate of `NNReal.le (ofRat a)(ofRat b)`:
    ///   `fun N => ∀ n, Nat.le N n → Rat.lt a (Rat.add b e)`.
    /// (The reduced body `val (seq (const (NNRat.ofRat a)) n) < val (…b…) n + e`
    /// is DEFEQ to `a < b + e` because the constant sequence's `val ∘ seq` ι-reduces.)
    fn reduced_pred(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, e: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, _n) = bn.fresh_local(self.nat.clone());
        let inner = self.reduced_pred_at(&bn, a, b, e, &_n);
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner))
    }

    /// `reduced_pred` fully applied at the cap `N`:
    ///   `∀ n, Nat.le N n → Rat.lt a (Rat.add b e)`.
    fn reduced_pred_at(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        b: &Expr,
        e: &Expr,
        cap: &Expr,
    ) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = bn.fresh_local(self.nat.clone());
        let hle = self.nat_le(cap.clone(), m.clone());
        let (hle_id, _hle) = bn.fresh_local(hle.clone());
        let concl = self.lt(a.clone(), self.add(b.clone(), e.clone()));
        let inner = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        bn.finish_child(bn.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), inner))
    }
}

/// Convert `h_le : NNReal.le (ofRat a ha)(ofRat b hb)` to the
/// `Rat.le_of_forall_lt_add` hypothesis `∀ e, 0<e → a < b+e`.
///
/// `NNReal.le (ofRat a)(ofRat b)` ι-reduces (binary `Quot.lift` over the two
/// `Quot.mk (const …)` arguments) to
///   `∀ ε, 0<ε → ∃ N, ∀ n, N≤n → val(seq(const(ofRat a)) n) < val(…b…) n + ε`,
/// and the constant-sequence `val ∘ seq` ι-reduces to `a` / `b`. So instantiating
/// `h_le` at `(e, he)` gives `∃ N, ∀ n, N≤n → a < b+e`; strip it by `Exists.elim`,
/// applying the witness predicate at `n := N` with `Nat.le.refl N`.
fn nnle_ofrat_to_forall(
    c: &OfRatInjConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    b: &Expr,
    h_le: &Expr,
) -> Expr {
    let mut bb = EnvDeclBuilder::child_of(parent);
    let (e_id, e) = bb.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), e.clone());
    let (hpos_id, hpos) = bb.fresh_local(hpos_ty.clone());

    // h_ex : ∃ N, ∀ n, N≤n → a < b+e   (= h_le e he, after ι-reduction).
    let h_ex = Expr::apps(h_le.clone(), [e.clone(), hpos]);
    let goal = c.lt(a.clone(), c.add(b.clone(), e.clone())); // a < b+e
    let pred = c.reduced_pred(&bb, a, b, &e);

    // f : ∀ N, (∀ n, N≤n → a<b+e) → a<b+e := fun N hN => hN N (Nat.le.refl N).
    let f = {
        let mut bf = EnvDeclBuilder::child_of(&bb);
        let (n_id, n_cap) = bf.fresh_local(c.nat.clone());
        let hn_ty = c.reduced_pred_at(&bf, a, b, &e, &n_cap);
        let (hn_id, hn) = bf.fresh_local(hn_ty.clone());
        let body = Expr::apps(hn, [n_cap.clone(), c.nat_le_refl(n_cap.clone())]);
        let lam = bf.mk_lam(hn_id, BinderInfo::Default, hn_ty, body);
        let lam = bf.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), lam);
        bf.finish_child(lam)
    };

    let stripped = c.exists_elim_nat(pred, goal, h_ex, f);
    let lam = bb.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, stripped);
    let lam = bb.mk_lam(e_id, BinderInfo::Default, c.rat.clone(), lam);
    bb.finish_child(lam)
}

impl Environment {
    /// Register `Rat.le_of_forall_lt_add` and `NNReal.ofRat_inj`. Idempotent;
    /// foundational-only closure. Pulls in the Rat order toolkit, classical
    /// `em`, and the forward `NNReal.le` carrier.
    pub fn init_algebra_nnreal_ofrat_inj(&mut self) -> Result<(), EnvError> {
        self.init_classical()?; // Classical.em (+ Or, Or.rec, False, False.elim)
        self.register_rat_order_proofs()?; // Rat.le_total, le_refl, le_antisymm, lt_iff_le_not_le
                                           // `init_algebra_nnreal_le` + `init_boolean_analysis_order_toolkit_b1b`
                                           // must precede `register_rat_add_comm_proof`: they seed the legacy
                                           // `Rat.num`/`Rat.denom` projections its kernel-checked proof body
                                           // reduces through (after `register_rat_order_proofs` runs alone, the
                                           // `init_rat_arith` idempotence flag is already set, so add_comm's own
                                           // chain no longer registers them — running these first restores them).
        self.init_algebra_nnreal_le()?; // NNReal.le, NNReal.le.refl, NNReal.ofRat
        self.init_boolean_analysis_order_toolkit_b1b()?; // Rat.sub_add_cancel, Rat.sub_pos_of_lt
        self.register_rat_add_comm_proof()?; // Rat.add_comm
        self.init_eq()?;

        let c = OfRatInjConsts::new();
        self.register_rat_le_of_forall_lt_add(&c)?;
        self.register_nnreal_ofrat_inj(&c)?;
        Ok(())
    }

    /// `Rat.le_of_forall_lt_add : ∀ a b, (∀ e, 0<e → a < b+e) → a ≤ b`.
    fn register_rat_le_of_forall_lt_add(&mut self, c: &OfRatInjConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_of_forall_lt_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let hyp_ty = forall_lt_add_hyp(c, &b, &a, &bv);
            let (h_id, _h) = b.fresh_local(hyp_ty.clone());
            let concl = c.le(a.clone(), bv.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp_ty, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_le_of_forall_lt_add(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.ofRat_inj : ∀ a b ha hb, Eq NNReal (ofRat a ha)(ofRat b hb) → Eq Rat a b`.
    fn register_nnreal_ofrat_inj(&mut self, c: &OfRatInjConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.ofRat_inj");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let ha_ty = c.nonneg(a.clone());
            let (ha_id, ha) = b.fresh_local(ha_ty.clone());
            let hb_ty = c.nonneg(bv.clone());
            let (hb_id, hb) = b.fresh_local(hb_ty.clone());
            let heq_ty = c.nn_eq(c.ofrat(&a, &ha), c.ofrat(&bv, &hb));
            let (heq_id, _heq) = b.fresh_local(heq_ty.clone());
            let concl = c.rat_eq(a.clone(), bv.clone());
            let e = b.mk_pi(heq_id, BinderInfo::Default, heq_ty, concl);
            let e = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, e);
            let e = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_ofrat_inj(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The hypothesis type of `le_of_forall_lt_add`:
///   `∀ e : Rat, Rat.lt Rat.zero e → Rat.lt a (Rat.add b e)`.
fn forall_lt_add_hyp(c: &OfRatInjConsts, parent: &EnvDeclBuilder, a: &Expr, b: &Expr) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (e_id, e) = bn.fresh_local(c.rat.clone());
    let hpos = c.lt(c.rat_zero.clone(), e.clone());
    let (hpos_id, _hpos) = bn.fresh_local(hpos.clone());
    let concl = c.lt(a.clone(), c.add(b.clone(), e.clone()));
    let inner = bn.mk_pi(hpos_id, BinderInfo::Default, hpos, concl);
    bn.finish_child(bn.mk_pi(e_id, BinderInfo::Default, c.rat.clone(), inner))
}

/// Proof term for `Rat.le_of_forall_lt_add`.
///
/// `Classical.em (a ≤ b)` splits the goal:
///   - positive `a ≤ b`: return it.
///   - negative `¬(a ≤ b)`: `Rat.le_total a b` gives `a≤b ∨ b≤a`; the left
///     branch returns `a≤b`, the right branch (`b≤a`) derives `False`:
///       `b < a := Iff.mpr (lt_iff b a) ⟨hba, hn⟩`
///       `0 < a−b := sub_pos_of_lt b a (b<a)`
///       `a < b + (a−b) := H (a−b) (0 < a−b)`
///       `b + (a−b) = a := trans (add_comm b (a−b)) (sub_add_cancel b a)`
///       `a < a := (b+(a−b)=a) ▸ (a < b+(a−b))`
///       `(a≤a) ∧ ¬(a≤a) := Iff.mp (lt_iff a a) (a<a)`; apply `¬(a≤a)` to
///       `le_refl a` for `False`.
fn build_le_of_forall_lt_add(c: &OfRatInjConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let hyp_ty = forall_lt_add_hyp(c, &b, &a, &bv);
    let (h_id, h) = b.fresh_local(hyp_ty.clone());

    let le_ab = c.le(a.clone(), bv.clone()); // a ≤ b  (goal)
    let not_le_ab = c.not_pi(&b, le_ab.clone()); // ¬(a ≤ b)
    let le_ba = c.le(bv.clone(), a.clone()); // b ≤ a

    // Classical.em (a ≤ b).
    let h_em = Expr::app(c.classical_em.clone(), le_ab.clone());

    // positive branch: λ (h : a≤b) => h.
    let em_pos = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (hp_id, hp) = ch.fresh_local(le_ab.clone());
        ch.finish_child(ch.mk_lam(hp_id, BinderInfo::Default, le_ab.clone(), hp))
    };

    // negative branch: λ (hn : ¬(a≤b)) => le_total split.
    let em_neg = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (hn_id, hn) = ch.fresh_local(not_le_ab.clone());
        let h_total = c.le_total(a.clone(), bv.clone());

        // total-left: λ (h:a≤b) => h.
        let tot_left = {
            let mut d = EnvDeclBuilder::child_of(&ch);
            let (hl_id, hl) = d.fresh_local(le_ab.clone());
            d.finish_child(d.mk_lam(hl_id, BinderInfo::Default, le_ab.clone(), hl))
        };

        // total-right: λ (hba:b≤a) => False.elim (a≤b) (...).
        let tot_right = {
            let mut d = EnvDeclBuilder::child_of(&ch);
            let (hba_id, hba) = d.fresh_local(le_ba.clone());

            // h_lt_ba : b < a = Iff.mpr (lt_iff b a)(And.intro (b≤a)(¬(a≤b)) hba hn).
            let not_le_ab_d = c.not_pi(&d, le_ab.clone());
            let and_ty = c.and_ty(le_ba.clone(), not_le_ab_d.clone());
            let and_proof = c.and_intro(le_ba.clone(), not_le_ab_d.clone(), hba, hn.clone());
            let lt_ba = c.lt(bv.clone(), a.clone());
            let h_lt_ba = c.iff_mpr(lt_ba, and_ty, c.lt_iff(bv.clone(), a.clone()), and_proof);

            // h_pos : 0 < a − b = sub_pos_of_lt b a (b<a).
            let amb = c.sub(a.clone(), bv.clone()); // a − b = Rat.sub a b
            let h_pos = Expr::apps(
                c.rat_sub_pos_of_lt.clone(),
                [bv.clone(), a.clone(), h_lt_ba],
            );

            // h_H : a < b + (a−b) = H (a−b) h_pos.
            let b_plus_amb = c.add(bv.clone(), amb.clone());
            let h_big = Expr::apps(h.clone(), [amb.clone(), h_pos]);

            // h_eq : b + (a−b) = a, via add_comm + sub_add_cancel.
            //   add_comm b (a−b) : b + (a−b) = (a−b) + b
            //   sub_add_cancel b a : (a−b) + b = a   [ (a − b) + b = a ]
            let amb_plus_b = c.add(amb.clone(), bv.clone());
            let h_comm = Expr::apps(c.rat_add_comm.clone(), [bv.clone(), amb.clone()]); // b+(a−b) = (a−b)+b
            let h_sac = Expr::apps(c.rat_sub_add_cancel.clone(), [bv.clone(), a.clone()]); // (a−b)+b = a
                                                                                           // chain via Eq.subst: from h_big : a < b+(a−b), rewrite b+(a−b) → a.
                                                                                           // First step b+(a−b) → (a−b)+b, then (a−b)+b → a.
                                                                                           // motive_1 : fun t => a < t.
            let motive_lt = |parent: &EnvDeclBuilder| -> Expr {
                let mut mb = EnvDeclBuilder::child_of(parent);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.lt(a.clone(), t);
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            // a < (a−b)+b.
            let h_mid = c.rat_subst(
                motive_lt(&d),
                b_plus_amb.clone(),
                amb_plus_b.clone(),
                h_comm,
                h_big,
            );
            // a < a.
            let h_aa = c.rat_subst(motive_lt(&d), amb_plus_b, a.clone(), h_sac, h_mid);

            // (a≤a) ∧ ¬(a≤a) = Iff.mp (lt_iff a a)(a<a); contradiction with le_refl a.
            let le_aa = c.le(a.clone(), a.clone());
            let not_le_aa = c.not_pi(&d, le_aa.clone());
            let rhs_aa = c.and_ty(le_aa.clone(), not_le_aa.clone());
            let mp_aa = c.iff_mp(
                c.lt(a.clone(), a.clone()),
                rhs_aa,
                c.lt_iff(a.clone(), a.clone()),
                h_aa,
            );
            let h_not_le = c.and_right(le_aa.clone(), not_le_aa.clone(), mp_aa);
            let h_false = Expr::app(h_not_le, c.le_refl(a.clone()));

            let body = c.false_elim(le_ab.clone(), h_false);
            d.finish_child(d.mk_lam(hba_id, BinderInfo::Default, le_ba.clone(), body))
        };

        let body = c.or_elim(
            &ch,
            le_ab.clone(),
            le_ba.clone(),
            le_ab.clone(),
            h_total,
            tot_left,
            tot_right,
        );
        ch.finish_child(ch.mk_lam(hn_id, BinderInfo::Default, not_le_ab.clone(), body))
    };

    let body = c.or_elim(
        &b,
        le_ab.clone(),
        not_le_ab.clone(),
        le_ab.clone(),
        h_em,
        em_pos,
        em_neg,
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp_ty, body);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e))
}

/// Proof term for `NNReal.ofRat_inj`.
///
/// From `heq : Eq NNReal (ofRat a)(ofRat b)`, build the two `NNReal.le`
/// directions by transporting `NNReal.le.refl (ofRat a)` along `heq` (forward)
/// and along its symmetric image (reverse). Each `NNReal.le (ofRat x)(ofRat y)`
/// is stripped by `nnle_ofrat_to_forall` to `∀ ε>0, x < y + ε`, which
/// `Rat.le_of_forall_lt_add x y` consumes. Then `Rat.le_antisymm a b` from the
/// two `Rat.le`s.
fn build_ofrat_inj(c: &OfRatInjConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let ha_ty = c.nonneg(a.clone());
    let (ha_id, ha) = b.fresh_local(ha_ty.clone());
    let hb_ty = c.nonneg(bv.clone());
    let (hb_id, hb) = b.fresh_local(hb_ty.clone());
    let oa = c.ofrat(&a, &ha);
    let ob = c.ofrat(&bv, &hb);
    let heq_ty = c.nn_eq(oa.clone(), ob.clone());
    let (heq_id, heq) = b.fresh_local(heq_ty.clone());

    // h_le_ab : NNReal.le (ofRat a)(ofRat b).
    //   Transport `NNReal.le.refl (ofRat a) : NNReal.le (ofRat a)(ofRat a)`
    //   along heq : (ofRat a) = (ofRat b), under motive `fun z => NNReal.le (ofRat a) z`.
    let refl_a = Expr::app(c.nnreal_le_refl.clone(), oa.clone()); // NNReal.le (ofRat a)(ofRat a)
    let motive_ab = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnle(oa.clone(), z);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let h_le_ab = c.nn_subst(motive_ab, oa.clone(), ob.clone(), heq.clone(), refl_a);

    // h_le_ba : NNReal.le (ofRat b)(ofRat a).
    //   Transport `NNReal.le.refl (ofRat a) : NNReal.le (ofRat a)(ofRat a)`
    //   along heq, under motive `fun z => NNReal.le z (ofRat a)`.
    let refl_a2 = Expr::app(c.nnreal_le_refl.clone(), oa.clone());
    let motive_ba = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnle(z, oa.clone());
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let h_le_ba = c.nn_subst(motive_ba, oa.clone(), ob.clone(), heq.clone(), refl_a2);

    // Extract Rat.le via the reverse bridge. `NNReal.le (ofRat a)(ofRat b)`
    // ι-reduces to `∀ε>0 ∃N ∀n≥N, a < b+ε`; `nnle_ofrat_to_forall` strips the
    // `∃N ∀n` wrapper to the `∀ε>0, a < b+ε` hypothesis of `le_of_forall_lt_add`.
    let fa_ab = nnle_ofrat_to_forall(c, &b, &a, &bv, &h_le_ab); // ∀ε>0, a < b+ε
    let fa_ba = nnle_ofrat_to_forall(c, &b, &bv, &a, &h_le_ba); // ∀ε>0, b < a+ε
    let h_rat_ab = Expr::apps(
        c.rat_le_of_forall_lt_add.clone(),
        [a.clone(), bv.clone(), fa_ab],
    ); // Rat.le a b
    let h_rat_ba = Expr::apps(
        c.rat_le_of_forall_lt_add.clone(),
        [bv.clone(), a.clone(), fa_ba],
    ); // Rat.le b a

    // Rat.le_antisymm a b (a≤b)(b≤a) : Eq Rat a b.
    let antisymm = Expr::apps(
        c.rat_le_antisymm.clone(),
        [a.clone(), bv.clone(), h_rat_ab, h_rat_ba],
    );

    let e = b.mk_lam(heq_id, BinderInfo::Default, heq_ty, antisymm);
    let e = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, e);
    let e = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["Rat.le_of_forall_lt_add", "NNReal.ofRat_inj"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_ofrat_inj()
            .expect("init_algebra_nnreal_ofrat_inj");
        env.init_algebra_nnreal_ofrat_inj().expect("idempotent");
        env
    }

    #[test]
    fn test_ofrat_inj_lemmas_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
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
    fn test_ofrat_inj_lemmas_constructive_empty_closure() {
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
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
