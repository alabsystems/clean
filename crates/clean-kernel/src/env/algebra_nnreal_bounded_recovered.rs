// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage B2: `NNReal.CauSeq` boundedness.
//!
//! # Why this module exists
//!
//! This is THE precise rung the last pass stopped at (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md`, Stage B2 remaining rung 2):
//! *every Cauchy `NNReal.CauSeq` is bounded above by some `NNRat`*. The
//! `NNReal.mul` `Quot.lift` respect proof factors its cross-term
//! `|fg − f'g'| ≤ |f|·|g−g'| + |g'|·|f−f'|` through the boundedness of the
//! fixed factors `|f|` and `|g'|`; that bound is exactly this theorem.
//!
//! # The single-sequence Cauchy predicate
//!
//! The carrier `NNReal.CauSeq` (`algebra_nnreal_cauchy.rs`) is a raw
//! `Nat → NNRat` wrapper — it carries NO Cauchy proof (`NNReal.CauSeq.Equiv` is
//! the *binary* "agree in the limit" relation, and `Equiv f f` is trivially
//! `refl`, NOT a Cauchy witness). Boundedness is FALSE for an arbitrary
//! sequence (e.g. `n ↦ n`), so it genuinely needs a Cauchy hypothesis. We add a
//! single-sequence predicate, deliberately the ONE-SIDED upper form (all an
//! upper bound needs), routed through `Rat.lt` (NOT `Rat.dist`, which is an
//! admitted axiom — same posture as `Equiv`):
//!
//! `NNReal.CauSeq.IsCauchy f := ∀ ε, Rat.lt 0 ε →`
//! `   ∃ N, ∀ m, Nat.le N m → Rat.lt (val (seq f m)) (Rat.add (val (seq f N)) ε)`
//!
//! i.e. the tail (from the modulus `N` on) stays within `ε` above the anchor
//! `seq f N`. This is implied by the two-sided Cauchy property a genuine
//! Cauchy carrier will carry; it is registered here as the minimal interface
//! boundedness consumes.
//!
//! # The theorem
//!
//! `NNReal.CauSeq.bounded : ∀ f, IsCauchy f →`
//! `   ∃ B : NNRat, ∀ n, NNRat.le (NNReal.CauSeq.seq f n) B`
//!
//! Construction (the plan's `B = max(prefix max over [0,N], seq f N + 1)`):
//! instantiate `IsCauchy` at `ε = 1` (`Rat.zero_lt_one`) to get a modulus `N`
//! and `hN : ∀ m ≥ N, val(seq f m) < val(seq f N) + 1`. Take
//! `B := NNRat.max (NNRat.prefixMax (seq f) N) (NNRat.add (seq f N) NNRat.one)`.
//! For each `n`, `Nat.le_total n N` splits:
//! - `n ≤ N`: `NNRat.le_prefixMax` gives `seq f n ≤ prefixMax (seq f) N`, then
//!   `NNRat.le_max_left` + `NNRat.le_trans` lands in `B`.
//! - `N ≤ n`: `hN n` gives `val(seq f n) < val(seq f N) + 1`. Since
//!   `NNRat.val (NNRat.add (seq f N) NNRat.one) ≡ val(seq f N) + 1` AND
//!   `NNRat.val NNRat.one ≡ Rat.one` (both definitional — `NNRat.add`/`NNRat.one`
//!   are `Subtype.mk`/`ofRat`, whose `.val` projection reduces), `Rat.le_of_lt`
//!   yields `seq f n ≤ NNRat.add (seq f N) NNRat.one`, then `NNRat.le_max_right`
//!   + `NNRat.le_trans` lands in `B`.
//!
//! `IsCauchy` is a `Definition`; `bounded` is a kernel-checked
//! `Declaration::Theorem`, `ProofQuality::Constructive`, with an empty admitted-
//! axiom closure (foundational only — `Rat.le_of_lt` is the fresh axiom-free
//! `Quot.ind` lift of the constructive `Int.le_of_lt`). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the boundedness theorem.
pub(crate) struct BoundedConsts {
    prop: Expr,
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_lt: Expr,
    rat_add: Expr,
    rat_le_of_lt: Expr,
    rat_zero_lt_one: Expr,
    nat_le: Expr,
    nat_le_total: Expr,
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_one: Expr,
    nnrat_add: Expr,
    nnrat_max: Expr,
    nnrat_le: Expr,
    nnrat_le_trans: Expr,
    nnrat_le_max_left: Expr,
    nnrat_le_max_right: Expr,
    nnrat_le_prefix_max: Expr,
    nnrat_prefix_max: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    is_cauchy: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    or_c: Expr,
    or_rec: Expr,
}

impl BoundedConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_lt: k("Rat.lt"),
            rat_add: k("Rat.add"),
            rat_le_of_lt: k("Rat.le_of_lt"),
            rat_zero_lt_one: k("Rat.zero_lt_one"),
            nat_le: k("Nat.le"),
            nat_le_total: k("Nat.le_total"),
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_one: k("NNRat.one"),
            nnrat_add: k("NNRat.add"),
            nnrat_max: k("NNRat.max"),
            nnrat_le: k("NNRat.le"),
            nnrat_le_trans: k("NNRat.le_trans"),
            nnrat_le_max_left: k("NNRat.le_max_left"),
            nnrat_le_max_right: k("NNRat.le_max_right"),
            nnrat_le_prefix_max: k("NNRat.le_prefixMax"),
            nnrat_prefix_max: k("NNRat.prefixMax"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            is_cauchy: k("NNReal.CauSeq.IsCauchy"),
            // Nat : Type 0 = Sort 1, so Exists over Nat / NNRat is Exists.{1}.
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![lvl1]),
            or_c: k("Or"),
            or_rec: k("Or.rec"),
        }
    }

    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn seq_ty(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.nat.clone(), self.nnrat.clone())
    }
    /// `NNReal.CauSeq.seq f : Nat → NNRat`.
    fn seq_of(&self, f: Expr) -> Expr {
        Expr::app(self.causeq_seq.clone(), f)
    }
    /// `(seq f) n : NNRat`.
    fn seq_at(&self, f: Expr, n: Expr) -> Expr {
        Expr::app(self.seq_of(f), n)
    }
    /// `NNRat.val q : Rat`.
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    /// `Nat.le a b : Prop`.
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `NNRat.le p q : Prop`.
    fn nle(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_le.clone(), [p, q])
    }
    /// `NNRat.max p q`.
    fn nmax(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_max.clone(), [p, q])
    }
    /// `NNRat.add p q`.
    fn nadd(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_add.clone(), [p, q])
    }
    /// `NNRat.prefixMax g n`.
    fn pmax(&self, g: Expr, n: Expr) -> Expr {
        Expr::apps(self.nnrat_prefix_max.clone(), [g, n])
    }
    /// `NNReal.CauSeq.IsCauchy f : Prop`.
    fn is_cauchy(&self, f: Expr) -> Expr {
        Expr::app(self.is_cauchy.clone(), f)
    }

    /// The `IsCauchy` body for a fixed `f`:
    /// `∀ ε, Rat.lt 0 ε → ∃ N, ∀ m, Nat.le N m → Rat.lt (val(seq f m)) (val(seq f N) + ε)`.
    fn is_cauchy_body(&self, parent: &EnvDeclBuilder, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (eps_id, eps) = b.fresh_local(self.rat.clone());
        let hpos = self.rlt(self.rat_zero.clone(), eps.clone());
        let (hpos_id, _hpos) = b.fresh_local(hpos.clone());
        let exists_n = self.tail_exists(&b, f, &eps);
        let e = b.mk_pi(hpos_id, BinderInfo::Default, hpos, exists_n);
        let e = b.mk_pi(eps_id, BinderInfo::Default, self.rat.clone(), e);
        b.finish_child(e)
    }

    /// `∃ N, ∀ m, Nat.le N m → Rat.lt (val(seq f m)) (val(seq f N) + ε)`.
    fn tail_exists(&self, parent: &EnvDeclBuilder, f: &Expr, eps: &Expr) -> Expr {
        let pred_n = self.tail_pred(parent, f, eps);
        Expr::apps(self.exists_c.clone(), [self.nat.clone(), pred_n])
    }

    /// `fun N => ∀ m, Nat.le N m → Rat.lt (val(seq f m)) (val(seq f N) + ε)`.
    fn tail_pred(&self, parent: &EnvDeclBuilder, f: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n_cap) = bn.fresh_local(self.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(self.nat.clone());
            let hle = self.nat_le(n_cap.clone(), m.clone());
            let (hle_id, _hle) = bi.fresh_local(hle.clone());
            let concl = self.rlt(
                self.val(self.seq_at(f.clone(), m.clone())),
                self.radd(self.val(self.seq_at(f.clone(), n_cap.clone())), eps.clone()),
            );
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
            bi.finish_child(e)
        };
        let lam = bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner);
        bn.finish_child(lam)
    }

    /// The bounded-by-`B` predicate for a fixed `f`:
    /// `fun (B : NNRat) => ∀ n, NNRat.le (seq f n) B`.
    fn bound_pred(&self, parent: &EnvDeclBuilder, f: &Expr) -> Expr {
        let mut bb = EnvDeclBuilder::child_of(parent);
        let (b_id, bvar) = bb.fresh_local(self.nnrat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bb);
            let (n_id, n) = bi.fresh_local(self.nat.clone());
            let concl = self.nle(self.seq_at(f.clone(), n.clone()), bvar.clone());
            let e = bi.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), concl);
            bi.finish_child(e)
        };
        let lam = bb.mk_lam(b_id, BinderInfo::Default, self.nnrat.clone(), inner);
        bb.finish_child(lam)
    }
}

impl Environment {
    /// Register `NNReal.CauSeq.IsCauchy` + `NNReal.CauSeq.bounded`. Idempotent.
    /// Pulls in the prefix-max core, `NNRat` order, and the fresh `Rat.le_of_lt`.
    pub fn init_algebra_nnreal_bounded_recovered(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cauchy()?;
        self.init_algebra_nnreal_nnrat_prefixmax()?; // prefixMax + NNRat order/max
        self.init_algebra_nnreal_nnrat_order()?; // NNRat.le_trans, + Rat.le_of_lt
        self.register_rat_order_proofs()?; // Rat.zero_lt_one
        self.register_nat_le_total_proof()?; // Nat.le_total
        let c = BoundedConsts::new();
        self.register_nnreal_is_cauchy_recovered(&c)?;
        self.register_nnreal_bounded(&c)?;
        Ok(())
    }

    /// `NNReal.CauSeq.IsCauchy : NNReal.CauSeq → Prop`.
    fn register_nnreal_is_cauchy_recovered(&mut self, c: &BoundedConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNReal.CauSeq.IsCauchy"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.causeq.clone(), c.prop.clone());
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let body = c.is_cauchy_body(&b, &f);
            let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNReal.CauSeq.IsCauchy"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.CauSeq.bounded : ∀ f, IsCauchy f → ∃ B, ∀ n, NNRat.le (seq f n) B`.
    fn register_nnreal_bounded(&mut self, c: &BoundedConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.bounded");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let hyp = c.is_cauchy(f.clone());
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let bound_pred = c.bound_pred(&b, &f);
            let concl = Expr::apps(c.exists_c.clone(), [c.nnrat.clone(), bound_pred]);
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        let value = build_bounded_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the proof term for `NNReal.CauSeq.bounded` (see registration doc).
fn build_bounded_proof(c: &BoundedConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.causeq.clone());
    let hyp = c.is_cauchy(f.clone());
    let (h_id, h) = b.fresh_local(hyp.clone());

    // The goal `∃ B, bound_pred B`.
    let bound_pred = c.bound_pred(&b, &f);
    let goal_exists = Expr::apps(c.exists_c.clone(), [c.nnrat.clone(), bound_pred.clone()]);

    // `h Rat.one Rat.zero_lt_one : ∃ N, ∀ m ≥ N, val(seq f m) < val(seq f N) + 1`.
    let one = c.rat_one.clone();
    let h_at_one = Expr::apps(h.clone(), [one.clone(), c.rat_zero_lt_one.clone()]);

    // pred_one N := ∀ m, Nat.le N m → Rat.lt (val(seq f m)) (val(seq f N) + 1).
    let pred_one = c.tail_pred(&b, &f, &one);
    // Exists.elim Nat pred_one goal_exists h_at_one elim_fn.
    let elim_fn = build_bounded_elim_fn(c, &b, &f, &one, &bound_pred);
    let elim = Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), pred_one, goal_exists, h_at_one, elim_fn],
    );
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, elim);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// `fun (N : Nat) (hN : pred_one N) => Exists.intro NNRat bound_pred B proof_forall`.
fn build_bounded_elim_fn(
    c: &BoundedConsts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    one: &Expr,
    bound_pred: &Expr,
) -> Expr {
    let mut be = EnvDeclBuilder::child_of(parent);
    let (n_id, n_cap) = be.fresh_local(c.nat.clone());

    // hN : pred_one N ≡ ∀ m, Nat.le N m → Rat.lt (val(seq f m)) (val(seq f N) + 1).
    let hn_ty = {
        let mut bn = EnvDeclBuilder::child_of(&be);
        let (m_id, m) = bn.fresh_local(c.nat.clone());
        let hle = c.nat_le(n_cap.clone(), m.clone());
        let (hle_id, _hle) = bn.fresh_local(hle.clone());
        let concl = c.rlt(
            c.val(c.seq_at(f.clone(), m.clone())),
            c.radd(c.val(c.seq_at(f.clone(), n_cap.clone())), one.clone()),
        );
        let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bn.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
        bn.finish_child(e)
    };
    let (hn_id, hn) = be.fresh_local(hn_ty.clone());

    // B := NNRat.max (prefixMax (seq f) N) (NNRat.add (seq f N) NNRat.one).
    let anchor_plus = c.nadd(c.seq_at(f.clone(), n_cap.clone()), c.nnrat_one.clone());
    let big_b = c.nmax(
        c.pmax(c.seq_of(f.clone()), n_cap.clone()),
        anchor_plus.clone(),
    );

    // proof_forall : ∀ n, NNRat.le (seq f n) B.
    let proof_forall = build_bounded_forall(c, &be, f, one, &n_cap, &hn, &anchor_plus, &big_b);

    let intro = Expr::apps(
        c.exists_intro.clone(),
        [c.nnrat.clone(), bound_pred.clone(), big_b, proof_forall],
    );
    let e = be.mk_lam(hn_id, BinderInfo::Default, hn_ty, intro);
    let e = be.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    be.finish_child(e)
}

/// `fun (n : Nat) => Or.rec … (Nat.le_total n N)` : `NNRat.le (seq f n) B`.
#[allow(clippy::too_many_arguments)]
fn build_bounded_forall(
    c: &BoundedConsts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    _one: &Expr,
    n_cap: &Expr,
    hn: &Expr,
    anchor_plus: &Expr,
    big_b: &Expr,
) -> Expr {
    let mut bf = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = bf.fresh_local(c.nat.clone());

    let seq_n = c.seq_at(f.clone(), n.clone());
    let pmax = c.pmax(c.seq_of(f.clone()), n_cap.clone());
    let goal = c.nle(seq_n.clone(), big_b.clone());

    // le_total disjuncts: P := Nat.le n N, Q := Nat.le N n.
    let p_le = c.nat_le(n.clone(), n_cap.clone());
    let q_le = c.nat_le(n_cap.clone(), n.clone());

    // motive := fun (_ : Or P Q) => NNRat.le (seq f n) B.
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&bf);
        let or_ty = Expr::apps(c.or_c.clone(), [p_le.clone(), q_le.clone()]);
        let (hh_id, _hh) = m.fresh_local(or_ty.clone());
        m.finish_child(m.mk_lam(hh_id, BinderInfo::Default, or_ty, goal.clone()))
    };

    // LEFT (h : Nat.le n N):
    //   le_prefixMax (seq f) n N h : NNRat.le (seq f n)(prefixMax (seq f) N)
    //   le_max_left pmax anchor_plus : NNRat.le pmax B
    //   le_trans (seq f n) pmax B  (..) (..).
    let case_left = {
        let mut cl = EnvDeclBuilder::child_of(&bf);
        let (hp_id, hp) = cl.fresh_local(p_le.clone());
        let h_pref = Expr::apps(
            c.nnrat_le_prefix_max.clone(),
            [c.seq_of(f.clone()), n.clone(), n_cap.clone(), hp],
        );
        let h_max_left = Expr::apps(
            c.nnrat_le_max_left.clone(),
            [pmax.clone(), anchor_plus.clone()],
        );
        let body = Expr::apps(
            c.nnrat_le_trans.clone(),
            [
                seq_n.clone(),
                pmax.clone(),
                big_b.clone(),
                h_pref,
                h_max_left,
            ],
        );
        let lam = cl.mk_lam(hp_id, BinderInfo::Default, p_le.clone(), body);
        cl.finish_child(lam)
    };

    // RIGHT (h : Nat.le N n):
    //   hN n h : Rat.lt (val(seq f n)) (val(seq f N) + 1).
    //   val(anchor_plus) ≡ val(seq f N) + val(NNRat.one) ≡ val(seq f N) + 1 (defeq).
    //   Rat.le_of_lt (val(seq f n)) (val anchor_plus) (hN n h)
    //     : Rat.le (val(seq f n))(val anchor_plus) ≡ NNRat.le (seq f n) anchor_plus.
    //   le_max_right pmax anchor_plus : NNRat.le anchor_plus B.
    //   le_trans (seq f n) anchor_plus B (..) (..).
    let case_right = {
        let mut cr = EnvDeclBuilder::child_of(&bf);
        let (hq_id, hq) = cr.fresh_local(q_le.clone());
        // hN n hq : Rat.lt (val(seq f n)) (val(seq f N) + 1).
        let h_tail = Expr::apps(hn.clone(), [n.clone(), hq]);
        // Rat.le_of_lt (val(seq f n)) (val anchor_plus) h_tail.
        // The target type val(anchor_plus) reduces to val(seq f N) + 1, matching
        // h_tail's RHS definitionally; we name val(anchor_plus) explicitly so the
        // result type is syntactically `Rat.le (val(seq f n))(val anchor_plus)`.
        let val_seq_n = c.val(seq_n.clone());
        let val_anchor = c.val(anchor_plus.clone());
        let h_le = Expr::apps(c.rat_le_of_lt.clone(), [val_seq_n, val_anchor, h_tail]);
        let h_max_right = Expr::apps(
            c.nnrat_le_max_right.clone(),
            [pmax.clone(), anchor_plus.clone()],
        );
        let body = Expr::apps(
            c.nnrat_le_trans.clone(),
            [
                seq_n.clone(),
                anchor_plus.clone(),
                big_b.clone(),
                h_le,
                h_max_right,
            ],
        );
        let lam = cr.mk_lam(hq_id, BinderInfo::Default, q_le.clone(), body);
        cr.finish_child(lam)
    };

    // Nat.le_total n N : Or (Nat.le n N)(Nat.le N n).
    let h_total = Expr::apps(c.nat_le_total.clone(), [n.clone(), n_cap.clone()]);
    // Or.rec P Q motive case_left case_right h_total.
    let rec = Expr::apps(
        c.or_rec.clone(),
        [p_le, q_le, motive, case_left, case_right, h_total],
    );
    let lam = bf.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec);
    bf.finish_child(lam)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_bounded_recovered()
            .expect("init_algebra_nnreal_bounded_recovered");
        env.init_algebra_nnreal_bounded_recovered()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_bounded_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["NNReal.CauSeq.IsCauchy", "NNReal.CauSeq.bounded"] {
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
    fn test_nnreal_bounded_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.CauSeq.bounded");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "bounded must be Theorem");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "bounded must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "bounded closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
        // Rat.le_of_lt — the fresh lt→le lift — must itself be empty-closure.
        let lol = Name::from_string("Rat.le_of_lt");
        assert!(
            env.axiom_deps(&lol).expect("deps").is_empty(),
            "Rat.le_of_lt closure must be foundational-only: {:?}",
            env.axiom_deps(&lol)
        );
    }
}
