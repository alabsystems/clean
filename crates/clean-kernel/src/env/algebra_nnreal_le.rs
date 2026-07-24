// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `NNReal.le` (the eventual one-sided domination order
//! on the Cauchy-SUBTYPE carrier; additive, dist-free).
//!
//! # Why this module exists
//!
//! With `NNReal.CauSeq.Equiv` a genuine setoid (`refl`/`symm`/`trans` all
//! landed) and `NNReal.add` lifted, the carrier ORDER can be lifted. This
//! module defines the eventual one-sided domination relation on Cauchy
//! sequences and lifts it to a binary `Prop` on `NNReal` via the nested
//! `Quot.lift` pattern (mirroring `NNReal.add`), then proves `refl` and `trans`
//! and the forward `ofRat` order bridge.
//!
//! # The relation (axiom-free, kernel-checked)
//!
//! `NNReal.CauSeq.le` is the eventual one-sided domination up to ε (NOT
//! `Rat.dist`, which is an admitted `Declaration::Axiom`):
//! - `NNReal.CauSeq.le : NNReal.CauSeq → NNReal.CauSeq → Prop`
//!   `:= fun f g => ∀ (ε : Rat), Rat.lt Rat.zero ε →`
//!   `     ∃ (N : Nat), ∀ (n : Nat), Nat.le N n →`
//!   `       Rat.lt (NNRat.val (seq f n)) (Rat.add (NNRat.val (seq g n)) ε)`
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.CauSeq.le` — the eventual one-sided domination relation.
//! - `NNReal.le : NNReal → NNReal → Prop` — the binary `Quot.lift` of
//!   `NNReal.CauSeq.le` (two-sided `Equiv`-respect via an ε/2 split reusing
//!   `Rat.add_halves`, `Quot.sound`-free: the lift target is `Prop`, so the
//!   respect obligations equate the two `Prop`s via `propext`).
//! - `NNReal.le.refl : ∀ a, NNReal.le a a`.
//! - `NNReal.le.trans : ∀ a b c, NNReal.le a b → NNReal.le b c → NNReal.le a c`
//!   (the ε/2 split).
//! - `NNReal.ofRat_le_ofRat : ∀ a b (ha : 0≤a)(hb : 0≤b), Rat.le a b →
//!       NNReal.le (NNReal.ofRat a ha) (NNReal.ofRat b hb)` — the forward
//!   `ofRat` order bridge (the reverse needs an unbuilt Archimedean
//!   `le_of_forall_lt_add`, so only the clean forward direction lands).
//!
//! Each theorem is `Declaration::Theorem`, `ProofQuality::Constructive`, with an
//! empty admitted-axiom closure (foundational only). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNReal.le`. The relation body
/// uses `NNRat.val (NNReal.CauSeq.seq · n)` bounded one-sidedly by `Rat.lt`.
pub(crate) struct LeConsts {
    prop: Expr,
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_le: Expr,
    nnrat_val: Expr,
    rat_add: Expr,
    rat_div: Expr,
    rat_two: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    nat_le: Expr,
    // Lemmas (Rat strict-order + recombination).
    rat_half_pos: Expr,
    rat_add_lt_add_left: Expr,
    rat_add_lt_add_right: Expr,
    rat_lt_trans: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_add_assoc: Expr,
    rat_add_halves: Expr,
    rat_add_zero: Expr,
    // Nat order.
    nat_max: Expr,
    nat_le_max_left: Expr,
    nat_le_max_right: Expr,
    nat_le_trans: Expr,
    // Logic: Exists / Exists.intro / Exists.elim at level 1.
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    // Eq.{1} over Rat (transport / congr).
    eq_trans: Expr,
    eq_subst: Expr,
    congr_arg: Expr,
    // Quot machinery at level 1.
    quot: Expr,
    quot_lift: Expr,
    quot_mk: Expr,
}

impl LeConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_le: k("NNReal.CauSeq.le"),
            nnrat_val: k("NNRat.val"),
            rat_add: k("Rat.add"),
            rat_div: k("Rat.div"),
            rat_two: k("Rat.two"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            nat_le: k("Nat.le"),
            rat_half_pos: k("Rat.half_pos"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_add_lt_add_right: k("Rat.add_lt_add_right"),
            rat_lt_trans: k("Rat.lt_trans"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_halves: k("Rat.add_halves"),
            rat_add_zero: k("Rat.add_zero"),
            nat_max: k("Nat.max"),
            nat_le_max_left: k("Nat.le_max_left"),
            nat_le_max_right: k("Nat.le_max_right"),
            nat_le_trans: k("Nat.le_trans"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(
                Name::from_string("congrArg"),
                vec![lvl1.clone(), lvl1.clone()],
            ),
            quot: Expr::const_(Name::from_string("Quot"), vec![lvl1.clone()]),
            quot_lift: Expr::const_(
                Name::from_string("Quot.lift"),
                vec![lvl1.clone(), lvl1.clone()],
            ),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1]),
        }
    }

    // ── term constructors ───────────────────────────────────────────────────

    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn half(&self, eps: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [eps, self.rat_two.clone()])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `NNRat.val (NNReal.CauSeq.seq x n) : Rat`.
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(self.causeq_seq.clone(), x.clone());
        let at = Expr::app(seq, n.clone());
        Expr::app(self.nnrat_val.clone(), at)
    }
    /// `NNReal.CauSeq.Equiv a b : Prop`.
    fn equiv(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [a, b])
    }
    /// `NNReal.CauSeq.le a b : Prop`.
    fn causeq_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_le.clone(), [a, b])
    }
    /// The one-sided domination conclusion at index `m`: `vseq a m < vseq b m + ε`.
    fn dom(&self, a: &Expr, bb: &Expr, m: &Expr, eps: &Expr) -> Expr {
        self.lt(self.vseq(a, m), self.add(self.vseq(bb, m), eps.clone()))
    }

    /// The `∀ N`-predicate body for `(a,b)` at tolerance `eps`:
    ///   `fun N => ∀ n, Nat.le N n → vseq a n < vseq b n + eps`.
    fn pred_n(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n_cap) = bn.fresh_local(self.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(self.nat.clone());
            let hle = self.nat_le(n_cap.clone(), m.clone());
            let (hle_id, _hle) = bi.fresh_local(hle.clone());
            let concl = self.dom(a, b, &m, eps);
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
            bi.finish_child(e)
        };
        let lam = bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner);
        bn.finish_child(lam)
    }

    /// `pred_n a b eps N` fully applied — `∀ n, Nat.le N n → vseq a n < vseq b n + eps`.
    fn pred_n_at(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        b: &Expr,
        eps: &Expr,
        cap: &Expr,
    ) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = bn.fresh_local(self.nat.clone());
        let hle = self.nat_le(cap.clone(), m.clone());
        let (hle_id, _hle) = bn.fresh_local(hle.clone());
        let concl = self.dom(a, b, &m, eps);
        let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bn.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
        bn.finish_child(e)
    }

    /// `∃ N, pred_n a b eps N : Prop`.
    fn exists_pred(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nat.clone(), self.pred_n(parent, a, b, eps)],
        )
    }

    /// The `NNReal.CauSeq.le` body for a fixed pair `(f,g)`:
    ///   `∀ ε, 0<ε → ∃ N, ∀ n, N≤n → vseq f n < vseq g n + ε`.
    fn le_body(&self, parent: &EnvDeclBuilder, f: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (eps_id, eps) = b.fresh_local(self.rat.clone());
        let hpos = self.lt(self.rat_zero.clone(), eps.clone());
        let (hpos_id, _hpos) = b.fresh_local(hpos.clone());
        let body = self.exists_pred(&b, f, g, &eps);
        let e = b.mk_pi(hpos_id, BinderInfo::Default, hpos, body);
        let e = b.mk_pi(eps_id, BinderInfo::Default, self.rat.clone(), e);
        b.finish_child(e)
    }

    // ── proof constructors ──────────────────────────────────────────────────

    /// `Rat.add_lt_add_left a b c h : (c+a) < (c+b)` from `h : a<b`.
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    /// `Rat.add_lt_add_right a b c h : (a+c) < (b+c)` from `h : a<b`.
    fn add_lt_add_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_right.clone(), [a, b, cc, h])
    }
    /// `Rat.lt_trans a b c hab hbc : a < c`.
    fn lt_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_lt_trans.clone(), [a, b, cc, hab, hbc])
    }
    /// `Rat.lt_of_le_of_lt a b c hab hbc : a < c` from `hab : a≤b`, `hbc : b<c`.
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, cc, hab, hbc])
    }
    /// `Rat.add_assoc a b c : Eq Rat ((a+b)+c) (a+(b+c))`.
    fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    /// `Rat.add_halves eps : Eq Rat ((eps/2)+(eps/2)) eps`.
    fn add_halves(&self, eps: Expr) -> Expr {
        Expr::app(self.rat_add_halves.clone(), eps)
    }
    /// `Rat.add_zero a : Eq Rat (Rat.add a Rat.zero) a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    /// `@Eq.trans Rat a b c hab hbc`.
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@congrArg Rat Rat a a' f h : Eq Rat (f a)(f a')`.
    fn congr_arg(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    /// `Nat.le_trans a b c hab hbc : Nat.le a c`.
    fn nat_le_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.nat_le_trans.clone(), [a, b, cc, hab, hbc])
    }

    /// `eq_recombine vx eps : Eq Rat ((vx + eps/2) + eps/2) (vx + eps)`.
    /// `(vx+ε/2)+ε/2 = vx+(ε/2+ε/2)` (add_assoc) `= vx+ε` (congrArg add_halves).
    fn eq_recombine(&self, parent: &EnvDeclBuilder, vx: &Expr, eps: &Expr) -> Expr {
        let half = self.half(eps.clone());
        let assoc = self.add_assoc(vx.clone(), half.clone(), half.clone());
        let half_pair = self.add(half.clone(), half.clone());
        let add_vx_fn = {
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = fb.fresh_local(self.rat.clone());
            let body = self.add(vx.clone(), t);
            fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let congr = self.congr_arg(
            half_pair.clone(),
            eps.clone(),
            add_vx_fn,
            self.add_halves(eps.clone()),
        );
        let lhs = self.add(self.add(vx.clone(), half.clone()), half);
        let mid = self.add(vx.clone(), half_pair);
        let rhs = self.add(vx.clone(), eps.clone());
        self.eq_trans(lhs, mid, rhs, assoc, congr)
    }

    /// `@Quot.mk.{1} CauSeq Equiv l : NNReal`.
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
    /// `NNReal := @Quot.{1} CauSeq Equiv`.
    fn nnreal(&self) -> Expr {
        Expr::apps(
            self.quot.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
}

impl Environment {
    /// Register `NNReal.CauSeq.le`, `NNReal.le`, `NNReal.le.refl`,
    /// `NNReal.le.trans`, and `NNReal.ofRat_le_ofRat`. Idempotent. Pulls in the
    /// Cauchy carrier (`Equiv`, `refl`/`symm`/`trans`), `Rat.half_pos`, and the
    /// Rat/Nat order lemmas the ε/2 arguments need.
    pub fn init_algebra_nnreal_le(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_trans()?; // CauSeq, Equiv (refl/symm/trans)
        self.init_algebra_rat_half_pos()?; // Rat.half_pos (+ Rat.add_halves, Rat.two)
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.register_rat_add_lt_add_right()?; // Rat.add_lt_add_right
        self.register_rat_lt_trans()?; // Rat.lt_trans
        self.init_boolean_analysis_order_toolkit_b1c()?; // Rat.lt_of_le_of_lt
        self.register_nat_minmax_proofs()?; // Nat.max, Nat.le_max_left/right
        self.register_nat_le_trans_proof()?; // Nat.le_trans
        self.init_rat_field_inst()?; // Rat.add_assoc, Rat.add_zero

        let c = LeConsts::new();
        self.register_nnreal_causeq_le(&c)?;
        self.register_nnreal_le(&c)?;
        self.register_nnreal_le_refl(&c)?;
        self.register_nnreal_le_trans(&c)?;
        self.register_nnreal_ofrat_le_ofrat(&c)?;
        Ok(())
    }

    /// The relation definition `NNReal.CauSeq.le`.
    fn register_nnreal_causeq_le(&mut self, c: &LeConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNReal.CauSeq.le"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.causeq.clone(),
            Expr::pi(BinderInfo::Default, c.causeq.clone(), c.prop.clone()),
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let (g_id, g) = b.fresh_local(c.causeq.clone());
            let body = c.le_body(&b, &f, &g);
            let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), body);
            let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNReal.CauSeq.le"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.le : NNReal → NNReal → Prop`, a nested binary `Quot.lift` of
    /// `NNReal.CauSeq.le`. The lift target is `Prop`, so each respect obligation
    /// is an `Eq Prop` equating the two relations; we discharge it with
    /// `propext` on the two-sided implication `Iff` built from the ε/2 split.
    fn register_nnreal_le(&mut self, c: &LeConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("NNReal.le")).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let ty = Expr::pi(
            BinderInfo::Default,
            nnreal.clone(),
            Expr::pi(BinderInfo::Default, nnreal.clone(), c.prop.clone()),
        );
        let value = build_nnreal_le_value(c, &nnreal);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNReal.le"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.le.refl : ∀ a, NNReal.le a a`. Routed through `Quot.ind` so the
    /// leaf is `CauSeq.le f f`, witnessed by `N := Nat.zero` and
    /// `vseq f n < vseq f n + ε` (from `add_lt_add_left 0 ε` + `add_zero`).
    fn register_nnreal_le_refl(&mut self, c: &LeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.le.refl");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let body = Expr::apps(
                Expr::const_(Name::from_string("NNReal.le"), vec![]),
                [a.clone(), a.clone()],
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), body);
            b.finish(e)
        };
        let value = build_le_refl_proof(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.le.trans : ∀ a b c, NNReal.le a b → NNReal.le b c → NNReal.le a c`.
    /// Routed through three `Quot.ind`s so the leaf is `CauSeq.le f h` from
    /// `CauSeq.le f g` and `CauSeq.le g h` via the ε/2 split.
    fn register_nnreal_le_trans(&mut self, c: &LeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.le.trans");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let (cv_id, cv) = b.fresh_local(nnreal.clone());
            let hab = Expr::apps(nnle.clone(), [a.clone(), bv.clone()]);
            let (hab_id, _hab) = b.fresh_local(hab.clone());
            let hbc = Expr::apps(nnle.clone(), [bv.clone(), cv.clone()]);
            let (hbc_id, _hbc) = b.fresh_local(hbc.clone());
            let concl = Expr::apps(nnle.clone(), [a.clone(), cv.clone()]);
            let e = b.mk_pi(hbc_id, BinderInfo::Default, hbc, concl);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab, e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_le_trans_proof(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.ofRat_le_ofRat : ∀ a b (ha : 0≤a)(hb : 0≤b), Rat.le a b →
    ///       NNReal.le (NNReal.ofRat a ha) (NNReal.ofRat b hb)`.
    ///
    /// `NNReal.ofRat a ha` reduces to `Quot.mk (CauSeq.const (NNRat.ofRat a ha))`,
    /// so `NNReal.le (ofRat a)(ofRat b)` reduces (by the `Quot.lift` computation
    /// rule) to `CauSeq.le (const (ofRat a)) (const (ofRat b))`, whose conclusion
    /// at index `n` is `a < b + ε` (the constant `.seq · n` reduces to the
    /// `NNRat`, and `NNRat.val (NNRat.ofRat a ha) ≡ a`). For all ε>0 take
    /// `N := Nat.zero` and prove `a < b + ε` via `lt_of_le_of_lt a b (b+ε)`
    /// with `b < b+ε` from `add_lt_add_left 0 ε b` transported along `add_zero b`.
    fn register_nnreal_ofrat_le_ofrat(&mut self, c: &LeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.ofRat_le_ofRat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
        let of_rat = Expr::const_(Name::from_string("NNReal.ofRat"), vec![]);
        let nonneg = |x: Expr| Expr::apps(c.rat_le.clone(), [c.rat_zero.clone(), x]);
        let rat_le = |x: Expr, y: Expr| Expr::apps(c.rat_le.clone(), [x, y]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let ha_ty = nonneg(a.clone());
            let (ha_id, ha) = b.fresh_local(ha_ty.clone());
            let hb_ty = nonneg(bv.clone());
            let (hb_id, hb) = b.fresh_local(hb_ty.clone());
            let hle_ty = rat_le(a.clone(), bv.clone());
            let (hle_id, _hle) = b.fresh_local(hle_ty.clone());
            let oa = Expr::apps(of_rat.clone(), [a.clone(), ha.clone()]);
            let ob = Expr::apps(of_rat.clone(), [bv.clone(), hb.clone()]);
            let concl = Expr::apps(nnle.clone(), [oa, ob]);
            let e = b.mk_pi(hle_id, BinderInfo::Default, hle_ty, concl);
            let e = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, e);
            let e = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_ofrat_le_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build `NNReal.le := fun a b => Quot.lift (outer_f) (outer_h) a`, where
/// `outer_f p` is itself a `Quot.lift` over `b`. The lift target is `Prop`, so
/// each respect obligation is an `Eq Prop`, discharged by `propext` on the
/// two-sided `Iff` between `CauSeq.le · ·` instances (the ε/2 respect).
fn build_nnreal_le_value(c: &LeConsts, nnreal: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());

    // inner_lift p second := Quot.lift (fun q => CauSeq.le p q) (inner_h p) second.
    let inner_lift = |p: &Expr, parent: &EnvDeclBuilder, second: &Expr| -> Expr {
        let inner_f = {
            let mut bi = EnvDeclBuilder::child_of(parent);
            let (q_id, q) = bi.fresh_local(c.causeq.clone());
            let body = c.causeq_le(p.clone(), q.clone());
            let lam = bi.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), body);
            bi.finish_child(lam)
        };
        let inner_h = {
            let mut bi = EnvDeclBuilder::child_of(parent);
            let (q_id, q) = bi.fresh_local(c.causeq.clone());
            let (q2_id, q2) = bi.fresh_local(c.causeq.clone());
            let hyp = c.equiv(q.clone(), q2.clone());
            let (hq_id, hq) = bi.fresh_local(hyp.clone());
            // propext (Iff between CauSeq.le p q and CauSeq.le p q2).
            let eqp = build_le_respect_propext(c, &bi, p, &q, &q2, &hq, /*right=*/ true);
            let lam = bi.mk_lam(hq_id, BinderInfo::Default, hyp, eqp);
            let lam = bi.mk_lam(q2_id, BinderInfo::Default, c.causeq.clone(), lam);
            let lam = bi.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), lam);
            bi.finish_child(lam)
        };
        Expr::apps(
            c.quot_lift.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                c.prop.clone(),
                inner_f,
                inner_h,
                second.clone(),
            ],
        )
    };

    let outer_f = {
        let mut bo = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bo.fresh_local(c.causeq.clone());
        let body = inner_lift(&p, &bo, &bv);
        let lam = bo.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), body);
        bo.finish_child(lam)
    };

    // outer_h : ∀ p p2, Equiv p p2 → Eq Prop (inner_lift p bv)(inner_lift p2 bv).
    // Routed through Quot.ind on bv so each leaf is propext of CauSeq.le p q vs
    // CauSeq.le p2 q (the LEFT respect).
    let outer_h = {
        let mut bh = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bh.fresh_local(c.causeq.clone());
        let (p2_id, p2) = bh.fresh_local(c.causeq.clone());
        let hyp = c.equiv(p.clone(), p2.clone());
        let (hp_id, hp) = bh.fresh_local(hyp.clone());

        let quot_ind = Expr::const_(
            Name::from_string("Quot.ind"),
            vec![Level::succ(Level::zero())],
        );
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&bh);
            let (x_id, x) = mb.fresh_local(nnreal.clone());
            let lhs = inner_lift(&p, &mb, &x);
            let rhs = inner_lift(&p2, &mb, &x);
            let eq_prop = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [c.prop.clone(), lhs, rhs],
            );
            mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), eq_prop))
        };
        let minor = {
            let mut mb = EnvDeclBuilder::child_of(&bh);
            let (q_id, q) = mb.fresh_local(c.causeq.clone());
            // propext between CauSeq.le p q and CauSeq.le p2 q (the LEFT respect).
            let eqp = build_le_respect_propext(c, &mb, &q, &p, &p2, &hp, /*right=*/ false);
            mb.finish_child(mb.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), eqp))
        };
        let ind = Expr::apps(
            quot_ind,
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive,
                minor,
                bv.clone(),
            ],
        );
        let lam = bh.mk_lam(hp_id, BinderInfo::Default, hyp, ind);
        let lam = bh.mk_lam(p2_id, BinderInfo::Default, c.causeq.clone(), lam);
        let lam = bh.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), lam);
        bh.finish_child(lam)
    };

    let outer = Expr::apps(
        c.quot_lift.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            c.prop.clone(),
            outer_f,
            outer_h,
            a.clone(),
        ],
    );
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), outer);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// Build `propext (Iff)` between two `CauSeq.le` instances differing in one
/// argument by `Equiv`.
///
/// `right = true`  (respect SECOND arg): `shared` is the fixed first arg `p`,
///   `x,x2` are the varying second args; produce
///   `Eq Prop (CauSeq.le p x)(CauSeq.le p x2)`.
/// `right = false` (respect FIRST arg):  `shared` is the fixed second arg `q`,
///   `x,x2` are the varying first args; produce
///   `Eq Prop (CauSeq.le x q)(CauSeq.le x2 q)`.
///
/// `hx : Equiv x x2`. Each implication direction is an ε/2 split: the goal
/// `… < … + ε` instantiates the source `CauSeq.le` at ε/2 and the `Equiv` bound
/// at ε/2, combines with `add_lt_add_right`/`add_lt_add_left` + `lt_trans`, then
/// recombines `(·+ε/2)+ε/2 = ·+ε`.
fn build_le_respect_propext(
    c: &LeConsts,
    parent: &EnvDeclBuilder,
    shared: &Expr,
    x: &Expr,
    x2: &Expr,
    hx: &Expr,
    right: bool,
) -> Expr {
    // The two relations, per `right`.
    let (lhs_le, rhs_le) = if right {
        (
            c.causeq_le(shared.clone(), x.clone()),
            c.causeq_le(shared.clone(), x2.clone()),
        )
    } else {
        (
            c.causeq_le(x.clone(), shared.clone()),
            c.causeq_le(x2.clone(), shared.clone()),
        )
    };

    // fwd : lhs_le → rhs_le.
    let fwd = build_le_respect_impl(c, parent, shared, x, x2, hx, right, /*forward=*/ true);
    // rev : rhs_le → lhs_le. We swap x,x2 and use the SYMM of hx.
    let hx_symm = {
        let symm = Expr::const_(Name::from_string("NNReal.CauSeq.Equiv.symm"), vec![]);
        Expr::apps(symm, [x.clone(), x2.clone(), hx.clone()])
    };
    let rev = build_le_respect_impl(
        c, parent, shared, x2, x, &hx_symm, right, /*forward=*/ false,
    );

    // Faithful `propext : {a b : Prop} → (a ↔ b) → a = b` takes a single `Iff`;
    // package the two implications via `Iff.intro lhs_le rhs_le fwd rev`:
    //   propext lhs_le rhs_le (Iff.intro lhs_le rhs_le fwd rev) : Eq Prop lhs_le rhs_le.
    let propext = Expr::const_(Name::from_string("propext"), vec![]);
    let iff = Expr::apps(
        Expr::const_(Name::from_string("Iff.intro"), vec![]),
        [lhs_le.clone(), rhs_le.clone(), fwd, rev],
    );
    Expr::apps(propext, [lhs_le, rhs_le, iff])
}

/// Build ONE implication direction of the respect.
///
/// `forward = true`:  domain `CauSeq.le A B`, codomain `CauSeq.le A' B'` where
///   the pair `(A,B)→(A',B')` realises adding the `Equiv` bound on the varying
///   argument. `x` is the domain's varying arg, `x2` the codomain's.
/// We always produce a term of type `(domain_le) → (codomain_le)`. The caller
/// arranges `x,x2` (and the symm of `hx`) so both directions are this same
/// shape with `x` the source-varying and `x2` the target-varying argument.
///
/// `right = true`  : second arg varies. domain `CauSeq.le shared x`, codomain
///   `CauSeq.le shared x2`. goal at m: `vseq shared m < vseq x2 m + ε`.
///   have `vseq shared m < vseq x m + ε/2` (hyp at ε/2) and
///   `vseq x m < vseq x2 m + ε/2` (Equiv x x2, left conjunct at ε/2).
///   ⟹ `vseq shared m < (vseq x2 m + ε/2) + ε/2` via add_lt_add_right on the
///   second + lt_trans; recombine to `vseq x2 m + ε`.
/// `right = false` : first arg varies. domain `CauSeq.le x shared`, codomain
///   `CauSeq.le x2 shared`. goal at m: `vseq x2 m < vseq shared m + ε`.
///   have `vseq x m < vseq shared m + ε/2` (hyp at ε/2) and
///   `vseq x2 m < vseq x m + ε/2` (Equiv x x2 with x2 on the left — left
///   conjunct of `Equiv x2 x`; the caller passes the symm so this is the LEFT
///   conjunct of the supplied `hx`). ⟹ `vseq x2 m < (vseq shared m + ε/2)+ε/2`.
#[allow(clippy::too_many_arguments)]
fn build_le_respect_impl(
    c: &LeConsts,
    parent: &EnvDeclBuilder,
    shared: &Expr,
    x: &Expr,
    x2: &Expr,
    hx: &Expr,
    right: bool,
    _forward: bool,
) -> Expr {
    // The domain & codomain `CauSeq.le` pairs.
    let (dom_a, dom_b, cod_a, cod_b) = if right {
        (shared.clone(), x.clone(), shared.clone(), x2.clone())
    } else {
        (x.clone(), shared.clone(), x2.clone(), shared.clone())
    };

    let mut bb = EnvDeclBuilder::child_of(parent);
    // hle_src : CauSeq.le dom_a dom_b.
    let hle_src_ty = c.causeq_le(dom_a.clone(), dom_b.clone());
    let (hsrc_id, hsrc) = bb.fresh_local(hle_src_ty.clone());

    // goal: CauSeq.le cod_a cod_b = ∀ ε, 0<ε → ∃ N, ∀ n, N≤n → vseq cod_a n < vseq cod_b n + ε.
    let (eps_id, eps) = bb.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = bb.fresh_local(hpos_ty.clone());

    let half = c.half(eps.clone());
    let heps2 = Expr::apps(c.rat_half_pos.clone(), [eps.clone(), hpos.clone()]);

    // src at ε/2: ∃ N1, ∀ n, N1≤n → vseq dom_a n < vseq dom_b n + ε/2.
    let exists_src = Expr::apps(hsrc.clone(), [half.clone(), heps2.clone()]);
    // Equiv x x2 at ε/2: ∃ N2, ∀ n, N2≤n → bound_pair (vseq x n)(vseq x2 n) ε/2.
    let exists_eq = Expr::apps(hx.clone(), [half.clone(), heps2]);

    let goal_exists = c.exists_pred(&bb, &cod_a, &cod_b, &eps);
    let pred_src = c.pred_n(&bb, &dom_a, &dom_b, &half);

    // Outer elim over the src exists, then inner elim over the Equiv exists.
    let elim_outer = {
        let mut bo = EnvDeclBuilder::child_of(&bb);
        let (n1_id, n1) = bo.fresh_local(c.nat.clone());
        let hn1_ty = c.pred_n_at(&bo, &dom_a, &dom_b, &half, &n1);
        let (hn1_id, hn1) = bo.fresh_local(hn1_ty.clone());

        let elim_inner = {
            let mut bi = EnvDeclBuilder::child_of(&bo);
            let (n2_id, n2) = bi.fresh_local(c.nat.clone());
            // hn2 : ∀ n, N2≤n → bound_pair (vseq x n)(vseq x2 n) ε/2.
            let hn2_ty = equiv_pred_at(c, &bi, x, x2, &half, &n2);
            let (hn2_id, hn2) = bi.fresh_local(hn2_ty.clone());

            let nmax = Expr::apps(c.nat_max.clone(), [n1.clone(), n2.clone()]);

            let witness = {
                let mut bw = EnvDeclBuilder::child_of(&bi);
                let (m_id, m) = bw.fresh_local(c.nat.clone());
                let hle_ty = c.nat_le(nmax.clone(), m.clone());
                let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

                let le_max_l = Expr::apps(c.nat_le_max_left.clone(), [n1.clone(), n2.clone()]);
                let le_max_r = Expr::apps(c.nat_le_max_right.clone(), [n1.clone(), n2.clone()]);
                let n1_le_m =
                    c.nat_le_trans(n1.clone(), nmax.clone(), m.clone(), le_max_l, hle.clone());
                let n2_le_m = c.nat_le_trans(n2.clone(), nmax.clone(), m.clone(), le_max_r, hle);

                // base_src : vseq dom_a m < vseq dom_b m + ε/2.
                let base_src = Expr::apps(hn1.clone(), [m.clone(), n1_le_m]);
                // base_eq : bound_pair (vseq x m)(vseq x2 m) ε/2.
                let base_eq = Expr::apps(hn2.clone(), [m.clone(), n2_le_m]);

                let proof = build_le_combine(
                    c, &bw, shared, x, x2, &m, &eps, &half, &base_src, &base_eq, right,
                );

                let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
                let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
                bw.finish_child(e)
            };

            let intro = Expr::apps(
                c.exists_intro.clone(),
                [
                    c.nat.clone(),
                    c.pred_n(&bi, &cod_a, &cod_b, &eps),
                    nmax,
                    witness,
                ],
            );
            let e = bi.mk_lam(hn2_id, BinderInfo::Default, hn2_ty, intro);
            let e = bi.mk_lam(n2_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };

        let elim_eq = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nat.clone(),
                equiv_pred(c, &bo, x, x2, &half),
                goal_exists.clone(),
                exists_eq.clone(),
                elim_inner,
            ],
        );
        let e = bo.mk_lam(hn1_id, BinderInfo::Default, hn1_ty, elim_eq);
        let e = bo.mk_lam(n1_id, BinderInfo::Default, c.nat.clone(), e);
        bo.finish_child(e)
    };

    let elim = Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), pred_src, goal_exists, exists_src, elim_outer],
    );

    let e = bb.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim);
    let e = bb.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = bb.mk_lam(hsrc_id, BinderInfo::Default, hle_src_ty, e);
    bb.finish_child(e)
}

/// Combine the source one-sided bound and the Equiv two-sided bound at ε/2 into
/// the codomain one-sided bound at ε, for a fixed index `m`.
///
/// `right = true`  : base_src : vseq shared m < vseq x m + ε/2 ;
///                   base_eq  : bound_pair (vseq x m)(vseq x2 m) ε/2 (LEFT: vseq x m < vseq x2 m + ε/2).
///   goal: vseq shared m < vseq x2 m + ε.
///   step1: (vseq x m + ε/2) < ((vseq x2 m + ε/2)+ε/2) via add_lt_add_right (A_eq) [+ε/2].
///   step2: vseq shared m < ((vseq x2 m + ε/2)+ε/2) via lt_trans (base_src, step1).
///   recombine ((vseq x2 m + ε/2)+ε/2) = (vseq x2 m + ε).
/// `right = false` : base_src : vseq x m < vseq shared m + ε/2 ;
///                   base_eq  : bound_pair (vseq x2 m)(vseq x m) ε/2 (caller passed symm; LEFT: vseq x2 m < vseq x m + ε/2).
///   goal: vseq x2 m < vseq shared m + ε.
///   step1: (vseq x m + ε/2) < ((vseq shared m + ε/2)+ε/2) via add_lt_add_right (base_src)[+ε/2].
///   step2: vseq x2 m < ((vseq shared m + ε/2)+ε/2) via lt_trans (A_eq, step1).
///   recombine.
#[allow(clippy::too_many_arguments)]
fn build_le_combine(
    c: &LeConsts,
    parent: &EnvDeclBuilder,
    shared: &Expr,
    x: &Expr,
    x2: &Expr,
    m: &Expr,
    eps: &Expr,
    half: &Expr,
    base_src: &Expr,
    base_eq: &Expr,
    right: bool,
) -> Expr {
    let v_shared = c.vseq(shared, m);
    let vx = c.vseq(x, m);
    let vx2 = c.vseq(x2, m);

    // `base_eq` is ALWAYS the Equiv pair in the (x, x2) order produced by
    // `equiv_pred(c, x, x2, …)`:
    //   And (vx < vx2 + ε/2) (vx2 < vx + ε/2).
    // For `right=true` we need the LEFT conjunct `vx < vx2 + ε/2`; for
    // `right=false` we need the RIGHT conjunct `vx2 < vx + ε/2`.
    let l_base = c.lt(vx.clone(), c.add(vx2.clone(), half.clone()));
    let r_base = c.lt(vx2.clone(), c.add(vx.clone(), half.clone()));
    let a_eq = if right {
        let and_left = Expr::const_(Name::from_string("And.left"), vec![]);
        Expr::apps(and_left, [l_base, r_base, base_eq.clone()]) // vx < vx2 + ε/2
    } else {
        let and_right = Expr::const_(Name::from_string("And.right"), vec![]);
        Expr::apps(and_right, [l_base, r_base, base_eq.clone()]) // vx2 < vx + ε/2
    };

    if right {
        // goal: v_shared < vx2 + ε.
        // base_src : v_shared < vx + ε/2.
        // a_eq     : vx < vx2 + ε/2.
        // step1: (vx + ε/2) < ((vx2 + ε/2)+ε/2)  via add_lt_add_right vx (vx2+ε/2) (ε/2) a_eq.
        let vx2_half = c.add(vx2.clone(), half.clone());
        let step1 = c.add_lt_add_right(vx.clone(), vx2_half.clone(), half.clone(), a_eq);
        // step2: v_shared < ((vx2+ε/2)+ε/2) via lt_trans v_shared (vx+ε/2) ((vx2+ε/2)+ε/2) base_src step1.
        let vx_half = c.add(vx.clone(), half.clone());
        let vx2_hh = c.add(vx2_half.clone(), half.clone());
        let step2 = c.lt_trans(
            v_shared.clone(),
            vx_half,
            vx2_hh.clone(),
            base_src.clone(),
            step1,
        );
        // recombine ((vx2+ε/2)+ε/2) = (vx2+ε).
        let rec = c.eq_recombine(parent, &vx2, eps);
        let vx2_eps = c.add(vx2.clone(), eps.clone());
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(v_shared.clone(), t);
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst(motive, vx2_hh, vx2_eps, rec, step2)
    } else {
        // goal: vx2 < v_shared + ε.
        // base_src : vx < v_shared + ε/2.
        // a_eq     : vx2 < vx + ε/2.
        // step1: (vx + ε/2) < ((v_shared + ε/2)+ε/2) via add_lt_add_right vx (v_shared+ε/2)(ε/2) base_src.
        let vshared_half = c.add(v_shared.clone(), half.clone());
        let step1 = c.add_lt_add_right(
            vx.clone(),
            vshared_half.clone(),
            half.clone(),
            base_src.clone(),
        );
        // step2: vx2 < ((v_shared+ε/2)+ε/2) via lt_trans vx2 (vx+ε/2) (…) a_eq step1.
        let vx_half = c.add(vx.clone(), half.clone());
        let vshared_hh = c.add(vshared_half.clone(), half.clone());
        let step2 = c.lt_trans(vx2.clone(), vx_half, vshared_hh.clone(), a_eq, step1);
        let rec = c.eq_recombine(parent, &v_shared, eps);
        let vshared_eps = c.add(v_shared.clone(), eps.clone());
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(vx2.clone(), t);
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst(motive, vshared_hh, vshared_eps, rec, step2)
    }
}

/// The Equiv predicate at `N`: `∀ n, Nat.le N n → bound_pair (vseq a n)(vseq b n) eps`.
fn equiv_pred_at(
    c: &LeConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    b: &Expr,
    eps: &Expr,
    cap: &Expr,
) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = bn.fresh_local(c.nat.clone());
    let hle = c.nat_le(cap.clone(), m.clone());
    let (hle_id, _hle) = bn.fresh_local(hle.clone());
    let concl = equiv_bound_pair(c, a, b, &m, eps);
    let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
    let e = bn.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    bn.finish_child(e)
}

/// The Equiv predicate `fun N => ∀ n, N≤n → bound_pair (vseq a n)(vseq b n) eps`.
fn equiv_pred(c: &LeConsts, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (n_id, n_cap) = bn.fresh_local(c.nat.clone());
    let inner = {
        let mut bi = EnvDeclBuilder::child_of(&bn);
        let (m_id, m) = bi.fresh_local(c.nat.clone());
        let hle = c.nat_le(n_cap.clone(), m.clone());
        let (hle_id, _hle) = bi.fresh_local(hle.clone());
        let concl = equiv_bound_pair(c, a, b, &m, eps);
        let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
        bi.finish_child(e)
    };
    let lam = bn.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner);
    bn.finish_child(lam)
}

/// `And (vseq a m < vseq b m + ε) (vseq b m < vseq a m + ε)` — the Equiv pair.
fn equiv_bound_pair(c: &LeConsts, a: &Expr, b: &Expr, m: &Expr, eps: &Expr) -> Expr {
    let va = c.vseq(a, m);
    let vb = c.vseq(b, m);
    let left = c.lt(va.clone(), c.add(vb.clone(), eps.clone()));
    let right = c.lt(vb, c.add(va, eps.clone()));
    Expr::apps(
        Expr::const_(Name::from_string("And"), vec![]),
        [left, right],
    )
}

/// Build `NNReal.le.refl` via `Quot.ind`: the leaf `CauSeq.le f f` is witnessed
/// by `N := Nat.zero` and `vseq f n < vseq f n + ε`.
fn build_le_refl_proof(c: &LeConsts, nnreal: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());

    let quot_ind = Expr::const_(
        Name::from_string("Quot.ind"),
        vec![Level::succ(Level::zero())],
    );
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);

    // motive x := NNReal.le x x.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let body = Expr::apps(nnle.clone(), [x.clone(), x.clone()]);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), body))
    };

    // minor f : NNReal.le (mk f)(mk f) ≡ CauSeq.le f f.
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (f_id, f) = mf.fresh_local(c.causeq.clone());
        let body = build_causeq_le_refl(c, &mf, &f);
        mf.finish_child(mf.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), body))
    };

    let ind = Expr::apps(
        quot_ind,
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            a.clone(),
        ],
    );
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), ind);
    b.finish(e)
}

/// `CauSeq.le f f` for a fixed `f`: `∀ ε, 0<ε → ∃ N=0, ∀ n, 0≤n → vseq f n < vseq f n + ε`.
fn build_causeq_le_refl(c: &LeConsts, parent: &EnvDeclBuilder, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(nat_zero.clone(), m.clone());
        let (hle_id, _hle) = bw.fresh_local(hle_ty.clone());
        let vfm = c.vseq(f, &m);
        // vfm < vfm + ε from add_lt_add_left 0 ε vfm hpos : (vfm+0) < (vfm+ε), subst along add_zero vfm.
        let step = c.add_lt_add_left(c.rat_zero.clone(), eps.clone(), vfm.clone(), hpos.clone());
        let vfm_zero = c.add(vfm.clone(), c.rat_zero.clone());
        let vfm_eps = c.add(vfm.clone(), eps.clone());
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(t, vfm_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let proof = c.subst(motive, vfm_zero, vfm.clone(), c.add_zero(vfm.clone()), step);
        let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
        let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
        bw.finish_child(e)
    };

    let intro = Expr::apps(
        c.exists_intro.clone(),
        [c.nat.clone(), c.pred_n(&b, f, f, &eps), nat_zero, witness],
    );
    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish_child(e)
}

/// Build `NNReal.le.trans` via three `Quot.ind`s. The leaf is
/// `CauSeq.le f h` from `CauSeq.le f g` and `CauSeq.le g h` (the ε/2 split).
fn build_le_trans_proof(c: &LeConsts, nnreal: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());
    let (cv_id, cv) = b.fresh_local(nnreal.clone());
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let hab_ty = Expr::apps(nnle.clone(), [a.clone(), bv.clone()]);
    let (hab_id, hab) = b.fresh_local(hab_ty.clone());
    let hbc_ty = Expr::apps(nnle.clone(), [bv.clone(), cv.clone()]);
    let (hbc_id, hbc) = b.fresh_local(hbc_ty.clone());

    // We need to reduce a, bv, cv to representatives. Use Quot.ind three times,
    // building a motive that, for fixed reps, reduces NNReal.le to CauSeq.le.
    //
    // The cleanest structure: build a helper that proves
    //   ∀ (f g h : CauSeq), CauSeq.le f g → CauSeq.le g h → CauSeq.le f h
    // then transport along the Quot.ind reductions. But hab/hbc are typed at
    // NNReal.le a bv / NNReal.le bv cv. We Quot.ind on a, bv, cv so the
    // hypotheses' types reduce to CauSeq.le on the representatives.
    //
    // Implementation: nest three Quot.ind eliminations with motives carrying the
    // hypotheses. We instead use the property that `NNReal.le (mk f)(mk g)` is
    // DEFEQ to `CauSeq.le f g` (Quot.lift computation), so once a,bv,cv are
    // `mk f, mk g, mk h`, hab : CauSeq.le f g and hbc : CauSeq.le g h directly.
    //
    // Quot.ind requires the motive to be a Prop family over the quotient. We
    // build the goal as `NNReal.le a cv` and discharge by inducting on all three.

    // Innermost: given reps f,g,h and hab':CauSeq.le f g, hbc':CauSeq.le g h,
    // produce CauSeq.le f h.
    // We thread via Quot.ind on a (motive depends on a): produce
    //   fun (f:CauSeq) => NNReal.le (mk f) cv   (from hab : NNReal.le (mk f) bv, hbc)
    // This is getting nested; instead, prove a standalone CauSeq.le.trans and
    // apply it after reducing hab,hbc with the defeq.

    // Standalone causeq trans proof term (a function value).
    let causeq_trans = build_causeq_le_trans_fn(c);

    // Quot.ind on `a` with motive: fun x => NNReal.le x cv  (needs hab : NNReal.le x bv).
    // But hab is fixed-typed at `a`; we cannot generalise it inside the motive
    // without it appearing. So instead apply causeq_trans through a triple
    // Quot.ind where the OUTER goal is the full statement.
    //
    // Simplest correct route: Quot.ind on a, bv, cv to get reps, with the
    // hypotheses re-supplied. Since NNReal.le (mk f)(mk g) is defeq CauSeq.le f g,
    // hab and hbc are accepted as CauSeq.le proofs after the reps are fixed —
    // BUT their types mention a,bv,cv literally, not mk f, etc.
    //
    // The kernel-friendly construction: induct with motive
    //   P a := NNReal.le a bv → NNReal.le bv cv → NNReal.le a cv   (Quot.ind on a),
    //   then inside (rep f) induct on bv with
    //   Q bv := CauSeq.le f (·rep of bv) → NNReal.le bv cv → NNReal.le (mk f) cv,
    //   ... This nests cleanly.

    // Build via nested Quot.ind, each motive an implication chain.
    let body = build_le_trans_via_ind(c, &b, nnreal, &a, &bv, &cv, &hab, &hbc, &causeq_trans);

    let e = b.mk_lam(hbc_id, BinderInfo::Default, hbc_ty, body);
    let e = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// Nested triple `Quot.ind` discharging `NNReal.le a cv` from `hab`,`hbc`.
///
/// Motive over `a`: `P a := NNReal.le a bv → NNReal.le bv cv → NNReal.le a cv`.
/// We apply `Quot.ind` with this motive, supply `hab`,`hbc`, and inside (rep
/// `fa`) descend on `bv` then `cv`. At the innermost leaf the three hypotheses
/// reduce to `CauSeq.le fa fb`,`CauSeq.le fb fc`, and the goal to
/// `CauSeq.le fa fc`, closed by `causeq_trans fa fb fc · ·`.
#[allow(clippy::too_many_arguments)]
fn build_le_trans_via_ind(
    c: &LeConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    a: &Expr,
    bv: &Expr,
    cv: &Expr,
    hab: &Expr,
    hbc: &Expr,
    causeq_trans: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let quot_ind = Expr::const_(
        Name::from_string("Quot.ind"),
        vec![Level::succ(Level::zero())],
    );

    // P a := NNReal.le a bv → NNReal.le bv cv → NNReal.le a cv.
    let motive_a = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let h1 = Expr::apps(nnle.clone(), [x.clone(), bv.clone()]);
        let h2 = Expr::apps(nnle.clone(), [bv.clone(), cv.clone()]);
        let concl = Expr::apps(nnle.clone(), [x.clone(), cv.clone()]);
        let imp2 = Expr::pi(BinderInfo::Default, h2, concl);
        let imp1 = Expr::pi(BinderInfo::Default, h1, imp2);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), imp1))
    };

    // minor_a fa : P (mk fa) = CauSeq.le?(no) — it is NNReal.le (mk fa) bv → … .
    let minor_a = {
        let mut mfa = EnvDeclBuilder::child_of(parent);
        let (fa_id, fa) = mfa.fresh_local(c.causeq.clone());
        let mka = c.quot_mk(fa.clone());
        // body : NNReal.le (mk fa) bv → NNReal.le bv cv → NNReal.le (mk fa) cv.
        let body = build_trans_descend_b(c, &mfa, nnreal, &mka, &fa, bv, cv, causeq_trans);
        mfa.finish_child(mfa.mk_lam(fa_id, BinderInfo::Default, c.causeq.clone(), body))
    };

    // Quot.ind … a : P a, then apply hab, hbc.
    let ind_a = Expr::apps(
        quot_ind,
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_a,
            minor_a,
            a.clone(),
        ],
    );
    Expr::apps(ind_a, [hab.clone(), hbc.clone()])
}

/// Descend on `bv`: motive `Q b := NNReal.le (mk fa) b → NNReal.le b cv →
/// NNReal.le (mk fa) cv`. Leaf supplies rep `fb`.
#[allow(clippy::too_many_arguments)]
fn build_trans_descend_b(
    c: &LeConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mka: &Expr,
    fa: &Expr,
    bv: &Expr,
    cv: &Expr,
    causeq_trans: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let quot_ind = Expr::const_(
        Name::from_string("Quot.ind"),
        vec![Level::succ(Level::zero())],
    );

    let motive_b = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = mb.fresh_local(nnreal.clone());
        let h1 = Expr::apps(nnle.clone(), [mka.clone(), y.clone()]);
        let h2 = Expr::apps(nnle.clone(), [y.clone(), cv.clone()]);
        let concl = Expr::apps(nnle.clone(), [mka.clone(), cv.clone()]);
        let imp2 = Expr::pi(BinderInfo::Default, h2, concl);
        let imp1 = Expr::pi(BinderInfo::Default, h1, imp2);
        mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), imp1))
    };

    let minor_b = {
        let mut mfb = EnvDeclBuilder::child_of(parent);
        let (fb_id, fb) = mfb.fresh_local(c.causeq.clone());
        let mkb = c.quot_mk(fb.clone());
        let body = build_trans_descend_c(c, &mfb, nnreal, mka, fa, &mkb, &fb, cv, causeq_trans);
        mfb.finish_child(mfb.mk_lam(fb_id, BinderInfo::Default, c.causeq.clone(), body))
    };

    Expr::apps(
        quot_ind,
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_b,
            minor_b,
            bv.clone(),
        ],
    )
}

/// Descend on `cv`: motive `R c := NNReal.le (mk fa)(mk fb) → NNReal.le (mk fb) c
/// → NNReal.le (mk fa) c`. Leaf supplies rep `fc`; the three hyps/goal reduce to
/// `CauSeq.le` and close by `causeq_trans fa fb fc`.
#[allow(clippy::too_many_arguments)]
fn build_trans_descend_c(
    c: &LeConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mka: &Expr,
    fa: &Expr,
    mkb: &Expr,
    fb: &Expr,
    cv: &Expr,
    causeq_trans: &Expr,
) -> Expr {
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let quot_ind = Expr::const_(
        Name::from_string("Quot.ind"),
        vec![Level::succ(Level::zero())],
    );

    let motive_c = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(nnreal.clone());
        let h1 = Expr::apps(nnle.clone(), [mka.clone(), mkb.clone()]);
        let h2 = Expr::apps(nnle.clone(), [mkb.clone(), z.clone()]);
        let concl = Expr::apps(nnle.clone(), [mka.clone(), z.clone()]);
        let imp2 = Expr::pi(BinderInfo::Default, h2, concl);
        let imp1 = Expr::pi(BinderInfo::Default, h1, imp2);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, nnreal.clone(), imp1))
    };

    let minor_c = {
        let mut mfc = EnvDeclBuilder::child_of(parent);
        let (fc_id, fc) = mfc.fresh_local(c.causeq.clone());
        // hyps reduce: NNReal.le (mk fa)(mk fb) ≡ CauSeq.le fa fb, etc.
        let h1_ty = c.causeq_le(fa.clone(), fb.clone());
        let (h1_id, h1) = mfc.fresh_local(h1_ty.clone());
        let h2_ty = c.causeq_le(fb.clone(), fc.clone());
        let (h2_id, h2) = mfc.fresh_local(h2_ty.clone());
        // causeq_trans fa fb fc h1 h2 : CauSeq.le fa fc ≡ NNReal.le (mk fa)(mk fc).
        let body = Expr::apps(
            causeq_trans.clone(),
            [fa.clone(), fb.clone(), fc.clone(), h1, h2],
        );
        let e = mfc.mk_lam(h2_id, BinderInfo::Default, h2_ty, body);
        let e = mfc.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
        let e = mfc.mk_lam(fc_id, BinderInfo::Default, c.causeq.clone(), e);
        mfc.finish_child(e)
    };

    Expr::apps(
        quot_ind,
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_c,
            minor_c,
            cv.clone(),
        ],
    )
}

/// `CauSeq.le.trans` as a free function value:
///   `fun f g h hfg hgh => <CauSeq.le f h>` via the ε/2 split.
fn build_causeq_le_trans_fn(c: &LeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.causeq.clone());
    let (g_id, g) = b.fresh_local(c.causeq.clone());
    let (h_id, h) = b.fresh_local(c.causeq.clone());
    let hfg_ty = c.causeq_le(f.clone(), g.clone());
    let (hfg_id, hfg) = b.fresh_local(hfg_ty.clone());
    let hgh_ty = c.causeq_le(g.clone(), h.clone());
    let (hgh_id, hgh) = b.fresh_local(hgh_ty.clone());

    // goal: CauSeq.le f h = ∀ ε, 0<ε → ∃ N, ∀ n, N≤n → vseq f n < vseq h n + ε.
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let half = c.half(eps.clone());
    let heps2 = Expr::apps(c.rat_half_pos.clone(), [eps.clone(), hpos.clone()]);
    let exists_fg = Expr::apps(hfg.clone(), [half.clone(), heps2.clone()]);
    let exists_gh = Expr::apps(hgh.clone(), [half.clone(), heps2]);

    let goal_exists = c.exists_pred(&b, &f, &h, &eps);
    let pred_fg = c.pred_n(&b, &f, &g, &half);
    let pred_gh = c.pred_n(&b, &g, &h, &half);

    let elim_outer = {
        let mut bo = EnvDeclBuilder::child_of(&b);
        let (n1_id, n1) = bo.fresh_local(c.nat.clone());
        let hn1_ty = c.pred_n_at(&bo, &f, &g, &half, &n1);
        let (hn1_id, hn1) = bo.fresh_local(hn1_ty.clone());

        let elim_inner = {
            let mut bi = EnvDeclBuilder::child_of(&bo);
            let (n2_id, n2) = bi.fresh_local(c.nat.clone());
            let hn2_ty = c.pred_n_at(&bi, &g, &h, &half, &n2);
            let (hn2_id, hn2) = bi.fresh_local(hn2_ty.clone());

            let nmax = Expr::apps(c.nat_max.clone(), [n1.clone(), n2.clone()]);

            let witness = {
                let mut bw = EnvDeclBuilder::child_of(&bi);
                let (m_id, m) = bw.fresh_local(c.nat.clone());
                let hle_ty = c.nat_le(nmax.clone(), m.clone());
                let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

                let le_max_l = Expr::apps(c.nat_le_max_left.clone(), [n1.clone(), n2.clone()]);
                let le_max_r = Expr::apps(c.nat_le_max_right.clone(), [n1.clone(), n2.clone()]);
                let n1_le_m =
                    c.nat_le_trans(n1.clone(), nmax.clone(), m.clone(), le_max_l, hle.clone());
                let n2_le_m = c.nat_le_trans(n2.clone(), nmax.clone(), m.clone(), le_max_r, hle);

                // base_fg : vseq f m < vseq g m + ε/2.
                let base_fg = Expr::apps(hn1.clone(), [m.clone(), n1_le_m]);
                // base_gh : vseq g m < vseq h m + ε/2.
                let base_gh = Expr::apps(hn2.clone(), [m.clone(), n2_le_m]);

                let vf = c.vseq(&f, &m);
                let vg = c.vseq(&g, &m);
                let vh = c.vseq(&h, &m);

                // step1: (vg + ε/2) < ((vh + ε/2)+ε/2) via add_lt_add_right vg (vh+ε/2)(ε/2) base_gh.
                let vh_half = c.add(vh.clone(), half.clone());
                let step1 = c.add_lt_add_right(vg.clone(), vh_half.clone(), half.clone(), base_gh);
                // step2: vf < ((vh+ε/2)+ε/2) via lt_trans vf (vg+ε/2) (…) base_fg step1.
                let vg_half = c.add(vg.clone(), half.clone());
                let vh_hh = c.add(vh_half.clone(), half.clone());
                let step2 = c.lt_trans(vf.clone(), vg_half, vh_hh.clone(), base_fg, step1);
                // recombine ((vh+ε/2)+ε/2)=(vh+ε).
                let rec = c.eq_recombine(&bw, &vh, &eps);
                let vh_eps = c.add(vh.clone(), eps.clone());
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.lt(vf.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let proof = c.subst(motive, vh_hh, vh_eps, rec, step2);

                let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
                let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
                bw.finish_child(e)
            };

            let intro = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), c.pred_n(&bi, &f, &h, &eps), nmax, witness],
            );
            let e = bi.mk_lam(hn2_id, BinderInfo::Default, hn2_ty, intro);
            let e = bi.mk_lam(n2_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };

        let elim_gh = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nat.clone(),
                pred_gh.clone(),
                goal_exists.clone(),
                exists_gh.clone(),
                elim_inner,
            ],
        );
        let e = bo.mk_lam(hn1_id, BinderInfo::Default, hn1_ty, elim_gh);
        let e = bo.mk_lam(n1_id, BinderInfo::Default, c.nat.clone(), e);
        bo.finish_child(e)
    };

    let elim_fg = Expr::apps(
        c.exists_elim.clone(),
        [
            c.nat.clone(),
            pred_fg.clone(),
            goal_exists,
            exists_fg,
            elim_outer,
        ],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim_fg);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(hgh_id, BinderInfo::Default, hgh_ty, e);
    let e = b.mk_lam(hfg_id, BinderInfo::Default, hfg_ty, e);
    let e = b.mk_lam(h_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// Build `NNReal.ofRat_le_ofRat`. After fixing a,b,ha,hb,hle, the goal
/// `NNReal.le (ofRat a ha)(ofRat b hb)` reduces (Quot.lift comp) to
/// `CauSeq.le (const (NNRat.ofRat a ha))(const (NNRat.ofRat b hb))`, whose body
/// at index n is `a < b + ε` (the constant seq's val ≡ a / b). For all ε>0 take
/// N := Nat.zero and prove `a < b + ε` via lt_of_le_of_lt a b (b+ε) hle (b<b+ε).
fn build_ofrat_le_proof(c: &LeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let of_rat = Expr::const_(Name::from_string("NNReal.ofRat"), vec![]);
    let nonneg = |x: Expr| Expr::apps(c.rat_le.clone(), [c.rat_zero.clone(), x]);
    let rat_le = |x: Expr, y: Expr| Expr::apps(c.rat_le.clone(), [x, y]);

    let (av_id, av) = b.fresh_local(c.rat.clone());
    let (bvv_id, bvv) = b.fresh_local(c.rat.clone());
    let ha_ty = nonneg(av.clone());
    let (ha_id, ha) = b.fresh_local(ha_ty.clone());
    let hb_ty = nonneg(bvv.clone());
    let (hb_id, hb) = b.fresh_local(hb_ty.clone());
    let hle_ty = rat_le(av.clone(), bvv.clone());
    let (hle_id, hle) = b.fresh_local(hle_ty.clone());

    // ofRat a ha, ofRat b hb (we don't need them in the proof body; the goal type
    // mentions them but the proof reduces through to constant `a`/`b`).
    let _oa = Expr::apps(of_rat.clone(), [av.clone(), ha.clone()]);
    let _ob = Expr::apps(of_rat.clone(), [bvv.clone(), hb.clone()]);

    // The proof of `CauSeq.le (const (ofRat a))(const (ofRat b))`:
    //   ∀ ε, 0<ε → ∃ N=0, ∀ n, 0≤n → a < b + ε.
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // a < b + ε : lt_of_le_of_lt a b (b+ε) hle (b < b+ε).
    //   b < b+ε from add_lt_add_left 0 ε b hpos : (b+0) < (b+ε), subst along add_zero b.
    let b_plus_eps = c.add(bvv.clone(), eps.clone());
    let step = c.add_lt_add_left(c.rat_zero.clone(), eps.clone(), bvv.clone(), hpos.clone());
    let b_plus_zero = c.add(bvv.clone(), c.rat_zero.clone());
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(t, b_plus_eps.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let b_lt_b_eps = c.subst(
        motive,
        b_plus_zero,
        bvv.clone(),
        c.add_zero(bvv.clone()),
        step,
    );
    let a_lt_b_eps = c.lt_of_le_of_lt(
        av.clone(),
        bvv.clone(),
        b_plus_eps.clone(),
        hle.clone(),
        b_lt_b_eps,
    );

    // The N-predicate for the constant `CauSeq.le`: at index m the body is
    //   vseq (const (ofRat a)) m < vseq (const (ofRat b)) m + ε ≡ a < b + ε.
    // We construct the witness lambda directly; the conclusion type uses the
    // const-form which is DEFEQ to `a < b + ε`.
    let oa_cs = const_causeq(c, &b, &av, &ha);
    let ob_cs = const_causeq(c, &b, &bvv, &hb);

    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle0_ty = c.nat_le(nat_zero.clone(), m.clone());
        let (hle0_id, _h) = bw.fresh_local(hle0_ty.clone());
        // proof has type a < b+ε, which is defeq to vseq(const(ofRat a)) m < vseq(const(ofRat b)) m + ε.
        let e = bw.mk_lam(hle0_id, BinderInfo::Default, hle0_ty, a_lt_b_eps.clone());
        let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
        bw.finish_child(e)
    };

    let intro = Expr::apps(
        c.exists_intro.clone(),
        [
            c.nat.clone(),
            c.pred_n(&b, &oa_cs, &ob_cs, &eps),
            nat_zero,
            witness,
        ],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(hle_id, BinderInfo::Default, hle_ty, e);
    let e = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, e);
    let e = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, e);
    let e = b.mk_lam(bvv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(av_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNReal.CauSeq.const (NNRat.ofRat x hx) : CauSeq` — the constant Cauchy
/// sequence at the nonneg rational `x`.
fn const_causeq(c: &LeConsts, _parent: &EnvDeclBuilder, x: &Expr, hx: &Expr) -> Expr {
    let _ = c;
    let nnrat_of = Expr::const_(Name::from_string("NNRat.ofRat"), vec![]);
    let causeq_const = Expr::const_(Name::from_string("NNReal.CauSeq.const"), vec![]);
    let q = Expr::apps(nnrat_of, [x.clone(), hx.clone()]);
    Expr::app(causeq_const, q)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const DEFS: &[&str] = &["NNReal.CauSeq.le", "NNReal.le"];
    const THEOREMS: &[&str] = &["NNReal.le.refl", "NNReal.le.trans", "NNReal.ofRat_le_ofRat"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_le()
            .expect("init_algebra_nnreal_le");
        env.init_algebra_nnreal_le().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_le_present_and_kernel_check() {
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
    fn test_nnreal_le_theorems_constructive_empty_closure() {
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
