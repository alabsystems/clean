// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the nonneg-real order `NNReal.le` (+ `le_refl`,
//! `le_trans`).
//!
//! # Why this module exists
//!
//! With `NNReal` a setoid quotient (`refl`/`symm`/`trans`) carrying an additive
//! commutative monoid (`algebra_nnreal_add{,_laws}.rs`), the next carrier rung is
//! the order. `NNReal.le` lifts the standard strict-eventual Cauchy order on
//! representatives through a binary `Quot.lift` into `Prop` — exactly the
//! `Qat.le` template (`algebra_rat_quotient.rs`): an inner `Quot.lift.{1,1}`
//! over the second operand whose respect proof is `propext` of two implications,
//! wrapped in an outer `Quot.ind` respect for the first operand.
//!
//! # The relation (deliberately strict-eventual)
//!
//! `NNReal.CauSeq.LE f g := ∀ ε, Rat.lt 0 ε →`
//! `   ∃ N, ∀ n, Nat.le N n → Rat.lt (val (seq f n)) (Rat.add (val (seq g n)) ε)`
//!
//! i.e. "`f` is eventually below `g` up to every positive slack". This is the
//! left conjunct of `Equiv`'s body; on the diagonal it is the `refl` pattern,
//! and it is the right order for Cauchy reals (`x ≤ y` iff `x − y ≤ ε` for all
//! `ε > 0`). Crucially its respect-under-`Equiv` proof needs only ε/2 splits
//! (the same `Rat.add_halves` / `Rat.add_assoc` recombination as `Equiv.trans`),
//! NOT thirds — so it is fully closeable axiom-free with the on-main Rat surface.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.CauSeq.LE : CauSeq → CauSeq → Prop`           (Definition)
//! - `NNReal.le : NNReal → NNReal → Prop`                  (binary Quot.lift)
//! - `NNReal.le_refl  : ∀ x, NNReal.le x x`                (Theorem)
//! - `NNReal.le_trans : ∀ x y z, NNReal.le x y → NNReal.le y z → NNReal.le x z`
//!
//! Each theorem is `Declaration::Theorem`, `ProofQuality::Constructive`, with an
//! empty admitted-axiom closure (foundational only: `propext`/`Quot.sound`/
//! `Classical.choice`). NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! The respect proofs are factored into `le_respects.rs` to keep both files
//! under the 500-line cap.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the nonneg-real order.
pub(crate) struct NNLeConsts {
    pub(crate) prop: Expr,
    pub(crate) nat: Expr,
    pub(crate) rat: Expr,
    pub(crate) rat_zero: Expr,
    pub(crate) rat_two: Expr,
    pub(crate) nnrat_val: Expr,
    pub(crate) causeq: Expr,
    pub(crate) causeq_seq: Expr,
    pub(crate) causeq_equiv: Expr,
    pub(crate) causeq_le: Expr,
    pub(crate) nnreal: Expr,
    pub(crate) rat_add: Expr,
    pub(crate) rat_div: Expr,
    pub(crate) rat_lt: Expr,
    pub(crate) nat_le: Expr,
    // Lemmas.
    pub(crate) rat_half_pos: Expr,
    pub(crate) rat_add_lt_add_right: Expr,
    pub(crate) rat_add_lt_add_left: Expr,
    pub(crate) rat_lt_trans: Expr,
    pub(crate) rat_add_assoc: Expr,
    pub(crate) rat_add_halves: Expr,
    pub(crate) rat_add_zero: Expr,
    pub(crate) nat_max: Expr,
    pub(crate) nat_le_max_left: Expr,
    pub(crate) nat_le_max_right: Expr,
    pub(crate) nat_le_trans: Expr,
    pub(crate) nat_zero: Expr,
    // Logic.
    pub(crate) and_c: Expr,
    pub(crate) and_left: Expr,
    pub(crate) and_right: Expr,
    pub(crate) exists_c: Expr,
    pub(crate) exists_intro: Expr,
    pub(crate) exists_elim: Expr,
    pub(crate) propext: Expr,
    // Eq.{1} over Rat.
    #[cfg(test)]
    pub(crate) eq_rat: Expr,
    pub(crate) eq_trans: Expr,
    pub(crate) eq_subst: Expr,
    pub(crate) congr_arg: Expr,
    // Quot machinery at level 1.
    pub(crate) quot_mk: Expr,
    pub(crate) quot_lift_prop: Expr,
    pub(crate) quot_ind: Expr,
}

impl NNLeConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_two: k("Rat.two"),
            nnrat_val: k("NNRat.val"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_le: k("NNReal.CauSeq.LE"),
            nnreal: k("NNReal"),
            rat_add: k("Rat.add"),
            rat_div: k("Rat.div"),
            rat_lt: k("Rat.lt"),
            nat_le: k("Nat.le"),
            rat_half_pos: k("Rat.half_pos"),
            rat_add_lt_add_right: k("Rat.add_lt_add_right"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_lt_trans: k("Rat.lt_trans"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_halves: k("Rat.add_halves"),
            rat_add_zero: k("Rat.add_zero"),
            nat_max: k("Nat.max"),
            nat_le_max_left: k("Nat.le_max_left"),
            nat_le_max_right: k("Nat.le_max_right"),
            nat_le_trans: k("Nat.le_trans"),
            nat_zero: k("Nat.zero"),
            and_c: k("And"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![lvl1.clone()]),
            propext: k("propext"),
            #[cfg(test)]
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(
                Name::from_string("congrArg"),
                vec![lvl1.clone(), lvl1.clone()],
            ),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            quot_lift_prop: Expr::const_(
                Name::from_string("Quot.lift"),
                vec![lvl1.clone(), lvl1.clone()],
            ),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![lvl1]),
        }
    }

    // ── term constructors ───────────────────────────────────────────────────

    pub(crate) fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    pub(crate) fn half(&self, eps: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [eps, self.rat_two.clone()])
    }
    pub(crate) fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    pub(crate) fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `NNRat.val (NNReal.CauSeq.seq x n) : Rat`.
    pub(crate) fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(self.causeq_seq.clone(), x.clone());
        let at = Expr::app(seq, n.clone());
        Expr::app(self.nnrat_val.clone(), at)
    }
    /// `NNReal.CauSeq.Equiv a b : Prop`.
    pub(crate) fn equiv(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [a, b])
    }
    /// `NNReal.CauSeq.LE a b : Prop`.
    pub(crate) fn causeq_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_le.clone(), [a, b])
    }
    /// `@Quot.mk.{1} CauSeq Equiv l : NNReal`.
    pub(crate) fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }

    /// The `∀ N`-predicate body for the strict-eventual one-sided bound of `(a,b)`
    /// at tolerance `eps`:
    ///   `fun N => ∀ n, Nat.le N n → Rat.lt (vseq a n) (vseq b n + eps)`.
    pub(crate) fn pred_n(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n_cap) = bn.fresh_local(self.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(self.nat.clone());
            let hle = self.nat_le(n_cap.clone(), m.clone());
            let (hle_id, _h) = bi.fresh_local(hle.clone());
            let concl = self.lt(self.vseq(a, &m), self.add(self.vseq(b, &m), eps.clone()));
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
            bi.finish_child(e)
        };
        let lam = bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner);
        bn.finish_child(lam)
    }

    /// `∃ N, pred_n a b eps N : Prop`.
    pub(crate) fn exists_pred(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        b: &Expr,
        eps: &Expr,
    ) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nat.clone(), self.pred_n(parent, a, b, eps)],
        )
    }

    /// `pred_n a b eps N` fully applied (re-derived with `N := cap`).
    pub(crate) fn pred_n_at(
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
        let (hle_id, _h) = bn.fresh_local(hle.clone());
        let concl = self.lt(self.vseq(a, &m), self.add(self.vseq(b, &m), eps.clone()));
        let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bn.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
        bn.finish_child(e)
    }

    /// The full `NNReal.CauSeq.LE`-body for a fixed pair `(f,g)` (a `Prop`):
    ///   `∀ ε, Rat.lt 0 ε → ∃ N, ∀ n, Nat.le N n → Rat.lt (vseq f n)(vseq g n + ε)`.
    pub(crate) fn le_body(&self, parent: &EnvDeclBuilder, f: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (eps_id, eps) = b.fresh_local(self.rat.clone());
        let hpos = self.lt(self.rat_zero.clone(), eps.clone());
        let (hpos_id, _h) = b.fresh_local(hpos.clone());
        let exists_n = self.exists_pred(&b, f, g, &eps);
        let e = b.mk_pi(hpos_id, BinderInfo::Default, hpos, exists_n);
        let e = b.mk_pi(eps_id, BinderInfo::Default, self.rat.clone(), e);
        b.finish_child(e)
    }

    // ── proof constructors (shared with le_respects.rs) ──────────────────────

    pub(crate) fn add_lt_add_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_right.clone(), [a, b, cc, h])
    }
    pub(crate) fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    pub(crate) fn lt_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_lt_trans.clone(), [a, b, cc, hab, hbc])
    }
    pub(crate) fn add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    pub(crate) fn add_halves(&self, eps: Expr) -> Expr {
        Expr::app(self.rat_add_halves.clone(), eps)
    }
    pub(crate) fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    pub(crate) fn eq_trans_rat(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    pub(crate) fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    pub(crate) fn congr_arg(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    pub(crate) fn nat_le_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.nat_le_trans.clone(), [a, b, cc, hab, hbc])
    }
    pub(crate) fn and_left(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_left.clone(), [p, q, h])
    }
    pub(crate) fn and_right(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_right.clone(), [p, q, h])
    }
    /// `@propext P1 P2 (Iff.intro P1 P2 fwd bwd) : @Eq Prop P1 P2`.
    ///
    /// Faithful Lean `propext : {a b} → (a ↔ b) → a = b` takes a single `Iff`;
    /// package the two implications via `Iff.intro` (same proof content).
    pub(crate) fn propext(&self, p1: Expr, p2: Expr, fwd: Expr, bwd: Expr) -> Expr {
        let iff = Expr::apps(
            Expr::const_(Name::from_string("Iff.intro"), vec![]),
            [p1.clone(), p2.clone(), fwd, bwd],
        );
        Expr::apps(self.propext.clone(), [p1, p2, iff])
    }

    /// `eq_recombine vx eps : Eq Rat ((vx + eps/2) + eps/2) (vx + eps)` — the
    /// ε/2-recombination (`add_assoc` then `congrArg (vx+·) (add_halves eps)`).
    pub(crate) fn eq_recombine(&self, parent: &EnvDeclBuilder, vx: &Expr, eps: &Expr) -> Expr {
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
        self.eq_trans_rat(lhs, mid, rhs, assoc, congr)
    }
}

impl Environment {
    /// Register the nonneg-real order: `NNReal.CauSeq.LE`, `NNReal.le`,
    /// `NNReal.le_refl`, `NNReal.le_trans`. Idempotent.
    pub fn init_algebra_nnreal_le_recovered(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_trans()?; // CauSeq, Equiv (refl/symm/trans), …
        self.init_propext()?;
        self.init_algebra_rat_half_pos()?; // Rat.half_pos, Rat.add_halves, Rat.two
        self.register_rat_add_lt_add_right()?;
        self.register_rat_add_lt_add_left()?;
        self.register_rat_lt_trans()?;
        self.register_nat_minmax_proofs()?;
        self.register_nat_le_trans_proof()?;
        self.init_rat_field_inst()?; // Rat.add_assoc, Rat.add_zero

        let c = NNLeConsts::new();
        self.register_nnreal_causeq_le_recovered(&c)?;
        self.register_nnreal_le_recovered(&c)?;
        self.register_nnreal_le_refl_recovered(&c)?;
        self.register_nnreal_le_trans_recovered(&c)?;
        Ok(())
    }

    /// `NNReal.CauSeq.LE : CauSeq → CauSeq → Prop` (the strict-eventual order).
    fn register_nnreal_causeq_le_recovered(&mut self, c: &NNLeConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNReal.CauSeq.LE"))
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
            name: Name::from_string("NNReal.CauSeq.LE"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.le : NNReal → NNReal → Prop`, a binary `Quot.lift` into `Prop`.
    fn register_nnreal_le_recovered(&mut self, c: &NNLeConsts) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("NNReal.le")).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.nnreal.clone(),
            Expr::pi(BinderInfo::Default, c.nnreal.clone(), c.prop.clone()),
        );
        let value = crate::env::algebra_nnreal_le_respects::build_nnreal_le_value(c);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNReal.le"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.le_refl : ∀ x, NNReal.le x x`.
    ///
    /// `Quot.ind` on `x`: at `mk p` the goal reduces to `CauSeq.LE p p`, the
    /// `refl` pattern (`val(p n) < val(p n) + ε` from `add_lt_add_left 0 ε v hpos`
    /// transported along `add_zero`, with `N := 0`).
    fn register_nnreal_le_refl_recovered(&mut self, c: &NNLeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.le_refl");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.nnreal.clone());
            let concl = Expr::apps(
                Expr::const_(Name::from_string("NNReal.le"), vec![]),
                [x.clone(), x.clone()],
            );
            let e = b.mk_pi(x_id, BinderInfo::Default, c.nnreal.clone(), concl);
            b.finish(e)
        };
        let value = crate::env::algebra_nnreal_le_respects::build_le_refl_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.le_trans : ∀ x y z, NNReal.le x y → NNReal.le y z → NNReal.le x z`.
    ///
    /// Triple `Quot.ind`: at `(mk p)(mk q)(mk r)` the goal reduces to
    /// `CauSeq.LE p q → CauSeq.LE q r → CauSeq.LE p r`, the ε/2-chain
    /// (instantiate both hyps at ε/2, `N := max N1 N2`, recombine).
    fn register_nnreal_le_trans_recovered(&mut self, c: &NNLeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.le_trans");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
        let le = |a: Expr, b: Expr| Expr::apps(nnle.clone(), [a, b]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.nnreal.clone());
            let (y_id, y) = b.fresh_local(c.nnreal.clone());
            let (z_id, z) = b.fresh_local(c.nnreal.clone());
            let hxy = le(x.clone(), y.clone());
            let (hxy_id, _h1) = b.fresh_local(hxy.clone());
            let hyz = le(y.clone(), z.clone());
            let (hyz_id, _h2) = b.fresh_local(hyz.clone());
            let concl = le(x.clone(), z.clone());
            let e = b.mk_pi(hyz_id, BinderInfo::Default, hyz, concl);
            let e = b.mk_pi(hxy_id, BinderInfo::Default, hxy, e);
            let e = b.mk_pi(z_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = crate::env::algebra_nnreal_le_respects::build_le_trans_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
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

    const DEFS: &[&str] = &["NNReal.CauSeq.LE", "NNReal.le"];
    const THEOREMS: &[&str] = &["NNReal.le_refl", "NNReal.le_trans"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_le_recovered()
            .expect("init_algebra_nnreal_le_recovered");
        env.init_algebra_nnreal_le_recovered().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_le_kernel_check() {
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
