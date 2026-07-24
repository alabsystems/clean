// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — the multiplicative- and additive-unit identities the
//! polynomial-identity helper for M2 lemma (A) needs:
//!
//! ```text
//!   NNReal.mul_one  : ∀ a : NNReal, NNReal.mul a (NNReal.ofRat Rat.one _) = a
//!   NNReal.add_zero : ∀ a : NNReal, NNReal.add a NNReal.zero            = a
//! ```
//!
//! # Why this module exists (ring-normalizer bricks)
//!
//! The deg-9 polynomial identity for lemma (A) is proved by a Rust ring-
//! normalizer that, among other things, must DROP the `·1` and `+0` identities
//! left behind by coefficient folding. The `NNReal` carrier already shipped
//! `mul_comm/assoc`, `add_comm/assoc`, `mul_add/add_mul`, `mul_zero`, `zero_add`,
//! but never the right-unit `mul_one` / `add_zero`. This module supplies them.
//!
//! # Proof shape (mirrors `NNReal.mul_zero` / `NNReal.zero_add`)
//!
//! Both are `Quot.ind` on the single `NNReal` argument followed by a
//! `Quot.sound` on a pointwise-`Rat`-equality `Equiv`:
//!
//! - `mul_one`: `NNReal.mul (mk fa) (NNReal.ofRat 1 _) ≡ mk (CauSeq.mul fa
//!   (const NNRat.one))`; the RHS is `mk fa`. Pointwise,
//!   `val(seq(mul fa (const one)) m) ≡ val(NNRat.mul (fa m) NNRat.one) ≡
//!   (val(fa m))·(val NNRat.one) ≡ (val(fa m))·1` (since `val NNRat.one ≡ 1`),
//!   which `Rat.mul_one (val(fa m))` identifies with `val(fa m) ≡ val(seq fa m)`.
//! - `add_zero`: `NNReal.add (mk fa) NNReal.zero ≡ mk (CauSeq.add fa
//!   (const (NNRat.ofRat 0 _)))`; the RHS is `mk fa`. Pointwise,
//!   `val(seq(add fa (const 0)) m) ≡ (val(fa m)) + 0` (since `NNRat.val_add`
//!   holds by `refl` and `val(const-zero m) ≡ 0`), which `Rat.add_zero
//!   (val(fa m))` identifies with `val(fa m) ≡ val(seq fa m)`.
//!
//! The two `<…+ε` `Equiv` bounds then transport `vL ↔ vR` along that equality
//! (`Eq.subst` + `Rat.add_lt_add_left`/`Rat.add_zero`), exactly as the on-main
//! `NNReal.mul_zero` / `NNReal.zero_add` do.
//!
//! Each is `Declaration::Theorem`, `ProofQuality::Constructive`, with an empty
//! admitted-axiom closure (foundational only). NO `sorry` / `add_decl_unchecked`
//! / `add_decl_structural`.
//!
//! # NOT built here: `NNReal.le_of_mul_le_mul_left` (positive-factor cancel)
//!
//! The third requested brick (`0<c ∧ c·a ≤ c·b ⟹ a ≤ b`) is BLOCKED on the
//! current carrier: the `NNReal` order layer ships NO strict-positivity
//! predicate (`NNReal.lt` / `0 < c` does not exist), and the reverse cancel
//! needs an eventual positive rational LOWER bound on the representative of `c`
//! (the dual of `IsCauchy_bounded`), which is also unbuilt. The forward
//! `NNReal.mul_le_mul_left` is itself a heavy `deltaMul`/`mul_close`/bounded
//! proof; the reverse direction's δ-choice infra is explicitly absent (see
//! `algebra_nnreal_pow32_bound.rs`). The two unit bricks land unconditionally.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors shared by the two unit lemmas (the
/// `Quot.sound`/CauSeq surface), mirroring `MulZeroConsts`/`ZeroAddConsts`.
struct UnitConsts {
    nat: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_lt: Expr,
    rat_add: Expr,
    rat_add_lt_add_left: Expr,
    rat_add_zero: Expr,
    rat_mul_one: Expr,
    rat_le_refl: Expr,
    rat_zero_le_one: Expr,
    nnrat_val: Expr,
    nnrat_one: Expr,
    nnrat_of_rat: Expr,
    nnreal_zero: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_add: Expr,
    causeq_mul: Expr,
    causeq_const: Expr,
    nat_le: Expr,
    exists_intro: Expr,
    and_intro: Expr,
    eq1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    quot_sound: Expr,
    quot_ind: Expr,
}

impl UnitConsts {
    fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_lt: k("Rat.lt"),
            rat_add: k("Rat.add"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_add_zero: k("Rat.add_zero"),
            rat_mul_one: k("Rat.mul_one"),
            rat_le_refl: k("Rat.le_refl"),
            rat_zero_le_one: k("Rat.zero_le_one"),
            nnrat_val: k("NNRat.val"),
            nnrat_one: k("NNRat.one"),
            nnrat_of_rat: k("NNRat.ofRat"),
            nnreal_zero: k("NNReal.zero"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_add: k("NNReal.CauSeq.add"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            causeq_const: k("NNReal.CauSeq.const"),
            nat_le: k("Nat.le"),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            and_intro: k("And.intro"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![lvl1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![lvl1]),
        }
    }

    fn nnreal(&self) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Quot"), vec![Level::succ(Level::zero())]),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
    fn nnreal_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.mul"), vec![]),
            [a, b],
        )
    }
    fn nnreal_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.add"), vec![]),
            [a, b],
        )
    }
    fn eq_nnreal(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nnreal(), a, b])
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    fn seq_at(&self, x: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone())
    }
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        self.val(self.seq_at(x, n))
    }
    fn causeq_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_add.clone(), [a, b])
    }
    fn causeq_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_mul.clone(), [a, b])
    }
    /// `NNReal.CauSeq.const (NNRat.ofRat 0 h0)` — the zero const seq.
    fn zero_const(&self, h0: &Expr) -> Expr {
        let zero_nn = Expr::apps(
            self.nnrat_of_rat.clone(),
            [self.rat_zero.clone(), h0.clone()],
        );
        Expr::app(self.causeq_const.clone(), zero_nn)
    }
    /// `NNReal.CauSeq.const NNRat.one` — the one const seq (`NNRat.one ≡ ofRat 1`).
    fn one_const(&self) -> Expr {
        Expr::app(self.causeq_const.clone(), self.nnrat_one.clone())
    }
    fn quot_sound(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), a, b, h],
        )
    }
    fn eq_symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `NNReal.ofRat Rat.one Rat.zero_le_one : NNReal` — the canonical NNReal one.
    fn nnreal_one(&self) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.ofRat"), vec![]),
            [self.rat_one.clone(), self.rat_zero_le_one.clone()],
        )
    }
    /// `0 ≤ 0` witness (`Rat.le_refl Rat.zero`) inside the zero const seq.
    fn h0(&self) -> Expr {
        Expr::app(self.rat_le_refl.clone(), self.rat_zero.clone())
    }
}

impl Environment {
    /// Register `NNReal.mul_one` and `NNReal.add_zero`. Idempotent;
    /// foundational-only closure.
    pub fn init_algebra_nnreal_semiring_units(&mut self) -> Result<(), EnvError> {
        // NNReal.mul, NNReal.add, the CauSeq carrier, NNRat.* val lemmas.
        self.init_algebra_nnreal_finsum_smul()?; // NNReal.mul_zero, NNRat.*, mul carrier
        self.init_algebra_nnreal_zero_add()?; // NNReal.add, NNReal.zero, CauSeq.add
        self.init_algebra_nnreal_nnrat()?; // NNRat.one, NNRat.val_mul, NNRat.ofRat, Rat.zero_le_one
        self.init_rat()?; // Rat.mul_one (constructive Rat-quotient theorem)
        self.init_eq()?;

        self.register_nnreal_mul_one()?;
        self.register_nnreal_add_zero()?;
        Ok(())
    }

    /// `NNReal.mul_one : ∀ a : NNReal, NNReal.mul a (NNReal.ofRat 1 _) = a`.
    fn register_nnreal_mul_one(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.mul_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = UnitConsts::new();
        let nnreal = c.nnreal();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let lhs = c.nnreal_mul(a.clone(), c.nnreal_one());
            let concl = c.eq_nnreal(lhs, a.clone());
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), concl);
            b.finish(e)
        };
        let value = build_mul_one_value(&c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.add_zero : ∀ a : NNReal, NNReal.add a NNReal.zero = a`.
    fn register_nnreal_add_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = UnitConsts::new();
        let nnreal = c.nnreal();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let lhs = c.nnreal_add(a.clone(), c.nnreal_zero.clone());
            let concl = c.eq_nnreal(lhs, a.clone());
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), concl);
            b.finish(e)
        };
        let value = build_add_zero_value(&c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build `NNReal.mul_one` value via `Quot.ind` on `a`.
fn build_mul_one_value(c: &UnitConsts, nnreal: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (av_id, av) = b.fresh_local(nnreal.clone());

    // Quot.ind motive: fun x => Eq NNReal (mul x (ofRat 1)) x.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let lhs = c.nnreal_mul(x.clone(), c.nnreal_one());
        let body = c.eq_nnreal(lhs, x.clone());
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), body))
    };
    // minor fa : Eq NNReal (mul (mk fa)(ofRat 1)) (mk fa).
    //   mul (mk fa)(ofRat 1) ≡ mk (CauSeq.mul fa (const NNRat.one)); RHS is mk fa.
    //   Close by Quot.sound on Equiv (CauSeq.mul fa (const one)) fa.
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (fa_id, fa) = mf.fresh_local(c.causeq.clone());
        let cl = c.causeq_mul(fa.clone(), c.one_const());
        let cr = fa.clone();
        let equiv = build_mul_one_equiv(c, &mf, &fa);
        let body = c.quot_sound(cl, cr, equiv);
        mf.finish_child(mf.mk_lam(fa_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    let ind = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            av.clone(),
        ],
    );
    let e = b.mk_lam(av_id, BinderInfo::Default, nnreal.clone(), ind);
    b.finish(e)
}

/// Build `Equiv (CauSeq.mul fa (const NNRat.one)) fa`. Pointwise:
/// `vL = val(seq(mul fa (const one)) m) ≡ val(NNRat.mul (fa m) NNRat.one) ≡
/// (val(fa m))·(val NNRat.one) ≡ (val(fa m))·1` (defeq via `NNRat.val_mul` /
/// `val NNRat.one ≡ 1`); `Rat.mul_one (val(fa m)) : (val(fa m))·1 = val(fa m)`
/// is defeq to `vL = vR`.
fn build_mul_one_equiv(c: &UnitConsts, parent: &EnvDeclBuilder, fa: &Expr) -> Expr {
    let cl = c.causeq_mul(fa.clone(), c.one_const());
    let cr = fa.clone();

    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let pred = build_units_pred(c, &b, &cl, &cr, &eps);
    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(c.nat_zero.clone(), m.clone());
        let (hle_id, _hle) = bw.fresh_local(hle_ty.clone());

        let vl = c.vseq(&cl, &m);
        let vr = c.vseq(&cr, &m);
        // h_eq : vL = vR.  vL ≡ (val(fa m))·1, vR ≡ val(fa m); `Rat.mul_one vR`.
        let h_eq = Expr::app(c.rat_mul_one.clone(), vr.clone());

        let proof = build_units_bounds(c, &bw, &vl, &vr, &eps, &hpos, h_eq);

        let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
        let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
        bw.finish_child(e)
    };

    let intro = Expr::apps(
        c.exists_intro.clone(),
        [c.nat.clone(), pred, c.nat_zero.clone(), witness],
    );
    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish_child(e)
}

/// Build `NNReal.add_zero` value via `Quot.ind` on `a`.
fn build_add_zero_value(c: &UnitConsts, nnreal: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (av_id, av) = b.fresh_local(nnreal.clone());

    // Quot.ind motive: fun x => Eq NNReal (add x NNReal.zero) x.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let lhs = c.nnreal_add(x.clone(), c.nnreal_zero.clone());
        let body = c.eq_nnreal(lhs, x.clone());
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), body))
    };
    // minor fa : Eq NNReal (add (mk fa) NNReal.zero) (mk fa).
    //   add (mk fa) NNReal.zero ≡ mk (CauSeq.add fa zc) ; RHS is mk fa.
    //   Close by Quot.sound on Equiv (CauSeq.add fa zc) fa.
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (fa_id, fa) = mf.fresh_local(c.causeq.clone());
        let zc = c.zero_const(&c.h0());
        let cl = c.causeq_add(fa.clone(), zc.clone());
        let cr = fa.clone();
        let equiv = build_add_zero_equiv(c, &mf, &fa);
        let body = c.quot_sound(cl, cr, equiv);
        mf.finish_child(mf.mk_lam(fa_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    let ind = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            av.clone(),
        ],
    );
    let e = b.mk_lam(av_id, BinderInfo::Default, nnreal.clone(), ind);
    b.finish(e)
}

/// Build `Equiv (CauSeq.add fa zc) fa`. Pointwise: `vL = val(seq(add fa zc) m) ≡
/// val(fa m) + 0` (`NNRat.val_add` holds by refl, `val(zc m) ≡ 0`), and
/// `Rat.add_zero (val(fa m))` identifies that with `val(fa m) ≡ val(seq fa m)`.
fn build_add_zero_equiv(c: &UnitConsts, parent: &EnvDeclBuilder, fa: &Expr) -> Expr {
    let zc = c.zero_const(&c.h0());
    let cl = c.causeq_add(fa.clone(), zc.clone());
    let cr = fa.clone();

    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let pred = build_units_pred(c, &b, &cl, &cr, &eps);
    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(c.nat_zero.clone(), m.clone());
        let (hle_id, _hle) = bw.fresh_local(hle_ty.clone());

        let vl = c.vseq(&cl, &m);
        let vr = c.vseq(&cr, &m);
        // h_eq : vL = vR.  vL ≡ (val(fa m)) + 0, vR ≡ val(fa m); `Rat.add_zero vR`.
        let h_eq = Expr::app(c.rat_add_zero.clone(), vr.clone());

        let proof = build_units_bounds(c, &bw, &vl, &vr, &eps, &hpos, h_eq);

        let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
        let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
        bw.finish_child(e)
    };

    let intro = Expr::apps(
        c.exists_intro.clone(),
        [c.nat.clone(), pred, c.nat_zero.clone(), witness],
    );
    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish_child(e)
}

/// Given `h_eq : vL = vR`, `hpos : 0<ε`, build the conjunction
/// `And (vL < vR + ε)(vR < vL + ε)` (the per-index `Equiv` payload).
fn build_units_bounds(
    c: &UnitConsts,
    parent: &EnvDeclBuilder,
    vl: &Expr,
    vr: &Expr,
    eps: &Expr,
    hpos: &Expr,
    h_eq: Expr,
) -> Expr {
    // vL < vR + ε from vR < vR+ε, subst vR → vL via symm h_eq.
    let vr_eps = c.radd(vr.clone(), eps.clone());
    let vr_lt = build_self_lt_add(c, parent, vr, eps, hpos);
    let motive_l = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(t, vr_eps.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let left = c.subst_rat(
        motive_l,
        vr.clone(),
        vl.clone(),
        c.eq_symm_rat(vl.clone(), vr.clone(), h_eq.clone()),
        vr_lt,
    );

    // vR < vL + ε from vL < vL+ε, subst LHS vL → vR via h_eq.
    let vl_eps = c.radd(vl.clone(), eps.clone());
    let vl_lt = build_self_lt_add(c, parent, vl, eps, hpos);
    let motive_r = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(t, vl_eps.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let right = c.subst_rat(motive_r, vl.clone(), vr.clone(), h_eq, vl_lt);

    let l_ty = c.lt(vl.clone(), vr_eps);
    let r_ty = c.lt(vr.clone(), vl_eps);
    Expr::apps(c.and_intro.clone(), [l_ty, r_ty, left, right])
}

/// `v < v + ε` from `0<ε`.
fn build_self_lt_add(
    c: &UnitConsts,
    parent: &EnvDeclBuilder,
    v: &Expr,
    eps: &Expr,
    hpos: &Expr,
) -> Expr {
    let h = Expr::apps(
        c.rat_add_lt_add_left.clone(),
        [c.rat_zero.clone(), eps.clone(), v.clone(), hpos.clone()],
    );
    let v_zero = c.radd(v.clone(), c.rat_zero.clone());
    let v_eps = c.radd(v.clone(), eps.clone());
    let add_zero = Expr::app(c.rat_add_zero.clone(), v.clone());
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.lt(t, v_eps.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst_rat(motive, v_zero, v.clone(), add_zero, h)
}

/// `fun N => ∀ n, N≤n → And (vseq cl n < vseq cr n + ε)(vseq cr n < vseq cl n + ε)`.
fn build_units_pred(
    c: &UnitConsts,
    parent: &EnvDeclBuilder,
    cl: &Expr,
    cr: &Expr,
    eps: &Expr,
) -> Expr {
    let and_c = Expr::const_(Name::from_string("And"), vec![]);
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (n_id, n_cap) = bn.fresh_local(c.nat.clone());
    let inner = {
        let mut bi = EnvDeclBuilder::child_of(&bn);
        let (m_id, m) = bi.fresh_local(c.nat.clone());
        let hle = c.nat_le(n_cap.clone(), m.clone());
        let (hle_id, _h) = bi.fresh_local(hle.clone());
        let vl = c.vseq(cl, &m);
        let vr = c.vseq(cr, &m);
        let left = c.lt(vl.clone(), c.radd(vr.clone(), eps.clone()));
        let right = c.lt(vr.clone(), c.radd(vl.clone(), eps.clone()));
        let concl = Expr::apps(and_c.clone(), [left, right]);
        let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
        bi.finish_child(e)
    };
    bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner))
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.mul_one", "NNReal.add_zero"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_semiring_units()
            .expect("init_algebra_nnreal_semiring_units");
        env.init_algebra_nnreal_semiring_units()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_semiring_units_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_nnreal_semiring_units_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
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
