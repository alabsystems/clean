// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the ADDITIVE carrier algebra `NNReal.add_comm` /
//! `NNReal.add_assoc` (the cross-monomial collectors for the cube-of-sum
//! RHS-assembly), plus their nonneg-rational shadows `NNRat.add_comm` /
//! `NNRat.add_assoc`.
//!
//! # Why this module exists
//!
//! The two-point-base RHS cube `(½·(α+β))³` expands through the binomial cube
//! identity `(u+v)³ = u³ + 3u²v + 3uv² + v³` over `NNReal`. Left/right
//! distributivity (`NNReal.mul_add`, `NNReal.add_mul`) multiply the cube out;
//! COLLECTING the three `u²v` and three `uv²` cross-monomials into the `3·`
//! coefficients additionally needs commutativity and associativity of
//! `NNReal.add`. Those are the general, reusable carrier lemmas built here.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNRat.add_comm  : ∀ a b : NNRat, NNRat.add a b = NNRat.add b a`.
//! - `NNRat.add_assoc : ∀ a b c : NNRat,
//!       NNRat.add (NNRat.add a b) c = NNRat.add a (NNRat.add b c)`.
//! - `NNReal.CauSeq.add_comm_equiv  : ∀ f g,
//!       CauSeq.Equiv (CauSeq.add f g)(CauSeq.add g f)`.
//! - `NNReal.CauSeq.add_assoc_equiv : ∀ f g h,
//!       CauSeq.Equiv (CauSeq.add (CauSeq.add f g) h)
//!                    (CauSeq.add f (CauSeq.add g h))`.
//! - `NNReal.add_comm  : ∀ a b : NNReal, NNReal.add a b = NNReal.add b a`.
//! - `NNReal.add_assoc : ∀ a b c : NNReal,
//!       NNReal.add (NNReal.add a b) c = NNReal.add a (NNReal.add b c)`.
//!
//! # Proof shape (axiom-free)
//!
//! `NNRat.add_comm`/`add_assoc`: `NNRat = Subtype`, so two `NNRat` are equal once
//! their `.val`s are equal (`NNRat.eq_of_val_eq`, proof-irrelevance on the
//! membership `Prop`). The `.val`s reduce (via `NNRat.val_add`) to `Rat` sums
//! equal by the on-main `Rat.add_comm`/`Rat.add_assoc`.
//!
//! `NNReal.CauSeq.add_comm_equiv`/`add_assoc_equiv`: the two combined sequences
//! are POINTWISE-EQUAL in `NNRat` (each index is `NNRat.add_comm`/`add_assoc`),
//! so each `Equiv` conjunct `vL < vR + ε`, `vR < vL + ε` follows from `vL = vR`
//! (the val-image of the pointwise `NNRat` equality) and `0 < ε`. Mirrors
//! `NNReal.CauSeq.mul_add_equiv`.
//!
//! `NNReal.add_comm` (double `Quot.ind`) / `NNReal.add_assoc` (triple `Quot.ind`)
//! reduce (via the `NNReal.add` `Quot.lift` computation) the goal to a
//! `Quot.sound` on the corresponding `CauSeq.Equiv`. Mirrors `NNReal.mul_add`.
//!
//! Each declaration is `Declaration::Theorem`, `ProofQuality::Constructive`,
//! with empty admitted-axiom closure (foundational only). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the additive carrier algebra.
pub(crate) struct AddAlgConsts {
    nat: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_lt: Expr,
    rat_add_comm: Expr,
    rat_add_assoc: Expr,
    rat_add_lt_add_left: Expr,
    rat_add_zero: Expr,
    nat_le: Expr,
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_add: Expr,
    nnrat_val_add: Expr,
    nnrat_add_comm: Expr,
    nnrat_add_assoc: Expr,
    nnrat_eq_of_val_eq: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_add: Expr,
    // logic.
    and_c: Expr,
    and_intro: Expr,
    #[cfg(test)]
    exists_c: Expr,
    exists_intro: Expr,
    // Eq.{1} over Rat / NNRat.
    eq1: Expr,
    eq_trans1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    congr_arg: Expr,
    // Quot machinery at level 1.
    quot: Expr,
    quot_mk: Expr,
    quot_sound: Expr,
    quot_ind: Expr,
}

impl AddAlgConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_add: k("Rat.add"),
            rat_lt: k("Rat.lt"),
            rat_add_comm: k("Rat.add_comm"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_add_zero: k("Rat.add_zero"),
            nat_le: k("Nat.le"),
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_add: k("NNRat.add"),
            nnrat_val_add: k("NNRat.val_add"),
            nnrat_add_comm: k("NNRat.add_comm"),
            nnrat_add_assoc: k("NNRat.add_assoc"),
            nnrat_eq_of_val_eq: k("NNRat.eq_of_val_eq"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_add: k("NNReal.CauSeq.add"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            #[cfg(test)]
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            quot: Expr::const_(Name::from_string("Quot"), vec![l1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![l1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![l1]),
        }
    }

    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `NNRat.val q : Rat`.
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    /// `NNRat.add a b : NNRat`.
    fn nnadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_add.clone(), [a, b])
    }
    /// `CauSeq.seq x n : NNRat`.
    fn seq_at(&self, x: &Expr, n: &Expr) -> Expr {
        Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone())
    }
    /// `NNRat.val (CauSeq.seq x n) : Rat`.
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        self.val(self.seq_at(x, n))
    }
    /// `CauSeq.add a b : CauSeq`.
    fn causeq_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_add.clone(), [a, b])
    }
    /// `CauSeq.Equiv a b : Prop`.
    fn equiv(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [a, b])
    }
    /// `@Eq.{1} Rat a b`.
    #[cfg(test)]
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    /// `@Eq.{1} NNRat a b`.
    fn eq_nnrat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nnrat.clone(), a, b])
    }
    /// `NNRat.val_add p q : val (add p q) = (val p)+(val q)`.
    fn val_add(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_add.clone(), [p, q])
    }
    /// `Rat.add_comm a b : a+b = b+a`.
    fn rat_add_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add_comm.clone(), [a, b])
    }
    /// `Rat.add_assoc a b c : (a+b)+c = a+(b+c)`.
    fn rat_add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, cc])
    }
    /// `NNRat.add_comm a b : add a b = add b a`.
    fn nnrat_add_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_add_comm.clone(), [a, b])
    }
    /// `NNRat.add_assoc a b c : add (add a b) c = add a (add b c)`.
    fn nnrat_add_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.nnrat_add_assoc.clone(), [a, b, cc])
    }
    fn eq_symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn eq_trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@congrArg NNRat Rat a a' f h : Eq Rat (f a)(f a')`.
    fn congr_arg_nnrat_rat(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nnrat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    /// `@congrArg Rat Rat a a' f h : Eq Rat (f a)(f a')`.
    fn congr_arg_rat(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    /// `@Quot.mk.{1} CauSeq Equiv l : NNReal`.
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
    /// `@Quot.sound.{1} CauSeq Equiv a b h : Eq NNReal (mk a)(mk b)`.
    fn quot_sound(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), a, b, h],
        )
    }
    fn nnreal(&self) -> Expr {
        Expr::apps(
            self.quot.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
}

impl Environment {
    /// Register `NNRat.add_comm`, `NNRat.add_assoc`,
    /// `NNReal.CauSeq.add_comm_equiv`, `NNReal.CauSeq.add_assoc_equiv`,
    /// `NNReal.add_comm`, `NNReal.add_assoc`. Idempotent.
    pub fn init_algebra_nnreal_add_comm_assoc(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_add()?; // NNReal.add, CauSeq.add, NNRat.val_add
        self.init_algebra_nnreal_mul_distrib()?; // NNRat.eq_of_val_eq
        self.init_rat_field_inst()?; // Rat.add_comm, Rat.add_assoc, Rat.add_zero
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.init_eq()?;
        self.init_and()?;
        self.init_exists()?;

        let c = AddAlgConsts::new();
        self.register_nnrat_add_comm(&c)?;
        self.register_nnrat_add_assoc(&c)?;
        self.register_nnreal_causeq_add_comm_equiv(&c)?;
        self.register_nnreal_causeq_add_assoc_equiv(&c)?;
        self.register_nnreal_add_comm(&c)?;
        self.register_nnreal_add_assoc(&c)?;
        Ok(())
    }

    /// `NNRat.add_comm : ∀ a b : NNRat, NNRat.add a b = NNRat.add b a`.
    /// Via `NNRat.eq_of_val_eq` on `val(add a b) = val(add b a)`.
    fn register_nnrat_add_comm(&mut self, c: &AddAlgConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNRat.add_comm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnrat.clone());
            let (bv_id, bv) = b.fresh_local(c.nnrat.clone());
            let concl = c.eq_nnrat(
                c.nnadd(a.clone(), bv.clone()),
                c.nnadd(bv.clone(), a.clone()),
            );
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nnrat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        let value = build_nnrat_add_comm(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNRat.add_assoc : ∀ a b c : NNRat,
    ///     NNRat.add (NNRat.add a b) c = NNRat.add a (NNRat.add b c)`.
    /// Via `NNRat.eq_of_val_eq` on the val-equality.
    fn register_nnrat_add_assoc(&mut self, c: &AddAlgConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNRat.add_assoc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnrat.clone());
            let (bv_id, bv) = b.fresh_local(c.nnrat.clone());
            let (cv_id, cv) = b.fresh_local(c.nnrat.clone());
            let lhs = c.nnadd(c.nnadd(a.clone(), bv.clone()), cv.clone());
            let rhs = c.nnadd(a.clone(), c.nnadd(bv.clone(), cv.clone()));
            let concl = c.eq_nnrat(lhs, rhs);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.nnrat.clone(), concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nnrat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        let value = build_nnrat_add_assoc(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.CauSeq.add_comm_equiv : ∀ f g,
    ///     CauSeq.Equiv (CauSeq.add f g)(CauSeq.add g f)`.
    fn register_nnreal_causeq_add_comm_equiv(&mut self, c: &AddAlgConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.add_comm_equiv");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let (g_id, g) = b.fresh_local(c.causeq.clone());
            let lhs = c.causeq_add(f.clone(), g.clone());
            let rhs = c.causeq_add(g.clone(), f.clone());
            let concl = c.equiv(lhs, rhs);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.causeq.clone(), concl);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        let value = build_add_comm_equiv(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.CauSeq.add_assoc_equiv : ∀ f g h,
    ///     CauSeq.Equiv (CauSeq.add (CauSeq.add f g) h)
    ///                  (CauSeq.add f (CauSeq.add g h))`.
    fn register_nnreal_causeq_add_assoc_equiv(&mut self, c: &AddAlgConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.add_assoc_equiv");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let (g_id, g) = b.fresh_local(c.causeq.clone());
            let (h_id, h) = b.fresh_local(c.causeq.clone());
            let lhs = c.causeq_add(c.causeq_add(f.clone(), g.clone()), h.clone());
            let rhs = c.causeq_add(f.clone(), c.causeq_add(g.clone(), h.clone()));
            let concl = c.equiv(lhs, rhs);
            let e = b.mk_pi(h_id, BinderInfo::Default, c.causeq.clone(), concl);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        let value = build_add_assoc_equiv(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.add_comm : ∀ a b : NNReal, NNReal.add a b = NNReal.add b a`.
    /// Double `Quot.ind` + `Quot.sound` on `NNReal.CauSeq.add_comm_equiv`.
    fn register_nnreal_add_comm(&mut self, c: &AddAlgConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add_comm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
        let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);
        let eq_nn = |x: Expr, y: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [nnreal.clone(), x, y],
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let concl = eq_nn(add(a.clone(), bv.clone()), add(bv.clone(), a.clone()));
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_add_comm(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.add_assoc : ∀ a b c : NNReal,
    ///     NNReal.add (NNReal.add a b) c = NNReal.add a (NNReal.add b c)`.
    /// Triple `Quot.ind` + `Quot.sound` on `NNReal.CauSeq.add_assoc_equiv`.
    fn register_nnreal_add_assoc(&mut self, c: &AddAlgConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add_assoc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
        let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);
        let eq_nn = |x: Expr, y: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [nnreal.clone(), x, y],
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let (cv_id, cv) = b.fresh_local(nnreal.clone());
            let lhs = add(add(a.clone(), bv.clone()), cv.clone());
            let rhs = add(a.clone(), add(bv.clone(), cv.clone()));
            let concl = eq_nn(lhs, rhs);
            let e = b.mk_pi(cv_id, BinderInfo::Default, nnreal.clone(), concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_add_assoc(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

// ─────────────────────────── NNRat-level shadows ───────────────────────────

/// `NNRat.add_comm` value: `NNRat.eq_of_val_eq` on `val(add a b)=val(add b a)`.
/// `val(add a b) = va+vb` (val_add), `val(add b a) = vb+va` (val_add); the
/// middle `va+vb = vb+va` is `Rat.add_comm va vb`.
fn build_nnrat_add_comm(c: &AddAlgConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nnrat.clone());
    let (bv_id, bv) = b.fresh_local(c.nnrat.clone());

    let lhs = c.nnadd(a.clone(), bv.clone());
    let rhs = c.nnadd(bv.clone(), a.clone());
    let va = c.val(a.clone());
    let vb = c.val(bv.clone());

    // val(lhs) = va+vb  (val_add a b).
    let vlhs = c.val(lhs.clone());
    let va_vb = c.radd(va.clone(), vb.clone());
    let l = c.val_add(a.clone(), bv.clone());
    // middle : va+vb = vb+va  (Rat.add_comm va vb).
    let vb_va = c.radd(vb.clone(), va.clone());
    let mid = c.rat_add_comm(va.clone(), vb.clone());
    // val(rhs) = vb+va  (val_add b a) ; symm to (vb+va) = val(rhs).
    let vrhs = c.val(rhs.clone());
    let r = c.val_add(bv.clone(), a.clone());
    let r_symm = c.eq_symm_rat(vrhs.clone(), vb_va.clone(), r);

    // chain: val(lhs) = va+vb = vb+va = val(rhs).
    let lm = c.eq_trans_rat(vlhs.clone(), va_vb.clone(), vb_va.clone(), l, mid);
    let hval = c.eq_trans_rat(vlhs, vb_va, vrhs, lm, r_symm);

    let body = Expr::apps(
        c.nnrat_eq_of_val_eq.clone(),
        [lhs.clone(), rhs.clone(), hval],
    );
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.nnrat.clone(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nnrat.clone(), e);
    b.finish(e)
}

/// `NNRat.add_assoc` value: `NNRat.eq_of_val_eq` on
/// `val(add (add a b) c) = val(add a (add b c))`.
/// LHS ≡ (va+vb)+vc after val_add + congrArg(val_add) ; RHS ≡ va+(vb+vc) after
/// val_add + congrArg(val_add) ; middle is `Rat.add_assoc va vb vc`.
fn build_nnrat_add_assoc(c: &AddAlgConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nnrat.clone());
    let (bv_id, bv) = b.fresh_local(c.nnrat.clone());
    let (cv_id, cv) = b.fresh_local(c.nnrat.clone());

    let va = c.val(a.clone());
    let vb = c.val(bv.clone());
    let vc = c.val(cv.clone());

    let add_ab = c.nnadd(a.clone(), bv.clone());
    let add_bc = c.nnadd(bv.clone(), cv.clone());
    let lhs = c.nnadd(add_ab.clone(), cv.clone()); // add (add a b) c
    let rhs = c.nnadd(a.clone(), add_bc.clone()); // add a (add b c)

    // ── LHS = (va+vb)+vc ──
    // val(add (add a b) c) = val(add a b) + vc   (val_add (add a b) c).
    let vlhs = c.val(lhs.clone());
    let v_add_ab = c.val(add_ab.clone());
    let l_step1 = c.val_add(add_ab.clone(), cv.clone()); // vlhs = v_add_ab + vc
    let vab_vc = c.radd(v_add_ab.clone(), vc.clone()); // v_add_ab + vc
                                                       // congrArg (fun t => t + vc) (val_add a b : v_add_ab = va+vb).
    let va_vb = c.radd(va.clone(), vb.clone());
    let add_vc_fn = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.rat.clone());
        let body = c.radd(t, vc.clone());
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let vab_eq = c.val_add(a.clone(), bv.clone()); // v_add_ab = va+vb
    let l_step2 = c.congr_arg_rat(v_add_ab.clone(), va_vb.clone(), add_vc_fn, vab_eq); // v_add_ab+vc = (va+vb)+vc
    let vavb_vc = c.radd(va_vb.clone(), vc.clone()); // (va+vb)+vc
    let l = c.eq_trans_rat(
        vlhs.clone(),
        vab_vc.clone(),
        vavb_vc.clone(),
        l_step1,
        l_step2,
    );

    // ── middle : (va+vb)+vc = va+(vb+vc)  (Rat.add_assoc va vb vc) ──
    let mid = c.rat_add_assoc(va.clone(), vb.clone(), vc.clone());
    let vb_vc = c.radd(vb.clone(), vc.clone());
    let va_vbvc = c.radd(va.clone(), vb_vc.clone()); // va+(vb+vc)

    // ── RHS = va+(vb+vc) ──
    // val(add a (add b c)) = va + val(add b c)   (val_add a (add b c)).
    let vrhs = c.val(rhs.clone());
    let v_add_bc = c.val(add_bc.clone());
    let r_step1 = c.val_add(a.clone(), add_bc.clone()); // vrhs = va + v_add_bc
    let va_vbc = c.radd(va.clone(), v_add_bc.clone()); // va + v_add_bc
                                                       // congrArg (fun t => va + t) (val_add b c : v_add_bc = vb+vc).
    let add_va_fn = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = fb.fresh_local(c.rat.clone());
        let body = c.radd(va.clone(), t);
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let vbc_eq = c.val_add(bv.clone(), cv.clone()); // v_add_bc = vb+vc
    let r_step2 = c.congr_arg_rat(v_add_bc.clone(), vb_vc.clone(), add_va_fn, vbc_eq); // va+v_add_bc = va+(vb+vc)
    let r = c.eq_trans_rat(
        vrhs.clone(),
        va_vbc.clone(),
        va_vbvc.clone(),
        r_step1,
        r_step2,
    );

    // combine: val(lhs) = (va+vb)+vc = va+(vb+vc) = val(rhs).
    let lm = c.eq_trans_rat(vlhs.clone(), vavb_vc.clone(), va_vbvc.clone(), l, mid);
    let r_symm = c.eq_symm_rat(vrhs.clone(), va_vbvc.clone(), r);
    let hval = c.eq_trans_rat(vlhs, va_vbvc, vrhs, lm, r_symm);

    let body = Expr::apps(
        c.nnrat_eq_of_val_eq.clone(),
        [lhs.clone(), rhs.clone(), hval],
    );
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.nnrat.clone(), body);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.nnrat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nnrat.clone(), e);
    b.finish(e)
}

// ─────────────────────────── CauSeq.Equiv lemmas ───────────────────────────

/// Build `CauSeq.add_comm_equiv` value: the two sequences `add f g`/`add g f`
/// are pointwise-equal (`NNRat.add_comm (f n)(g n)` lifted through `val`).
fn build_add_comm_equiv(c: &AddAlgConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.causeq.clone());
    let (g_id, g) = b.fresh_local(c.causeq.clone());

    let cl = c.causeq_add(f.clone(), g.clone());
    let cr = c.causeq_add(g.clone(), f.clone());

    let pointwise = move |bw: &EnvDeclBuilder, m: &Expr| -> Expr {
        let _ = bw;
        // NNRat.add_comm (f m)(g m) : add (f m)(g m) = add (g m)(f m).
        let fm = c.seq_at(&f, m);
        let gm = c.seq_at(&g, m);
        let comm = c.nnrat_add_comm(fm.clone(), gm.clone());
        let lhs_nn = c.nnadd(fm.clone(), gm.clone());
        let rhs_nn = c.nnadd(gm.clone(), fm.clone());
        // congrArg NNRat.val comm : val(lhs_nn) = val(rhs_nn) ≡ vseq cl m = vseq cr m.
        c.congr_arg_nnrat_rat(lhs_nn, rhs_nn, c.nnrat_val.clone(), comm)
    };

    let body = build_pointwise_equiv(c, &b, &cl, &cr, &pointwise);
    let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), body);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// Build `CauSeq.add_assoc_equiv` value: the two sequences
/// `add (add f g) h`/`add f (add g h)` are pointwise-equal
/// (`NNRat.add_assoc (f n)(g n)(h n)` lifted through `val`).
fn build_add_assoc_equiv(c: &AddAlgConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.causeq.clone());
    let (g_id, g) = b.fresh_local(c.causeq.clone());
    let (h_id, h) = b.fresh_local(c.causeq.clone());

    let cl = c.causeq_add(c.causeq_add(f.clone(), g.clone()), h.clone());
    let cr = c.causeq_add(f.clone(), c.causeq_add(g.clone(), h.clone()));

    let pointwise = move |bw: &EnvDeclBuilder, m: &Expr| -> Expr {
        let _ = bw;
        // NNRat.add_assoc (f m)(g m)(h m) : add (add (f m)(g m))(h m)
        //                                  = add (f m)(add (g m)(h m)).
        let fm = c.seq_at(&f, m);
        let gm = c.seq_at(&g, m);
        let hm = c.seq_at(&h, m);
        let assoc = c.nnrat_add_assoc(fm.clone(), gm.clone(), hm.clone());
        let lhs_nn = c.nnadd(c.nnadd(fm.clone(), gm.clone()), hm.clone());
        let rhs_nn = c.nnadd(fm.clone(), c.nnadd(gm.clone(), hm.clone()));
        c.congr_arg_nnrat_rat(lhs_nn, rhs_nn, c.nnrat_val.clone(), assoc)
    };

    let body = build_pointwise_equiv(c, &b, &cl, &cr, &pointwise);
    let e = b.mk_lam(h_id, BinderInfo::Default, c.causeq.clone(), body);
    let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// Build the body `∀ ε, 0<ε → ∃ N, ∀ n, N≤n → And(vL<vR+ε)(vR<vL+ε)` for two
/// POINTWISE-EQUAL combined sequences `cl`, `cr`, where `pointwise bw m` proves
/// `vseq cl m = vseq cr m`. Mirrors `mul_distrib`'s `build_mul_add_equiv` body.
fn build_pointwise_equiv(
    c: &AddAlgConsts,
    parent: &EnvDeclBuilder,
    cl: &Expr,
    cr: &Expr,
    pointwise: &dyn Fn(&EnvDeclBuilder, &Expr) -> Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let pred = build_equiv_pred(c, &b, cl, cr, &eps);
    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(c.nat_zero.clone(), m.clone());
        let (hle_id, _hle) = bw.fresh_local(hle_ty.clone());

        let vl = c.vseq(cl, &m);
        let vr = c.vseq(cr, &m);
        // h_eq : vL = vR.
        let h_eq = pointwise(&bw, &m);

        // vL < vR + ε:  from vR < vR+ε (self_lt_add) and subst vR → vL via symm h_eq.
        let vr_eps = c.radd(vr.clone(), eps.clone());
        let vr_lt = build_self_lt_add(c, &bw, &vr, &eps, &hpos);
        let motive_l = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.rlt(t, vr_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let left = c.subst_rat(
            motive_l,
            vr.clone(),
            vl.clone(),
            c.eq_symm_rat(vl.clone(), vr.clone(), h_eq.clone()),
            vr_lt,
        );

        // vR < vL + ε:  from vL < vL+ε and subst LHS vL → vR via h_eq.
        let vl_eps = c.radd(vl.clone(), eps.clone());
        let vl_lt = build_self_lt_add(c, &bw, &vl, &eps, &hpos);
        let motive_r = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.rlt(t, vl_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let right = c.subst_rat(motive_r, vl.clone(), vr.clone(), h_eq, vl_lt);

        let l_ty = c.rlt(vl.clone(), vr_eps);
        let r_ty = c.rlt(vr.clone(), vl_eps);
        let proof = Expr::apps(c.and_intro.clone(), [l_ty, r_ty, left, right]);

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

/// `v < v + ε` from `0<ε`: add_lt_add_left 0 ε v hpos : (v+0)<(v+ε), subst v+0→v.
fn build_self_lt_add(
    c: &AddAlgConsts,
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
    let add_zero = Expr::app(c.rat_add_zero.clone(), v.clone()); // v+0 = v
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(t, v_eps.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst_rat(motive, v_zero, v.clone(), add_zero, h)
}

/// `fun N => ∀ n, N≤n → And (vseq cl n < vseq cr n + ε)(vseq cr n < vseq cl n + ε)`.
fn build_equiv_pred(
    c: &AddAlgConsts,
    parent: &EnvDeclBuilder,
    cl: &Expr,
    cr: &Expr,
    eps: &Expr,
) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (n_id, n_cap) = bn.fresh_local(c.nat.clone());
    let inner = {
        let mut bi = EnvDeclBuilder::child_of(&bn);
        let (m_id, m) = bi.fresh_local(c.nat.clone());
        let hle = c.nat_le(n_cap.clone(), m.clone());
        let (hle_id, _h) = bi.fresh_local(hle.clone());
        let vl = c.vseq(cl, &m);
        let vr = c.vseq(cr, &m);
        let left = c.rlt(vl.clone(), c.radd(vr.clone(), eps.clone()));
        let right = c.rlt(vr.clone(), c.radd(vl.clone(), eps.clone()));
        let concl = Expr::apps(c.and_c.clone(), [left, right]);
        let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
        bi.finish_child(e)
    };
    bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner))
}

// ─────────────────────── NNReal-level Quot.ind lifts ───────────────────────

/// `NNReal.add_comm` value: double `Quot.ind` + `Quot.sound` on the Equiv.
fn build_nnreal_add_comm(c: &AddAlgConsts, nnreal: &Expr) -> Expr {
    let equiv_lemma = Expr::const_(Name::from_string("NNReal.CauSeq.add_comm_equiv"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);
    let eq_nn = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nnreal.clone(), x, y],
        )
    };

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());

    // descend on `a` with motive P x := add x bv = add bv x.
    let motive_a = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let body = eq_nn(add(x.clone(), bv.clone()), add(bv.clone(), x.clone()));
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), body))
    };
    let minor_a = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (f_id, f) = mf.fresh_local(c.causeq.clone());
        let mkf = c.quot_mk(f.clone());
        // descend on `bv` with motive Q y := add (mk f) y = add y (mk f).
        let motive_b = {
            let mut mb = EnvDeclBuilder::child_of(&mf);
            let (y_id, y) = mb.fresh_local(nnreal.clone());
            let body = eq_nn(add(mkf.clone(), y.clone()), add(y.clone(), mkf.clone()));
            mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), body))
        };
        let minor_b = {
            let mut mg = EnvDeclBuilder::child_of(&mf);
            let (g_id, g) = mg.fresh_local(c.causeq.clone());
            // leaf goal: add (mk f)(mk g) = add (mk g)(mk f)
            //   ι-reduces to mk (CauSeq.add f g) = mk (CauSeq.add g f).
            let cl = c.causeq_add(f.clone(), g.clone());
            let cr = c.causeq_add(g.clone(), f.clone());
            let equiv = Expr::apps(equiv_lemma.clone(), [f.clone(), g.clone()]);
            let sound = c.quot_sound(cl, cr, equiv);
            mg.finish_child(mg.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), sound))
        };
        let ind_b = Expr::apps(
            c.quot_ind.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive_b,
                minor_b,
                bv.clone(),
            ],
        );
        mf.finish_child(mf.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), ind_b))
    };
    let ind_a = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_a,
            minor_a,
            a.clone(),
        ],
    );
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), ind_a);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// `NNReal.add_assoc` value: triple `Quot.ind` + `Quot.sound` on the Equiv.
fn build_nnreal_add_assoc(c: &AddAlgConsts, nnreal: &Expr) -> Expr {
    let equiv_lemma = Expr::const_(Name::from_string("NNReal.CauSeq.add_assoc_equiv"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);
    let eq_nn = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nnreal.clone(), x, y],
        )
    };
    let assoc_eq = move |x: &Expr, y: &Expr, z: &Expr| -> Expr {
        eq_nn(
            add(add(x.clone(), y.clone()), z.clone()),
            add(x.clone(), add(y.clone(), z.clone())),
        )
    };

    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());
    let (cv_id, cv) = b.fresh_local(nnreal.clone());

    // descend on a.
    let motive_a = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let body = assoc_eq(&x, &bv, &cv);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), body))
    };
    let minor_a = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (f_id, f) = mf.fresh_local(c.causeq.clone());
        let mkf = c.quot_mk(f.clone());
        // descend on b.
        let motive_b = {
            let mut mb = EnvDeclBuilder::child_of(&mf);
            let (y_id, y) = mb.fresh_local(nnreal.clone());
            let body = assoc_eq(&mkf, &y, &cv);
            mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), body))
        };
        let minor_b = {
            let mut mg = EnvDeclBuilder::child_of(&mf);
            let (g_id, g) = mg.fresh_local(c.causeq.clone());
            let mkg = c.quot_mk(g.clone());
            // descend on c.
            let motive_c = {
                let mut mb = EnvDeclBuilder::child_of(&mg);
                let (z_id, z) = mb.fresh_local(nnreal.clone());
                let body = assoc_eq(&mkf, &mkg, &z);
                mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, nnreal.clone(), body))
            };
            let minor_c = {
                let mut mh = EnvDeclBuilder::child_of(&mg);
                let (h_id, h) = mh.fresh_local(c.causeq.clone());
                // leaf goal: add (add (mk f)(mk g))(mk h) = add (mk f)(add (mk g)(mk h))
                //   ι-reduces to mk (CauSeq.add (CauSeq.add f g) h)
                //              = mk (CauSeq.add f (CauSeq.add g h)).
                let cl = c.causeq_add(c.causeq_add(f.clone(), g.clone()), h.clone());
                let cr = c.causeq_add(f.clone(), c.causeq_add(g.clone(), h.clone()));
                let equiv = Expr::apps(equiv_lemma.clone(), [f.clone(), g.clone(), h.clone()]);
                let sound = c.quot_sound(cl, cr, equiv);
                mh.finish_child(mh.mk_lam(h_id, BinderInfo::Default, c.causeq.clone(), sound))
            };
            let ind_c = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.causeq.clone(),
                    c.causeq_equiv.clone(),
                    motive_c,
                    minor_c,
                    cv.clone(),
                ],
            );
            mg.finish_child(mg.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), ind_c))
        };
        let ind_b = Expr::apps(
            c.quot_ind.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive_b,
                minor_b,
                bv.clone(),
            ],
        );
        mf.finish_child(mf.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), ind_b))
    };
    let ind_a = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_a,
            minor_a,
            a.clone(),
        ],
    );
    let e = b.mk_lam(cv_id, BinderInfo::Default, nnreal.clone(), ind_a);
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "NNRat.add_comm",
        "NNRat.add_assoc",
        "NNReal.CauSeq.add_comm_equiv",
        "NNReal.CauSeq.add_assoc_equiv",
        "NNReal.add_comm",
        "NNReal.add_assoc",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_add_comm_assoc()
            .expect("init_algebra_nnreal_add_comm_assoc");
        env.init_algebra_nnreal_add_comm_assoc()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_add_comm_assoc_kernel_check() {
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
    fn test_nnreal_add_comm_assoc_constructive_empty_closure() {
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
