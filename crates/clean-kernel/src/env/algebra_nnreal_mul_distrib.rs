// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component B, target 4a: LEFT-DISTRIBUTIVITY of
//! `NNReal.mul` over `NNReal.add` (`NNReal.mul_add`) + the nonneg-rational
//! base lemma `NNRat.left_distrib`.
//!
//! # Why this module exists
//!
//! The scalar-pull `NNReal.finSum_smul`
//! (`finSum n (fun i => mul c (f i)) = mul c (finSum n f)`) closes its `Nat.rec`
//! step case with the left-distributivity of `NNReal.mul` over `NNReal.add`:
//!
//! - `NNReal.mul_add : ∀ c a b, NNReal.mul c (NNReal.add a b) =
//!       NNReal.add (NNReal.mul c a) (NNReal.mul c b)`.
//!
//! Its nonneg-rational shadow is:
//!
//! - `NNRat.left_distrib : ∀ c a b, NNRat.mul c (NNRat.add a b) =
//!       NNRat.add (NNRat.mul c a) (NNRat.mul c b)`.
//!
//! # Proof shape (axiom-free)
//!
//! `NNRat.left_distrib`: `NNRat = Subtype`, so two `NNRat` are equal once their
//! `.val`s are equal (`NNRat.eq_of_val_eq`, proof-irrelevance on the membership
//! `Prop`). The `.val`s of both sides reduce (via `NNRat.val_mul`/`val_add`) to
//! `vc·(va+vb)` and `vc·va + vc·vb`, equal by the on-main `Rat.left_distrib`.
//!
//! `NNReal.mul_add`: triple `Quot.ind` on `c,a,b` reduces the goal (via the
//! `NNReal.mul`/`NNReal.add` `Quot.lift` computation) to a `Quot.sound` on the
//! `CauSeq.Equiv` between `CauSeq.mul fc (CauSeq.add fa fb)` and
//! `CauSeq.add (CauSeq.mul fc fa)(CauSeq.mul fc fb)`. Those two sequences are
//! POINTWISE-EQUAL in `NNRat` (each index is `NNRat.left_distrib (fc n)(fa n)
//! (fb n)`), so the `Equiv` conjuncts `vL < vR + ε`, `vR < vL + ε` follow from
//! `vL = vR` (the val-image of the pointwise `NNRat` equality) and `0 < ε`.
//!
//! `NNRat.eq_of_val_eq`, `NNRat.left_distrib`, `NNReal.CauSeq.mul_add_equiv`,
//! `NNReal.mul_add` are each `Declaration::Theorem`, `ProofQuality::Constructive`,
//! with empty admitted-axiom closure (foundational only). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::ExprKind;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the distributivity lemmas.
pub(crate) struct DistribConsts {
    nat: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_le: Expr,
    rat_add: Expr,
    rat_left_distrib: Expr,
    rat_add_lt_add_left: Expr,
    rat_add_zero: Expr,
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_mul: Expr,
    nnrat_add: Expr,
    nnrat_val_mul: Expr,
    nnrat_val_add: Expr,
    nnrat_left_distrib: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_mul: Expr,
    causeq_add: Expr,
    rat_lt: Expr,
    nat_le: Expr,
    // logic.
    #[cfg(test)]
    exists_c: Expr,
    exists_intro: Expr,
    and_c: Expr,
    and_intro: Expr,
    // Eq.{1} over Rat / NNRat.
    eq1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    congr_arg: Expr,
    // Subtype machinery (for eq_of_val_eq).
    #[cfg(test)]
    subtype_val: Expr,
    // Quot machinery at level 1.
    quot_mk: Expr,
    quot_sound: Expr,
    quot_ind: Expr,
}

impl DistribConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_le: k("Rat.le"),
            rat_add: k("Rat.add"),
            rat_left_distrib: k("Rat.left_distrib"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_add_zero: k("Rat.add_zero"),
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_mul: k("NNRat.mul"),
            nnrat_add: k("NNRat.add"),
            nnrat_val_mul: k("NNRat.val_mul"),
            nnrat_val_add: k("NNRat.val_add"),
            nnrat_left_distrib: k("NNRat.left_distrib"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            causeq_add: k("NNReal.CauSeq.add"),
            rat_lt: k("Rat.lt"),
            nat_le: k("Nat.le"),
            #[cfg(test)]
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            and_c: k("And"),
            and_intro: k("And.intro"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(
                Name::from_string("congrArg"),
                vec![lvl1.clone(), lvl1.clone()],
            ),
            #[cfg(test)]
            subtype_val: Expr::const_(Name::from_string("Subtype.val"), vec![lvl1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![lvl1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![lvl1]),
        }
    }

    #[cfg(test)]
    fn prop(&self) -> Expr {
        Expr::from_kind(ExprKind::Sort(Level::zero()))
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
    fn nnmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_mul.clone(), [a, b])
    }
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
    fn causeq_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_mul.clone(), [a, b])
    }
    fn causeq_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_add.clone(), [a, b])
    }
    /// `NNReal.CauSeq.Equiv a b : Prop`.
    fn equiv(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [a, b])
    }
    /// `@Eq.{1} Rat a b`.
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    /// `@Eq.{1} NNRat a b`.
    fn eq_nnrat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nnrat.clone(), a, b])
    }
    /// `Rat.left_distrib a b c : a·(b+c) = a·b + a·c`.
    fn rat_left_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_left_distrib.clone(), [a, b, cc])
    }
    /// `NNRat.val_mul p q : val (mul p q) = (val p)·(val q)`.
    fn val_mul(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_mul.clone(), [p, q])
    }
    /// `NNRat.val_add p q : val (add p q) = (val p)+(val q)`.
    fn val_add(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_add.clone(), [p, q])
    }
    /// `NNRat.left_distrib c a b : mul c (add a b) = add (mul c a)(mul c b)`.
    fn nnrat_left_distrib(&self, c: Expr, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnrat_left_distrib.clone(), [c, a, b])
    }
    fn eq_symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
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
            Expr::const_(Name::from_string("Quot"), vec![Level::succ(Level::zero())]),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
}

impl Environment {
    /// Register `NNRat.eq_of_val_eq`, `NNRat.left_distrib`,
    /// `NNReal.CauSeq.mul_add_equiv`, and `NNReal.mul_add`. Idempotent.
    pub fn init_algebra_nnreal_mul_distrib(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul, CauSeq.mul (+ NNRat)
        self.init_algebra_nnreal_add()?; // NNReal.add, CauSeq.add
        self.init_rat()?; // Rat.left_distrib (constructive Rat-quotient theorem)
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.init_rat_field_inst()?; // Rat.add_zero
        self.init_exists()?;

        let c = DistribConsts::new();
        self.register_nnrat_eq_of_val_eq(&c)?;
        self.register_nnrat_left_distrib(&c)?;
        self.register_nnreal_causeq_mul_add_equiv(&c)?;
        self.register_nnreal_mul_add(&c)?;
        Ok(())
    }

    /// `NNRat.eq_of_val_eq : ∀ (p q : NNRat), NNRat.val p = NNRat.val q → p = q`.
    ///
    /// `NNRat = Subtype`; the membership predicate is a `Prop`, so by proof
    /// irrelevance two `NNRat` with equal `.val` are equal. Proof: transport `q`
    /// along `Eq.symm hval` with motive `fun (t : Rat) => p = ?`... we instead
    /// substitute into `Eq` directly: `Eq.subst (motive r := p = r)`-style is not
    /// available without exposing the witness, so we use the val-projection
    /// route: `congrArg`-free transport via the dependent recursor is avoided by
    /// using `Eq.subst` on the GOAL `p = q`, rewriting `q`'s val. The clean
    /// route the kernel accepts (proof irrelevance ON): `p = q` holds because
    /// `NNRat.val p ≡ NNRat.val q` after substitution and the proofs are defeq.
    fn register_nnrat_eq_of_val_eq(&mut self, c: &DistribConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNRat.eq_of_val_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // We prove it by `Subtype.rec` on `p`, exposing `Subtype.mk pv pp`, then
        // transporting `q` along the val-equality. The simplest kernel-checkable
        // form uses `Eq.subst` over `Subtype` with the val-injection. Concretely:
        //   eq_of_val_eq p q h := @Eq.subst NNRat (fun (r:NNRat) => p = r) ??? ...
        // is circular. Instead use the canonical proof via `Subtype.val`
        // injectivity expressed through the recursor. Build it as:
        //   fun p q h => @Subtype.rec ... on q, mapping to p = (mk qv qp).
        // We rely on: after `Subtype.rec` on BOTH, the goal `mk pv pp = mk qv qp`
        // with `h : pv = qv` reduces — `mk pv pp = mk qv qp` is obtained by
        // `congrArg (fun t => mk t _) h` IF the membership proof is irrelevant.
        //
        // The robust, recursor-free construction: rewrite the GOAL `p = q` is not
        // possible without a value. So we use `Subtype.val`-based: the kernel
        // (proof irrelevance ON) accepts that `Subtype.mk (val q) (property q)`
        // is defeq to `q` (eta for structures). Hence:
        //   p = q  ⟸  val p = val q   via   @Eq.subst Rat
        //     (motive t := p = Subtype.mk t (transport of property q))
        // To avoid the dependent membership, we transport `property p` instead:
        //   Build `mk_p := Subtype.mk (val p)(property p)` ≡ p (eta).
        //   Build `mk_q := Subtype.mk (val q)(property q)` ≡ q (eta).
        //   subst along h : val p = val q sends mk_p's val to val q; the proof
        //   slot is filled by proof irrelevance.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnrat.clone());
            let (q_id, q) = b.fresh_local(c.nnrat.clone());
            let hval = c.eq_rat(c.val(p.clone()), c.val(q.clone()));
            let (h_id, _h) = b.fresh_local(hval.clone());
            let concl = c.eq_nnrat(p.clone(), q.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hval, concl);
            let e = b.mk_pi(q_id, BinderInfo::Default, c.nnrat.clone(), e);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        let value = build_eq_of_val_eq(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNRat.left_distrib : ∀ c a b, NNRat.mul c (NNRat.add a b) =
    ///     NNRat.add (NNRat.mul c a)(NNRat.mul c b)`.
    /// Via `NNRat.eq_of_val_eq` on the val-equality
    /// `vc·(va+vb) = vc·va + vc·vb` (= `Rat.left_distrib` after val transports).
    fn register_nnrat_left_distrib(&mut self, c: &DistribConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNRat.left_distrib");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cv_id, cv) = b.fresh_local(c.nnrat.clone());
            let (a_id, a) = b.fresh_local(c.nnrat.clone());
            let (bv_id, bv) = b.fresh_local(c.nnrat.clone());
            let lhs = c.nnmul(cv.clone(), c.nnadd(a.clone(), bv.clone()));
            let rhs = c.nnadd(
                c.nnmul(cv.clone(), a.clone()),
                c.nnmul(cv.clone(), bv.clone()),
            );
            let concl = c.eq_nnrat(lhs, rhs);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nnrat.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nnrat.clone(), e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.nnrat.clone(), e);
            b.finish(e)
        };
        let value = build_nnrat_left_distrib(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.CauSeq.mul_add_equiv : ∀ fc fa fb,
    ///     CauSeq.Equiv (CauSeq.mul fc (CauSeq.add fa fb))
    ///                  (CauSeq.add (CauSeq.mul fc fa)(CauSeq.mul fc fb))`.
    /// The two sequences are POINTWISE-EQUAL (each index `NNRat.left_distrib`),
    /// so each `Equiv` conjunct `vL < vR + ε` follows from `vL = vR` and `0<ε`.
    fn register_nnreal_causeq_mul_add_equiv(&mut self, c: &DistribConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.mul_add_equiv");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (fc_id, fc) = b.fresh_local(c.causeq.clone());
            let (fa_id, fa) = b.fresh_local(c.causeq.clone());
            let (fb_id, fb) = b.fresh_local(c.causeq.clone());
            let lhs = c.causeq_mul(fc.clone(), c.causeq_add(fa.clone(), fb.clone()));
            let rhs = c.causeq_add(
                c.causeq_mul(fc.clone(), fa.clone()),
                c.causeq_mul(fc.clone(), fb.clone()),
            );
            let concl = c.equiv(lhs, rhs);
            let e = b.mk_pi(fb_id, BinderInfo::Default, c.causeq.clone(), concl);
            let e = b.mk_pi(fa_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(fc_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        let value = build_mul_add_equiv(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.mul_add : ∀ c a b, NNReal.mul c (NNReal.add a b) =
    ///     NNReal.add (NNReal.mul c a)(NNReal.mul c b)`. Triple `Quot.ind` +
    /// `Quot.sound` on `NNReal.CauSeq.mul_add_equiv`.
    fn register_nnreal_mul_add(&mut self, c: &DistribConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.mul_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
        let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
        let eq_nnreal = |a: Expr, bb: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [nnreal.clone(), a, bb],
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cv_id, cv) = b.fresh_local(nnreal.clone());
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let lhs = Expr::apps(
                nnmul.clone(),
                [
                    cv.clone(),
                    Expr::apps(nnadd.clone(), [a.clone(), bv.clone()]),
                ],
            );
            let rhs = Expr::apps(
                nnadd.clone(),
                [
                    Expr::apps(nnmul.clone(), [cv.clone(), a.clone()]),
                    Expr::apps(nnmul.clone(), [cv.clone(), bv.clone()]),
                ],
            );
            let concl = eq_nnreal(lhs, rhs);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_nnreal_mul_add(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `NNRat.eq_of_val_eq` value. The canonical `Subtype.eq` proof:
/// `Subtype.rec` on `p` and `q` to expose `Subtype.mk pv pp`/`Subtype.mk qv qq`,
/// then `Eq.rec` on the val-equality `pv = qv` transporting `Eq.refl (mk pv pp)`;
/// the membership-proof slot is filled by proof irrelevance.
fn build_eq_of_val_eq(c: &DistribConsts) -> Expr {
    build_subtype_eq(c)
}

/// Build `Subtype.eq`-style proof via `Subtype.rec` (×2) + `Eq.rec`.
fn build_subtype_eq(c: &DistribConsts) -> Expr {
    let lvl1 = Level::succ(Level::zero());
    let nn_pred = nn_pred(c);
    // Subtype.rec.{motive_univ, α_univ}; motive returns Prop (Sort 0), α = Rat : Sort 1.
    let subtype_rec = Expr::const_(
        Name::from_string("Subtype.rec"),
        vec![Level::zero(), lvl1.clone()],
    );
    let eq_ndrec = Expr::const_(
        Name::from_string("Eq.ndrec"),
        vec![lvl1.clone(), lvl1.clone()],
    );
    let subtype_mk = Expr::const_(Name::from_string("Subtype.mk"), vec![lvl1.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![lvl1.clone()]);

    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(c.nnrat.clone());
    let (q_id, q) = b.fresh_local(c.nnrat.clone());
    let hval_ty = c.eq_rat(c.val(p.clone()), c.val(q.clone()));
    let (h_id, h) = b.fresh_local(hval_ty.clone());

    // Recurse on p with motive: fun (pp : NNRat) => val pp = val q → pp = q.
    // minor (pv : Rat)(ppr : 0≤pv) : val (mk pv ppr) = val q → mk pv ppr = q
    //   ≡ pv = val q → mk pv ppr = q   (val (mk pv ppr) ≡ pv).
    let motive_p = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (pp_id, pp) = mb.fresh_local(c.nnrat.clone());
        let hh = c.eq_rat(c.val(pp.clone()), c.val(q.clone()));
        let concl = c.eq_nnrat(pp.clone(), q.clone());
        let imp = Expr::pi(BinderInfo::Default, hh, concl);
        mb.finish_child(mb.mk_lam(pp_id, BinderInfo::Default, c.nnrat.clone(), imp))
    };
    let minor_p = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (pv_id, pv) = mb.fresh_local(c.rat.clone());
        let ppr_ty = nonneg(c, &pv);
        let (ppr_id, ppr) = mb.fresh_local(ppr_ty.clone());
        let mk_p = Expr::apps(
            subtype_mk.clone(),
            [c.rat.clone(), nn_pred.clone(), pv.clone(), ppr.clone()],
        );
        // hh : pv = val q  (val (mk pv ppr) ≡ pv).
        let hh_ty = c.eq_rat(pv.clone(), c.val(q.clone()));
        let (hh_id, hh) = mb.fresh_local(hh_ty.clone());
        // Now recurse on q with motive: fun (qq : NNRat) => pv = val qq → mk pv ppr = qq.
        let body = build_recurse_q(c, &mb, &nn_pred, &mk_p, &pv, &ppr, &q, &hh);
        let e = mb.mk_lam(hh_id, BinderInfo::Default, hh_ty, body);
        let e = mb.mk_lam(ppr_id, BinderInfo::Default, ppr_ty, e);
        let e = mb.mk_lam(pv_id, BinderInfo::Default, c.rat.clone(), e);
        mb.finish_child(e)
    };
    let _ = (eq_ndrec, eq_refl);
    let rec_p = Expr::apps(
        subtype_rec.clone(),
        [c.rat.clone(), nn_pred.clone(), motive_p, minor_p, p.clone()],
    );
    let applied = Expr::app(rec_p, h.clone());

    let e = b.mk_lam(h_id, BinderInfo::Default, hval_ty, applied);
    let e = b.mk_lam(q_id, BinderInfo::Default, c.nnrat.clone(), e);
    let e = b.mk_lam(p_id, BinderInfo::Default, c.nnrat.clone(), e);
    b.finish(e)
}

/// Recurse on `q` so the goal becomes `mk pv ppr = mk qv qqr` with
/// `hh : pv = qv`; close by `Eq.ndrec` transport of `Eq.refl (mk pv ppr)` along
/// `hh` (proof irrelevance fills the membership slot).
#[allow(clippy::too_many_arguments)]
fn build_recurse_q(
    c: &DistribConsts,
    parent: &EnvDeclBuilder,
    nn_pred: &Expr,
    mk_p: &Expr,
    pv: &Expr,
    _ppr: &Expr,
    q: &Expr,
    hh: &Expr,
) -> Expr {
    let lvl1 = Level::succ(Level::zero());
    // Subtype.rec.{motive_univ, α_univ}; motive returns Prop (Sort 0), α = Rat : Sort 1.
    let subtype_rec = Expr::const_(
        Name::from_string("Subtype.rec"),
        vec![Level::zero(), lvl1.clone()],
    );
    let subtype_mk = Expr::const_(Name::from_string("Subtype.mk"), vec![lvl1.clone()]);
    let eq_ndrec = Expr::const_(
        Name::from_string("Eq.ndrec"),
        vec![lvl1.clone(), lvl1.clone()],
    );
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![lvl1.clone()]);

    // motive_q : fun (qq : NNRat) => pv = val qq → mk_p = qq.
    let motive_q = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (qq_id, qq) = mb.fresh_local(c.nnrat.clone());
        let hh2 = c.eq_rat(pv.clone(), c.val(qq.clone()));
        let concl = c.eq_nnrat(mk_p.clone(), qq.clone());
        let imp = Expr::pi(BinderInfo::Default, hh2, concl);
        mb.finish_child(mb.mk_lam(qq_id, BinderInfo::Default, c.nnrat.clone(), imp))
    };
    // minor_q : (qv : Rat)(qqr : 0≤qv) : pv = val (mk qv qqr) → mk_p = mk qv qqr
    //   ≡ pv = qv → mk_p = mk qv qqr.
    let minor_q = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (qv_id, qv) = mb.fresh_local(c.rat.clone());
        let qqr_ty = nonneg(c, &qv);
        let (qqr_id, qqr) = mb.fresh_local(qqr_ty.clone());
        let _mk_q = Expr::apps(
            subtype_mk.clone(),
            [c.rat.clone(), nn_pred.clone(), qv.clone(), qqr.clone()],
        );
        let hh2_ty = c.eq_rat(pv.clone(), qv.clone());
        let (hh2_id, hh2) = mb.fresh_local(hh2_ty.clone());
        // Dependent `Eq.rec` over `hh2 : pv = qv` with motive
        //   `fun (t : Rat)(heq : pv = t) => Eq NNRat mk_p (Subtype.mk t (0≤t))`,
        // where the `0≤t` proof is `qqr : 0≤qv` transported to `pv` (via symm hh2)
        // then forward to `t` (via heq). `base = Eq.refl mk_p` at `(pv, refl)`.
        let motive_t = {
            let mut tb = EnvDeclBuilder::child_of(&mb);
            let (t_id, t) = tb.fresh_local(c.rat.clone());
            let heq_ty = c.eq_rat(pv.clone(), t.clone());
            let (heq_id, heq) = tb.fresh_local(heq_ty.clone());
            // proof (0≤t) := Eq.subst (motive s := 0≤s) pv t heq (qqr' : 0≤pv).
            // But qqr is 0≤qv, not 0≤pv. We need 0≤pv. Derive via hh2? hh2:pv=qv,
            // so 0≤pv from qqr via subst along symm hh2. Build qpv : 0≤pv.
            // (qqr : 0≤qv) ; subst (motive s := 0≤s) qv pv (symm hh2) qqr : 0≤pv.
            let qpv = c.subst_rat(
                nonneg_motive(c, &mb),
                qv.clone(),
                pv.clone(),
                c.eq_symm_rat(pv.clone(), qv.clone(), hh2.clone()),
                qqr.clone(),
            );
            // proof_t : 0≤t := subst (motive s := 0≤s) pv t heq qpv.
            let proof_t = c.subst_rat(nonneg_motive(c, &tb), pv.clone(), t.clone(), heq, qpv);
            let mk_t = Expr::apps(
                subtype_mk.clone(),
                [c.rat.clone(), nn_pred.clone(), t.clone(), proof_t],
            );
            let body = c.eq_nnrat(mk_p.clone(), mk_t);
            let e = tb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
            tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), e))
        };
        // base : motive_t pv (Eq.refl pv) := Eq.refl mk_p   (mk pv (proof at pv) ≡ mk_p by proof irrel).
        let refl_mk_p = Expr::apps(eq_refl.clone(), [c.nnrat.clone(), mk_p.clone()]);
        // @Eq.rec.{motive_univ, eq_type_univ} Rat pv motive_t base qv hh2 — dependent.
        // motive returns Prop (Sort 0); the Eq is over Rat : Sort 1.
        let eq_rec = Expr::const_(
            Name::from_string("Eq.rec"),
            vec![Level::zero(), lvl1.clone()],
        );
        let transported = Expr::apps(
            eq_rec,
            [
                c.rat.clone(),
                pv.clone(),
                motive_t,
                refl_mk_p,
                qv.clone(),
                hh2.clone(),
            ],
        );
        let e = mb.mk_lam(hh2_id, BinderInfo::Default, hh2_ty, transported);
        let e = mb.mk_lam(qqr_id, BinderInfo::Default, qqr_ty, e);
        let e = mb.mk_lam(qv_id, BinderInfo::Default, c.rat.clone(), e);
        mb.finish_child(e)
    };
    let _ = eq_ndrec;
    let rec_q = Expr::apps(
        subtype_rec,
        [c.rat.clone(), nn_pred.clone(), motive_q, minor_q, q.clone()],
    );
    Expr::app(rec_q, hh.clone())
}

/// `nnPred := fun x : Rat => Rat.le Rat.zero x`.
fn nn_pred(c: &DistribConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let body = Expr::apps(c.rat_le.clone(), [c.rat_zero.clone(), x]);
    let lam = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
    b.finish(lam)
}

/// `Rat.le Rat.zero v : Prop`.
fn nonneg(c: &DistribConsts, v: &Expr) -> Expr {
    Expr::apps(c.rat_le.clone(), [c.rat_zero.clone(), v.clone()])
}

/// `fun s : Rat => Rat.le Rat.zero s` — the nonneg motive for `Eq.subst`.
fn nonneg_motive(c: &DistribConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (s_id, s) = b.fresh_local(c.rat.clone());
    let body = Expr::apps(c.rat_le.clone(), [c.rat_zero.clone(), s]);
    b.finish_child(b.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), body))
}

/// `NNRat.left_distrib` value: `NNRat.eq_of_val_eq` on the val-equality.
fn build_nnrat_left_distrib(c: &DistribConsts) -> Expr {
    let eq_of_val_eq = Expr::const_(Name::from_string("NNRat.eq_of_val_eq"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (cv_id, cv) = b.fresh_local(c.nnrat.clone());
    let (a_id, a) = b.fresh_local(c.nnrat.clone());
    let (bv_id, bv) = b.fresh_local(c.nnrat.clone());

    let lhs = c.nnmul(cv.clone(), c.nnadd(a.clone(), bv.clone()));
    let rhs = c.nnadd(
        c.nnmul(cv.clone(), a.clone()),
        c.nnmul(cv.clone(), bv.clone()),
    );

    let vc = c.val(cv.clone());
    let va = c.val(a.clone());
    let vb = c.val(bv.clone());

    // The val-equality val(lhs) = val(rhs).
    let hval = build_val_distrib_eq(c, &b, &cv, &a, &bv, &vc, &va, &vb);

    let body = Expr::apps(eq_of_val_eq, [lhs.clone(), rhs.clone(), hval]);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.nnrat.clone(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nnrat.clone(), e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.nnrat.clone(), e);
    b.finish(e)
}

/// Build `val(NNRat.mul c (NNRat.add a b)) = val(NNRat.add (mul c a)(mul c b))`.
/// LHS ≡ vc·(va+vb) after val_mul + congrArg val_add; RHS ≡ vc·va + vc·vb after
/// val_add + congrArg(×2) val_mul; the middle is `Rat.left_distrib vc va vb`.
#[allow(clippy::too_many_arguments)]
fn build_val_distrib_eq(
    c: &DistribConsts,
    parent: &EnvDeclBuilder,
    cv: &Expr,
    a: &Expr,
    bv: &Expr,
    vc: &Expr,
    va: &Expr,
    vb: &Expr,
) -> Expr {
    let lvl1 = Level::succ(Level::zero());
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![lvl1]);
    let trans = |x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr| {
        Expr::apps(eq_trans.clone(), [c.rat.clone(), x, y, z, h1, h2])
    };

    // ── LHS = vc·(va+vb) ──
    // val(mul c (add a b)) = vc · val(add a b)   (val_mul c (add a b)).
    let add_ab = c.nnadd(a.clone(), bv.clone());
    let lhs0 = c.val(c.nnmul(cv.clone(), add_ab.clone())); // val(mul c (add a b))
    let v_add_ab = c.val(add_ab.clone()); // val(add a b)
    let l_step1 = c.val_mul(cv.clone(), add_ab.clone()); // lhs0 = vc · v_add_ab
    let vc_vadd = mul_rat(c, vc.clone(), v_add_ab.clone()); // vc · v_add_ab
                                                            // congrArg (fun t => vc · t) (val_add a b : v_add_ab = va+vb).
    let va_vb = c.radd(va.clone(), vb.clone());
    let mul_vc_fn = {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = fb.fresh_local(c.rat.clone());
        let body = mul_rat(c, vc.clone(), t);
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let vab_eq = c.val_add(a.clone(), bv.clone()); // v_add_ab = va+vb
    let l_step2 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            v_add_ab.clone(),
            va_vb.clone(),
            mul_vc_fn,
            vab_eq,
        ],
    ); // vc·v_add_ab = vc·(va+vb)
    let vc_va_vb = mul_rat(c, vc.clone(), va_vb.clone()); // vc·(va+vb)
                                                          // l : lhs0 = vc·(va+vb).
    let l = trans(
        lhs0.clone(),
        vc_vadd.clone(),
        vc_va_vb.clone(),
        l_step1,
        l_step2,
    );

    // ── middle : vc·(va+vb) = vc·va + vc·vb  (Rat.left_distrib vc va vb) ──
    let mid = c.rat_left_distrib(vc.clone(), va.clone(), vb.clone());
    let vcva = mul_rat(c, vc.clone(), va.clone());
    let vcvb = mul_rat(c, vc.clone(), vb.clone());
    let vcva_vcvb = c.radd(vcva.clone(), vcvb.clone());

    // ── RHS = vc·va + vc·vb ──
    // val(add (mul c a)(mul c b)) = val(mul c a) + val(mul c b)   (val_add).
    let mul_ca = c.nnmul(cv.clone(), a.clone());
    let mul_cb = c.nnmul(cv.clone(), bv.clone());
    let rhs0 = c.val(c.nnadd(mul_ca.clone(), mul_cb.clone())); // val(add (mul c a)(mul c b))
    let v_mul_ca = c.val(mul_ca.clone());
    let v_mul_cb = c.val(mul_cb.clone());
    let r_step1 = c.val_add(mul_ca.clone(), mul_cb.clone()); // rhs0 = v_mul_ca + v_mul_cb
    let sum_vmca_vmcb = c.radd(v_mul_ca.clone(), v_mul_cb.clone());
    // rewrite v_mul_ca → vc·va via val_mul c a, in the LEFT summand.
    let vmca_eq = c.val_mul(cv.clone(), a.clone()); // v_mul_ca = vc·va
    let add_right_fn = {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = fb.fresh_local(c.rat.clone());
        let body = c.radd(t, v_mul_cb.clone());
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let r_step2 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            v_mul_ca.clone(),
            vcva.clone(),
            add_right_fn,
            vmca_eq,
        ],
    ); // (v_mul_ca + v_mul_cb) = (vc·va + v_mul_cb)
    let sum_vcva_vmcb = c.radd(vcva.clone(), v_mul_cb.clone());
    // rewrite v_mul_cb → vc·vb via val_mul c b, in the RIGHT summand.
    let vmcb_eq = c.val_mul(cv.clone(), bv.clone()); // v_mul_cb = vc·vb
    let add_left_fn = {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = fb.fresh_local(c.rat.clone());
        let body = c.radd(vcva.clone(), t);
        fb.finish_child(fb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let r_step3 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            v_mul_cb.clone(),
            vcvb.clone(),
            add_left_fn,
            vmcb_eq,
        ],
    ); // (vc·va + v_mul_cb) = (vc·va + vc·vb)
       // r : rhs0 = vc·va + vc·vb.
    let r01 = trans(
        rhs0.clone(),
        sum_vmca_vmcb.clone(),
        sum_vcva_vmcb.clone(),
        r_step1,
        r_step2,
    );
    let r = trans(
        rhs0.clone(),
        sum_vcva_vmcb.clone(),
        vcva_vcvb.clone(),
        r01,
        r_step3,
    );

    // combine: lhs0 = vc·(va+vb) = vc·va+vc·vb = rhs0.
    //   l : lhs0 = vc·(va+vb)
    //   mid : vc·(va+vb) = vc·va+vc·vb
    //   symm r : vc·va+vc·vb = rhs0
    let lm = trans(lhs0.clone(), vc_va_vb.clone(), vcva_vcvb.clone(), l, mid);
    let r_symm = c.eq_symm_rat(rhs0.clone(), vcva_vcvb.clone(), r);
    trans(lhs0, vcva_vcvb, rhs0, lm, r_symm)
}

/// `Rat.mul a b`.
fn mul_rat(_c: &DistribConsts, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Rat.mul"), vec![]), [a, b])
}

/// Build `NNReal.CauSeq.mul_add_equiv` value.
fn build_mul_add_equiv(c: &DistribConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (fc_id, fc) = b.fresh_local(c.causeq.clone());
    let (fa_id, fa) = b.fresh_local(c.causeq.clone());
    let (fb_id, fb) = b.fresh_local(c.causeq.clone());

    let cl = c.causeq_mul(fc.clone(), c.causeq_add(fa.clone(), fb.clone()));
    let cr = c.causeq_add(
        c.causeq_mul(fc.clone(), fa.clone()),
        c.causeq_mul(fc.clone(), fb.clone()),
    );

    // Equiv body: ∀ ε, 0<ε → ∃ N, ∀ n, N≤n → And (vL<vR+ε)(vR<vL+ε).
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let pred = build_equiv_pred(c, &b, &cl, &cr, &eps);
    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(c.nat_zero.clone(), m.clone());
        let (hle_id, _hle) = bw.fresh_local(hle_ty.clone());

        // vL = vseq cl m, vR = vseq cr m. They are EQUAL via the pointwise
        // NNRat.left_distrib lifted through NNRat.val.
        let vl = c.vseq(&cl, &m);
        let vr = c.vseq(&cr, &m);
        // h_eq : vL = vR.
        let h_eq = build_pointwise_val_eq(c, &bw, &fc, &fa, &fb, &m);

        // vL < vR + ε:  from vR < vR+ε (add_lt_add_left 0 ε vR + add_zero) and
        //   subst vR → vL via symm h_eq on the LHS.
        let vr_eps = c.radd(vr.clone(), eps.clone());
        let vr_lt = build_self_lt_add(c, &bw, &vr, &eps, &hpos);
        // left : vL < vR + ε := subst (motive t := t < vR+ε) vR vL (symm h_eq) vr_lt.
        let motive_l = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
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

        // vR < vL + ε:  from vL < vL+ε and subst vL → vR via h_eq on BOTH the LHS
        //   and the inner RHS summand. Simplest: vL < vL+ε, then subst vL→vR.
        let vl_eps = c.radd(vl.clone(), eps.clone());
        let vl_lt = build_self_lt_add(c, &bw, &vl, &eps, &hpos);
        // right0 : vL < vL + ε ; rewrite LHS vL → vR via h_eq → vR < vL + ε.
        let motive_r = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(t, vl_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let right = c.subst_rat(motive_r, vl.clone(), vr.clone(), h_eq, vl_lt);

        // And.intro (vL<vR+ε)(vR<vL+ε) left right.
        let l_ty = c.lt(vl.clone(), vr_eps);
        let r_ty = c.lt(vr.clone(), vl_eps);
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
    let e = b.mk_lam(fb_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(fa_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(fc_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// `v < v + ε` from `0<ε`: add_lt_add_left 0 ε v hpos : (v+0)<(v+ε), subst v+0→v.
fn build_self_lt_add(
    c: &DistribConsts,
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
        let body = c.lt(t, v_eps.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst_rat(motive, v_zero, v.clone(), add_zero, h)
}

/// The pointwise val-equality `vseq cl m = vseq cr m`, where `cl = mul fc (add
/// fa fb)`, `cr = add (mul fc fa)(mul fc fb)`.
///
/// `vseq cl m ≡ val(NNRat.mul (fc m)(NNRat.add (fa m)(fb m)))` (defeq through
/// CauSeq.mul/add/seq/mk), and likewise `vseq cr m ≡ val(NNRat.add (NNRat.mul
/// (fc m)(fa m))(NNRat.mul (fc m)(fb m)))`. The two are
/// `congrArg NNRat.val (NNRat.left_distrib (fc m)(fa m)(fb m))`.
fn build_pointwise_val_eq(
    c: &DistribConsts,
    parent: &EnvDeclBuilder,
    fc: &Expr,
    fa: &Expr,
    fb: &Expr,
    m: &Expr,
) -> Expr {
    let cm = c.seq_at(fc, m);
    let am = c.seq_at(fa, m);
    let bm = c.seq_at(fb, m);
    // NNRat.left_distrib (fc m)(fa m)(fb m) : mul cm (add am bm) = add (mul cm am)(mul cm bm).
    let ld = c.nnrat_left_distrib(cm.clone(), am.clone(), bm.clone());
    let lhs_nn = c.nnmul(cm.clone(), c.nnadd(am.clone(), bm.clone()));
    let rhs_nn = c.nnadd(
        c.nnmul(cm.clone(), am.clone()),
        c.nnmul(cm.clone(), bm.clone()),
    );
    // congrArg NNRat.val ld : val(lhs_nn) = val(rhs_nn) ≡ vseq cl m = vseq cr m.
    let _ = parent;
    c.congr_arg_nnrat_rat(lhs_nn, rhs_nn, c.nnrat_val.clone(), ld)
}

/// `fun N => ∀ n, N≤n → And (vseq cl n < vseq cr n + ε)(vseq cr n < vseq cl n + ε)`.
fn build_equiv_pred(
    c: &DistribConsts,
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
        let left = c.lt(vl.clone(), c.radd(vr.clone(), eps.clone()));
        let right = c.lt(vr.clone(), c.radd(vl.clone(), eps.clone()));
        let concl = Expr::apps(c.and_c.clone(), [left, right]);
        let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
        bi.finish_child(e)
    };
    bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner))
}

/// `NNReal.mul_add` value: triple `Quot.ind` + `Quot.sound` on the Equiv.
fn build_nnreal_mul_add(c: &DistribConsts, nnreal: &Expr) -> Expr {
    let equiv_lemma = Expr::const_(Name::from_string("NNReal.CauSeq.mul_add_equiv"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (cv_id, cv) = b.fresh_local(nnreal.clone());
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());
    let body = descend_c(c, &b, nnreal, &cv, &a, &bv, &equiv_lemma);
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// Descend on `c` (the scalar) with motive `fun x => Eq NNReal (mul x (add a b))
///   (add (mul x a)(mul x b))`. Leaf supplies rep `fc`.
fn descend_c(
    c: &DistribConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    cv: &Expr,
    a: &Expr,
    bv: &Expr,
    equiv_lemma: &Expr,
) -> Expr {
    let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let mul = |x: Expr, y: Expr| Expr::apps(nnmul.clone(), [x, y]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);
    let eq_nn = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nnreal.clone(), x, y],
        )
    };
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let lhs = mul(x.clone(), add(a.clone(), bv.clone()));
        let rhs = add(mul(x.clone(), a.clone()), mul(x.clone(), bv.clone()));
        let body = eq_nn(lhs, rhs);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), body))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (fc_id, fc) = mf.fresh_local(c.causeq.clone());
        let mkc = c.quot_mk(fc.clone());
        let body = descend_a(c, &mf, nnreal, &mkc, &fc, a, bv, equiv_lemma);
        mf.finish_child(mf.mk_lam(fc_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            cv.clone(),
        ],
    )
}

/// Descend on `a` with motive `fun y => Eq NNReal (mul (mk fc)(add y bv))
///   (add (mul (mk fc) y)(mul (mk fc) bv))`. Leaf supplies rep `fa`.
#[allow(clippy::too_many_arguments)]
fn descend_a(
    c: &DistribConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mkc: &Expr,
    fc: &Expr,
    a: &Expr,
    bv: &Expr,
    equiv_lemma: &Expr,
) -> Expr {
    let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let mul = |x: Expr, y: Expr| Expr::apps(nnmul.clone(), [x, y]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);
    let eq_nn = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nnreal.clone(), x, y],
        )
    };
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = mb.fresh_local(nnreal.clone());
        let lhs = mul(mkc.clone(), add(y.clone(), bv.clone()));
        let rhs = add(mul(mkc.clone(), y.clone()), mul(mkc.clone(), bv.clone()));
        let body = eq_nn(lhs, rhs);
        mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), body))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (fa_id, fa) = mf.fresh_local(c.causeq.clone());
        let mka = c.quot_mk(fa.clone());
        let body = descend_b(c, &mf, nnreal, mkc, fc, &mka, &fa, bv, equiv_lemma);
        mf.finish_child(mf.mk_lam(fa_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            a.clone(),
        ],
    )
}

/// Descend on `b` with motive `fun z => Eq NNReal (mul (mk fc)(add (mk fa) z))
///   (add (mul (mk fc)(mk fa))(mul (mk fc) z))`. Leaf supplies rep `fb`; the goal
/// reduces (NNReal.mul/add Quot.lift comp) to `Quot.sound` on the Equiv.
#[allow(clippy::too_many_arguments)]
fn descend_b(
    c: &DistribConsts,
    parent: &EnvDeclBuilder,
    nnreal: &Expr,
    mkc: &Expr,
    fc: &Expr,
    mka: &Expr,
    fa: &Expr,
    bv: &Expr,
    equiv_lemma: &Expr,
) -> Expr {
    let nnmul = Expr::const_(Name::from_string("NNReal.mul"), vec![]);
    let nnadd = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let mul = |x: Expr, y: Expr| Expr::apps(nnmul.clone(), [x, y]);
    let add = |x: Expr, y: Expr| Expr::apps(nnadd.clone(), [x, y]);
    let eq_nn = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nnreal.clone(), x, y],
        )
    };
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = mb.fresh_local(nnreal.clone());
        let lhs = mul(mkc.clone(), add(mka.clone(), z.clone()));
        let rhs = add(mul(mkc.clone(), mka.clone()), mul(mkc.clone(), z.clone()));
        let body = eq_nn(lhs, rhs);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, nnreal.clone(), body))
    };
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(parent);
        let (fb_id, fb) = mf.fresh_local(c.causeq.clone());
        // goal: Eq NNReal (mul (mk fc)(add (mk fa)(mk fb)))
        //                 (add (mul (mk fc)(mk fa))(mul (mk fc)(mk fb))).
        // LHS ≡ mk (CauSeq.mul fc (CauSeq.add fa fb)); RHS ≡ mk (CauSeq.add
        //   (CauSeq.mul fc fa)(CauSeq.mul fc fb)) — via NNReal.mul/add Quot.lift
        //   computation. So Quot.sound on the Equiv lemma closes it.
        let cl = c.causeq_mul(fc.clone(), c.causeq_add(fa.clone(), fb.clone()));
        let cr = c.causeq_add(
            c.causeq_mul(fc.clone(), fa.clone()),
            c.causeq_mul(fc.clone(), fb.clone()),
        );
        let equiv = Expr::apps(equiv_lemma.clone(), [fc.clone(), fa.clone(), fb.clone()]);
        let body = c.quot_sound(cl, cr, equiv);
        mf.finish_child(mf.mk_lam(fb_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            bv.clone(),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "NNRat.eq_of_val_eq",
        "NNRat.left_distrib",
        "NNReal.CauSeq.mul_add_equiv",
        "NNReal.mul_add",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_mul_distrib()
            .expect("init_algebra_nnreal_mul_distrib");
        env.init_algebra_nnreal_mul_distrib().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_mul_add_kernel_check() {
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
    fn test_nnreal_mul_add_constructive_empty_closure() {
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
