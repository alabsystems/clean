// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage B2 (REBUILT): the nonneg-real Cauchy carrier as
//! a Cauchy SUBTYPE.
//!
//! # Why this module was rebuilt
//!
//! The first scaffold defined `NNReal.CauSeq` as a FREE inductive over an
//! arbitrary `Nat → NNRat` (constructor `mk : (Nat → NNRat) → CauSeq`, NO
//! Cauchy modulus). The sqrt panel proved that carrier FATALLY DEFECTIVE for
//! `NNReal.mul`: a total axiom-free multiplicative `Quot.lift` needs the shared
//! factor of `Equiv`-related sequences to be BOUNDED, and over the unbounded
//! free carrier no such bound exists (counterexample `s_n = n`, `x = const 0`,
//! `x2_n = 1/n`: `s·x ≡ s·x2` fails to be `Equiv` because `s_n·(x_n − x2_n) =
//! n·(1/n) = 1 ↛ 0`). The cure is to make `CauSeq` a **Cauchy SUBTYPE**, so
//! every representative carries an `IsCauchy` proof and is therefore BOUNDED
//! (`NNReal.IsCauchy_bounded`, `algebra_nnreal_mul.rs`), which is exactly what
//! the multiplicative respect proof consumes.
//!
//! # The carrier (axiom-free, kernel-checked)
//!
//! `IsCauchy` predicate (two-sided strict-bound ε-form on the `.val`s — NOT
//! `Rat.dist`, which is an admitted `Declaration::Axiom`):
//! - `NNReal.IsCauchy : (Nat → NNRat) → Prop`
//!   `:= fun f => ∀ (ε : Rat), Rat.lt Rat.zero ε →`
//!   `     ∃ (N : Nat), ∀ (m n : Nat), Nat.le N m → Nat.le N n →`
//!   `       And (Rat.lt (val (f m)) (Rat.add (val (f n)) ε))`
//!   `           (Rat.lt (val (f n)) (Rat.add (val (f m)) ε))`
//!
//! The Cauchy subtype + projections (built on the existing `Subtype` inductive,
//! exactly as `NNRat` is):
//! - `NNReal.CauSeq : Type 0 := @Subtype.{1} (Nat → NNRat) NNReal.IsCauchy`
//! - `NNReal.CauSeq.seq : NNReal.CauSeq → (Nat → NNRat)`   (= `Subtype.val`)
//! - `NNReal.CauSeq.mk : (f : Nat → NNRat) → IsCauchy f → NNReal.CauSeq`
//!     (= `Subtype.mk`)
//! - `NNReal.CauSeq.property : (s : CauSeq) → IsCauchy (seq s)`
//!     (= `Subtype.property`)
//! - `NNReal.CauSeq.const : NNRat → NNReal.CauSeq`   (constant sequence; its
//!     `IsCauchy` proof is `NNReal.IsCauchy.const_proof`)
//!
//! Supporting theorem (empty closure):
//! - `NNReal.IsCauchy.const_proof : ∀ c, IsCauchy (fun _ => c)`
//!
//! The equivalence relation (SAME dist-free two-sided strict-bound ε-form,
//! representatives via `.seq`):
//! - `NNReal.CauSeq.Equiv : NNReal.CauSeq → NNReal.CauSeq → Prop`
//!   `:= fun f g => ∀ (ε : Rat), Rat.lt 0 ε →`
//!   `     ∃ (N : Nat), ∀ (n : Nat), Nat.le N n →`
//!   `       And (Rat.lt (val (seq f n)) (Rat.add (val (seq g n)) ε))`
//!   `           (Rat.lt (val (seq g n)) (Rat.add (val (seq f n)) ε))`
//!
//! Equivalence properties (each `Declaration::Theorem`, Constructive,
//! foundational closure):
//! - `NNReal.CauSeq.Equiv.refl : ∀ f, Equiv f f`
//! - `NNReal.CauSeq.Equiv.symm : ∀ f g, Equiv f g → Equiv g f`
//!
//! (`trans` lands in `algebra_nnreal_trans.rs`.)
//!
//! The quotient carrier + the constant embedding:
//! - `NNReal : Type 0 := @Quot.{1} NNReal.CauSeq NNReal.CauSeq.Equiv`
//! - `NNReal.mk : NNReal.CauSeq → NNReal`   (= `Quot.mk`)
//! - `NNReal.ofRat : (x : Rat) → Rat.le 0 x → NNReal`
//!     `:= fun x h => NNReal.mk (CauSeq.const (NNRat.ofRat x h))`
//!
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural` anywhere.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved constant handles + smart-constructors for the nonneg-real
/// Cauchy SUBTYPE carrier. The raw sequence elements are `NNRat` (Stage B1);
/// distances are taken over `NNRat.val : NNRat → Rat`.
pub(crate) struct NNRealConsts {
    prop: Expr,
    nat: Expr,
    rat: Expr,
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_of_rat: Expr,
    rat_zero: Expr,
    rat_lt: Expr,
    rat_add: Expr,
    rat_add_zero: Expr,
    rat_add_lt_add_left: Expr,
    rat_le: Expr,
    nat_le: Expr,
    // And machinery (Prop level).
    and_c: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    // The Cauchy subtype is `@Subtype.{1} (Nat → NNRat) IsCauchy`.
    subtype: Expr,
    subtype_mk: Expr,
    subtype_val: Expr,
    subtype_property: Expr,
    is_cauchy: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    quot: Expr,
    quot_mk: Expr,
    // Logic: Exists / Exists.intro at level 1 (witness Nat : Sort 1).
    exists_c: Expr,
    exists_intro: Expr,
    // Eq.{1} over Rat, for transporting along add_zero.
    eq_subst_rat: Expr,
}

impl NNRealConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nat: k("Nat"),
            rat: k("Rat"),
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_of_rat: k("NNRat.ofRat"),
            rat_zero: k("Rat.zero"),
            rat_lt: k("Rat.lt"),
            rat_add: k("Rat.add"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_le: k("Rat.le"),
            nat_le: k("Nat.le"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            and_left: k("And.left"),
            and_right: k("And.right"),
            subtype: Expr::const_(Name::from_string("Subtype"), vec![lvl1.clone()]),
            subtype_mk: Expr::const_(Name::from_string("Subtype.mk"), vec![lvl1.clone()]),
            subtype_val: Expr::const_(Name::from_string("Subtype.val"), vec![lvl1.clone()]),
            subtype_property: Expr::const_(
                Name::from_string("Subtype.property"),
                vec![lvl1.clone()],
            ),
            is_cauchy: k("NNReal.IsCauchy"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            quot: Expr::const_(Name::from_string("Quot"), vec![lvl1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            // Nat : Type 0 = Sort 1, so Exists over Nat is `Exists.{1}`.
            exists_c: Expr::const_(Name::from_string("Exists"), vec![lvl1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![lvl1.clone()]),
            eq_subst_rat: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1]),
        }
    }

    /// `Nat → NNRat` — the raw sequence type.
    fn seq_ty(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.nat.clone(), self.nnrat.clone())
    }
    /// `NNRat.val q : Rat`.
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    /// `f n : NNRat` for a raw sequence `f : Nat → NNRat`.
    fn raw_at(&self, f: Expr, n: Expr) -> Expr {
        Expr::app(f, n)
    }
    /// `NNReal.CauSeq.seq f : Nat → NNRat`.
    fn seq_of(&self, f: Expr) -> Expr {
        Expr::app(self.causeq_seq.clone(), f)
    }
    /// `(seq f) n : NNRat`.
    fn seq_at(&self, f: Expr, n: Expr) -> Expr {
        Expr::app(self.seq_of(f), n)
    }
    /// `Rat.add a b : Rat`.
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    /// `Rat.lt a b : Prop`.
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    /// `And p q : Prop`.
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    /// `@And.intro p q hp hq : And p q`.
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p, q, hp, hq])
    }
    /// `Rat.add_lt_add_left a b c (h : a<b) : Rat.lt (c+a) (c+b)`.
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    /// `Rat.add_zero a : Eq (Rat.add a Rat.zero) a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    /// The two-sided strict-bound conjunction for the pair `(x,y)` at tolerance
    /// `ε`:  `And (Rat.lt x (y+ε)) (Rat.lt y (x+ε))`.
    fn bound_pair(&self, x: Expr, y: Expr, eps: Expr) -> Expr {
        let left = self.lt(x.clone(), self.add(y.clone(), eps.clone()));
        let right = self.lt(y, self.add(x, eps));
        self.and_ty(left, right)
    }
    /// `Nat.le a b : Prop`.
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `NNReal.IsCauchy f : Prop` for a raw sequence `f : Nat → NNRat`.
    fn is_cauchy(&self, f: Expr) -> Expr {
        Expr::app(self.is_cauchy.clone(), f)
    }
    /// `NNReal.CauSeq.Equiv f g : Prop`.
    fn equiv(&self, f: Expr, g: Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [f, g])
    }
    /// `@Quot.mk.{1} CauSeq Equiv l : NNReal`.
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst_rat.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@Subtype.mk.{1} (Nat→NNRat) IsCauchy f h : CauSeq`.
    fn subtype_mk(&self, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.subtype_mk.clone(),
            [self.seq_ty(), self.is_cauchy.clone(), f, h],
        )
    }
    /// `@Subtype.val.{1} (Nat→NNRat) IsCauchy s : Nat→NNRat`.
    fn subtype_val(&self, s: Expr) -> Expr {
        Expr::apps(
            self.subtype_val.clone(),
            [self.seq_ty(), self.is_cauchy.clone(), s],
        )
    }
    /// `@Subtype.property.{1} (Nat→NNRat) IsCauchy s : IsCauchy (Subtype.val s)`.
    fn subtype_property(&self, s: Expr) -> Expr {
        Expr::apps(
            self.subtype_property.clone(),
            [self.seq_ty(), self.is_cauchy.clone(), s],
        )
    }

    /// The `IsCauchy` body for a fixed raw sequence `f : Nat → NNRat` (a
    /// `Prop`): `∀ ε, 0<ε → ∃ N, ∀ m n, N≤m → N≤n → bound_pair (val (f m))(val (f n)) ε`.
    fn is_cauchy_body(&self, parent: &EnvDeclBuilder, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (eps_id, eps) = b.fresh_local(self.rat.clone());
        let hpos = self.lt(self.rat_zero.clone(), eps.clone());
        let (hpos_id, _hpos) = b.fresh_local(hpos.clone());

        // pred_n N := ∀ m n, N≤m → N≤n → bound_pair (val (f m))(val (f n)) ε
        let pred_n = {
            let mut bn = EnvDeclBuilder::child_of(&b);
            let (cap_id, cap) = bn.fresh_local(self.nat.clone());
            let inner = {
                let mut bi = EnvDeclBuilder::child_of(&bn);
                let (m_id, m) = bi.fresh_local(self.nat.clone());
                let (n_id, n) = bi.fresh_local(self.nat.clone());
                let hle_m = self.nat_le(cap.clone(), m.clone());
                let (hlem_id, _h) = bi.fresh_local(hle_m.clone());
                let hle_n = self.nat_le(cap.clone(), n.clone());
                let (hlen_id, _h2) = bi.fresh_local(hle_n.clone());
                let concl = self.bound_pair(
                    self.val(self.raw_at(f.clone(), m.clone())),
                    self.val(self.raw_at(f.clone(), n.clone())),
                    eps.clone(),
                );
                let e = bi.mk_pi(hlen_id, BinderInfo::Default, hle_n, concl);
                let e = bi.mk_pi(hlem_id, BinderInfo::Default, hle_m, e);
                let e = bi.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), e);
                let e = bi.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
                bi.finish_child(e)
            };
            let lam = bn.mk_lam(cap_id, BinderInfo::Default, self.nat.clone(), inner);
            bn.finish_child(lam)
        };
        let exists_n = Expr::apps(self.exists_c.clone(), [self.nat.clone(), pred_n]);
        let e = b.mk_pi(hpos_id, BinderInfo::Default, hpos, exists_n);
        let e = b.mk_pi(eps_id, BinderInfo::Default, self.rat.clone(), e);
        b.finish_child(e)
    }

    /// The `Equiv` body for a fixed pair `f g` (a `Prop`):
    ///   `∀ ε, Rat.lt 0 ε → ∃ N, ∀ n, Nat.le N n →`
    ///   `   bound_pair (val (seq f n))(val (seq g n)) ε`.
    fn equiv_body(&self, parent: &EnvDeclBuilder, f: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (eps_id, eps) = b.fresh_local(self.rat.clone());
        let hpos = self.lt(self.rat_zero.clone(), eps.clone());
        let (hpos_id, _hpos) = b.fresh_local(hpos.clone());

        let pred_n = {
            let mut bn = EnvDeclBuilder::child_of(&b);
            let (n_id, n_cap) = bn.fresh_local(self.nat.clone());
            let inner = {
                let mut bi = EnvDeclBuilder::child_of(&bn);
                let (m_id, m) = bi.fresh_local(self.nat.clone());
                let hle = self.nat_le(n_cap.clone(), m.clone());
                let (hle_id, _hle) = bi.fresh_local(hle.clone());
                let concl = self.bound_pair(
                    self.val(self.seq_at(f.clone(), m.clone())),
                    self.val(self.seq_at(g.clone(), m.clone())),
                    eps.clone(),
                );
                let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
                let e = bi.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
                bi.finish_child(e)
            };
            let lam = bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner);
            bn.finish_child(lam)
        };
        let exists_n = Expr::apps(self.exists_c.clone(), [self.nat.clone(), pred_n]);
        let e = b.mk_pi(hpos_id, BinderInfo::Default, hpos, exists_n);
        let e = b.mk_pi(eps_id, BinderInfo::Default, self.rat.clone(), e);
        b.finish_child(e)
    }
}

impl Environment {
    /// Register the Stage-B2 nonneg-real Cauchy-SUBTYPE carrier: the `IsCauchy`
    /// predicate, the `CauSeq := Subtype IsCauchy` carrier, its `mk`/`seq`/
    /// `property`/`const`, the `Equiv` relation, `refl`/`symm`, the `NNReal :=
    /// Quot Equiv` carrier, `NNReal.mk`, and `NNReal.ofRat`. Idempotent.
    /// (`trans` lands in `algebra_nnreal_trans.rs`; arithmetic/order/sqrt
    /// elsewhere.)
    pub fn init_algebra_nnreal_cauchy(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_nnrat()?;
        self.init_subtype()?;
        self.init_exists()?;
        self.init_eq()?;
        self.init_and()?;
        self.init_quot();
        // Rat.lt, Rat.add_zero, Nat.le.
        self.init_rat_linear_order()?;
        // Rat.add_lt_add_left (constructive strict-add monotonicity).
        self.register_rat_add_lt_add_left()?;

        let c = NNRealConsts::new();
        self.register_nnreal_is_cauchy(&c)?;
        self.register_nnreal_cauchy_carrier(&c)?;
        self.register_nnreal_cauchy_equiv(&c)?;
        self.register_nnreal_cauchy_equiv_props(&c)?;
        self.register_nnreal_quotient(&c)?;
        Ok(())
    }

    /// B2-0. The `IsCauchy` predicate + the constant-sequence proof.
    fn register_nnreal_is_cauchy(&mut self, c: &NNRealConsts) -> Result<(), EnvError> {
        // NNReal.IsCauchy : (Nat → NNRat) → Prop
        if self
            .get_const(&Name::from_string("NNReal.IsCauchy"))
            .is_none()
        {
            let ty = Expr::pi(BinderInfo::Default, c.seq_ty(), c.prop.clone());
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, f) = b.fresh_local(c.seq_ty());
                let body = c.is_cauchy_body(&b, &f);
                let e = b.mk_lam(f_id, BinderInfo::Default, c.seq_ty(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNReal.IsCauchy"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // NNReal.IsCauchy.const_proof : ∀ (cval : NNRat), IsCauchy (fun _ => cval).
        //
        // For any ε with 0<ε, take N := Nat.zero. For all m,n the two values are
        // `val cval` and `val cval`; both conjuncts are `val cval < val cval + ε`
        // from `Rat.add_lt_add_left 0 ε (val cval) hpos : (val cval + 0) < (val
        // cval + ε)` transported along `Rat.add_zero (val cval)`.
        if self
            .get_const(&Name::from_string("NNReal.IsCauchy.const_proof"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (cv_id, cv) = b.fresh_local(c.nnrat.clone());
                let const_seq = const_seq_expr(c, &b, &cv);
                let body = c.is_cauchy(const_seq);
                let e = b.mk_pi(cv_id, BinderInfo::Default, c.nnrat.clone(), body);
                b.finish(e)
            };
            let value = build_const_cauchy_proof(c);
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("NNReal.IsCauchy.const_proof"),
                level_params: vec![],
                type_: ty,
                value,
            })?;
        }
        Ok(())
    }

    /// B2a. The Cauchy subtype carrier + `seq`/`mk`/`property`/`const`.
    fn register_nnreal_cauchy_carrier(&mut self, c: &NNRealConsts) -> Result<(), EnvError> {
        // NNReal.CauSeq : Type 0 := @Subtype.{1} (Nat → NNRat) NNReal.IsCauchy
        if self
            .get_const(&Name::from_string("NNReal.CauSeq"))
            .is_none()
        {
            let causeq_ty = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
            let value = Expr::apps(c.subtype.clone(), [c.seq_ty(), c.is_cauchy.clone()]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNReal.CauSeq"),
                level_params: vec![],
                type_: causeq_ty,
                value,
                is_reducible: true,
            })?;
        }

        // NNReal.CauSeq.seq : CauSeq → (Nat → NNRat) := fun s => Subtype.val s
        if self
            .get_const(&Name::from_string("NNReal.CauSeq.seq"))
            .is_none()
        {
            let ty = Expr::pi(BinderInfo::Default, c.causeq.clone(), c.seq_ty());
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(c.causeq.clone());
                let body = c.subtype_val(s);
                let e = b.mk_lam(s_id, BinderInfo::Default, c.causeq.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNReal.CauSeq.seq"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // NNReal.CauSeq.mk : (f : Nat → NNRat) → IsCauchy f → CauSeq
        //   := fun f h => Subtype.mk f h
        if self
            .get_const(&Name::from_string("NNReal.CauSeq.mk"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, f) = b.fresh_local(c.seq_ty());
                let hcau = c.is_cauchy(f.clone());
                let (h_id, _h) = b.fresh_local(hcau.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hcau, c.causeq.clone());
                let e = b.mk_pi(f_id, BinderInfo::Default, c.seq_ty(), e);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, f) = b.fresh_local(c.seq_ty());
                let hcau = c.is_cauchy(f.clone());
                let (h_id, h) = b.fresh_local(hcau.clone());
                let body = c.subtype_mk(f.clone(), h);
                let e = b.mk_lam(h_id, BinderInfo::Default, hcau, body);
                let e = b.mk_lam(f_id, BinderInfo::Default, c.seq_ty(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNReal.CauSeq.mk"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // NNReal.CauSeq.property : (s : CauSeq) → IsCauchy (seq s)
        //   := fun s => Subtype.property s
        if self
            .get_const(&Name::from_string("NNReal.CauSeq.property"))
            .is_none()
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(c.causeq.clone());
                let concl = c.is_cauchy(c.seq_of(s.clone()));
                let e = b.mk_pi(s_id, BinderInfo::Default, c.causeq.clone(), concl);
                b.finish(e)
            };
            // Subtype.property s : IsCauchy (Subtype.val s) ≡ IsCauchy (seq s).
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(c.causeq.clone());
                let body = c.subtype_property(s);
                let e = b.mk_lam(s_id, BinderInfo::Default, c.causeq.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNReal.CauSeq.property"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // NNReal.CauSeq.const : NNRat → CauSeq
        //   := fun q => CauSeq.mk (fun _ => q) (IsCauchy.const_proof q)
        if self
            .get_const(&Name::from_string("NNReal.CauSeq.const"))
            .is_none()
        {
            let causeq_mk = Expr::const_(Name::from_string("NNReal.CauSeq.mk"), vec![]);
            let const_proof =
                Expr::const_(Name::from_string("NNReal.IsCauchy.const_proof"), vec![]);
            let ty = Expr::pi(BinderInfo::Default, c.nnrat.clone(), c.causeq.clone());
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (q_id, q) = b.fresh_local(c.nnrat.clone());
                let const_seq = const_seq_expr(c, &b, &q);
                let hcau = Expr::app(const_proof, q.clone());
                let body = Expr::apps(causeq_mk, [const_seq, hcau]);
                let e = b.mk_lam(q_id, BinderInfo::Default, c.nnrat.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNReal.CauSeq.const"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        Ok(())
    }

    /// B2b. The `Equiv` relation definition.
    fn register_nnreal_cauchy_equiv(&mut self, c: &NNRealConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNReal.CauSeq.Equiv"))
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
            let body = c.equiv_body(&b, &f, &g);
            let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), body);
            let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNReal.CauSeq.Equiv"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// B2c. `Equiv.refl` and `Equiv.symm` (Constructive, foundational closure).
    fn register_nnreal_cauchy_equiv_props(&mut self, c: &NNRealConsts) -> Result<(), EnvError> {
        self.register_nnreal_equiv_refl(c)?;
        self.register_nnreal_equiv_symm(c)?;
        Ok(())
    }

    /// `NNReal.CauSeq.Equiv.refl : ∀ f, Equiv f f`.
    fn register_nnreal_equiv_refl(&mut self, c: &NNRealConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.Equiv.refl");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let body = c.equiv(f.clone(), f.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, c.causeq.clone(), body);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let hpos = c.lt(c.rat_zero.clone(), eps.clone());
            let (hpos_id, hpos_h) = b.fresh_local(hpos.clone());

            // pred_n := fun N => ∀ n, Nat.le N n → bound_pair (val(seq f n))(val(seq f n)) ε
            let pred_n = {
                let mut bn = EnvDeclBuilder::child_of(&b);
                let (n_id, n_cap) = bn.fresh_local(c.nat.clone());
                let inner = {
                    let mut bi = EnvDeclBuilder::child_of(&bn);
                    let (m_id, m) = bi.fresh_local(c.nat.clone());
                    let hle = c.nat_le(n_cap.clone(), m.clone());
                    let (hle_id, _hle) = bi.fresh_local(hle.clone());
                    let vfm = c.val(c.seq_at(f.clone(), m.clone()));
                    let concl = c.bound_pair(vfm.clone(), vfm.clone(), eps.clone());
                    let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
                    let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
                    bi.finish_child(e)
                };
                let lam = bn.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner);
                bn.finish_child(lam)
            };

            // witness over N := Nat.zero.
            let witness_proof = {
                let mut bw = EnvDeclBuilder::child_of(&b);
                let (m_id, m) = bw.fresh_local(c.nat.clone());
                let hle = c.nat_le(
                    Expr::const_(Name::from_string("Nat.zero"), vec![]),
                    m.clone(),
                );
                let (hle_id, _hle) = bw.fresh_local(hle.clone());
                let vfm = c.val(c.seq_at(f.clone(), m.clone()));
                let v_plus_eps = c.add(vfm.clone(), eps.clone());
                let step =
                    c.add_lt_add_left(c.rat_zero.clone(), eps.clone(), vfm.clone(), hpos_h.clone());
                let v_plus_zero = c.add(vfm.clone(), c.rat_zero.clone());
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.lt(t, v_plus_eps.clone());
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let p = c.subst_rat(
                    motive,
                    v_plus_zero,
                    vfm.clone(),
                    c.add_zero(vfm.clone()),
                    step,
                );
                let conj = c.lt(vfm.clone(), v_plus_eps.clone());
                let proof = c.and_intro(conj.clone(), conj, p.clone(), p);
                let e = bw.mk_lam(hle_id, BinderInfo::Default, hle, proof);
                let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
                bw.finish_child(e)
            };

            let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let exists_term = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), pred_n, nat_zero, witness_proof],
            );

            let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos, exists_term);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.CauSeq.Equiv.symm : ∀ f g, Equiv f g → Equiv g f`.
    fn register_nnreal_equiv_symm(&mut self, c: &NNRealConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.CauSeq.Equiv.symm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.causeq.clone());
            let (g_id, g) = b.fresh_local(c.causeq.clone());
            let hyp = c.equiv(f.clone(), g.clone());
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let concl = c.equiv(g.clone(), f.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.causeq.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.causeq.clone(), e);
            b.finish(e)
        };

        let value = build_equiv_symm_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// B2d. The quotient carrier `NNReal := Quot Equiv`, `NNReal.mk`,
    /// `NNReal.ofRat`.
    fn register_nnreal_quotient(&mut self, c: &NNRealConsts) -> Result<(), EnvError> {
        // NNReal : Type 0 := @Quot.{1} CauSeq Equiv
        if self.get_const(&Name::from_string("NNReal")).is_none() {
            let nnreal_ty = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
            let value = Expr::apps(c.quot.clone(), [c.causeq.clone(), c.causeq_equiv.clone()]);
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNReal"),
                level_params: vec![],
                type_: nnreal_ty,
                value,
                is_reducible: true,
            })?;
        }
        let nnreal = Expr::const_(Name::from_string("NNReal"), vec![]);

        // NNReal.mk : CauSeq → NNReal := fun f => Quot.mk _ Equiv f
        if self.get_const(&Name::from_string("NNReal.mk")).is_none() {
            let ty = Expr::pi(BinderInfo::Default, c.causeq.clone(), nnreal.clone());
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, f) = b.fresh_local(c.causeq.clone());
                let body = c.quot_mk(f);
                let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNReal.mk"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        // NNReal.ofRat : (x : Rat) → Rat.le 0 x → NNReal
        //   := fun x h => NNReal.mk (CauSeq.const (NNRat.ofRat x h))
        if self.get_const(&Name::from_string("NNReal.ofRat")).is_none() {
            let nnreal_mk = Expr::const_(Name::from_string("NNReal.mk"), vec![]);
            let causeq_const = Expr::const_(Name::from_string("NNReal.CauSeq.const"), vec![]);
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(c.rat.clone());
                let hnn = Expr::apps(c.rat_le.clone(), [c.rat_zero.clone(), x.clone()]);
                let (h_id, _h) = b.fresh_local(hnn.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hnn, nnreal.clone());
                let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
                b.finish(e)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(c.rat.clone());
                let hnn = Expr::apps(c.rat_le.clone(), [c.rat_zero.clone(), x.clone()]);
                let (h_id, h) = b.fresh_local(hnn.clone());
                let q = Expr::apps(c.nnrat_of_rat.clone(), [x.clone(), h]);
                let cs = Expr::app(causeq_const, q);
                let body = Expr::app(nnreal_mk, cs);
                let e = b.mk_lam(h_id, BinderInfo::Default, hnn, body);
                let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("NNReal.ofRat"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        Ok(())
    }
}

/// `fun _ : Nat => cv` — the constant raw sequence.
fn const_seq_expr(c: &NNRealConsts, parent: &EnvDeclBuilder, cv: &Expr) -> Expr {
    let mut m = EnvDeclBuilder::child_of(parent);
    let (n_id, _n) = m.fresh_local(c.nat.clone());
    m.finish_child(m.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), cv.clone()))
}

/// Build the proof of `NNReal.IsCauchy.const_proof`. For any `cv`, `ε`, `0<ε`,
/// take `N := Nat.zero`; for all `m,n` both conjuncts are `val cv < val cv + ε`.
fn build_const_cauchy_proof(c: &NNRealConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (cv_id, cv) = b.fresh_local(c.nnrat.clone());
    let const_seq = const_seq_expr(c, &b, &cv);
    let vcv = c.val(cv.clone());

    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos_h) = b.fresh_local(hpos.clone());

    // pred_n := fun N => ∀ m n, N≤m → N≤n → bound_pair (val ((fun _ => cv) m))(val ((fun _ => cv) n)) ε.
    // `(fun _ => cv) m` reduces to `cv`, so the conclusion is bound_pair vcv vcv ε.
    let pred_n = {
        let mut bn = EnvDeclBuilder::child_of(&b);
        let (cap_id, cap) = bn.fresh_local(c.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(c.nat.clone());
            let (n_id, n) = bi.fresh_local(c.nat.clone());
            let hle_m = c.nat_le(cap.clone(), m.clone());
            let (hlem_id, _h) = bi.fresh_local(hle_m.clone());
            let hle_n = c.nat_le(cap.clone(), n.clone());
            let (hlen_id, _h2) = bi.fresh_local(hle_n.clone());
            let vm = c.val(c.raw_at(const_seq.clone(), m.clone()));
            let vn = c.val(c.raw_at(const_seq.clone(), n.clone()));
            let concl = c.bound_pair(vm, vn, eps.clone());
            let e = bi.mk_pi(hlen_id, BinderInfo::Default, hle_n, concl);
            let e = bi.mk_pi(hlem_id, BinderInfo::Default, hle_m, e);
            let e = bi.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };
        let lam = bn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner);
        bn.finish_child(lam)
    };

    // p : Rat.lt vcv (vcv+ε), from add_lt_add_left transported along add_zero.
    let v_plus_eps = c.add(vcv.clone(), eps.clone());
    let step = c.add_lt_add_left(c.rat_zero.clone(), eps.clone(), vcv.clone(), hpos_h.clone());
    let v_plus_zero = c.add(vcv.clone(), c.rat_zero.clone());
    let p = {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(t, v_plus_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst_rat(
            motive,
            v_plus_zero,
            vcv.clone(),
            c.add_zero(vcv.clone()),
            step,
        )
    };

    // witness over N := Nat.zero. Both conjuncts are vcv < vcv+ε.
    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, _m) = bw.fresh_local(c.nat.clone());
        let (n_id, _n) = bw.fresh_local(c.nat.clone());
        let hle_m = c.nat_le(
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
            _m.clone(),
        );
        let (hlem_id, _h) = bw.fresh_local(hle_m.clone());
        let hle_n = c.nat_le(
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
            _n.clone(),
        );
        let (hlen_id, _h2) = bw.fresh_local(hle_n.clone());
        let conj = c.lt(vcv.clone(), v_plus_eps.clone());
        let proof = c.and_intro(conj.clone(), conj, p.clone(), p.clone());
        let e = bw.mk_lam(hlen_id, BinderInfo::Default, hle_n, proof);
        let e = bw.mk_lam(hlem_id, BinderInfo::Default, hle_m, e);
        let e = bw.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
        bw.finish_child(e)
    };

    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let exists_term = Expr::apps(
        c.exists_intro.clone(),
        [c.nat.clone(), pred_n, nat_zero, witness],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos, exists_term);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.nnrat.clone(), e);
    b.finish(e)
}

/// Build the proof term for `NNReal.CauSeq.Equiv.symm`. Given the `f,g` bound,
/// the same `N` witnesses `Equiv g f`, with the two conjuncts swapped.
fn build_equiv_symm_proof(c: &NNRealConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.causeq.clone());
    let (g_id, g) = b.fresh_local(c.causeq.clone());
    let hyp_fg = c.equiv(f.clone(), g.clone());
    let (h_id, h) = b.fresh_local(hyp_fg.clone());

    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos_h) = b.fresh_local(hpos.clone());

    let h_applied = Expr::apps(h.clone(), [eps.clone(), hpos_h.clone()]);

    let pred_fg = |bb: &EnvDeclBuilder| -> Expr {
        let mut bn = EnvDeclBuilder::child_of(bb);
        let (n_id, n_cap) = bn.fresh_local(c.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(c.nat.clone());
            let hle = c.nat_le(n_cap.clone(), m.clone());
            let (hle_id, _hle) = bi.fresh_local(hle.clone());
            let concl = c.bound_pair(
                c.val(c.seq_at(f.clone(), m.clone())),
                c.val(c.seq_at(g.clone(), m.clone())),
                eps.clone(),
            );
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };
        let lam = bn.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner);
        bn.finish_child(lam)
    };
    let pred_gf = |bb: &EnvDeclBuilder| -> Expr {
        let mut bn = EnvDeclBuilder::child_of(bb);
        let (n_id, n_cap) = bn.fresh_local(c.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(c.nat.clone());
            let hle = c.nat_le(n_cap.clone(), m.clone());
            let (hle_id, _hle) = bi.fresh_local(hle.clone());
            let concl = c.bound_pair(
                c.val(c.seq_at(g.clone(), m.clone())),
                c.val(c.seq_at(f.clone(), m.clone())),
                eps.clone(),
            );
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };
        let lam = bn.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner);
        bn.finish_child(lam)
    };

    let pred_fg_e = pred_fg(&b);
    let pred_gf_e = pred_gf(&b);

    let exists_gf = Expr::apps(c.exists_c.clone(), [c.nat.clone(), pred_gf_e.clone()]);
    let exists_elim = Expr::const_(
        Name::from_string("Exists.elim"),
        vec![Level::succ(Level::zero())],
    );

    let elim_fn = {
        let mut be = EnvDeclBuilder::child_of(&b);
        let (cap_id, cap_n) = be.fresh_local(c.nat.clone());
        let hn_ty = {
            let mut bn = EnvDeclBuilder::child_of(&be);
            let (m_id, m) = bn.fresh_local(c.nat.clone());
            let hle = c.nat_le(cap_n.clone(), m.clone());
            let (hle_id, _hle) = bn.fresh_local(hle.clone());
            let concl = c.bound_pair(
                c.val(c.seq_at(f.clone(), m.clone())),
                c.val(c.seq_at(g.clone(), m.clone())),
                eps.clone(),
            );
            let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bn.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            bn.finish_child(e)
        };
        let (hn_id, hn) = be.fresh_local(hn_ty.clone());

        let repackaged = {
            let mut bp = EnvDeclBuilder::child_of(&be);
            let (m_id, m) = bp.fresh_local(c.nat.clone());
            let hle = c.nat_le(cap_n.clone(), m.clone());
            let (hle_id, hle_h) = bp.fresh_local(hle.clone());
            let vfm = c.val(c.seq_at(f.clone(), m.clone()));
            let vgm = c.val(c.seq_at(g.clone(), m.clone()));
            let l = c.lt(vfm.clone(), c.add(vgm.clone(), eps.clone()));
            let r = c.lt(vgm.clone(), c.add(vfm.clone(), eps.clone()));
            let base = Expr::apps(hn.clone(), [m.clone(), hle_h]);
            let hr = Expr::apps(c.and_right.clone(), [l.clone(), r.clone(), base.clone()]);
            let hl = Expr::apps(c.and_left.clone(), [l.clone(), r.clone(), base]);
            let proof = c.and_intro(r, l, hr, hl);
            let e = bp.mk_lam(hle_id, BinderInfo::Default, hle, proof);
            let e = bp.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            bp.finish_child(e)
        };

        let intro = Expr::apps(
            c.exists_intro.clone(),
            [c.nat.clone(), pred_gf_e.clone(), cap_n.clone(), repackaged],
        );
        let e = be.mk_lam(hn_id, BinderInfo::Default, hn_ty, intro);
        let e = be.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), e);
        be.finish_child(e)
    };

    let elim = Expr::apps(
        exists_elim,
        [c.nat.clone(), pred_fg_e, exists_gf, h_applied, elim_fn],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos, elim);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp_fg, e);
    let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const DEFS: &[&str] = &[
        "NNReal.IsCauchy",
        "NNReal.CauSeq",
        "NNReal.CauSeq.seq",
        "NNReal.CauSeq.mk",
        "NNReal.CauSeq.property",
        "NNReal.CauSeq.const",
        "NNReal.CauSeq.Equiv",
        "NNReal",
        "NNReal.mk",
        "NNReal.ofRat",
    ];

    const THEOREMS: &[&str] = &[
        "NNReal.IsCauchy.const_proof",
        "NNReal.CauSeq.Equiv.refl",
        "NNReal.CauSeq.Equiv.symm",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cauchy()
            .expect("init_algebra_nnreal_cauchy");
        env.init_algebra_nnreal_cauchy().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_cauchy_present_and_kernel_check() {
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
    fn test_nnreal_cauchy_theorems_constructive_empty_closure() {
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
