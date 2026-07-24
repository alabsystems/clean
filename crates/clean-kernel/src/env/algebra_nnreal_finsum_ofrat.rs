// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage C consumer bridge: `NNReal.finSum_ofRat`
//! (the `ofRat`/`finSum` commutation) + its `NNReal.ofRat_add` step lemma.
//!
//! # Why this module exists
//!
//! The sharp KKL charge consumer `Σ_i Inf_i^{3/2} ≤ ε^{1/2}·I[f]` assembles to
//! `NNReal.mul (sqrtRat ε) (NNReal.finSum n (fun i => NNReal.ofRat (Inf_i) _))`,
//! but the target RHS is `NNReal.mul (sqrtRat ε) (NNReal.ofRat (TotalInfluence
//! n f) _)`. The two `NNReal` factors agree iff the `NNReal.finSum` of the
//! coordinatewise `ofRat` embeddings equals the `ofRat` of the (monomorphic-
//! over-`Rat`) `Fin.sum`:
//!
//! ```text
//!   NNReal.finSum_ofRat :
//!     ∀ (n : Nat) (g : Fin n → Rat) (hg : ∀ i, Rat.le Rat.zero (g i))
//!       (hsum : Rat.le Rat.zero (Fin.sum n g)),
//!       NNReal.finSum n (fun i => NNReal.ofRat (g i) (hg i))
//!         = NNReal.ofRat (Fin.sum n g) hsum
//! ```
//!
//! Since `TotalInfluence n f ≡ Fin.sum n (fun i => Influence n f i)` (reducible
//! Definition), the consumer reads its RHS off this bridge by δ.
//!
//! # Proof shape (axiom-free)
//!
//! - **`NNReal.ofRat_add`** (the step lemma): `∀ a b (ha hb hab),
//!   NNReal.add (NNReal.ofRat a ha) (NNReal.ofRat b hb)
//!     = NNReal.ofRat (Rat.add a b) hab`. Both sides are `NNReal.mk = Quot.mk`:
//!   the LHS ι-reduces (nested binary `Quot.lift`) to
//!   `Quot.mk (CauSeq.add (const (NNRat.ofRat a))(const (NNRat.ofRat b)))`, the
//!   RHS is `Quot.mk (const (NNRat.ofRat (a+b)))`, so the goal is `Quot.sound`
//!   on the dist-free two-sided `Equiv`. Its leaf at index `m` is
//!   `val(seq(add (const A)(const B)) m) = val(seq(const C) m)`, both of which
//!   ι-reduce DEFINITIONALLY to `a + b` (`val(NNRat.add A B) ≡ val A + val B ≡
//!   a + b` via the `Subtype`/`NNRat.add` projections, and `val C ≡ a + b` via
//!   the `NNRat.ofRat` projection). So `h_eq` is `Eq.refl (a+b)` and the two
//!   strict bounds are `v < v + ε` — exactly the `NNReal.mul_zero` Equiv
//!   pattern, minus the `congrArg` (the leaf is already refl here).
//! - **`NNReal.finSum_ofRat`**: `Nat.rec.{0}` over `n` (Prop motive
//!   `fun k => ∀ g hg hsum, finSum k (ofRat∘g) = ofRat (Fin.sum k g)`).
//!   - BASE `k=0`: `finSum 0 _ ≡ NNReal.zero ≡ NNReal.ofRat 0 _`, and
//!     `Fin.sum 0 g ≡ Rat.zero`, so `ofRat (Fin.sum 0 g) hsum ≡ NNReal.ofRat 0 _
//!     ≡ NNReal.zero` (proof-irrelevance on the `0≤0` witnesses), closed by
//!     `Eq.refl NNReal.zero`.
//!   - STEP `k=succ j`: `finSum (j+1) (ofRat∘g) ≡ NNReal.add (finSum j
//!     ((ofRat∘g)∘castSucc)) (ofRat (g (last j)))` (Nat.rec step ι) and
//!     `(ofRat∘g)∘castSucc ≡ ofRat∘(g∘castSucc)` (defeq); the IH at `g∘castSucc`
//!     rewrites the prefix to `ofRat (Fin.sum j (g∘castSucc))`; then
//!     `NNReal.ofRat_add` folds `add (ofRat P)(ofRat L) = ofRat (P + L)`; and
//!     `Fin.sum (j+1) g ≡ Rat.add (Fin.sum j (g∘castSucc)) (g (last j))` (the
//!     on-main `Fin.sum_succ`, defeq) reconciles the RHS by proof-irrelevance.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the `ofRat`/`finSum` bridge.
pub(crate) struct FinSumOfRatConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_add: Expr,
    rat_add_lt_add_left: Expr,
    rat_add_zero: Expr,
    fin: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    fin_sum: Expr,
    fin_sum_nonneg: Expr,
    nnrat_val: Expr,
    nnrat_of_rat: Expr,
    nnreal: Expr,
    nnreal_zero: Expr,
    nnreal_add: Expr,
    nnreal_of_rat: Expr,
    nnreal_finsum: Expr,
    nnreal_of_rat_add: Expr,
    // carrier internals (for the ofRat_add Quot.sound).
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_add: Expr,
    causeq_const: Expr,
    nat_le: Expr,
    nat_rec0: Expr,
    // logic.
    eq1: Expr,
    eq_refl1: Expr,
    eq_subst1: Expr,
    eq_symm1: Expr,
    exists_intro: Expr,
    and_c: Expr,
    and_intro: Expr,
    quot_sound: Expr,
}

impl FinSumOfRatConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_add: k("Rat.add"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_add_zero: k("Rat.add_zero"),
            fin: k("Fin"),
            fin_cast_succ: k("Fin.castSucc"),
            fin_last: k("Fin.last"),
            fin_sum: k("Fin.sum"),
            fin_sum_nonneg: k("Fin.sum_nonneg"),
            nnrat_val: k("NNRat.val"),
            nnrat_of_rat: k("NNRat.ofRat"),
            nnreal: k("NNReal"),
            nnreal_zero: k("NNReal.zero"),
            nnreal_add: k("NNReal.add"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_finsum: k("NNReal.finSum"),
            nnreal_of_rat_add: k("NNReal.ofRat_add"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_add: k("NNReal.CauSeq.add"),
            causeq_const: k("NNReal.CauSeq.const"),
            nat_le: k("Nat.le"),
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            and_c: k("And"),
            and_intro: k("And.intro"),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![l1]),
        }
    }

    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    /// `NNReal.ofRat x h : NNReal`.
    fn of_rat(&self, x: Expr, h: Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x, h])
    }
    /// `NNReal.add a b : NNReal`.
    fn nnadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a, b])
    }
    /// `NNReal.finSum n f : NNReal`.
    fn finsum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.nnreal_finsum.clone(), [n, f])
    }
    /// `Fin.sum n g : Rat`.
    fn fin_sum(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, g])
    }
    /// `@Eq.{1} NNReal a b`.
    fn eq_nnreal(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nnreal.clone(), a, b])
    }
    /// `@Eq.refl.{1} NNReal a`.
    fn refl_nnreal(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.nnreal.clone(), a])
    }
    /// `@Eq.refl.{1} Rat a`.
    fn refl_rat(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), a])
    }
    /// `@Eq.symm.{1} Rat a b h : Eq Rat b a`.
    fn eq_symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    /// `@Eq.symm.{1} NNReal a b h : Eq NNReal b a`.
    fn eq_symm_nnreal(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.nnreal.clone(), a, b, h])
    }
    /// `@Eq.subst.{1} NNReal motive a b h_eq h : motive b`.
    fn subst_nnreal(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `Rat.add_lt_add_left a b c h : (c+a) < (c+b)`.
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    /// `Rat.add_zero a : Eq Rat (a+0) a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `fun (i : Fin n) => g (Fin.castSucc n i)` — the cast prefix (Rat-valued).
    fn cast_prefix(&self, parent: &EnvDeclBuilder, n: Expr, g: Expr) -> Expr {
        let fin_n = self.fin_of(&n);
        let mut b = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let cast_i = Expr::app(Expr::app(self.fin_cast_succ.clone(), n), i);
        let body = Expr::app(g, cast_i);
        let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
        b.finish_child(lam)
    }
}

impl Environment {
    /// Register `NNReal.ofRat_add` and `NNReal.finSum_ofRat`. Idempotent.
    pub fn init_algebra_nnreal_finsum_ofrat(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_finsum()?; // NNReal.zero, NNReal.finSum (+ carrier, ofRat)
        self.init_fin_sum()?; // Fin.sum (+ Fin.sum_succ defeq carrier), Fin.castSucc/last, Fin.sum_nonneg
        self.init_rat_field_inst()?; // Rat.add_zero
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.init_eq()?;

        let c = FinSumOfRatConsts::new();
        self.register_nnreal_ofrat_add(&c)?;
        self.register_nnreal_finsum_ofrat(&c)?;
        Ok(())
    }

    /// `NNReal.ofRat_add : ∀ (a b : Rat) (ha : 0≤a)(hb : 0≤b)(hab : 0≤a+b),
    ///     NNReal.add (NNReal.ofRat a ha)(NNReal.ofRat b hb)
    ///       = NNReal.ofRat (Rat.add a b) hab`.
    fn register_nnreal_ofrat_add(&mut self, c: &FinSumOfRatConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.ofRat_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bb_id, bb) = b.fresh_local(c.rat.clone());
            let ha_ty = c.rle(c.rat_zero.clone(), a.clone());
            let (ha_id, ha) = b.fresh_local(ha_ty.clone());
            let hb_ty = c.rle(c.rat_zero.clone(), bb.clone());
            let (hb_id, hb) = b.fresh_local(hb_ty.clone());
            let hab_ty = c.rle(c.rat_zero.clone(), c.radd(a.clone(), bb.clone()));
            let (hab_id, hab) = b.fresh_local(hab_ty.clone());

            let lhs = c.nnadd(c.of_rat(a.clone(), ha), c.of_rat(bb.clone(), hb));
            let rhs = c.of_rat(c.radd(a.clone(), bb.clone()), hab);
            let concl = c.eq_nnreal(lhs, rhs);

            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_ty, concl);
            let e = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, e);
            let e = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_pi(bb_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bb_id, bb) = b.fresh_local(c.rat.clone());
            let ha_ty = c.rle(c.rat_zero.clone(), a.clone());
            let (ha_id, ha) = b.fresh_local(ha_ty.clone());
            let hb_ty = c.rle(c.rat_zero.clone(), bb.clone());
            let (hb_id, hb) = b.fresh_local(hb_ty.clone());
            let hab_ty = c.rle(c.rat_zero.clone(), c.radd(a.clone(), bb.clone()));
            let (hab_id, hab) = b.fresh_local(hab_ty.clone());

            // The two raw CauSeqs whose Quot.mk the two goal sides ι-reduce to:
            //   cl = CauSeq.add (const (NNRat.ofRat a ha))(const (NNRat.ofRat b hb))
            //   cr = const (NNRat.ofRat (a+b) hab)
            let nn_a = Expr::apps(c.nnrat_of_rat.clone(), [a.clone(), ha]);
            let nn_b = Expr::apps(c.nnrat_of_rat.clone(), [bb.clone(), hb]);
            let ab = c.radd(a.clone(), bb.clone());
            let nn_ab = Expr::apps(c.nnrat_of_rat.clone(), [ab, hab]);
            let const_a = Expr::app(c.causeq_const.clone(), nn_a);
            let const_b = Expr::app(c.causeq_const.clone(), nn_b);
            let cl = Expr::apps(c.causeq_add.clone(), [const_a, const_b]);
            let cr = Expr::app(c.causeq_const.clone(), nn_ab);

            let equiv = build_ofrat_add_equiv(c, &b, &cl, &cr);
            let sound = Expr::apps(
                c.quot_sound.clone(),
                [c.causeq.clone(), c.causeq_equiv.clone(), cl, cr, equiv],
            );

            let e = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, sound);
            let e = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, e);
            let e = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, e);
            let e = b.mk_lam(bb_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.finSum_ofRat`. `Nat.rec.{0}` over `n`. See module docs.
    fn register_nnreal_finsum_ofrat(&mut self, c: &FinSumOfRatConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.finSum_ofRat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = build_finsum_ofrat_type(c);
        let value = build_finsum_ofrat_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `∀ (n : Nat)(g : Fin n → Rat)(hg : ∀ i, 0≤g i)(hsum : 0≤Fin.sum n g),
///     NNReal.finSum n (fun i => NNReal.ofRat (g i)(hg i))
///       = NNReal.ofRat (Fin.sum n g) hsum`.
fn build_finsum_ofrat_type(c: &FinSumOfRatConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_type = c.fin_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_type.clone());
    let hg = pointwise_nonneg(c, &b, &n, &g);
    let (hg_id, hg_h) = b.fresh_local(hg.clone());
    let hsum_ty = c.rle(c.rat_zero.clone(), c.fin_sum(n.clone(), g.clone()));
    let (hsum_id, hsum) = b.fresh_local(hsum_ty.clone());

    let lhs = c.finsum(n.clone(), ofrat_fn(c, &b, &n, &g, &hg_h));
    let rhs = c.of_rat(c.fin_sum(n.clone(), g.clone()), hsum);
    let concl = c.eq_nnreal(lhs, rhs);

    let e = b.mk_pi(hsum_id, BinderInfo::Default, hsum_ty, concl);
    let e = b.mk_pi(hg_id, BinderInfo::Default, hg, e);
    let e = b.mk_pi(g_id, BinderInfo::Default, g_type, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `∀ (i : Fin n), Rat.le Rat.zero (g i)`.
fn pointwise_nonneg(c: &FinSumOfRatConsts, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
    let fin_n = c.fin_of(n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.rle(c.rat_zero.clone(), Expr::app(g.clone(), i));
    let pi = b.mk_pi(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(pi)
}

/// `fun (i : Fin n) => NNReal.ofRat (g i)(hg i)` — the coordinatewise embedding.
fn ofrat_fn(c: &FinSumOfRatConsts, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, hg: &Expr) -> Expr {
    let fin_n = c.fin_of(n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let gi = Expr::app(g.clone(), i.clone());
    let hgi = Expr::app(hg.clone(), i);
    let body = c.of_rat(gi, hgi);
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(lam)
}

/// Motive: `fun k => ∀ g hg hsum, finSum k (ofRat∘g) = ofRat (Fin.sum k g)`.
fn build_finsum_ofrat_motive(c: &FinSumOfRatConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let g_type = c.fin_to_rat(&k);
    let (g_id, g) = b.fresh_local(g_type.clone());
    let hg = pointwise_nonneg(c, &b, &k, &g);
    let (hg_id, hg_h) = b.fresh_local(hg.clone());
    let hsum_ty = c.rle(c.rat_zero.clone(), c.fin_sum(k.clone(), g.clone()));
    let (hsum_id, hsum) = b.fresh_local(hsum_ty.clone());

    let lhs = c.finsum(k.clone(), ofrat_fn(c, &b, &k, &g, &hg_h));
    let rhs = c.of_rat(c.fin_sum(k.clone(), g.clone()), hsum);
    let body = c.eq_nnreal(lhs, rhs);

    let e = b.mk_pi(hsum_id, BinderInfo::Default, hsum_ty, body);
    let e = b.mk_pi(hg_id, BinderInfo::Default, hg, e);
    let e = b.mk_pi(g_id, BinderInfo::Default, g_type, e);
    let lam = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(lam)
}

/// Base case `motive 0`: `fun g hg hsum => Eq.refl NNReal.zero`.
/// `finSum 0 (ofRat∘g) ≡ NNReal.zero` and `ofRat (Fin.sum 0 g) hsum ≡
/// ofRat 0 _ ≡ NNReal.zero` (proof-irrelevance), so the goal is `Eq.refl`.
fn build_finsum_ofrat_base(c: &FinSumOfRatConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let g_type = c.fin_to_rat(&c.nat_zero.clone());
    let (g_id, g) = b.fresh_local(g_type.clone());
    let hg = pointwise_nonneg(c, &b, &c.nat_zero.clone(), &g);
    let (hg_id, _hg) = b.fresh_local(hg.clone());
    let hsum_ty = c.rle(c.rat_zero.clone(), c.fin_sum(c.nat_zero.clone(), g.clone()));
    let (hsum_id, _hsum) = b.fresh_local(hsum_ty.clone());

    let proof = c.refl_nnreal(c.nnreal_zero.clone());
    let val = b.mk_lam(hsum_id, BinderInfo::Default, hsum_ty, proof);
    let val = b.mk_lam(hg_id, BinderInfo::Default, hg, val);
    let val = b.mk_lam(g_id, BinderInfo::Default, g_type, val);
    b.finish(val)
}

/// Step case `motive j → motive (j+1)`.
fn build_finsum_ofrat_step(c: &FinSumOfRatConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (j_id, j) = b.fresh_local(c.nat.clone());

    // IH : ∀ g hg hsum, finSum j (ofRat∘g) = ofRat (Fin.sum j g) hsum.
    let ih_type = {
        let mut ib = EnvDeclBuilder::child_of(&b);
        let g_type = c.fin_to_rat(&j);
        let (g_id, g) = ib.fresh_local(g_type.clone());
        let hg = pointwise_nonneg(c, &ib, &j, &g);
        let (hg_id, hg_h) = ib.fresh_local(hg.clone());
        let hsum_ty = c.rle(c.rat_zero.clone(), c.fin_sum(j.clone(), g.clone()));
        let (hsum_id, hsum) = ib.fresh_local(hsum_ty.clone());
        let lhs = c.finsum(j.clone(), ofrat_fn(c, &ib, &j, &g, &hg_h));
        let rhs = c.of_rat(c.fin_sum(j.clone(), g.clone()), hsum);
        let concl = c.eq_nnreal(lhs, rhs);
        let e = ib.mk_pi(hsum_id, BinderInfo::Default, hsum_ty, concl);
        let e = ib.mk_pi(hg_id, BinderInfo::Default, hg, e);
        let e = ib.mk_pi(g_id, BinderInfo::Default, g_type, e);
        ib.finish_child(e)
    };
    let (ih_id, ih) = b.fresh_local(ih_type.clone());

    let succ_j = Expr::app(c.nat_succ.clone(), j.clone());
    let g_type = c.fin_to_rat(&succ_j);
    let (g_id, g) = b.fresh_local(g_type.clone());
    let hg = pointwise_nonneg(c, &b, &succ_j, &g);
    let (hg_id, hg_h) = b.fresh_local(hg.clone());
    let hsum_ty = c.rle(c.rat_zero.clone(), c.fin_sum(succ_j.clone(), g.clone()));
    let (hsum_id, hsum) = b.fresh_local(hsum_ty.clone());

    // g_cast := fun i : Fin j => g (Fin.castSucc j i) : Fin j → Rat.
    let g_cast = c.cast_prefix(&b, j.clone(), g.clone());
    // hg_cast := fun i : Fin j => hg (Fin.castSucc j i) : ∀ i, 0 ≤ g_cast i.
    let hg_cast = {
        let fin_j = c.fin_of(&j);
        let mut hb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = hb.fresh_local(fin_j.clone());
        let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), j.clone()), i);
        let body = Expr::app(hg_h.clone(), cast_i);
        let lam = hb.mk_lam(i_id, BinderInfo::Default, fin_j, body);
        hb.finish_child(lam)
    };

    // The prefix Rat sum `P := Fin.sum j g_cast` and last `L := g (Fin.last j)`.
    let last_j = Expr::app(c.fin_last.clone(), j.clone());
    let g_last = Expr::app(g.clone(), last_j.clone());
    let prefix_sum = c.fin_sum(j.clone(), g_cast.clone());
    // hg_last := hg (Fin.last j) : 0 ≤ L.
    let hg_last = Expr::app(hg_h.clone(), last_j.clone());

    // hP : 0 ≤ P — needed for `ofRat P`. Via Fin.sum_nonneg j g_cast hg_cast.
    let hp = Expr::apps(
        c.fin_sum_nonneg.clone(),
        [j.clone(), g_cast.clone(), hg_cast.clone()],
    );

    // step1 (IH): finSum j (ofRat∘g_cast) = ofRat P hP.
    let ih_app = Expr::apps(ih, [g_cast.clone(), hg_cast, hp.clone()]);
    let prefix_nn_lhs = c.finsum(
        j.clone(),
        ofrat_fn(c, &b, &j, &g_cast, &hg_h_cast_dummy(c, &b, &j, &hg_h)),
    );
    let prefix_nn_rhs = c.of_rat(prefix_sum.clone(), hp.clone());
    let last_nn = c.of_rat(g_last.clone(), hg_last.clone());

    // motive_step1 : fun t => Eq NNReal (NNReal.add t (ofRat L)) RHS_target.
    let motive_step1 = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.nnreal.clone());
        let add_t = c.nnadd(t, last_nn.clone());
        let rhs_target = c.of_rat(c.fin_sum(succ_j.clone(), g.clone()), hsum.clone());
        let body = c.eq_nnreal(add_t, rhs_target);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };

    // inner : Eq NNReal (NNReal.add (ofRat P hP)(ofRat L)) (ofRat (Fin.sum (j+1) g) hsum).
    //   `Fin.sum (j+1) g ≡ Rat.add P L` (Fin.sum_succ defeq), so the goal RHS is
    //   defeq to `ofRat (Rat.add P L) hsum`. NNReal.ofRat_add P L hP (hg L) hsum
    //   gives `add (ofRat P)(ofRat L) = ofRat (Rat.add P L) hsum`.
    let inner = Expr::apps(
        c.nnreal_of_rat_add.clone(),
        [
            prefix_sum.clone(),
            g_last.clone(),
            hp.clone(),
            hg_last.clone(),
            hsum.clone(),
        ],
    );

    // proof : rewrite `ofRat P hP` BACK to `finSum j (ofRat∘g_cast)` (= the
    // Nat.rec-reduced LHS prefix) via Eq.subst along (Eq.symm step1).
    let step1_symm = c.eq_symm_nnreal(prefix_nn_lhs.clone(), prefix_nn_rhs.clone(), ih_app);
    let proof = c.subst_nnreal(
        motive_step1,
        prefix_nn_rhs,
        prefix_nn_lhs,
        step1_symm,
        inner,
    );

    let val = b.mk_lam(hsum_id, BinderInfo::Default, hsum_ty, proof);
    let val = b.mk_lam(hg_id, BinderInfo::Default, hg, val);
    let val = b.mk_lam(g_id, BinderInfo::Default, g_type, val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_type, val);
    let val = b.mk_lam(j_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

/// `hg_cast := fun i : Fin j => hg (Fin.castSucc j i)` — re-built for the
/// LHS `ofRat∘g_cast` summand-function (the prefix `finSum` argument). It is
/// definitionally the same nonnegativity proof family used in `hg_cast` above;
/// re-derived here to live in the right `parent` scope.
fn hg_h_cast_dummy(c: &FinSumOfRatConsts, parent: &EnvDeclBuilder, j: &Expr, hg_h: &Expr) -> Expr {
    let fin_j = c.fin_of(j);
    let mut hb = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = hb.fresh_local(fin_j.clone());
    let cast_i = Expr::app(Expr::app(c.fin_cast_succ.clone(), j.clone()), i);
    let body = Expr::app(hg_h.clone(), cast_i);
    let lam = hb.mk_lam(i_id, BinderInfo::Default, fin_j, body);
    hb.finish_child(lam)
}

/// `NNReal.finSum_ofRat := fun n => Nat.rec.{0} motive base step n`.
fn build_finsum_ofrat_value(c: &FinSumOfRatConsts) -> Expr {
    let motive = build_finsum_ofrat_motive(c);
    let base = build_finsum_ofrat_base(c);
    let step = build_finsum_ofrat_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = Expr::apps(c.nat_rec0.clone(), [motive, base, step, n]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
    b.finish(val)
}

// ── NNReal.ofRat_add — the Quot.sound Equiv ──────────────────────────────────

/// Build `Equiv cl cr` where the two CauSeqs are pointwise-equal at every index
/// (both `val(seq · m)` ι-reduce to `a+b`). The leaf `h_eq : vL = vR` is
/// `Eq.refl (a+b)` (both sides defeq to `a+b`); the strict bounds are `v < v+ε`.
fn build_ofrat_add_equiv(
    c: &FinSumOfRatConsts,
    parent: &EnvDeclBuilder,
    cl: &Expr,
    cr: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.rlt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    // val(seq x m) helper.
    let vseq = |x: &Expr, m: &Expr| -> Expr {
        let seq_xm = Expr::app(Expr::app(c.causeq_seq.clone(), x.clone()), m.clone());
        Expr::app(c.nnrat_val.clone(), seq_xm)
    };

    let pred = {
        let mut bn = EnvDeclBuilder::child_of(&b);
        let (cap_id, cap) = bn.fresh_local(c.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(c.nat.clone());
            let hle = c.nat_le(cap.clone(), m.clone());
            let (hle_id, _h) = bi.fresh_local(hle.clone());
            let vl = vseq(cl, &m);
            let vr = vseq(cr, &m);
            let left = c.rlt(vl.clone(), c.radd(vr.clone(), eps.clone()));
            let right = c.rlt(vr.clone(), c.radd(vl.clone(), eps.clone()));
            let concl = Expr::apps(c.and_c.clone(), [left, right]);
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };
        bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner))
    };

    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(c.nat_zero.clone(), m.clone());
        let (hle_id, _hle) = bw.fresh_local(hle_ty.clone());

        let vl = vseq(cl, &m);
        let vr = vseq(cr, &m);
        // h_eq : vL = vR. Both reduce defeq to `a+b`, so Eq.refl at vL.
        let h_eq = c.refl_rat(vl.clone());

        let vr_eps = c.radd(vr.clone(), eps.clone());
        let vl_eps = c.radd(vl.clone(), eps.clone());
        let vr_lt = self_lt_add(c, &bw, &vr, &eps, &hpos);
        let vl_lt = self_lt_add(c, &bw, &vl, &eps, &hpos);

        // left : vL < vR + ε  — from vR < vR+ε, subst vR → vL via symm h_eq.
        let motive_l = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.rlt(t, vr_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_eq_symm = c.eq_symm_rat(vl.clone(), vr.clone(), h_eq.clone());
        let left = c.subst_rat(motive_l, vr.clone(), vl.clone(), h_eq_symm, vr_lt);

        // right : vR < vL + ε — from vL < vL+ε, subst vL → vR via h_eq.
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

/// `v < v + ε` from `0 < ε` (`add_lt_add_left 0 ε v` + `add_zero` transport).
fn self_lt_add(
    c: &FinSumOfRatConsts,
    parent: &EnvDeclBuilder,
    v: &Expr,
    eps: &Expr,
    hpos: &Expr,
) -> Expr {
    let h = c.add_lt_add_left(c.rat_zero.clone(), eps.clone(), v.clone(), hpos.clone());
    let v_zero = c.radd(v.clone(), c.rat_zero.clone());
    let v_eps = c.radd(v.clone(), eps.clone());
    let e_az = c.add_zero(v.clone());
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(c.rat.clone());
        let body = c.rlt(t, v_eps.clone());
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst_rat(motive, v_zero, v.clone(), e_az, h)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.ofRat_add", "NNReal.finSum_ofRat"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_finsum_ofrat()
            .expect("init_algebra_nnreal_finsum_ofrat");
        env.init_algebra_nnreal_finsum_ofrat().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_finsum_ofrat_kernel_check() {
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
    fn test_nnreal_finsum_ofrat_constructive_empty_closure() {
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
