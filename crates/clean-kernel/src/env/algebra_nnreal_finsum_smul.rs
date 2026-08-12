// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component B, target 4: the SCALAR-PULL
//! `NNReal.finSum_smul` (+ the base-case helper `NNReal.mul_zero`).
//!
//! # Why this module exists
//!
//! The KKL charge derivation pulls the constant `ε^{1/2}` out of the summed
//! per-coordinate bound: `Σ_i ε^{1/2}·Inf_i = ε^{1/2}·Σ_i Inf_i = ε^{1/2}·I[f]`.
//! The scalar-pull over the `NNReal`-valued `Fin.sum` is:
//!
//! - `NNReal.finSum_smul : ∀ (n : Nat) (c : NNReal) (f : Fin n → NNReal),
//!       NNReal.finSum n (fun i => NNReal.mul c (f i)) =
//!       NNReal.mul c (NNReal.finSum n f)`.
//!
//! # Proof shape (axiom-free)
//!
//! `Nat.rec.{0}` over `n` (Prop motive
//! `fun k => ∀ c f, finSum k (scaled c f) = mul c (finSum k f)`), mirroring the
//! on-main `Fin.sum_smul`:
//! - BASE `n=0`: both `finSum 0 _ ≡ NNReal.zero`; the goal `NNReal.zero =
//!   NNReal.mul c NNReal.zero` is `Eq.symm (NNReal.mul_zero c)`.
//! - STEP `n=k+1`: `finSum (k+1) g ≡ NNReal.add (finSum k (g∘castSucc))
//!   (g (last k))` (Nat.rec step ι). The scaled function commutes with the cast
//!   prefix (`(scaled c f)∘castSucc ≡ scaled c (f∘castSucc)` defeq), so the IH at
//!   `(c, f∘castSucc)` rewrites the prefix; `NNReal.mul_add` then refactors
//!   `mul c P + mul c L` back into `mul c (P + L) = mul c (finSum (k+1) f)`.
//!
//! Supporting:
//! - `NNRat.mul_zero : ∀ c, NNRat.mul c NNRat.zero = NNRat.zero` (via
//!   `NNRat.eq_of_val_eq` on `vc·0 = 0` = `Rat.mul_zero`).
//! - `NNReal.mul_zero : ∀ c, NNReal.mul c NNReal.zero = NNReal.zero` (`Quot.ind`
//!   on `c` + `Quot.sound` on the pointwise-`NNRat.mul_zero` `Equiv`).
//!
//! Each is `Declaration::Theorem`, `ProofQuality::Constructive`, with empty
//! admitted-axiom closure (foundational only). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`.

use super::algebra_nnreal_finsum::NNFinSumConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNReal.finSum_smul`.
pub(crate) struct FinSumSmulConsts {
    base: NNFinSumConsts,
    nat_rec0: Expr,
    nnreal_mul: Expr,
    nnreal_mul_zero: Expr,
    nnreal_mul_add: Expr,
    // Eq.{1} over NNReal.
    eq_trans1: Expr,
    eq_symm1: Expr,
    congr_arg: Expr,
}

impl FinSumSmulConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            base: NNFinSumConsts::new(),
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nnreal_mul: k("NNReal.mul"),
            nnreal_mul_zero: k("NNReal.mul_zero"),
            nnreal_mul_add: k("NNReal.mul_add"),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]),
        }
    }

    fn nat(&self) -> Expr {
        self.base.nat.clone()
    }
    fn nnreal(&self) -> Expr {
        self.base.nnreal.clone()
    }
    fn fin_to_nnreal(&self, n: Expr) -> Expr {
        self.base.fin_to_nnreal(n)
    }
    fn sum(&self, n: Expr, f: Expr) -> Expr {
        self.base.sum(n, f)
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        self.base.add(a, b)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a, b])
    }
    /// `@Eq.{1} NNReal a b`.
    fn eq_nnreal(&self, a: Expr, b: Expr) -> Expr {
        self.base.eq_nnreal(a, b)
    }
    fn eq_trans(&self, a: Expr, b: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.nnreal(), a, b, d, h1, h2])
    }
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.nnreal(), a, b, h])
    }
    /// `@congrArg NNReal NNReal a b g h : g a = g b`.
    fn congr_nnreal(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nnreal(), self.nnreal(), a, b, g, h],
        )
    }

    /// `fun (i : Fin n) => NNReal.mul c (f i)` — the scaled summand function.
    fn scaled_fn(&self, parent: &EnvDeclBuilder, n: Expr, c: Expr, f: Expr) -> Expr {
        let fin_n = Expr::app(self.base.fin.clone(), n);
        let mut b = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.mul(c, Expr::app(f, i));
        let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
        b.finish_child(lam)
    }

    /// `fun (x : NNReal) => NNReal.add x right` — congrArg the left summand.
    fn add_right_fn(&self, parent: &EnvDeclBuilder, right: Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = b.fresh_local(self.nnreal());
        let body = self.add(x, right);
        let lam = b.mk_lam(x_id, BinderInfo::Default, self.nnreal(), body);
        b.finish_child(lam)
    }
}

impl Environment {
    /// Register `NNRat.mul_zero`, `NNReal.mul_zero`, `NNReal.finSum_smul`.
    /// Idempotent.
    pub fn init_algebra_nnreal_finsum_smul(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_finsum()?; // NNReal.zero, NNReal.finSum
        self.init_algebra_nnreal_mul_distrib()?; // NNReal.mul_add, NNRat.eq_of_val_eq
        self.init_rat()?; // Rat.mul_zero (constructive Rat-quotient theorem)

        self.register_nnrat_mul_zero()?;
        self.register_nnreal_mul_zero()?;

        let name = Name::from_string("NNReal.finSum_smul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = FinSumSmulConsts::new();
        let ty = build_smul_type(&c);
        let value = build_smul_value(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNRat.mul_zero : ∀ c, NNRat.mul c NNRat.zero = NNRat.zero`.
    /// Via `NNRat.eq_of_val_eq` on `vc·0 = 0` (`Rat.mul_zero vc`).
    fn register_nnrat_mul_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNRat.mul_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let lvl1 = Level::succ(Level::zero());
        let nnrat = Expr::const_(Name::from_string("NNRat"), vec![]);
        let nnrat_zero = Expr::const_(Name::from_string("NNRat.zero"), vec![]);
        let nnrat_mul = Expr::const_(Name::from_string("NNRat.mul"), vec![]);
        let nnrat_val = Expr::const_(Name::from_string("NNRat.val"), vec![]);
        let eq_of_val_eq = Expr::const_(Name::from_string("NNRat.eq_of_val_eq"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_mul_zero = Expr::const_(Name::from_string("Rat.mul_zero"), vec![]);
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]);
        let nnval = |q: Expr| Expr::app(nnrat_val.clone(), q);
        let eq_nnrat = |a: Expr, b: Expr| Expr::apps(eq1.clone(), [nnrat.clone(), a, b]);
        let _ = (&rat, &rat_zero, &rat_mul);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(nnrat.clone());
            let lhs = Expr::apps(nnrat_mul.clone(), [c.clone(), nnrat_zero.clone()]);
            let concl = eq_nnrat(lhs, nnrat_zero.clone());
            let e = b.mk_pi(c_id, BinderInfo::Default, nnrat.clone(), concl);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(nnrat.clone());
            let lhs = Expr::apps(nnrat_mul.clone(), [c.clone(), nnrat_zero.clone()]);
            let vc = nnval(c.clone());
            // val(mul c zero) ≡ vc·val(zero) ≡ vc·0 (NNRat.zero.val ≡ 0); and
            // val(NNRat.zero) ≡ 0. So the val-equality is `Rat.mul_zero vc`,
            // typed `vc·0 = 0`, which is DEFEQ to `val(mul c zero) = val(zero)`.
            let hval = Expr::app(rat_mul_zero.clone(), vc); // vc·0 = 0
            let body = Expr::apps(eq_of_val_eq, [lhs, nnrat_zero.clone(), hval]);
            let e = b.mk_lam(c_id, BinderInfo::Default, nnrat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.mul_zero : ∀ c, NNReal.mul c NNReal.zero = NNReal.zero`.
    /// `Quot.ind` on `c` + `Quot.sound` on the pointwise-`NNRat.mul_zero`
    /// `Equiv (CauSeq.mul fc (const (NNRat.ofRat 0 _)))(const (NNRat.ofRat 0 _))`.
    fn register_nnreal_mul_zero(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.mul_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = MulZeroConsts::new();
        let nnreal = c.nnreal();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cv_id, cv) = b.fresh_local(nnreal.clone());
            let lhs = c.nnreal_mul(cv.clone(), c.nnreal_zero.clone());
            let concl = c.eq_nnreal(lhs, c.nnreal_zero.clone());
            let e = b.mk_pi(cv_id, BinderInfo::Default, nnreal.clone(), concl);
            b.finish(e)
        };
        let value = build_mul_zero_value(&c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `∀ (n : Nat)(c : NNReal)(f : Fin n → NNReal),
///     NNReal.finSum n (scaled c f) = NNReal.mul c (NNReal.finSum n f)`.
fn build_smul_type(c: &FinSumSmulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat());
    let (cv_id, cv) = b.fresh_local(c.nnreal());
    let f_type = c.fin_to_nnreal(n.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let lhs = c.sum(n.clone(), c.scaled_fn(&b, n.clone(), cv.clone(), f.clone()));
    let rhs = c.mul(cv.clone(), c.sum(n.clone(), f));
    let concl = c.eq_nnreal(lhs, rhs);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_type, concl);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.nnreal(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat(), e);
    b.finish(e)
}

/// Motive: `fun k => ∀ c f, finSum k (scaled c f) = mul c (finSum k f)`.
fn build_smul_motive(c: &FinSumSmulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat());
    let (cv_id, cv) = b.fresh_local(c.nnreal());
    let f_type = c.fin_to_nnreal(k.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let lhs = c.sum(k.clone(), c.scaled_fn(&b, k.clone(), cv.clone(), f.clone()));
    let rhs = c.mul(cv.clone(), c.sum(k.clone(), f));
    let body = c.eq_nnreal(lhs, rhs);
    let pi_f = b.mk_pi(f_id, BinderInfo::Default, f_type, body);
    let pi_c = b.mk_pi(cv_id, BinderInfo::Default, c.nnreal(), pi_f);
    let lam = b.mk_lam(k_id, BinderInfo::Default, c.nat(), pi_c);
    b.finish(lam)
}

/// Base case `motive 0`: `fun c f => Eq.symm (NNReal.mul_zero c)` at
/// `NNReal.zero = NNReal.mul c NNReal.zero`.
fn build_smul_base(c: &FinSumSmulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (cv_id, cv) = b.fresh_local(c.nnreal());
    let f_type = c.fin_to_nnreal(c.base.nat_zero.clone());
    let (f_id, _f) = b.fresh_local(f_type.clone());
    let mul_c_zero = c.mul(cv.clone(), c.base.nnreal_zero.clone());
    // NNReal.mul_zero c : NNReal.mul c NNReal.zero = NNReal.zero.
    let h = Expr::app(c.nnreal_mul_zero.clone(), cv.clone());
    // Eq.symm : NNReal.zero = NNReal.mul c NNReal.zero.
    let proof = c.eq_symm(mul_c_zero, c.base.nnreal_zero.clone(), h);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_type, proof);
    let val = b.mk_lam(cv_id, BinderInfo::Default, c.nnreal(), val);
    b.finish(val)
}

/// Step case `motive k → motive (k+1)`.
fn build_smul_step(c: &FinSumSmulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat());

    // IH : ∀ c f, finSum k (scaled c f) = mul c (finSum k f).
    let ih_type = {
        let mut bb = EnvDeclBuilder::child_of(&b);
        let (cv_id, cv) = bb.fresh_local(c.nnreal());
        let f_type = c.fin_to_nnreal(k.clone());
        let (f_id, f) = bb.fresh_local(f_type.clone());
        let lhs = c.sum(
            k.clone(),
            c.scaled_fn(&bb, k.clone(), cv.clone(), f.clone()),
        );
        let rhs = c.mul(cv.clone(), c.sum(k.clone(), f));
        let body = c.eq_nnreal(lhs, rhs);
        let pi_f = bb.mk_pi(f_id, BinderInfo::Default, f_type, body);
        let pi_c = bb.mk_pi(cv_id, BinderInfo::Default, c.nnreal(), pi_f);
        bb.finish_child(pi_c)
    };
    let (ih_id, ih) = b.fresh_local(ih_type.clone());

    let succ_k = Expr::app(c.base.nat_succ.clone(), k.clone());
    let (cv_id, cv) = b.fresh_local(c.nnreal());
    let f_type_succ = c.fin_to_nnreal(succ_k.clone());
    let (f_id, f) = b.fresh_local(f_type_succ.clone());

    // f_cast = fun i : Fin k => f (Fin.castSucc k i).
    let f_cast = c.base.cast_prefix(&b, k.clone(), f.clone());
    // P = finSum k f_cast ; L = f (Fin.last k).
    let prefix_sum = c.sum(k.clone(), f_cast.clone());
    let last_val = Expr::app(f.clone(), Expr::app(c.base.fin_last.clone(), k.clone()));

    // LHS (after ι on finSum (k+1)):
    //   finSum k ((scaled c f)∘castSucc) + (scaled c f)(last)
    //   ≡ finSum k (scaled c f_cast) + mul c L   (definitionally).
    let scaled_prefix = c.sum(
        k.clone(),
        c.scaled_fn(&b, k.clone(), cv.clone(), f_cast.clone()),
    );
    let mul_c_last = c.mul(cv.clone(), last_val.clone());
    let lhs = c.add(scaled_prefix.clone(), mul_c_last.clone());

    // mid = mul c P + mul c L  (after IH rewrites the prefix).
    let mul_c_prefix = c.mul(cv.clone(), prefix_sum.clone());
    let mid = c.add(mul_c_prefix.clone(), mul_c_last.clone());

    // RHS = mul c (finSum (k+1) f) ≡ mul c (P + L)  (ι on finSum_succ).
    let p_plus_l = c.add(prefix_sum.clone(), last_val.clone());
    let rhs = c.mul(cv.clone(), p_plus_l.clone());

    // step1 : lhs = mid  via congrArg (· + mul c L) (IH c f_cast).
    let ih_app = Expr::app(Expr::app(ih.clone(), cv.clone()), f_cast.clone());
    let step1_fn = c.add_right_fn(&b, mul_c_last.clone());
    let step1 = c.congr_nnreal(scaled_prefix, mul_c_prefix, step1_fn, ih_app);

    // step2 : mid = rhs  via Eq.symm (NNReal.mul_add c P L).
    //   NNReal.mul_add c P L : mul c (P + L) = mul c P + mul c L.
    let distrib = Expr::apps(
        c.nnreal_mul_add.clone(),
        [cv.clone(), prefix_sum.clone(), last_val.clone()],
    );
    let step2 = c.eq_symm(rhs.clone(), mid.clone(), distrib);

    // proof : lhs = rhs.
    let proof = c.eq_trans(lhs, mid, rhs, step1, step2);

    let val = b.mk_lam(f_id, BinderInfo::Default, f_type_succ, proof);
    let val = b.mk_lam(cv_id, BinderInfo::Default, c.nnreal(), val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_type, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat(), val);
    b.finish(val)
}

fn build_smul_value(c: &FinSumSmulConsts) -> Expr {
    let motive = build_smul_motive(c);
    let base = build_smul_base(c);
    let step = build_smul_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat());
    let body = Expr::apps(c.nat_rec0.clone(), [motive, base, step, n]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat(), body);
    b.finish(val)
}

// ── NNReal.mul_zero ──────────────────────────────────────────────────────────

/// Handles for `NNReal.mul_zero`.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
struct MulZeroConsts {
    nat: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    #[cfg(test)]
    rat_le: Expr,
    rat_lt: Expr,
    rat_add: Expr,
    rat_add_lt_add_left: Expr,
    rat_add_zero: Expr,
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_mul: Expr,
    nnrat_zero: Expr,
    nnrat_of_rat: Expr,
    nnrat_mul_zero: Expr,
    nnreal_zero: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_mul: Expr,
    causeq_const: Expr,
    nat_le: Expr,
    #[cfg(test)]
    exists_c: Expr,
    exists_intro: Expr,
    and_c: Expr,
    and_intro: Expr,
    eq1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    congr_arg: Expr,
    #[cfg(test)]
    quot_mk: Expr,
    quot_sound: Expr,
    quot_ind: Expr,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl MulZeroConsts {
    fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            #[cfg(test)]
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_add: k("Rat.add"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_add_zero: k("Rat.add_zero"),
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_mul: k("NNRat.mul"),
            nnrat_zero: k("NNRat.zero"),
            nnrat_of_rat: k("NNRat.ofRat"),
            nnrat_mul_zero: k("NNRat.mul_zero"),
            nnreal_zero: k("NNReal.zero"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            causeq_const: k("NNReal.CauSeq.const"),
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
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
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
    fn causeq_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_mul.clone(), [a, b])
    }
    /// `NNReal.CauSeq.const (NNRat.ofRat 0 h0) : CauSeq` — the zero const seq.
    /// `NNReal.zero ≡ NNReal.mk (CauSeq.const (NNRat.ofRat 0 h0))`.
    fn zero_const(&self, h0: &Expr) -> Expr {
        let zero_nn = Expr::apps(
            self.nnrat_of_rat.clone(),
            [self.rat_zero.clone(), h0.clone()],
        );
        Expr::app(self.causeq_const.clone(), zero_nn)
    }
    #[cfg(test)]
    fn equiv(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [a, b])
    }
    #[cfg(test)]
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l],
        )
    }
    fn quot_sound(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), a, b, h],
        )
    }
    #[cfg(test)]
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
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
    fn congr_nnrat_rat(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nnrat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
}

/// Build `NNReal.mul_zero` value via `Quot.ind` on `c`.
fn build_mul_zero_value(c: &MulZeroConsts, nnreal: &Expr) -> Expr {
    // 0 ≤ 0 for the NNRat.ofRat 0 witness inside NNReal.zero.
    let rat_le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let h0 = Expr::app(rat_le_refl, c.rat_zero.clone());

    let mut b = EnvDeclBuilder::new();
    let (cv_id, cv) = b.fresh_local(nnreal.clone());

    // Quot.ind motive: fun x => Eq NNReal (mul x NNReal.zero) NNReal.zero.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let lhs = c.nnreal_mul(x.clone(), c.nnreal_zero.clone());
        let body = c.eq_nnreal(lhs, c.nnreal_zero.clone());
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), body))
    };
    // minor fc : Eq NNReal (mul (mk fc) NNReal.zero) NNReal.zero.
    //   mul (mk fc) NNReal.zero ≡ mk (CauSeq.mul fc (const (ofRat 0)));
    //   NNReal.zero ≡ mk (const (ofRat 0)).
    //   Close by Quot.sound on the Equiv.
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (fc_id, fc) = mf.fresh_local(c.causeq.clone());
        let zc = c.zero_const(&h0);
        let cl = c.causeq_mul(fc.clone(), zc.clone());
        let cr = zc.clone();
        let equiv = build_mul_zero_equiv(c, &mf, &fc, &h0);
        let body = c.quot_sound(cl, cr, equiv);
        mf.finish_child(mf.mk_lam(fc_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    let ind = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            cv.clone(),
        ],
    );
    let e = b.mk_lam(cv_id, BinderInfo::Default, nnreal.clone(), ind);
    b.finish(e)
}

/// Build `Equiv (CauSeq.mul fc (const (ofRat 0)))(const (ofRat 0))`. The two
/// sequences are pointwise-equal: `val(seq(mul fc (const 0)) n) ≡ val(NNRat.mul
/// (fc n)(NNRat.zero)) = 0` (`congrArg val (NNRat.mul_zero (fc n))`, and
/// `val(NNRat.zero) ≡ 0`), and `val(seq(const 0) n) ≡ 0`.
fn build_mul_zero_equiv(c: &MulZeroConsts, parent: &EnvDeclBuilder, fc: &Expr, h0: &Expr) -> Expr {
    let zc = c.zero_const(h0);
    let cl = c.causeq_mul(fc.clone(), zc.clone());
    let cr = zc.clone();

    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let pred = build_mz_pred(c, &b, &cl, &cr, &eps);
    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(c.nat_zero.clone(), m.clone());
        let (hle_id, _hle) = bw.fresh_local(hle_ty.clone());

        let vl = c.vseq(&cl, &m);
        let vr = c.vseq(&cr, &m);
        // h_eq : vL = vR. Both ≡ 0:
        //   vR = val(seq(const 0) m) ≡ val(NNRat.zero) ≡ 0.
        //   vL = val(seq(mul fc (const 0)) m) ≡ val(NNRat.mul (fc m) NNRat.zero).
        //     congrArg val (NNRat.mul_zero (fc m)) : val(mul (fc m) zero) = val(zero) ≡ 0.
        // So h_eq : vL = vR via congrArg val (NNRat.mul_zero (fc m)) (since vR ≡ val(zero)).
        let fcm = c.seq_at(fc, &m);
        let mul_zero_m = Expr::app(c.nnrat_mul_zero.clone(), fcm.clone()); // mul (fc m) zero = zero
        let lhs_nn = Expr::apps(c.nnrat_mul.clone(), [fcm.clone(), c.nnrat_zero.clone()]);
        let h_eq = c.congr_nnrat_rat(
            lhs_nn,
            c.nnrat_zero.clone(),
            c.nnrat_val.clone(),
            mul_zero_m,
        );

        // vL < vR + ε from vR < vR+ε and subst vR → vL via symm h_eq.
        let vr_eps = c.radd(vr.clone(), eps.clone());
        let vr_lt = build_self_lt_add(c, &bw, &vr, &eps, &hpos);
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

        // vR < vL + ε from vL < vL+ε and subst LHS vL → vR via h_eq.
        let vl_eps = c.radd(vl.clone(), eps.clone());
        let vl_lt = build_self_lt_add(c, &bw, &vl, &eps, &hpos);
        let motive_r = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(t, vl_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let right = c.subst_rat(motive_r, vl.clone(), vr.clone(), h_eq, vl_lt);

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
    b.finish_child(e)
}

/// `v < v + ε` from `0<ε`.
fn build_self_lt_add(
    c: &MulZeroConsts,
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
fn build_mz_pred(
    c: &MulZeroConsts,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNRat.mul_zero", "NNReal.mul_zero", "NNReal.finSum_smul"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_finsum_smul()
            .expect("init_algebra_nnreal_finsum_smul");
        env.init_algebra_nnreal_finsum_smul().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_finsum_smul_kernel_check() {
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
    fn test_nnreal_finsum_smul_constructive_empty_closure() {
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
