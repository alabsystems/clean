// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component B, target 3: `NNReal.finSum_le`
//! (monotonicity of the `NNReal`-valued `Fin.sum`).
//!
//! # Why this module exists
//!
//! The sharp KKL charge `Σ_i Inf_i^{3/2} ≤ ε^{1/2}·I[f]` is proven from the
//! per-coordinate bound `Inf_i^{3/2} ≤ ε^{1/2}·Inf_i` by summing both sides; the
//! sum-monotonicity step is exactly:
//!
//! - `NNReal.finSum_le : ∀ (n : Nat) (f g : Fin n → NNReal),
//!       (∀ i, NNReal.le (f i) (g i)) →
//!       NNReal.le (NNReal.finSum n f) (NNReal.finSum n g)`.
//!
//! # Proof shape (axiom-free)
//!
//! `Nat.rec.{0}` over `n` (Prop motive
//! `fun k => ∀ f g, (∀ i, le (f i)(g i)) → le (finSum k f)(finSum k g)`),
//! mirroring the on-main `Fin.sum_le`:
//! - BASE `n=0`: `finSum 0 f ≡ NNReal.zero ≡ finSum 0 g` (Nat.rec base ι), so
//!   `NNReal.le NNReal.zero NNReal.zero` via `NNReal.le.refl NNReal.zero`.
//! - STEP `n=k+1`: `finSum (k+1) f ≡ NNReal.add (finSum k (f∘castSucc))
//!   (f (last k))` (Nat.rec step ι), so apply `NNReal.add_le_add` to the prefix
//!   inequality (IH on the cast-restricted functions, hypothesis composed with
//!   `castSucc`) and the last-index inequality (hypothesis at `last k`).
//!
//! Unlike the on-main `Fin.sum_le` (which needs an `add_comm`/`add_assoc`
//! reshuffle to combine the two Rat inequalities), `NNReal.add_le_add` discharges
//! BOTH arguments directly, so the step case is a single application.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::algebra_nnreal_finsum::NNFinSumConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNReal.finSum_le`.
pub(crate) struct FinSumLeConsts {
    base: NNFinSumConsts,
    nat_rec0: Expr,
    nnreal_le: Expr,
    nnreal_le_refl: Expr,
    nnreal_add_le_add: Expr,
}

impl FinSumLeConsts {
    pub(crate) fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            base: NNFinSumConsts::new(),
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            nnreal_le: k("NNReal.le"),
            nnreal_le_refl: k("NNReal.le.refl"),
            nnreal_add_le_add: k("NNReal.add_le_add"),
        }
    }

    fn nat(&self) -> Expr {
        self.base.nat.clone()
    }
    #[cfg(test)]
    fn nnreal(&self) -> Expr {
        self.base.nnreal.clone()
    }
    fn fin_to_nnreal(&self, n: Expr) -> Expr {
        self.base.fin_to_nnreal(n)
    }
    fn sum(&self, n: Expr, f: Expr) -> Expr {
        self.base.sum(n, f)
    }
    /// `NNReal.le a b : Prop`.
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a, b])
    }
    fn fin(&self, n: Expr) -> Expr {
        Expr::app(self.base.fin.clone(), n)
    }

    /// `∀ (i : Fin n), NNReal.le (f i)(g i)` — the pointwise-le hypothesis.
    fn pointwise_le(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, g: &Expr) -> Expr {
        let fin_n = self.fin(n.clone());
        let mut b = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.le(Expr::app(f.clone(), i.clone()), Expr::app(g.clone(), i));
        let pi = b.mk_pi(i_id, BinderInfo::Default, fin_n, body);
        b.finish_child(pi)
    }
}

impl Environment {
    /// Register `NNReal.finSum_le`. Idempotent.
    pub fn init_algebra_nnreal_finsum_le(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_finsum()?; // NNReal.zero, NNReal.finSum
        self.init_algebra_nnreal_le()?; // NNReal.le, NNReal.le.refl
        self.init_algebra_nnreal_le_add()?; // NNReal.add_le_add

        let name = Name::from_string("NNReal.finSum_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = FinSumLeConsts::new();
        let ty = build_finsum_le_type(&c);
        let value = build_finsum_le_value(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `∀ (n : Nat)(f g : Fin n → NNReal),
///     (∀ i, NNReal.le (f i)(g i)) → NNReal.le (finSum n f)(finSum n g)`.
fn build_finsum_le_type(c: &FinSumLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat());
    let f_type = c.fin_to_nnreal(n.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let (g_id, g) = b.fresh_local(f_type.clone());
    let hyp = c.pointwise_le(&b, &n, &f, &g);
    let (h_id, _h) = b.fresh_local(hyp.clone());
    let concl = c.le(c.sum(n.clone(), f), c.sum(n.clone(), g));
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(g_id, BinderInfo::Default, f_type.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_type, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat(), e);
    b.finish(e)
}

/// The `Nat.rec.{0}` motive: `fun k => ∀ f g, (∀ i, le (f i)(g i)) →
///   le (finSum k f)(finSum k g)`.
fn build_motive(c: &FinSumLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat());
    let f_type = c.fin_to_nnreal(k.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let (g_id, g) = b.fresh_local(f_type.clone());
    let hyp = c.pointwise_le(&b, &k, &f, &g);
    let (h_id, _h) = b.fresh_local(hyp.clone());
    let concl = c.le(c.sum(k.clone(), f), c.sum(k.clone(), g));
    let pi_h = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let pi_g = b.mk_pi(g_id, BinderInfo::Default, f_type.clone(), pi_h);
    let pi_f = b.mk_pi(f_id, BinderInfo::Default, f_type, pi_g);
    let lam = b.mk_lam(k_id, BinderInfo::Default, c.nat(), pi_f);
    b.finish(lam)
}

/// Base case (n=0): `fun f g _h => NNReal.le.refl NNReal.zero`.
/// `finSum 0 f ≡ NNReal.zero ≡ finSum 0 g`, so the goal `le (finSum 0 f)
/// (finSum 0 g)` is defeq to `le NNReal.zero NNReal.zero` = `le.refl zero`.
fn build_base(c: &FinSumLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let f_type = c.fin_to_nnreal(c.base.nat_zero.clone());
    let (f_id, f) = b.fresh_local(f_type.clone());
    let (g_id, g) = b.fresh_local(f_type.clone());
    let hyp = c.pointwise_le(&b, &c.base.nat_zero.clone(), &f, &g);
    let (h_id, _h) = b.fresh_local(hyp.clone());
    let proof = Expr::app(c.nnreal_le_refl.clone(), c.base.nnreal_zero.clone());
    let val = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
    let val = b.mk_lam(g_id, BinderInfo::Default, f_type.clone(), val);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_type, val);
    b.finish(val)
}

/// Step case (n=k+1): `fun k ih f g h =>
///   NNReal.add_le_add (finSum k (f∘castSucc))(finSum k (g∘castSucc))
///                     (f (last k))(g (last k))
///                     (ih (f∘castSucc)(g∘castSucc)(h∘castSucc))
///                     (h (last k))`.
/// `finSum (k+1) f ≡ NNReal.add (finSum k (f∘castSucc))(f (last k))` (step ι),
/// so the goal `le (finSum (k+1) f)(finSum (k+1) g)` is defeq to
/// `le (NNReal.add … …)(NNReal.add … …)` = the `add_le_add` result.
fn build_step(c: &FinSumLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat());

    // ih : ∀ f g, (∀ i, le (f i)(g i)) → le (finSum k f)(finSum k g).
    let f_type_k = c.fin_to_nnreal(k.clone());
    let ih_type = {
        let mut ib = EnvDeclBuilder::child_of(&b);
        let (ihf_id, ihf) = ib.fresh_local(f_type_k.clone());
        let (ihg_id, ihg) = ib.fresh_local(f_type_k.clone());
        let ih_hyp = c.pointwise_le(&ib, &k, &ihf, &ihg);
        let (ihh_id, _h) = ib.fresh_local(ih_hyp.clone());
        let ih_concl = c.le(c.sum(k.clone(), ihf.clone()), c.sum(k.clone(), ihg.clone()));
        let e = ib.mk_pi(ihh_id, BinderInfo::Default, ih_hyp, ih_concl);
        let e = ib.mk_pi(ihg_id, BinderInfo::Default, f_type_k.clone(), e);
        let e = ib.mk_pi(ihf_id, BinderInfo::Default, f_type_k.clone(), e);
        ib.finish_child(e)
    };
    let (ih_id, ih) = b.fresh_local(ih_type.clone());

    let succ_k = Expr::app(c.base.nat_succ.clone(), k.clone());
    let f_type_succ = c.fin_to_nnreal(succ_k.clone());
    let (f_id, f) = b.fresh_local(f_type_succ.clone());
    let (g_id, g) = b.fresh_local(f_type_succ.clone());
    let hyp = c.pointwise_le(&b, &succ_k, &f, &g);
    let (h_id, h) = b.fresh_local(hyp.clone());

    // Cast-prefix functions and the cast-composed hypothesis.
    let f_cast = c.base.cast_prefix(&b, k.clone(), f.clone());
    let g_cast = c.base.cast_prefix(&b, k.clone(), g.clone());
    let h_cast = {
        let fin_k = c.fin(k.clone());
        let mut hb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = hb.fresh_local(fin_k.clone());
        let cast_i = Expr::app(Expr::app(c.base.fin_cast_succ.clone(), k.clone()), i);
        let body = Expr::app(h.clone(), cast_i);
        let lam = hb.mk_lam(i_id, BinderInfo::Default, fin_k, body);
        hb.finish_child(lam)
    };

    // prefix_le : le (finSum k (f∘cast))(finSum k (g∘cast)) := ih (f∘cast)(g∘cast)(h∘cast).
    let prefix_le = Expr::apps(ih, [f_cast.clone(), g_cast.clone(), h_cast]);

    // last_le : le (f (last k))(g (last k)) := h (last k).
    let last_k = Expr::app(c.base.fin_last.clone(), k.clone());
    let f_last = Expr::app(f.clone(), last_k.clone());
    let g_last = Expr::app(g.clone(), last_k.clone());
    let last_le = Expr::app(h.clone(), last_k);

    // add_le_add (finSum k (f∘cast))(finSum k (g∘cast))(f last)(g last) prefix_le last_le.
    let sum_f_cast = c.sum(k.clone(), f_cast);
    let sum_g_cast = c.sum(k.clone(), g_cast);
    let proof = Expr::apps(
        c.nnreal_add_le_add.clone(),
        [sum_f_cast, sum_g_cast, f_last, g_last, prefix_le, last_le],
    );

    let val = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
    let val = b.mk_lam(g_id, BinderInfo::Default, f_type_succ.clone(), val);
    let val = b.mk_lam(f_id, BinderInfo::Default, f_type_succ, val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_type, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat(), val);
    b.finish(val)
}

/// `NNReal.finSum_le := fun n => Nat.rec.{0} motive base step n` (then the
/// f/g/h binders come from the motive's body).
fn build_finsum_le_value(c: &FinSumLeConsts) -> Expr {
    let motive = build_motive(c);
    let base = build_base(c);
    let step = build_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat());
    let body = Expr::apps(c.nat_rec0.clone(), [motive, base, step, n]);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat(), body);
    b.finish(val)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_finsum_le()
            .expect("init_algebra_nnreal_finsum_le");
        env.init_algebra_nnreal_finsum_le().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_finsum_le_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.finSum_le");
        let info = env.get_const(&nm).expect("NNReal.finSum_le registered");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("NNReal.finSum_le must kernel-check");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
    }

    #[test]
    fn test_nnreal_finsum_le_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.finSum_le");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }
}
