// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage C, the half-power CHARGE consumer:
//! `Σ_i Inf_i^{3/2} ≤ ε^{1/2}·I[f]` (the SHARP, `n`-free max-influence charge).
//!
//! # Statement
//!
//! ```text
//! BoolAnalysis.kkl_sum_pow32_influence_le :
//!   ∀ (n : Nat) (f : BoolFn n) (eps : Rat),
//!     (∀ i, Rat.le Rat.zero (Influence n f i)) →
//!     (∀ i, Rat.le (Influence n f i) eps) →
//!     Rat.lt eps Rat.one →
//!     NNReal.le
//!       (NNReal.finSum n (fun i => NNReal.pow32 (Influence n f i) (hnn i)))
//!       (NNReal.mul (NNReal.sqrtRat eps)
//!                   (NNReal.ofRat (TotalInfluence n f)
//!                                 (Fin.sum_nonneg n (fun i => Influence n f i) hnn)))
//! ```
//!
//! Under `max_i Inf_i ≤ ε < 1` (the genuine KKL regime — influences live in
//! `[0,1]`), the half-power charge collapses to `ε^{1/2}·I[f]`. This is the
//! CHARGE side the dual `(4/3→2)` hypercontractive bridge `M_{1..k} ≤
//! C·Σ_i Inf_i^{3/2}` feeds into; together they close the conditional KKL bound.
//!
//! # Proof (a COMPOSITION of landed axiom-free bricks)
//!
//! Write `Inf_i := Influence n f i`, `c := NNReal.sqrtRat eps`. All four bricks
//! are landed and axiom-free:
//!
//! 1. **per-coordinate** (`NNReal.pow32_le_sqrt_eps_mul`): for each `i`,
//!    `NNReal.pow32 Inf_i (hnn i) ≤ NNReal.mul c (NNReal.ofRat Inf_i (hnn i))`
//!    (uses `hnn i : 0≤Inf_i`, `hle i : Inf_i≤ε`, `he1 : ε<1`).
//! 2. **`NNReal.finSum_le`**: lift (1) pointwise to
//!    `finSum n (fun i => pow32 Inf_i) ≤ finSum n (fun i => mul c (ofRat Inf_i))`.
//! 3. **`NNReal.finSum_smul`**: pull the scalar out —
//!    `finSum n (fun i => mul c (ofRat Inf_i)) = mul c (finSum n (fun i => ofRat Inf_i))`.
//! 4. **`NNReal.finSum_ofRat`** (the bridge): commute `ofRat`/`finSum` —
//!    `finSum n (fun i => ofRat Inf_i (hnn i)) = ofRat (Fin.sum n (fun i => Inf_i)) hTot`,
//!    and `Fin.sum n (fun i => Inf_i) ≡ TotalInfluence n f` (reducible δ), so the
//!    RHS is `ofRat (TotalInfluence n f) hTot`.
//!
//! Chain: `NNReal.le.trans` is NOT needed — step 2 already lands on the
//! `finSum (scaled)` form, and steps 3+4 supply the EQUALITY
//! `finSum (scaled) = mul c (ofRat (TotalInfluence n f) hTot)` (the target RHS),
//! so an `Eq.subst` of that equality into the `≤` of step 2 closes the goal:
//!
//! ```text
//!   heq : finSum (scaled) = mul c (ofRat (TotalInfluence n f) hTot)
//!       := Eq.trans (finSum_smul …) (congrArg (mul c) (finSum_ofRat …))
//!   @Eq.subst NNReal (fun t => NNReal.le (finSum (pow32-fn)) t)
//!             (finSum (scaled)) (mul c (ofRat Total hTot)) heq (finSum_le …)
//! ```
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the half-power consumer.
struct Pow32ConsumerConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    fin: Expr,
    bool_fn: Expr,
    influence: Expr,
    total_influence: Expr,
    fin_sum: Expr,
    fin_sum_nonneg: Expr,
    nnreal: Expr,
    nnreal_le: Expr,
    nnreal_mul: Expr,
    nnreal_of_rat: Expr,
    nnreal_sqrt: Expr,
    nnreal_pow32: Expr,
    nnreal_finsum: Expr,
    pow32_bound: Expr,
    finsum_le: Expr,
    finsum_smul: Expr,
    finsum_ofrat: Expr,
    // logic.
    eq1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
    congr_arg: Expr,
}

impl Pow32ConsumerConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            fin: k("Fin"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            influence: k("BoolAnalysis.Influence"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            fin_sum: k("Fin.sum"),
            fin_sum_nonneg: k("Fin.sum_nonneg"),
            nnreal: k("NNReal"),
            nnreal_le: k("NNReal.le"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_sqrt: k("NNReal.sqrtRat"),
            nnreal_pow32: k("NNReal.pow32"),
            nnreal_finsum: k("NNReal.finSum"),
            pow32_bound: k("NNReal.pow32_le_sqrt_eps_mul"),
            finsum_le: k("NNReal.finSum_le"),
            finsum_smul: k("NNReal.finSum_smul"),
            finsum_ofrat: k("NNReal.finSum_ofRat"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    /// `Influence n f i : Rat`.
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    /// `TotalInfluence n f : Rat`.
    fn total_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    /// `NNReal.le a b : Prop`.
    fn nnle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a, b])
    }
    /// `NNReal.mul a b : NNReal`.
    fn nnmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a, b])
    }
    /// `NNReal.ofRat x h : NNReal`.
    fn of_rat(&self, x: Expr, h: Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x, h])
    }
    /// `NNReal.sqrtRat eps : NNReal`.
    fn sqrt(&self, eps: &Expr) -> Expr {
        Expr::app(self.nnreal_sqrt.clone(), eps.clone())
    }
    /// `NNReal.pow32 x h : NNReal`.
    fn pow32(&self, x: Expr, h: Expr) -> Expr {
        Expr::apps(self.nnreal_pow32.clone(), [x, h])
    }
    /// `NNReal.finSum n f : NNReal`.
    fn finsum(&self, n: &Expr, f: Expr) -> Expr {
        Expr::apps(self.nnreal_finsum.clone(), [n.clone(), f])
    }
    /// `Fin.sum n g : Rat`.
    fn fin_sum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), g])
    }
    /// `@Eq.{1} NNReal a b`.
    fn eq_nnreal(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nnreal.clone(), a, b])
    }
    fn eq_trans(&self, a: Expr, b: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.nnreal.clone(), a, b, d, h1, h2],
        )
    }
    /// `@Eq.subst.{1} NNReal motive a b h_eq h : motive b`.
    fn subst_nnreal(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@congrArg NNReal NNReal a b g h : g a = g b`.
    fn congr_nnreal(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.nnreal.clone(), self.nnreal.clone(), a, b, g, h],
        )
    }
}

impl Environment {
    /// Register `BoolAnalysis.kkl_sum_pow32_influence_le`. Idempotent;
    /// kernel-checked, Constructive, empty admitted-axiom closure.
    pub fn init_boolean_analysis_kkl_pow32_consumer(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_sum_pow32_influence_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Bricks (+ their transitive prereqs).
        self.init_algebra_nnreal_pow32_bound()?; // NNReal.pow32(_le_sqrt_eps_mul), sqrtRat, mul, ofRat
        self.init_algebra_nnreal_finsum_le()?; // NNReal.finSum(_le), NNReal.le
        self.init_algebra_nnreal_finsum_smul()?; // NNReal.finSum_smul, NNReal.mul_add
        self.init_algebra_nnreal_finsum_ofrat()?; // NNReal.finSum_ofRat (+ Fin.sum_nonneg)
        self.init_boolean_analysis()?; // Influence, TotalInfluence (reducible defs), BoolFn
        self.init_eq()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register this
        // theorem transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = Pow32ConsumerConsts::new();
        let ty = build_consumer_type(&c);
        let value = build_consumer_value(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `∀ (i : Fin n), Rat.le Rat.zero (Influence n f i)`.
fn nn_hyp(c: &Pow32ConsumerConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let fin_n = c.fin_of(n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.rle(c.rat_zero.clone(), c.influence_of(n, f, &i));
    let pi = b.mk_pi(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(pi)
}

/// `∀ (i : Fin n), Rat.le (Influence n f i) eps`.
fn le_hyp(
    c: &Pow32ConsumerConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    eps: &Expr,
) -> Expr {
    let fin_n = c.fin_of(n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.rle(c.influence_of(n, f, &i), eps.clone());
    let pi = b.mk_pi(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(pi)
}

/// `fun (i : Fin n) => NNReal.pow32 (Influence n f i)(hnn i)`.
fn pow32_fn(
    c: &Pow32ConsumerConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    hnn: &Expr,
) -> Expr {
    let fin_n = c.fin_of(n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let inf = c.influence_of(n, f, &i);
    let hi = Expr::app(hnn.clone(), i.clone());
    let body = c.pow32(inf, hi);
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(lam)
}

/// `fun (i : Fin n) => NNReal.ofRat (Influence n f i)(hnn i)`.
fn ofrat_fn(
    c: &Pow32ConsumerConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    hnn: &Expr,
) -> Expr {
    let fin_n = c.fin_of(n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let inf = c.influence_of(n, f, &i);
    let hi = Expr::app(hnn.clone(), i.clone());
    let body = c.of_rat(inf, hi);
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(lam)
}

/// `fun (i : Fin n) => NNReal.mul (sqrtRat eps) (NNReal.ofRat (Influence n f i)(hnn i))`.
fn scaled_fn(
    c: &Pow32ConsumerConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    eps: &Expr,
    hnn: &Expr,
) -> Expr {
    let fin_n = c.fin_of(n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let inf = c.influence_of(n, f, &i);
    let hi = Expr::app(hnn.clone(), i.clone());
    let body = c.nnmul(c.sqrt(eps), c.of_rat(inf, hi));
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(lam)
}

/// `fun (i : Fin n) => Influence n f i` — the Rat-valued summand of `Fin.sum`.
fn influence_fn(c: &Pow32ConsumerConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let fin_n = c.fin_of(n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let body = c.influence_of(n, f, &i);
    let lam = b.mk_lam(i_id, BinderInfo::Default, fin_n, body);
    b.finish_child(lam)
}

/// `0 ≤ TotalInfluence n f`, via `Fin.sum_nonneg n (fun i => Influence n f i) hnn`
/// (`TotalInfluence n f ≡ Fin.sum n (fun i => Influence n f i)` defeq).
fn h_total_nonneg(
    c: &Pow32ConsumerConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    hnn: &Expr,
) -> Expr {
    let infl = influence_fn(c, parent, n, f);
    Expr::apps(c.fin_sum_nonneg.clone(), [n.clone(), infl, hnn.clone()])
}

fn build_consumer_type(c: &Pow32ConsumerConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let h_nn = nn_hyp(c, &b, &n, &f);
    let (hnn_id, hnn) = b.fresh_local(h_nn.clone());
    let h_le = le_hyp(c, &b, &n, &f, &eps);
    let (hle_id, _hle) = b.fresh_local(h_le.clone());
    let he1_ty = c.rlt(eps.clone(), c.rat_one.clone());
    let (he1_id, _he1) = b.fresh_local(he1_ty.clone());

    let lhs = c.finsum(&n, pow32_fn(c, &b, &n, &f, &hnn));
    let h_tot = h_total_nonneg(c, &b, &n, &f, &hnn);
    let rhs = c.nnmul(c.sqrt(&eps), c.of_rat(c.total_of(&n, &f), h_tot));
    let concl = c.nnle(lhs, rhs);

    let e = b.mk_pi(he1_id, BinderInfo::Default, he1_ty, concl);
    let e = b.mk_pi(hle_id, BinderInfo::Default, h_le, e);
    let e = b.mk_pi(hnn_id, BinderInfo::Default, h_nn, e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

fn build_consumer_value(c: &Pow32ConsumerConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let h_nn = nn_hyp(c, &b, &n, &f);
    let (hnn_id, hnn) = b.fresh_local(h_nn.clone());
    let h_le = le_hyp(c, &b, &n, &f, &eps);
    let (hle_id, hle) = b.fresh_local(h_le.clone());
    let he1_ty = c.rlt(eps.clone(), c.rat_one.clone());
    let (he1_id, he1) = b.fresh_local(he1_ty.clone());

    let sqrt_eps = c.sqrt(&eps);
    let p_fn = pow32_fn(c, &b, &n, &f, &hnn);
    let s_fn = scaled_fn(c, &b, &n, &f, &eps, &hnn);
    let o_fn = ofrat_fn(c, &b, &n, &f, &hnn);
    let h_tot = h_total_nonneg(c, &b, &n, &f, &hnn);

    // ── Step 1+2: per-coordinate bound lifted by finSum_le.
    //   pointwise : fun i => pow32_bound (Inf_i) eps (hnn i)(hle i) he1
    //     : NNReal.le (pow32 Inf_i (hnn i)) (mul (sqrtRat eps)(ofRat Inf_i (hnn i)))
    //   = NNReal.le (p_fn i)(s_fn i).
    let pointwise = {
        let fin_n = c.fin_of(&n);
        let mut pb = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = pb.fresh_local(fin_n.clone());
        let inf = c.influence_of(&n, &f, &i);
        let hi = Expr::app(hnn.clone(), i.clone());
        let hle_i = Expr::app(hle.clone(), i.clone());
        let body = Expr::apps(
            c.pow32_bound.clone(),
            [inf, eps.clone(), hi, hle_i, he1.clone()],
        );
        let lam = pb.mk_lam(i_id, BinderInfo::Default, fin_n, body);
        pb.finish_child(lam)
    };
    // h_le_step : NNReal.le (finSum n p_fn)(finSum n s_fn).
    let finsum_p = c.finsum(&n, p_fn.clone());
    let finsum_s = c.finsum(&n, s_fn.clone());
    let h_le_step = Expr::apps(
        c.finsum_le.clone(),
        [n.clone(), p_fn.clone(), s_fn.clone(), pointwise],
    );

    // ── Step 3: finSum_smul pulls the scalar out.
    //   smul : finSum n (fun i => mul (sqrtRat eps)(o_fn i))
    //            = mul (sqrtRat eps)(finSum n o_fn).
    //   LHS `fun i => mul (sqrtRat eps)(o_fn i)` is defeq to `s_fn` (β).
    let finsum_o = c.finsum(&n, o_fn.clone());
    let mul_c_finsum_o = c.nnmul(sqrt_eps.clone(), finsum_o.clone());
    let smul = Expr::apps(
        c.finsum_smul.clone(),
        [n.clone(), sqrt_eps.clone(), o_fn.clone()],
    );

    // ── Step 4: the bridge.
    //   bridge : finSum n o_fn = ofRat (Fin.sum n (fun i => Inf_i)) hTot
    //          ≡ ofRat (TotalInfluence n f) hTot   (δ on TotalInfluence).
    let infl = influence_fn(c, &b, &n, &f);
    let bridge = Expr::apps(
        c.finsum_ofrat.clone(),
        [n.clone(), infl.clone(), hnn.clone(), h_tot.clone()],
    );
    let ofrat_total = c.of_rat(c.total_of(&n, &f), h_tot.clone());
    let mul_c_ofrat_total = c.nnmul(sqrt_eps.clone(), ofrat_total.clone());

    // congr : mul (sqrtRat eps)(finSum n o_fn) = mul (sqrtRat eps)(ofRat Total hTot)
    //   via congrArg (mul (sqrtRat eps)) bridge.
    let mul_left_fn = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnmul(sqrt_eps.clone(), x);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let ofrat_total_for_bridge = c.of_rat(c.fin_sum(&n, infl), h_tot.clone());
    let congr = c.congr_nnreal(
        finsum_o.clone(),
        ofrat_total_for_bridge,
        mul_left_fn,
        bridge,
    );

    // heq : finSum n s_fn = mul (sqrtRat eps)(ofRat Total hTot).
    //   = Eq.trans smul congr.  (`finSum n s_fn` is defeq to the smul LHS.)
    let heq = c.eq_trans(
        finsum_s.clone(),
        mul_c_finsum_o,
        mul_c_ofrat_total.clone(),
        smul,
        congr,
    );

    // ── Close: subst heq into the ≤ of step 2.
    //   motive := fun t => NNReal.le (finSum n p_fn) t.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnle(finsum_p.clone(), t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let proof = c.subst_nnreal(motive, finsum_s, mul_c_ofrat_total, heq, h_le_step);

    let e = b.mk_lam(he1_id, BinderInfo::Default, he1_ty, proof);
    let e = b.mk_lam(hle_id, BinderInfo::Default, h_le, e);
    let e = b.mk_lam(hnn_id, BinderInfo::Default, h_nn, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_pow32_consumer()
            .expect("init_boolean_analysis_kkl_pow32_consumer");
        env.init_boolean_analysis_kkl_pow32_consumer()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_kkl_sum_pow32_influence_le_kernel_check() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.kkl_sum_pow32_influence_le");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_).unwrap_or_else(|e| {
            panic!("BoolAnalysis.kkl_sum_pow32_influence_le must kernel-check: {e:?}")
        });
    }

    #[test]
    fn test_kkl_sum_pow32_influence_le_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.kkl_sum_pow32_influence_le");
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
