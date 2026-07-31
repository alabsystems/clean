// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type builders for C010 robustness-generalization bounds.
//!
//! Contains definition type builders and theorem type builders:
//!
//! Definitions:
//! - `certified_robust`, `lipschitz_local`, `nat_to_rat`, `sqrt`, `ln`
//! - `rademacher_complexity`, `generalization_gap`, `gen_bound`
//!
//! Theorems:
//! 1. `certified_implies_lipschitz_local`: cert robust => locally Lipschitz
//! 2. `lipschitz_rademacher_bound`: Lipschitz => Rademacher complexity bound
//! 3. `rademacher_gen_bound`: Rademacher => generalization bound (PAC)
//! 4. `certificate_gen_bound`: cert => generalization bound (main theorem)
//! 5. `tighter_cert_better_gen`: tighter cert => better generalization
//!
//! Part of #3262.

#[cfg(test)]
use super::nn_verify_robustness_generalization::RobustnessGenConsts;
#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};

// =============================================================================
// Definition type builders
// =============================================================================

/// `NNVerify.RobustnessGen.certified_robust : Nat -> (NNVec n -> NNVec n) -> Rat -> Prop`
#[cfg(test)]
pub(super) fn build_certified_robust_type(c: &RobustnessGenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (f_id, _) = b.fresh_local(endo.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.RobustnessGen.lipschitz_local : Nat -> (NNVec n -> NNVec n) -> Rat -> Rat -> Prop`
#[cfg(test)]
pub(super) fn build_lipschitz_local_type(c: &RobustnessGenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (f_id, _) = b.fresh_local(endo.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let (l_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.RobustnessGen.nat_to_rat : Nat -> Rat`
#[cfg(test)]
pub(super) fn build_nat_to_rat_type(c: &RobustnessGenConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.nat.clone(), c.rat.clone())
}

/// `NNVerify.RobustnessGen.sqrt : Rat -> Rat`
#[cfg(test)]
pub(super) fn build_sqrt_type(c: &RobustnessGenConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone())
}

/// `NNVerify.RobustnessGen.ln : Rat -> Rat`
#[cfg(test)]
pub(super) fn build_ln_type(c: &RobustnessGenConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone())
}

/// `NNVerify.RobustnessGen.rademacher_complexity : Nat -> Rat -> Rat`
#[cfg(test)]
pub(super) fn build_rademacher_complexity_type(c: &RobustnessGenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, _) = b.fresh_local(c.nat.clone());
    let (l_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.RobustnessGen.generalization_gap : Rat -> Rat -> Rat`
#[cfg(test)]
pub(super) fn build_generalization_gap_type(c: &RobustnessGenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (tr_id, _) = b.fresh_local(c.rat.clone());
    let (te_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(te_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(tr_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNVerify.RobustnessGen.gen_bound : Nat -> Rat -> Rat -> Rat -> Rat`
#[cfg(test)]
pub(super) fn build_gen_bound_type(c: &RobustnessGenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, _) = b.fresh_local(c.nat.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let (m_id, _) = b.fresh_local(c.rat.clone());
    let (delta_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(delta_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(m_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Theorem type builders
// =============================================================================

/// `NNVerify.RobustnessGen.certified_implies_lipschitz_local`:
/// ```text
/// forall (d : Nat) (f : NNVec d -> NNVec d) (eps : Rat),
///   certified_robust d f eps -> 0 < eps ->
///   lipschitz_local d f eps (Rat.div Rat.one eps)
/// ```
///
/// Certified robustness radius eps implies local Lipschitz constant 1/eps.
#[cfg(test)]
pub(super) fn build_certified_implies_lipschitz_local_type(c: &RobustnessGenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&d);
    let (f_id, f) = b.fresh_local(endo.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    // hypothesis 1: certified_robust d f eps
    let hyp_cert = Expr::apps(
        c.certified_robust.clone(),
        [d.clone(), f.clone(), eps.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_cert.clone());
    // hypothesis 2: 0 < eps
    let hyp_pos = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h2_id, _) = b.fresh_local(hyp_pos.clone());
    // conclusion: lipschitz_local d f eps (1/eps)
    let one_over_eps = c.div(c.rat_one.clone(), eps.clone());
    let concl = Expr::apps(c.lipschitz_local.clone(), [d.clone(), f, eps, one_over_eps]);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_pos, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_cert, e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// NOTE (#3578): `build_certified_implies_lipschitz_local_constructive_proof`
// deleted during Branch A demasquerade. The former #3463 proof term
// `fun d f eps _h1 _h2 => True.intro` was a MASQUERADE per
// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M2 + M4: it
// type-checked only because `lipschitz_local` was simultaneously
// promoted to a reducible `Declaration::Definition` with body
// `fun _ _ _ _ => True` (`register_rg_lipschitz_local` in
// `..._values.rs`). Reverting `lipschitz_local` to `Declaration::Opaque`
// closes the delta-reduction path, and demoting
// `certified_implies_lipschitz_local` to `Declaration::Axiom` drops the
// vacuous proof term. A `#[cfg(test)]` copy of the deleted builder is
// intentionally NOT retained — guard tests pin the axiom shape directly
// (see `tests_nn_verify_robustness_gen.rs`
// `test_c010_certified_implies_lipschitz_local_is_axiom_honest_demotion_3578`).
// Branch B (faithful Lipschitz predicate + genuine proof) is tracked
// under epic #3470.

/// `NNVerify.RobustnessGen.lipschitz_rademacher_bound`:
/// ```text
/// forall (d : Nat) (L m_samples : Rat),
///   0 < L -> 0 < m_samples ->
///   LE.le (rademacher_complexity d L)
///         (Rat.div (Rat.mul L (sqrt (nat_to_rat d))) (sqrt m_samples))
/// ```
///
/// Classical result: Rademacher complexity of L-Lipschitz class on R^d
/// is bounded by L * sqrt(d) / sqrt(m).
#[cfg(test)]
pub(super) fn build_lipschitz_rademacher_bound_type(c: &RobustnessGenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());
    let (m_id, m) = b.fresh_local(c.rat.clone());
    // hypothesis 1: 0 < L
    let hyp_l = c.rat_lt(c.rat_zero.clone(), l.clone());
    let (h1_id, _) = b.fresh_local(hyp_l.clone());
    // hypothesis 2: 0 < m_samples
    let hyp_m = c.rat_lt(c.rat_zero.clone(), m.clone());
    let (h2_id, _) = b.fresh_local(hyp_m.clone());
    // conclusion: rademacher_complexity d L <= L * sqrt(d) / sqrt(m)
    let lhs = Expr::apps(c.rademacher_complexity.clone(), [d.clone(), l.clone()]);
    let sqrt_d = Expr::app(c.sqrt.clone(), Expr::app(c.nat_to_rat.clone(), d));
    let sqrt_m = Expr::app(c.sqrt.clone(), m);
    let rhs = c.div(c.mul(l, sqrt_d), sqrt_m);
    let concl = c.rat_le(lhs, rhs);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_m, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_l, e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.RobustnessGen.rademacher_gen_bound`:
/// ```text
/// forall (R_n m_rat delta : Rat),
///   0 < m_rat -> 0 < delta -> delta < 1 ->
///   forall (train_risk test_risk : Rat),
///     LE.le (generalization_gap train_risk test_risk)
///           (Rat.add (Rat.mul 2 R_n)
///                    (sqrt (Rat.div (ln (Rat.div 2 delta))
///                                   (Rat.mul 2 m_rat))))
/// ```
///
/// Standard PAC-learning generalization bound via Rademacher complexity.
#[cfg(test)]
pub(super) fn build_rademacher_gen_bound_type(c: &RobustnessGenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rn_id, r_n) = b.fresh_local(c.rat.clone());
    let (m_id, m_rat) = b.fresh_local(c.rat.clone());
    let (delta_id, delta) = b.fresh_local(c.rat.clone());
    // hypothesis 1: 0 < m_rat
    let hyp_m = c.rat_lt(c.rat_zero.clone(), m_rat.clone());
    let (h1_id, _) = b.fresh_local(hyp_m.clone());
    // hypothesis 2: 0 < delta
    let hyp_d = c.rat_lt(c.rat_zero.clone(), delta.clone());
    let (h2_id, _) = b.fresh_local(hyp_d.clone());
    // hypothesis 3: delta < 1
    let hyp_d1 = c.rat_lt(delta.clone(), c.rat_one.clone());
    let (h3_id, _) = b.fresh_local(hyp_d1.clone());
    // inner forall over train_risk, test_risk
    let inner = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (tr_id, tr) = ch.fresh_local(c.rat.clone());
        let (te_id, te) = ch.fresh_local(c.rat.clone());
        // gen_gap(tr, te) <= 2*R_n + sqrt(ln(2/delta) / (2*m))
        let gap = Expr::apps(c.generalization_gap.clone(), [tr, te]);
        let two = c.two();
        let rademacher_term = c.mul(two.clone(), r_n.clone());
        let confidence_num = Expr::app(c.ln.clone(), c.div(two.clone(), delta.clone()));
        let confidence_denom = c.mul(two, m_rat.clone());
        let confidence_term = Expr::app(c.sqrt.clone(), c.div(confidence_num, confidence_denom));
        let bound = c.add(rademacher_term, confidence_term);
        let concl = c.rat_le(gap, bound);
        let r = ch.mk_pi(te_id, BinderInfo::Default, c.rat.clone(), concl);
        let r = ch.mk_pi(tr_id, BinderInfo::Default, c.rat.clone(), r);
        ch.finish_child(r)
    };
    let e = b.mk_pi(h3_id, BinderInfo::Default, hyp_d1, inner);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_d, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_m, e);
    let e = b.mk_pi(delta_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(rn_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNVerify.RobustnessGen.certificate_gen_bound` (MAIN THEOREM):
/// ```text
/// forall (d : Nat) (f : NNVec d -> NNVec d) (eps m_rat delta : Rat),
///   certified_robust d f eps ->
///   0 < eps -> 0 < m_rat -> 0 < delta -> delta < 1 ->
///   LE.le (gen_bound d eps m_rat delta)
///         (Rat.add (Rat.div (Rat.mul 2 (sqrt (nat_to_rat d)))
///                           (Rat.mul eps (sqrt m_rat)))
///                  (sqrt (Rat.div (ln (Rat.div 2 delta))
///                                 (Rat.mul 2 m_rat))))
/// ```
///
/// The main theorem: a verification certificate with robustness radius eps
/// implies a generalization bound that decreases with eps (tighter
/// certificate => better generalization). The bound has two terms:
/// - Rademacher term: 2*sqrt(d)/(eps*sqrt(m)) from certificate => Lipschitz
/// - Confidence term: sqrt(ln(2/delta)/(2*m)) from PAC tail bound
#[cfg(test)]
pub(super) fn build_certificate_gen_bound_type(c: &RobustnessGenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&d);
    let (f_id, f) = b.fresh_local(endo.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let (m_id, m_rat) = b.fresh_local(c.rat.clone());
    let (delta_id, delta) = b.fresh_local(c.rat.clone());
    // hypothesis 1: certified_robust d f eps
    let hyp_cert = Expr::apps(c.certified_robust.clone(), [d.clone(), f, eps.clone()]);
    let (h1_id, _) = b.fresh_local(hyp_cert.clone());
    // hypothesis 2: 0 < eps
    let hyp_eps = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h2_id, _) = b.fresh_local(hyp_eps.clone());
    // hypothesis 3: 0 < m_rat
    let hyp_m = c.rat_lt(c.rat_zero.clone(), m_rat.clone());
    let (h3_id, _) = b.fresh_local(hyp_m.clone());
    // hypothesis 4: 0 < delta
    let hyp_d = c.rat_lt(c.rat_zero.clone(), delta.clone());
    let (h4_id, _) = b.fresh_local(hyp_d.clone());
    // hypothesis 5: delta < 1
    let hyp_d1 = c.rat_lt(delta.clone(), c.rat_one.clone());
    let (h5_id, _) = b.fresh_local(hyp_d1.clone());
    // conclusion: gen_bound d eps m_rat delta <= explicit_bound
    let lhs = Expr::apps(
        c.gen_bound.clone(),
        [d.clone(), eps.clone(), m_rat.clone(), delta.clone()],
    );
    let two = c.two();
    // Rademacher term: 2*sqrt(d) / (eps*sqrt(m))
    let sqrt_d = Expr::app(c.sqrt.clone(), Expr::app(c.nat_to_rat.clone(), d));
    let sqrt_m = Expr::app(c.sqrt.clone(), m_rat.clone());
    let rademacher_term = c.div(c.mul(two.clone(), sqrt_d), c.mul(eps, sqrt_m));
    // Confidence term: sqrt(ln(2/delta) / (2*m))
    let confidence_num = Expr::app(c.ln.clone(), c.div(two.clone(), delta));
    let confidence_denom = c.mul(two, m_rat);
    let confidence_term = Expr::app(c.sqrt.clone(), c.div(confidence_num, confidence_denom));
    let rhs = c.add(rademacher_term, confidence_term);
    let concl = c.rat_le(lhs, rhs);
    let e = b.mk_pi(h5_id, BinderInfo::Default, hyp_d1, concl);
    let e = b.mk_pi(h4_id, BinderInfo::Default, hyp_d, e);
    let e = b.mk_pi(h3_id, BinderInfo::Default, hyp_m, e);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_eps, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_cert, e);
    let e = b.mk_pi(delta_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.RobustnessGen.tighter_cert_better_gen`:
/// ```text
/// forall (d : Nat) (eps1 eps2 m_rat delta : Rat),
///   0 < eps1 -> LE.le eps1 eps2 ->
///   0 < m_rat -> 0 < delta -> delta < 1 ->
///   LE.le (gen_bound d eps2 m_rat delta)
///         (gen_bound d eps1 m_rat delta)
/// ```
///
/// Monotonicity: a larger robustness radius (tighter certificate) implies
/// a smaller generalization bound. This follows from the 1/eps factor in
/// the Rademacher term.
#[cfg(test)]
pub(super) fn build_tighter_cert_better_gen_type(c: &RobustnessGenConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let (eps1_id, eps1) = b.fresh_local(c.rat.clone());
    let (eps2_id, eps2) = b.fresh_local(c.rat.clone());
    let (m_id, m_rat) = b.fresh_local(c.rat.clone());
    let (delta_id, delta) = b.fresh_local(c.rat.clone());
    // hypothesis 1: 0 < eps1
    let hyp_eps1 = c.rat_lt(c.rat_zero.clone(), eps1.clone());
    let (h1_id, _) = b.fresh_local(hyp_eps1.clone());
    // hypothesis 2: eps1 <= eps2
    let hyp_le = c.rat_le(eps1.clone(), eps2.clone());
    let (h2_id, _) = b.fresh_local(hyp_le.clone());
    // hypothesis 3: 0 < m_rat
    let hyp_m = c.rat_lt(c.rat_zero.clone(), m_rat.clone());
    let (h3_id, _) = b.fresh_local(hyp_m.clone());
    // hypothesis 4: 0 < delta
    let hyp_d = c.rat_lt(c.rat_zero.clone(), delta.clone());
    let (h4_id, _) = b.fresh_local(hyp_d.clone());
    // hypothesis 5: delta < 1
    let hyp_d1 = c.rat_lt(delta.clone(), c.rat_one.clone());
    let (h5_id, _) = b.fresh_local(hyp_d1.clone());
    // conclusion: gen_bound d eps2 m_rat delta <= gen_bound d eps1 m_rat delta
    let bound_eps2 = Expr::apps(
        c.gen_bound.clone(),
        [d.clone(), eps2, m_rat.clone(), delta.clone()],
    );
    let bound_eps1 = Expr::apps(c.gen_bound.clone(), [d, eps1, m_rat, delta]);
    let concl = c.rat_le(bound_eps2, bound_eps1);
    let e = b.mk_pi(h5_id, BinderInfo::Default, hyp_d1, concl);
    let e = b.mk_pi(h4_id, BinderInfo::Default, hyp_d, e);
    let e = b.mk_pi(h3_id, BinderInfo::Default, hyp_m, e);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_le, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_eps1, e);
    let e = b.mk_pi(delta_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(eps2_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(eps1_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
