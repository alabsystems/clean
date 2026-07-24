// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the per-term Lagrange identity (Cauchy-Schwarz
//! keystone, scalar layer).
//!
//! `Rat.lagrange_term : ∀ (p q r s : Rat),
//!     (p·s − q·r)·(p·s − q·r)
//!       = (((p·p)·(s·s)) + (1+1)·(Rat.neg ((p·r)·(q·s)))) + ((q·q)·(r·r))`
//!
//! The single-coordinate-pair expansion of the cross-difference square. With
//! `p=aᵢ, q=aⱼ, r=bᵢ, s=bⱼ`, the cross term `aᵢbⱼ − aⱼbᵢ` squares to
//! `aᵢ²bⱼ² + aⱼ²bᵢ² − 2(aᵢbᵢ)(aⱼbⱼ)`, where the three products are written in
//! the `(outer-i)·(inner-j)` form `Fin.sum_mul_sum` consumes:
//! `(p·p)·(s·s)`, `(q·q)·(r·r)`, and `(p·r)·(q·s)`.
//!
//! Built from `Rat.sub_sq` (the `(x−y)²` expansion) followed by three
//! 4-factor regroups via `Rat.mul_mul_mul_comm` (`(a·b)·(c·d) = (a·c)·(b·d)`)
//! and `Rat.mul_neg`, lifted over the surrounding `Rat.add` structure with the
//! `RingConsts` congruence smart-constructors. Every dependency is
//! `ProofQuality::Constructive` (empty domain-axiom closure), so is this lemma.

use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register `Rat.lagrange_term`. Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_rat_lagrange_term(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lagrange_term");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_ring_identities()?; // Rat.sub_sq + ring surface
        self.register_rat_mul_mul_mul_comm_theorem()?;

        let c = RingConsts::new();
        let mmmc = Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]);
        let (ty, value) = build_lagrange_term(&c, &mmmc);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
fn mmmc4(mmmc: &Expr, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
    Expr::apps(mmmc.clone(), [a, b, cc, d])
}

/// `congrArg Rat.neg h : Rat.neg x = Rat.neg y`  from `h : x = y` over `Rat`.
fn cong_neg(c: &RingConsts, x: Expr, y: Expr, h: Expr) -> Expr {
    use crate::level::Level;
    let u1 = Level::succ(Level::zero());
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]);
    let neg_c = Expr::const_(Name::from_string("Rat.neg"), vec![]);
    Expr::apps(congr_arg, [c.rat(), c.rat(), x, y, neg_c, h])
}

/// Build the type + proof of `Rat.lagrange_term`.
fn build_lagrange_term(c: &RingConsts, mmmc: &Expr) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (p_id, p) = b.fresh_local(c.rat());
        let (q_id, q) = b.fresh_local(c.rat());
        let (r_id, r) = b.fresh_local(c.rat());
        let (s_id, s) = b.fresh_local(c.rat());
        let lhs = lhs_of(c, &p, &q, &r, &s);
        let rhs = rhs_of(c, &p, &q, &r, &s);
        let body = c.eq(lhs, rhs);
        let e = b.mk_pi(s_id, BinderInfo::Default, c.rat(), body);
        let e = b.mk_pi(r_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(q_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(p_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (p_id, p) = b.fresh_local(c.rat());
        let (q_id, q) = b.fresh_local(c.rat());
        let (r_id, r) = b.fresh_local(c.rat());
        let (s_id, s) = b.fresh_local(c.rat());
        let body = build_proof(c, mmmc, &b, &p, &q, &r, &s);
        let e = b.mk_lam(s_id, BinderInfo::Default, c.rat(), body);
        let e = b.mk_lam(r_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(q_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(p_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    (ty, value)
}

/// `(p·s − q·r)·(p·s − q·r)`.
fn lhs_of(c: &RingConsts, p: &Expr, q: &Expr, r: &Expr, s: &Expr) -> Expr {
    let ps = c.mul(p.clone(), s.clone());
    let qr = c.mul(q.clone(), r.clone());
    let d = c.sub(ps, qr);
    c.mul(d.clone(), d)
}

/// `(((p·p)·(s·s)) + (1+1)·(−((p·r)·(q·s)))) + ((q·q)·(r·r))`.
fn rhs_of(c: &RingConsts, p: &Expr, q: &Expr, r: &Expr, s: &Expr) -> Expr {
    let pp_ss = c.mul(c.mul(p.clone(), p.clone()), c.mul(s.clone(), s.clone()));
    let qq_rr = c.mul(c.mul(q.clone(), q.clone()), c.mul(r.clone(), r.clone()));
    let pr_qs = c.mul(c.mul(p.clone(), r.clone()), c.mul(q.clone(), s.clone()));
    let two_neg = c.nmul(c.two(), c.neg(pr_qs));
    c.add(c.add(pp_ss, two_neg), qq_rr)
}

/// The proof body: `lhs = rhs` for FREE `p q r s`.
///
/// Step A — `Rat.sub_sq (p·s) (q·r)`:
///   `lhs = (((ps)·(ps)) + 2·((ps)·(−(qr)))) + ((qr)·(qr))`  =: E0
/// Step B — regroup `(ps)·(ps) → (p·p)·(s·s)`  (`mmmc p s p s`).
/// Step C — regroup `(qr)·(qr) → (q·q)·(r·r)`  (`mmmc q r q r`).
/// Step D — the cross term `2·((ps)·(−(qr)))`:
///   D1 `mul_neg (ps) (qr)` : `(ps)·(−(qr)) = −((ps)·(qr))`.
///   D2 regroup `(ps)·(qr) → (p·r)·(q·s)` via
///       `(ps)(qr) =[cong qr=rq]= (ps)(rq) =[mmmc p s r q]= (pr)(sq)
///        =[cong sq=qs]= (pr)(qs)`.
///   So `(ps)·(−(qr)) = −((pr)(qs))`, hence `2·((ps)·(−(qr))) = 2·(−((pr)(qs)))`.
/// All three rewrites are lifted over the `(_ + _) + _` skeleton with the
/// `RingConsts` congruences and chained with `Eq.trans`.
fn build_proof(
    c: &RingConsts,
    mmmc: &Expr,
    b: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    r: &Expr,
    s: &Expr,
) -> Expr {
    let add_c = c.add_const();
    let ps = c.mul(p.clone(), s.clone());
    let qr = c.mul(q.clone(), r.clone());
    let sub_sq = Expr::const_(Name::from_string("Rat.sub_sq"), vec![]);

    // ── Step A: sub_sq (ps) (qr) ──
    // E0 := (((ps)·(ps)) + 2·((ps)·(−(qr)))) + ((qr)·(qr))
    let ps_ps = c.mul(ps.clone(), ps.clone());
    let neg_qr = c.neg(qr.clone());
    let ps_negqr = c.mul(ps.clone(), neg_qr.clone());
    let two_ps_negqr = c.nmul(c.two(), ps_negqr.clone());
    let qr_qr = c.mul(qr.clone(), qr.clone());
    let head0 = c.add(ps_ps.clone(), two_ps_negqr.clone()); // (ps·ps) + 2·(ps·(−qr))
    let e0 = c.add(head0.clone(), qr_qr.clone());
    let step_a = Expr::apps(sub_sq, [ps.clone(), qr.clone()]); // lhs = E0

    // ── Step B: (ps·ps) → (p·p)·(s·s)  [mmmc p s p s] ──
    let pp_ss = c.mul(c.mul(p.clone(), p.clone()), c.mul(s.clone(), s.clone()));
    let h_b = mmmc4(mmmc, p.clone(), s.clone(), p.clone(), s.clone()); // (ps)(ps)=(pp)(ss)
                                                                       // lift over head0's left addend, then over the outer left addend.
    let head_b = c.add(pp_ss.clone(), two_ps_negqr.clone());
    let cong_b_head = c.cong_left(
        b,
        &add_c,
        ps_ps.clone(),
        pp_ss.clone(),
        two_ps_negqr.clone(),
        h_b,
    );
    let e_b = c.add(head_b.clone(), qr_qr.clone());
    let step_b = c.cong_left(
        b,
        &add_c,
        head0.clone(),
        head_b.clone(),
        qr_qr.clone(),
        cong_b_head,
    );

    // ── Step C: (qr·qr) → (q·q)·(r·r)  [mmmc q r q r] ──
    let qq_rr = c.mul(c.mul(q.clone(), q.clone()), c.mul(r.clone(), r.clone()));
    let h_c = mmmc4(mmmc, q.clone(), r.clone(), q.clone(), r.clone()); // (qr)(qr)=(qq)(rr)
    let e_c = c.add(head_b.clone(), qq_rr.clone());
    let step_c = c.cong_right(b, &add_c, qr_qr.clone(), qq_rr.clone(), head_b.clone(), h_c);

    // ── Step D: 2·((ps)·(−qr)) → 2·(−((pr)(qs))) ──
    // D1: (ps)·(−qr) = −((ps)·(qr))   [mul_neg (ps) (qr)]
    let ps_qr = c.mul(ps.clone(), qr.clone());
    let neg_ps_qr = c.neg(ps_qr.clone());
    let h_d1 = c.mneg(ps.clone(), qr.clone()); // (ps)·(−qr) = −((ps)·(qr))
                                               // D2: (ps)·(qr) = (p·r)·(q·s) via cong-mmmc-cong
    let pr_qs = c.mul(c.mul(p.clone(), r.clone()), c.mul(q.clone(), s.clone()));
    let h_d2 = build_cross_regroup(c, mmmc, b, p, q, r, s);
    // congrArg Rat.neg on h_d2: −((ps)(qr)) = −((pr)(qs))
    let neg_pr_qs = c.neg(pr_qs.clone());
    let h_d2_neg = cong_neg(c, ps_qr.clone(), pr_qs.clone(), h_d2);
    // chain h_d1 ; h_d2_neg : (ps)·(−qr) = −((pr)(qs))
    let h_d = c.trans(
        ps_negqr.clone(),
        neg_ps_qr.clone(),
        neg_pr_qs.clone(),
        h_d1,
        h_d2_neg,
    );
    // congrArg (2·_) : 2·((ps)·(−qr)) = 2·(−((pr)(qs)))
    let two = c.two();
    let mul_c = c.mul_const();
    let two_neg_prqs = c.nmul(two.clone(), neg_pr_qs.clone());
    let step_d_inner = c.cong_right(
        b,
        &mul_c,
        ps_negqr.clone(),
        neg_pr_qs.clone(),
        two.clone(),
        h_d,
    );
    // lift over head_b's right addend (fixed (pp)(ss)), then over outer (fixed (qq)(rr))
    let head_d = c.add(pp_ss.clone(), two_neg_prqs.clone());
    let cong_d_head = c.cong_right(
        b,
        &add_c,
        two_ps_negqr.clone(),
        two_neg_prqs.clone(),
        pp_ss.clone(),
        step_d_inner,
    );
    let e_d = c.add(head_d.clone(), qq_rr.clone());
    let step_d = c.cong_left(
        b,
        &add_c,
        head_b.clone(),
        head_d.clone(),
        qq_rr.clone(),
        cong_d_head,
    );

    // ── chain: lhs = E0 = E_b = E_c = E_d ──
    let lhs = lhs_of(c, p, q, r, s);
    let t_ab = c.trans(lhs.clone(), e0.clone(), e_b.clone(), step_a, step_b);
    let t_abc = c.trans(lhs.clone(), e_b.clone(), e_c.clone(), t_ab, step_c);
    c.trans(lhs, e_c, e_d, t_abc, step_d)
}

/// Proof of `(p·s)·(q·r) = (p·r)·(q·s)` via
/// `(ps)(qr) =[cong qr=rq]= (ps)(rq) =[mmmc p s r q]= (pr)(sq) =[cong sq=qs]= (pr)(qs)`.
fn build_cross_regroup(
    c: &RingConsts,
    mmmc: &Expr,
    b: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    r: &Expr,
    s: &Expr,
) -> Expr {
    let mul_c = c.mul_const();
    let ps = c.mul(p.clone(), s.clone());
    let qr = c.mul(q.clone(), r.clone());
    let rq = c.mul(r.clone(), q.clone());
    let sq = c.mul(s.clone(), q.clone());
    let qs = c.mul(q.clone(), s.clone());
    let pr = c.mul(p.clone(), r.clone());

    let ps_qr = c.mul(ps.clone(), qr.clone());
    let ps_rq = c.mul(ps.clone(), rq.clone());
    let pr_sq = c.mul(pr.clone(), sq.clone());
    let pr_qs = c.mul(pr.clone(), qs.clone());

    // cong1: (ps)·(qr) = (ps)·(rq)   [qr = rq via mcomm q r, fixed left ps]
    let h_qr = c.mcomm(q.clone(), r.clone()); // q·r = r·q
    let cong1 = c.cong_right(b, &mul_c, qr.clone(), rq.clone(), ps.clone(), h_qr);
    // mmmc p s r q : (ps)·(rq) = (pr)·(sq)
    let h_mmmc = mmmc4(mmmc, p.clone(), s.clone(), r.clone(), q.clone());
    // cong3: (pr)·(sq) = (pr)·(qs)   [sq = qs via mcomm s q, fixed left pr]
    let h_sq = c.mcomm(s.clone(), q.clone()); // s·q = q·s
    let cong3 = c.cong_right(b, &mul_c, sq.clone(), qs.clone(), pr.clone(), h_sq);

    // chain: ps_qr = ps_rq = pr_sq = pr_qs
    let t1 = c.trans(ps_qr.clone(), ps_rq.clone(), pr_sq.clone(), cong1, h_mmmc);
    c.trans(ps_qr, pr_sq, pr_qs, t1, cong3)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::Expr;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_rat_lagrange_term()
            .expect("register_rat_lagrange_term should succeed");
        env
    }

    #[test]
    fn test_lagrange_term_type_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("Rat.lagrange_term"),
                vec![],
            ))
            .expect("Rat.lagrange_term should type-check");
    }

    #[test]
    fn test_lagrange_term_constructive_axiom_free() {
        let env = env();
        let name = Name::from_string("Rat.lagrange_term");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}
