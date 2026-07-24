// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL pre-build — K3 layer: the √-killer `BoolAnalysis.am_gm_linearize`.
//!
//! The two-term AM–GM inequality, stated MULTIPLICATIVELY (no division) so it
//! is exactly `Rat`-expressible and consumes no field-inverse axioms:
//!
//! ```text
//! BoolAnalysis.am_gm_linearize : ∀ A s : Rat,
//!   (1+1)·(s·A) ≤ A·A + s·s
//! ```
//!
//! This replaces every "take square roots" step in the classical KKL write-up:
//! the inequality `2·s·A ≤ A² + s²` is the linearized, root-free shadow of
//! `(A−s)² ≥ 0`. No positivity hypothesis on `s` is needed — the bound holds for
//! ALL `A, s` because it is just `(A−s)·(A−s) ≥ 0` expanded.
//!
//! ## Proof (constructive, empty domain-axiom closure)
//!
//! Write `D := A − s`, `P := (1+1)·(s·A)`.
//!
//! 1. `Rat.sq_nonneg D : 0 ≤ D·D`.
//! 2. `Rat.sub_sq A s : D·D = (A·A + (1+1)·(A·(−s))) + s·s`.
//! 3. Ring-rewrite the RHS of (2) into `(A·A + s·s) − P`:
//!    - `A·(−s) = −(A·s)`               [`Rat.mul_neg`]
//!    - `(1+1)·(−(A·s)) = −((1+1)·(A·s))` [`Rat.mul_neg`]
//!    - `A·s = s·A`                     [`Rat.mul_comm`], lifted through the
//!      `(1+1)·_` and the outer `Rat.neg`, giving
//!      `(1+1)·(A·(−s)) = −P`.
//!    - regroup `(A·A + (−P)) + s·s = (A·A + s·s) + (−P)` via
//!      `Rat.add_assoc` / `Rat.add_comm`. The result is DEFINITIONALLY
//!      `(A·A + s·s) − P` (reducible `Rat.sub`).
//! 4. `Eq.subst` transports (1) along the chained equation `D·D = (A·A+s·s)−P`
//!    under motive `λ z, 0 ≤ z`, yielding `0 ≤ (A·A + s·s) − P`.
//! 5. `Rat.le_of_sub_nonneg P (A·A+s·s)` discharges it to `P ≤ A·A + s·s`.
//!
//! Every dependency (`Rat.sq_nonneg`, `Rat.sub_sq`, `Rat.mul_neg`,
//! `Rat.mul_comm`, `Rat.add_assoc`, `Rat.add_comm`, `Rat.le_of_sub_nonneg`) is
//! itself `ProofQuality::Constructive` with empty closure, so `am_gm_linearize`
//! is too.

use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// `congrArg.{1,1} Rat Rat x y f h : f x = f y` (for `f : Rat → Rat`).
///
/// `RingConsts` exposes `cong_left`/`cong_right` over binary ops; for the unary
/// `Rat.neg` rewrite we use `congrArg` directly with a `λ w, Rat.neg w` lift.
fn cong_neg(c: &RingConsts, parent: &EnvDeclBuilder, x: Expr, y: Expr, h: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]);
    let neg_c = Expr::const_(Name::from_string("Rat.neg"), vec![]);
    let f = {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = ch.fresh_local(c.rat());
        let body = Expr::app(neg_c.clone(), w);
        let lam = ch.mk_lam(w_id, BinderInfo::Default, c.rat(), body);
        ch.finish_child(lam)
    };
    Expr::apps(congr_arg, [c.rat(), c.rat(), x, y, f, h])
}

impl Environment {
    /// `BoolAnalysis.am_gm_linearize : ∀ A s : Rat,`
    /// `  LE.le ((1+1)·(s·A)) (A·A + s·s)`.
    ///
    /// The K3 √-killer. Idempotent. Constructive, empty axiom closure.
    pub fn register_am_gm_linearize(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.am_gm_linearize");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Brings in Rat.sq_nonneg, Rat.sub_sq, Rat.mul_neg, Rat.mul_comm,
        // Rat.add_assoc, Rat.add_comm (order toolkit + ring identities) and,
        // transitively, Rat.le_of_sub_nonneg (nn_verify_rat_ordering).
        self.init_boolean_analysis_ring_identities()?;

        let c = RingConsts::new();

        let two = c.two(); // 1+1
        let prod_term = |a: &Expr, s: &Expr| c.mul(two.clone(), c.mul(s.clone(), a.clone())); // (1+1)·(s·A)
        let sum_sq =
            |a: &Expr, s: &Expr| c.add(c.mul(a.clone(), a.clone()), c.mul(s.clone(), s.clone())); // A·A + s·s

        // Type: ∀ A s, LE.le ((1+1)·(s·A)) (A·A + s·s)
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat());
            let (s_id, s) = b.fresh_local(c.rat());
            let body = c.o.rat_le(prod_term(&a, &s), sum_sq(&a, &s));
            let e = b.mk_pi(s_id, BinderInfo::Default, c.rat(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat(), e);
            b.finish(e)
        };

        let value = build_am_gm_linearize_proof(&c);

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

/// Build the proof term for `BoolAnalysis.am_gm_linearize`.
fn build_am_gm_linearize_proof(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat());
    let (s_id, s) = b.fresh_local(c.rat());

    let two = c.two();
    let add_c = c.add_const();
    let mul_c = c.mul_const();

    // Atoms.
    let aa = c.mul(a.clone(), a.clone()); // A·A
    let ss = c.mul(s.clone(), s.clone()); // s·s
    let neg_s = c.neg(s.clone()); // −s
    let a_negs = c.mul(a.clone(), neg_s.clone()); // A·(−s)
    let a_s = c.mul(a.clone(), s.clone()); // A·s
    let s_a = c.mul(s.clone(), a.clone()); // s·A
    let p = c.mul(two.clone(), s_a.clone()); // P = (1+1)·(s·A)
    let two_a_s = c.mul(two.clone(), a_s.clone()); // (1+1)·(A·s)
    let two_a_negs = c.mul(two.clone(), a_negs.clone()); // (1+1)·(A·(−s))
    let neg_p = c.neg(p.clone()); // −P
    let neg_two_a_s = c.neg(two_a_s.clone()); // −((1+1)·(A·s))

    // h0 : 0 ≤ D·D   where D = A − s,  D·D = (A−s)·(A−s).
    let d = c.sub(a.clone(), s.clone());
    let dd = c.mul(d.clone(), d.clone());
    let sq_nonneg = Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]);
    let h0 = Expr::app(sq_nonneg, d.clone()); // 0 ≤ (A−s)·(A−s)

    // h_sub_sq : D·D = (A·A + (1+1)·(A·(−s))) + s·s.
    let sub_sq = Expr::const_(Name::from_string("Rat.sub_sq"), vec![]);
    let h_sub_sq = Expr::apps(sub_sq, [a.clone(), s.clone()]);
    let rhs0_inner = c.add(aa.clone(), two_a_negs.clone()); // A·A + (1+1)·(A·(−s))
    let rhs0 = c.add(rhs0_inner.clone(), ss.clone()); // (A·A + (1+1)·(A·(−s))) + s·s

    // ── hcross : (1+1)·(A·(−s)) = −P ────────────────────────────────────────
    // step a: A·(−s) = −(A·s)            [Rat.mul_neg A s]
    let mul_neg = Expr::const_(Name::from_string("Rat.mul_neg"), vec![]);
    let h_an = Expr::apps(mul_neg.clone(), [a.clone(), s.clone()]); // A·(−s) = −(A·s)
    let neg_a_s = c.neg(a_s.clone()); // −(A·s)
                                      // lift through (1+1)·_ : (1+1)·(A·(−s)) = (1+1)·(−(A·s))
    let two_neg_a_s = c.mul(two.clone(), neg_a_s.clone());
    let c_lift_a = c.cong_right(
        &b,
        &mul_c,
        a_negs.clone(),
        neg_a_s.clone(),
        two.clone(),
        h_an,
    );
    // step b: (1+1)·(−(A·s)) = −((1+1)·(A·s))   [Rat.mul_neg (1+1) (A·s)]
    let h_two_neg = Expr::apps(mul_neg, [two.clone(), a_s.clone()]);
    // chain so far: (1+1)·(A·(−s)) = −((1+1)·(A·s))
    let h_step_ab = c.trans(
        two_a_negs.clone(),
        two_neg_a_s.clone(),
        neg_two_a_s.clone(),
        c_lift_a,
        h_two_neg,
    );
    // step c: A·s = s·A   [Rat.mul_comm A s]; lift to (1+1)·(A·s) = (1+1)·(s·A) = P
    let h_comm = c.mcomm(a.clone(), s.clone()); // A·s = s·A
    let c_lift_two = c.cong_right(&b, &mul_c, a_s.clone(), s_a.clone(), two.clone(), h_comm);
    // negate: −((1+1)·(A·s)) = −P
    let h_neg_p = cong_neg(c, &b, two_a_s.clone(), p.clone(), c_lift_two);
    // hcross : (1+1)·(A·(−s)) = −P
    let hcross = c.trans(
        two_a_negs.clone(),
        neg_two_a_s.clone(),
        neg_p.clone(),
        h_step_ab,
        h_neg_p,
    );

    // ── rewrite RHS0 : (A·A + (1+1)·(A·(−s))) + s·s = (A·A + (−P)) + s·s ─────
    // lift hcross through the inner (A·A + _) : (A·A + (1+1)·(A·(−s))) = (A·A + (−P))
    let aa_negp = c.add(aa.clone(), neg_p.clone()); // A·A + (−P)
    let cong_inner = c.cong_right(
        &b,
        &add_c,
        two_a_negs.clone(),
        neg_p.clone(),
        aa.clone(),
        hcross,
    );
    // lift through the outer (_ + s·s) : RHS0 = (A·A + (−P)) + s·s
    let rhs1 = c.add(aa_negp.clone(), ss.clone()); // (A·A + (−P)) + s·s
    let cong_outer = c.cong_left(
        &b,
        &add_c,
        rhs0_inner.clone(),
        aa_negp.clone(),
        ss.clone(),
        cong_inner,
    );

    // ── regroup : (A·A + (−P)) + s·s = (A·A + s·s) + (−P) ────────────────────
    // r1 : (A·A + (−P)) + s·s = A·A + ((−P) + s·s)      [add_assoc A·A (−P) s·s]
    let negp_ss = c.add(neg_p.clone(), ss.clone()); // (−P) + s·s
    let mid_assoc = c.add(aa.clone(), negp_ss.clone()); // A·A + ((−P) + s·s)
    let r1 = c.aassoc(aa.clone(), neg_p.clone(), ss.clone());
    // r2 : (−P) + s·s = s·s + (−P)   [add_comm], lift through (A·A + _)
    let ss_negp = c.add(ss.clone(), neg_p.clone()); // s·s + (−P)
    let h_acomm = c.acomm(neg_p.clone(), ss.clone());
    let mid_assoc2 = c.add(aa.clone(), ss_negp.clone()); // A·A + (s·s + (−P))
    let r2 = c.cong_right(
        &b,
        &add_c,
        negp_ss.clone(),
        ss_negp.clone(),
        aa.clone(),
        h_acomm,
    );
    // r3 : A·A + (s·s + (−P)) = (A·A + s·s) + (−P)   [symm (add_assoc A·A s·s (−P))]
    let aa_ss = c.add(aa.clone(), ss.clone()); // A·A + s·s
    let target = c.add(aa_ss.clone(), neg_p.clone()); // (A·A + s·s) + (−P)  ≡  (A·A+s·s) − P
    let r3_fwd = c.aassoc(aa.clone(), ss.clone(), neg_p.clone()); // (A·A+s·s)+(−P) = A·A+(s·s+(−P))
    let r3 = c.symm(target.clone(), mid_assoc2.clone(), r3_fwd);
    // regroup chain: rhs1 = mid_assoc = mid_assoc2 = target
    let reg1 = c.trans(rhs1.clone(), mid_assoc.clone(), mid_assoc2.clone(), r1, r2);
    let regroup = c.trans(rhs1.clone(), mid_assoc2.clone(), target.clone(), reg1, r3);

    // ── full ring chain : D·D = (A·A + s·s) + (−P) ─────────────────────────
    // D·D = RHS0 = rhs1 = target.
    let chain1 = c.trans(dd.clone(), rhs0.clone(), rhs1.clone(), h_sub_sq, cong_outer);
    let hring = c.trans(dd.clone(), rhs1.clone(), target.clone(), chain1, regroup);

    // ── transport h0 : 0 ≤ D·D  along hring  to  0 ≤ (A·A+s·s)+(−P) ─────────
    // motive : λ z, 0 ≤ z
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = ch.fresh_local(c.rat());
        let body = c.o.rat_le(c.o.rat_zero.clone(), z);
        let lam = ch.mk_lam(z_id, BinderInfo::Default, c.rat(), body);
        ch.finish_child(lam)
    };
    let h_le_sub = c.o.subst(motive, dd.clone(), target.clone(), hring, h0);

    // ── le_of_sub_nonneg : (A·A+s·s) + (−P) ≡ (A·A+s·s) − P,  so P ≤ A·A+s·s ──
    // Rat.le_of_sub_nonneg a b : 0 ≤ b − a → a ≤ b.  Here a = P, b = A·A + s·s,
    // and `b − a` δ-reduces to `(A·A+s·s) + (−P)` = target, so `h_le_sub`
    // (type `0 ≤ target`) inhabits `0 ≤ b − a` by def-eq on reducible Rat.sub.
    let le_of_sub_nonneg = Expr::const_(Name::from_string("Rat.le_of_sub_nonneg"), vec![]);
    let body = Expr::apps(le_of_sub_nonneg, [p.clone(), aa_ss.clone(), h_le_sub]);

    let e = b.mk_lam(s_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_am_gm_linearize_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_am_gm_linearize()
            .expect("register_am_gm_linearize");
        let name = Name::from_string("BoolAnalysis.am_gm_linearize");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("am_gm_linearize proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "am_gm_linearize must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "am_gm_linearize's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_am_gm_linearize_idempotent() {
        let mut env = Environment::new();
        env.register_am_gm_linearize().expect("first");
        env.register_am_gm_linearize().expect("second (idempotent)");
    }
}
