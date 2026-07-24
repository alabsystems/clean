// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL pre-build — K4 building block: strict left-add monotonicity.
//!
//! The missing strict-order primitive the K4 pigeonhole (`Fin.sum_lt_sum`) and
//! the broader KKL assault need:
//!
//! ```text
//! Rat.add_lt_add_left : ∀ a b c : Rat, a < b → (c + a) < (c + b)
//! ```
//!
//! `Rat.lt` is a `Quot.lift` and is NEVER reduced for variable arguments — all
//! strict-order reasoning goes through `Rat.lt_iff_le_not_le` propositionally,
//! exactly as in the B1c/B1d layers.
//!
//! ## Proof (constructive, empty domain-axiom closure)
//!
//! From `h : a < b`, `Iff.mp (lt_iff a b) h : (a ≤ b) ∧ ¬(b ≤ a)`.
//!
//! - le-half:  `Rat.add_le_add_left a b (And.left …) c : (c+a) ≤ (c+b)`.
//! - not-le half: `λ (hc : (c+b) ≤ (c+a))`, push `(−c)+_` on the left via
//!   `Rat.add_le_add_left (c+b) (c+a) hc (−c) : (−c)+(c+b) ≤ (−c)+(c+a)`, then
//!   rewrite each side `(−c)+(c+x) = x` (symm `add_assoc` → `add_left_neg` →
//!   `zero_add`, via `Eq.subst`) to get `b ≤ a`, contradicting `And.right …`.
//! - `Iff.mpr (lt_iff (c+a)(c+b)) (And.intro le-half not-le-half)`.
//!
//! Dependencies (`Rat.lt_iff_le_not_le`, `Rat.add_le_add_left`,
//! `Rat.add_assoc`, `Rat.add_left_neg`, `Rat.zero_add`) are all `Constructive`
//! with empty closure, so `Rat.add_lt_add_left` is too.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

// ── Small Prop / Iff / And plumbing (mirrors the B1c/B1d layers) ───────────

fn rat_lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
}
fn not_(p: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p)
}
fn and_(p: Expr, q: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q])
}
fn and_intro(p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [p, q, hp, hq],
    )
}
fn and_left(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [p, q, h],
    )
}
fn and_right(p: Expr, q: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("And.right"), vec![]),
        [p, q, h],
    )
}
fn iff_mp(lhs: Expr, rhs: Expr, hiff: Expr, hlhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Iff.mp"), vec![]),
        [lhs, rhs, hiff, hlhs],
    )
}
fn iff_mpr(lhs: Expr, rhs: Expr, hiff: Expr, hrhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Iff.mpr"), vec![]),
        [lhs, rhs, hiff, hrhs],
    )
}
fn lt_iff(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]),
        [a, b],
    )
}
fn lt_rhs(c: &OrderConsts, a: Expr, b: Expr) -> Expr {
    and_(c.rat_le(a.clone(), b.clone()), not_(c.rat_le(b, a)))
}

impl Environment {
    /// `Rat.add_lt_add_left : ∀ a b c : Rat, a < b → (c + a) < (c + b)`.
    ///
    /// Strict left-add monotonicity. Kernel-checked, constructive, empty
    /// closure. Idempotent.
    pub fn register_rat_add_lt_add_left(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_lt_add_left");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Brings in lt_iff (order toolkit B1b/B1c chain) + add_le_add_left,
        // add_assoc, add_left_neg, zero_add (interval-arith / field surface).
        self.init_boolean_analysis_order_toolkit()?;

        let c = OrderConsts::new();
        let ty = add_lt_add_left_type(&c);
        let value = build_add_lt_add_left_proof(&c);

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

/// Type `∀ a b c, Rat.lt a b → Rat.lt (c+a) (c+b)`.
fn add_lt_add_left_type(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ty = rat_lt(a.clone(), bv.clone());
    let concl = rat_lt(c.add(cv.clone(), a.clone()), c.add(cv.clone(), bv.clone()));
    let (h_id, _) = b.fresh_local(h_ty.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `Rat.add_le_add_left x y h z : Rat.le (z+x) (z+y)`.
fn add_le_add_left(x: Expr, y: Expr, h: Expr, z: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_le_add_left"), vec![]),
        [x, y, h, z],
    )
}

/// `h_simp : (−z) + (z + w) = w`, built from `add_assoc` / `add_left_neg` /
/// `zero_add` (chained through `Eq.subst`).
///
/// `(−z)+(z+w) = ((−z)+z)+w`  [symm (add_assoc (−z) z w)]
///            = 0 + w          [add_left_neg z, lifted over `_ + w`]
///            = w              [zero_add w]
fn neg_cancel_left(c: &OrderConsts, parent: &EnvDeclBuilder, z: &Expr, w: &Expr) -> Expr {
    let neg_z = c.neg(z.clone());
    let negz_z = c.add(neg_z.clone(), z.clone()); // (−z)+z
    let negz_zw = c.add(neg_z.clone(), c.add(z.clone(), w.clone())); // (−z)+(z+w)
    let regrouped = c.add(negz_z.clone(), w.clone()); // ((−z)+z)+w
    let zero_w = c.add(c.rat_zero.clone(), w.clone()); // 0+w

    // s0 : (−z)+(z+w) = ((−z)+z)+w   [symm (add_assoc (−z) z w)]
    // add_assoc (−z) z w : ((−z)+z)+w = (−z)+(z+w)  ≡  regrouped = negz_zw,
    // so symm(regrouped, negz_zw, h_assoc) : negz_zw = regrouped.
    let add_assoc = Expr::const_(Name::from_string("Rat.add_assoc"), vec![]);
    let h_assoc = Expr::apps(add_assoc, [neg_z.clone(), z.clone(), w.clone()]);
    let s0 = c.symm(regrouped.clone(), negz_zw.clone(), h_assoc);

    // h_lneg : (−z)+z = 0   [add_left_neg z]
    let add_left_neg = Expr::const_(Name::from_string("Rat.add_left_neg"), vec![]);
    let h_lneg = Expr::app(add_left_neg, z.clone());
    // lift over `_ + w` via Eq.subst, motive λ t, ((−z)+(z+w)) = (t + w)
    let motive1 = {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = ch.fresh_local(c.rat.clone());
        let body = c.rat_eq(negz_zw.clone(), c.add(t, w.clone()));
        ch.finish_child(ch.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // subst motive1 (−z+z) 0 h_lneg s0 : ((−z)+(z+w)) = (0 + w)
    let s1 = c.subst(motive1, negz_z.clone(), c.rat_zero.clone(), h_lneg, s0);

    // h_zadd : 0 + w = w   [zero_add w]
    let zero_add = Expr::const_(Name::from_string("Rat.zero_add"), vec![]);
    let h_zadd = Expr::app(zero_add, w.clone());
    // lift via Eq.subst, motive λ t, ((−z)+(z+w)) = t
    let motive2 = {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = ch.fresh_local(c.rat.clone());
        let body = c.rat_eq(negz_zw.clone(), t);
        ch.finish_child(ch.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst(motive2, zero_w, w.clone(), h_zadd, s1)
}

/// Build the proof term for `Rat.add_lt_add_left`.
fn build_add_lt_add_left_proof(c: &OrderConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_ty = rat_lt(a.clone(), bv.clone());
    let (h_id, h) = b.fresh_local(h_ty.clone());

    // mp h : (a ≤ b) ∧ ¬(b ≤ a)
    let rhs_ab = lt_rhs(c, a.clone(), bv.clone());
    let mp = iff_mp(
        rat_lt(a.clone(), bv.clone()),
        rhs_ab,
        lt_iff(a.clone(), bv.clone()),
        h,
    );
    let le_ab = c.rat_le(a.clone(), bv.clone());
    let not_le_ba = not_(c.rat_le(bv.clone(), a.clone()));
    let h_le_ab = and_left(le_ab.clone(), not_le_ba.clone(), mp.clone()); // a ≤ b
    let h_not_le_ba = and_right(le_ab.clone(), not_le_ba.clone(), mp); // ¬(b ≤ a)

    let ca = c.add(cv.clone(), a.clone()); // c+a
    let cb = c.add(cv.clone(), bv.clone()); // c+b

    // le-half: (c+a) ≤ (c+b)   [add_le_add_left a b h_le_ab c]
    let h_le_cacb = add_le_add_left(a.clone(), bv.clone(), h_le_ab, cv.clone());

    // not-le half: λ (hc : (c+b) ≤ (c+a)) => h_not_le_ba (b ≤ a)
    let le_cbca = c.rat_le(cb.clone(), ca.clone());
    let not_le_half = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (hc_id, hc) = ch.fresh_local(le_cbca.clone());
        let neg_c = c.neg(cv.clone());
        // push (−c)+_ : (−c)+(c+b) ≤ (−c)+(c+a)
        let h_pushed = add_le_add_left(cb.clone(), ca.clone(), hc, neg_c.clone());
        let negc_cb = c.add(neg_c.clone(), cb.clone()); // (−c)+(c+b)
        let negc_ca = c.add(neg_c.clone(), ca.clone()); // (−c)+(c+a)

        // h_simp_b : (−c)+(c+b) = b ;  h_simp_a : (−c)+(c+a) = a
        let h_simp_b = neg_cancel_left(c, &ch, &cv, &bv);
        let h_simp_a = neg_cancel_left(c, &ch, &cv, &a);

        // rewrite LHS endpoint: ((−c)+(c+b)) ≤ ((−c)+(c+a))  ⟶  b ≤ ((−c)+(c+a))
        let motive_l = {
            let mut m = EnvDeclBuilder::child_of(&ch);
            let (t_id, t) = m.fresh_local(c.rat.clone());
            let body = c.rat_le(t, negc_ca.clone());
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let step_l = c.subst(motive_l, negc_cb.clone(), bv.clone(), h_simp_b, h_pushed);
        // rewrite RHS endpoint: b ≤ ((−c)+(c+a))  ⟶  b ≤ a
        let motive_r = {
            let mut m = EnvDeclBuilder::child_of(&ch);
            let (t_id, t) = m.fresh_local(c.rat.clone());
            let body = c.rat_le(bv.clone(), t);
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_b_le_a = c.subst(motive_r, negc_ca.clone(), a.clone(), h_simp_a, step_l); // b ≤ a
                                                                                        // contradiction
        let false_proof = Expr::app(h_not_le_ba, h_b_le_a);
        let lam = ch.mk_lam(hc_id, BinderInfo::Default, le_cbca.clone(), false_proof);
        ch.finish_child(lam)
    };

    // Iff.mpr (lt_iff (c+a)(c+b)) (And.intro ((c+a)≤(c+b)) ¬((c+b)≤(c+a)) le-half not-le-half)
    let le_cacb = c.rat_le(ca.clone(), cb.clone());
    let not_le_cbca = not_(le_cbca);
    let and_proof = and_intro(le_cacb.clone(), not_le_cbca.clone(), h_le_cacb, not_le_half);
    let body = iff_mpr(
        rat_lt(ca.clone(), cb.clone()),
        and_(le_cacb, not_le_cbca),
        lt_iff(ca.clone(), cb.clone()),
        and_proof,
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_add_lt_add_left_is_constructive_theorem() {
        let mut env = Environment::new();
        env.register_rat_add_lt_add_left()
            .expect("register_rat_add_lt_add_left");
        let name = Name::from_string("Rat.add_lt_add_left");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("add_lt_add_left proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "add_lt_add_left must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "add_lt_add_left's transitive axiom closure must be empty"
        );
    }

    #[test]
    fn test_add_lt_add_left_idempotent() {
        let mut env = Environment::new();
        env.register_rat_add_lt_add_left().expect("first");
        env.register_rat_add_lt_add_left()
            .expect("second (idempotent)");
    }
}
