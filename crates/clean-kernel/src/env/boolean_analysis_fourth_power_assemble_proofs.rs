// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner B5 fourth-power assembly — bridge proof-term builders.
//!
//! Connects the run-2/3 square identities to the parallelogram law
//! `Rat.add_sq_add_sub_sq` so the even-pair fourth-power identity
//!   `(A+B)⁴ + (A−B)⁴ = 2·A⁴ + 12·A²·B² + 2·B⁴`
//! can be assembled at `m := A²+B²`, `c := 2·A·B`.
//!
//! This commit lands the **regroup bridge**
//!   `Rat.add_sq_regroup A B :
//!       (A+B)·(A+B) = (A·A + B·B) + (1+1)·(A·B)`
//! which restates `Rat.add_sq`'s RHS `(A·A + 2·(A·B)) + B·B` in the
//! `m + c` shape (`m = A²+B²`, `c = 2·A·B`) that the parallelogram law's
//! binders expect. The move is the `((p+t)+r) = (p+r)+t` swap (commute the
//! trailing `B·B` past the cross term), built from `Rat.add_assoc` +
//! `Rat.add_comm`.
//!
//! The remaining `(A−B)²` mirror regroup, the `(A±B)⁴ = ((A±B)²)²` squaring,
//! the `2·m²` / `2·c²` expansions, and the final `4+8 = 12` coefficient
//! collection are the run-7 residual (see `boolean_analysis_fourth_power.rs`).
//!
//! Split into its own file to keep each under the 500-line limit. Constructive
//! (empty domain-axiom closure): only `Rat.add_sq` + the constructive `Rat`
//! additive surface are used.

use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Proof of `((p+t)+r) = (p+r)+t` for free `p`, `t`, `r` over `Rat`.
///
/// `(p+t)+r = p+(t+r)` [add_assoc] = `p+(r+t)` [add_comm under `p+·`] =
/// `(p+r)+t` [symm add_assoc]. `b` is the parent builder whose fvar scope the
/// terms live in.
fn swap_last(c: &RingConsts, b: &EnvDeclBuilder, p: &Expr, t: &Expr, r: &Expr) -> Expr {
    let add_c = c.add_const();
    let l1 = c.add(c.add(p.clone(), t.clone()), r.clone()); // (p+t)+r
    let t_plus_r = c.add(t.clone(), r.clone());
    let r_plus_t = c.add(r.clone(), t.clone());
    let p_tr = c.add(p.clone(), t_plus_r.clone()); // p+(t+r)
    let p_rt = c.add(p.clone(), r_plus_t.clone()); // p+(r+t)
    let pr = c.add(p.clone(), r.clone());
    let pr_t = c.add(pr.clone(), t.clone()); // (p+r)+t

    let s_assoc = c.aassoc(p.clone(), t.clone(), r.clone()); // (p+t)+r = p+(t+r)
    let h_comm = c.acomm(t.clone(), r.clone()); // t+r = r+t
    let s_comm = c.cong_right(
        b,
        &add_c,
        t_plus_r.clone(),
        r_plus_t.clone(),
        p.clone(),
        h_comm,
    ); // p+(t+r) = p+(r+t)
    let s_assoc2_raw = c.aassoc(p.clone(), r.clone(), t.clone()); // (p+r)+t = p+(r+t)
    let s_assoc2 = c.symm(pr_t.clone(), p_rt.clone(), s_assoc2_raw); // p+(r+t) = (p+r)+t

    let s = c.trans(l1.clone(), p_tr.clone(), p_rt.clone(), s_assoc, s_comm);
    c.trans(l1, p_rt, pr_t, s, s_assoc2)
}

/// Type of `Rat.sub_sq_regroup`:
/// `∀ A B, (A−B)·(A−B) = (A·A + B·B) + (1+1)·(A·(−B))`.
///
/// The `(A−B)²` mirror of `add_sq_regroup`: restates `Rat.sub_sq`'s RHS
/// `(A·A + 2·(A·(−B))) + B·B` in the `m + c` shape with `c = 2·(A·(−B))`, the
/// negative of `add_sq_regroup`'s cross term. Together they line the binders
/// `m := A·A + B·B`, `c_add := 2·(A·B)`, `c_sub := 2·(A·(−B))` up for the
/// parallelogram law in the fourth-power even-pair assembly.
pub(super) fn sub_sq_regroup_type(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat());
    let (bv_id, bv) = b.fresh_local(c.rat());
    let d = c.sub(a.clone(), bv.clone());
    let lhs = c.mul(d.clone(), d);
    let aa = c.mul(a.clone(), a.clone());
    let bb = c.mul(bv.clone(), bv.clone());
    let neg_b = c.neg(bv.clone());
    let a_negb = c.mul(a.clone(), neg_b);
    let rhs = c.add(c.add(aa, bb), c.nmul(c.two(), a_negb));
    let body = c.eq(lhs, rhs);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.sub_sq_regroup`.
///
/// `Rat.sub_sq A B : (A−B)² = (A·A + 2·(A·(−B))) + B·B`, then `swap_last`
/// commutes the trailing `B·B` past the cross term to land
/// `(A·A + B·B) + 2·(A·(−B))`. Identical move to `add_sq_regroup` with the
/// cross term `A·(−B)` in place of `A·B`.
pub(super) fn build_sub_sq_regroup_proof(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat());
    let (bv_id, bv) = b.fresh_local(c.rat());

    let d = c.sub(a.clone(), bv.clone());
    let lhs = c.mul(d.clone(), d.clone()); // (A−B)²

    let aa = c.mul(a.clone(), a.clone());
    let bb = c.mul(bv.clone(), bv.clone());
    let neg_b = c.neg(bv.clone());
    let a_negb = c.mul(a.clone(), neg_b); // A·(−B)
    let two_anegb = c.nmul(c.two(), a_negb.clone()); // 2·(A·(−B))

    // h_sub : (A−B)² = (A·A + 2·(A·(−B))) + B·B   [Rat.sub_sq A B]
    let sub_sq = Expr::const_(Name::from_string("Rat.sub_sq"), vec![]);
    let h_sub = Expr::apps(sub_sq, [a.clone(), bv.clone()]);
    let sub_rhs = c.add(c.add(aa.clone(), two_anegb.clone()), bb.clone()); // (A·A + 2·A·(−B)) + B·B

    // swap : (A·A + 2·A·(−B)) + B·B = (A·A + B·B) + 2·A·(−B)
    //   [swap_last at p := A·A, t := 2·(A·(−B)), r := B·B]
    let swap = swap_last(c, &b, &aa, &two_anegb, &bb);
    let target = c.add(c.add(aa.clone(), bb.clone()), two_anegb.clone());

    // body : (A−B)² = target   [trans h_sub swap]
    let body = c.trans(lhs.clone(), sub_rhs.clone(), target.clone(), h_sub, swap);

    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Type of `Rat.add_sq_regroup`:
/// `∀ A B, (A+B)·(A+B) = (A·A + B·B) + (1+1)·(A·B)`.
pub(super) fn add_sq_regroup_type(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat());
    let (bv_id, bv) = b.fresh_local(c.rat());
    let s = c.add(a.clone(), bv.clone());
    let lhs = c.mul(s.clone(), s);
    let aa = c.mul(a.clone(), a.clone());
    let bb = c.mul(bv.clone(), bv.clone());
    let ab = c.mul(a.clone(), bv.clone());
    let rhs = c.add(c.add(aa, bb), c.nmul(c.two(), ab));
    let body = c.eq(lhs, rhs);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.add_sq_regroup`.
///
/// `Rat.add_sq A B : (A+B)² = (A·A + 2·(A·B)) + B·B`, then `swap_last` commutes
/// the trailing `B·B` past the cross term to land `(A·A + B·B) + 2·(A·B)`.
pub(super) fn build_add_sq_regroup_proof(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat());
    let (bv_id, bv) = b.fresh_local(c.rat());

    let s = c.add(a.clone(), bv.clone());
    let lhs = c.mul(s.clone(), s.clone()); // (A+B)²

    let aa = c.mul(a.clone(), a.clone());
    let bb = c.mul(bv.clone(), bv.clone());
    let ab = c.mul(a.clone(), bv.clone());
    let two_ab = c.nmul(c.two(), ab.clone()); // 2·(A·B)

    // h_add : (A+B)² = (A·A + 2·(A·B)) + B·B   [Rat.add_sq A B]
    let add_sq = Expr::const_(Name::from_string("Rat.add_sq"), vec![]);
    let h_add = Expr::apps(add_sq, [a.clone(), bv.clone()]);
    let add_rhs = c.add(c.add(aa.clone(), two_ab.clone()), bb.clone()); // (A·A + 2AB) + B·B

    // swap : (A·A + 2AB) + B·B = (A·A + B·B) + 2AB
    //   [swap_last at p := A·A, t := 2·(A·B), r := B·B]
    let swap = swap_last(c, &b, &aa, &two_ab, &bb);
    let target = c.add(c.add(aa.clone(), bb.clone()), two_ab.clone());

    // body : (A+B)² = target   [trans h_add swap]
    let body = c.trans(lhs.clone(), add_rhs.clone(), target.clone(), h_add, swap);

    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}
