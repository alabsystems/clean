// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner B5 fourth-power even-pair — keystone identity.
//!
//! The capstone the (2,4)-hypercontractivity B5 step consumes. The fourth-power
//! even-pair identity, in the parallelogram-factored normal form:
//!   `(A+B)⁴ + (A−B)⁴ = (1+1)·(M·M) + (1+1)·(C·C)`
//! with `M := A·A + B·B` and `C := (1+1)·(A·B)`.
//!
//! ## Assembly
//!
//! Let `M := A·A + B·B`, `C := (1+1)·(A·B)`. The two regroup bridges
//!   `Rat.add_sq_regroup A B : (A+B)·(A+B) = M + C`
//!   `Rat.sub_sq_regroup A B : (A−B)·(A−B) = M + (1+1)·(A·(−B))`
//! restate the squares in `m+c` shape. Folding `(1+1)·(A·(−B)) = −C` through
//! `Rat.mul_neg` (twice) turns the sub-regroup RHS into `M + (−C)`, which is
//! `Rat.sub M C` (reducible `Rat.sub`). Then:
//!   `(A+B)⁴ = (A+B)²·(A+B)² = (M+C)·(M+C)`            [congr both factors]
//!   `(A−B)⁴ = (A−B)²·(A−B)² = (M−C)·(M−C)`            [congr both factors]
//! and the parallelogram law `Rat.add_sq_add_sub_sq M C`
//!   `(M+C)·(M+C) + (M−C)·(M−C) = (1+1)·(M·M) + (1+1)·(C·C)`
//! closes the chain.
//!
//! Every dependency (`Rat.add_sq_regroup`, `Rat.sub_sq_regroup`,
//! `Rat.add_sq_add_sub_sq`, `Rat.mul_neg`, the `Rat` additive/congruence
//! surface) is `ProofQuality::Constructive` with empty domain-axiom closure, so
//! the keystone is too.
//!
//! Split into its own file to keep each under the 500-line limit.

use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// `Rat.add_sq_regroup A B : (A+B)·(A+B) = (A·A + B·B) + (1+1)·(A·B)`.
fn add_sq_regroup(a: &Expr, bv: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_sq_regroup"), vec![]),
        [a.clone(), bv.clone()],
    )
}

/// `Rat.sub_sq_regroup A B : (A−B)·(A−B) = (A·A + B·B) + (1+1)·(A·(−B))`.
fn sub_sq_regroup(a: &Expr, bv: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.sub_sq_regroup"), vec![]),
        [a.clone(), bv.clone()],
    )
}

/// `Rat.add_sq_add_sub_sq m c :
///     (m+c)·(m+c) + (m−c)·(m−c) = (1+1)·(m·m) + (1+1)·(c·c)`.
fn parallelogram(m: &Expr, cv: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_sq_add_sub_sq"), vec![]),
        [m.clone(), cv.clone()],
    )
}

/// `Rat.mul_neg a b : a·(−b) = −(a·b)`.
fn mul_neg(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_neg"), vec![]),
        [a.clone(), b.clone()],
    )
}

/// Type of `Rat.fourth_power_even_pair`:
/// `∀ A B,
///     ((A+B)·(A+B))·((A+B)·(A+B)) + ((A−B)·(A−B))·((A−B)·(A−B))
///       = (1+1)·(M·M) + (1+1)·(C·C)`
/// with `M := A·A + B·B`, `C := (1+1)·(A·B)`.
pub(super) fn fourth_power_even_pair_type(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat());
    let (bv_id, bv) = b.fresh_local(c.rat());

    let s = c.add(a.clone(), bv.clone());
    let sq_add = c.mul(s.clone(), s); // (A+B)²
    let d = c.sub(a.clone(), bv.clone());
    let sq_sub = c.mul(d.clone(), d); // (A−B)²
    let p_add = c.mul(sq_add.clone(), sq_add); // (A+B)⁴
    let p_sub = c.mul(sq_sub.clone(), sq_sub); // (A−B)⁴
    let lhs = c.add(p_add, p_sub);

    let m = c.add(c.mul(a.clone(), a.clone()), c.mul(bv.clone(), bv.clone()));
    let cross = c.nmul(c.two(), c.mul(a.clone(), bv.clone()));
    let mm = c.mul(m.clone(), m.clone());
    let cc = c.mul(cross.clone(), cross.clone());
    let rhs = c.add(c.nmul(c.two(), mm), c.nmul(c.two(), cc));

    let body = c.eq(lhs, rhs);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.fourth_power_even_pair`.
pub(super) fn build_fourth_power_even_pair_proof(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat());
    let (bv_id, bv) = b.fresh_local(c.rat());

    let mul_c = c.mul_const();
    let add_c = c.add_const();

    let s = c.add(a.clone(), bv.clone());
    let sq_add = c.mul(s.clone(), s.clone()); // (A+B)²
    let d = c.sub(a.clone(), bv.clone());
    let sq_sub = c.mul(d.clone(), d.clone()); // (A−B)²
    let p_add = c.mul(sq_add.clone(), sq_add.clone()); // (A+B)⁴
    let p_sub = c.mul(sq_sub.clone(), sq_sub.clone()); // (A−B)⁴
    let lhs = c.add(p_add.clone(), p_sub.clone());

    // M := A·A + B·B,  C := 2·(A·B),  Cm := 2·(A·(−B)).
    let aa = c.mul(a.clone(), a.clone());
    let bb = c.mul(bv.clone(), bv.clone());
    let m = c.add(aa.clone(), bb.clone());
    let ab = c.mul(a.clone(), bv.clone());
    let two = c.two();
    let cross = c.nmul(two.clone(), ab.clone()); // C = 2·(A·B)
    let neg_b = c.neg(bv.clone());
    let a_negb = c.mul(a.clone(), neg_b.clone()); // A·(−B)
    let cross_m = c.nmul(two.clone(), a_negb.clone()); // Cm = 2·(A·(−B))

    let m_plus_c = c.add(m.clone(), cross.clone()); // M + C
    let m_plus_cm = c.add(m.clone(), cross_m.clone()); // M + Cm
    let neg_c = c.neg(cross.clone()); // −C

    // ── h_add : (A+B)² = M + C   [add_sq_regroup A B]
    let h_add = add_sq_regroup(&a, &bv);
    // ── h_sub0 : (A−B)² = M + Cm   [sub_sq_regroup A B]
    let h_sub0 = sub_sq_regroup(&a, &bv);

    // ── h_cm : Cm = −C
    //   step1: A·(−B) = −(A·B)            [mul_neg A B]
    //   step2: 2·(A·(−B)) = 2·(−(A·B))    [cong_right mul over 2]
    //   step3: 2·(−(A·B)) = −(2·(A·B))    [mul_neg 2 (A·B)]
    let neg_ab = c.neg(ab.clone());
    let two_neg_ab = c.nmul(two.clone(), neg_ab.clone()); // 2·(−(A·B))
    let s1 = mul_neg(&a, &bv); // A·(−B) = −(A·B)
    let cong1 = c.cong_right(&b, &mul_c, a_negb.clone(), neg_ab.clone(), two.clone(), s1); // 2·(A·(−B)) = 2·(−(A·B))
    let s3 = mul_neg(&two, &ab); // 2·(−(A·B)) = −(2·(A·B))
    let h_cm = c.trans(
        cross_m.clone(),
        two_neg_ab.clone(),
        neg_c.clone(),
        cong1,
        s3,
    ); // Cm = −C

    // ── h_sub : (A−B)² = M + (−C)   [trans h_sub0 (cong_right add: Cm → −C)]
    let m_plus_negc = c.add(m.clone(), neg_c.clone()); // M + (−C)  (= M − C reducibly)
    let cong_sub = c.cong_right(&b, &add_c, cross_m.clone(), neg_c.clone(), m.clone(), h_cm); // M+Cm = M+(−C)
    let h_sub = c.trans(
        sq_sub.clone(),
        m_plus_cm.clone(),
        m_plus_negc.clone(),
        h_sub0,
        cong_sub,
    );

    // ── Rewrite (A+B)⁴ = (A+B)²·(A+B)² → (M+C)·(M+C)
    //   left factor:  (A+B)²·(A+B)² = (M+C)·(A+B)²        [cong_left mul, h_add]
    //   right factor: (M+C)·(A+B)²  = (M+C)·(M+C)         [cong_right mul, h_add]
    let mc_sqadd = c.mul(m_plus_c.clone(), sq_add.clone()); // (M+C)·(A+B)²
    let mc_mc = c.mul(m_plus_c.clone(), m_plus_c.clone()); // (M+C)·(M+C)
    let cl_add = c.cong_left(
        &b,
        &mul_c,
        sq_add.clone(),
        m_plus_c.clone(),
        sq_add.clone(),
        h_add.clone(),
    );
    let cr_add = c.cong_right(
        &b,
        &mul_c,
        sq_add.clone(),
        m_plus_c.clone(),
        m_plus_c.clone(),
        h_add.clone(),
    );
    let p_add_eq = c.trans(
        p_add.clone(),
        mc_sqadd.clone(),
        mc_mc.clone(),
        cl_add,
        cr_add,
    ); // (A+B)⁴ = (M+C)·(M+C)

    // ── Rewrite (A−B)⁴ = (A−B)²·(A−B)² → (M+(−C))·(M+(−C))
    let mnc_sqsub = c.mul(m_plus_negc.clone(), sq_sub.clone()); // (M+(−C))·(A−B)²
    let mnc_mnc = c.mul(m_plus_negc.clone(), m_plus_negc.clone()); // (M+(−C))·(M+(−C))
    let cl_sub = c.cong_left(
        &b,
        &mul_c,
        sq_sub.clone(),
        m_plus_negc.clone(),
        sq_sub.clone(),
        h_sub.clone(),
    );
    let cr_sub = c.cong_right(
        &b,
        &mul_c,
        sq_sub.clone(),
        m_plus_negc.clone(),
        m_plus_negc.clone(),
        h_sub.clone(),
    );
    let p_sub_eq = c.trans(
        p_sub.clone(),
        mnc_sqsub.clone(),
        mnc_mnc.clone(),
        cl_sub,
        cr_sub,
    ); // (A−B)⁴ = (M+(−C))·(M+(−C))

    // ── lhs = (M+C)·(M+C) + (M+(−C))·(M+(−C))   [congr both summands]
    let lhs1 = c.add(mc_mc.clone(), p_sub.clone());
    let cl_lhs = c.cong_left(
        &b,
        &add_c,
        p_add.clone(),
        mc_mc.clone(),
        p_sub.clone(),
        p_add_eq,
    );
    let lhs2 = c.add(mc_mc.clone(), mnc_mnc.clone());
    let cr_lhs = c.cong_right(
        &b,
        &add_c,
        p_sub.clone(),
        mnc_mnc.clone(),
        mc_mc.clone(),
        p_sub_eq,
    );
    let lhs_rewrite = c.trans(lhs.clone(), lhs1.clone(), lhs2.clone(), cl_lhs, cr_lhs);

    // ── Parallelogram law at m := M, c := C.
    //   add_sq_add_sub_sq M C :
    //     (M+C)·(M+C) + (M−C)·(M−C) = (1+1)·(M·M) + (1+1)·(C·C)
    //   The stated LHS uses `Rat.sub M C`, which is reducibly `M + (−C)`, so it
    //   is defeq to `lhs2`'s second summand `(M+(−C))·(M+(−C))`. We anchor the
    //   trans at `lhs2` (the syntactic form we built); the parallelogram's LHS
    //   `(M+C)·(M+C) + (M−C)·(M−C)` unifies up to that reduction.
    let mm = c.mul(m.clone(), m.clone());
    let cc = c.mul(cross.clone(), cross.clone());
    let rhs = c.add(
        c.nmul(two.clone(), mm.clone()),
        c.nmul(two.clone(), cc.clone()),
    );
    let para = parallelogram(&m, &cross);
    // Parallelogram's stated LHS is `(M+C)·(M+C) + (M−C)·(M−C)` using `Rat.sub`.
    // `Rat.sub M C` is reducibly `M + (−C)`, so it is defeq to `lhs2`'s second
    // summand `(M+(−C))·(M+(−C))`.
    //
    // Chain: lhs = lhs2 (lhs_rewrite) = rhs (para). `Eq.trans` checks defeq of
    // the shared middle term; `lhs2` ≡ the parallelogram's LHS since
    // `M + (−C)` ≡ `Rat.sub M C`.
    let body = c.trans(lhs.clone(), lhs2.clone(), rhs.clone(), lhs_rewrite, para);

    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}
