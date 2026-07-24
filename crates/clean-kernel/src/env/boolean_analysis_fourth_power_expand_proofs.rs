// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner B5 fourth-power even-pair — expanded normal form.
//!
//! Takes the parallelogram-factored keystone `Rat.fourth_power_even_pair`
//!   `(A+B)⁴ + (A−B)⁴ = 2·(M·M) + 2·(C·C)`,  M := A·A+B·B,  C := 2·(A·B)
//! and expands the right-hand side to the monomial normal form
//!   `(A+B)⁴ + (A−B)⁴ = (2·A⁴ + 2·B⁴) + ((2·2) + 2·(2·2))·(A²·B²)`
//! with `A⁴ := (A·A)·(A·A)`, `B⁴ := (B·B)·(B·B)`, `A²·B² := (A·A)·(B·B)`, and the
//! cross coefficient the honest `4 + 8` split (`2·2` from `2·M²`, `2·(2·2)` from
//! `2·C²`) collected under one `Rat.right_distrib`.
//!
//! ## Expansion
//!
//! `M·M = (A²+B²)·(A²+B²) = (A⁴ + B⁴) + 2·(A²·B²)`   [add_sq_regroup A² B²]
//! `C·C = (2·(A·B))·(2·(A·B)) = (2·2)·(A²·B²)`        [mul_mul_mul_comm ×2]
//! Distribute the two outer `2·`s (`Rat.left_distrib`, `Rat.mul_assoc`) and
//! gather the two `A²·B²` terms (`Rat.right_distrib`).
//!
//! Every dependency (`Rat.fourth_power_even_pair`, `Rat.add_sq_regroup`,
//! `Rat.mul_mul_mul_comm`, the `Rat` ring/congruence surface) is
//! `ProofQuality::Constructive` with empty domain-axiom closure, so the expanded
//! form is too.

use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// `Rat.fourth_power_even_pair A B`.
fn keystone(a: &Expr, bv: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.fourth_power_even_pair"), vec![]),
        [a.clone(), bv.clone()],
    )
}

/// `Rat.add_sq_regroup X Y : (X+Y)·(X+Y) = (X·X + Y·Y) + (1+1)·(X·Y)`.
fn add_sq_regroup(x: &Expr, y: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_sq_regroup"), vec![]),
        [x.clone(), y.clone()],
    )
}

/// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
fn mmmc(a: &Expr, bb: &Expr, cc: &Expr, dd: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
        [a.clone(), bb.clone(), cc.clone(), dd.clone()],
    )
}

/// Build `M·M = (A⁴ + B⁴) + 2·(A²·B²)` for the free `A`, `B`.
///
/// `add_sq_regroup (A·A) (B·B)` at `X := A·A`, `Y := B·B` gives exactly
/// `(A·A + B·B)·(A·A + B·B) = ((A·A)·(A·A) + (B·B)·(B·B)) + 2·((A·A)·(B·B))`.
fn mm_expand(c: &RingConsts, a: &Expr, bv: &Expr) -> Expr {
    let aa = c.mul(a.clone(), a.clone());
    let bb = c.mul(bv.clone(), bv.clone());
    add_sq_regroup(&aa, &bb)
}

/// Build `C·C = (2·2)·(A²·B²)` for the free `A`, `B`, where `C := 2·(A·B)`.
///
///   `(2·(A·B))·(2·(A·B)) = (2·2)·((A·B)·(A·B))`   [mmmc 2 (A·B) 2 (A·B)]
///   `(A·B)·(A·B) = (A·A)·(B·B)`                   [mmmc A B A B]
/// lifted over the fixed `(2·2)·` factor.
fn cc_expand(c: &RingConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let mul_c = c.mul_const();
    let two = c.two();
    let ab = c.mul(a.clone(), bv.clone());
    let cv = c.nmul(two.clone(), ab.clone()); // C = 2·(A·B)
    let cc = c.mul(cv.clone(), cv.clone()); // C·C
    let two_two = c.mul(two.clone(), two.clone()); // 2·2
    let ab_ab = c.mul(ab.clone(), ab.clone()); // (A·B)·(A·B)
    let twotwo_abab = c.mul(two_two.clone(), ab_ab.clone()); // (2·2)·((A·B)·(A·B))
    let aa = c.mul(a.clone(), a.clone());
    let bb = c.mul(bv.clone(), bv.clone());
    let a2b2 = c.mul(aa.clone(), bb.clone()); // (A·A)·(B·B)
    let twotwo_a2b2 = c.mul(two_two.clone(), a2b2.clone()); // (2·2)·((A·A)·(B·B))

    // step1 : C·C = (2·2)·((A·B)·(A·B))
    let step1 = mmmc(&two, &ab, &two, &ab);
    // inner : (A·B)·(A·B) = (A·A)·(B·B)
    let inner = mmmc(a, bv, a, bv);
    // lift inner over fixed (2·2): (2·2)·((A·B)·(A·B)) = (2·2)·((A·A)·(B·B))
    let lift = c.cong_right(
        parent,
        &mul_c,
        ab_ab.clone(),
        a2b2.clone(),
        two_two.clone(),
        inner,
    );
    c.trans(cc, twotwo_abab, twotwo_a2b2, step1, lift)
}

/// Type of `Rat.fourth_power_even_pair_expanded`:
/// `∀ A B,
///     ((A+B)·(A+B))·((A+B)·(A+B)) + ((A−B)·(A−B))·((A−B)·(A−B))
///       = ((1+1)·A⁴ + (1+1)·B⁴) + ((1+1)·(1+1) + (1+1)·((1+1)·(1+1)))·(A²·B²)`
/// with `A⁴ := (A·A)·(A·A)`, `B⁴ := (B·B)·(B·B)`, `A²·B² := (A·A)·(B·B)`.
pub(super) fn fourth_power_even_pair_expanded_type(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat());
    let (bv_id, bv) = b.fresh_local(c.rat());

    let s = c.add(a.clone(), bv.clone());
    let sq_add = c.mul(s.clone(), s);
    let d = c.sub(a.clone(), bv.clone());
    let sq_sub = c.mul(d.clone(), d);
    let lhs = c.add(c.mul(sq_add.clone(), sq_add), c.mul(sq_sub.clone(), sq_sub));

    let rhs = expanded_rhs(c, &a, &bv);
    let body = c.eq(lhs, rhs);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// The expanded RHS `(2·A⁴ + 2·B⁴) + (2·2 + 2·(2·2))·(A²·B²)`.
fn expanded_rhs(c: &RingConsts, a: &Expr, bv: &Expr) -> Expr {
    let two = c.two();
    let aa = c.mul(a.clone(), a.clone());
    let bb = c.mul(bv.clone(), bv.clone());
    let a4 = c.mul(aa.clone(), aa.clone());
    let b4 = c.mul(bb.clone(), bb.clone());
    let a2b2 = c.mul(aa.clone(), bb.clone());
    let two_two = c.mul(two.clone(), two.clone());
    let two_a4 = c.nmul(two.clone(), a4);
    let two_b4 = c.nmul(two.clone(), b4);
    let coeff = c.add(two_two.clone(), c.nmul(two.clone(), two_two.clone())); // (2·2) + 2·(2·2)
    c.add(c.add(two_a4, two_b4), c.mul(coeff, a2b2))
}

/// Build the proof term for `Rat.fourth_power_even_pair_expanded`.
pub(super) fn build_fourth_power_even_pair_expanded_proof(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat());
    let (bv_id, bv) = b.fresh_local(c.rat());

    let add_c = c.add_const();
    let mul_c = c.mul_const();
    let two = c.two();

    // Sub-monomials.
    let aa = c.mul(a.clone(), a.clone());
    let bb = c.mul(bv.clone(), bv.clone());
    let a4 = c.mul(aa.clone(), aa.clone()); // A⁴
    let b4 = c.mul(bb.clone(), bb.clone()); // B⁴
    let a2b2 = c.mul(aa.clone(), bb.clone()); // A²·B²
    let ab = c.mul(a.clone(), bv.clone());
    let m = c.add(aa.clone(), bb.clone()); // M
    let cross = c.nmul(two.clone(), ab.clone()); // C
    let mm = c.mul(m.clone(), m.clone()); // M·M
    let cc = c.mul(cross.clone(), cross.clone()); // C·C
    let two_two = c.mul(two.clone(), two.clone()); // 2·2

    // ── keystone : LHS = 2·(M·M) + 2·(C·C)
    let two_mm = c.nmul(two.clone(), mm.clone());
    let two_cc = c.nmul(two.clone(), cc.clone());
    let key_rhs = c.add(two_mm.clone(), two_cc.clone());
    let key = keystone(&a, &bv);

    // ── Expand M·M = (A⁴+B⁴) + 2·(A²·B²); lift over outer 2·.
    let a4_b4 = c.add(a4.clone(), b4.clone());
    let two_a2b2 = c.nmul(two.clone(), a2b2.clone());
    let mm_rhs = c.add(a4_b4.clone(), two_a2b2.clone()); // (A⁴+B⁴) + 2·(A²·B²)
    let h_mm = mm_expand(c, &a, &bv); // M·M = mm_rhs
    let two_mm_rhs = c.nmul(two.clone(), mm_rhs.clone());
    let cong_mm = c.cong_right(&b, &mul_c, mm.clone(), mm_rhs.clone(), two.clone(), h_mm); // 2·(M·M) = 2·mm_rhs

    // ── Expand C·C = (2·2)·(A²·B²); lift over outer 2·.
    let twotwo_a2b2 = c.mul(two_two.clone(), a2b2.clone());
    let h_cc = cc_expand(c, &b, &a, &bv); // C·C = (2·2)·(A²·B²)
    let two_cc_rhs = c.nmul(two.clone(), twotwo_a2b2.clone());
    let cong_cc = c.cong_right(
        &b,
        &mul_c,
        cc.clone(),
        twotwo_a2b2.clone(),
        two.clone(),
        h_cc,
    ); // 2·(C·C) = 2·((2·2)·A²B²)

    // ── key_rhs → 2·mm_rhs + 2·twotwo_a2b2  [congr both summands]
    let mid1 = c.add(two_mm_rhs.clone(), two_cc.clone());
    let cl = c.cong_left(
        &b,
        &add_c,
        two_mm.clone(),
        two_mm_rhs.clone(),
        two_cc.clone(),
        cong_mm,
    );
    let mid2 = c.add(two_mm_rhs.clone(), two_cc_rhs.clone());
    let cr = c.cong_right(
        &b,
        &add_c,
        two_cc.clone(),
        two_cc_rhs.clone(),
        two_mm_rhs.clone(),
        cong_cc,
    );
    let to_mid2 = c.trans(key_rhs.clone(), mid1.clone(), mid2.clone(), cl, cr);

    // ── 2·mm_rhs = 2·(A⁴+B⁴) + 2·(2·A²B²)   [left_distrib 2 (A⁴+B⁴) (2·A²B²)]
    let two_a4b4 = c.nmul(two.clone(), a4_b4.clone());
    let two_two_a2b2 = c.nmul(two.clone(), two_a2b2.clone()); // 2·(2·A²B²)
    let split_mm = c.add(two_a4b4.clone(), two_two_a2b2.clone());
    let ld_mm = c.ldist(two.clone(), a4_b4.clone(), two_a2b2.clone()); // 2·mm_rhs = split_mm

    //   2·(A⁴+B⁴) = 2·A⁴ + 2·B⁴   [left_distrib 2 A⁴ B⁴]
    let two_a4 = c.nmul(two.clone(), a4.clone());
    let two_b4 = c.nmul(two.clone(), b4.clone());
    let two_a4_two_b4 = c.add(two_a4.clone(), two_b4.clone());
    let ld_a4b4 = c.ldist(two.clone(), a4.clone(), b4.clone());

    //   2·(2·A²B²) = (2·2)·A²B²   [symm mul_assoc 2 2 A²B²]
    let assoc = c.massoc(two.clone(), two.clone(), a2b2.clone()); // (2·2)·A²B² = 2·(2·A²B²)
                                                                  // symm(a, b, h:a=b) : b=a; assoc : twotwo_a2b2 = two_two_a2b2, so a:=twotwo_a2b2, b:=two_two_a2b2.
    let h_22 = c.symm(twotwo_a2b2.clone(), two_two_a2b2.clone(), assoc); // 2·(2·A²B²) = (2·2)·A²B²

    //   2·((2·2)·A²B²) = (2·(2·2))·A²B²   [symm mul_assoc 2 (2·2) A²B²]
    let two_22 = c.nmul(two.clone(), two_two.clone()); // 2·(2·2)
    let two_22_a2b2 = c.mul(two_22.clone(), a2b2.clone());
    let assoc2 = c.massoc(two.clone(), two_two.clone(), a2b2.clone()); // (2·(2·2))·A²B² = 2·((2·2)·A²B²)
    let h_222 = c.symm(two_22_a2b2.clone(), two_cc_rhs.clone(), assoc2); // 2·((2·2)·A²B²) = (2·(2·2))·A²B²

    // Rewrite mid2 step-by-step into the final shape.
    //  mid2 = 2·mm_rhs + 2·twotwo_a2b2
    //  s1: 2·mm_rhs → split_mm
    let mid_s1 = c.add(split_mm.clone(), two_cc_rhs.clone());
    let cl1 = c.cong_left(
        &b,
        &add_c,
        two_mm_rhs.clone(),
        split_mm.clone(),
        two_cc_rhs.clone(),
        ld_mm,
    );
    //  s2: split_mm's left 2·(A⁴+B⁴) → 2·A⁴ + 2·B⁴   (cong inside split_mm, then lift)
    let split_mm2 = c.add(two_a4_two_b4.clone(), two_two_a2b2.clone());
    let cl_inner = c.cong_left(
        &b,
        &add_c,
        two_a4b4.clone(),
        two_a4_two_b4.clone(),
        two_two_a2b2.clone(),
        ld_a4b4,
    ); // split_mm = split_mm2
    let mid_s2 = c.add(split_mm2.clone(), two_cc_rhs.clone());
    let cl2 = c.cong_left(
        &b,
        &add_c,
        split_mm.clone(),
        split_mm2.clone(),
        two_cc_rhs.clone(),
        cl_inner,
    );
    //  s3: split_mm2's right 2·(2·A²B²) → (2·2)·A²B²
    let split_mm3 = c.add(two_a4_two_b4.clone(), twotwo_a2b2.clone());
    let c_inner3 = c.cong_right(
        &b,
        &add_c,
        two_two_a2b2.clone(),
        twotwo_a2b2.clone(),
        two_a4_two_b4.clone(),
        h_22,
    ); // split_mm2 = split_mm3
    let mid_s3 = c.add(split_mm3.clone(), two_cc_rhs.clone());
    let cl3 = c.cong_left(
        &b,
        &add_c,
        split_mm2.clone(),
        split_mm3.clone(),
        two_cc_rhs.clone(),
        c_inner3,
    );
    //  s4: outer right 2·((2·2)·A²B²) → (2·(2·2))·A²B²
    let mid_s4 = c.add(split_mm3.clone(), two_22_a2b2.clone());
    let cr4 = c.cong_right(
        &b,
        &add_c,
        two_cc_rhs.clone(),
        two_22_a2b2.clone(),
        split_mm3.clone(),
        h_222,
    );

    // Now mid_s4 = ((2·A⁴ + 2·B⁴) + (2·2)·A²B²) + (2·(2·2))·A²B²
    // Reassoc to gather the two A²B² coeff terms:
    //   ((P + u·z) + v·z) = (P + (u·z + v·z))   [mul_assoc form — additive]
    //   then right_distrib collects u·z + v·z = (u+v)·z.
    let p_part = two_a4_two_b4.clone(); // 2·A⁴ + 2·B⁴
    let uz = twotwo_a2b2.clone(); // (2·2)·A²B²
    let vz = two_22_a2b2.clone(); // (2·(2·2))·A²B²
                                  //   aassoc P (u·z) (v·z) : ((P + u·z) + v·z) = P + (u·z + v·z)
    let uz_vz = c.add(uz.clone(), vz.clone());
    let p_uzvz = c.add(p_part.clone(), uz_vz.clone());
    let reassoc = c.aassoc(p_part.clone(), uz.clone(), vz.clone());
    //   right_distrib (2·2) (2·(2·2)) A²B² : ((2·2)+(2·(2·2)))·A²B² = (2·2)·A²B² + (2·(2·2))·A²B²
    let coeff = c.add(two_two.clone(), two_22.clone()); // (2·2)+(2·(2·2))
    let coeff_a2b2 = c.mul(coeff.clone(), a2b2.clone());
    let rd = c.rdist(two_two.clone(), two_22.clone(), a2b2.clone()); // coeff·A²B² = u·z + v·z
    let rd_sym = c.symm(coeff_a2b2.clone(), uz_vz.clone(), rd); // u·z + v·z = coeff·A²B²
                                                                //   lift over fixed P: P + (u·z + v·z) = P + coeff·A²B²
    let p_coeff = c.add(p_part.clone(), coeff_a2b2.clone());
    let lift_coeff = c.cong_right(
        &b,
        &add_c,
        uz_vz.clone(),
        coeff_a2b2.clone(),
        p_part.clone(),
        rd_sym,
    );

    // Final target `p_coeff = (2·A⁴ + 2·B⁴) + coeff·A²B²` is, by construction,
    // syntactically the `expanded_rhs` the stated type uses; the kernel checks
    // this when the proof is registered against `fourth_power_even_pair_expanded_type`.

    // ── Assemble the trans chain.
    let lhs = c.add(
        {
            let s = c.add(a.clone(), bv.clone());
            let sq = c.mul(s.clone(), s.clone());
            c.mul(sq.clone(), sq)
        },
        {
            let d = c.sub(a.clone(), bv.clone());
            let sq = c.mul(d.clone(), d.clone());
            c.mul(sq.clone(), sq)
        },
    );

    // chain: lhs =[key] key_rhs =[to_mid2] mid2 =[cl1] mid_s1 =[cl2] mid_s2
    //        =[cl3] mid_s3 =[cr4] mid_s4 =[reassoc] p_uzvz =[lift_coeff] p_coeff(=target)
    let s = c.trans(lhs.clone(), key_rhs.clone(), mid2.clone(), key, to_mid2);
    let s = c.trans(lhs.clone(), mid2.clone(), mid_s1.clone(), s, cl1);
    let s = c.trans(lhs.clone(), mid_s1.clone(), mid_s2.clone(), s, cl2);
    let s = c.trans(lhs.clone(), mid_s2.clone(), mid_s3.clone(), s, cl3);
    let s = c.trans(lhs.clone(), mid_s3.clone(), mid_s4.clone(), s, cr4);
    let s = c.trans(lhs.clone(), mid_s4.clone(), p_uzvz.clone(), s, reassoc);
    let body = c.trans(lhs.clone(), p_uzvz.clone(), p_coeff.clone(), s, lift_coeff);

    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;
    use crate::tc::TypeChecker;

    /// Full kernel check (`infer_only = false`) of the expanded proof body
    /// against its declared type, over an env with the keystone + dependencies
    /// registered. This is the same check `add_decl` performs; guards against a
    /// fast-infer-only false positive.
    #[test]
    fn test_expanded_proof_full_checks() {
        let mut env = Environment::new();
        // Registers ring identities, mul_mul_mul_comm, and the keystone (the
        // expanded decl is the last registration; if it ever fails to register,
        // init returns Err — exercised by the parent module's tests).
        env.init_boolean_analysis_fourth_power()
            .expect("init should register the expanded decl too");
        let c = RingConsts::new();
        let val = build_fourth_power_even_pair_expanded_proof(&c);
        let ty = fourth_power_even_pair_expanded_type(&c);
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&val, &ty)
            .expect("expanded proof body must fully kernel-check against its type");
    }
}
