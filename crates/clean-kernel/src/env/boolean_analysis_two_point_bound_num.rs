// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Numeral + ring-collapse helpers for the two-point bound proof.
//
// `include!`d into `boolean_analysis_two_point_bound_proof.rs`; shares its
// `use`s and the `RingConsts` / `HcBoundsConsts` surfaces.

/// `Rat.mul_one a : a·1 = a`.
fn mul_one_c(a: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
        a.clone(),
    )
}

/// `h : (six·two) = coeff`, where `six := 2·3 = 2·(2+1)`, `two := 1+1`,
/// `coeff := (2·2) + 2·(2·2)`.
///
/// Both are the numeral `12`. Derivation:
///   `six·two = (2·(2+1))·2`
///     = `(2·2 + 2·1)·2`              [cong_left mul, ldist 2 2 1]
///     = `(2·2 + 2)·2`               [cong_left mul, cong_right add, mul_one 2]
///     = `(2·2)·2 + 2·2`             [rdist (2·2) 2 2]
///     = `2·(2·2) + 2·2`            [cong_left add, mul_assoc 2 2 2]
///     = `(2·2) + 2·(2·2)`         [add_comm]  = coeff.
fn build_twelve_eq(
    c: &RingConsts,
    parent: &EnvDeclBuilder,
    six: &Expr,
    two: &Expr,
    coeff: &Expr,
) -> Expr {
    let add_c = c.add_const();
    let mul_c = c.mul_const();
    let one = c.one();
    let three = c.add(two.clone(), one.clone()); // 2+1  (== HcBoundsConsts::three)

    // six·two = (2·(2+1))·2
    let six_two = c.mul(six.clone(), two.clone());

    // ── e1 : six = 2·2 + 2·1   [ldist 2 2 1]  (six := 2·(2+1), so `2·(2+1)` ι-shapes
    //    directly into `Rat.left_distrib 2 2 1 : 2·(2+1) = 2·2 + 2·1`). Lift over (·2).
    let _ = three;
    let two_two = c.mul(two.clone(), two.clone());
    let two_one = c.mul(two.clone(), one.clone());
    let sum_22_21 = c.add(two_two.clone(), two_one.clone());
    let step1_rhs = c.mul(sum_22_21.clone(), two.clone());
    let h_six = ld_six(c, two, &one); // six = 2·2 + 2·1
    let cl1 = c.cong_left(
        parent,
        &mul_c,
        six.clone(),
        sum_22_21.clone(),
        two.clone(),
        h_six,
    );

    // ── e2 : 2·1 = 2   [mul_one 2]; rewrite inside (2·2 + 2·1) → (2·2 + 2)
    let two_two_plus_two = c.add(two_two.clone(), two.clone());
    let mo = mul_one_c(two); // 2·1 = 2
    let cong_inner = c.cong_right(
        parent,
        &add_c,
        two_one.clone(),
        two.clone(),
        two_two.clone(),
        mo,
    );
    // lift over (·2): (2·2+2·1)·2 = (2·2+2)·2
    let cl2 = c.cong_left(
        parent,
        &mul_c,
        sum_22_21.clone(),
        two_two_plus_two.clone(),
        two.clone(),
        cong_inner,
    );
    let step2_rhs = c.mul(two_two_plus_two.clone(), two.clone());

    // ── e3 : (2·2+2)·2 = (2·2)·2 + 2·2   [rdist (2·2) 2 2]
    let twotwo_two = c.mul(two_two.clone(), two.clone()); // (2·2)·2
    let two_two2 = c.mul(two.clone(), two.clone()); // 2·2  (right summand from rdist's b·c with b=2,c=2)
    let rd = c.rdist(two_two.clone(), two.clone(), two.clone()); // (2·2+2)·2 = (2·2)·2 + 2·2
    let step3_rhs = c.add(twotwo_two.clone(), two_two2.clone());

    // ── e4 : (2·2)·2 = 2·(2·2)   [mul_assoc 2 2 2]; rewrite left summand
    let two_twotwo = c.mul(two.clone(), two_two.clone()); // 2·(2·2)
    let assoc = c.massoc(two.clone(), two.clone(), two.clone()); // (2·2)·2 = 2·(2·2)
    let cl4 = c.cong_left(
        parent,
        &add_c,
        twotwo_two.clone(),
        two_twotwo.clone(),
        two_two2.clone(),
        assoc,
    );
    let step4_rhs = c.add(two_twotwo.clone(), two_two2.clone());

    // ── e5 : 2·(2·2) + 2·2 = (2·2) + 2·(2·2)   [add_comm]
    let acomm = c.acomm(two_twotwo.clone(), two_two2.clone()); // (2·(2·2)) + (2·2) = (2·2) + (2·(2·2))
                                                               // target coeff = (2·2) + 2·(2·2)  — note coeff's second summand is `2·(2·2)` where
                                                               // the inner `2·2` is `mul(two,two)`; matches two_twotwo. And first summand `2·2` = two_two.
    let target = c.add(two_two.clone(), two_twotwo.clone());
    let _ = coeff; // coeff is definitionally `target` (same construction); kept for doc.

    // ── Assemble: six_two = step1_rhs = step2_rhs = step3_rhs = step4_rhs = target.
    let s = c.trans(
        six_two.clone(),
        step1_rhs.clone(),
        step2_rhs.clone(),
        cl1,
        cl2,
    );
    let s = c.trans(six_two.clone(), step2_rhs.clone(), step3_rhs.clone(), s, rd);
    let s = c.trans(
        six_two.clone(),
        step3_rhs.clone(),
        step4_rhs.clone(),
        s,
        cl4,
    );
    c.trans(six_two, step4_rhs, target, s, acomm)
}

/// `h : six = (2·2) + (2·1)`  where `six := 2·(2+1)`  [ldist 2 2 1].
fn ld_six(c: &RingConsts, two: &Expr, one: &Expr) -> Expr {
    c.ldist(two.clone(), two.clone(), one.clone())
}

/// `0 ≤ 2·((A·A)·(B·B))`.
///
/// `A2B2 := (A·A)·(B·B) = (A·B)·(A·B)` [mul_mul_mul_comm A A B B], so
/// `0 ≤ A2B2` from `sq_nonneg (A·B)` carried across the equality; then
/// `0 ≤ 2·A2B2` from `le_add_of_nonneg_right`-style doubling: `2·A2B2 = A2B2 + A2B2`
/// and `0 ≤ A2B2 + A2B2` follows. We build it directly:
///   `0 ≤ A2B2` (subst sq_nonneg (A·B) along (A·B)·(A·B) = A2B2)
///   `0 ≤ 2·A2B2` via `mul_le_mul_of_nonneg_left 2 0 A2B2 (0≤A2B2) (0≤2)` giving
///   `2·0 ≤ 2·A2B2`, and `2·0 = 0`.
fn build_nonneg_two_a2b2(
    c: &RingConsts,
    hc: &HcBoundsConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
) -> Expr {
    let aa = c.mul(a.clone(), a.clone());
    let bb = c.mul(bv.clone(), bv.clone());
    let a2b2 = c.mul(aa.clone(), bb.clone());
    let ab = c.mul(a.clone(), bv.clone());
    let ab_ab = c.mul(ab.clone(), ab.clone());
    let two = c.two();
    let zero = hc.zero();

    // 0 ≤ (A·B)·(A·B)   [sq_nonneg (A·B)]
    let nn_abab = hc.sqnn(ab.clone());
    // (A·B)·(A·B) = (A·A)·(B·B)   [mmmc A B A B]
    let eq_abab = mmmc_c(a, bv, a, bv); // ab_ab = a2b2
                                        // 0 ≤ A2B2   [subst_le_right 0 (ab_ab) (a2b2) eq_abab nn_abab]
    let nn_a2b2 = hc.subst_le_right(
        parent,
        zero.clone(),
        ab_ab.clone(),
        a2b2.clone(),
        eq_abab,
        nn_abab,
    );

    // 0 ≤ 2·A2B2 : mul_le_left 2 0 A2B2 (0≤A2B2) (0≤2) : 2·0 ≤ 2·A2B2; then 2·0 = 0.
    let zle2 = hc.zero_le_two();
    let two_zero = c.mul(two.clone(), zero.clone());
    let two_a2b2 = c.mul(two.clone(), a2b2.clone());
    let bnd = hc.mll(two.clone(), zero.clone(), a2b2.clone(), nn_a2b2, zle2); // 2·0 ≤ 2·A2B2
                                                                              // 2·0 = 0   [mul_zero 2]
    let mul_zero = Expr::app(
        Expr::const_(Name::from_string("Rat.mul_zero"), vec![]),
        two.clone(),
    ); // 2·0 = 0
       // subst LHS: 2·0 → 0 in (2·0 ≤ 2·A2B2) gives 0 ≤ 2·A2B2.
    hc.subst_le_left(parent, two_a2b2, two_zero, zero, mul_zero, bnd)
}

/// `eq_final : ((2·A4 + 2·B4) + 2·(2·((A·A)·(B·B)))) = 2·((A·A+B·B)·(A·A+B·B))`.
///
/// Reverse of the expansion `2·(M·M) = 2·(A4 + B4 + 2·A2B2) = 2A4 + 2B4 + 4A2B2`.
/// We compute `2·(M·M)` forward and `symm`:
///   `M·M = (A4 + B4) + 2·A2B2`               [add_sq_regroup (A·A) (B·B)]
///   `2·(M·M) = 2·((A4+B4) + 2·A2B2)`
///           = `2·(A4+B4) + 2·(2·A2B2)`       [ldist 2 (A4+B4) (2·A2B2)]
///           = `(2·A4 + 2·B4) + 2·(2·A2B2)`   [cong_left, ldist 2 A4 B4]
/// then symm.
fn build_eq_final(c: &RingConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let add_c = c.add_const();
    let mul_c = c.mul_const();
    let two = c.two();
    let aa = c.mul(a.clone(), a.clone());
    let bb = c.mul(bv.clone(), bv.clone());
    let a4 = c.mul(aa.clone(), aa.clone());
    let b4 = c.mul(bb.clone(), bb.clone());
    let a2b2 = c.mul(aa.clone(), bb.clone());
    let m = c.add(aa.clone(), bb.clone());
    let mm = c.mul(m.clone(), m.clone());
    let two_mm = c.mul(two.clone(), mm.clone());

    // h_mm : M·M = (A4 + B4) + 2·A2B2   [add_sq_regroup (A·A) (B·B)]
    let a4_b4 = c.add(a4.clone(), b4.clone());
    let two_a2b2 = c.nmul(two.clone(), a2b2.clone());
    let mm_rhs = c.add(a4_b4.clone(), two_a2b2.clone());
    let h_mm = Expr::apps(
        Expr::const_(Name::from_string("Rat.add_sq_regroup"), vec![]),
        [aa.clone(), bb.clone()],
    );
    // 2·(M·M) = 2·mm_rhs   [cong_right mul over 2]
    let two_mm_rhs = c.mul(two.clone(), mm_rhs.clone());
    let cong_mm = c.cong_right(
        parent,
        &mul_c,
        mm.clone(),
        mm_rhs.clone(),
        two.clone(),
        h_mm,
    );

    // 2·mm_rhs = 2·(A4+B4) + 2·(2·A2B2)   [ldist 2 (A4+B4) (2·A2B2)]
    let two_a4b4 = c.nmul(two.clone(), a4_b4.clone());
    let two_two_a2b2 = c.nmul(two.clone(), two_a2b2.clone());
    let split = c.add(two_a4b4.clone(), two_two_a2b2.clone());
    let ld_mm = c.ldist(two.clone(), a4_b4.clone(), two_a2b2.clone());

    // 2·(A4+B4) = 2·A4 + 2·B4   [ldist 2 A4 B4]; rewrite left summand of split
    let two_a4 = c.nmul(two.clone(), a4.clone());
    let two_b4 = c.nmul(two.clone(), b4.clone());
    let two_a4_two_b4 = c.add(two_a4.clone(), two_b4.clone());
    let ld_a4b4 = c.ldist(two.clone(), a4.clone(), b4.clone());
    let split2 = c.add(two_a4_two_b4.clone(), two_two_a2b2.clone());
    let cl = c.cong_left(
        parent,
        &add_c,
        two_a4b4.clone(),
        two_a4_two_b4.clone(),
        two_two_a2b2.clone(),
        ld_a4b4,
    );

    // chain forward: two_mm = two_mm_rhs = split = split2
    let s = c.trans(
        two_mm.clone(),
        two_mm_rhs.clone(),
        split.clone(),
        cong_mm,
        ld_mm,
    );
    let fwd = c.trans(two_mm.clone(), split.clone(), split2.clone(), s, cl);
    // fwd : 2·(M·M) = (2·A4 + 2·B4) + 2·(2·A2B2)
    // We need the reverse: bound_rhs = 2·(M·M). bound_rhs IS `split2`. symm.
    c.symm(two_mm, split2, fwd)
}
