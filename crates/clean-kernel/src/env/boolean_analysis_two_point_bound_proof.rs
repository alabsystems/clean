// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Proof-term builder for `Rat.fourth_power_rho_two_point_bound` — the
// (2,4)-hypercontractivity two-point inequality.
//
// `include!`d into `boolean_analysis_two_point_bound.rs`; shares its `use`s.
//
// ## Strategy (O'Donnell 9.22, per coordinate)
//
// Let `M := A·A + B·B`, and write the four monomials
//   `A4 := (A·A)·(A·A)`, `B4 := (B·B)·(B·B)`, `A2B2 := (A·A)·(B·B)`,
//   `s := ρ·ρ` (so `ρ⁴ = s·s`).
//
// 1. `Rat.fourth_power_even_pair_expanded A (ρ·B)` gives
//      `(A+ρB)⁴ + (A−ρB)⁴ = (2·A4 + 2·(ρB)⁴) + coeff·((A·A)·((ρB)·(ρB)))`
//    with `coeff := (2·2)+2·(2·2)` (= 12), `ρB := ρ·B`.
//
// 2. Two monomial equalities (pure `Rat` ring facts):
//      `eq_b4   : (ρB)⁴                       = (s·s)·B4`
//      `eq_cross: coeff·((A·A)·((ρB)·(ρB)))   = (6·s)·(2·A2B2)`
//
// 3. B6 coefficient bounds (with `0 ≤ B4`, `0 ≤ 2·A2B2` from `sq_nonneg`):
//      `hc_rho_four_t_le_t  ρ B4    : (s·s)·B4   ≤ B4`
//      `hc_six_rho_sq_t_le_two_t ρ (2·A2B2) : (6·s)·(2·A2B2) ≤ 2·(2·A2B2)`
//    lifted: `2·(ρB)⁴ ≤ 2·B4` (mul_le_left 2) and `cross ≤ 2·(2·A2B2)`.
//
// 4. `add_le_add` assembles `E ≤ (2·A4 + 2·B4) + 2·(2·A2B2)`.
//
// 5. Ring identity `eq_final : (2·A4 + 2·B4) + 2·(2·A2B2) = 2·(M·M)` closes
//    the chain (`subst_le_right`).

use super::boolean_analysis_hc_bounds_proofs::HcBoundsConsts;

/// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
fn massoc_c(a: &Expr, b: &Expr, cc: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
        [a.clone(), b.clone(), cc.clone()],
    )
}

/// `Rat.mul_comm a b : a·b = b·a`.
fn mcomm_c(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
        [a.clone(), b.clone()],
    )
}

/// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
fn mmmc_c(a: &Expr, b: &Expr, cc: &Expr, dd: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
        [a.clone(), b.clone(), cc.clone(), dd.clone()],
    )
}

/// `Rat.add_le_add a b c d (h_ab : a ≤ b) (h_cd : c ≤ d) : a+c ≤ b+d`.
///
/// Binder order matches the registered theorem
/// `∀ (a b c d : Rat), a ≤ b → c ≤ d → a+c ≤ b+d`.
fn add_le_add(a: &Expr, b: &Expr, cc: &Expr, dd: &Expr, h_ab: Expr, h_cd: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_le_add"), vec![]),
        [a.clone(), b.clone(), cc.clone(), dd.clone(), h_ab, h_cd],
    )
}

/// `Rat.le_refl a : a ≤ a`.
fn le_refl(a: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
        a.clone(),
    )
}

/// Build the type + proof of `Rat.fourth_power_rho_two_point_bound`.
fn build_two_point_bound(c: &RingConsts) -> (Expr, Expr) {
    let hc = HcBoundsConsts::new();
    let mul_c = c.mul_const();

    // ── Type: ∀ A B ρ, 3·(ρ·ρ) ≤ 1 → (A+ρB)⁴+(A−ρB)⁴ ≤ 2·(M·M).
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.rat());
        let (bv_id, bv) = b.fresh_local(c.rat());
        let (rho_id, rho) = b.fresh_local(c.rat());
        let s = c.mul(rho.clone(), rho.clone()); // ρ·ρ
        let h_ty = hc.le(c.mul(hc.three(), s.clone()), c.one()); // 3·(ρ·ρ) ≤ 1
        let (h_id, _) = b.fresh_local(h_ty.clone());

        let rho_b = c.mul(rho.clone(), bv.clone());
        let sum = c.add(a.clone(), rho_b.clone());
        let diff = c.sub(a.clone(), rho_b.clone());
        let lhs = c.add(pow4_of(c, &sum), pow4_of(c, &diff));
        let m = c.add(c.mul(a.clone(), a.clone()), c.mul(bv.clone(), bv.clone()));
        let rhs = c.nmul(c.two(), c.mul(m.clone(), m.clone())); // 2·(M·M)
        let concl = hc.le(lhs, rhs);

        let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
        let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    // ── Proof.
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.rat());
        let (bv_id, bv) = b.fresh_local(c.rat());
        let (rho_id, rho) = b.fresh_local(c.rat());
        let s = c.mul(rho.clone(), rho.clone()); // ρ·ρ
        let h_ty = hc.le(c.mul(hc.three(), s.clone()), c.one());
        let (h_id, h_bound) = b.fresh_local(h_ty.clone());

        // Monomials.
        let aa = c.mul(a.clone(), a.clone());
        let bb = c.mul(bv.clone(), bv.clone());
        let a4 = c.mul(aa.clone(), aa.clone());
        let b4 = c.mul(bb.clone(), bb.clone());
        let a2b2 = c.mul(aa.clone(), bb.clone());
        let two = c.two();
        let two_two = c.mul(two.clone(), two.clone());
        let coeff = c.add(two_two.clone(), c.nmul(two.clone(), two_two.clone())); // 12
        let rho_b = c.mul(rho.clone(), bv.clone());
        let rb_sq = c.mul(rho_b.clone(), rho_b.clone()); // (ρB)·(ρB)
        let rb4 = c.mul(rb_sq.clone(), rb_sq.clone()); // (ρB)⁴
        let ss = c.mul(s.clone(), s.clone()); // ρ⁴ = (ρ·ρ)·(ρ·ρ)
        let six = hc.six();
        let six_s = c.mul(six.clone(), s.clone()); // 6·(ρ·ρ)
        let two_a2b2 = c.nmul(two.clone(), a2b2.clone()); // 2·A²B²

        // E := (2·A4 + 2·(ρB)⁴) + coeff·((A·A)·((ρB)·(ρB)))   [expanded RHS at (A,ρB)]
        let two_a4 = c.nmul(two.clone(), a4.clone());
        let two_rb4 = c.nmul(two.clone(), rb4.clone());
        let cross = c.mul(coeff.clone(), c.mul(aa.clone(), rb_sq.clone())); // coeff·(A²·(ρB)²)
        let e_left = c.add(two_a4.clone(), two_rb4.clone());
        let e = c.add(e_left.clone(), cross.clone());

        // h_expand : LHS = E   [fourth_power_even_pair_expanded A (ρ·B)]
        let sum = c.add(a.clone(), rho_b.clone());
        let diff = c.sub(a.clone(), rho_b.clone());
        let lhs = c.add(pow4_of(c, &sum), pow4_of(c, &diff));
        let h_expand = Expr::apps(
            Expr::const_(
                Name::from_string("Rat.fourth_power_even_pair_expanded"),
                vec![],
            ),
            [a.clone(), rho_b.clone()],
        );

        // ── eq_b4 : (ρB)⁴ = ρ⁴·B4   i.e. ((ρB)·(ρB))·((ρB)·(ρB)) = ((ρ·ρ)·(ρ·ρ))·((B·B)·(B·B)).
        let eq_b4 = build_eq_rb4(c, &b, &rho, &bv);
        // ── eq_cross : coeff·((A·A)·((ρB)·(ρB))) = (6·s)·(2·A2B2).
        let eq_cross = build_eq_cross(c, &b, &a, &bv, &rho, &coeff, &six);

        // ── B6 nonneg side conditions.
        // 0 ≤ B4 = sq_nonneg (B·B)
        let nn_b4 = hc.sqnn(bb.clone());
        // 0 ≤ 2·A2B2: 2·((A·A)·(B·B)) — build from sq_nonneg via the helper.
        let nn_two_a2b2 = build_nonneg_two_a2b2(c, &hc, &b, &a, &bv);

        // ── B6 bounds (instantiated).
        // hc_rho_four_t_le_t ρ B4 h_bound nn_b4 : (ρ⁴)·B4 ≤ B4
        let rho_four_b4 = c.mul(ss.clone(), b4.clone());
        let bnd_rho4 = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.hc_rho_four_t_le_t"), vec![]),
            [rho.clone(), b4.clone(), h_bound.clone(), nn_b4],
        ); // (ρ⁴)·B4 ≤ B4
           // lift over 2·: 2·((ρ⁴)·B4) ≤ 2·B4 via mul_le_left 2 ... ... 0≤2.
        let two_rho4_b4 = c.nmul(two.clone(), rho_four_b4.clone());
        let two_b4 = c.nmul(two.clone(), b4.clone());
        let zle2 = hc.zero_le_two();
        let bnd_two_rho4_b4 = hc.mll(
            two.clone(),
            rho_four_b4.clone(),
            b4.clone(),
            bnd_rho4,
            zle2.clone(),
        ); // 2·(ρ⁴·B4) ≤ 2·B4

        // hc_six_rho_sq_t_le_two_t ρ (2·A2B2) h_bound nn_two_a2b2 : (6·s)·(2·A2B2) ≤ 2·(2·A2B2)
        let six_s_t = c.mul(six_s.clone(), two_a2b2.clone());
        let two_two_a2b2 = c.nmul(two.clone(), two_a2b2.clone());
        let bnd_six = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.hc_six_rho_sq_t_le_two_t"),
                vec![],
            ),
            [rho.clone(), two_a2b2.clone(), h_bound.clone(), nn_two_a2b2],
        ); // (6·s)·(2·A2B2) ≤ 2·(2·A2B2)

        // ── Rewrite E's legs to the B6-input forms, then bound.
        // Leg 2: 2·(ρB)⁴ → 2·(ρ⁴·B4) via cong_right mul (2 fixed) on eq_b4.
        let two_rb4_eq = c.cong_right(
            &b,
            &mul_c,
            rb4.clone(),
            rho_four_b4.clone(),
            two.clone(),
            eq_b4,
        );
        // now: 2·(ρB)⁴ = 2·(ρ⁴·B4); use subst_le_left to carry the bound.
        // bound on 2·(ρB)⁴: from bnd_two_rho4_b4 : 2·(ρ⁴·B4) ≤ 2·B4, subst LHS back to 2·(ρB)⁴.
        let two_rb4_eq_sym = c.symm(two_rb4.clone(), two_rho4_b4.clone(), two_rb4_eq); // 2·(ρ⁴B4) = 2·(ρB)⁴
        let bnd_two_rb4 = hc.subst_le_left(
            &b,
            two_b4.clone(),
            two_rho4_b4.clone(),
            two_rb4.clone(),
            two_rb4_eq_sym,
            bnd_two_rho4_b4,
        ); // 2·(ρB)⁴ ≤ 2·B4

        // Leg 3: cross = coeff·((A·A)·((ρB)·(ρB))) → (6·s)·(2·A2B2) via eq_cross;
        // bound on cross: from bnd_six : (6·s)·(2·A2B2) ≤ 2·(2·A2B2), subst LHS to cross.
        let eq_cross_sym = c.symm(cross.clone(), six_s_t.clone(), eq_cross); // (6·s)·(2·A2B2) = cross
        let bnd_cross = hc.subst_le_left(
            &b,
            two_two_a2b2.clone(),
            six_s_t.clone(),
            cross.clone(),
            eq_cross_sym,
            bnd_six,
        ); // cross ≤ 2·(2·A2B2)

        // ── Combine: e_left = 2·A4 + 2·(ρB)⁴ ≤ 2·A4 + 2·B4.
        // add_le_add a b c d (a≤b) (c≤d) : a+c ≤ b+d.
        // Want 2A4+2(ρB)⁴ ≤ 2A4+2B4: a=2A4, b=2A4, c=2(ρB)⁴, d=2B4.
        let refl_two_a4 = le_refl(&two_a4);
        let e_left_bound_rhs = c.add(two_a4.clone(), two_b4.clone());
        let bnd_e_left = add_le_add(
            &two_a4,
            &two_a4,
            &two_rb4,
            &two_b4,
            refl_two_a4,
            bnd_two_rb4,
        ); // (2A4 + 2(ρB)⁴) ≤ (2A4 + 2B4)

        // ── E = e_left + cross ≤ (2A4+2B4) + 2·(2·A2B2).
        // Want e_left+cross ≤ e_left_bound_rhs + two_two_a2b2:
        //   a=e_left, b=e_left_bound_rhs, c=cross, d=two_two_a2b2.
        let bound_rhs = c.add(e_left_bound_rhs.clone(), two_two_a2b2.clone());
        let bnd_e = add_le_add(
            &e_left,
            &e_left_bound_rhs,
            &cross,
            &two_two_a2b2,
            bnd_e_left,
            bnd_cross,
        ); // E ≤ bound_rhs

        // ── eq_final : bound_rhs = 2·(M·M).
        let m = c.add(aa.clone(), bb.clone());
        let mm = c.mul(m.clone(), m.clone());
        let two_mm = c.nmul(two.clone(), mm.clone());
        let eq_final = build_eq_final(c, &b, &a, &bv);
        // bound_rhs ≤ 2·(M·M): subst RHS of bnd_e from bound_rhs to two_mm.
        let bnd_e_final = hc.subst_le_right(
            &b,
            e.clone(),
            bound_rhs.clone(),
            two_mm.clone(),
            eq_final,
            bnd_e,
        ); // E ≤ 2·(M·M)

        // ── Chain LHS = E ≤ 2·(M·M): subst LHS of bnd_e_final from E to LHS.
        let h_expand_sym = c.symm(lhs.clone(), e.clone(), h_expand); // E = LHS
        let proof = hc.subst_le_left(
            &b,
            two_mm.clone(),
            e.clone(),
            lhs.clone(),
            h_expand_sym,
            bnd_e_final,
        ); // LHS ≤ 2·(M·M)

        let e_lam = b.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
        let e_lam = b.mk_lam(rho_id, BinderInfo::Default, c.rat(), e_lam);
        let e_lam = b.mk_lam(bv_id, BinderInfo::Default, c.rat(), e_lam);
        let e_lam = b.mk_lam(a_id, BinderInfo::Default, c.rat(), e_lam);
        b.finish(e_lam)
    };

    (ty, value)
}

/// `eq_b4 : ((ρB)·(ρB))·((ρB)·(ρB)) = ((ρ·ρ)·(ρ·ρ))·((B·B)·(B·B))`
/// where `ρB := ρ·B`.
///
/// Two `mul_mul_mul_comm` regroups: first on the outer product
/// `((ρB)·(ρB))·((ρB)·(ρB)) = ((ρB)·(ρB))·((ρB)·(ρB))` — actually we regroup the
/// inner squares. `(ρB)·(ρB) = (ρ·ρ)·(B·B)` [mmmc ρ B ρ B], then the outer
/// `((ρ·ρ)·(B·B))·((ρ·ρ)·(B·B)) = ((ρ·ρ)·(ρ·ρ))·((B·B)·(B·B))` [mmmc].
fn build_eq_rb4(c: &RingConsts, parent: &EnvDeclBuilder, rho: &Expr, bv: &Expr) -> Expr {
    let mul_c = c.mul_const();
    let rho_b = c.mul(rho.clone(), bv.clone());
    let rb_sq = c.mul(rho_b.clone(), rho_b.clone()); // (ρB)·(ρB)
    let rb4 = c.mul(rb_sq.clone(), rb_sq.clone());
    let s = c.mul(rho.clone(), rho.clone()); // ρ·ρ
    let bb = c.mul(bv.clone(), bv.clone()); // B·B
    let s_bb = c.mul(s.clone(), bb.clone()); // (ρ·ρ)·(B·B)
    let ss = c.mul(s.clone(), s.clone());
    let bbbb = c.mul(bb.clone(), bb.clone());
    let target = c.mul(ss.clone(), bbbb.clone()); // ((ρ·ρ)·(ρ·ρ))·((B·B)·(B·B))

    // step1 : (ρB)·(ρB) = (ρ·ρ)·(B·B)   [mmmc ρ B ρ B]
    let step1 = mmmc_c(rho, bv, rho, bv);
    // rewrite rb4's left factor: rb_sq·rb_sq = s_bb·rb_sq  [cong_left mul]
    let cl = c.cong_left(
        parent,
        &mul_c,
        rb_sq.clone(),
        s_bb.clone(),
        rb_sq.clone(),
        step1.clone(),
    );
    let sbb_rbsq = c.mul(s_bb.clone(), rb_sq.clone());
    // rewrite right factor: s_bb·rb_sq = s_bb·s_bb  [cong_right mul]
    let cr = c.cong_right(
        parent,
        &mul_c,
        rb_sq.clone(),
        s_bb.clone(),
        s_bb.clone(),
        step1,
    );
    let sbb_sbb = c.mul(s_bb.clone(), s_bb.clone());
    // step_both : rb4 = s_bb·s_bb
    let step_both = c.trans(rb4.clone(), sbb_rbsq.clone(), sbb_sbb.clone(), cl, cr);
    // step2 : s_bb·s_bb = ((ρ·ρ)·(ρ·ρ))·((B·B)·(B·B))   [mmmc (ρ·ρ) (B·B) (ρ·ρ) (B·B)]
    let step2 = mmmc_c(&s, &bb, &s, &bb);
    c.trans(rb4, sbb_sbb, target, step_both, step2)
}

/// `eq_cross : coeff·((A·A)·((ρB)·(ρB))) = (6·(ρ·ρ))·(2·((A·A)·(B·B)))`
/// with `coeff := (2·2)+2·(2·2)` (= 12), `6 := 2·3`, `ρB := ρ·B`.
///
/// Both sides equal `12·ρ²·A²·B²`. We bring both to the common normal form
/// `coeff·(((A·A)·(B·B))·(ρ·ρ))` and use `coeff = 6·2` plus associativity.
fn build_eq_cross(
    c: &RingConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
    rho: &Expr,
    coeff: &Expr,
    six: &Expr,
) -> Expr {
    let mul_c = c.mul_const();
    let two = c.two();
    let aa = c.mul(a.clone(), a.clone());
    let bb = c.mul(bv.clone(), bv.clone());
    let a2b2 = c.mul(aa.clone(), bb.clone());
    let s = c.mul(rho.clone(), rho.clone());
    let rho_b = c.mul(rho.clone(), bv.clone());
    let rb_sq = c.mul(rho_b.clone(), rho_b.clone()); // (ρB)·(ρB)

    // LHS = coeff·((A·A)·((ρB)·(ρB)))
    let lhs_inner = c.mul(aa.clone(), rb_sq.clone());
    let lhs = c.mul(coeff.clone(), lhs_inner.clone());

    // step_rbsq : (ρB)·(ρB) = (ρ·ρ)·(B·B)   [mmmc ρ B ρ B]
    let s_bb = c.mul(s.clone(), bb.clone());
    let step_rbsq = mmmc_c(rho, bv, rho, bv);
    // lhs_inner = (A·A)·((ρ·ρ)·(B·B))   [cong_right mul over A·A]
    let inner2 = c.mul(aa.clone(), s_bb.clone());
    let cong_inner = c.cong_right(
        parent,
        &mul_c,
        rb_sq.clone(),
        s_bb.clone(),
        aa.clone(),
        step_rbsq,
    );
    // lift over coeff: lhs = coeff·inner2
    let lhs2 = c.mul(coeff.clone(), inner2.clone());
    let cong_lhs = c.cong_right(
        parent,
        &mul_c,
        lhs_inner.clone(),
        inner2.clone(),
        coeff.clone(),
        cong_inner,
    );

    // Now both LHS-side `coeff·((A·A)·((ρ·ρ)·(B·B)))` and the RHS
    // `(6·s)·(2·((A·A)·(B·B)))` are closed `Rat` products of the SAME six atoms
    // {coeff↔6·2 split, A·A, B·B, ρ·ρ}. We finish via the explicit normal-form
    // bridge `build_eq_cross_tail`, which rewrites `coeff·((A·A)·((ρ·ρ)·(B·B)))`
    // into `(6·(ρ·ρ))·(2·((A·A)·(B·B)))`.
    let rhs_tail = build_eq_cross_tail(c, parent, &aa, &bb, &s, coeff, six, &two, &a2b2);
    // rhs_tail : coeff·inner2 = (6·s)·(2·A2B2)
    c.trans(lhs, lhs2, rhs_tail.1, cong_lhs, rhs_tail.0)
}

/// Returns `(proof, target)` where
///   `proof : coeff·((A·A)·((ρ·ρ)·(B·B))) = (6·(ρ·ρ))·(2·((A·A)·(B·B)))`
/// and `target` is that RHS. `aa = A·A`, `bb = B·B`, `s = ρ·ρ`,
/// `a2b2 = (A·A)·(B·B)`, `coeff = (2·2)+2·(2·2)`, `six = 2·3`.
///
/// Plan — rewrite both factors of `coeff·((A·A)·((ρ·ρ)·(B·B)))` into the target:
///   inner  `(A·A)·((ρ·ρ)·(B·B))`
///        = `(A·A)·((B·B)·(ρ·ρ))`        [cong_right mul, mul_comm (ρ·ρ) (B·B)]
///        = `((A·A)·(B·B))·(ρ·ρ)`        [symm mul_assoc → (A2B2)·s]
///   so inner = `A2B2 · s`. Then
///   `coeff·(A2B2·s)`
///        = `(coeff·A2B2)·s`             [symm mul_assoc coeff A2B2 s]
///   and the target `(6·s)·(2·A2B2)`:
///        = `6·(s·(2·A2B2))`             [mul_assoc 6 s (2·A2B2)]
///        = `6·(2·(A2B2·s))`            ... this path is long. Instead we prove
///   the target equals `(coeff·A2B2)·s` by computing both as `12·A2B2·s`-shaped
///   closed products through `coeff = 6·2`, commutativity and associativity.
fn build_eq_cross_tail(
    c: &RingConsts,
    parent: &EnvDeclBuilder,
    aa: &Expr,
    bb: &Expr,
    s: &Expr,
    coeff: &Expr,
    six: &Expr,
    two: &Expr,
    a2b2: &Expr,
) -> (Expr, Expr) {
    let mul_c = c.mul_const();
    // inner = (A·A)·((ρ·ρ)·(B·B))
    let s_bb = c.mul(s.clone(), bb.clone());
    let inner = c.mul(aa.clone(), s_bb.clone());
    let lhs = c.mul(coeff.clone(), inner.clone());

    // (1) inner = (A·A)·((B·B)·(ρ·ρ))   [cong_right mul (A·A), mul_comm s bb]
    let bb_s = c.mul(bb.clone(), s.clone());
    let comm_sbb = mcomm_c(s, bb); // (ρ·ρ)·(B·B) = (B·B)·(ρ·ρ)
    let inner_b = c.mul(aa.clone(), bb_s.clone());
    let cong1 = c.cong_right(
        parent,
        &mul_c,
        s_bb.clone(),
        bb_s.clone(),
        aa.clone(),
        comm_sbb,
    );
    // (2) (A·A)·((B·B)·(ρ·ρ)) = ((A·A)·(B·B))·(ρ·ρ)   [symm mul_assoc A2 B2 s]
    let assoc = massoc_c(aa, bb, s); // ((A·A)·(B·B))·(ρ·ρ) = (A·A)·((B·B)·(ρ·ρ))
    let a2b2_s = c.mul(a2b2.clone(), s.clone());
    let assoc_sym = c.symm(a2b2_s.clone(), inner_b.clone(), assoc); // inner_b = a2b2·s
                                                                    // inner = a2b2·s
    let inner_eq = c.trans(
        inner.clone(),
        inner_b.clone(),
        a2b2_s.clone(),
        cong1,
        assoc_sym,
    );
    // lift over coeff: lhs = coeff·(a2b2·s)
    let coeff_a2b2s = c.mul(coeff.clone(), a2b2_s.clone());
    let cong_lhs = c.cong_right(
        parent,
        &mul_c,
        inner.clone(),
        a2b2_s.clone(),
        coeff.clone(),
        inner_eq,
    );

    // (3) coeff·(a2b2·s) = (coeff·a2b2)·s   [symm mul_assoc coeff a2b2 s]
    let assoc2 = massoc_c(coeff, a2b2, s); // (coeff·a2b2)·s = coeff·(a2b2·s)
    let coeff_a2b2 = c.mul(coeff.clone(), a2b2.clone());
    let coeff_a2b2_then_s = c.mul(coeff_a2b2.clone(), s.clone());
    let assoc2_sym = c.symm(coeff_a2b2_then_s.clone(), coeff_a2b2s.clone(), assoc2);
    let lhs_to = c.trans(
        lhs.clone(),
        coeff_a2b2s.clone(),
        coeff_a2b2_then_s.clone(),
        cong_lhs,
        assoc2_sym,
    );
    // now lhs = (coeff·a2b2)·s

    // ── Target side: (6·s)·(2·a2b2).
    let six_s = c.mul(six.clone(), s.clone());
    let two_a2b2 = c.mul(two.clone(), a2b2.clone());
    let target = c.mul(six_s.clone(), two_a2b2.clone());

    // Bring target to (coeff·a2b2)·s as well, then trans through.
    // (T1) (6·s)·(2·a2b2) = (6·(2·a2b2))·s    via mmmc? Use mul_mul_mul_comm:
    //      (6·s)·(2·a2b2) = (6·2)·(s·a2b2)     [mmmc 6 s 2 a2b2]
    let six_two = c.mul(six.clone(), two.clone());
    let s_a2b2 = c.mul(s.clone(), a2b2.clone());
    let sixtwo_sa2b2 = c.mul(six_two.clone(), s_a2b2.clone());
    let t1 = mmmc_c(six, s, two, a2b2); // target = (6·2)·(s·a2b2)
                                        // (T2) (6·2)·(s·a2b2) = (6·2)·(a2b2·s)    [cong_right mul, mul_comm s a2b2]
    let a2b2_s2 = c.mul(a2b2.clone(), s.clone());
    let comm_sa = mcomm_c(s, a2b2);
    let sixtwo_a2b2s = c.mul(six_two.clone(), a2b2_s2.clone());
    let t2 = c.cong_right(
        parent,
        &mul_c,
        s_a2b2.clone(),
        a2b2_s2.clone(),
        six_two.clone(),
        comm_sa,
    );
    // (T3) (6·2)·(a2b2·s) = ((6·2)·a2b2)·s    [symm mul_assoc (6·2) a2b2 s]
    let sixtwo_a2b2 = c.mul(six_two.clone(), a2b2.clone());
    let sixtwo_a2b2_s = c.mul(sixtwo_a2b2.clone(), s.clone());
    let assoc_t = massoc_c(&six_two, a2b2, s); // ((6·2)·a2b2)·s = (6·2)·(a2b2·s)
    let assoc_t_sym = c.symm(sixtwo_a2b2_s.clone(), sixtwo_a2b2s.clone(), assoc_t);
    // (T4) ((6·2)·a2b2)·s = (coeff·a2b2)·s    [cong_left mul (·s), cong_left on (6·2)→coeff over a2b2]
    //   need h_coeff : 6·2 = coeff   (coeff := (2·2)+2·(2·2)).
    let h_coeff = build_six_two_eq_coeff(c, parent, six, two, coeff);
    // ((6·2)·a2b2) = (coeff·a2b2)   [cong_left mul over a2b2]
    let cong_co = c.cong_left(
        parent,
        &mul_c,
        six_two.clone(),
        coeff.clone(),
        a2b2.clone(),
        h_coeff,
    );
    // lift over (·s): ((6·2)·a2b2)·s = (coeff·a2b2)·s
    let t4 = c.cong_left(
        parent,
        &mul_c,
        sixtwo_a2b2.clone(),
        coeff_a2b2.clone(),
        s.clone(),
        cong_co,
    );

    // target chain: target = sixtwo_sa2b2 = sixtwo_a2b2s = sixtwo_a2b2_s = coeff_a2b2_then_s
    let tc1 = c.trans(
        target.clone(),
        sixtwo_sa2b2.clone(),
        sixtwo_a2b2s.clone(),
        t1,
        t2,
    );
    let tc2 = c.trans(
        target.clone(),
        sixtwo_a2b2s.clone(),
        sixtwo_a2b2_s.clone(),
        tc1,
        assoc_t_sym,
    );
    let target_to = c.trans(
        target.clone(),
        sixtwo_a2b2_s.clone(),
        coeff_a2b2_then_s.clone(),
        tc2,
        t4,
    );
    // target = (coeff·a2b2)·s ; symm to get (coeff·a2b2)·s = target
    let target_from = c.symm(target.clone(), coeff_a2b2_then_s.clone(), target_to);

    // proof : lhs = target   [trans lhs_to (= (coeff·a2b2)·s) and target_from]
    let proof = c.trans(lhs, coeff_a2b2_then_s, target.clone(), lhs_to, target_from);
    (proof, target)
}

/// `h_coeff : (6·2) = ((2·2)+2·(2·2))`  where `6 := 2·3`, `2 := 1+1`, `3 := 2+1`.
///
/// Both are closed `Rat` numerals equal to `12`. Proved by `Rat.numeral`-style
/// expansion: `6·2 = (2·3)·2`, distribute, and likewise for the coeff side,
/// using `left_distrib`/`right_distrib` and `one_mul`/associativity to reach the
/// common `((1+1)+...)`-shape. Built by `build_twelve_eq` below.
fn build_six_two_eq_coeff(
    c: &RingConsts,
    parent: &EnvDeclBuilder,
    six: &Expr,
    two: &Expr,
    coeff: &Expr,
) -> Expr {
    // Strategy: show both `6·2` and `coeff` equal the canonical `(2·2)+(2·(2·2))`
    // through pure arithmetic, but since `coeff` IS `(2·2)+2·(2·2)` by
    // construction, we only need `6·2 = (2·2)+(2·(2·2))`.
    build_twelve_eq(c, parent, six, two, coeff)
}

include!("boolean_analysis_two_point_bound_num.rs");
