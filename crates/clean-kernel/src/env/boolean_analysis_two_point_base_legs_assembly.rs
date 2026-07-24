// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// The (A)-conditional assembly of the two-point base.
//
// `include!`d into `boolean_analysis_two_point_base_legs.rs`.
//
// `two_point_base_43_of_A` discharges the a=1 instance of the landed
// `two_point_base_43` PIN MODULO the single hard lemma (A) `H ≥ S`:
//
//   ∀ (b : Rat)(α β : NNReal)(hm : 0 ≤ LHS)(hS : 0 ≤ S)
//     (ha : NNReal.le (NNReal.ofRat S hS) (½·(α+β))),
//       NNReal.le (NNReal.ofRat LHS hm) (((H·H)·H))
//
// with `H := ½·(α+β)`, `S := 1 + (2/9)·(b·b)`, `LHS := (1 + (2/3)·(b·b)) +
// (1/81)·((b·b)·(b·b))`. The chain:
//   (B)   Rat.le LHS S³                                  -- leg (B), this crate
//   ↦     NNReal.le (ofRat LHS) (ofRat S³)               -- ofRat_le_ofRat
//   =     NNReal.le (ofRat LHS) ((ofRat S)³)             -- ofRat-cube homomorphism
//   ≤     NNReal.le ((ofRat S)³) (H³)                    -- cube_le_cube_of_le ha
//   ⟹     NNReal.le (ofRat LHS) (H³)                     -- NNReal.le.trans.
//
// (A) = `ha` is an EXPLICIT hypothesis (NOT an axiom, NOT refl-circular).

impl Environment {
    /// `BoolAnalysis.two_point_base_43_of_A` — the conditional reduction of the
    /// (a=1) two-point base to the single hard lemma (A). See module header.
    fn register_two_point_base_43_of_a(&mut self, c: &TwoPointLegConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.two_point_base_43_of_A");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_two_point_base_43_of_a(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The pivot `S := 1 + (2/9)·(b·b)`.
fn pivot_s(c: &TwoPointLegConsts, bb: &Expr) -> Expr {
    c.add(c.rat_one.clone(), c.mul(c.frac(2, 9), bb.clone()))
}

/// `(type, value)` for `two_point_base_43_of_A`.
fn build_two_point_base_43_of_a(c: &TwoPointLegConsts) -> (Expr, Expr) {
    // Shared binder schema builder (used identically for the Pi type and the
    // Lambda value), returning the open conclusion + the bound atoms.
    //
    //   b : Rat, α β : NNReal, hm : 0 ≤ LHS, hS : 0 ≤ S, ha : ofRat S hS ≤ H.

    // ── type ──
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (bv_id, bv) = b.fresh_local(c.rat.clone());
        let (al_id, al) = b.fresh_local(c.nnreal.clone());
        let (be_id, be) = b.fresh_local(c.nnreal.clone());
        let bb = c.mul(bv.clone(), bv.clone());
        let lhs = moment_lhs(c, &bb);
        let s = pivot_s(c, &bb);
        let hm_ty = c.nonneg(lhs.clone());
        let (hm_id, hm) = b.fresh_local(hm_ty.clone());
        let hs_ty = c.nonneg(s.clone());
        let (hs_id, hs) = b.fresh_local(hs_ty.clone());
        let h = nn_half_mean(c, &al, &be); // H = ½·(α+β)
        let ha_ty = c.nnle(c.ofrat(&s, &hs), h.clone());
        let (ha_id, _ha) = b.fresh_local(ha_ty.clone());

        let concl = c.nnle(c.ofrat(&lhs, &hm), c.nncube(&h));

        let e = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, concl);
        let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty, e);
        let e = b.mk_pi(hm_id, BinderInfo::Default, hm_ty, e);
        let e = b.mk_pi(be_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(al_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e))
    };

    // ── value ──
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (bv_id, bv) = b.fresh_local(c.rat.clone());
        let (al_id, al) = b.fresh_local(c.nnreal.clone());
        let (be_id, be) = b.fresh_local(c.nnreal.clone());
        let bb = c.mul(bv.clone(), bv.clone());
        let lhs = moment_lhs(c, &bb);
        let s = pivot_s(c, &bb);
        let hm_ty = c.nonneg(lhs.clone());
        let (hm_id, hm) = b.fresh_local(hm_ty.clone());
        let hs_ty = c.nonneg(s.clone());
        let (hs_id, hs) = b.fresh_local(hs_ty.clone());
        let h = nn_half_mean(c, &al, &be); // H = ½·(α+β)
        let ha_ty = c.nnle(c.ofrat(&s, &hs), h.clone());
        let (ha_id, ha) = b.fresh_local(ha_ty.clone());

        let s_cube = c.cube(&s); // (S·S)·S  (Rat)
        let of_lhs = c.ofrat(&lhs, &hm);
        let of_s = c.ofrat(&s, &hs);

        // 0 ≤ S³ : needed for `ofRat S³`. S³ ≥ 0 since `mul_nonneg` of nonneg S.
        let h_ss_nn = c.mul_nonneg(&s, &s, hs.clone(), hs.clone()); // 0 ≤ S·S
        let ss = c.mul(s.clone(), s.clone());
        let h_s3_nn = c.mul_nonneg(&ss, &s, h_ss_nn, hs.clone()); // 0 ≤ (S·S)·S
        let of_s3 = c.ofrat(&s_cube, &h_s3_nn);

        // (B) at b : Rat.le LHS S³.
        let leg_b = Expr::app(
            Expr::const_(
                Name::from_string("BoolAnalysis.two_point_S_cube_ge_moment"),
                vec![],
            ),
            bv.clone(),
        );

        // step1 : NNReal.le (ofRat LHS hm) (ofRat S³ h_s3).
        //   ofRat_le_ofRat LHS S³ hm h_s3 (B).
        let step1 = Expr::apps(
            c.nnreal_ofrat_le_ofrat.clone(),
            [
                lhs.clone(),
                s_cube.clone(),
                hm.clone(),
                h_s3_nn.clone(),
                leg_b,
            ],
        );

        // h_hom : ofRat S³ h_s3 = (ofRat S hs)³   (the cube homomorphism).
        let h_hom = build_ofrat_cube_hom(c, &b, &s, &hs, &h_ss_nn_dummy(c, &s, &hs), &h_s3_nn);

        // step2 : NNReal.le (ofRat LHS) ((ofRat S)³)   (transport step1 along h_hom).
        let of_s_cube = c.nncube(&of_s);
        let motive2 = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = m.fresh_local(c.nnreal.clone());
            let body = c.nnle(of_lhs.clone(), z);
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let step2 = c.subst_nn(motive2, of_s3.clone(), of_s_cube.clone(), h_hom, step1);

        // step3 : NNReal.le ((ofRat S)³) (H³)  := cube_le_cube_of_le (ofRat S) H ha.
        let step3 = Expr::apps(
            c.nnreal_cube_le_cube_of_le.clone(),
            [of_s.clone(), h.clone(), ha],
        );

        // body : NNReal.le (ofRat LHS) (H³)  := le.trans (ofRat LHS) ((ofRat S)³) (H³) step2 step3.
        let h_cube = c.nncube(&h);
        let body = Expr::apps(
            c.nnreal_le_trans.clone(),
            [of_lhs.clone(), of_s_cube, h_cube, step2, step3],
        );

        let e = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, body);
        let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty, e);
        let e = b.mk_lam(hm_id, BinderInfo::Default, hm_ty, e);
        let e = b.mk_lam(be_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(al_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e))
    };

    (ty, value)
}

/// `H := NNReal.mul half (NNReal.add α β)`, `half := ofRat (1/2) (0 ≤ 1/2)`.
fn nn_half_mean(c: &TwoPointLegConsts, al: &Expr, be: &Expr) -> Expr {
    let half_pos = c.lit_nonneg(1, 2);
    let half = c.ofrat(&c.frac(1, 2), &half_pos);
    c.nnmul(half, c.nnadd(al.clone(), be.clone()))
}

/// `0 ≤ S·S` (helper to keep the homomorphism builder's signature uniform).
fn h_ss_nn_dummy(c: &TwoPointLegConsts, s: &Expr, hs: &Expr) -> Expr {
    c.mul_nonneg(s, s, hs.clone(), hs.clone())
}

/// `ofRat (S³) h_s3 = (ofRat S hs) · (ofRat S hs) · (ofRat S hs)`  (left-nested
/// cube), via two `NNReal.ofRat_mul` collapses (in reverse):
///   `(ofRat S · ofRat S) · ofRat S
///      =[ofRat_mul S S]·_   ofRat (S·S) · ofRat S
///      =[ofRat_mul (S·S) S]  ofRat ((S·S)·S) = ofRat S³`.
/// We return the equation `ofRat S³ = (ofRat S)³` (so the caller can rewrite the
/// `ofRat S³` on step1's RHS into `(ofRat S)³`).
fn build_ofrat_cube_hom(
    c: &TwoPointLegConsts,
    parent: &EnvDeclBuilder,
    s: &Expr,
    hs: &Expr,
    h_ss_nn: &Expr,
    h_s3_nn: &Expr,
) -> Expr {
    let _ = parent;
    let of_s = c.ofrat(s, hs);
    let ss = c.mul(s.clone(), s.clone()); // S·S (Rat)
    let s_cube = c.mul(ss.clone(), s.clone()); // (S·S)·S (Rat)
    let of_ss = c.ofrat(&ss, h_ss_nn);
    let of_s3 = c.ofrat(&s_cube, h_s3_nn);

    // m1 : ofRat S · ofRat S = ofRat (S·S)        [ofRat_mul S S hs hs h_ss_nn].
    let m1 = Expr::apps(
        c.nnreal_ofrat_mul.clone(),
        [
            s.clone(),
            s.clone(),
            hs.clone(),
            hs.clone(),
            h_ss_nn.clone(),
        ],
    ); // (ofRat S · ofRat S) = ofRat (S·S)
       // m2 : ofRat (S·S) · ofRat S = ofRat ((S·S)·S) [ofRat_mul (S·S) S h_ss_nn hs h_s3_nn].
    let m2 = Expr::apps(
        c.nnreal_ofrat_mul.clone(),
        [
            ss.clone(),
            s.clone(),
            h_ss_nn.clone(),
            hs.clone(),
            h_s3_nn.clone(),
        ],
    ); // (ofRat (S·S) · ofRat S) = ofRat ((S·S)·S)

    // (ofRat S · ofRat S) · ofRat S
    //   =[congr_mul_left of_s m1]  ofRat (S·S) · ofRat S
    //   =[m2]                      ofRat ((S·S)·S) = ofRat S³.
    let of_s_sq = c.nnmul(of_s.clone(), of_s.clone()); // ofRat S · ofRat S
    let of_s_cube = c.nnmul(of_s_sq.clone(), of_s.clone()); // (ofRat S)³
    let ofss_ofs = c.nnmul(of_ss.clone(), of_s.clone());
    let cl = nn_congr_mul_left(c, parent, &of_s, of_s_sq.clone(), of_ss.clone(), m1);
    let fwd = c.trans_rat_nn(of_s_cube.clone(), ofss_ofs.clone(), of_s3.clone(), cl, m2);
    // We want `ofRat S³ = (ofRat S)³`, i.e. the SYMM of `fwd`.
    c.symm_nn(of_s_cube, of_s3, fwd)
}

/// `congrArg (fun t => l · t) h` over NNReal for `h : a = b`.
fn nn_congr_mul_left(
    c: &TwoPointLegConsts,
    parent: &EnvDeclBuilder,
    l: &Expr,
    a: Expr,
    b: Expr,
    h: Expr,
) -> Expr {
    // congrArg.{1,1} NNReal NNReal a b (fun t => l·t) h  — but a,b here are the
    // LHS pair `(ofRat S · ofRat S)` and `ofRat (S·S)`; rewriting the LEFT factor
    // of `(·) · of_s`, i.e. `fun t => t · of_s`.
    let f = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(c.nnreal.clone());
        let body = c.nnmul(w, l.clone());
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    Expr::apps(
        c.congr_arg11.clone(),
        [c.nnreal.clone(), c.nnreal.clone(), a, b, f, h],
    )
}
