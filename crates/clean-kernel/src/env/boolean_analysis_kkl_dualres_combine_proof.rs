// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-term builder for `BoolAnalysis.holder_quad_combine` — split out of
//! `boolean_analysis_kkl_dualres_combine.rs` to keep both files within the
//! 500-line module budget. See the parent module for the statement and outline.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_kkl_dualres_combine::CombineConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;

pub(super) fn build_combine_proof(
    c: &CombineConsts,
    b: &EnvDeclBuilder,
    l2: &Expr,
    w: &Expr,
    cnt: &Expr,
    f4: &Expr,
    h_l2: Expr,
    h_w: Expr,
    h_cnt: Expr,
    h1: Expr,
    h2: Expr,
    kk: &dyn Fn(&Expr, &Expr) -> Expr,
    target_rhs: &dyn Fn(&Expr, &Expr) -> Expr,
) -> Expr {
    let four = c.lit(4);
    let sixteen = c.lit(16);
    let k = kk(w, cnt); // K = (4·w)·cnt
    let l2l2 = c.mul(l2.clone(), l2.clone());
    let ww = c.mul(w.clone(), w.clone());
    let cntcnt = c.mul(cnt.clone(), cnt.clone());
    let f4cnt = c.mul(f4.clone(), cnt.clone());

    // 0 ≤ K = mul_nonneg (4·w) cnt (mul_nonneg 4 w h4 h_w) h_cnt.
    let h_4w_nn = c.mul_nonneg(four.clone(), w.clone(), c.nonneg_lit(4), h_w);
    let h_k_nn = c.mul_nonneg(c.mul(four.clone(), w.clone()), cnt.clone(), h_4w_nn, h_cnt);

    // sqA : l2·l2 ≤ K·K.
    let t1 = c.mul_le_left(l2.clone(), l2.clone(), k.clone(), h1.clone(), h_l2);
    let t2 = c.mul_le_right(k.clone(), l2.clone(), k.clone(), h1, h_k_nn);
    let l2_k = c.mul(l2.clone(), k.clone());
    let k_k = c.mul(k.clone(), k.clone());
    let sq_a = c.le_trans(l2l2.clone(), l2_k, k_k.clone(), t1, t2);

    // eqK : K·K = (16·(w·w))·(cnt·cnt).
    //   mmmc (4w) cnt (4w) cnt : K·K = ((4w)·(4w))·(cnt·cnt).
    let four_w = c.mul(four.clone(), w.clone());
    let mmmc_k = c.mmmc(four_w.clone(), cnt.clone(), four_w.clone(), cnt.clone());
    let fw_fw = c.mul(four_w.clone(), four_w.clone()); // (4w)·(4w)
    let fw_fw_cc = c.mul(fw_fw.clone(), cntcnt.clone()); // ((4w)(4w))·(cnt²)
                                                         //   h_fw : (4w)·(4w) = (4·4)·(w·w)   [mmmc 4 w 4 w]
    let mmmc_fw = c.mmmc(four.clone(), w.clone(), four.clone(), w.clone());
    let ff = c.mul(four.clone(), four.clone()); // 4·4 (defeq 16)
    let ff_ww = c.mul(ff.clone(), ww.clone()); // (4·4)·(w·w)
                                               //   h44 : 4·4 = 16   [Eq.refl (4·4), typed at (4·4)=16 by ground reduction]
    let h44 = Expr::apps(c.eq_refl_u1(), [c.rat(), ff.clone()]);
    let cong44 = c.congr_arg(ff.clone(), sixteen.clone(), c.lam_mul_right(b, &ww), h44);
    let sixteen_ww = c.mul(sixteen.clone(), ww.clone()); // 16·(w·w)
                                                         //   h_fw : (4w)·(4w) = 16·(w·w)
    let h_fw = c.trans(
        fw_fw.clone(),
        ff_ww.clone(),
        sixteen_ww.clone(),
        mmmc_fw,
        cong44,
    );
    //   congr into outer: ((4w)(4w))·(cnt²) = (16·(w·w))·(cnt²)
    let cong_outer = c.congr_arg(
        fw_fw.clone(),
        sixteen_ww.clone(),
        c.lam_mul_right(b, &cntcnt),
        h_fw,
    );
    let sixteen_ww_cc = c.mul(sixteen_ww.clone(), cntcnt.clone()); // (16·(w·w))·(cnt²)
    let eq_k = c.trans(
        k_k.clone(),
        fw_fw_cc.clone(),
        sixteen_ww_cc.clone(),
        mmmc_k,
        cong_outer,
    );

    // sqB : l2·l2 ≤ (16·(w·w))·(cnt·cnt)   [Eq.subst eqK into sqA's RHS]
    let motive_b = c.lam_le_rhs(b, &l2l2);
    let sq_b = c.subst(motive_b, k_k.clone(), sixteen_ww_cc.clone(), eq_k, sq_a);

    // 16·(w·w) ≤ 16·(f4·cnt)   [mul_le_left 16 (w·w) (f4·cnt) h2 (0≤16)]
    let h_16ww_le = c.mul_le_left(
        sixteen.clone(),
        ww.clone(),
        f4cnt.clone(),
        h2,
        c.nonneg_lit(16),
    );
    // step_c : (16·(w·w))·(cnt²) ≤ (16·(f4·cnt))·(cnt²)   [right-mono, 0≤cnt²]
    let h_cc_nn = c.sq_nonneg(cnt.clone());
    let sixteen_f4cnt = c.mul(sixteen.clone(), f4cnt.clone()); // 16·(f4·cnt)
    let step_c = c.mul_le_right(
        cntcnt.clone(),
        sixteen_ww.clone(),
        sixteen_f4cnt.clone(),
        h_16ww_le,
        h_cc_nn,
    );
    let sixteen_f4cnt_cc = c.mul(sixteen_f4cnt.clone(), cntcnt.clone());
    // sqC : l2·l2 ≤ (16·(f4·cnt))·(cnt²)
    let sq_c = c.le_trans(
        l2l2.clone(),
        sixteen_ww_cc.clone(),
        sixteen_f4cnt_cc.clone(),
        sq_b,
        step_c,
    );

    // eqF : (16·(f4·cnt))·(cnt²) = f4·((16·cnt)·(cnt²)).
    //   eq1 : 16·(f4·cnt) = f4·(16·cnt)
    //     = trans( mul_comm 16 (f4·cnt) : 16·(f4·cnt) = (f4·cnt)·16
    //            , trans( mul_assoc f4 cnt 16 : (f4·cnt)·16 = f4·(cnt·16)
    //                   , congrArg (f4·) (mul_comm cnt 16) : f4·(cnt·16) = f4·(16·cnt) ))
    let f4cnt_16 = c.mul(f4cnt.clone(), sixteen.clone());
    let cnt_16 = c.mul(cnt.clone(), sixteen.clone());
    let f4_cnt16 = c.mul(f4.clone(), cnt_16.clone());
    let sixteen_cnt = c.mul(sixteen.clone(), cnt.clone());
    let f4_16cnt = c.mul(f4.clone(), sixteen_cnt.clone());
    let mc_a = c.mul_comm(sixteen.clone(), f4cnt.clone()); // 16·(f4cnt) = (f4cnt)·16
    let ma_b = c.mul_assoc(f4.clone(), cnt.clone(), sixteen.clone()); // (f4·cnt)·16 = f4·(cnt·16)
    let cong_c = c.congr_arg(
        cnt_16.clone(),
        sixteen_cnt.clone(),
        c.lam_mul_left(b, f4),
        c.mul_comm(cnt.clone(), sixteen.clone()),
    ); // f4·(cnt·16) = f4·(16·cnt)
    let eq1 = c.trans(
        sixteen_f4cnt.clone(),
        f4cnt_16.clone(),
        f4_16cnt.clone(),
        mc_a,
        c.trans(
            f4cnt_16.clone(),
            f4_cnt16.clone(),
            f4_16cnt.clone(),
            ma_b,
            cong_c,
        ),
    );
    //   step2 : (16·(f4·cnt))·(cnt²) = (f4·(16·cnt))·(cnt²)   [congrArg (·(cnt²)) eq1]
    let step2 = c.congr_arg(
        sixteen_f4cnt.clone(),
        f4_16cnt.clone(),
        c.lam_mul_right(b, &cntcnt),
        eq1,
    );
    let f4_16cnt_cc = c.mul(f4_16cnt.clone(), cntcnt.clone());
    //   step3 : (f4·(16·cnt))·(cnt²) = f4·((16·cnt)·(cnt²))   [mul_assoc f4 (16·cnt) (cnt²)]
    let step3 = c.mul_assoc(f4.clone(), sixteen_cnt.clone(), cntcnt.clone());
    let target = target_rhs(f4, cnt); // f4·((16·cnt)·(cnt²))
    let eq_f = c.trans(
        sixteen_f4cnt_cc.clone(),
        f4_16cnt_cc.clone(),
        target.clone(),
        step2,
        step3,
    );

    // final : l2·l2 ≤ f4·((16·cnt)·(cnt²))   [Eq.subst eqF into sqC's RHS]
    let motive_f = c.lam_le_rhs(b, &l2l2);
    let _ = c.symm(target.clone(), sixteen_f4cnt_cc.clone(), eq_f.clone()); // (doc)
    c.subst(motive_f, sixteen_f4cnt_cc, target, eq_f, sq_c)
}
