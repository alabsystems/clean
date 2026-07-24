// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Int-level numerator equality for `Rat.add_assoc` (#3572 Phase 3).
//!
//! Factored out of the parent `mod.rs` so each step-group helper stays
//! under the 80-line function limit. See the parent module docs for the
//! mathematical sketch — this file carries the proof implementation.

#![allow(non_snake_case)]

use super::super::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;

use super::mod_helpers::{
    eq_symm_of, i_add, i_mul, int_congr, int_trans, motive_add_left, motive_add_right,
    motive_mul_right, n_mul, AddAssocSymbols, Terms,
};

/// Everything computed on the way from `L0` to `L8`. Exposed to keep the
/// parent register function able to name `lhs_num`, `rhs_num`, etc.
pub(super) struct HNumResult {
    pub(super) proof: Expr,
    pub(super) lhs_num: Expr,
    pub(super) rhs_num: Expr,
}

/// Stable per-step terms shared across the four stage helpers.
struct StageTerms {
    nA_pB: Expr,
    nB_pA: Expr,
    nA_pB_pC: Expr,
    nB_pA_pC: Expr,
    pB_pC: Expr,
    pA_pC: Expr,
    pC_pA: Expr,
    pA_pB: Expr,
    pB_pA: Expr,
    nA_pB_pC_assoc: Expr, // nA·(pB·pC)
    nB_pA_pC_assoc: Expr, // nB·(pA·pC)
    nB_pC_pA_assoc: Expr, // nB·(pC·pA)
    nB_pC: Expr,
    nB_pC_pA: Expr,       // (nB·pC)·pA
    nC_pA_pB_assoc: Expr, // nC·(pA·pB)
    nC_pB_pA_assoc: Expr, // nC·(pB·pA)
    nC_pB: Expr,
    nC_pB_pA: Expr, // (nC·pB)·pA
    ofn_dAdB: Expr,
    ofn_dBdC: Expr,
    nC_ofn_dAdB: Expr,
    nA_ofn_dBdC: Expr,
}

fn build_stage_terms(sym: &AddAssocSymbols, t: &Terms) -> StageTerms {
    let nA_pB = i_mul(sym, t.n_a.clone(), t.p_b.clone());
    let nB_pA = i_mul(sym, t.n_b.clone(), t.p_a.clone());
    let nA_pB_pC = i_mul(sym, nA_pB.clone(), t.p_c.clone());
    let nB_pA_pC = i_mul(sym, nB_pA.clone(), t.p_c.clone());
    let pB_pC = i_mul(sym, t.p_b.clone(), t.p_c.clone());
    let pA_pC = i_mul(sym, t.p_a.clone(), t.p_c.clone());
    let pC_pA = i_mul(sym, t.p_c.clone(), t.p_a.clone());
    let pA_pB = i_mul(sym, t.p_a.clone(), t.p_b.clone());
    let pB_pA = i_mul(sym, t.p_b.clone(), t.p_a.clone());
    let nA_pB_pC_assoc = i_mul(sym, t.n_a.clone(), pB_pC.clone());
    let nB_pA_pC_assoc = i_mul(sym, t.n_b.clone(), pA_pC.clone());
    let nB_pC_pA_assoc = i_mul(sym, t.n_b.clone(), pC_pA.clone());
    let nB_pC = i_mul(sym, t.n_b.clone(), t.p_c.clone());
    let nB_pC_pA = i_mul(sym, nB_pC.clone(), t.p_a.clone());
    let nC_pA_pB_assoc = i_mul(sym, t.n_c.clone(), pA_pB.clone());
    let nC_pB_pA_assoc = i_mul(sym, t.n_c.clone(), pB_pA.clone());
    let nC_pB = i_mul(sym, t.n_c.clone(), t.p_b.clone());
    let nC_pB_pA = i_mul(sym, nC_pB.clone(), t.p_a.clone());
    let ofn_dAdB = Expr::app(
        sym.tb.int_of_nat.clone(),
        n_mul(sym, t.d_a.clone(), t.d_b.clone()),
    );
    let ofn_dBdC = Expr::app(
        sym.tb.int_of_nat.clone(),
        n_mul(sym, t.d_b.clone(), t.d_c.clone()),
    );
    let nC_ofn_dAdB = i_mul(sym, t.n_c.clone(), ofn_dAdB.clone());
    let nA_ofn_dBdC = i_mul(sym, t.n_a.clone(), ofn_dBdC.clone());
    StageTerms {
        nA_pB,
        nB_pA,
        nA_pB_pC,
        nB_pA_pC,
        pB_pC,
        pA_pC,
        pC_pA,
        pA_pB,
        pB_pA,
        nA_pB_pC_assoc,
        nB_pA_pC_assoc,
        nB_pC_pA_assoc,
        nB_pC,
        nB_pC_pA,
        nC_pA_pB_assoc,
        nC_pB_pA_assoc,
        nC_pB,
        nC_pB_pA,
        ofn_dAdB,
        ofn_dBdC,
        nC_ofn_dAdB,
        nA_ofn_dBdC,
    }
}

/// Stage 1: build `L0` and the equalities for steps 1 and 2. Returns the
/// combined proof `L0 = L2` and the intermediate terms `l0`, `l2`, and
/// `new_left_1`.
fn stage_1_distrib_and_ofnat(
    sym: &AddAssocSymbols,
    b: &EnvDeclBuilder,
    t: &Terms,
    st: &StageTerms,
) -> (Expr, Expr, Expr, Expr) {
    // L0 = (nA·pB + nB·pA)·pC + nC·ofn(dA·dB)
    let nA_pB_plus_nB_pA = i_add(sym, st.nA_pB.clone(), st.nB_pA.clone());
    let l0_left = i_mul(sym, nA_pB_plus_nB_pA, t.p_c.clone());
    let l0 = i_add(sym, l0_left.clone(), st.nC_ofn_dAdB.clone());

    // Step 1: Int.right_distrib (nA·pB) (nB·pA) pC
    let rdist_1 = Expr::apps(
        sym.int_right_distrib.clone(),
        [st.nA_pB.clone(), st.nB_pA.clone(), t.p_c.clone()],
    );
    let new_left_1 = i_add(sym, st.nA_pB_pC.clone(), st.nB_pA_pC.clone());
    let mot1 = motive_add_left(sym, b, &st.nC_ofn_dAdB);
    let step1 = int_congr(sym, l0_left, new_left_1.clone(), mot1, rdist_1);
    let l1 = i_add(sym, new_left_1.clone(), st.nC_ofn_dAdB.clone());

    // Step 2: Int.ofNat_mul dA dB under nC·_ + new_left_1.
    let ofnm_dAdB = Expr::apps(sym.int_ofnat_mul.clone(), [t.d_a.clone(), t.d_b.clone()]);
    let mot2_mul = motive_mul_right(sym, b, &t.n_c);
    let step2_mul = int_congr(
        sym,
        st.ofn_dAdB.clone(),
        st.pA_pB.clone(),
        mot2_mul,
        ofnm_dAdB,
    );
    let mot2_outer = motive_add_right(sym, b, &new_left_1);
    let step2 = int_congr(
        sym,
        st.nC_ofn_dAdB.clone(),
        st.nC_pA_pB_assoc.clone(),
        mot2_outer,
        step2_mul,
    );
    let l2 = i_add(sym, new_left_1.clone(), st.nC_pA_pB_assoc.clone());
    let proof = int_trans(sym, l0.clone(), l1, l2.clone(), step1, step2);
    (proof, l0, l2, new_left_1)
}

/// Stage 2: steps 3 and 4a (left-side associativity on nA·pB·pC and
/// nB·pA·pC). Returns `(acc_proof, l4a, new_left_4a)`.
fn stage_2_mul_assoc_left(
    sym: &AddAssocSymbols,
    b: &EnvDeclBuilder,
    t: &Terms,
    st: &StageTerms,
    l0: &Expr,
    l2: &Expr,
    new_left_1: &Expr,
    t01: Expr,
) -> (Expr, Expr, Expr) {
    // Step 3: Int.mul_assoc nA pB pC
    let massoc_nA = Expr::apps(
        sym.int_mul_assoc.clone(),
        [t.n_a.clone(), t.p_b.clone(), t.p_c.clone()],
    );
    let mot3_inner = motive_add_left(sym, b, &st.nB_pA_pC);
    let step3_inner = int_congr(
        sym,
        st.nA_pB_pC.clone(),
        st.nA_pB_pC_assoc.clone(),
        mot3_inner,
        massoc_nA,
    );
    let mot3_outer = motive_add_left(sym, b, &st.nC_pA_pB_assoc);
    let new_left_3 = i_add(sym, st.nA_pB_pC_assoc.clone(), st.nB_pA_pC.clone());
    let step3 = int_congr(
        sym,
        new_left_1.clone(),
        new_left_3.clone(),
        mot3_outer,
        step3_inner,
    );
    let l3 = i_add(sym, new_left_3.clone(), st.nC_pA_pB_assoc.clone());
    let t02 = int_trans(sym, l0.clone(), l2.clone(), l3.clone(), t01, step3);

    // Step 4a: Int.mul_assoc nB pA pC
    let massoc_nB = Expr::apps(
        sym.int_mul_assoc.clone(),
        [t.n_b.clone(), t.p_a.clone(), t.p_c.clone()],
    );
    let mot4a_inner = motive_add_right(sym, b, &st.nA_pB_pC_assoc);
    let step4a_inner = int_congr(
        sym,
        st.nB_pA_pC.clone(),
        st.nB_pA_pC_assoc.clone(),
        mot4a_inner,
        massoc_nB,
    );
    let mot4a_outer = motive_add_left(sym, b, &st.nC_pA_pB_assoc);
    let new_left_4a = i_add(sym, st.nA_pB_pC_assoc.clone(), st.nB_pA_pC_assoc.clone());
    let step4a = int_congr(
        sym,
        new_left_3,
        new_left_4a.clone(),
        mot4a_outer,
        step4a_inner,
    );
    let l4a = i_add(sym, new_left_4a.clone(), st.nC_pA_pB_assoc.clone());
    let t03 = int_trans(sym, l0.clone(), l3, l4a.clone(), t02, step4a);
    (t03, l4a, new_left_4a)
}

/// Stage 3: steps 4b, 4c, 5a, 5b (reorder pA·pC → pC·pA under nB, then
/// reassociate; mirror for nC side). Returns `(acc_proof, l5b, new_left_4c)`.
fn stage_3_reassociate(
    sym: &AddAssocSymbols,
    b: &EnvDeclBuilder,
    t: &Terms,
    st: &StageTerms,
    l0: &Expr,
    l4a: &Expr,
    new_left_4a: &Expr,
    t03: Expr,
) -> (Expr, Expr, Expr) {
    // Step 4b: Int.mul_comm pA pC under nB·_ + _ + nC·(pA·pB)
    let mcomm_pA_pC = Expr::apps(sym.int_mul_comm.clone(), [t.p_a.clone(), t.p_c.clone()]);
    let mot4b_inner = motive_mul_right(sym, b, &t.n_b);
    let step4b_inner = int_congr(
        sym,
        st.pA_pC.clone(),
        st.pC_pA.clone(),
        mot4b_inner,
        mcomm_pA_pC,
    );
    let mot4b_mid = motive_add_right(sym, b, &st.nA_pB_pC_assoc);
    let step4b_mid = int_congr(
        sym,
        st.nB_pA_pC_assoc.clone(),
        st.nB_pC_pA_assoc.clone(),
        mot4b_mid,
        step4b_inner,
    );
    let mot4b_outer = motive_add_left(sym, b, &st.nC_pA_pB_assoc);
    let new_left_4b = i_add(sym, st.nA_pB_pC_assoc.clone(), st.nB_pC_pA_assoc.clone());
    let step4b = int_congr(
        sym,
        new_left_4a.clone(),
        new_left_4b.clone(),
        mot4b_outer,
        step4b_mid,
    );
    let l4b = i_add(sym, new_left_4b.clone(), st.nC_pA_pB_assoc.clone());
    let t04 = int_trans(sym, l0.clone(), l4a.clone(), l4b.clone(), t03, step4b);

    // Step 4c: Eq.symm (Int.mul_assoc nB pC pA): nB·(pC·pA) = (nB·pC)·pA
    let massoc_nB_pC = Expr::apps(
        sym.int_mul_assoc.clone(),
        [t.n_b.clone(), t.p_c.clone(), t.p_a.clone()],
    );
    let symm_massoc_nB_pC = eq_symm_of(
        sym,
        &sym.tb.int_type,
        st.nB_pC_pA.clone(),
        st.nB_pC_pA_assoc.clone(),
        massoc_nB_pC,
    );
    let mot4c_mid = motive_add_right(sym, b, &st.nA_pB_pC_assoc);
    let step4c_mid = int_congr(
        sym,
        st.nB_pC_pA_assoc.clone(),
        st.nB_pC_pA.clone(),
        mot4c_mid,
        symm_massoc_nB_pC,
    );
    let mot4c_outer = motive_add_left(sym, b, &st.nC_pA_pB_assoc);
    let new_left_4c = i_add(sym, st.nA_pB_pC_assoc.clone(), st.nB_pC_pA.clone());
    let step4c = int_congr(
        sym,
        new_left_4b,
        new_left_4c.clone(),
        mot4c_outer,
        step4c_mid,
    );
    let l4c = i_add(sym, new_left_4c.clone(), st.nC_pA_pB_assoc.clone());
    let t05 = int_trans(sym, l0.clone(), l4b, l4c.clone(), t04, step4c);

    // Step 5a: Int.mul_comm pA pB under nC·_ + new_left_4c.
    let mcomm_pA_pB = Expr::apps(sym.int_mul_comm.clone(), [t.p_a.clone(), t.p_b.clone()]);
    let mot5a_inner = motive_mul_right(sym, b, &t.n_c);
    let step5a_inner = int_congr(
        sym,
        st.pA_pB.clone(),
        st.pB_pA.clone(),
        mot5a_inner,
        mcomm_pA_pB,
    );
    let mot5a_outer = motive_add_right(sym, b, &new_left_4c);
    let step5a = int_congr(
        sym,
        st.nC_pA_pB_assoc.clone(),
        st.nC_pB_pA_assoc.clone(),
        mot5a_outer,
        step5a_inner,
    );
    let l5a = i_add(sym, new_left_4c.clone(), st.nC_pB_pA_assoc.clone());
    let t06 = int_trans(sym, l0.clone(), l4c, l5a.clone(), t05, step5a);

    // Step 5b: Eq.symm (Int.mul_assoc nC pB pA): nC·(pB·pA) = (nC·pB)·pA
    let massoc_nC_pB = Expr::apps(
        sym.int_mul_assoc.clone(),
        [t.n_c.clone(), t.p_b.clone(), t.p_a.clone()],
    );
    let symm_massoc_nC_pB = eq_symm_of(
        sym,
        &sym.tb.int_type,
        st.nC_pB_pA.clone(),
        st.nC_pB_pA_assoc.clone(),
        massoc_nC_pB,
    );
    let mot5b_outer = motive_add_right(sym, b, &new_left_4c);
    let step5b = int_congr(
        sym,
        st.nC_pB_pA_assoc.clone(),
        st.nC_pB_pA.clone(),
        mot5b_outer,
        symm_massoc_nC_pB,
    );
    let l5b = i_add(sym, new_left_4c.clone(), st.nC_pB_pA.clone());
    let t07 = int_trans(sym, l0.clone(), l5a, l5b.clone(), t06, step5b);
    (t07, l5b, new_left_4c)
}

/// Stage 4: steps 6, 7, 8 (Int.add_assoc regroup; collapse right sum via
/// Eq.symm of right_distrib; rewrite nA·(pB·pC) to nA·ofn(dB·dC)).
fn stage_4_finalize(
    sym: &AddAssocSymbols,
    b: &EnvDeclBuilder,
    t: &Terms,
    st: &StageTerms,
    l0: &Expr,
    l5b: &Expr,
    t07: Expr,
) -> Expr {
    // Step 6: Int.add_assoc (nA·(pB·pC)) (nB·pC·pA) (nC·pB·pA)
    let aadd_assoc = Expr::apps(
        sym.int_add_assoc.clone(),
        [
            st.nA_pB_pC_assoc.clone(),
            st.nB_pC_pA.clone(),
            st.nC_pB_pA.clone(),
        ],
    );
    let right_sum = i_add(sym, st.nB_pC_pA.clone(), st.nC_pB_pA.clone());
    let l6 = i_add(sym, st.nA_pB_pC_assoc.clone(), right_sum.clone());
    let t08 = int_trans(sym, l0.clone(), l5b.clone(), l6.clone(), t07, aadd_assoc);

    // Step 7: Eq.symm (Int.right_distrib (nB·pC) (nC·pB) pA)
    let rdist_2 = Expr::apps(
        sym.int_right_distrib.clone(),
        [st.nB_pC.clone(), st.nC_pB.clone(), t.p_a.clone()],
    );
    let nB_pC_plus_nC_pB = i_add(sym, st.nB_pC.clone(), st.nC_pB.clone());
    let nB_pC_plus_nC_pB_times_pA = i_mul(sym, nB_pC_plus_nC_pB, t.p_a.clone());
    let symm_rdist_2 = eq_symm_of(
        sym,
        &sym.tb.int_type,
        nB_pC_plus_nC_pB_times_pA.clone(),
        right_sum.clone(),
        rdist_2,
    );
    let mot7 = motive_add_right(sym, b, &st.nA_pB_pC_assoc);
    let step7 = int_congr(
        sym,
        right_sum,
        nB_pC_plus_nC_pB_times_pA.clone(),
        mot7,
        symm_rdist_2,
    );
    let l7 = i_add(
        sym,
        st.nA_pB_pC_assoc.clone(),
        nB_pC_plus_nC_pB_times_pA.clone(),
    );
    let t09 = int_trans(sym, l0.clone(), l6, l7.clone(), t08, step7);

    // Step 8: Eq.symm (Int.ofNat_mul dB dC) under nA·_ + right-side-fixed.
    let ofnm_dBdC = Expr::apps(sym.int_ofnat_mul.clone(), [t.d_b.clone(), t.d_c.clone()]);
    let symm_ofnm_dBdC = eq_symm_of(
        sym,
        &sym.tb.int_type,
        st.pB_pC.clone(),
        st.ofn_dBdC.clone(),
        ofnm_dBdC,
    );
    let mot8_inner = motive_mul_right(sym, b, &t.n_a);
    let step8_inner = int_congr(
        sym,
        st.pB_pC.clone(),
        st.ofn_dBdC.clone(),
        mot8_inner,
        symm_ofnm_dBdC,
    );
    let mot8_outer = motive_add_left(sym, b, &nB_pC_plus_nC_pB_times_pA);
    let step8 = int_congr(
        sym,
        st.nA_pB_pC_assoc.clone(),
        st.nA_ofn_dBdC.clone(),
        mot8_outer,
        step8_inner,
    );
    let l8 = i_add(sym, st.nA_ofn_dBdC.clone(), nB_pC_plus_nC_pB_times_pA);
    int_trans(sym, l0.clone(), l7, l8, t09, step8)
}

/// Build the Int numerator equality proof.
pub(super) fn build_h_num(sym: &AddAssocSymbols, b: &EnvDeclBuilder, t: &Terms) -> HNumResult {
    let st = build_stage_terms(sym, t);

    let (t01, l0, l2, new_left_1) = stage_1_distrib_and_ofnat(sym, b, t, &st);
    let (t03, l4a, new_left_4a) =
        stage_2_mul_assoc_left(sym, b, t, &st, &l0, &l2, &new_left_1, t01);
    let (t07, l5b, _new_left_4c) =
        stage_3_reassociate(sym, b, t, &st, &l0, &l4a, &new_left_4a, t03);
    let proof = stage_4_finalize(sym, b, t, &st, &l0, &l5b, t07);

    // Endpoint expressions for the register function.
    let nA_pB_plus_nB_pA = i_add(sym, st.nA_pB.clone(), st.nB_pA.clone());
    let lhs_num_left = i_mul(sym, nA_pB_plus_nB_pA, t.p_c.clone());
    let lhs_num = i_add(sym, lhs_num_left, st.nC_ofn_dAdB.clone());

    let nB_pC_plus_nC_pB = i_add(sym, st.nB_pC.clone(), st.nC_pB.clone());
    let rhs_num_right = i_mul(sym, nB_pC_plus_nC_pB, t.p_a.clone());
    let rhs_num = i_add(sym, st.nA_ofn_dBdC.clone(), rhs_num_right);

    HNumResult {
        proof,
        lhs_num,
        rhs_num,
    }
}
