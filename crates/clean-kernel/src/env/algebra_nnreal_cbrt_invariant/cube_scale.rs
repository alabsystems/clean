// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The cube scaling identity `(ofNat 2k)³ = ofNat 8 · (ofNat k)³`.
//!
//! This is the genuinely-new cube arithmetic (vs the sqrt layer's
//! `(ofNat 2k)² = ofNat 4 · (ofNat k)²`). Built purely from `Rat.ofNat_mul`,
//! `Rat.mul_mul_mul_comm` and `Eq`-toolkit transports — no new axiom.
//!
//! Let `A := of2·ofk` (with `of2 = ofNat 2`, `ofk = ofNat k`). Then
//! `ofNat 2k = A` (`ofNat_mul 2 k`), and the cube `((of_2k·of_2k)·of_2k)`:
//!
//! ```text
//!   ((of_2k·of_2k)·of_2k)
//!     = ((A·A)·A)                                  rewrite all three of_2k → A
//!     = (P·A)            where P := (of2·of2)·(ofk·ofk)    [mmmc of2 ofk of2 ofk on A·A]
//!     = ((of2·of2)·of2)·((ofk·ofk)·ofk)           [mmmc (of2·of2)(ofk·ofk) of2 ofk on P·A]
//!     = ofNat 8 · ((ofk·ofk)·ofk)                 [(of2·of2)·of2 = ofNat 8: ofNat_mul ×2]
//!     = ofNat 8 · (ofNat k)³.
//! ```

use super::CbrtInvConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::Expr;

impl CbrtInvConsts {
    /// `(ofNat 2k)³ = ofNat 8 · (ofNat k)³`, as a `Rat` `Eq` proof term.
    /// `kk` is the `Nat` value `k`. `pub(crate)` so the cbrt upper-bound module
    /// can reuse it (symm gives the RHS rewrite there).
    pub(crate) fn cube_scale_eq(&self, parent: &EnvDeclBuilder, kk: &Expr) -> Expr {
        let of2 = self.s_rofnat(self.s_nat_lit(2));
        let of4 = self.s_rofnat(self.s_nat_lit(4));
        let of8 = self.s_rofnat(self.s_nat_lit(8));
        let ofk = self.s_rofnat(kk.clone());
        let two_k = self.s_nmul(self.s_nat_lit(2), kk.clone());
        let of_2k = self.s_rofnat(two_k);

        // A := of2·ofk.
        let a = self.s_rmul(of2.clone(), ofk.clone());
        // e_2k : of_2k = A   (ofNat_mul 2 k).
        let e_2k = self.s_ofnat_mul(self.s_nat_lit(2), kk.clone());

        // cube_2k := (of_2k·of_2k)·of_2k.   Rewrite all three of_2k → A.
        let sq_2k = self.s_rmul(of_2k.clone(), of_2k.clone());
        let cube_2k = self.s_rmul(sq_2k.clone(), of_2k.clone());

        // s1 : (of_2k·of_2k) = (A·of_2k)   congr (· · of_2k) e_2k.
        let f1 = self.s_f_right(parent, of_2k.clone());
        let s1 = self.s_congr(of_2k.clone(), a.clone(), f1, e_2k.clone());
        let a_2k = self.s_rmul(a.clone(), of_2k.clone());
        // s2 : (A·of_2k) = (A·A)   congr (A · ·) e_2k.
        let f2 = self.s_f_left(parent, a.clone());
        let s2 = self.s_congr(of_2k.clone(), a.clone(), f2, e_2k.clone());
        let aa = self.s_rmul(a.clone(), a.clone());
        // sq_2k = A·A   (s1 ; s2).
        let sq_eq_aa = self.s_trans(sq_2k.clone(), a_2k.clone(), aa.clone(), s1, s2);

        // s3 : (of_2k·of_2k)·of_2k = (A·A)·of_2k   congr (· · of_2k) sq_eq_aa.
        let f3 = self.s_f_right(parent, of_2k.clone());
        let s3 = self.s_congr(sq_2k.clone(), aa.clone(), f3, sq_eq_aa);
        let aa_2k = self.s_rmul(aa.clone(), of_2k.clone());
        // s4 : (A·A)·of_2k = (A·A)·A   congr ((A·A) · ·) e_2k.
        let f4 = self.s_f_left(parent, aa.clone());
        let s4 = self.s_congr(of_2k.clone(), a.clone(), f4, e_2k.clone());
        let cube_a = self.s_rmul(aa.clone(), a.clone()); // (A·A)·A
                                                         // cube_2k = (A·A)·A   (s3 ; s4).
        let cube_eq_cube_a = self.s_trans(cube_2k.clone(), aa_2k.clone(), cube_a.clone(), s3, s4);

        // mmmc on A·A : (of2·ofk)·(of2·ofk) = (of2·of2)·(ofk·ofk) =: P.
        let o2o2 = self.s_rmul(of2.clone(), of2.clone());
        let okok = self.s_rmul(ofk.clone(), ofk.clone());
        let p = self.s_rmul(o2o2.clone(), okok.clone());
        let mmmc_aa = self.s_mmmc(of2.clone(), ofk.clone(), of2.clone(), ofk.clone());
        // s5 : (A·A)·A = P·A   congr (· · A) mmmc_aa.
        let f5 = self.s_f_right(parent, a.clone());
        let s5 = self.s_congr(aa.clone(), p.clone(), f5, mmmc_aa);
        let p_a = self.s_rmul(p.clone(), a.clone());
        // cube_2k = P·A.
        let cube_eq_pa = self.s_trans(
            cube_2k.clone(),
            cube_a.clone(),
            p_a.clone(),
            cube_eq_cube_a,
            s5,
        );

        // mmmc on P·A = ((of2·of2)·(ofk·ofk))·(of2·ofk)
        //   : = ((of2·of2)·of2)·((ofk·ofk)·ofk) =: Q.
        let mmmc_pa = self.s_mmmc(o2o2.clone(), okok.clone(), of2.clone(), ofk.clone());
        let lhs8 = self.s_rmul(o2o2.clone(), of2.clone()); // (of2·of2)·of2
        let rhs_cube_k = self.s_rmul(okok.clone(), ofk.clone()); // (ofk·ofk)·ofk = (ofNat k)³
        let q = self.s_rmul(lhs8.clone(), rhs_cube_k.clone());
        // cube_2k = Q.
        let cube_eq_q = self.s_trans(cube_2k.clone(), p_a.clone(), q.clone(), cube_eq_pa, mmmc_pa);

        // (of2·of2)·of2 = ofNat 8:
        //   e_22 : ofNat 4 = of2·of2  (ofnat_mul 2 2). symm → of2·of2 = ofNat 4.
        let e_22 = self.s_ofnat_mul(self.s_nat_lit(2), self.s_nat_lit(2));
        let e_22_symm = self.s_symm(of4.clone(), o2o2.clone(), e_22); // o2o2 = ofNat 4
                                                                      // congr (· · of2) e_22_symm : (o2o2·of2) = (ofNat4·of2).
        let f6 = self.s_f_right(parent, of2.clone());
        let s6 = self.s_congr(o2o2.clone(), of4.clone(), f6, e_22_symm);
        let of4_of2 = self.s_rmul(of4.clone(), of2.clone());
        //   e_42 : ofNat 8 = ofNat4·of2  (ofnat_mul 4 2). symm → ofNat4·of2 = ofNat 8.
        let e_42 = self.s_ofnat_mul(self.s_nat_lit(4), self.s_nat_lit(2));
        let e_42_symm = self.s_symm(of8.clone(), of4_of2.clone(), e_42); // of4·of2 = ofNat 8
                                                                         // lhs8 = ofNat 8   (s6 ; e_42_symm).
        let lhs8_eq_8 = self.s_trans(lhs8.clone(), of4_of2.clone(), of8.clone(), s6, e_42_symm);

        // Q = ofNat 8 · ((ofk·ofk)·ofk)   congr (· · rhs_cube_k) lhs8_eq_8.
        let f7 = self.s_f_right(parent, rhs_cube_k.clone());
        let q_eq_target = self.s_congr(lhs8.clone(), of8.clone(), f7, lhs8_eq_8);
        let target = self.s_rmul(of8.clone(), rhs_cube_k.clone()); // ofNat 8 · (ofNat k)³

        // cube_2k = target  (cube_eq_q ; q_eq_target).
        self.s_trans(cube_2k, q, target, cube_eq_q, q_eq_target)
    }
}
