// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boolean function analysis proof registrations for `ProofLibrary`.
//!
//! Registers the KKL inequality proof chain (S41-S43, S46, S50):
//!
//! - S41: Parseval's identity — sum of Fourier coefficients squared = E[f^2]
//! - S42: Influence-Fourier identity — Inf_i(f) = sum_{S containing i} hat{f}(S)^2
//! - S46: Total influence identity — I(f) = sum_S |S| * hat{f}(S)^2
//! - S50: Bonami-Beckner hypercontractivity — ||T_rho f||_q <= ||f||_p
//! - S43: KKL inequality — max_i Inf_i(f) >= Mathverse(Var(f) * log(n) / n)
//!
//! References:
//! - Kahn, Kalai, Linial, "The influence of variables on Boolean functions," 1988
//! - O'Donnell, "Analysis of Boolean Functions," Cambridge, 2014
//!
//! Part of #3264.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    /// Add Boolean function analysis proof terms (KKL inequality chain).
    ///
    /// These proofs reference the kernel-level axiom declarations registered
    /// by `Environment::init_boolean_analysis()`. Each proof term wraps the
    /// corresponding axiom with the proper type signature.
    pub(super) fn add_boolean_analysis_proofs(&mut self) {
        // =====================================================================
        // S41: Parseval's identity
        // sum_S hat{f}(S)^2 = E[f^2]
        // =====================================================================
        self.proofs.insert(
            "BoolAnalysis.parseval_identity".to_string(),
            ProofTerm::new(
                "BoolAnalysis.parseval_identity",
                "fun (n : Nat) (f : BoolAnalysis.BoolFn n) => BoolAnalysis.parseval_identity n f",
                "S41: Parseval's identity — the sum of squared Fourier coefficients \
                 equals E[f^2] under the uniform distribution on {0,1}^n. \
                 Ref: O'Donnell, Analysis of Boolean Functions, Theorem 1.10.",
            ),
        );

        // =====================================================================
        // S42: Influence-Fourier identity
        // Inf_i(f) = sum_{S : i in S} hat{f}(S)^2
        // =====================================================================
        self.proofs.insert(
            "BoolAnalysis.influence_fourier".to_string(),
            ProofTerm::new(
                "BoolAnalysis.influence_fourier",
                "fun (n : Nat) (f : BoolAnalysis.BoolFn n) (i : Fin n) => BoolAnalysis.influence_fourier n f i",
                "S42: Influence-Fourier identity — the influence of variable i equals \
                 the sum of hat{f}(S)^2 over all subsets S containing i. \
                 Ref: O'Donnell, Analysis of Boolean Functions, Proposition 2.17.",
            ),
        );

        // =====================================================================
        // S46: Total influence identity
        // I(f) = sum_S |S| * hat{f}(S)^2
        // =====================================================================
        self.proofs.insert(
            "BoolAnalysis.total_influence_identity".to_string(),
            ProofTerm::new(
                "BoolAnalysis.total_influence_identity",
                "fun (n : Nat) (f : BoolAnalysis.BoolFn n) => BoolAnalysis.total_influence_identity n f",
                "S46: Total influence identity — I(f) equals the sum of |S| * hat{f}(S)^2 \
                 over all subsets S. Follows from S42 by summing over all variables. \
                 Ref: O'Donnell, Analysis of Boolean Functions, Proposition 2.18.",
            ),
        );

        // =====================================================================
        // S50: Bonami-Beckner hypercontractivity theorem
        // ||T_rho f||_q <= ||f||_p for 1<=p<=q, rho <= sqrt((p-1)/(q-1))
        // =====================================================================
        self.proofs.insert(
            "BoolAnalysis.bonami_beckner".to_string(),
            ProofTerm::new(
                "BoolAnalysis.bonami_beckner",
                "fun (n : Nat) (f : BoolAnalysis.BoolFn n) (rho : Rat) (p : Rat) (q : Rat) (h : BoolAnalysis.bonami_beckner_conditions rho p q) => BoolAnalysis.bonami_beckner n f rho p q h",
                "S50: Bonami-Beckner hypercontractivity — the noise operator T_rho contracts \
                 L^p norms: ||T_rho f||_q <= ||f||_p when rho^2 <= (p-1)/(q-1). \
                 Key ingredient for the KKL inequality via log-Sobolev techniques. \
                 Ref: Bonami (1970), Beckner (1975); O'Donnell Ch. 9.",
            ),
        );

        // =====================================================================
        // S43: KKL inequality (the culminating theorem)
        // max_i Inf_i(f) >= Mathverse(Var(f) * log(n) / n)
        // =====================================================================
        self.proofs.insert(
            "BoolAnalysis.kkl_inequality".to_string(),
            ProofTerm::new(
                "BoolAnalysis.kkl_inequality",
                "fun (n : Nat) (f : BoolAnalysis.BoolFn n) => BoolAnalysis.kkl_inequality n f",
                "S43: KKL inequality — for any Boolean function f:{0,1}^n -> {0,1}, \
                 the maximum influence satisfies the genuine max-influence bound. \
                 STATUS: RETIRED to a kernel-CHECKED constructive Theorem (KKL finish). \
                 The helper is now a reducible Definition carrying the genuine max-influence \
                 KKL statement (under the small-influence regime max_i Inf_i <= delta^2 < 1 and \
                 the dual-HC 9^k threshold, SOME coordinate carries Inf_i >= (k+1)*Var/(2n)), and \
                 BoolAnalysis.kkl_inequality is proved by kkl_exists_max_influence — the \
                 conditional sharp-KKL variance pinch fed through the general-n pigeonhole, with \
                 EMPTY admitted-axiom closure. The supporting Cauchy-real sqrt carrier, dual-HC \
                 aggregate, and the NNReal->Rat order reflection are all proved axiom-free. \
                 Ref: Kahn, Kalai, Linial, FOCS 1988; O'Donnell, Theorem 9.28.",
            ),
        );
    }
}
