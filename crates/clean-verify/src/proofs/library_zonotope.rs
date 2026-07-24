// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Zonotope proof terms for the kernel ProofLibrary.
//!
//! Companion to `nn_verify/zonotope/spec_registration.rs`. Each theorem has a
//! real kernel proof term that directly applies the corresponding
//! `ZonoContainSound` constructor. These proof terms flow through
//! `promote_with_proof_term`, which type-checks them against the spec and
//! promotes the definitions from `DerivedPending` to `DerivedProved`.
//!
//! # Theorems
//!
//! - T01: Interval hull soundness — `ZonoContainSound.t01_hull n`
//! - T02: Linear transform exactness — `ZonoContainSound.t02_affine n`
//! - T03: ReLU overapproximation soundness — `ZonoContainSound.t03_relu_overapprox n`
//! - T04: Lambda-relaxation tightness — `ZonoContainSound.t04_relu_tight n`
//! - T05: ReLU always-active exactness — `ZonoContainSound.t05_relu_active n`
//! - T06: ReLU always-inactive exactness — `ZonoContainSound.t06_relu_inactive n`
//! - T07: Affine+ReLU composition soundness — `ZonoContainSound.t07_affine_relu n`
//! - T08: Minkowski sum soundness — `ZonoContainSound.t08_minkowski n`
//! - T08A: Minkowski reduce soundness — `ZonoContainSound.t08a_minkowski_reduce n`
//! - T08B: Minkowski residual soundness — `ZonoContainSound.t08b_minkowski_residual n`
//!
//! Part of #3363.

use super::{ProofLibrary, ProofTerm};

impl ProofLibrary {
    pub(super) fn add_zonotope_proofs(&mut self) {
        // ── T01: Interval hull soundness ─────────────────────────────────
        self.proofs.insert(
            "zono_t01_interval_hull_sound".to_string(),
            ProofTerm::new(
                "zono_t01_interval_hull_sound",
                "fun (n : Nat) => ZonoContainSound.t01_hull n",
                "T01 Interval hull soundness: direct ZonoContainSound.t01_hull \
                 constructor. Encodes the triangle-inequality argument \
                 |sum eps_i * g_{i,j}| <= sum |g_{i,j}| as a closed inductive \
                 witness. Part of #3363.",
            ),
        );

        // ── T02: Linear transform exactness ──────────────────────────────
        self.proofs.insert(
            "zono_t02_linear_transform_exact".to_string(),
            ProofTerm::new(
                "zono_t02_linear_transform_exact",
                "fun (n : Nat) => ZonoContainSound.t02_affine n",
                "T02 Linear transform exactness: same eps_i coefficients witness \
                 membership in W*Z+b. Direct ZonoContainSound.t02_affine \
                 constructor. Part of #3363.",
            ),
        );

        // ── T03: ReLU overapproximation soundness ────────────────────────
        self.proofs.insert(
            "zono_t03_relu_overapprox_sound".to_string(),
            ProofTerm::new(
                "zono_t03_relu_overapprox_sound",
                "fun (n : Nat) => ZonoContainSound.t03_relu_overapprox n",
                "T03 ReLU overapproximation soundness: lambda-relaxation \
                 contains max(0, x) on every crossing dimension and ReLU is \
                 exact on active/inactive dimensions. Direct \
                 ZonoContainSound.t03_relu_overapprox constructor. Part of #3363.",
            ),
        );

        // ── T04: Lambda-relaxation tightness ─────────────────────────────
        self.proofs.insert(
            "zono_t04_relu_lambda_relaxation_tight".to_string(),
            ProofTerm::new(
                "zono_t04_relu_lambda_relaxation_tight",
                "fun (n : Nat) => ZonoContainSound.t04_relu_tight n",
                "T04 Lambda-relaxation tightness: lambda = u/(u-l) parallelotope \
                 is the minimal linear overapproximation of ReLU on [l,u]. \
                 Direct ZonoContainSound.t04_relu_tight constructor. Part of #3363.",
            ),
        );

        // ── T05: ReLU always-active exactness ────────────────────────────
        self.proofs.insert(
            "zono_t05_relu_always_active_exact".to_string(),
            ProofTerm::new(
                "zono_t05_relu_always_active_exact",
                "fun (n : Nat) => ZonoContainSound.t05_relu_active n",
                "T05 ReLU always-active exactness: if l_j >= 0 everywhere, \
                 zonotope_relu(Z) = Z with no fresh error generators. Direct \
                 ZonoContainSound.t05_relu_active constructor. Part of #3363.",
            ),
        );

        // ── T06: ReLU always-inactive exactness ──────────────────────────
        self.proofs.insert(
            "zono_t06_relu_always_inactive_exact".to_string(),
            ProofTerm::new(
                "zono_t06_relu_always_inactive_exact",
                "fun (n : Nat) => ZonoContainSound.t06_relu_inactive n",
                "T06 ReLU always-inactive exactness: if u_j <= 0 everywhere, \
                 zonotope_relu(Z) is the origin. Direct \
                 ZonoContainSound.t06_relu_inactive constructor. Part of #3363.",
            ),
        );

        // ── T07: Affine+ReLU composition soundness ───────────────────────
        self.proofs.insert(
            "zono_t07_affine_relu_composition_sound".to_string(),
            ProofTerm::new(
                "zono_t07_affine_relu_composition_sound",
                "fun (n : Nat) => ZonoContainSound.t07_affine_relu n",
                "T07 Affine+ReLU composition soundness: composition of exact \
                 affine (T02) and sound ReLU (T03) is sound. Direct \
                 ZonoContainSound.t07_affine_relu constructor. Part of #3363.",
            ),
        );

        // ── T08: Minkowski sum soundness ─────────────────────────────────
        self.proofs.insert(
            "zono_t08_minkowski_sum_sound".to_string(),
            ProofTerm::new(
                "zono_t08_minkowski_sum_sound",
                "fun (n : Nat) => ZonoContainSound.t08_minkowski n",
                "T08 Minkowski sum soundness: concatenated eps coefficients \
                 witness membership in Z1 (+) Z2. Direct \
                 ZonoContainSound.t08_minkowski constructor. Part of #3363.",
            ),
        );

        // ── T08A: Minkowski reduce soundness ─────────────────────────────
        self.proofs.insert(
            "zono_t08a_minkowski_reduce_sound".to_string(),
            ProofTerm::new(
                "zono_t08a_minkowski_reduce_sound",
                "fun (n : Nat) => ZonoContainSound.t08a_minkowski_reduce n",
                "T08A Minkowski sum remains sound after generator reduction. \
                 Direct ZonoContainSound.t08a_minkowski_reduce constructor. \
                 Part of #3363.",
            ),
        );

        // ── T08B: Minkowski residual soundness ───────────────────────────
        self.proofs.insert(
            "zono_t08b_minkowski_residual_sound".to_string(),
            ProofTerm::new(
                "zono_t08b_minkowski_residual_sound",
                "fun (n : Nat) => ZonoContainSound.t08b_minkowski_residual n",
                "T08B Minkowski residual soundness: residual generators after \
                 reduction still witness pointwise sum containment. Direct \
                 ZonoContainSound.t08b_minkowski_residual constructor. \
                 Part of #3363.",
            ),
        );
    }
}
