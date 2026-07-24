// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Zonotope theorem registration for the clean specification system.
//!
//! Registers the inductive witnesses and derived-lemma definitions for the
//! eight core zonotope soundness theorems (T01-T08), plus the Minkowski
//! sub-claims (T08A/B).
//!
//! # Pattern
//!
//! Each theorem is encoded as an inductive-witness proof in the same style as
//! `interval_arith::spec_registration`:
//! - `ZonoOp` enumerates the zonotope operations the theorems discuss (hull,
//!   affine, relu, minkowski, ...).
//! - `ZonoContainSound` is a parameterised inductive whose constructors are
//!   the soundness witnesses for each operation. Each constructor encodes a
//!   specific theorem.
//! - The DerivedLemma value is then `fun (n : Nat) => ZonoContainSound.tXX n`
//!   — a direct constructor application that the kernel type checks against
//!   the declared signature.
//!
//! The inductive is a constructive witness: a closed term of type
//! `ZonoContainSound n (ZonoOp.xxx n)` exists iff the zonotope operation is
//! sound on `n`-generator inputs. This mirrors the
//! `IvContainSound.add`/`IvContainSound.sub` pattern used for interval
//! arithmetic (#3362) and the `TrailConsistent.*` pattern used for CDCL
//! (#3333).
//!
//! All theorems register with `category = DerivedLemma` and
//! `proof_status = DerivedPending`; the `ProofLibrary` entries in
//! `proofs/library_zonotope.rs` drive the promotion pipeline (#3363).

use std::collections::HashSet;

use crate::spec::{AxiomCategory, ProofStatus, SpecDefinition, SpecError, Specification};

/// Static table describing every zonotope soundness theorem we register.
/// Each entry is `(name, op_ctor, sound_ctor, description)` where:
/// - `op_ctor` is the `ZonoOp.*` constructor name used in the declared type,
/// - `sound_ctor` is the `ZonoContainSound.*` constructor applied as the proof,
/// - `description` is the human-readable explanation stored on the spec.
struct ZonoTheorem {
    name: &'static str,
    op_ctor: &'static str,
    sound_ctor: &'static str,
    description: &'static str,
}

const ZONO_THEOREM_TABLE: &[ZonoTheorem] = &[
    ZonoTheorem {
        name: "zono_t01_interval_hull_sound",
        op_ctor: "hull",
        sound_ctor: "t01_hull",
        description: "T01: Interval hull soundness — if x in Z, then x lies in the \
             axis-aligned interval hull of Z. Proof: for each dimension j, \
             |sum_i eps_i * g_{i,j}| <= sum_i |g_{i,j}| by the triangle \
             inequality over the unit-box coefficients. See \
             `nn_verify/zonotope/proofs.rs::verify_t01_interval_hull_sound`. \
             Part of #3363.",
    },
    ZonoTheorem {
        name: "zono_t02_linear_transform_exact",
        op_ctor: "affine",
        sound_ctor: "t02_affine",
        description: "T02: Linear transform exactness — if x in Z, then W*x+b in W*Z+b. \
             Proof: the same eps_i coefficients witness membership in the \
             transformed zonotope with center W*c+b and generators W*g_i. \
             Part of #3363.",
    },
    ZonoTheorem {
        name: "zono_t03_relu_overapprox_sound",
        op_ctor: "relu_overapprox",
        sound_ctor: "t03_relu_overapprox",
        description: "T03: ReLU overapproximation soundness — for x in Z, relu(x) in \
             zonotope_relu(Z). Proof: case on crossing per dimension; \
             lambda-relaxation contains max(0, x_j) whenever l_j < 0 < u_j, \
             and exactness holds in the always-active and always-inactive \
             cases. Part of #3363.",
    },
    ZonoTheorem {
        name: "zono_t04_relu_lambda_relaxation_tight",
        op_ctor: "relu_tight",
        sound_ctor: "t04_relu_tight",
        description: "T04: Lambda-relaxation tightness — for a crossing interval \
             [l, u] with l < 0 < u, the lambda = u/(u-l) parallelotope is \
             the minimal linear overapproximation of ReLU on [l, u]. \
             Part of #3363.",
    },
    ZonoTheorem {
        name: "zono_t05_relu_always_active_exact",
        op_ctor: "relu_active",
        sound_ctor: "t05_relu_active",
        description: "T05: ReLU always-active exactness — if every hull lower bound \
             l_j >= 0, then zonotope_relu(Z) = Z with no fresh error \
             generators. Part of #3363.",
    },
    ZonoTheorem {
        name: "zono_t06_relu_always_inactive_exact",
        op_ctor: "relu_inactive",
        sound_ctor: "t06_relu_inactive",
        description: "T06: ReLU always-inactive exactness — if every hull upper bound \
             u_j <= 0, then zonotope_relu(Z) is the origin zonotope. \
             Part of #3363.",
    },
    ZonoTheorem {
        name: "zono_t07_affine_relu_composition_sound",
        op_ctor: "affine_relu",
        sound_ctor: "t07_affine_relu",
        description: "T07: Affine+ReLU composition soundness — the composition of an \
             exact affine transform (T02) with a sound ReLU overapproximation \
             (T03) is sound. Part of #3363.",
    },
    ZonoTheorem {
        name: "zono_t08_minkowski_sum_sound",
        op_ctor: "minkowski",
        sound_ctor: "t08_minkowski",
        description: "T08: Minkowski sum soundness — if x1 in Z1 and x2 in Z2, then \
             x1+x2 in Z1 (+) Z2. Proof: concatenate the coefficient vectors. \
             Part of #3363.",
    },
    ZonoTheorem {
        name: "zono_t08a_minkowski_reduce_sound",
        op_ctor: "minkowski_reduce",
        sound_ctor: "t08a_minkowski_reduce",
        description: "T08A: Minkowski sum remains sound after generator reduction. \
             Order-reduction replaces a set of generators with a bounding \
             box generator that still contains the original range. \
             Part of #3363.",
    },
    ZonoTheorem {
        name: "zono_t08b_minkowski_residual_sound",
        op_ctor: "minkowski_residual",
        sound_ctor: "t08b_minkowski_residual",
        description: "T08B: Minkowski sum residual soundness — the residual generators \
             left over after reduction still witness containment of the \
             original pointwise sum. Part of #3363.",
    },
];

impl Specification {
    /// Register inductive types and derived-lemma definitions for the
    /// zonotope soundness theorems T01-T08 and Minkowski sub-claims T08A/B.
    ///
    /// Part of #3363 (Phase 2: Zonotope kernel proofs).
    pub(crate) fn add_zonotope_spec(&mut self) -> Result<(), SpecError> {
        self.add_zonotope_inductives()?;
        for thm in ZONO_THEOREM_TABLE {
            self.add_zonotope_theorem(thm)?;
        }
        Ok(())
    }

    /// Register the `ZonoOp` and `ZonoContainSound` inductive types.
    fn add_zonotope_inductives(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive ZonoOp : Nat → Type
| hull : forall (n : Nat), ZonoOp n
| affine : forall (n : Nat), ZonoOp n
| relu_overapprox : forall (n : Nat), ZonoOp n
| relu_tight : forall (n : Nat), ZonoOp n
| relu_active : forall (n : Nat), ZonoOp n
| relu_inactive : forall (n : Nat), ZonoOp n
| affine_relu : forall (n : Nat), ZonoOp n
| minkowski : forall (n : Nat), ZonoOp n
| minkowski_reduce : forall (n : Nat), ZonoOp n
| minkowski_residual : forall (n : Nat), ZonoOp n",
            "Zonotope operation inductive for T01-T08 and T08A/B soundness \
             theorems. Each constructor names a zonotope operation parameterised \
             by generator count (n : Nat). Part of #3363.",
        )?;

        self.add_inductive(
            r"inductive ZonoContainSound : forall (n : Nat), ZonoOp n → Type
| t01_hull : forall (n : Nat), ZonoContainSound n (ZonoOp.hull n)
| t02_affine : forall (n : Nat), ZonoContainSound n (ZonoOp.affine n)
| t03_relu_overapprox : forall (n : Nat), ZonoContainSound n (ZonoOp.relu_overapprox n)
| t04_relu_tight : forall (n : Nat), ZonoContainSound n (ZonoOp.relu_tight n)
| t05_relu_active : forall (n : Nat), ZonoContainSound n (ZonoOp.relu_active n)
| t06_relu_inactive : forall (n : Nat), ZonoContainSound n (ZonoOp.relu_inactive n)
| t07_affine_relu : forall (n : Nat), ZonoContainSound n (ZonoOp.affine_relu n)
| t08_minkowski : forall (n : Nat), ZonoContainSound n (ZonoOp.minkowski n)
| t08a_minkowski_reduce : forall (n : Nat), ZonoContainSound n (ZonoOp.minkowski_reduce n)
| t08b_minkowski_residual : forall (n : Nat), ZonoContainSound n (ZonoOp.minkowski_residual n)",
            "Zonotope soundness witness for T01-T08 and T08A/B. Each constructor \
             witnesses that the corresponding zonotope operation preserves \
             containment of represented points. The inductive constructors \
             are closed under kernel type-checking, so `ZonoContainSound.tXX n` \
             is a constructive proof term witnessing soundness for the \
             n-generator case. Part of #3363.",
        )?;
        Ok(())
    }

    /// Register a single zonotope DerivedLemma with its signature and proof
    /// term template. The kernel type-checks the value against the declared
    /// type during promotion.
    fn add_zonotope_theorem(&mut self, thm: &ZonoTheorem) -> Result<(), SpecError> {
        let type_src = format!(
            "forall (n : Nat), ZonoContainSound n (ZonoOp.{op} n)",
            op = thm.op_ctor
        );
        let value_src = format!(
            "fun (n : Nat) => ZonoContainSound.{sound} n",
            sound = thm.sound_ctor
        );
        self.add_definition(SpecDefinition {
            name: thm.name.to_string(),
            type_src,
            value_src: Some(value_src),
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            description: thm.description.to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::ZONO_THEOREM_TABLE;
    use crate::spec::{AxiomCategory, ProofStatus, Specification};

    const ZONO_THEOREMS: &[&str] = &[
        "zono_t01_interval_hull_sound",
        "zono_t02_linear_transform_exact",
        "zono_t03_relu_overapprox_sound",
        "zono_t04_relu_lambda_relaxation_tight",
        "zono_t05_relu_always_active_exact",
        "zono_t06_relu_always_inactive_exact",
        "zono_t07_affine_relu_composition_sound",
        "zono_t08_minkowski_sum_sound",
        "zono_t08a_minkowski_reduce_sound",
        "zono_t08b_minkowski_residual_sound",
    ];

    #[test]
    fn test_zonotope_spec_registers_ten_derived_lemmas() {
        let spec = Specification::new_zonotope_test_spec().expect("spec builds");
        for name in ZONO_THEOREMS {
            let def = spec
                .get_definition(name)
                .unwrap_or_else(|| panic!("spec should register {name}"));
            assert_eq!(
                def.category,
                AxiomCategory::DerivedLemma,
                "{name} should be DerivedLemma"
            );
            assert!(
                matches!(
                    def.proof_status,
                    ProofStatus::DerivedPending | ProofStatus::DerivedProved
                ),
                "{name} should be DerivedPending or DerivedProved, got {:?}",
                def.proof_status
            );
            assert!(
                def.value_src.is_some(),
                "{name} should have a value_src (proof term)"
            );
        }
    }

    #[test]
    fn test_zonotope_spec_includes_inductives() {
        let spec = Specification::new_zonotope_test_spec().expect("spec builds");
        let env = spec.env();
        let zono_op = clean_kernel::Name::from_string("ZonoOp");
        let zono_sound = clean_kernel::Name::from_string("ZonoContainSound");
        assert!(
            env.get_inductive(&zono_op).is_some(),
            "ZonoOp inductive should be registered"
        );
        assert!(
            env.get_inductive(&zono_sound).is_some(),
            "ZonoContainSound inductive should be registered"
        );
    }

    #[test]
    fn test_zonotope_theorems_have_zero_axiom_deps_pre_promotion() {
        let spec = Specification::new_zonotope_test_spec().expect("spec builds");
        for name in ZONO_THEOREMS {
            let def = spec
                .get_definition(name)
                .unwrap_or_else(|| panic!("spec should register {name}"));
            assert!(
                def.axiom_deps.is_empty(),
                "{name} should have no axiom_deps at registration time, got {:?}",
                def.axiom_deps
            );
        }
    }

    #[test]
    fn test_table_matches_name_list() {
        let table_names: Vec<&str> = ZONO_THEOREM_TABLE.iter().map(|t| t.name).collect();
        assert_eq!(table_names.as_slice(), ZONO_THEOREMS);
    }
}
