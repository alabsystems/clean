// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Snapshot-based extraction plan for issue #1282.
//!
//! This module is intentionally descriptive rather than executable production
//! logic. It records a source-level snapshot of `src/env/` before crate
//! extraction work:
//! - `ENV_FILE_METRICS` captures line counts for every file under `env/`
//!   except this planning file itself.
//! - `ENV_SUBMODULES` rolls those files up to top-level `env` submodules as
//!   declared in `env/mod.rs`, plus one currently unwired orphan test file.
//! - `ENV_GROUP_PLANS` defines the proposed extraction layers and their
//!   dependency graph.
//!
//! Key findings from the snapshot encoded below:
//! - `generated/` is the largest single extraction target at 21,937 LOC once
//!   `generated_overlay.rs` is included.
//! - Handwritten algebra is the next largest layer at 20,608 LOC.
//! - The minimal "must move together" foundation layer is still large
//!   (15,898 LOC) because it owns `Environment` mutation, inductive machinery,
//!   registries, and the Eq/HEq bootstrap.
//! - `tests_recursor.rs` exists under `env/` but is not wired through
//!   `env/mod.rs`; that should be resolved before any crate split.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum EnvModule {
    Foundation,
    DataPrelude,
    OrderPrelude,
    AlgebraPrelude,
    GeneratedTopology,
    AnalysisTopology,
    ExtendedOverlay,
    ContractsAndHarnesses,
    Tests,
    Orphaned,
}

impl EnvModule {
    pub(crate) const ALL: [Self; 10] = [
        Self::Foundation,
        Self::DataPrelude,
        Self::OrderPrelude,
        Self::AlgebraPrelude,
        Self::GeneratedTopology,
        Self::AnalysisTopology,
        Self::ExtendedOverlay,
        Self::ContractsAndHarnesses,
        Self::Tests,
        Self::Orphaned,
    ];

    pub(crate) fn is_candidate(self) -> bool {
        matches!(
            self,
            Self::Foundation
                | Self::DataPrelude
                | Self::OrderPrelude
                | Self::AlgebraPrelude
                | Self::GeneratedTopology
                | Self::AnalysisTopology
                | Self::ExtendedOverlay
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WiringState {
    WiredInModRs,
    OrphanedSourceFile,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct EnvGroupPlan {
    pub module: EnvModule,
    pub loc: usize,
    pub depends_on: &'static [EnvModule],
    pub extract_candidate: bool,
    pub note: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct EnvSubmoduleMetric {
    pub name: &'static str,
    pub loc: usize,
    pub bucket: EnvModule,
    pub wiring: WiringState,
    pub direct_deps: &'static [&'static str],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct EnvFileMetric {
    pub path: &'static str,
    pub loc: usize,
}

macro_rules! f {
    ($path:literal, $loc:literal) => {
        EnvFileMetric {
            path: $path,
            loc: $loc,
        }
    };
}

macro_rules! m {
    ($name:literal, $loc:literal, $bucket:ident, $wiring:ident, [$($dep:literal),* $(,)?]) => {
        EnvSubmoduleMetric {
            name: $name,
            loc: $loc,
            bucket: EnvModule::$bucket,
            wiring: WiringState::$wiring,
            direct_deps: &[$($dep),*],
        }
    };
}

pub(crate) const ENV_GROUP_PLANS: &[EnvGroupPlan] = &[
    EnvGroupPlan {
        module: EnvModule::Foundation,
        loc: 15_898,
        depends_on: &[],
        extract_candidate: true,
        note: "Keep `Environment`, declaration/registry mutation, native reducers, inductive builders, and core Eq/HEq bootstrap together.",
    },
    EnvGroupPlan {
        module: EnvModule::DataPrelude,
        loc: 7_448,
        depends_on: &[EnvModule::Foundation],
        extract_candidate: true,
        note: "Core data types, collections, monads, and typeclasses layer cleanly on top of the foundation APIs.",
    },
    EnvGroupPlan {
        module: EnvModule::OrderPrelude,
        loc: 8_079,
        depends_on: &[EnvModule::Foundation, EnvModule::DataPrelude],
        extract_candidate: true,
        note: "Ordering infrastructure sits above data primitives and does not create back-edges into higher math.",
    },
    EnvGroupPlan {
        module: EnvModule::AlgebraPrelude,
        loc: 20_608,
        depends_on: &[
            EnvModule::Foundation,
            EnvModule::DataPrelude,
            EnvModule::OrderPrelude,
        ],
        extract_candidate: true,
        note: "Largest handwritten prelude block after generated payloads; depends only on lower prelude layers and internal algebra helpers.",
    },
    EnvGroupPlan {
        module: EnvModule::GeneratedTopology,
        loc: 21_937,
        depends_on: &[EnvModule::Foundation],
        extract_candidate: true,
        note: "Best first extraction target: generated payloads are large, mechanically produced, and have narrow compile-time dependencies.",
    },
    EnvGroupPlan {
        module: EnvModule::AnalysisTopology,
        loc: 12_136,
        depends_on: &[
            EnvModule::Foundation,
            EnvModule::DataPrelude,
            EnvModule::OrderPrelude,
            EnvModule::AlgebraPrelude,
            EnvModule::GeneratedTopology,
        ],
        extract_candidate: true,
        note: "Metric, topology, and analysis overlays consume generated payloads and lower preludes without feeding back into them.",
    },
    EnvGroupPlan {
        module: EnvModule::ExtendedOverlay,
        loc: 9_657,
        depends_on: &[
            EnvModule::Foundation,
            EnvModule::DataPrelude,
            EnvModule::OrderPrelude,
            EnvModule::AlgebraPrelude,
            EnvModule::GeneratedTopology,
            EnvModule::AnalysisTopology,
        ],
        extract_candidate: true,
        note: "High-level domain overlays can remain feature-split above the analysis layer.",
    },
    EnvGroupPlan {
        module: EnvModule::ContractsAndHarnesses,
        loc: 1_335,
        depends_on: &[
            EnvModule::Foundation,
            EnvModule::DataPrelude,
            EnvModule::OrderPrelude,
            EnvModule::AlgebraPrelude,
            EnvModule::GeneratedTopology,
            EnvModule::AnalysisTopology,
            EnvModule::ExtendedOverlay,
        ],
        extract_candidate: false,
        note: "Keep contract helpers and test harness support in `clean-kernel`; they are not extraction targets.",
    },
    EnvGroupPlan {
        module: EnvModule::Tests,
        loc: 49_037,
        depends_on: &[
            EnvModule::Foundation,
            EnvModule::DataPrelude,
            EnvModule::OrderPrelude,
            EnvModule::AlgebraPrelude,
            EnvModule::GeneratedTopology,
            EnvModule::AnalysisTopology,
            EnvModule::ExtendedOverlay,
            EnvModule::ContractsAndHarnesses,
        ],
        extract_candidate: false,
        note: "Tests dominate raw LOC under `env/`, but they should stay local to the kernel crate.",
    },
    EnvGroupPlan {
        module: EnvModule::Orphaned,
        loc: 954,
        depends_on: &[EnvModule::ContractsAndHarnesses],
        extract_candidate: false,
        note: "Currently only `tests_recursor.rs`; wire or remove it before any crate split so the tree is structurally complete.",
    },
];

pub(crate) const ENV_FILE_METRICS: &[EnvFileMetric] = &[
    f!("aesop.rs", 148),
    f!("algebra.rs", 853),
    f!("algebra_abs.rs", 584),
    f!("algebra_abs_int.rs", 457),
    f!("algebra_abs_nat.rs", 244),
    f!("algebra_advanced/euclidean_domain.rs", 457),
    f!("algebra_advanced/euclidean_domain_int.rs", 375),
    f!("algebra_advanced/factorization/associated.rs", 301),
    f!("algebra_advanced/factorization/fate_stubs.rs", 363),
    f!("algebra_advanced/factorization/gcd_monoid.rs", 492),
    f!("algebra_advanced/factorization/int_gcd.rs", 269),
    f!("algebra_advanced/factorization/mod.rs", 17),
    f!("algebra_advanced/factorization/nat_gcd.rs", 293),
    f!("algebra_advanced/factorization/nat_gcd_props.rs", 290),
    f!("algebra_advanced/factorization/prime_irreducible.rs", 447),
    f!("algebra_advanced/factorization/ufm.rs", 277),
    f!("algebra_advanced/field.rs", 788),
    f!("algebra_advanced/integral_domain.rs", 341),
    f!("algebra_advanced/mod.rs", 16),
    f!("algebra_advanced/nontrivial.rs", 345),
    f!("algebra_advanced/well_founded.rs", 473),
    f!("algebra_basic.rs", 785),
    f!("algebra_basic_instances.rs", 251),
    f!("algebra_basic_instances_int.rs", 303),
    f!("algebra_basic_ofnat.rs", 267),
    f!("algebra_basic_ofnat_uint.rs", 372),
    f!("algebra_comm_group.rs", 405),
    f!("algebra_comm_monoid.rs", 327),
    f!("algebra_comm_semigroup.rs", 238),
    f!("algebra_dist.rs", 705),
    f!("algebra_field.rs", 749),
    f!("algebra_field_inst.rs", 619),
    f!("algebra_group_instances.rs", 315),
    f!("algebra_groups.rs", 461),
    f!("algebra_hetero.rs", 1052),
    f!("algebra_linear.rs", 334),
    f!("algebra_module.rs", 693),
    f!("algebra_ring.rs", 596),
    f!("algebra_ring_comm.rs", 872),
    f!("algebra_ring_fields.rs", 389),
    f!("algebra_ring_instances.rs", 406),
    f!("algebra_ring_semiring.rs", 1086),
    f!("algebra_structure_instances.rs", 260),
    f!("algebra_structures.rs", 518),
    f!("algebra_substructures.rs", 556),
    f!("algebraic_geometry.rs", 413),
    f!("cast_lemmas.rs", 367),
    f!("category_theory.rs", 289),
    f!("causal_inference.rs", 365),
    f!("combinatorics.rs", 476),
    f!("computability.rs", 252),
    f!("computational_geometry.rs", 282),
    f!("concurrency_theory.rs", 747),
    f!("core/trust.rs", 151),
    f!("core.rs", 806),
    f!("core_eq/basic.rs", 191),
    f!("core_eq/congr.rs", 154),
    f!("core_eq/congruence.rs", 368),
    f!("core_eq/context.rs", 50),
    f!("core_eq/recursors.rs", 326),
    f!("core_eq/transport.rs", 422),
    f!("core_eq.rs", 54),
    f!("core_heq/bridge.rs", 301),
    f!("core_heq/context.rs", 59),
    f!("core_heq/transport.rs", 359),
    f!("core_heq.rs", 53),
    f!("cryptography.rs", 313),
    f!("data.rs", 123),
    f!("data_collection_ops.rs", 631),
    f!("data_monad.rs", 552),
    f!("data_monad_control.rs", 508),
    f!("data_typeclasses.rs", 529),
    f!("data_typeclasses_beq.rs", 438),
    f!("data_typeclasses_hashable.rs", 277),
    f!("data_types.rs", 251),
    f!("data_types_arithmetic.rs", 759),
    f!("data_types_collections.rs", 125),
    f!("data_types_int_lemmas.rs", 618),
    f!("data_types_nat.rs", 739),
    f!("data_types_nat_lemmas.rs", 461),
    f!("data_types_uint.rs", 375),
    f!("decl_add.rs", 627),
    f!("decl_builder.rs", 663),
    f!("decl_emit.rs", 45),
    f!("decl_signature_oracle.rs", 706),
    f!("differential_equations.rs", 441),
    f!("differential_privacy.rs", 437),
    f!("elim_analysis.rs", 126),
    f!("euclidean_geometry.rs", 994),
    f!("fixed_point.rs", 394),
    f!("formal_logic.rs", 425),
    f!("functional_analysis.rs", 365),
    f!("generated/mod.rs", 85),
    f!("generated/simple_axioms.rs", 40),
    f!("generated/topology_characteristic.rs", 436),
    f!("generated/topology_cobordism.rs", 633),
    f!("generated/topology_connection.rs", 38),
    f!("generated/topology_contractible.rs", 629),
    f!("generated/topology_coproduct.rs", 351),
    f!("generated/topology_covering_space.rs", 945),
    f!("generated/topology_cw.rs", 190),
    f!("generated/topology_derham.rs", 524),
    f!("generated/topology_embedding.rs", 658),
    f!("generated/topology_fiber_bundle.rs", 1081),
    f!("generated/topology_filtration.rs", 276),
    f!("generated/topology_fundamental_group.rs", 717),
    f!("generated/topology_higher_homotopy.rs", 688),
    f!("generated/topology_homology.rs", 445),
    f!("generated/topology_homotopy_equivalence.rs", 1271),
    f!("generated/topology_kahler.rs", 63),
    f!("generated/topology_ktheory.rs", 474),
    f!("generated/topology_lie_group.rs", 43),
    f!("generated/topology_manifold.rs", 52),
    f!("generated/topology_morse.rs", 340),
    f!("generated/topology_path_connected.rs", 594),
    f!("generated/topology_payload_legacy.rs", 1939),
    f!("generated/topology_principal_bundle.rs", 34),
    f!("generated/topology_product.rs", 1378),
    f!("generated/topology_quotient.rs", 834),
    f!("generated/topology_retract.rs", 961),
    f!("generated/topology_scheme.rs", 315),
    f!("generated/topology_sheaf.rs", 609),
    f!("generated/topology_simplicial.rs", 257),
    f!("generated/topology_simply_connected.rs", 603),
    f!("generated/topology_spectral.rs", 692),
    f!("generated/topology_spin.rs", 99),
    f!("generated/topology_subspace.rs", 543),
    f!("generated/topology_suspension.rs", 748),
    f!("generated/topology_symplectic.rs", 52),
    f!("generated/topology_topological_space.rs", 572),
    f!("generated/topology_vector_bundle.rs", 695),
    f!("generated_overlay.rs", 1033),
    f!("graph_theory.rs", 773),
    f!("homological.rs", 321),
    f!("inductive_below.rs", 492),
    f!("inductive_builder.rs", 671),
    f!("inductive_fixed_indices.rs", 805),
    f!("inductive_no_confusion.rs", 1265),
    f!("inductive_recursor.rs", 653),
    f!("inductive_recursor_rules.rs", 327),
    f!("inductive_recursor_types.rs", 465),
    f!("information_theory.rs", 173),
    f!("init_contracts.rs", 1214),
    f!("init_data.rs", 345),
    f!("init_data_types.rs", 287),
    f!("init_data_types_collections.rs", 430),
    f!("init_shared.rs", 111),
    f!("logic.rs", 335),
    f!("logic_connectives.rs", 409),
    f!("logic_decidable.rs", 354),
    f!("logic_iff.rs", 489),
    f!("logic_ite.rs", 182),
    f!("logic_or.rs", 108),
    f!("logic_true_false.rs", 281),
    f!("measure_theory.rs", 367),
    f!("metric.rs", 546),
    f!("metric_bounded.rs", 292),
    f!("metric_compact.rs", 200),
    f!("metric_complete.rs", 323),
    f!("metric_completeness.rs", 360),
    f!("metric_continuity.rs", 512),
    f!("metric_continuity_lipschitz.rs", 337),
    f!("metric_continuity_uniform.rs", 325),
    f!("metric_separable.rs", 289),
    f!("metric_totally_bounded.rs", 298),
    f!("mod.rs", 1756),
    f!("native_reducers.rs", 513),
    f!("native_reducers_arith.rs", 385),
    f!("number_theory.rs", 296),
    f!("optimization.rs", 463),
    f!("order.rs", 891),
    f!("order_arith.rs", 1126),
    f!("order_int.rs", 1056),
    f!("order_le_lt.rs", 735),
    f!("order_lemmas.rs", 778),
    f!("order_lemmas_minmax.rs", 214),
    f!("order_lemmas_succ.rs", 326),
    f!("order_nat_cmp.rs", 689),
    f!("order_ord.rs", 575),
    f!("order_relation_props.rs", 686),
    f!("order_structures.rs", 1003),
    f!("real_complex_analysis.rs", 2093),
    f!("registration.rs", 616),
    f!("registries.rs", 698),
    f!("representation_theory.rs", 413),
    f!("serialization.rs", 169),
    f!("set_theory.rs", 616),
    f!("sorry_summary.rs", 113),
    f!("stochastic_processes.rs", 317),
    f!("tensor_ml.rs", 243),
    f!("test_helpers.rs", 121),
    f!("tests.rs", 10387),
    f!("tests_add_decl_audit.rs", 474),
    f!("tests_advanced.rs", 3889),
    f!("tests_advanced2/analysis.rs", 374),
    f!("tests_advanced2/combinatorics.rs", 653),
    f!("tests_advanced2/computability.rs", 383),
    f!("tests_advanced2/cryptography.rs", 324),
    f!("tests_advanced2/differential_equations.rs", 621),
    f!("tests_advanced2/formal_logic.rs", 352),
    f!("tests_advanced2/functional_analysis.rs", 381),
    f!("tests_advanced2/information_theory.rs", 123),
    f!("tests_advanced2/mod.rs", 17),
    f!("tests_advanced2/optimization.rs", 707),
    f!("tests_advanced2/set_theory.rs", 395),
    f!("tests_advanced2/stochastic_processes.rs", 308),
    f!("tests_builder_migration_regression.rs", 428),
    f!("tests_cast_simp.rs", 162),
    f!("tests_init_contracts.rs", 517),
    f!("tests_issue_1488.rs", 240),
    f!("tests_metric.rs", 3819),
    f!("tests_monad_init.rs", 328),
    f!("tests_numeric.rs", 4966),
    f!("tests_ordering.rs", 4507),
    f!("tests_positivity.rs", 391),
    f!("tests_recursor.rs", 954),
    f!("tests_registries.rs", 1155),
    f!("tests_shadowing_overlay.rs", 280),
    f!("tests_tensor_ml.rs", 391),
    f!("tests_topology.rs", 3278),
    f!("tests_topology_diff.rs", 3933),
    f!("tests_topology_harness.rs", 1266),
    f!("tests_topology_homotopy.rs", 3732),
    f!("tests_topology_manifold.rs", 256),
    f!("topology.rs", 335),
    f!("topology2.rs", 221),
    f!("topology_algebraic.rs", 437),
    f!("topology_algebraic2.rs", 293),
    f!("topology_basic.rs", 505),
    f!("topology_compact.rs", 725),
    f!("topology_connected.rs", 381),
    f!("topology_construct.rs", 264),
    f!("topology_diff.rs", 462),
    f!("topology_hausdorff.rs", 478),
    f!("topology_homeomorphism.rs", 609),
    f!("topology_homotopy.rs", 243),
    f!("topology_homotopy2.rs", 247),
    f!("trusted_ext.rs", 173),
    f!("type_theory.rs", 843),
    f!("types.rs", 498),
    f!("unfold.rs", 186),
];

pub(crate) const ENV_SUBMODULES: &[EnvSubmoduleMetric] = &[
    m!("aesop", 148, Foundation, WiredInModRs, []),
    m!(
        "algebra",
        853,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_abs",
        584,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_abs_int",
        457,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_abs_nat",
        244,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_advanced",
        5544,
        AlgebraPrelude,
        WiredInModRs,
        ["algebra_ring_fields", "decl_builder"]
    ),
    m!(
        "algebra_basic",
        785,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_basic_instances",
        251,
        AlgebraPrelude,
        WiredInModRs,
        []
    ),
    m!(
        "algebra_basic_instances_int",
        303,
        AlgebraPrelude,
        WiredInModRs,
        []
    ),
    m!(
        "algebra_basic_ofnat",
        267,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_basic_ofnat_uint",
        372,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_comm_group",
        405,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_comm_monoid",
        327,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_comm_semigroup",
        238,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_dist",
        705,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_field",
        749,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_field_inst",
        619,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_group_instances",
        315,
        AlgebraPrelude,
        WiredInModRs,
        []
    ),
    m!(
        "algebra_groups",
        461,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_hetero",
        1052,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!("algebra_linear", 334, AlgebraPrelude, WiredInModRs, []),
    m!(
        "algebra_module",
        693,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_ring",
        596,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_ring_comm",
        872,
        AlgebraPrelude,
        WiredInModRs,
        ["algebra_ring_fields", "decl_builder"]
    ),
    m!(
        "algebra_ring_fields",
        389,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_ring_instances",
        406,
        AlgebraPrelude,
        WiredInModRs,
        []
    ),
    m!(
        "algebra_ring_semiring",
        1086,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_structure_instances",
        260,
        AlgebraPrelude,
        WiredInModRs,
        []
    ),
    m!(
        "algebra_structures",
        518,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "algebra_substructures",
        556,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!("algebraic_geometry", 413, ExtendedOverlay, WiredInModRs, []),
    m!(
        "cast_lemmas",
        367,
        AlgebraPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!("category_theory", 289, ExtendedOverlay, WiredInModRs, []),
    m!("causal_inference", 365, ExtendedOverlay, WiredInModRs, []),
    m!("combinatorics", 476, ExtendedOverlay, WiredInModRs, []),
    m!("computability", 252, ExtendedOverlay, WiredInModRs, []),
    m!(
        "computational_geometry",
        282,
        ExtendedOverlay,
        WiredInModRs,
        []
    ),
    m!("concurrency_theory", 747, ExtendedOverlay, WiredInModRs, []),
    m!("core", 957, Foundation, WiredInModRs, ["decl_builder"]),
    m!(
        "core_eq",
        1565,
        Foundation,
        WiredInModRs,
        ["decl_builder", "decl_emit"]
    ),
    m!(
        "core_heq",
        772,
        Foundation,
        WiredInModRs,
        ["decl_builder", "decl_emit"]
    ),
    m!("cryptography", 313, ExtendedOverlay, WiredInModRs, []),
    m!(
        "data",
        123,
        DataPrelude,
        WiredInModRs,
        ["decl_builder", "init_shared"]
    ),
    m!(
        "data_collection_ops",
        631,
        DataPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "data_monad",
        552,
        DataPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "data_monad_control",
        508,
        DataPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "data_typeclasses",
        529,
        DataPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "data_typeclasses_beq",
        438,
        DataPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "data_typeclasses_hashable",
        277,
        DataPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "data_types",
        251,
        DataPrelude,
        WiredInModRs,
        ["decl_builder", "init_shared"]
    ),
    m!(
        "data_types_arithmetic",
        759,
        DataPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "data_types_collections",
        125,
        DataPrelude,
        WiredInModRs,
        ["decl_builder", "init_shared"]
    ),
    m!(
        "data_types_int_lemmas",
        618,
        DataPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "data_types_nat",
        739,
        DataPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "data_types_nat_lemmas",
        461,
        DataPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "data_types_uint",
        375,
        DataPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!("decl_add", 627, Foundation, WiredInModRs, ["types"]),
    m!("decl_builder", 663, Foundation, WiredInModRs, []),
    m!("decl_emit", 45, Foundation, WiredInModRs, []),
    m!(
        "decl_signature_oracle",
        706,
        Foundation,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "differential_equations",
        441,
        ExtendedOverlay,
        WiredInModRs,
        []
    ),
    m!(
        "differential_privacy",
        437,
        ExtendedOverlay,
        WiredInModRs,
        []
    ),
    m!("elim_analysis", 126, Foundation, WiredInModRs, []),
    m!(
        "euclidean_geometry",
        994,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!("fixed_point", 394, ExtendedOverlay, WiredInModRs, []),
    m!("formal_logic", 425, ExtendedOverlay, WiredInModRs, []),
    m!(
        "functional_analysis",
        365,
        ExtendedOverlay,
        WiredInModRs,
        []
    ),
    m!(
        "generated",
        20904,
        GeneratedTopology,
        WiredInModRs,
        ["decl_builder", "types"]
    ),
    m!(
        "generated_overlay",
        1033,
        GeneratedTopology,
        WiredInModRs,
        ["generated", "types"]
    ),
    m!("graph_theory", 773, ExtendedOverlay, WiredInModRs, []),
    m!("homological", 321, ExtendedOverlay, WiredInModRs, []),
    m!(
        "inductive_below",
        492,
        Foundation,
        WiredInModRs,
        ["decl_builder", "inductive_fixed_indices", "types"]
    ),
    m!(
        "inductive_builder",
        671,
        Foundation,
        WiredInModRs,
        ["decl_add", "inductive_fixed_indices", "types"]
    ),
    m!("inductive_fixed_indices", 805, Foundation, WiredInModRs, []),
    m!(
        "inductive_no_confusion",
        1265,
        Foundation,
        WiredInModRs,
        ["inductive_fixed_indices", "types"]
    ),
    m!(
        "inductive_recursor",
        653,
        Foundation,
        WiredInModRs,
        ["elim_analysis", "inductive_fixed_indices", "types"]
    ),
    m!(
        "inductive_recursor_rules",
        327,
        Foundation,
        WiredInModRs,
        []
    ),
    m!(
        "inductive_recursor_types",
        465,
        Foundation,
        WiredInModRs,
        ["inductive_fixed_indices"]
    ),
    m!("information_theory", 173, ExtendedOverlay, WiredInModRs, []),
    m!(
        "init_contracts",
        1214,
        ContractsAndHarnesses,
        WiredInModRs,
        []
    ),
    m!(
        "init_data",
        345,
        DataPrelude,
        WiredInModRs,
        ["decl_builder", "init_shared"]
    ),
    m!(
        "init_data_types",
        287,
        DataPrelude,
        WiredInModRs,
        ["decl_builder", "init_shared"]
    ),
    m!(
        "init_data_types_collections",
        430,
        DataPrelude,
        WiredInModRs,
        ["decl_builder", "init_shared"]
    ),
    m!("init_shared", 111, Foundation, WiredInModRs, []),
    m!("logic", 335, Foundation, WiredInModRs, ["decl_builder"]),
    m!(
        "logic_connectives",
        409,
        Foundation,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "logic_decidable",
        354,
        Foundation,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!("logic_iff", 489, Foundation, WiredInModRs, ["decl_builder"]),
    m!("logic_ite", 182, Foundation, WiredInModRs, ["decl_builder"]),
    m!("logic_or", 108, Foundation, WiredInModRs, ["decl_builder"]),
    m!(
        "logic_true_false",
        281,
        Foundation,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!("measure_theory", 367, AnalysisTopology, WiredInModRs, []),
    m!(
        "metric",
        546,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "metric_bounded",
        292,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "metric_compact",
        200,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "metric_complete",
        323,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "metric_completeness",
        360,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "metric_continuity",
        512,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "metric_continuity_lipschitz",
        337,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "metric_continuity_uniform",
        325,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "metric_separable",
        289,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "metric_totally_bounded",
        298,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!("native_reducers", 513, Foundation, WiredInModRs, []),
    m!("native_reducers_arith", 385, Foundation, WiredInModRs, []),
    m!("number_theory", 296, ExtendedOverlay, WiredInModRs, []),
    m!("optimization", 463, ExtendedOverlay, WiredInModRs, []),
    m!("order", 891, OrderPrelude, WiredInModRs, ["decl_builder"]),
    m!(
        "order_arith",
        1126,
        OrderPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "order_int",
        1056,
        OrderPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "order_le_lt",
        735,
        OrderPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "order_lemmas",
        778,
        OrderPrelude,
        WiredInModRs,
        ["decl_builder", "order"]
    ),
    m!(
        "order_lemmas_minmax",
        214,
        OrderPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "order_lemmas_succ",
        326,
        OrderPrelude,
        WiredInModRs,
        ["decl_builder", "order"]
    ),
    m!(
        "order_nat_cmp",
        689,
        OrderPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "order_ord",
        575,
        OrderPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "order_relation_props",
        686,
        OrderPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "order_structures",
        1003,
        OrderPrelude,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "real_complex_analysis",
        2093,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!("registration", 616, Foundation, WiredInModRs, ["types"]),
    m!(
        "registries",
        698,
        Foundation,
        WiredInModRs,
        ["aesop", "types"]
    ),
    m!(
        "representation_theory",
        413,
        ExtendedOverlay,
        WiredInModRs,
        []
    ),
    m!("serialization", 169, Foundation, WiredInModRs, ["types"]),
    m!(
        "set_theory",
        616,
        ExtendedOverlay,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!("sorry_summary", 113, Foundation, WiredInModRs, ["types"]),
    m!(
        "stochastic_processes",
        317,
        ExtendedOverlay,
        WiredInModRs,
        []
    ),
    m!("tensor_ml", 243, ExtendedOverlay, WiredInModRs, []),
    m!("test_helpers", 121, ContractsAndHarnesses, WiredInModRs, []),
    m!("tests", 10387, Tests, WiredInModRs, ["test_helpers"]),
    m!("tests_add_decl_audit", 474, Tests, WiredInModRs, []),
    m!("tests_advanced", 3889, Tests, WiredInModRs, []),
    m!(
        "tests_advanced2",
        4638,
        Tests,
        WiredInModRs,
        ["test_helpers"]
    ),
    m!(
        "tests_builder_migration_regression",
        428,
        Tests,
        WiredInModRs,
        []
    ),
    m!(
        "tests_cast_simp",
        162,
        Tests,
        WiredInModRs,
        ["test_helpers"]
    ),
    m!(
        "tests_init_contracts",
        517,
        Tests,
        WiredInModRs,
        ["init_contracts"]
    ),
    m!("tests_issue_1488", 240, Tests, WiredInModRs, []),
    m!("tests_metric", 3819, Tests, WiredInModRs, ["test_helpers"]),
    m!("tests_monad_init", 328, Tests, WiredInModRs, []),
    m!("tests_numeric", 4966, Tests, WiredInModRs, ["test_helpers"]),
    m!(
        "tests_ordering",
        4507,
        Tests,
        WiredInModRs,
        ["test_helpers"]
    ),
    m!("tests_positivity", 391, Tests, WiredInModRs, ["types"]),
    m!(
        "tests_recursor",
        954,
        Orphaned,
        OrphanedSourceFile,
        ["test_helpers"]
    ),
    m!("tests_registries", 1155, Tests, WiredInModRs, []),
    m!("tests_shadowing_overlay", 280, Tests, WiredInModRs, []),
    m!("tests_tensor_ml", 391, Tests, WiredInModRs, []),
    m!(
        "tests_topology",
        3278,
        Tests,
        WiredInModRs,
        ["test_helpers", "tests_topology_harness"]
    ),
    m!(
        "tests_topology_diff",
        3933,
        Tests,
        WiredInModRs,
        ["test_helpers"]
    ),
    m!(
        "tests_topology_harness",
        1266,
        Tests,
        WiredInModRs,
        [
            "generated",
            "topology_basic",
            "topology_compact",
            "topology_connected",
            "topology_hausdorff",
            "topology_homeomorphism"
        ]
    ),
    m!(
        "tests_topology_homotopy",
        3732,
        Tests,
        WiredInModRs,
        ["test_helpers"]
    ),
    m!("tests_topology_manifold", 256, Tests, WiredInModRs, []),
    m!(
        "topology",
        335,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder", "generated_overlay"]
    ),
    m!(
        "topology2",
        221,
        AnalysisTopology,
        WiredInModRs,
        ["generated_overlay"]
    ),
    m!(
        "topology_algebraic",
        437,
        AnalysisTopology,
        WiredInModRs,
        ["generated_overlay"]
    ),
    m!(
        "topology_algebraic2",
        293,
        AnalysisTopology,
        WiredInModRs,
        ["generated_overlay"]
    ),
    m!(
        "topology_basic",
        505,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder", "generated_overlay"]
    ),
    m!(
        "topology_compact",
        725,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "topology_connected",
        381,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "topology_construct",
        264,
        AnalysisTopology,
        WiredInModRs,
        ["generated", "generated_overlay"]
    ),
    m!(
        "topology_diff",
        462,
        AnalysisTopology,
        WiredInModRs,
        ["generated_overlay"]
    ),
    m!(
        "topology_hausdorff",
        478,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "topology_homeomorphism",
        609,
        AnalysisTopology,
        WiredInModRs,
        ["decl_builder"]
    ),
    m!(
        "topology_homotopy",
        243,
        AnalysisTopology,
        WiredInModRs,
        ["generated_overlay"]
    ),
    m!(
        "topology_homotopy2",
        247,
        AnalysisTopology,
        WiredInModRs,
        ["generated_overlay"]
    ),
    m!("trusted_ext", 173, Foundation, WiredInModRs, ["types"]),
    m!("type_theory", 843, ExtendedOverlay, WiredInModRs, []),
    m!("types", 498, Foundation, WiredInModRs, []),
    m!("unfold", 186, Foundation, WiredInModRs, ["types"]),
];

pub(crate) fn group_plan(module: EnvModule) -> &'static EnvGroupPlan {
    ENV_GROUP_PLANS
        .iter()
        .find(|plan| plan.module == module)
        .expect("missing group plan")
}

pub(crate) fn submodule(name: &str) -> Option<&'static EnvSubmoduleMetric> {
    ENV_SUBMODULES.iter().find(|metric| metric.name == name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};

    fn submodule_map() -> BTreeMap<&'static str, &'static EnvSubmoduleMetric> {
        ENV_SUBMODULES
            .iter()
            .map(|metric| (metric.name, metric))
            .collect()
    }

    fn transitive_dependencies(module: EnvModule) -> BTreeSet<EnvModule> {
        fn visit(current: EnvModule, out: &mut BTreeSet<EnvModule>) {
            if !out.insert(current) {
                return;
            }
            for dep in group_plan(current).depends_on {
                visit(*dep, out);
            }
        }

        let mut out = BTreeSet::new();
        for dep in group_plan(module).depends_on {
            visit(*dep, &mut out);
        }
        out
    }

    #[test]
    fn group_rollups_match_submodule_totals() {
        for plan in ENV_GROUP_PLANS {
            let total: usize = ENV_SUBMODULES
                .iter()
                .filter(|metric| metric.bucket == plan.module)
                .map(|metric| metric.loc)
                .sum();
            assert_eq!(
                plan.loc, total,
                "stale LOC rollup for {:?}: plan={}, actual={}",
                plan.module, plan.loc, total
            );
        }
    }

    #[test]
    fn extraction_group_graph_has_no_cycles() {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Mark {
            Visiting,
            Done,
        }

        fn dfs(module: EnvModule, marks: &mut BTreeMap<EnvModule, Mark>) -> Result<(), EnvModule> {
            match marks.get(&module) {
                Some(Mark::Done) => return Ok(()),
                Some(Mark::Visiting) => return Err(module),
                None => {}
            }

            marks.insert(module, Mark::Visiting);
            for dep in group_plan(module).depends_on {
                if dep.is_candidate() {
                    dfs(*dep, marks)?;
                }
            }
            marks.insert(module, Mark::Done);
            Ok(())
        }

        let mut marks = BTreeMap::new();
        for module in EnvModule::ALL {
            if module.is_candidate() {
                dfs(module, &mut marks).expect("candidate extraction graph contains a cycle");
            }
        }
    }

    #[test]
    fn candidate_groups_are_self_contained() {
        let by_name = submodule_map();

        for metric in ENV_SUBMODULES {
            let plan = group_plan(metric.bucket);
            if !plan.extract_candidate {
                continue;
            }

            let mut allowed = transitive_dependencies(metric.bucket);
            allowed.insert(metric.bucket);

            for dep in metric.direct_deps {
                let dep_metric = by_name
                    .get(dep)
                    .copied()
                    .unwrap_or_else(|| panic!("unknown dependency `{dep}` for `{}`", metric.name));
                let dep_plan = group_plan(dep_metric.bucket);

                assert!(
                    dep_metric.wiring == WiringState::WiredInModRs,
                    "candidate `{}` depends on orphaned `{}`",
                    metric.name,
                    dep_metric.name
                );
                assert!(
                    dep_plan.extract_candidate,
                    "candidate `{}` depends on non-candidate group {:?} via `{}`",
                    metric.name, dep_metric.bucket, dep_metric.name
                );
                assert!(
                    allowed.contains(&dep_metric.bucket),
                    "candidate `{}` in {:?} depends on `{}` in {:?}, which is outside its allowed upstream closure {:?}",
                    metric.name,
                    metric.bucket,
                    dep_metric.name,
                    dep_metric.bucket,
                    allowed
                );
            }
        }
    }

    #[test]
    fn orphaned_entries_remain_non_candidates() {
        let orphaned: Vec<_> = ENV_SUBMODULES
            .iter()
            .filter(|metric| metric.wiring == WiringState::OrphanedSourceFile)
            .collect();

        assert_eq!(
            orphaned.len(),
            1,
            "unexpected orphaned env files in snapshot"
        );
        assert_eq!(orphaned[0].name, "tests_recursor");
        assert!(!group_plan(orphaned[0].bucket).extract_candidate);
    }
}
