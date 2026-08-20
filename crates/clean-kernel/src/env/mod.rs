// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! Environment and declarations
//!
//! The environment contains all defined constants, inductives, etc.
//!
//! # Naming Conventions
//!
//! The Environment API follows these naming patterns:
//!
//! - **`get_X`**: Returns `Option<&T>` for lookups (e.g., `get_constant`, `get_inductive`)
//! - **`add_X`**: Validates and adds data (may fail with error)
//! - **`register_X`**: Adds pre-validated data (trusts caller, no validation)
//! - **`is_X`**: Boolean identity check ("is this a class?", "is this an instance?")
//! - **`has_X`**: Boolean state check ("has quot been initialized?", "has priority override?")
//! - **`with_X`**: Constructor variants for building objects with specific configurations
//! - **`_unchecked`**: Suffix indicating validation is skipped (for trusted imports)
#![allow(clippy::doc_overindented_list_items)]

use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{
    Constructor, ConstructorVal, InductiveDecl, InductiveType, InductiveVal, RecursorVal,
};
use crate::level::Level;
use crate::name::Name;
use crate::quot::{init_quot_vals, QuotKind, QuotVal};
use hashbrown::HashMap;
use serde::{Deserialize, Serialize};

// Extracted sub-modules for organization (see #307)
mod axiom_audit;
#[cfg(any(test, feature = "math-overlays"))]
mod carrier_refutation;
mod codata_origin;
mod decl_add;
mod decl_emit;
mod inductive_info;
mod init_shared;
mod origin;
mod proof_elision;
mod proof_quality;
#[cfg(any(test, feature = "math-overlays"))]
mod refute_axiom_body;
mod registration;
mod serialization;
#[cfg(test)]
mod shared_init;
mod snapshot;
mod sorry_summary;
mod sorry_tracer;
#[cfg(any(test, feature = "math-overlays"))]
mod soundness_certificate;
mod trusted_ext;
mod unfold;
pub use axiom_audit::{
    canonical_ambient_axiom_kind, is_foundational_axiom, is_trust_marker,
    CanonicalAmbientAxiomKind, CertificationAudit, CertificationIssue, ProofQuality,
    SoundnessReport,
};
#[cfg(any(test, feature = "math-overlays"))]
pub use carrier_refutation::{
    census_carriers, classify_refutation, is_refutable, scan_admitted_axioms, CarrierCensus,
    RefutationOutcome, RefutationScan,
};
pub use codata_origin::{CodataLane, CodataOrigin};
#[cfg(test)]
use decl_add::find_undef_level_param;
pub use decl_add::{mm_axiom_only, mm_two_pass_active, set_mm_axiom_only, MmAxiomOnlyGuard};
pub use inductive_deep_induction::{DeepIndError, DeepIndOutcome};
pub use inductive_info::InductiveInfo;
pub use inductive_local_lift::{LiftedFamilyInfo, LocalLift, LocalLiftError};
pub use inductive_local_lift_bridge::{BridgeOutcome, LocalLiftBridgeError};
pub use inductive_no_confusion::{
    NoConfusionRegenerationDiagnostic, NoConfusionRegenerationIssue, NoConfusionRegenerationReport,
};
pub use origin::{ConstantOrigin, DeclarationVerification, OriginTrust};
pub use proof_quality::{ProofQualityError, ProofQualityFinding};
#[cfg(any(test, feature = "math-overlays"))]
pub use refute_axiom_body::{refute_friedgut_body, refute_or_ok, Counterexample, RefuteBudget};
pub use serialization::{ConstantOriginInfo, JsonEnvironment, StructureFieldInfo};
pub use snapshot::{
    SnapshotError, SnapshotHeader, SnapshotLoadOutcome, ENV_SCHEMA_FINGERPRINT, SNAPSHOT_VERSION,
};
pub use sorry_summary::{DeclarationTrustSummary, SorrySummary};
pub use sorry_tracer::SorryTracer;
#[cfg(any(test, feature = "math-overlays"))]
pub use soundness_certificate::{
    C1Reverification, C2TcbEnumeration, C3TrustMarkers, C4Coverage, C4Refutation,
    C5ExploitResistance, GoldenTcb, SoundnessCertificate, TrustedBase,
};
pub use trusted_ext::TrustedEnvExt;

// Sub-modules for domain-specific initialization.
// Many overlay init methods are defined but not yet wired into the main init
// chain, so dead_code is expected during incremental development (#1769).
//
// Modules gated behind `cfg(any(test, feature = "math-overlays"))` are
// pure-overlay modules whose public functions are ONLY called from tests
// or from other gated modules. Gating them saves ~6.4K LOC from default
// `cargo check` debug builds (#1432). The remaining `#[allow(dead_code)]`
// modules contain functions called from live production code and cannot
// be safely gated without deeper refactoring.
#[cfg(any(test, feature = "math-overlays"))]
mod abstract_interpretation;
#[cfg(any(test, feature = "math-overlays"))]
mod abstract_interpretation_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod abstract_interpretation_framework;
#[cfg(any(test, feature = "math-overlays"))]
mod abstract_interpretation_framework_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod abstract_interpretation_framework_defs2;
#[cfg(any(test, feature = "math-overlays"))]
mod abstract_interpretation_framework_ext;
pub mod ai_proof_search;
#[cfg(test)]
pub(crate) mod ai_proof_tactics;
#[cfg(test)]
pub(crate) mod ai_verify_loop;
mod algebra;
mod algebra_abs;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_abs_int;
mod algebra_abs_nat;
mod algebra_advanced;
mod algebra_basic;
mod algebra_basic_instances;
mod algebra_basic_instances_int;
mod algebra_basic_ofnat;
mod algebra_basic_ofnat_uint;
mod algebra_bool_and_eq_true_bridge;
mod algebra_bool_comm_proof;
mod algebra_bool_dec_eq_proof;
mod algebra_comm_group;
mod algebra_comm_monoid;
mod algebra_comm_semigroup;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_dist;
mod algebra_field;
mod algebra_field_inst;
mod algebra_fin_dec_eq_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_fin_index_lemmas;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_fin_last_cases;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_fin_split_index;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_int_abs_add_le_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_int_abs_cond_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_int_abs_mul_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_int_abs_neg_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_int_abs_sub_abs_le_dist_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_int_abs_sub_le_proof;
mod algebra_int_add_assoc_negsucc_negsucc_negsucc_proof;
mod algebra_int_add_assoc_negsucc_negsucc_ofnat_succ_proof;
mod algebra_int_add_assoc_negsucc_ofnat_succ_negsucc_proof;
mod algebra_int_add_assoc_negsucc_ofnat_succ_ofnat_succ_proof;
mod algebra_int_add_assoc_ofnat_proof;
mod algebra_int_add_assoc_ofnat_succ_negsucc_negsucc_proof;
mod algebra_int_add_assoc_ofnat_succ_negsucc_ofnat_succ_proof;
mod algebra_int_add_assoc_ofnat_succ_ofnat_negsucc_proof;
mod algebra_int_add_assoc_proof;
mod algebra_int_add_assoc_zero_left_proof;
mod algebra_int_add_assoc_zero_middle_proof;
mod algebra_int_add_assoc_zero_right_proof;
mod algebra_int_add_comm_proof;
mod algebra_int_add_le_add_left_proof;
mod algebra_int_add_le_add_right_proof;
mod algebra_int_add_lt_add_left_proof;
mod algebra_int_add_lt_add_right_proof;
mod algebra_int_add_neg_cancel_right_proof;
mod algebra_int_add_neg_self_proof;
mod algebra_int_add_negsucc_negsucc_sub_nat_nat_zero_proof;
mod algebra_int_add_negsucc_ofnat_succ_proof;
mod algebra_int_add_negsucc_sub_nat_nat_proof;
mod algebra_int_add_ofnat_negsucc_proof;
mod algebra_int_add_ofnat_succ_negsucc_proof;
mod algebra_int_add_ofnat_succ_sub_nat_nat_proof;
mod algebra_int_add_one_sub_self_proof;
mod algebra_int_add_right_cancel_proof;
mod algebra_int_add_sub_add_left_proof;
mod algebra_int_add_sub_add_right_proof;
mod algebra_int_add_sub_nat_nat_negsucc_proof;
mod algebra_int_add_sub_nat_nat_ofnat_succ_proof;
mod algebra_int_add_sub_nat_nat_zero_left_ofnat_succ_proof;
mod algebra_int_add_sub_nat_nat_zero_right_negsucc_proof;
mod algebra_int_add_sub_nat_nat_zero_right_ofnat_succ_proof;
mod algebra_int_add_zero_proof;
mod algebra_int_dec_eq_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_int_dist_comm_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_int_dist_self_proof;
mod algebra_int_le_antisymm_proof;
mod algebra_int_le_of_add_le_add_left_proof;
mod algebra_int_le_of_add_le_add_right_proof;
mod algebra_int_le_of_lt_proof;
// Overlay-only: `register_int_le_of_ofnat_le_ofnat_proof` is reached only from
// gated overlays and tests; keep it on the `math-overlays` gate (cf. #1432).
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_int_le_of_ofnat_le_ofnat_proof;
mod algebra_int_le_refl_proof;
mod algebra_int_le_self_add_one_proof;
mod algebra_int_le_trans_proof;
mod algebra_int_left_distrib_proof;
mod algebra_int_lt_cross_trans_proof;
mod algebra_int_lt_iff_le_not_le_proof;
mod algebra_int_lt_irrefl_proof;
mod algebra_int_lt_of_add_lt_add_left_proof;
mod algebra_int_lt_of_add_lt_add_right_proof;
mod algebra_int_lt_of_le_of_lt_proof;
mod algebra_int_lt_of_lt_of_le_proof;
mod algebra_int_lt_trans_proof;
mod algebra_int_minmax_def_prime_proof;
mod algebra_int_minmax_proof;
mod algebra_int_mul_assoc_proof;
mod algebra_int_mul_comm_proof;
mod algebra_int_mul_le_mul_of_nonneg_left_proof;
mod algebra_int_mul_le_mul_of_nonneg_right_proof;
mod algebra_int_mul_le_mul_proof;
mod algebra_int_mul_left_cancel_ofnat_succ_proof;
mod algebra_int_mul_nonneg_proof;
mod algebra_int_mul_one_proof;
mod algebra_int_mul_pos_proof;
mod algebra_int_mul_zero_proof;
mod algebra_int_neg_add_proof;
mod algebra_int_neg_add_self_proof;
mod algebra_int_neg_mul_left_proof;
mod algebra_int_neg_mul_right_proof;
mod algebra_int_neg_neg_proof;
mod algebra_int_neg_sub_nat_nat_proof;
mod algebra_int_negofnat_add_proof;
mod algebra_int_negsucc_mul_sub_nat_nat_proof;
mod algebra_int_nonneg_add_proof;
mod algebra_int_ofnat_add_proof;
mod algebra_int_ofnat_mul_proof;
mod algebra_int_ofnat_mul_sub_nat_nat_proof;
mod algebra_int_ofnat_zero_le_proof;
mod algebra_int_one_mul_proof;
mod algebra_int_right_distrib_proof;
mod algebra_int_sub_add_one_self_proof;
mod algebra_int_sub_add_sub_cancel_proof;
mod algebra_int_sub_eq_add_neg_proof;
mod algebra_int_sub_nat_nat_add_add_proof;
mod algebra_int_sub_nat_nat_eq_add_proof;
mod algebra_int_sub_nat_nat_self_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_int_sub_nat_nat_self_succ_proof;
mod algebra_int_sub_nat_nat_succ_succ_proof;
mod algebra_int_sub_nat_nat_zero_left_proof;
mod algebra_int_sub_nat_nat_zero_right_proof;
mod algebra_int_sub_nat_nat_zero_succ_proof;
mod algebra_int_sub_self_proof;
mod algebra_int_tonat_ofnat_proof;
mod algebra_int_zero_add_proof;
mod algebra_int_zero_mul_proof;
mod algebra_list_char_dec_eq_proof;
mod algebra_nat_add_assoc_proof;
mod algebra_nat_add_comm_proof;
mod algebra_nat_add_left_cancel_proof;
mod algebra_nat_add_right_cancel_proof;
mod algebra_nat_add_succ_proof;
mod algebra_nat_add_zero_proof;
mod algebra_nat_beq_proof;
mod algebra_nat_bitwise_def;
mod algebra_nat_ble_le_proof;
mod algebra_nat_dec_eq_proof;
mod algebra_nat_dec_le_proof;
mod algebra_nat_div2_lt_self_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_eight_mul_pow_two_add_two_le_proof;
mod algebra_nat_eq_of_testbit_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_forty_eight_pow_eq_split_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_four_mul_pow_eq_proof;
mod algebra_nat_left_distrib_proof;
mod algebra_nat_mul_assoc_proof;
mod algebra_nat_mul_cancel_proof;
mod algebra_nat_mul_comm_proof;
mod algebra_nat_mul_one_proof;
mod algebra_nat_mul_succ_proof;
mod algebra_nat_mul_zero_proof;
mod algebra_nat_one_mul_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_one_pow_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_pow_add_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_pow_le_pow_left_proof;
mod algebra_nat_pow_le_pow_right_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_pow_mul_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_pow_nine_eightfold_le_budget_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_pow_nine_le_pow_two_eightfold_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_pow_one_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_pow_two_e_plus_one_cubed_proof;
mod algebra_nat_pow_two_succ_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_pow_zero_proof;
mod algebra_nat_right_distrib_proof;
mod algebra_nat_sub_zero_proof;
mod algebra_nat_succ_add_proof;
mod algebra_nat_succ_eq_add_one_proof;
mod algebra_nat_succ_inj_proof;
mod algebra_nat_succ_mul_proof;
mod algebra_nat_testbit_add_two_pow_proof;
mod algebra_nat_testbit_bitwise_proof;
mod algebra_nat_testbit_def;
mod algebra_nat_testbit_lt_pow_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_three_e_add_five_bound_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nat_xor_involution_proof;
mod algebra_nat_zero_add_proof;
mod algebra_nat_zero_mul_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_add;
// Recovered (kkl-nnreal-mul): NNReal mul carrier modules.
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_add_comm_assoc;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_add_cube;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_add_mul;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_add_sq;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_amgm_cross;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cancel;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cauchy;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_causeq_mul;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_cauchy_le;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_cauchy_mono;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_cauchy_step;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_cauchy_tele;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_def;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_dyadic;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_gen;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_gen_mono;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_identity;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_invariant;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_iscauchy;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_mono;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_seq;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_squeeze;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cbrt_upper;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cube_holder3_base;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cube_minkowski;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cube_minkowski_merge;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cube_mono;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cube_reassoc;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cube_superadd;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_cubed_amgm;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_desquare;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_finsum;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_finsum_add;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_finsum_cube;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_finsum_le;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_finsum_ofrat;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_finsum_smul;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_finsum_split;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_holder3_cross_mono;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_iscauchy_mul;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_iscauchy_ops;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_le;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_le_add;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_le_antisymm;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_le_self_add;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_mul;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_mul_cancel;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_mul_distrib;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_mul_lift;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_mul_op;
// Recovered (kkl-carrier-lattice): branch-only NNReal carrier modules.
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_add_laws;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_add_le;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_bounded_recovered;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_le_recovered;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_le_respects;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_nnrat;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_nnrat_max;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_nnrat_max_recovered;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_nnrat_order;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_nnrat_prefixmax;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_ofrat_inj;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_pow32;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_pow32_bound;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_pow43;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_pow43_cubed;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_pow43_gen_mono;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_reverse_cube;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_reverse_square;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_reverse_square_algebra;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_reverse_square_mono;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_reverse_square_sq;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_semiring_units;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_cauchy;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_cauchy_double;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_cauchy_le;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_cauchy_mono;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_cauchy_step;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_cauchy_tele;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_def;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_dyadic;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_dyadic_mono;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_gen;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_gen_mono;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_gen_mul;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_gen_mul_eq;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_gen_subadd;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_identity;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_invariant;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_iscauchy;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_le;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_mono;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_radicand;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_seq;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_squeeze;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_strict;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_sqrt_upper;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_three_cube;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_trans;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_two_four_thirds;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_nnreal_zero_add;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_abs_mul_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_abs_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_add_assoc_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_add_comm_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_add_lt_add_mixed;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_archimedean;
// Recovered (kkl-nnreal-mul): rat mul/div/inv leaves.
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_archimedean_intpos;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_archimedean_witness;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_cube_amgm;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_div_mul_cancel;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_inv_pos;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_mul_close_recovered;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_mul_left_close;
// Recovered (kkl-cube-amgm): self-contained polynomial-normalizer proof of
// Rat.cube_amgm_two_one (registered as Rat.cube_amgm_two_one_recovered to
// coexist with main's RatPolyProver-based proof). Owns the identity submodule.
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_cube_amgm_recovered;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_cube_identity;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_cube_le_sq_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_delta_choice;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_half_pos;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_halves;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_inv_dyadic;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_inv_dyadic_modulus;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_inv_dyadic_step;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_inv_mul;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_lt_or_eq;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_minmax_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_mul_cancel_left;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_mul_close;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_mul_respect;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_mul_strict;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_ofnat_mul;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_poly_prover;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_pow3_le_pow3_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_pownat_mulbase;
mod algebra_uint_dec_eq_proof;
pub(crate) use algebra_uint_dec_eq_proof::WrapperCarrier;
mod algebra_uint_dec_le_proof;
pub(crate) use data_typeclasses::uint_wrapper_carrier;
mod nat_arith_order_proof;
// `algebra_rat_mk_eq_bridge` REMOVED (#3654): bridge axiom was unsound
// under the current free-inductive Rat carrier. See
// `crates/clean-kernel/src/env/algebra_field_inst.rs` Tranche C note.
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_le_of_natcast_le_natcast_proof;
mod algebra_rat_le_trans_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_mul_assoc_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_mul_comm_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_mul_le_mul_proof;
mod algebra_rat_order_proofs;
mod algebra_rat_quotient;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_sub_add_assoc_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_sub_add_sub_proof;
mod algebra_rat_tranche_b_proofs;
// `algebra_rat_tranche_d1_proofs` REMOVED (#3654): proofs relied on the
// `Rat.mk_eq_mk_of_cross_eq` bridge (unsound under free inductive Rat).
// `Rat.zero_mul` and `Rat.mul_zero` are now honest domain axioms again.
// `algebra_rat_left_distrib_proof` REMOVED (#3654): proof relied on the
// `Rat.mk_eq_mk_of_cross_eq` bridge (unsound under free inductive Rat).
// `Rat.left_distrib` is now an honest domain axiom again.
mod algebra_group_instances;
mod algebra_groups;
mod algebra_hetero;
mod algebra_linear;
mod algebra_module;
mod algebra_ring;
mod algebra_ring_comm;
mod algebra_ring_fields;
mod algebra_ring_instances;
mod algebra_ring_semiring;
mod algebra_string_dec_eq_proof;
mod algebra_structure_instances;
mod algebra_structures;
mod algebra_substructures;
#[cfg(any(test, feature = "math-overlays"))]
mod algebraic_geometry;
#[cfg(any(test, feature = "math-overlays"))]
mod bcp_loop_refinement;
#[cfg(any(test, feature = "math-overlays"))]
mod bcp_loop_refinement_theorems;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_amgm;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_cauchy_schwarz;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_cauchy_schwarz_assemble;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_cauchy_schwarz_lagrange;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_diag_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_flip_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_inner_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_mul_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_offdiag_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_pair_diag;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_quad_diag;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_quad_orthogonality;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_sign_bilinear;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_sign_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_succ_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_symm_diff_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_chi_xside_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_delta_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_deriv_4norm;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_deriv_coeff;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_dyadic_level_sum;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_expect_congr_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_expect_one_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_prod_mul_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_prod_one_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_prod_succ_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_reindex_fixed_step;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_reindex_keystone;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_reindex_twocycle_step;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_sigma_complement;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_sigma_restrict;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_skip_coherence;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_skip_ne_p;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_sum_const;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_sum_const_one_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_sum_reindex;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_sum_remove;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_sum_skip;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fin_val_cast_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_finsum_cube_split;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_flip_invariant;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_flip_involution_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_flip_roundtrip_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_foundations;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fourth_power;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fourth_power_assemble_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fourth_power_even_pair_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fourth_power_expand_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_fourth_power_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_case_threshold;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_cheap_rungs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_coland;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_deg_band_masked;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_dr_sq_cancel;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_l2_core;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_masked_finsum;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_masked_noise;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_masked_reconcile;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_natcast_nine_sq;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_pow9_bridge;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_restricted_mass;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_retire;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_rung4;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_size_poly;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_tcb_bricks;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_friedgut_wiring;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc24_assemble;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc24_core;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc24_core_base;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc24_s7;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc24_step;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc43_core;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc43_core_base;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc43_core_step;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc43_four_le_pow;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc43_norm_split;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc43_two_point_close;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc_bounds;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc_bounds_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc_decode_split_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc_decode_surjective;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_hc_sum_split_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_high_degree_mass;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_influence_chain;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_inversion_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_amgm;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_applyt;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_applyt_coeff;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_applyt_pairing;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_assembly;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_bridge_level;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_bridgestruct_bool;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_bridgestruct_compose;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_bridgestruct_dc;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_bridgestruct_lr;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_bridgestruct_pointwise;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_cond_assembly;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_conditional;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_cubecharge;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_deg_band;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_doublecount;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dual_selfadjoint;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dual_semigroup;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualb_cs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualb_holder;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualb_interp;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualb_pow4_anchor;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualb_support;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualb_twonorm;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualbound_assemble;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualfinal_bound;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualfinal_h1;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualfinal_m2;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_desqcancel;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_glue;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_half2;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_halfderiv;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_holder;
// Recovered (kkl-dualhc-rational): branch-only modules for the UNCONDITIONAL
// dual-HC chain (H1/H2/percoord_linear/h_dual_sum/kkl_lowband_mass_fired) and
// its noise-semigroup / spectral / norm-cancel supporting rungs. These coexist
// with main's squared-shadow dual-HC; nothing is dropped.
#[cfg(any(test, feature = "math-overlays"))]
mod algebra_rat_pownat_mul_base;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_dualhc_w_spectral;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_band_reconcile;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_bandregroup;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_descent;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_final;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_h1;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_h1b;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_h1connect;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_minfl;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_noisefold;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_norm;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_norminfl;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_percoord;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_percoord_recovered;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_step2;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_step3;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_step4;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualhc_step4_assemble;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualres_combine;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualres_combine_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualres_holder;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualres_holder_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualres_m2;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_dualres_mask;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_emptyset;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_fourier_norm;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_halfpower;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_hcdual;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_hcdualtotal;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_k2b;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_levellower;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_levelsplit;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_levelwt;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_lowband;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_lowband_extract;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_m1_norm;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_m2close_contraction;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_mask_collapse;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_masssplit;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_maxinf;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_maxinf_uncond;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_natbridge;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_nnrpow;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_noise_compose;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_norm_reconcile;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_normparseval;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_pigeonhole;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_pigeonhole_pos;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_pow2_bridge;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_pow32_charge;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_pow32_consumer;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_pownat_inv_cancel;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_pownat_mono;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_rung2;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_rung2_core;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_rung2_noise;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_rung3;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_rung4_reflect;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_rung4_sqrtbound;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_rungb;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_smallinfl;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_squared_bound;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_strictadd;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_strictadd2;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_sumltsum;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_tailbound;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_total_influence;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_kkl_variance_le_one;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_compose;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_delta_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_density_symm;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_extend_bridge;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_fn;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_fn_linear;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_fn_split;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_fn_succ;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_lift;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_peel;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_self_adjoint;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_semigroup;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_semigroup_factor;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_noise_spectral;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_norm43;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_order_toolkit;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_order_toolkit_b1b;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_order_toolkit_b1b_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_order_toolkit_b1c;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_order_toolkit_b1c_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_order_toolkit_b1d;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_order_toolkit_b1d_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_order_toolkit_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_parseval_rung1;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_parseval_rung2;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_parseval_rung3;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_parseval_rung3b;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_peel;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_peel_compute;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_peel_parts;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_per_point_ct;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_pm_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_pointwise_keystone;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_pow2_succ_split;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_pow4_spectral;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_pow4_spectral_diag;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_pow_nat_nonneg;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_pow_nat_pos;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_prod_collapse_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_prod_offdiag_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_prod_single_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_ring_identities;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_ring_identities_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_subset_diag_extract;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_subset_sum;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_symmdiff_unique;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_theorems;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_two_point_base_legs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_two_point_base_lemma_a;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_two_point_base_moment;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_two_point_base_rhs;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_two_point_bound;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_two_point_sigma_le_two_uncond;
#[cfg(any(test, feature = "math-overlays"))]
mod boolean_analysis_xside_core;
#[cfg(any(test, feature = "math-overlays"))]
mod bounded_width_automatizability;
#[cfg(any(test, feature = "math-overlays"))]
mod bounded_width_automatizability_theorems;
mod cast_lemmas;
mod category_theory;
#[cfg(any(test, feature = "math-overlays"))]
mod causal_inference;
#[cfg(any(test, feature = "math-overlays"))]
mod cdcl_soundness;
#[cfg(any(test, feature = "math-overlays"))]
mod cdcl_soundness_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod cdcl_soundness_theorems;
mod classical_em_proof;
mod combinatorics;
#[cfg(any(test, feature = "math-overlays"))]
mod computability;
mod computational_geometry;
#[cfg(any(test, feature = "math-overlays"))]
mod concurrency_theory;
#[cfg(any(test, feature = "math-overlays"))]
pub mod constructive_claims;
mod core;
mod core_eq;
mod core_heq;
#[cfg(any(test, feature = "math-overlays"))]
mod craig_interpolation;
#[cfg(any(test, feature = "math-overlays"))]
mod craig_interpolation_theorems;
#[cfg(any(test, feature = "math-overlays"))]
mod cryptography;
#[cfg(any(test, feature = "math-overlays"))]
mod cutting_planes;
#[cfg(any(test, feature = "math-overlays"))]
mod cutting_planes_theorems;
mod data;
mod data_bool_ops;
mod data_collection_ops;
mod data_control_lazy;
mod data_dvd;
mod data_for_in;
mod data_fun_comp;
mod data_fun_const;
mod data_fun_flip;
mod data_fun_id;
mod data_functor;
mod data_getelem;
mod data_getelem_list;
mod data_insert_singleton;
mod data_list_get;
mod data_monad;
mod data_monad_control;
mod data_monad_insts;
mod data_nat_repr;
mod data_seq_classes;
mod data_typeclasses;
mod data_typeclasses_beq;
mod data_typeclasses_beq_list;
mod data_typeclasses_beq_of_decidable_eq;
mod data_typeclasses_beq_optstr;
mod data_typeclasses_hashable;
mod data_typeclasses_repr;
mod data_types;
mod data_types_arithmetic;
mod data_types_bitvec;
mod data_types_bool_simp;
mod data_types_collections;
mod data_types_finset;
mod data_types_int_lemmas;
mod data_types_list_perm;
mod data_types_multiset;
mod data_types_nat;
mod data_types_nat_div_mod_lemmas;
mod data_types_nat_lemmas;
mod data_types_nat_sub_simp;
mod data_types_nat_ulp_round_lemmas;
mod data_types_uint;
pub(crate) mod decl_builder;
#[cfg(test)]
pub(crate) mod decl_signature_oracle;
#[cfg(any(test, feature = "math-overlays"))]
mod differential_equations;
#[cfg(any(test, feature = "math-overlays"))]
mod differential_privacy;
#[cfg(any(test, feature = "math-overlays"))]
mod entropy_clause_quality;
#[cfg(any(test, feature = "math-overlays"))]
mod entropy_clause_quality_theorems;
mod euclidean_geometry;
#[cfg(any(test, feature = "math-overlays"))]
mod extension_rule;
#[cfg(any(test, feature = "math-overlays"))]
mod extension_rule_soundness;
#[cfg(any(test, feature = "math-overlays"))]
mod extension_rule_soundness_model_thms;
#[cfg(any(test, feature = "math-overlays"))]
mod extension_rule_soundness_theorems;
#[cfg(any(test, feature = "math-overlays"))]
mod extension_rule_theorems;
pub mod farkas_soundness;
#[cfg(any(test, feature = "math-overlays"))]
mod feasible_interpolation;
#[cfg(any(test, feature = "math-overlays"))]
mod feasible_interpolation_theorems;
mod fixed_point;
#[cfg(any(test, feature = "math-overlays"))]
mod formal_logic;
#[cfg(any(test, feature = "math-overlays"))]
mod fourier_boolean;
#[cfg(any(test, feature = "math-overlays"))]
mod fourier_boolean_theorems;
mod fourier_weight_parseval_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod functional_analysis;
#[cfg(any(test, feature = "math-overlays"))]
pub mod gamma_crown_verify;
#[cfg(any(test, feature = "math-overlays"))]
pub mod gamma_crown_verify_format;
pub(crate) mod generated;
pub(crate) mod generated_overlay;
#[cfg(any(test, feature = "math-overlays"))]
mod gf2_polynomial_calculus;
#[cfg(any(test, feature = "math-overlays"))]
mod gf2_polynomial_calculus_theorems;
mod graph_theory;
#[cfg(any(test, feature = "math-overlays"))]
mod homological;
#[cfg(any(test, feature = "math-overlays"))]
mod influence_fourier_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod information_theory;
#[cfg(any(test, feature = "math-overlays"))]
mod interpolation_proofs;
mod io_ops;
#[cfg(any(test, feature = "math-overlays"))]
mod isasat_refinement;
#[cfg(any(test, feature = "math-overlays"))]
mod isasat_refinement_theorems;
#[cfg(any(test, feature = "math-overlays"))]
mod labelled_interpolation_minimality;
#[cfg(any(test, feature = "math-overlays"))]
mod labelled_interpolation_minimality_theorems;
#[cfg(any(test, feature = "math-overlays"))]
mod learned_clause_minimality;
#[cfg(any(test, feature = "math-overlays"))]
mod learned_clause_minimality_theorems;
mod logic;
mod logic_connectives;
mod logic_decidable;
mod logic_decidable_instances;
mod logic_iff;
mod logic_ite;
mod logic_ite_lemmas;
mod logic_of_decide;
mod logic_or;
mod logic_prop_eq;
mod logic_simp_ite_eq;
mod logic_true_false;
mod measure_theory;
mod metric;
#[cfg(any(test, feature = "math-overlays"))]
mod metric_bounded;
#[cfg(any(test, feature = "math-overlays"))]
mod metric_compact;
#[cfg(any(test, feature = "math-overlays"))]
mod metric_complete;
#[cfg(any(test, feature = "math-overlays"))]
mod metric_completeness;
#[cfg(any(test, feature = "math-overlays"))]
mod metric_continuity;
#[cfg(any(test, feature = "math-overlays"))]
mod metric_continuity_lipschitz;
#[cfg(any(test, feature = "math-overlays"))]
mod metric_continuity_uniform;
#[cfg(any(test, feature = "math-overlays"))]
mod metric_separable;
#[cfg(any(test, feature = "math-overlays"))]
mod metric_totally_bounded;
mod nn_verification;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verification_c002;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verification_c002_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verification_c002_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verification_c002_values;
mod nn_verification_c009;
mod nn_verification_c009_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_abstract_domain;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_abstract_domain_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_abstract_domain_ibp;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_abstract_domain_ops_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_abstract_domain_thms;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_base;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_ext;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_ext_carriers;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_ext_compose;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_ext_compose_count_eq_self;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_ext_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_ext_t20;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_ext_t21;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_ext_t22;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_ext_t61_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_hyp;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_value_builders;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_blockwise_crown_values;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_cert_complexity;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_cert_parser;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_cert_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_cert_proofs_list;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_certified_eval;
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) mod nn_verify_certified_eval_compute;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_certified_eval_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_certified_eval_register;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_certified_training;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_certified_training_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_certified_training_thms;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_crown_backward;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_crown_layernorm;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_crown_layernorm_faithful;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_crown_layernorm_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_crown_layernorm_refl_succ;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_dot_product_error;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_eclipse_convergence;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_eclipse_convergence_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_eclipse_convergence_values;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_elementwise;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_elementwise_axioms;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_farkas_list;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_farkas_list_proofs;
#[cfg(any(test, feature = "math-overlays", feature = "farkas-constructive"))]
mod nn_verify_farkas_order;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_farkas_to_interval_constructive;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_farkas_to_interval_constructive_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_fin_sum;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_fin_sum_add_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_fin_sum_le_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_fin_sum_linearity;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_fin_sum_nonneg_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_fin_sum_single_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_fin_sum_smul_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_fin_sum_split_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_fin_sum_sub_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_float_rational;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_float_rational_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_foundation_theorems;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_foundation_theorems_farkas;
#[cfg(any(test, feature = "math-overlays", feature = "farkas-constructive"))]
mod nn_verify_foundation_theorems_farkas_constructive;
#[cfg(any(test, feature = "math-overlays", feature = "farkas-constructive"))]
mod nn_verify_foundation_theorems_farkas_constructive_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_foundation_types;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_composition;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_conv;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_linear;
#[cfg(any(test, feature = "math-overlays", feature = "farkas-constructive"))]
mod nn_verify_ibp_linear_add_le;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_linear_decomp;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_linear_define;
#[cfg(any(test, feature = "math-overlays", feature = "farkas-constructive"))]
mod nn_verify_ibp_linear_mul_le;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_linear_mul_nonpos_le;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_linear_per_component_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_linear_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_linear_transport;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_sigmoid;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_tightness;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_tightness_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_tightness_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_tightness_step_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_tightness_step_value;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_width_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_ibp_width_zero_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_interval_arith_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_interval_arith_rat_neg_le_neg_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_interval_arith_rat_sub_le_sub_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_interval_arith_width_le_monotone_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_interval_arith_width_monotone_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_interval_containment_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_interval_primitives;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_rat_interval;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_rat_interval_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_rounding_half_ulp;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_minkowski_define;
mod rust_giveback_refinement;
// `nn_verify_tier_b_rat_abs_proofs` module was deleted in #3565 when the
// four `Rat.abs_*` MASQUERADE theorems (Eq.refl / Rat.le_refl over the
// reducible identity carrier) were demoted to honest `Declaration::Axiom`.
// Its four proof-term builders had no remaining callers. See
// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Branch A.
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_interval_arith_t09_t10_helpers;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_interval_arith_t09_t10_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_nat_ordering;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_add_left_neg_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_add_neg_self_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_le_refl_max_zero_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_le_refl_min_zero_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_le_refl_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_max_eq_min;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_max_zero_zero_alt;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_min_eq_max;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_min_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_min_zero_zero_alt;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_mul_neg_zero_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_mul_one_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_mul_zero_one;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_mul_zero_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_neg_zero_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_zero_eq_max;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_zero_eq_min;
// Batch 4 (#3551): Rat min/max transitivity / idempotence at ground zero.
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_max_le_min_zero_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_max_max_zero_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_max_min_zero_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_min_le_max_zero_zero;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_tier_a_rat_min_min_zero_zero;
// #3615: canonical `Rat.min_le_max` constructive lemma (general case).
// Unblocks C004 Phase 2 γ-scale carrier body.
mod nat_le_inversion_proof;
mod nat_lt_irrefl_proof;
mod nat_lt_wf_proof;
mod nat_not_succ_lt_zero_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nat_strong_rec_lt;
mod nat_sub_order_remaining_proof;
mod nat_top_level_ordering_proof;
mod nat_totality_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_lipschitz;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_lipschitz_compose;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_lipschitz_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_lipschitz_eclipse;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_lipschitz_ext;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_matrix_rank;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_matrix_rank_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_mccormick;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_mccormick_attention;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_mccormick_attention_types;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_mccormick_ext;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_network_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_nullstellensatz;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_nullstellensatz_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_nullstellensatz_opaques;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_nullstellensatz_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_orbit_crown;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_orbit_crown_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_orbit_crown_theorems;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_pac_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_pac_proof_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_proof_complexity;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_proof_complexity_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_proof_guided_nas;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_proof_guided_nas_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_proof_guided_nas_defs2;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_rat_min_le_max;
#[cfg(any(test, feature = "math-overlays", feature = "farkas-constructive"))]
mod nn_verify_rat_ordering;
#[cfg(any(test, feature = "math-overlays", feature = "farkas-constructive"))]
mod nn_verify_rat_ordering_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_relu;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_relu_builders;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_relu_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_relu_stability;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_relu_stability_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_relu_stability_values;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_robustness_generalization;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_robustness_generalization_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_robustness_generalization_values;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_softmax_c011;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_softmax_c011_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_streaming_certs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_streaming_certs_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_streaming_certs_opaques;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_streaming_certs_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_types;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_types_ops;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_compress;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_compress_c001;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_compress_c001_consts;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_compress_define;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_compress_ext;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_contains;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_crown;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_crown_conjecture;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_crown_defs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_crown_values;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_to_ibp_faithful;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_to_ibp_sound_proof;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_to_ibp_sound_rhs;
#[cfg(any(test, feature = "math-overlays"))]
mod nn_verify_zonotope_to_ibp_summand;
#[cfg(any(test, feature = "math-overlays"))]
mod nnreal_poly_normalize;
#[cfg(any(test, feature = "math-overlays"))]
mod number_theory;
#[cfg(any(test, feature = "math-overlays"))]
mod optimization;
mod order;
mod order_arith;
mod order_int;
mod order_int_dec_le_lt_proof;
mod order_int_le_total_proof;
mod order_int_lt_trichotomy_proof;
mod order_le_lt;
mod order_lemmas;
mod order_lemmas_minmax;
mod order_lemmas_minmax_proofs;
mod order_lemmas_succ;
mod order_nat_cmp;
mod order_nat_le_antisymm_proof;
mod order_nat_le_total_proof;
mod order_nat_le_trans_proof;
mod order_nat_lt_trans_proof;
mod order_ord;
mod order_relation_props;
mod order_structures;
#[cfg(any(test, feature = "math-overlays"))]
mod pb_pigeonhole;
#[cfg(any(test, feature = "math-overlays"))]
mod pb_pigeonhole_length_bound;
#[cfg(any(test, feature = "math-overlays"))]
mod pb_pigeonhole_theorems;
#[cfg(test)]
pub(crate) mod proof_builder;
#[cfg(any(test, feature = "math-overlays"))]
mod proof_complexity_proofs;
#[cfg(any(test, feature = "math-overlays"))]
mod proof_hierarchy;
#[cfg(any(test, feature = "math-overlays"))]
mod proof_hierarchy_theorems;
pub mod proof_search;
mod quotient_setoid;
#[cfg(any(test, feature = "math-overlays"))]
mod real_cauchy_carrier;
mod real_complex_analysis;
#[cfg(any(test, feature = "math-overlays"))]
mod representation_theory;
#[cfg(any(test, feature = "math-overlays"))]
mod resolution_complexity;
#[cfg(any(test, feature = "math-overlays"))]
mod resolution_complexity_theorems;
mod set_theory;
#[cfg(any(test, feature = "math-overlays"))]
mod stochastic_processes;
#[cfg(any(test, feature = "math-overlays"))]
mod tensor_ml;
#[cfg(any(test, feature = "math-overlays"))]
mod topology;
#[cfg(any(test, feature = "math-overlays"))]
mod topology2;
#[cfg(any(test, feature = "math-overlays"))]
mod topology_algebraic;
#[cfg(any(test, feature = "math-overlays"))]
mod topology_algebraic2;
mod topology_basic;
#[cfg(any(test, feature = "math-overlays"))]
mod topology_compact;
#[cfg(any(test, feature = "math-overlays"))]
mod topology_connected;
#[cfg(any(test, feature = "math-overlays"))]
mod topology_construct;
#[cfg(any(test, feature = "math-overlays"))]
mod topology_diff;
#[cfg(any(test, feature = "math-overlays"))]
mod topology_hausdorff;
#[cfg(any(test, feature = "math-overlays"))]
mod topology_homeomorphism;
#[cfg(any(test, feature = "math-overlays"))]
mod topology_homotopy;
#[cfg(any(test, feature = "math-overlays"))]
mod topology_homotopy2;
#[cfg(any(test, feature = "math-overlays"))]
mod tree_width_resolution;
#[cfg(any(test, feature = "math-overlays"))]
mod tree_width_resolution_theorems;
#[cfg(any(test, feature = "math-overlays"))]
mod type_theory;
#[cfg(any(test, feature = "math-overlays"))]
mod verified_proof_search;
#[cfg(any(test, feature = "math-overlays"))]
mod verified_proof_search_theorems;
#[cfg(any(test, feature = "math-overlays"))]
mod veripb_checker;
#[cfg(any(test, feature = "math-overlays"))]
mod veripb_checker_steps;
#[cfg(any(test, feature = "math-overlays"))]
mod veripb_checker_theorems;
#[cfg(any(test, feature = "math-overlays"))]
mod veripb_checker_theorems_verifier;
#[cfg(any(test, feature = "math-overlays"))]
mod wf_recursion_support;
#[cfg(any(test, feature = "math-overlays"))]
mod width_expansion;
#[cfg(any(test, feature = "math-overlays"))]
mod width_expansion_theorems;

// Aesop tactic types - extracted for organization
mod aesop;
pub use aesop::{AesopIndexMode, AesopRule, AesopRuleBuilder, AesopRulePhase, AesopRuleSet};

// Core types - extracted for organization (see #1161)
mod types;
pub use types::{
    collect_fvar_ids_for_diagnostics, ConstantInfo, ConstantKind, Declaration, EnvError,
    EnvExtensionEntry, EnvExtensionEntryData, KernelClassInfo, KernelInstanceInfo,
    PersistentEnvExtensionState, Reducibility, SimpLemmaInfo, SimpPriority, TransparencyMode,
    DEFAULT_INSTANCE_PRIORITY, LEAN_DEFAULT_INSTANCE_PRIORITY,
};

// Bounded-memory closure loading: elide never-unfolded proof VALUES from a
// trusted imported closure environment (Mathverse Subsumption Engine WS3).
pub use proof_elision::{ProofElisionStats, ProofValueElision};

// Typed persistent environment extension framework (#916)
pub mod persistent_ext;
pub use persistent_ext::{
    get_ext_idx, register_persistent_ext, ExtensionIdx, PersistentExtEntry, PersistentExtState,
};

// Simp lemma persistent extension (first concrete consumer of the framework)
pub mod ext_simp;
pub use ext_simp::{simp_ext_idx, SimpExtEntry, SimpExtState};

// Instance registry persistent extension
pub mod ext_instance;
pub use ext_instance::{instance_ext_idx, InstanceExtEntry, InstanceExtState, InstanceInfo};

// General-purpose attribute registry persistent extension
pub mod ext_attr;
pub use ext_attr::{attr_ext_idx, AttrExtEntry, AttrExtState, AttrRegistration};

// Elimination analysis for inductive types (Prop-only vs large elimination)
pub(crate) mod elim_analysis;

// Inductive type construction - extracted for organization (see #1161, #307)
mod inductive_all_family;
mod inductive_aux_values;
mod inductive_below;
mod inductive_below_minors;
#[allow(clippy::unnecessary_cast)]
mod inductive_builder;
mod inductive_deep_induction;
mod inductive_fixed_indices;
mod inductive_local_lift;
mod inductive_local_lift_bridge;
mod inductive_nested_elim;
mod inductive_nested_restore;
mod inductive_no_confusion;
mod inductive_no_confusion_hetero;
mod inductive_recursor;
mod inductive_recursor_minor;
mod inductive_recursor_rules;
mod inductive_recursor_types;
mod inductive_recursor_types_mutual;
mod rec_apply;

// Type class, aesop rule, and attribute registries - extracted for organization (see #1161)
mod registries;

// Built-in native reducer functions for @[implemented_by]/@[extern] support
// Differential reducer harness vs Lean v4.30 ground truth (carrier-parity A6)
#[cfg(test)]
mod carrier_differential_tests;
// P2 Char seed-shape fidelity vs the v4.30 oracle (carrier-parity A5)
#[cfg(test)]
mod carrier_char_fidelity_tests;
mod native_reducers;
mod native_reducers_arith;
#[cfg(test)]
mod native_reducers_arith_tests;
mod native_reducers_beq_shortcircuit;
mod native_reducers_bitvec;
mod native_reducers_bool_ext;
mod native_reducers_char;
mod native_reducers_decidable;
mod native_reducers_decidable_aliases;
mod native_reducers_decidable_ext;
#[cfg(test)]
mod native_reducers_decidable_ext_tests;
#[cfg(test)]
mod native_reducers_decidable_tests;
mod native_reducers_float;
#[cfg(test)]
mod native_reducers_float_tests;
mod native_reducers_float_to_rat;
mod native_reducers_hetero_shortcircuit;
mod native_reducers_init;
mod native_reducers_int;
mod native_reducers_name;
mod native_reducers_platform;
mod native_reducers_sint;
mod native_reducers_string;
mod native_reducers_string_ext;
mod native_reducers_uint;
mod native_reducers_uint_conv;
#[cfg(test)]
mod reduction_cache;
#[cfg(test)]
mod tests_native_reducers_init;
pub use native_reducers::NativeReducerFn;
pub(crate) use native_reducers_string::murmur_hash_64a;

/// The environment containing all declarations.
///
/// An `Environment` stores all definitions, axioms, theorems, and inductive types
/// that can be referenced during type checking. It is the persistent state that
/// accumulates as declarations are added.
///
/// # Example
///
/// ```
/// use clean_kernel::{Declaration, Environment, Expr, Name};
///
/// let mut env = Environment::new();
///
/// // Add an axiom: `myProp : Prop`
/// let prop = Expr::prop();
/// let name = Name::from_string("myProp");
/// let axiom = Declaration::Axiom {
///     name: name.clone(),
///     level_params: vec![],
///     type_: prop,
/// };
/// env.add_decl(axiom).expect("axiom over `Prop` always type-checks");
///
/// // Look up the constant
/// assert!(env.get_const(&name).is_some());
/// ```
/// A lazy, demand-paged source of [`ConstantInfo`] for the trusted import closure.
///
/// The zero-copy closure loader installs a `ConstantSource` so closure constants are
/// materialized on first lookup from mmap-backed shards, instead of the whole closure
/// being eagerly deserialized into [`Environment::constants`] (the ~100GiB OOM on deep
/// Mathlib). [`Environment::get_const`] consults the eager map FIRST and falls back to
/// the source only on a miss, so an `Environment` with no source set (the default)
/// behaves byte-identically to before.
///
/// Implementors hand out `&ConstantInfo` borrows stable for the lifetime of `&self`
/// (e.g. an append-only cache), since `get_const` returns a borrow. The source is
/// shared (`Arc`), `Send + Sync`, metadata-only, and can never mint a verdict — it
/// only supplies the same `ConstantInfo` the eager path would have built (pinned by
/// the eager-vs-lazy KernelVerified-set invariance gate). This trait is pure-safe;
/// any `unsafe` needed for stable references lives in the implementor's crate, so
/// `clean-kernel` stays `#![forbid(unsafe_code)]`.
pub trait ConstantSource: std::fmt::Debug + Send + Sync {
    /// The constant named `name`, materialized on demand, or `None` if absent here.
    fn get(&self, name: &Name) -> Option<&ConstantInfo>;

    /// Whether this source provides `name` (without forcing materialization).
    fn contains(&self, name: &Name) -> bool;

    /// All names this source can serve, for closure enumeration (e.g. scanning
    /// imported constants for typeclass instances). Default empty for sources
    /// that do not support enumeration.
    fn names(&self) -> Vec<Name> {
        Vec::new()
    }

    /// A fresh view of this source with any internal memoization CLEARED, or
    /// `None` (the default) for sources with no cache to reset.
    ///
    /// PURE MEMORY HOOK — soundness-neutral by contract: a fresh view MUST
    /// materialize byte-identical constants to the original (a source's cache
    /// is a memo of deterministic materialization, never an input to it), so
    /// swapping views can never change what any name resolves to — only WHEN
    /// the memo's memory is reclaimed. Long-running consumers (e.g. a chunked
    /// batch checker) may swap views at their own batch boundaries via
    /// [`Environment::refresh_constant_source_cache`] to bound resident
    /// memoized constants to one batch's working set.
    fn fresh(&self) -> Option<std::sync::Arc<dyn ConstantSource>> {
        None
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Environment {
    /// The mode this environment operates in (Constructive, Classical, etc.)
    /// This affects which expressions and axioms are valid.
    mode: crate::mode::CleanMode,
    /// All constants (definitions, axioms, theorems)
    constants: HashMap<Name, ConstantInfo>,
    /// Optional lazy source for trusted-closure constants NOT present in
    /// `constants` (the zero-copy mmap loader). `None` (the default) ⇒ `get_const`
    /// behaves exactly as before. Skipped by serde: a persisted environment is
    /// fully owned, with no lazy backing.
    #[serde(skip)]
    lazy_source: Option<std::sync::Arc<dyn ConstantSource>>,
    /// Per-constant origin/trust metadata, kept out of `ConstantInfo`.
    #[serde(default)]
    constant_origins: HashMap<Name, ConstantOrigin>,
    /// Transient validation provenance for exact declaration type/value pairs.
    ///
    /// This is intentionally not serialized: an environment loaded from an
    /// artifact must not inherit a kernel-checked claim without rechecking.
    /// Missing metadata is conservative/unknown, never checked-by-default.
    #[serde(skip)]
    declaration_verification: HashMap<Name, DeclarationVerification>,
    /// Provenance for elaborator-generated `codata`/`codef` constants (B2).
    ///
    /// Not serialized, for the same reason as `declaration_verification` and
    /// one more: this is a HINT that a consumer must structurally replay, so a
    /// deserialized artifact must not be able to ship a forged origin claiming
    /// a hand-written constant is generated codata. Absence downgrades (the
    /// consumer declines); presence still authorizes nothing on its own.
    /// Never consulted by type checking. See [`codata_origin`].
    #[serde(skip)]
    codata_origins: HashMap<Name, CodataOrigin>,
    /// Carrier types the `codata` command generated (B3 carrier provenance).
    ///
    /// Not serialized, for the same reasons as `codata_origins`. Recognition
    /// requires membership here, so a hand-written type that merely owns a
    /// `<C>.corec` cannot be mistaken for generated codata.
    #[serde(skip)]
    codata_carriers: hashbrown::HashSet<Name>,
    /// Persistent environment extension entries and state (Lean 4-compatible).
    persistent_extensions: HashMap<Name, PersistentEnvExtensionState>,
    /// Materialized typed extension states (from persistent_ext framework, #916).
    /// Built lazily from `persistent_extensions` on first access.
    #[serde(default)]
    extension_states: persistent_ext::EnvExtensionStates,
    /// Inductive type information
    inductives: HashMap<Name, InductiveVal>,
    /// Constructor information
    constructors: HashMap<Name, ConstructorVal>,
    /// Recursor information
    recursors: HashMap<Name, RecursorVal>,
    /// Quotient type information
    quotients: HashMap<Name, QuotVal>,
    /// Whether quotient types have been initialized
    quot_init: bool,
    /// Whether Eq type has been initialized
    eq_init: bool,
    /// Whether HEq (heterogeneous equality) type has been initialized
    heq_init: bool,
    /// Whether propext axiom has been added
    propext_init: bool,
    /// Whether funext axiom has been added
    funext_init: bool,
    /// Whether Quot.sound axiom has been added
    quot_sound_init: bool,
    /// Whether Iff structure has been initialized
    iff_init: bool,
    /// Whether the Prop-level simp equalities (and_true, or_false, …) have been
    /// registered as `propext`-based theorems
    prop_eq_lemmas_init: bool,
    /// Whether the Bool-level simp equalities (Bool.and_true, Bool.or_false,
    /// Bool.not_not, …) have been registered as `Bool.rec`/`Eq.refl` theorems
    bool_simp_lemmas_init: bool,
    /// Whether the `Nat.sub`-level simp equalities (Nat.sub_zero, Nat.sub_self,
    /// Nat.add_sub_cancel, Nat.zero_sub, Nat.sub_one) have been registered as
    /// `Nat.rec`/`Eq.refl` theorems
    nat_sub_simp_lemmas_init: bool,
    /// Whether Decidable typeclass has been initialized
    decidable_init: bool,
    /// Whether ite has been initialized
    ite_init: bool,
    /// Whether the canonical `Decidable True`/`Decidable False` instances
    /// (`instDecidableTrue`/`instDecidableFalse`) have been registered.
    decidable_true_false_inst_init: bool,
    /// Whether Classical axioms have been added
    classical_init: bool,
    /// Whether And structure has been initialized
    and_init: bool,
    /// Whether Or disjunction has been initialized
    or_init: bool,
    /// Whether Exists inductive has been initialized
    exists_init: bool,
    /// Whether True/False types have been initialized
    true_false_init: bool,
    /// Whether Prod structure has been initialized
    prod_init: bool,
    /// Whether PProd structure has been initialized
    pprod_init: bool,
    /// Whether Sigma dependent pair has been initialized
    sigma_init: bool,
    /// Whether Subtype structure has been initialized
    subtype_init: bool,
    /// Whether Option type has been initialized
    option_init: bool,
    /// Whether Sum disjoint union has been initialized
    sum_init: bool,
    /// Whether PSum (universe-polymorphic Sum) has been initialized
    psum_init: bool,
    /// Whether PSigma (universe-polymorphic Sigma) has been initialized
    psigma_init: bool,
    /// Whether Empty type has been initialized
    empty_init: bool,
    /// Whether PEmpty type has been initialized
    pempty_init: bool,
    /// Whether Bool type has been initialized
    bool_init: bool,
    /// Whether Nat type has been initialized
    nat_init: bool,
    /// Whether ULift type has been initialized
    ulift_init: bool,
    /// Whether Char type has been initialized
    char_init: bool,
    /// Whether String type has been initialized
    string_init: bool,
    /// Whether `String.append` definition has been initialized
    string_append_init: bool,
    /// Whether List type has been initialized
    list_init: bool,
    /// Whether List membership (`List.Mem` + instance + lemmas) has been initialized
    list_mem_init: bool,
    /// Whether List permutation (`List.Perm` + refl/symm) has been initialized
    list_perm_init: bool,
    /// Whether the `Multiset` quotient prelude (`List.Nodup`, `Multiset`,
    /// `Multiset.nil`/`cons`/`Mem`) has been initialized
    multiset_init: bool,
    /// Whether the `Finset` prelude (`Multiset.Nodup`, `Finset`,
    /// `Finset.empty`/`Mem`) has been initialized
    finset_init: bool,
    /// Whether Int type has been initialized
    int_init: bool,
    /// Whether UInt8 type has been initialized
    uint8_init: bool,
    /// Whether UInt16 type has been initialized
    uint16_init: bool,
    /// Whether UInt32 type has been initialized
    uint32_init: bool,
    /// Whether UInt64 type has been initialized
    uint64_init: bool,
    /// Whether Float type has been initialized
    float_init: bool,
    /// Whether Unit type has been initialized
    unit_init: bool,
    /// Whether PUnit (universe-polymorphic unit) has been initialized
    punit_init: bool,
    /// Whether PLift type has been initialized
    plift_init: bool,
    /// Whether Fin type has been initialized
    fin_init: bool,
    /// Whether Array type has been initialized
    array_init: bool,
    /// Whether IO monad has been initialized
    io_init: bool,
    /// Whether IO operation axioms have been initialized (IO.println, etc.)
    io_ops_init: bool,
    /// Whether StateT monad transformer has been initialized
    state_t_init: bool,
    /// Whether StateM type alias has been initialized
    state_m_init: bool,
    /// Whether Id monad has been initialized
    id_init: bool,
    /// Whether abstract monad type classes (Bind, Pure, Bind.bind, Pure.pure) have been initialized
    monad_classes_init: bool,
    /// Whether the `id` function combinator has been initialized (Brick P1)
    #[serde(default)]
    fun_id_init: bool,
    /// Whether the `Function.comp` combinator has been initialized
    #[serde(default)]
    fun_comp_init: bool,
    /// Whether the `flip` combinator has been initialized
    #[serde(default)]
    fun_flip_init: bool,
    /// Whether the `Function.const` combinator has been initialized
    #[serde(default)]
    fun_const_init: bool,
    /// Whether the `Functor` class (+ map/mapConst/mapRev) has been initialized (Brick P1)
    #[serde(default)]
    functor_class_init: bool,
    /// Whether the `Functor Option` / `Functor List` instances have been initialized (Brick P1)
    #[serde(default)]
    functor_instances_init: bool,
    /// Whether the `Seq`/`SeqLeft`/`SeqRight` classes have been initialized (Brick P1)
    #[serde(default)]
    seq_classes_init: bool,
    /// Whether the `Seq`/`SeqLeft`/`SeqRight` `Option` instances have been initialized (Brick P1)
    #[serde(default)]
    seq_option_insts_init: bool,
    /// Whether the real `Pure`/`Bind` class structures have been initialized (Brick B07)
    #[serde(default)]
    pure_bind_classes_init: bool,
    /// Whether the `Pure Option`/`Bind Option` instances have been initialized (Brick B07)
    #[serde(default)]
    monad_option_insts_init: bool,
    /// Whether the `Pure Id`/`Bind Id` identity-monad instances have been
    /// initialized (Brick B22 — Id-monad reduction)
    #[serde(default)]
    monad_id_insts_init: bool,
    /// Whether the `Pure List`/`Bind List` instances have been initialized (Brick B07;
    /// builtin-prelude-only — Lean core has no List monad instance)
    #[serde(default)]
    monad_list_insts_init: bool,
    /// Strict monad-instance gate for the `--prelude lean4-core` check lane
    /// (Brick B07): when set, the elaborator's monad-materialization pass
    /// rejects `Pure.pure`/`Bind.bind` stub applications over a concrete monad
    /// that has no registered `Pure`/`Bind` instance and is not one of the
    /// stub-modeled Lean-core monads — mirroring real Lean core's
    /// "failed to synthesize" rejection (e.g. `do` over `List`,
    /// GAP_SWEEP_2026-07-09 §5 OVER_ACCEPT-01).
    #[serde(default)]
    lean4_core_strict_monads: bool,
    /// Whether the `HAndThen`/`HOrElse` lazy hetero classes have been initialized (Brick P1)
    #[serde(default)]
    handthen_horelse_init: bool,
    /// Whether the `HAndThen`/`HOrElse` `Option` instances have been initialized (Brick 3)
    #[serde(default)]
    handthen_horelse_option_insts_init: bool,
    /// Whether `Bind.bindLeft`/`Bind.kleisliRight`/`Bind.kleisliLeft` have been initialized (Brick P1)
    #[serde(default)]
    bind_combinators_init: bool,
    /// Whether the `Dvd` class has been initialized (Brick P1)
    #[serde(default)]
    dvd_init: bool,
    /// Whether the `Dvd Nat` instance has been initialized (Brick P1)
    #[serde(default)]
    nat_dvd_inst_init: bool,
    /// Whether the `GetElem`/`GetElem?` classes have been initialized (Brick P1)
    #[serde(default)]
    getelem_classes_init: bool,
    /// Whether `List.get` + the `List` `GetElem`/`GetElem?` instances have been initialized (Brick 4)
    #[serde(default)]
    getelem_list_instances_init: bool,
    /// Whether the `Insert`/`Singleton` classes have been initialized (Brick P1)
    #[serde(default)]
    insert_singleton_init: bool,
    /// Whether the `Insert`/`Singleton` `List` instances have been initialized (Brick P1)
    #[serde(default)]
    list_insert_singleton_inst_init: bool,
    /// Whether ExceptT/Except/MonadExcept have been initialized (#1818 Phase 4A)
    except_t_init: bool,
    /// Whether OptionT has been initialized (#1818 Phase 4A)
    option_t_init: bool,
    /// Whether Ordering type has been initialized
    ordering_init: bool,
    /// Whether Option operations (map, bind, getD) have been initialized
    option_ops_init: bool,
    /// Whether basic Bool operations (toNat) have been initialized
    #[serde(default)]
    bool_ops_init: bool,
    /// Whether List operations (append, reverse, map) have been initialized
    list_ops_init: bool,
    /// Whether `List.mapM` has been initialized. Registered after the
    /// `Bind.bind` / `Pure.pure` monad-class constants exist (it references
    /// them), so it cannot live in `init_list_combinators` (which runs in
    /// prelude-core, before `init_monad_classes`). Track ZZ.
    list_mapm_init: bool,
    /// Whether the `ForInStep` inductive has been initialized. Required by the
    /// do-notation for-loop lowering, which emits `ForInStep.done`/`yield`.
    for_in_step_init: bool,
    /// Whether the `ForIn` type class + `ForIn.forIn` method have been
    /// initialized. The for-loop desugarer emits `@ForIn.forIn …`. Track EE.
    for_in_init: bool,
    /// Whether `List.forIn` + the `instForInList` instance have been
    /// initialized, so `for x in (xs : List _) do …` resolves its `[ForIn …]`
    /// argument. Track EE.
    list_for_in_inst_init: bool,
    /// Whether Nat comparison operations have been initialized
    nat_cmp_init: bool,
    /// Whether Inhabited typeclass has been initialized
    inhabited_init: bool,
    /// Whether BEq typeclass has been initialized
    beq_init: bool,
    /// Whether Nat min/max operations have been initialized
    nat_minmax_init: bool,
    /// Whether the Min/Max homogeneous typeclasses + surface aliases are initialized
    minmax_class_init: bool,
    /// Whether the Min Nat / Max Nat instances are initialized
    nat_minmax_inst_init: bool,
    /// Whether Ord typeclass has been initialized
    ord_init: bool,
    /// Whether DecidableEq typeclass has been initialized
    decidable_eq_init: bool,
    /// Whether Hashable typeclass has been initialized
    hashable_init: bool,
    /// Whether Repr typeclass has been initialized
    repr_init: bool,
    /// Whether ToString typeclass has been initialized
    to_string_init: bool,
    /// Whether LE typeclass has been initialized
    le_init: bool,
    /// Whether LT typeclass has been initialized
    lt_init: bool,
    /// Whether GE definitions have been initialized
    ge_init: bool,
    /// Whether GT definitions have been initialized
    gt_init: bool,
    /// Whether Trans typeclass has been initialized
    trans_init: bool,
    /// Import-verification mode: suppress the kernel's hand-rolled, NON-Lean-
    /// faithful `extends`-structure prelude stubs (`Preorder`/`PartialOrder`/
    /// `LinearOrder` and the `Semigroup`→…→`Field` algebra hierarchy) and the
    /// Nat/Int order/algebra *instances* built on them.
    ///
    /// SOUNDNESS / WS17: those stubs encode FEWER constructor fields than Lean 4
    /// (e.g. `Preorder.mk` drops the trailing auto-param field
    /// `lt_iff_le_not_ge`, so the stub has 4 fields vs Lean's 5). When such a
    /// stub is pre-seeded, the `.olean` importer SKIPS the real, full-fidelity
    /// structure (it dedups by name — see `clean-olean` `load_register`), so the
    /// closure keeps the lossy 4-field `Preorder.mk` and every downstream
    /// instance that applies the genuine 5th field is (correctly) kernel-
    /// rejected and masked to an axiom. Setting this flag makes the import
    /// prelude register STRICTLY FEWER trusted constants; the real structures
    /// then enter through the checked `.olean` import / `add_inductive` replay
    /// with their full Lean field telescope. It can only make the kernel check
    /// the REAL declaration — never let an invalid term pass. The default
    /// `with_prelude()` (kernel-internal proof scaffolding) is unaffected.
    suppress_lossy_structure_stubs: bool,
    /// Cumulative-subtyping mode for `add_decl`'s type checking. When `true`,
    /// the per-call [`crate::tc::TypeChecker`] uses `is_le` (Coq/pCIC cumulativity:
    /// `Prop ≤ Set ≤ Type`, covariant product codomains) at type-ascription
    /// points instead of symmetric definitional equality.
    ///
    /// Default `false` = Lean-faithful non-cumulative checking (the only behavior
    /// for the Lean/olean lane). Set `true` ONLY when re-verifying Coq-sourced
    /// declarations, whose type theory is genuinely cumulative.
    ///
    /// SOUNDNESS: cumulativity is a sound pCIC rule; it only accepts terms
    /// well-typed under Coq's theory and is gated to the Coq lane. Tracking: #3300.
    #[serde(default)]
    cumulative: bool,
    /// Whether Preorder typeclass has been initialized
    preorder_init: bool,
    /// Whether PartialOrder typeclass has been initialized
    partial_order_init: bool,
    /// Whether LinearOrder typeclass has been initialized
    linear_order_init: bool,
    /// Whether Reflexive typeclass has been initialized
    reflexive_init: bool,
    /// Whether Antisymm typeclass has been initialized
    antisymm_init: bool,
    /// Whether Irrefl typeclass has been initialized
    irrefl_init: bool,
    /// Whether Asymm typeclass has been initialized
    asymm_init: bool,
    /// Whether Nat Preorder instance has been initialized
    nat_preorder_init: bool,
    /// Whether Nat PartialOrder instance has been initialized
    nat_partial_order_init: bool,
    /// Whether Nat LinearOrder instance has been initialized
    nat_linear_order_init: bool,
    /// Whether Nat.le Reflexive instance has been initialized
    nat_le_reflexive_init: bool,
    /// Whether Nat.lt Irrefl instance has been initialized
    nat_lt_irrefl_init: bool,
    /// Whether Nat.lt Asymm instance has been initialized
    nat_lt_asymm_init: bool,
    /// Whether Nat.lt Trans instance has been initialized
    nat_lt_trans_init: bool,
    /// Whether Nat.le Antisymm instance has been initialized
    nat_le_antisymm_init: bool,
    /// Whether Nat.le Trans instance has been initialized
    nat_le_trans_init: bool,
    /// Whether StrictOrder typeclass has been initialized
    strict_order_init: bool,
    /// Whether Nat.lt StrictOrder instance has been initialized
    nat_lt_strict_order_init: bool,
    /// Whether mixed Trans instance (lt, le) -> lt has been initialized
    nat_trans_lt_le_lt_init: bool,
    /// Whether mixed Trans instance (le, lt) -> lt has been initialized
    nat_trans_le_lt_lt_init: bool,
    /// Whether mixed Trans instance (lt, lt) -> le has been initialized
    nat_trans_lt_lt_le_init: bool,
    /// Whether Nat.lt_or_eq_of_le lemma has been initialized
    nat_lt_or_eq_of_le_init: bool,
    /// Whether Nat.lt_of_le_of_ne lemma has been initialized
    nat_lt_of_le_of_ne_init: bool,
    /// Whether Nat.not_lt and Nat.not_le lemmas have been initialized
    nat_not_lt_le_init: bool,
    /// Whether Nat.zero_lt_succ/Nat.not_succ_lt_zero/Nat.lt_succ_self have been initialized
    nat_succ_base_init: bool,
    /// Whether Nat.lt_succ_iff and Nat.succ_lt_succ lemmas have been initialized
    nat_succ_lt_init: bool,
    /// Whether Nat.lt_trichotomy lemma has been initialized
    nat_lt_trichotomy_init: bool,
    /// Whether Decidable instances for Nat.lt and Nat.le have been initialized
    nat_decidable_ord_init: bool,
    /// Whether the `≤`/`<` order stack (LE/LT/Decidable instances) for the
    /// `Nat`-wrapper widths (UInt8/16/32/64/USize/Float) has been initialized
    uint_decidable_ord_init: bool,
    /// Whether Nat min/max ordering lemmas have been initialized
    nat_minmax_lemmas_init: bool,
    /// Whether Nat addition ordering lemmas have been initialized
    nat_add_ord_init: bool,
    /// Whether Nat multiplication ordering lemmas have been initialized
    nat_mul_ord_init: bool,
    /// Whether Nat subtraction ordering lemmas have been initialized
    nat_sub_ord_init: bool,
    /// Whether Nat power ordering lemmas have been initialized
    nat_pow_ord_init: bool,
    /// Whether Int arithmetic operations have been initialized
    int_arith_init: bool,
    /// Whether Int ordering (le/lt) has been initialized
    int_ord_init: bool,
    /// Whether Int decidable ordering instances have been initialized
    int_decidable_ord_init: bool,
    /// Whether Int ordering lemmas have been initialized
    int_ord_lemmas_init: bool,
    /// Whether Int LinearOrder instance has been initialized
    int_linear_order_init: bool,
    /// Whether Int sign/abs operations have been initialized
    int_sign_abs_init: bool,
    /// Whether Int arithmetic lemmas (commutativity, associativity, etc.) have been initialized
    int_arith_lemmas_init: bool,
    /// Whether Nat arithmetic lemmas (commutativity, associativity, etc.) have been initialized
    nat_arith_lemmas_init: bool,
    /// Whether Int/Nat conversion lemmas (ofNat/toNat interaction) have been initialized
    int_nat_conv_lemmas_init: bool,
    /// Whether cast-normalization simp lemmas have been initialized (#2516)
    cast_simp_lemmas_init: bool,
    /// Whether Zero typeclass has been initialized
    zero_init: bool,
    /// Whether One typeclass has been initialized
    one_init: bool,
    /// Whether Add typeclass has been initialized
    add_init: bool,
    /// Whether Mul typeclass has been initialized
    mul_init: bool,
    /// Whether Neg typeclass has been initialized
    neg_init: bool,
    /// Whether Sub typeclass has been initialized
    sub_init: bool,
    /// Whether Nat has Zero instance
    nat_zero_inst_init: bool,
    /// Whether Nat has One instance
    nat_one_inst_init: bool,
    /// Whether Nat has Add instance
    nat_add_inst_init: bool,
    /// Whether Nat has Mul instance
    nat_mul_inst_init: bool,
    /// Whether Nat has Sub instance
    nat_sub_inst_init: bool,
    /// Whether Int has Zero instance
    int_zero_inst_init: bool,
    /// Whether Int has One instance
    int_one_inst_init: bool,
    /// Whether Int has Add instance
    int_add_inst_init: bool,
    /// Whether Int has Mul instance
    int_mul_inst_init: bool,
    /// Whether Int has Neg instance
    int_neg_inst_init: bool,
    /// Whether Int has Sub instance
    int_sub_inst_init: bool,
    /// Whether HAdd heterogeneous typeclass has been initialized
    hadd_init: bool,
    /// Whether HSub heterogeneous typeclass has been initialized
    hsub_init: bool,
    /// Whether HMul heterogeneous typeclass has been initialized
    hmul_init: bool,
    /// Whether HDiv heterogeneous typeclass has been initialized
    hdiv_init: bool,
    /// Whether Div typeclass has been initialized
    div_init: bool,
    /// Whether HMod heterogeneous typeclass has been initialized
    hmod_init: bool,
    /// Whether Mod typeclass has been initialized
    mod_init: bool,
    /// Whether HPow heterogeneous typeclass has been initialized
    hpow_init: bool,
    /// Whether Pow typeclass has been initialized
    pow_init: bool,
    /// Whether Nat has HAdd instance
    nat_hadd_inst_init: bool,
    /// Whether Int has HAdd instance
    int_hadd_inst_init: bool,
    /// Whether Nat has HSub instance
    nat_hsub_inst_init: bool,
    /// Whether Int has HSub instance
    int_hsub_inst_init: bool,
    /// Whether Nat has HMul instance
    nat_hmul_inst_init: bool,
    /// Whether Int has HMul instance
    int_hmul_inst_init: bool,
    /// Whether the `Float.add`/`sub`/`mul`/`div`/`neg`/`round` Opaque op
    /// declarations have been registered (Track EF)
    float_arith_ops_init: bool,
    /// Whether Float has HAdd instance (Track EF)
    float_hadd_inst_init: bool,
    /// Whether Float has HSub instance (Track EF)
    float_hsub_inst_init: bool,
    /// Whether Float has HMul instance (Track EF)
    float_hmul_inst_init: bool,
    /// Whether Float has HDiv instance (Track EF)
    float_hdiv_inst_init: bool,
    /// Whether Float has Neg instance (Track EF)
    float_neg_inst_init: bool,
    /// Whether HAnd heterogeneous typeclass has been initialized
    hand_init: bool,
    /// Whether HOr heterogeneous typeclass has been initialized
    hor_init: bool,
    /// Whether HXor heterogeneous typeclass has been initialized
    hxor_init: bool,
    /// Whether HShiftLeft heterogeneous typeclass has been initialized
    hshiftleft_init: bool,
    /// Whether HShiftRight heterogeneous typeclass has been initialized
    hshiftright_init: bool,
    /// Whether HAppend heterogeneous typeclass has been initialized
    happend_init: bool,
    /// Whether String has HAppend instance
    string_happend_inst_init: bool,
    /// Whether List has the parametric HAppend instance
    list_happend_inst_init: bool,
    /// Whether Nat has HAnd instance
    nat_hand_inst_init: bool,
    /// Whether Nat has HOr instance
    nat_hor_inst_init: bool,
    /// Whether Nat has HXor instance
    nat_hxor_inst_init: bool,
    /// Whether Nat has HShiftLeft instance
    nat_hshiftleft_inst_init: bool,
    /// Whether Nat has HShiftRight instance
    nat_hshiftright_inst_init: bool,
    /// Whether Semigroup typeclass has been initialized
    semigroup_init: bool,
    /// Whether AddSemigroup typeclass has been initialized
    add_semigroup_init: bool,
    /// Whether Monoid typeclass has been initialized
    monoid_init: bool,
    /// Whether AddMonoid typeclass has been initialized
    add_monoid_init: bool,
    /// Whether Nat has AddSemigroup instance
    nat_add_semigroup_inst_init: bool,
    /// Whether Int has AddSemigroup instance
    int_add_semigroup_inst_init: bool,
    /// Whether Nat has AddMonoid instance
    nat_add_monoid_inst_init: bool,
    /// Whether Int has AddMonoid instance
    int_add_monoid_inst_init: bool,
    /// Whether Group typeclass has been initialized
    group_init: bool,
    /// Whether AddGroup typeclass has been initialized
    add_group_init: bool,
    /// Whether Int has AddGroup instance
    int_add_group_inst_init: bool,
    /// Whether CommSemigroup typeclass has been initialized
    comm_semigroup_init: bool,
    /// Whether AddCommSemigroup typeclass has been initialized
    add_comm_semigroup_init: bool,
    /// Whether CommMonoid typeclass has been initialized
    comm_monoid_init: bool,
    /// Whether AddCommMonoid typeclass has been initialized
    add_comm_monoid_init: bool,
    /// Whether CommGroup typeclass has been initialized
    comm_group_init: bool,
    /// Whether AddCommGroup typeclass has been initialized
    add_comm_group_init: bool,
    /// Whether Nat has AddCommSemigroup instance
    nat_add_comm_semigroup_inst_init: bool,
    /// Whether Int has AddCommSemigroup instance
    int_add_comm_semigroup_inst_init: bool,
    /// Whether Nat has AddCommMonoid instance
    nat_add_comm_monoid_inst_init: bool,
    /// Whether Int has AddCommMonoid instance
    int_add_comm_monoid_inst_init: bool,
    /// Whether Int has AddCommGroup instance
    int_add_comm_group_inst_init: bool,
    /// Whether Semiring typeclass has been initialized
    semiring_init: bool,
    /// Whether Ring typeclass has been initialized
    ring_init: bool,
    /// Whether CommSemiring typeclass has been initialized
    comm_semiring_init: bool,
    /// Whether CommRing typeclass has been initialized
    comm_ring_init: bool,
    /// Whether Nat has Semiring instance
    nat_semiring_inst_init: bool,
    /// Whether Int has Semiring instance
    int_semiring_inst_init: bool,
    /// Whether Int has Ring instance
    int_ring_inst_init: bool,
    /// Whether Nat has CommSemiring instance
    nat_comm_semiring_inst_init: bool,
    /// Whether Int has CommSemiring instance
    int_comm_semiring_inst_init: bool,
    /// Whether Int has CommRing instance
    int_comm_ring_inst_init: bool,
    /// Whether DivisionRing typeclass has been initialized
    division_ring_init: bool,
    /// Whether Field typeclass has been initialized
    field_init: bool,
    /// Whether IntegralDomain typeclass has been initialized
    integral_domain_init: bool,
    /// Whether Int has IntegralDomain instance
    int_integral_domain_inst_init: bool,
    /// Whether Nat has IntegralDomain instance
    nat_integral_domain_inst_init: bool,
    /// Whether Nontrivial typeclass has been initialized
    nontrivial_init: bool,
    /// Whether Int has Nontrivial instance
    int_nontrivial_inst_init: bool,
    /// Whether WellFounded has been initialized
    well_founded_init: bool,
    /// Whether WF recursion support types have been initialized
    wf_recursion_support_init: bool,
    /// Whether EuclideanDomain typeclass has been initialized
    euclidean_domain_init: bool,
    /// Whether Int has EuclideanDomain instance
    int_euclidean_domain_inst_init: bool,
    /// Whether Int GCD/LCM axioms have been initialized
    int_gcd_init: bool,
    /// Whether Nat GCD/LCM axioms have been initialized
    nat_gcd_init: bool,
    /// Whether GcdMonoid typeclass has been initialized
    gcd_monoid_init: bool,
    /// Whether Nat has GcdMonoid instance
    nat_gcd_monoid_inst_init: bool,
    /// Whether Nat Prime has been initialized
    nat_prime_init: bool,
    /// Whether Irreducible predicate has been initialized
    irreducible_init: bool,
    /// Whether Associated relation has been initialized
    associated_init: bool,
    /// Whether UniqueFactorizationMonoid typeclass has been initialized
    ufm_init: bool,
    /// Whether Nat UFM instance has been initialized
    nat_ufm_inst_init: bool,
    /// Whether generic Prime typeclass has been initialized
    prime_init: bool,
    /// Whether IsPrincipalIdealRing typeclass has been initialized
    is_principal_ideal_ring_init: bool,
    /// Whether Polynomial type has been initialized
    polynomial_init: bool,
    /// Whether Rat type has been initialized
    rat_init: bool,
    /// Whether Rat arithmetic (neg/add/sub/mul/inv/div) has been initialized
    rat_arith_init: bool,
    /// Whether Rat has Field instance
    rat_field_inst_init: bool,
    /// Whether Rat normalization has been initialized
    rat_normalize_init: bool,
    /// Whether Rat ordering (le/lt) has been initialized
    rat_ord_init: bool,
    /// Whether Rat LinearOrder instance has been initialized
    rat_linear_order_init: bool,
    /// Whether LinearOrderedField typeclass has been initialized
    linear_ordered_field_init: bool,
    /// Whether Rat ordered field axioms (add_le_add_left, mul_pos, zero_lt_one) have been initialized
    rat_ordered_field_axioms_init: bool,
    /// Whether Rat LinearOrderedField instance has been initialized
    rat_linear_ordered_field_inst_init: bool,
    /// Whether Rat Decidable ordering instances have been initialized
    rat_decidable_ord_init: bool,
    /// Whether Rat min/max functions have been initialized
    // Only written/read by the `math-overlays`-gated `init_rat_minmax` /
    // `has_rat_minmax`; unused in the default trusted-kernel build.
    #[cfg_attr(not(any(test, feature = "math-overlays")), allow(dead_code))]
    rat_minmax_init: bool,
    /// Whether Rat absolute value function has been initialized
    rat_abs_init: bool,
    /// Whether Int min/max functions have been initialized
    int_minmax_init: bool,
    /// Whether Int.abs properties have been initialized
    int_abs_props_init: bool,
    /// Whether Nat.absDiff function and properties have been initialized
    nat_abs_diff_init: bool,
    /// Whether Rat.dist (distance/metric) function and properties have been initialized
    rat_dist_init: bool,
    /// Whether Int.dist (distance/metric) function and properties have been initialized
    int_dist_init: bool,
    /// Whether Nat.dist (distance/metric) function and properties have been initialized
    nat_dist_init: bool,
    /// Whether MetricSpace typeclass has been initialized
    metric_space_init: bool,
    /// Whether Nat MetricSpace instance has been initialized
    nat_metric_space_init: bool,
    /// Whether Int MetricSpace instance has been initialized
    int_metric_space_init: bool,
    /// Whether Rat MetricSpace instance has been initialized
    rat_metric_space_init: bool,
    /// Whether Metric.ball/closedBall constructions have been initialized
    metric_ball_init: bool,
    /// Whether Metric.Continuous has been initialized
    metric_continuous_init: bool,
    /// Whether Metric.Lipschitz has been initialized
    metric_lipschitz_init: bool,
    /// Whether Metric.UniformContinuous has been initialized
    metric_uniform_continuous_init: bool,
    /// Whether Metric.CauchySeq has been initialized
    metric_cauchy_seq_init: bool,
    /// Whether Metric.Complete (complete metric spaces) has been initialized
    metric_complete_init: bool,
    /// Whether Metric.Bounded (bounded metric spaces) has been initialized
    metric_bounded_init: bool,
    /// Whether Metric.Compact (compact metric spaces) has been initialized
    metric_compact_init: bool,
    /// Whether Metric.TotallyBounded (totally bounded/precompact metric spaces) has been initialized
    metric_totally_bounded_init: bool,
    /// Whether Metric.Separable (separable metric spaces with countable dense subsets) has been initialized
    metric_separable_init: bool,
    /// Whether TopologicalSpace typeclass has been initialized
    topological_space_init: bool,
    /// Whether Topology.Continuous (continuous maps between topological spaces) has been initialized
    topology_continuous_init: bool,
    /// Whether Topology.Connected (connected topological spaces) has been initialized
    topology_connected_init: bool,
    /// Whether Topology.Compact (compact topological spaces) has been initialized
    topology_compact_init: bool,
    /// Whether Topology.Hausdorff (T2 separation axiom) has been initialized
    topology_hausdorff_init: bool,
    /// Whether Topology.Homeomorphism (homeomorphic spaces and equivalences) has been initialized
    topology_homeomorphism_init: bool,
    /// Whether Topology.LocallyCompact (locally compact spaces) has been initialized
    topology_locally_compact_init: bool,
    /// Whether Topology.PathConnected (path-connected spaces) has been initialized
    topology_path_connected_init: bool,
    /// Whether Topology.SimplyConnected (simply connected spaces) has been initialized
    topology_simply_connected_init: bool,
    /// Whether Topology.Contractible (contractible spaces) has been initialized
    topology_contractible_init: bool,
    /// Whether Topology.CoveringSpace (covering space theory) has been initialized
    topology_covering_space_init: bool,
    /// Whether Topology.FundamentalGroup (fundamental group structure) has been initialized
    topology_fundamental_group_init: bool,
    /// Whether Topology.HomotopyEquivalence (homotopy equivalence) has been initialized
    topology_homotopy_equivalence_init: bool,
    /// Whether Topology.Retract (retracts and deformation retracts) has been initialized
    topology_retract_init: bool,
    /// Whether Topology.FiberBundle (fiber bundle theory) has been initialized
    topology_fiber_bundle_init: bool,
    /// Whether Topology.Quotient (quotient topology) has been initialized
    topology_quotient_init: bool,
    /// Whether Topology.Subspace (subspace topology) has been initialized
    topology_subspace_init: bool,
    /// Whether Topology.Product (product topology) has been initialized
    topology_product_init: bool,
    /// Whether Topology.HigherHomotopy (higher homotopy groups πₙ) has been initialized
    topology_higher_homotopy_init: bool,
    /// Whether Topology.Suspension (suspension and cone) has been initialized
    topology_suspension_init: bool,
    /// Whether Topology.VectorBundle (vector bundle theory) has been initialized
    topology_vector_bundle_init: bool,
    /// Whether Topology.CoproductTopology (disjoint union topology) has been initialized
    topology_coproduct_init: bool,
    /// Whether Topology.CW (CW complex theory) has been initialized
    topology_cw_init: bool,
    /// Whether Topology.SimplicialComplex (simplicial complex theory) has been initialized
    topology_simplicial_complex_init: bool,
    /// Whether Topology.Homology (singular homology theory) has been initialized
    topology_homology_init: bool,
    /// Whether Topology.DeRham (de Rham cohomology) has been initialized
    topology_derham_init: bool,
    /// Whether Topology.Morse (Morse theory) has been initialized
    topology_morse_init: bool,
    /// Whether Topology.KTheory (topological K-theory) has been initialized
    topology_ktheory_init: bool,
    /// Whether Topology.Filtration (filtered objects and graded pieces) has been initialized
    topology_filtration_init: bool,
    /// Whether Topology.Spectral (spectral sequences) has been initialized
    topology_spectral_init: bool,
    /// Whether Topology.Sheaf (sheaf theory) has been initialized
    topology_sheaf_init: bool,
    /// Whether Topology.Scheme (scheme theory) has been initialized
    topology_scheme_init: bool,
    /// Whether Topology.Cobordism (cobordism theory) has been initialized
    topology_cobordism_init: bool,
    /// Whether Topology.Characteristic (characteristic classes) has been initialized
    topology_characteristic_init: bool,
    /// Whether Topology.Manifold (smooth manifolds) has been initialized
    topology_manifold_init: bool,
    /// Whether Topology.LieGroup (Lie groups and algebras) has been initialized
    topology_lie_group_init: bool,
    /// Whether Topology.PrincipalBundle (principal bundles) has been initialized
    topology_principal_bundle_init: bool,
    /// Whether Topology.Connection (connections on bundles) has been initialized
    topology_connection_init: bool,
    /// Whether Topology.Symplectic (symplectic manifolds) has been initialized
    topology_symplectic_init: bool,
    /// Whether Topology.Kahler (Kähler manifolds) has been initialized
    topology_kahler_init: bool,
    /// Whether Topology.Spin (spin structures) has been initialized
    topology_spin_init: bool,
    /// Whether Algebra.LinearAlgebra (linear algebra) has been initialized
    algebra_linear_init: bool,
    /// Whether NNVerification foundation axioms (Interval, AffineLayer, IBP) have been initialized
    nn_verification_init: bool,
    /// Whether Module R M typeclass has been initialized
    module_init: bool,
    /// Whether Algebra R A typeclass has been initialized
    algebra_init: bool,
    /// Whether Submodule R M type has been initialized
    submodule_init: bool,
    /// Whether Ideal R type has been initialized
    ideal_init: bool,
    /// Whether domain-related types (IsDomain, ChainComplex, etc.) have been initialized
    domain_types_init: bool,
    /// Whether FATE-X order theory stubs (WithBot, Top.top, etc.) have been initialized
    fate_x_order_stubs_init: bool,
    /// Whether CategoryTheory (category theory) has been initialized
    category_theory_init: bool,
    /// Whether HomologicalAlgebra (homological algebra) has been initialized
    homological_algebra_init: bool,
    /// Whether NumberTheory (number theory) has been initialized
    number_theory_init: bool,
    /// Whether AlgebraicGeometry (algebraic geometry) has been initialized
    algebraic_geometry_init: bool,
    /// Whether RepresentationTheory (representation theory) has been initialized
    representation_theory_init: bool,
    /// Whether MeasureTheory (measure theory and probability) has been initialized
    measure_theory_init: bool,
    /// Whether FunctionalAnalysis (Banach/Hilbert spaces, operators) has been initialized
    functional_analysis_init: bool,
    /// Whether InformationTheory (entropy, divergence, coding) has been initialized
    information_theory_init: bool,
    /// Whether DifferentialEquations (ODEs, PDEs, dynamical systems) has been initialized
    differential_equations_init: bool,
    /// Whether Combinatorics (graphs, matroids, enumeration) has been initialized
    combinatorics_init: bool,
    /// Whether Optimization (convex, variational, operations research) has been initialized
    optimization_init: bool,
    /// Whether Computability (Turing machines, decidability, complexity) has been initialized
    computability_init: bool,
    /// Whether Set Theory (cardinals, ordinals, well-orderings, ZFC) has been initialized
    set_theory_init: bool,
    /// Whether basic Set type (Set α := α → Prop) has been initialized
    set_init: bool,
    /// Whether Fixed Point Theory (lfp, gfp, Knaster-Tarski, induction/coinduction) has been initialized
    fixed_point_init: bool,
    /// Whether Stochastic Processes (Markov chains, concentration inequalities) has been initialized
    stochastic_processes_init: bool,
    /// Whether Formal Logic (propositional, first-order, modal, proof theory) has been initialized
    formal_logic_init: bool,
    /// Whether Cryptography (primitives, protocols, security) has been initialized
    cryptography_init: bool,
    /// Whether Real and Complex Analysis (calculus, complex analysis) has been initialized
    real_complex_analysis_init: bool,
    /// Whether Real ordering (le/lt) has been initialized
    real_ord_init: bool,
    /// Whether Real LinearOrder instance has been initialized
    real_linear_order_init: bool,
    /// Whether Real HAdd instance (instHAddReal) has been initialized
    real_hadd_inst_init: bool,
    /// Whether Real HMul instance (instHMulReal) has been initialized
    real_hmul_inst_init: bool,
    /// Whether Real Neg instance (instNegReal) has been initialized
    real_neg_inst_init: bool,
    /// Whether Real HPow Nat instance (instHPowRealNat) has been initialized
    real_hpow_nat_inst_init: bool,
    /// Whether OfNat typeclass has been initialized
    ofnat_init: bool,
    /// Whether OfNat Nat instance (instOfNatNat) has been initialized
    ofnat_nat_inst_init: bool,
    /// Whether OfNat Real instance (instOfNatReal) has been initialized
    ofnat_real_inst_init: bool,
    /// Whether OfNat UInt8 instance has been initialized
    ofnat_uint8_inst_init: bool,
    /// Whether OfNat UInt16 instance has been initialized
    ofnat_uint16_inst_init: bool,
    /// Whether OfNat UInt32 instance has been initialized
    ofnat_uint32_inst_init: bool,
    /// Whether OfNat UInt64 instance has been initialized
    ofnat_uint64_inst_init: bool,
    /// Whether USize type has been initialized
    usize_init: bool,
    /// Whether OfNat USize instance has been initialized
    ofnat_usize_inst_init: bool,
    /// Whether Causal Inference (SCMs, do-calculus, identifiability, fairness) has been initialized
    causal_inference_init: bool,
    /// Whether Differential Privacy (ε-DP, (ε,δ)-DP, mechanisms, composition) has been initialized
    differential_privacy_init: bool,
    /// Whether Graph Theory (graphs, algorithms, properties) has been initialized
    graph_theory_init: bool,
    /// Whether Computational Geometry (predicates, hulls, tessellations, collision) has been initialized
    computational_geometry_init: bool,
    /// Whether Euclidean Geometry (EuclideanSpace, InnerProductSpace, PiLp) has been initialized
    euclidean_geometry_init: bool,
    /// Whether Euclidean angle functions (angle, arccos, pi) have been initialized
    euclidean_angle_init: bool,
    /// Whether Concurrency Theory (process algebras, temporal logic, synchronization) has been initialized
    concurrency_theory_init: bool,
    /// Whether Type Theory (dependent types, HoTT, cubical, universes) has been initialized
    type_theory_init: bool,
    /// Whether Subgroup structure has been initialized
    subgroup_init: bool,
    /// Whether Subring structure has been initialized
    subring_init: bool,
    /// Whether Subfield structure has been initialized
    subfield_init: bool,
    /// Whether Submonoid structure has been initialized
    submonoid_init: bool,
    /// Whether Fact typeclass has been initialized
    fact_init: bool,
    /// Whether Odd predicate has been initialized
    odd_init: bool,
    /// Whether Nat.card has been initialized
    nat_card_init: bool,
    /// Whether RingHom structure has been initialized
    ring_hom_init: bool,
    /// Whether IsEmpty typeclass has been initialized
    is_empty_init: bool,
    /// Whether Finite typeclass has been initialized
    finite_init: bool,
    /// Whether ML.TensorSemantics (tensor types, NN ops, IBP soundness) has been initialized
    tensor_ml_init: bool,
    /// Whether NNVerification.C002 (LayerNorm correlation firewall for zonotopes) has been initialized
    nn_verification_c002_init: bool,
    /// Whether NNVerify.C011 (Softmax monotonicity preservation) has been initialized
    nn_verify_softmax_c011_init: bool,
    /// Whether NNVerification.C009 (CROWN exponentially tighter than IBP) axioms have been initialized
    nn_verification_c009_init: bool,
    /// Whether abstract domain theory (Galois connections, transformers, composition) has been initialized
    nn_verify_abstract_domain_init: bool,
    /// Whether abstract domain IBP instance (ibp_instance, ibp_sound_linear/relu/compose) has been initialized
    nn_verify_abstract_domain_ibp_init: bool,
    /// Whether NN verify types (NNVec, NNMat, IntervalBounds) have been initialized
    nn_verify_types_init: bool,
    /// Whether NN verify type operations (NNVec.add, NNVec.smul, NNVec.dot, NNMat.mulVec) have been initialized
    nn_verify_types_ops_init: bool,
    /// Whether foundational NN verification operations (l1_norm, width, transpose, minkowski_add, sub) have been initialized
    nn_verify_foundation_types_init: bool,
    /// Whether foundational NN verification theorems (T01, T02, T04, T05, T08, T09) have been initialized
    nn_verify_foundation_theorems_init: bool,
    /// Whether the constructive Farkas-combination theorems (farkas_scale, farkas_combine_2, farkas_combine_2_le_bound) have been initialized
    nn_verify_farkas_constructive_init: bool,
    /// Whether the general n-row Farkas list combination has been initialized
    nn_verify_farkas_list_init: bool,
    /// Whether the constructive Farkas-to-bound successor (farkasCertificateValid
    /// definition + farkas_to_interval_constructive theorem) has been initialized
    nn_verify_farkas_to_interval_constructive_init: bool,
    /// Whether Fin.sum and associated lemmas have been initialized
    fin_sum_init: bool,
    /// Whether NN verify ReLU defs and T81 (IBP ReLU soundness) have been initialized
    nn_verify_relu_init: bool,
    /// Whether NN verify proofs (entailment_transitivity) have been initialized
    nn_verify_proofs_init: bool,
    /// Whether interval arithmetic kernel proofs (T01-T20) have been initialized
    nn_verify_interval_arith_proofs_init: bool,
    /// Whether IntervalBounds containment/subset foundational lemmas (#3603)
    /// have been initialized: `interval_subset_refl`,
    /// `interval_contains_self_lower`, `interval_contains_self_upper`.
    nn_verify_interval_containment_proofs_init: bool,
    /// Whether Phase-1 `Rat` scalar interval primitives (#3615) have been initialized
    nn_verify_interval_primitives_init: bool,
    /// Whether C004 Step-1 `NNVerify.Rat.interval_*` aliases (#3615 design
    /// `2026-04-20-c004-faithful-carrier-redesign.md`) have been initialized.
    nn_verify_rat_interval_init: bool,
    /// Whether constructive `NNVerify.Rat.interval_*` monotonicity theorems
    /// (`interval_add_valid`, `interval_hull_lo_le_fst_lo`,
    /// `interval_hull_fst_hi_le_hi`) have been initialized (#3615).
    nn_verify_rat_interval_proofs_init: bool,
    /// Whether T80 (IBP linear soundness) declarations have been initialized
    nn_verify_ibp_linear_init: bool,
    /// Whether Rat field→order bridging lemmas (#3503) have been initialized
    nn_verify_rat_ordering_init: bool,
    /// Whether T82 (IBP composition — layer chaining proof) has been initialized
    nn_verify_ibp_composition_init: bool,
    /// Whether C004 (CROWN/LayerNorm degeneracy = IBP) has been initialized
    nn_verify_crown_layernorm_init: bool,
    /// Whether C030 (Orbit-CROWN symmetry quotienting) has been initialized
    nn_verify_orbit_crown_init: bool,
    /// Whether C006 (block-wise CROWN = monolithic for transformers) has been initialized
    nn_verify_blockwise_crown_init: bool,
    /// Whether C008 (IBP tightness bound with infinity norm) has been initialized
    nn_verify_ibp_tightness_init: bool,
    /// Whether T4 sub-lemmas for `ibp_width_zero` (#3490 T4, #3476) have been initialized
    nn_verify_ibp_width_zero_init: bool,
    /// Whether Tier A Rat.min_zero_zero lemma (#3551) has been initialized
    nn_verify_tier_a_rat_min_zero_init: bool,
    /// Whether Tier A Rat.le_refl_zero lemma (#3551) has been initialized
    nn_verify_tier_a_rat_le_refl_zero_init: bool,
    /// Whether Tier A Rat.zero_eq_max_zero_zero lemma (#3551) has been initialized
    nn_verify_tier_a_rat_zero_eq_max_init: bool,
    /// Whether Tier A Rat.zero_eq_min_zero_zero lemma (#3551) has been initialized
    nn_verify_tier_a_rat_zero_eq_min_init: bool,
    /// Whether Tier A Rat.max_eq_min_zero_zero lemma (#3551) has been initialized
    nn_verify_tier_a_rat_max_eq_min_init: bool,
    /// Whether Tier A Rat.min_eq_max_zero_zero lemma (#3551 Batch 2) has been initialized
    nn_verify_tier_a_rat_min_eq_max_init: bool,
    /// Whether Tier A Rat.max_zero_zero_alt lemma (#3551 Batch 2) has been initialized
    nn_verify_tier_a_rat_max_zero_zero_alt_init: bool,
    /// Whether Tier A Rat.min_zero_zero_alt lemma (#3551 Batch 2) has been initialized
    nn_verify_tier_a_rat_min_zero_zero_alt_init: bool,
    /// Whether Tier A Rat.le_refl_max_zero_zero lemma (#3551 Batch 2) has been initialized
    nn_verify_tier_a_rat_le_refl_max_zero_zero_init: bool,
    /// Whether Tier A Rat.le_refl_min_zero_zero lemma (#3551 Batch 2) has been initialized
    nn_verify_tier_a_rat_le_refl_min_zero_zero_init: bool,
    /// Whether Tier A Rat.mul_zero_zero lemma (#3551 Batch 3) has been initialized
    nn_verify_tier_a_rat_mul_zero_zero_init: bool,
    /// Whether Tier A Rat.mul_one_zero lemma (#3551 Batch 3) has been initialized
    nn_verify_tier_a_rat_mul_one_zero_init: bool,
    /// Whether Tier A Rat.mul_zero_one lemma (#3551 Batch 3) has been initialized
    nn_verify_tier_a_rat_mul_zero_one_init: bool,
    /// Whether Tier A Rat.add_neg_self_zero lemma (#3551 Batch 3) has been initialized
    nn_verify_tier_a_rat_add_neg_self_zero_init: bool,
    /// Whether Tier A Rat.add_left_neg_zero lemma (#3551 Batch 3) has been initialized
    nn_verify_tier_a_rat_add_left_neg_zero_init: bool,
    /// Whether Tier A Rat.mul_neg_zero_zero lemma (#3551 Batch 3) has been initialized
    nn_verify_tier_a_rat_mul_neg_zero_zero_init: bool,
    /// Whether Tier A Rat.neg_zero_zero lemma (#3551 zero-trio) has been initialized
    nn_verify_tier_a_rat_neg_zero_zero_init: bool,
    /// Whether Tier A Batch 3 Nat ordering primitives (#3599, Part of #3551) have been initialized
    nn_verify_tier_a_nat_ordering_init: bool,
    /// Whether top-level `Nat.*` ordering primitives have been promoted from
    /// Axiom to Theorem (#3599 Wave-16): `Nat.le_refl`, `Nat.succ_le_succ`,
    /// `Nat.succ_lt_succ`, `Nat.le_of_lt`, `Nat.zero_lt_succ`.
    nat_top_level_ordering_init: bool,
    /// Whether Tier A Batch 4 Rat.min_le_max_zero_zero lemma (#3551) has been initialized
    nn_verify_tier_a_rat_min_le_max_zero_zero_init: bool,
    /// Whether Tier A Batch 4 Rat.max_le_min_zero_zero lemma (#3551) has been initialized
    nn_verify_tier_a_rat_max_le_min_zero_zero_init: bool,
    /// Whether Tier A Batch 4 Rat.min_min_zero_zero lemma (#3551) has been initialized
    nn_verify_tier_a_rat_min_min_zero_zero_init: bool,
    /// Whether Tier A Batch 4 Rat.max_max_zero_zero lemma (#3551) has been initialized
    nn_verify_tier_a_rat_max_max_zero_zero_init: bool,
    /// Whether Tier A Batch 4 Rat.max_min_zero_zero lemma (#3551) has been initialized
    nn_verify_tier_a_rat_max_min_zero_zero_init: bool,
    /// Whether the canonical `Rat.min_le_max` general lemma (#3615 prerequisite) has been initialized
    rat_min_le_max_init: bool,
    /// Whether T71 (network_cert_sound) network proof has been initialized
    nn_verify_network_proof_init: bool,
    /// Whether McCormick bilinear relaxation envelope (NNVerify.McCormick.*) has been initialized
    nn_verify_mccormick_init: bool,
    /// Whether element-wise vector/matrix inequalities (NNVerify.vec_le, mat_le, etc.) have been initialized
    nn_verify_elementwise_init: bool,
    /// Whether certified training (differentiable IBP) declarations have been initialized
    nn_verify_certified_training_init: bool,
    /// Whether certified eval (NNVerify.concrete_input, eval_trace, soundness axioms) has been initialized
    nn_verify_certified_eval_init: bool,
    /// Whether BoolAnalysis (KKL inequality, Boolean function analysis) has been initialized
    boolean_analysis_init: bool,
    /// Re-entrancy latch for `init_boolean_analysis`: true while its single
    /// init pass is in flight. The bonami-beckner retirement (run 16) made the
    /// pass register the full `hc24_core` chain, whose registrars themselves
    /// depend on `init_boolean_analysis` (for `hcDecode`/`pm`); without the
    /// latch those dependencies would start a second full pass mid-flight.
    /// Foundations (`hcDecode`, `pm`) are registered at the START of the pass
    /// and the hc24 chain at the END, so a latched no-op re-entry always sees
    /// its prerequisites already present.
    boolean_analysis_init_in_progress: bool,
    /// Whether the Stage-1 BoolFn-redesign foundations (Fin.prod, HCPoint,
    /// hcDecode, Expect, chi) have been initialized
    boolean_analysis_foundations_init: bool,
    /// Whether the Bonami-Beckner B1 order toolkit (Rat order monotonicity /
    /// square-nonnegativity lemmas consumed by the (2,4)-hypercontractivity
    /// induction) has been initialized
    boolean_analysis_order_toolkit_init: bool,
    /// Whether the Bonami-Beckner B1b lt↔sub bridge toolkit (strict-order
    /// lifting of the B1 `≤`-monotonicity lemmas: `Rat.sub_add_cancel`,
    /// `Rat.sub_pos_of_lt`, `Rat.lt_of_sub_pos`, `Rat.mul_lt_mul_of_pos_left`)
    /// has been initialized
    boolean_analysis_order_toolkit_b1b_init: bool,
    /// Whether the Bonami-Beckner B1c mixed strict/non-strict transitivity
    /// toolkit (`Rat.lt_of_le_of_lt`, `Rat.lt_of_lt_of_le` — the predecessor's
    /// exact prerequisite for `Rat.le_of_sq_le_sq`) has been initialized
    boolean_analysis_order_toolkit_b1c_init: bool,
    /// Whether the Bonami-Beckner B1d square-root monotonicity toolkit
    /// (`Rat.sq_lt_sq_of_lt_of_nonneg`, `Rat.le_of_sq_le_sq` — the
    /// (2,4)-hypercontractivity square-root step, routed through
    /// `Classical.em`) has been initialized
    boolean_analysis_order_toolkit_b1d_init: bool,
    /// Whether the Bonami-Beckner ring-identity layer (square expansion /
    /// fourth-power even-pair identity consumed by the B5 step) has been
    /// initialized
    boolean_analysis_ring_identities_init: bool,
    /// Whether the Bonami-Beckner B5 fourth-power even-pair layer (the
    /// parallelogram law `Rat.add_sq_add_sub_sq`, en route to
    /// `(A+B)⁴+(A−B)⁴ = 2A⁴+12A²B²+2B⁴`) has been initialized
    boolean_analysis_fourth_power_init: bool,
    /// Whether the Bonami-Beckner coordinate-peel extension maps
    /// (`BoolAnalysis.extendF`/`extendT : HCPoint n → HCPoint (n+1)`) have been
    /// initialized
    boolean_analysis_peel_init: bool,
    /// Whether the `Fin.lastCases` ι-computation lemmas for the coordinate-peel
    /// extension maps (`BoolAnalysis.extendF_castSucc`/`_last` + `extendT`
    /// mirrors) have been initialized
    boolean_analysis_peel_compute_init: bool,
    /// Whether the coordinate-peel `g`/`h` parts (`BoolAnalysis.gPart`/`hPart`)
    /// and the reconstruction identity (`BoolAnalysis.peel_reconstruct`) have been
    /// initialized
    boolean_analysis_peel_parts_init: bool,
    /// Whether the noise-density point-peel lemmas
    /// (`BoolAnalysis.noiseDensityW_point_peel_{ff,ft,tf,tt}`) have been initialized
    boolean_analysis_noise_peel_init: bool,
    /// Whether the decode↔extend bridges
    /// (`BoolAnalysis.hcDecode_castP_castAdd_extendF` / `_addNat_extendT`) have
    /// been initialized
    boolean_analysis_noise_extend_bridge_init: bool,
    /// Whether Fourier Boolean hypercube analysis (Parseval, noise stability, Friedgut) has been initialized
    fourier_boolean_init: bool,
    /// Whether ResComplexity (Haken's theorem, resolution lower bounds) has been initialized
    resolution_complexity_init: bool,
    /// Whether TreeWidthRes (tree-width bounds on resolution width and size) has been initialized
    tree_width_resolution_init: bool,
    /// Whether WidthExpansion (Ben-Sasson-Wigderson width-expansion theorem) has been initialized
    width_expansion_init: bool,
    /// Whether ProofTheory (p-simulation hierarchy: Resolution < CP < Frege) has been initialized
    proof_hierarchy_init: bool,
    /// Whether CraigInterpolation (Craig interpolation, constructive extraction) has been initialized
    craig_interpolation_init: bool,
    /// Whether CuttingPlanes (CP proof system, p-simulation of resolution) has been initialized
    cutting_planes_init: bool,
    /// Whether VeriPB (certificate checker surface for PB proofs) has been initialized
    veripb_checker_init: bool,
    /// Whether AbstractInterp (Cousot & Cousot abstract interpretation framework) has been initialized
    abstract_interpretation_init: bool,
    /// Whether AbstractInterp.Framework (lattice ops, Galois, domain instances, NN transfers) has been initialized
    abstract_interpretation_framework_init: bool,
    /// Whether LabelledInterpolationMinimality (D'Silva ESOP 2010 labelled interpolation lattice) has been initialized
    labelled_interpolation_minimality_init: bool,
    /// Whether LearnedClauseMinimality (interpolation-based learned clause minimality) has been initialized
    learned_clause_minimality_init: bool,
    /// Whether GF2PolynomialCalculus (PC soundness over GF(2) for Groebner basis SAT certs) has been initialized
    gf2_polynomial_calculus_init: bool,
    /// Whether PBPigeonhole (PB proofs, PHP, exponential separation from resolution) has been initialized
    pb_pigeonhole_init: bool,
    /// Whether PBPigeonholeLengthBound (concrete PHP proof size bounds) has been initialized
    pb_pigeonhole_length_bound_init: bool,
    /// Whether float-to-rational bridge (NNVerify.FloatRational.*) has been initialized
    nn_verify_float_rational_init: bool,
    /// Whether zonotope types and compression soundness (T10-T12) have been initialized
    nn_verify_zonotope_compress_init: bool,
    /// Whether zonotope kernel proofs (T01-T08, Minkowski) have been initialized
    nn_verify_zonotope_proofs_init: bool,
    /// Whether FeasibleInterpolation (Pudlak's theorem, monotone circuits, DAG-vs-tree) has been initialized
    feasible_interpolation_init: bool,
    /// Whether ExtensionRule (extension rule soundness, ER completeness, Tseitin) has been initialized
    extension_rule_init: bool,
    /// Whether BoundedWidth (bounded-width automatizability, CDCL simulation) has been initialized
    bounded_width_automatizability_init: bool,
    /// Whether CDCLSoundness (CDCL correctness invariants: trail, 2WL, resolution, backtrack, propagation, termination) has been initialized
    cdcl_soundness_init: bool,
    /// Whether EntropyClauseQuality (entropy-based semantic clause quality for CNF search states) has been initialized
    entropy_clause_quality_init: bool,
    /// Whether ExtensionSoundness (concrete propositional syntax/semantics for the extension rule) has been initialized
    extension_rule_soundness_init: bool,
    /// Whether IsaSAT refinement (abstract CDCL_W + concrete watched-literal refinement) has been initialized
    isasat_refinement_init: bool,
    /// Whether BCPLoop (abstract/imperative BCP loop refinement with mutable watch arrays) has been initialized
    bcp_loop_refinement_init: bool,
    /// Whether VerifiedProofSearch (proof search soundness, completeness, termination) has been initialized
    verified_proof_search_init: bool,
    /// Field names for structures (single-constructor inductives)
    structure_fields: HashMap<Name, Vec<Name>>,
    /// Default values for structure fields, keyed by structure name then field
    /// name. Populated by elaboration (not the kernel itself); used by
    /// inheritance resolution to propagate parent defaults to child structs.
    /// Empty by default and not consulted by type checking.
    #[serde(default)]
    structure_field_defaults: HashMap<Name, HashMap<Name, Expr>>,
    /// Parent subobject fields of a structure declared with `extends`, keyed by
    /// structure name. Each entry is `(toParent_field_name, parent_struct_name)`
    /// in constructor order. Mirrors Lean's `StructureFieldInfo.subobject?`
    /// (`src/Lean/Structure.lean`). Populated by elaboration (structure/class
    /// declaration) — an elaborator-only metadata channel, NOT consulted by
    /// type checking. Used to flatten anonymous constructors across subobjects
    /// and to assemble/update parent subobjects in structure-literal syntax.
    #[serde(default)]
    structure_parents: HashMap<Name, Vec<(Name, Name)>>,
    /// Registered type classes (name -> class info)
    ///
    /// Populated by kernel init functions when defining type classes.
    /// The elaborator's InstanceTable is initialized from this data.
    classes: HashMap<Name, KernelClassInfo>,
    /// Instances by class name (class -> list of instances)
    ///
    /// Populated by kernel init functions when defining instances.
    /// Instances are stored in priority order (highest first).
    instances: HashMap<Name, Vec<KernelInstanceInfo>>,
    /// Reverse lookup: instance name -> true (for O(1) instance check)
    ///
    /// Populated alongside `instances` by `register_instance`.
    /// Used by `unfold_with_transparency` for `TransparencyMode::Instances`.
    instance_names: hashbrown::HashSet<Name>,
    /// Per-instance synthesization order (`InstanceEntry.synthOrder` in Lean,
    /// `Lean/Meta/Instances.lean:46-60`): the order in which the instance's
    /// Pi-telescope binders are to be synthesized during typeclass resolution,
    /// as binder indices. Populated by the `.olean` import bridge from decoded
    /// `Lean.Meta.instanceExtension` entries; instances without an entry here
    /// (hand-registered prelude lane) get a Lean-style default computed by the
    /// elaborator's resolver (out-param-driven, mirroring `computeSynthOrder`,
    /// `Lean/Meta/Instances.lean:145-229`). Kept as a side table so
    /// `KernelInstanceInfo` construction sites stay untouched.
    #[serde(default)]
    instance_synth_orders: HashMap<Name, Vec<usize>>,
    /// Registered aesop rules by phase (for tactic search) - default rule set
    aesop_rules: AesopRuleSet,
    /// Named rule sets for domain-specific tactics (e.g., Measurable, Continuous)
    /// Key is the rule set name, value is the rules in that set
    aesop_rule_sets: HashMap<Name, AesopRuleSet>,
    /// Set of declared rule set names (for validation)
    declared_aesop_rule_sets: hashbrown::HashSet<Name>,
    /// Index of rules by target head constant (for fast lookup)
    aesop_target_index: HashMap<Name, Vec<AesopRule>>,
    /// Index of rules by hypothesis type head constant
    aesop_hyps_index: HashMap<Name, Vec<AesopRule>>,
    /// Unindexed rules (checked for all goals)
    aesop_unindexed_rules: Vec<AesopRule>,

    // ========================================================================
    // Attribute Registry (#1133)
    // ========================================================================
    /// Registered simp lemmas by name
    simp_lemmas: HashMap<Name, SimpLemmaInfo>,
    /// Bumped ONLY by simp-lemma register/unregister (never by `add_decl`),
    /// so consumers that cache derived simp structures (the elaborator's
    /// per-env `SimpLemmaSet`) can key on it and survive append-only
    /// declaration growth, while any registry mutation — including a
    /// count-and-content-neutral remove/re-add cycle — forces a rebuild.
    simp_registry_revision: u64,
    /// Imported `export` aliases decoded from `Lean.aliasExtension`
    /// (`export Decidable (isTrue …)` → `isTrue ↦ Decidable.isTrue`).
    /// Resolution metadata only: an alias never introduces a constant, it
    /// only lets a SHORT name reach one the kernel already checked, so a
    /// wrong entry can at worst fail to resolve or resolve to a constant
    /// whose type then rejects the use.
    #[serde(default)]
    export_aliases: HashMap<Name, Name>,
    /// Extern bindings (declaration -> C function name)
    extern_bindings: HashMap<Name, String>,
    /// @[implemented_by] bindings (declaration -> implementing function name).
    /// When a constant `f` has `@[implemented_by g]`, the kernel can replace
    /// applications of `f` with applications of `g` during native reduction.
    /// This maps `f.name -> g.name`.
    implemented_by: HashMap<Name, Name>,
    /// Native reducer functions registered for specific constants.
    /// These provide fast-path computation rules (e.g., `Nat.decEq` via native
    /// comparison vs. recursor unfolding). The function receives WHNF'd arguments
    /// and returns `Some(result)` if reduction succeeds.
    ///
    /// Reference: Lean 4 type_checker.cpp:988-991 `reduce_native`
    #[serde(skip)]
    native_reducers: HashMap<Name, NativeReducerFn>,
    /// Export bindings (declaration -> exported C name)
    export_bindings: HashMap<Name, String>,
    /// Deprecated declarations with optional message
    deprecated: HashMap<Name, Option<String>>,
    /// Declarations with @[inline] attribute
    inline_hints: hashbrown::HashSet<Name>,
    /// Declarations with @[noinline] attribute
    noinline_hints: hashbrown::HashSet<Name>,
    /// Declarations with @[always_inline] attribute
    always_inline_hints: hashbrown::HashSet<Name>,
    /// Declarations with @[macro_inline] attribute
    #[serde(default)]
    macro_inline_hints: hashbrown::HashSet<Name>,
    /// Declarations with @[inline_if_reduce] attribute
    #[serde(default)]
    inline_if_reduce_hints: hashbrown::HashSet<Name>,
    /// Declarations with @[nospecialize] attribute
    #[serde(default)]
    nospecialize_hints: hashbrown::HashSet<Name>,
    /// Declarations with @[specialize] attribute
    specialize_hints: hashbrown::HashSet<Name>,
    /// Declarations with @[csimp] attribute
    csimp_lemmas: hashbrown::HashSet<Name>,
    /// Registered congr lemmas
    congr_lemmas: hashbrown::HashSet<Name>,
    /// Registered ext lemmas
    ext_lemmas: hashbrown::HashSet<Name>,
    /// Registered refl lemmas
    refl_lemmas: hashbrown::HashSet<Name>,
    /// Registered symm lemmas
    symm_lemmas: hashbrown::HashSet<Name>,
    /// Declarations registered as coercions via `@[coe]`
    #[serde(default)]
    coercion_decls: hashbrown::HashSet<Name>,
    /// Declarations registered as match patterns via `@[match_pattern]`
    #[serde(default)]
    match_pattern_decls: hashbrown::HashSet<Name>,
    /// Declarations registered as init functions via `@[init]`
    #[serde(default)]
    init_fn_decls: hashbrown::HashSet<Name>,
    /// Declarations registered as default instances via `@[default_instance]`
    #[serde(default)]
    default_instance_decls: hashbrown::HashSet<Name>,
    /// User-defined derive handlers registered via `@[derive_handler]`,
    /// keyed by the class they derive.
    #[serde(default)]
    derive_handlers: HashMap<Name, Vec<Name>>,
    /// Declarations marked `private` (not exported outside module)
    private_decls: hashbrown::HashSet<Name>,
    /// Declarations marked `protected` (only accessible via fully qualified name)
    protected_decls: hashbrown::HashSet<Name>,
    /// Declarations marked `noncomputable` (no code generation)
    noncomputable_decls: hashbrown::HashSet<Name>,
    /// Declarations marked `partial` (non-terminating allowed)
    #[serde(default)]
    partial_decls: hashbrown::HashSet<Name>,
    /// Declarations marked `unsafe`
    #[serde(default)]
    unsafe_decls: hashbrown::HashSet<Name>,
    /// Parameter names for constants (binder names from declarations).
    /// Used by the elaborator for named argument matching (#1230).
    #[serde(default)]
    param_names: HashMap<Name, Vec<String>>,
    /// Binder kinds parallel to `param_names` (same key, same order/length;
    /// B01, GAP_SWEEP_2026-07-09). Lean-faithful named-argument binding needs
    /// each recorded parameter's explicitness so positional arguments fill
    /// only the remaining *explicit* binders (Lean `Lean/Elab/App.lean`,
    /// `ElabAppArgs`). Entries registered through the names-only legacy path
    /// have no row here; consumers must then treat every slot as explicit
    /// (the pre-B01 behavior).
    #[serde(default)]
    param_binder_infos: HashMap<Name, Vec<BinderInfo>>,
    /// Monotonically increasing counter, bumped on every mutation (#1279).
    /// Used by `TypeChecker::compute_env_hash` for cache invalidation.
    /// Default is 0; never wraps in practice (u64 overflow at ~584 years at 1GHz).
    #[serde(default)]
    generation: u64,
    #[serde(default)]
    options: HashMap<String, Option<String>>,
    /// Names installed as PROVISIONAL HEADERS by header-first elaboration
    /// (Trust I1): a signature staged so that later declarations resolve names
    /// independently of source order. A header is a name and a type with no
    /// value, which is indistinguishable downstream from an axiom the user
    /// never wrote — so an environment holding one is NOT authoritative.
    ///
    /// This set is the kernel-side marker for that state. Its only job is to
    /// make the non-authoritative environment *say so* if it ever escapes the
    /// batch that built it: [`Environment::audit_certification`] reports
    /// `CertificationIssue::Staged` for any reachable member, which is a
    /// blocking issue, so a proof resting on a staged header can never be
    /// certified. It is deliberately serialized (with `#[serde(default)]` for
    /// backward compatibility) so a round-trip cannot launder the marker away.
    ///
    /// The structural firewall is separate and stronger: header-first
    /// elaboration keeps two environments and never installs a header in the
    /// one declarations are registered into, so `add_decl` refuses a term
    /// naming a header by unknown-constant. This set is defence in depth.
    #[serde(default)]
    staged_headers: hashbrown::HashSet<Name>,
}

impl Environment {
    /// Convert usize to u32 with overflow checking.
    /// Returns u32::MAX if the value overflows (safe fallback for indices).
    /// In practice, no type will have more than 2^32 constructors/fields.
    #[inline]
    fn usize_to_u32(value: usize) -> u32 {
        u32::try_from(value).unwrap_or(u32::MAX)
    }

    /// Create a new empty environment in Constructive mode (default)
    /// REQUIRES: none (pure constructor)
    /// ENSURES: Returns a fresh Environment with Sorry, trustedArith, trustedAy initialized
    pub fn new() -> Self {
        let mut env = Self {
            macro_inline_hints: hashbrown::HashSet::default(),
            inline_if_reduce_hints: hashbrown::HashSet::default(),
            nospecialize_hints: hashbrown::HashSet::default(),
            ..Self::default()
        };
        env.init_sorry()
            .expect("init_sorry should be infallible in a fresh environment");
        env.init_trusted_arith()
            .expect("init_trusted_arith should be infallible in a fresh environment");
        env.init_trusted_ay()
            .expect("init_trusted_ay should be infallible in a fresh environment");
        // Register built-in native reducers unconditionally.
        // These are pure function registrations with no dependency on declarations.
        // Critical for .olean import: Environment::default() + load_module_with_deps
        // bypasses with_prelude(), so native reducers must be available from new().
        env.ensure_native_reducers();
        env
    }

    /// Ensure all built-in native reducers are registered.
    ///
    /// Idempotent: safe to call multiple times (HashMap insert overwrites).
    /// Call this from any environment construction path that may bypass
    /// `with_prelude()` (e.g., .olean import using `Environment::default()`).
    ///
    /// Part of #3210.
    pub fn ensure_native_reducers(&mut self) {
        self.init_native_reducers();
        self.init_arith_native_reducers();
        self.init_bool_ext_native_reducers();
        self.init_uint_native_reducers();
        self.init_uint_conv_native_reducers();
        self.init_platform_native_reducers();
        self.init_string_native_reducers();
        self.init_string_ext_native_reducers();
        self.init_char_native_reducers();
        self.init_float_native_reducers();
        self.init_float_to_rat_native_reducers();
        self.init_name_native_reducers();
        self.init_decidable_native_reducers();
        self.init_decidable_ext_native_reducers();
        self.init_decidable_alias_native_reducers();
        self.init_int_native_reducers();
        self.init_sint_native_reducers();
        self.init_bitvec_native_reducers();
        self.init_beq_shortcircuit_native_reducers();
        self.init_hetero_shortcircuit_native_reducers();
        self.init_init_native_reducers();
    }

    /// Create a new environment with Lean 4 prelude types initialized.
    ///
    /// This includes core types that Lean 4 files expect to be available:
    /// - Eq (equality type and refl/symm/trans)
    /// - Bool (true/false)
    /// - Nat (zero/succ, arithmetic)
    /// - List (nil/cons)
    /// - Char, String (literals, basic text)
    /// - Unit
    /// - Empty
    /// - Option
    /// - And, Or, Not, Iff (logic)
    /// - True, False (propositions)
    ///
    /// Use this for checking Lean files that don't explicitly import modules.
    /// For minimal environments, use `Environment::new()` instead.
    ///
    /// # Panics
    ///
    /// Panics if any init method fails. Use [`try_with_prelude`](Self::try_with_prelude)
    /// for structured error reporting.
    pub fn with_prelude() -> Self {
        Self::try_with_prelude().expect("prelude initialization failed")
    }

    /// Create a new environment with Lean 4 prelude types initialized,
    /// returning a structured error on failure.
    ///
    /// Identical to [`with_prelude`](Self::with_prelude) but propagates errors
    /// instead of panicking. Useful during active declaration migration (#1444)
    /// where init methods may fail with informative `EnvError` values.
    pub fn try_with_prelude() -> Result<Self, EnvError> {
        let mut env = Self::default();
        env.init_prelude_core()?;
        env.init_prelude_algebra()?;
        env.init_prelude_extended()?;
        Ok(env)
    }

    /// Build a prelude for `.olean` / `.mathverse` import verification that does
    /// NOT seed the kernel's hand-rolled, non-Lean-faithful `extends`-structure
    /// stubs (and the Nat/Int order & algebra instances layered on them).
    ///
    /// Identical to [`try_with_prelude`](Self::try_with_prelude) except the lossy
    /// `extends`-structure families are suppressed (see
    /// [`Self::suppress_lossy_structure_stubs`]). Use this whenever a real Lean
    /// environment is imported on top of the prelude: the genuine
    /// `Preorder`/`Semigroup`/… structures (with their FULL Lean field
    /// telescope) then register through the checked import path instead of being
    /// shadowed by a stub that drops trailing fields.
    ///
    /// # Errors
    ///
    /// Same surface as [`try_with_prelude`](Self::try_with_prelude).
    pub fn try_with_prelude_for_import() -> Result<Self, EnvError> {
        let mut env = Self {
            suppress_lossy_structure_stubs: true,
            ..Self::default()
        };
        env.init_prelude_core()?;
        env.init_prelude_algebra()?;
        env.init_prelude_extended()?;
        Ok(env)
    }

    /// Whether this environment was built with the lossy `extends`-structure
    /// prelude stubs suppressed (see [`Self::try_with_prelude_for_import`]).
    #[must_use]
    pub fn suppresses_lossy_structure_stubs(&self) -> bool {
        self.suppress_lossy_structure_stubs
    }

    /// Enable the strict monad-instance gate for the `--prelude lean4-core`
    /// check lane (Brick B07). See the field doc on
    /// [`Environment::lean4_core_strict_monads`] and
    /// `clean-elab::infer::elab_monad_materialize` for the enforcement point.
    pub fn set_lean4_core_strict_monads(&mut self, strict: bool) {
        self.lean4_core_strict_monads = strict;
    }

    /// Whether the strict monad-instance gate is enabled (Brick B07).
    #[must_use]
    pub fn lean4_core_strict_monads(&self) -> bool {
        self.lean4_core_strict_monads
    }

    /// Initialize core prelude types: logic, data types, equality.
    fn init_prelude_core(&mut self) -> Result<(), EnvError> {
        self.init_sorry()?;
        self.init_trusted_arith()?;
        self.init_trusted_ay()?;
        self.init_eq()?;
        // HEq must be initialized before the first PARAMETERIZED inductive
        // (List/Option/…): under the v4.30 heterogeneous noConfusion
        // convention every param-mentioning field equality is an HEq, so any
        // init-time proof that reduces through a parameterized
        // noConfusionType chain (e.g. ListChar.decEq) needs HEq + the
        // eq_of_heq/heq_of_eq bridge registered. Idempotent; previously ran
        // just before init_sigma. Design:
        // designs/2026-07-03-noconfusion-ctoridx-convention.md §5/N2.
        self.init_heq()?;
        self.init_true_false()?;
        self.init_and()?;
        self.init_bool()?;
        // Commutativity of the boolean binops (Bool.and_comm / or_comm / xor_comm)
        // as real axiom-free `Bool.rec` casework theorems. Referenced by trust-ir's
        // bitwise-commutativity proofs (Track Y).
        self.register_bool_comm_proofs()?;
        // Bool.and → `= true` projection bridges (Bool.and_eq_true_left/right)
        // as real axiom-free `Bool.rec` casework. Back the Trust spec-elab
        // CONJUNCTION certified monitor (§1.1): a `P && Q` clause monitor cites
        // these to split the shared `Bool.and mon_P mon_Q = true` hypothesis onto
        // each conjunct. Axiom closure empty; default lane byte-identical.
        self.register_bool_and_eq_true_bridges()?;
        self.init_unit()?;
        self.init_punit()?;
        self.init_empty()?;
        self.init_pempty()?;
        self.init_nat()?;
        self.init_list()?;
        self.init_string()?;
        self.init_option()?;
        self.init_sum()?;
        // PSum was registered but never wired into the live prelude
        // (found by the 2026-08-10 binder-fidelity audit): Lean core has
        // it (Init/Core.lean), and its init fn existed dead in data_types.rs.
        self.init_psum()?;
        self.init_fin()?;
        self.init_int()?;
        self.init_prod()?;
        // HEq is initialized early (right after init_eq above) — required
        // before ANY parameterized inductive under the v4.30 noConfusion
        // convention, which subsumes the old "before Sigma because of
        // dependent fields" ordering constraint. The call here would be a
        // no-op (idempotent).
        self.init_sigma()?;
        // PSigma (`Init/Core.lean:301`, `Σ' a : α, β a` / `(a : α) ×' β a`).
        // Registered through the same fully-checked `add_inductive` +
        // `add_decl(Definition)` path as Sigma — zero axioms. Before this call
        // the head was absent from the prelude, so every `Σ'`/`×'` surface
        // form auto-bound `PSigma` as an implicit `Sort`-typed binder and
        // failed with `TooManyArguments { func_type: Sort(u) }` (audit row
        // e09).
        self.init_psigma()?;
        self.init_iff()?;
        // Prop-level simp equalities (and_true, or_false, and_self, …) as real
        // `propext (Iff.intro …)` theorems. Before this, the family was never
        // registered as kernel `Declaration`s: `simp`'s `push_if_present` gates
        // each Prop-Eq rewrite on `env.get_const(name).is_some()` and silently
        // skipped them (NoProgress on `(p ∧ True) = p`), and explicit `:=
        // and_true` references auto-bound the identifier and failed the kernel.
        // Seeds And/Or/Iff/True/False/propext itself; axiom closure ⊆ {propext}
        // (FOUNDATIONAL), so the domain-specific axiom count is unchanged.
        self.init_prop_eq_lemmas()?;
        // Bool-level simp equalities (Bool.and_true, Bool.or_false,
        // Bool.and_self, Bool.not_not, …) as real `Bool.rec`/`Eq.refl`
        // theorems. Like the Prop-Eq family, the simp machinery's
        // `push_if_present` gates each Bool rewrite on `get_const`, so without
        // these the family was silently skipped (NoProgress on `(b && true) =
        // b`) and explicit `Bool.and_true b` references failed the kernel.
        // Seeds Bool/Eq; axiom closure empty, so the domain-specific axiom
        // count is unchanged.
        self.init_bool_simp_lemmas()?;
        // `Nat.sub`-level simp equalities (Nat.sub_zero, Nat.sub_self,
        // Nat.add_sub_cancel, Nat.zero_sub, Nat.sub_one) as real `Nat.rec`/
        // `Eq.refl` theorems. Eagerly registering Nat.sub_zero/Nat.sub_self in
        // the prelude (previously only reachable via the lazy `init_nat_sub_ord`
        // contracts table) also makes the guarded legacy `Declaration::Axiom`
        // sites in `order_arith.rs::init_nat_sub_ord` permanent no-ops. Axiom
        // closure empty; domain-specific axiom count unchanged.
        self.init_nat_sub_simp_lemmas()?;
        // `Nat.min` / `Nat.max` (reducible `Bool.rec`-over-`Nat.ble`
        // definitions) plus the constructive ordering lemmas
        // (`Nat.min_le_left`, `Nat.min_le_right`, `Nat.le_min`, `Nat.min_comm`,
        // `Nat.le_max_left`, `Nat.le_max_right`, `Nat.max_le`, `Nat.max_comm`,
        // `Nat.min_self`, `Nat.max_self`). Before this wiring these were only
        // reachable from `env/tests.rs`, never from the elaboration env that
        // `clean check` uses, so `Nat.min a b` failed to resolve (dot-notation
        // `UnknownIdent`) and omega could not discharge any min/max goal.
        // `init_nat_minmax_lemmas` is idempotent and every emitted lemma is a
        // constructive `Declaration::Theorem` with an empty domain-axiom
        // closure, so the domain-specific axiom count is unchanged.
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`): these Clean-native
        // overlays DIVERGE from their genuine Lean `.olean` definitions —
        // Clean spells `Nat.min := Bool.rec … (Nat.ble …)` and
        // `instMinNat := Min.mk Nat.min`, whereas Lean 4 ships
        // `Nat.min := @Min.min Nat instMinNat` (an abbrev for `min n m`) and
        // `instMinNat := minOfLe Nat instLENat Nat.decLe`
        // (`minOfLe.min x y := ite (LE.le x y) x y`). Registering the divergent
        // overlay first makes the import dedup filter DROP the genuine olean
        // value (it is `duplicate_filtered` because the name already exists with
        // a value), masking `Nat.instLinearOrder` (whose `min_def`/`max_def`
        // autoParam fields are `rfl`-typed proofs the kernel can only discharge
        // against the genuine `minOfLe`-spelled `Min.min instMinNat`, NOT the
        // `Bool.rec(Nat.ble)` overlay) and cascading 50+ downstream
        // `LE.le`/`LT.lt`/`Eq` instance-diamond rows in `Mathlib/Data/Nat/Defs`.
        // Suppressing the overlays here lets the genuine olean `Min`/`Max`
        // classes, `Nat.min`/`Nat.max`, `instMinNat`/`instMaxNat` and the
        // min/max lemmas flow through the normal CHECKED `add_decl` import path —
        // so the kernel verifies the real values and the diamond converges.
        // SOUNDNESS-NEUTRAL: this only WITHHOLDS Clean-native definitions in the
        // import-only prelude; every constant the import then carries is the
        // genuine olean value, re-checked by the unmodified kernel.
        if !self.suppress_lossy_structure_stubs {
            self.init_nat_minmax_lemmas()?;
            // The `Min` / `Max` homogeneous typeclasses (`class Min (α) where
            // min : α → α → α`), their reducible projection methods (`Min.min` /
            // `Max.max`), the lowercase surface aliases (`min` / `max`), and the
            // `Min Nat` / `Max Nat` instances backed by `Nat.min` / `Nat.max`.
            // Before this wiring, surface `min a b` / `max a b` (a bare lowercase
            // identifier) resolved to no environment constant, so the elaborator
            // over-applied it (`TooManyArguments`). `@Min.min Nat instMinNat a b`
            // is definitionally `Nat.min a b`, so omega's min/max recognizer can
            // peel the projection head back to the bare op. Every emitted
            // declaration is an inductive / reducible `Definition` (no `Axiom`),
            // so the domain-specific axiom count is unchanged. Both inits are
            // idempotent.
            self.init_minmax_class()?;
            self.init_nat_minmax_inst()?;
        }
        self.init_inhabited()?;
        self.init_beq()?;
        // `List.contains` (core Lean-4 `BEq`-based membership test) is registered
        // by `init_beq_list` at the tail of `init_beq` just above (the SINGLE
        // registrar — see `init_list_contains`'s doc); this call is the
        // standalone-caller dependency wrapper and a no-op here.
        //
        // Gated on the non-import lane: in import-verification mode
        // `init_beq_list` withholds the hand-rolled `List` stubs — the genuine
        // Lean `List.contains` registers through the checked `.olean` import path
        // instead. Same suppression discipline as the `init_multiset`/
        // `init_finset` stubs below. SOUNDNESS: suppression only ever lets the
        // genuine, fully kernel-checked Lean `List.contains` import in the
        // stub's place; nothing here touches `is_def_eq`/`whnf` or acceptance.
        if !self.suppress_lossy_structure_stubs {
            self.init_list_contains()?;
        }
        // Ord typeclass (`class Ord (α : Type u) where compare : α → α → Ordering`)
        // + `instOrdNat`/`instOrdBool`/`instOrdOrdering`. `init_ord` (order_ord.rs)
        // was complete but never wired, so `deriving Ord` failed its kernel re-check
        // with "Unknown constant: Ord". The class + `Ord.compare` projection register
        // Lean 4's EXACT signature (Ordering-valued `compare`), so they are
        // import-faithful and wired unconditionally alongside `init_beq`; the
        // instance cluster (`instOrdNat`/`instOrdBool`/`instOrdOrdering` and their
        // Clean-only `Nat.compare`/`Bool.compare`/`Ordering.compare` spellings)
        // diverges from v4.30's genuine olean bodies and is import-gated INSIDE
        // `init_ord` (ring 2 of the Nat core-arithmetic suppression; see
        // order_ord.rs for the SOUNDNESS note).
        self.init_ord()?;
        // Repr / ToString / Hashable typeclasses. Without these registered in
        // the prelude, an explicit `instance : Repr X` / `instance : ToString X`
        // resolves the (unknown) class name via auto-implicit to `Sort u_0` and
        // then over-applies it to `X`, raising `TooManyArguments`. Registering
        // the class inductives + structure-field tables makes the class head
        // resolve to a real environment constant. All registered terms are
        // axiom-free `Definition`s built from the class recursor (Task NN).
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`): the hand-rolled `Repr`
        // is String-valued (`reprPrec : α → Nat → String`) but Lean 4.8's genuine
        // class is Format-valued (`reprPrec : α → Nat → Std.Format`), so the stub
        // SHADOWS the real `Repr`/`Repr.reprPrec` on `.olean` import and every
        // real Mathlib `Repr` instance (e.g. `WithBot.instRepr`) fails its
        // kernel re-check with `Type mismatch: expected Std.Format, got String`.
        // The `ToString` class itself matches Lean, but its placeholder
        // instances (`instToStringNat := fun _ => ""` …) shadow Lean's genuine
        // value-bearing instances of the same names. Same lossy-stub shadowing
        // class as WS17/18/19 (see `tests_ws17_import_prelude.rs`): in import
        // mode suppress both inits so the genuine declarations register through
        // the checked import path. SOUNDNESS: suppression only ever lets the
        // genuine, fully kernel-checked Lean declarations import in the stubs'
        // place; nothing here touches `is_def_eq`/`whnf` or relaxes acceptance.
        // The proof-execution lane (default prelude, stubs NOT suppressed) is
        // byte-identical. Nothing else in the prelude references these members.
        // `Hashable` joins them for a worse reason: the stub's signature is
        // universe-unfaithful (`Type u → Type u`; Lean's class is
        // `Sort u → Sort (max 1 u)`) and its `hash` field is `Nat`-valued
        // (Lean: `UInt64`). Shadowing the genuine class poisons every
        // `[Hashable α]` binder in an imported closure with an off-by-one
        // universe (`expected Sort(u+2), got Sort(u+1)`) — PersistentHashMap,
        // HashMap/HashSet, Std.DHashMap, SMap, and all their dependents.
        if !self.suppress_lossy_structure_stubs {
            self.init_repr()?;
            self.init_to_string()?;
            self.init_hashable()?;
        }
        self.init_subtype()?;

        // The Lean 4 core quotient-by-a-setoid package (Equivalence, Setoid,
        // HasEquiv + the `≈` notation, Quotient, and the Quot companions).
        // The five quotient PRIMITIVES and their ι-rule already live in the
        // kernel (quot.rs + tc/reduction); this is the ordinary checked layer
        // above them, and it is what makes the parser's long-standing `≈`
        // desugaring resolve to a real constant.
        self.init_quotient_setoid()?;
        self.init_hadd()?;
        self.init_hsub()?;
        self.init_hmul()?;
        self.init_hdiv()?;
        self.init_hmod()?;
        self.init_nat_hadd_inst()?;
        self.init_nat_hsub_inst()?;
        self.init_nat_hmul_inst()?;
        // `/` and `%` over Nat, backed by the Nat.div / Nat.mod constants.
        // Previously HDiv/HMod were absent from the prelude, so `v / w`
        // and `v % w` failed to resolve `HDiv`/`HMod`. (Track TAC)
        self.init_nat_hdiv_inst()?;
        self.init_nat_hmod_inst()?;

        // Homogeneous `Add/Mul/Sub Nat` instances (Lean 4 core Init/Prelude:
        // `instance instAddNat : Add Nat := ⟨Nat.add⟩`, likewise Mul/Sub).
        // The heterogeneous instHAddNat chain covers `a + b`, but a direct
        // `Add.add a b` needs the homogeneous instance in the instance table
        // (`FailedToSynthesizeInstance { goal: "Add {0} Nat" }` otherwise).
        // Found absent by the 2026-08-10 prelude-fidelity audit.
        self.init_nat_add_inst()?;
        self.init_nat_mul_inst()?;
        self.init_nat_sub_inst()?;
        // `+`, `-`, `*`, `/`, `%` over Int, backed by the Int.add/sub/mul
        // (real `Int.rec`/`Nat.rec` definitions) and Int.div/Int.mod (Opaque,
        // native-reduced) constants from `init_int_arith`. Without these,
        // `a + b * c - a / b % c` over `Int` left every `HAdd/HSub/HMul/HDiv/
        // HMod Int Int Int` instance argument unfilled ("contains free
        // variables"), so trust-ir's Arith.lean integer-semantics block could
        // not elaborate. Axiom-free: each instance is a `HAdd.mk … Int.add`
        // style `Definition`, and the backing ops are Definition/Opaque, never
        // `Axiom`. (Track PP)
        self.init_int_hadd_inst()?;
        self.init_int_hsub_inst()?;
        self.init_int_hmul_inst()?;
        self.init_int_hdiv_inst()?;
        self.init_int_hmod_inst()?;
        // `-operand` (prefix `-` → `Neg.neg`) over `Int`: registers the
        // `instNegInt : Neg Int` instance (backed by `Int.neg`) AND the `Neg`
        // class registration (in init_neg). Without these, `-operand` over
        // `Int` (trust-ir's `semIntUnOp`) left its `[Neg Int]` argument unfilled
        // ("contains free variables"). Axiom-free (`Int.neg` is a Definition).
        // (Track EF)
        self.init_int_neg_inst()?;
        // `+`, `-`, `*`, `/` over `Float` and prefix `-` over `Float`: the
        // `Float.add`/`sub`/`mul`/`div`/`neg` Opaque ops (native-reduced, NOT
        // axioms) and the corresponding `HAdd`/`HSub`/`HMul`/`HDiv`/`Neg` Float
        // instances. Without these, `lhs + rhs` / `-operand` over `Float`
        // (trust-ir's `semFloatBinOp`/`semFloatUnOp`) left every instance
        // argument unfilled ("contains free variables"). (Track EF)
        self.init_float_hadd_inst()?;
        self.init_float_hsub_inst()?;
        self.init_float_hmul_inst()?;
        self.init_float_hdiv_inst()?;
        self.init_float_neg_inst()?;
        // `(b : Int) ^ (n : Nat)` — the heterogeneous power shape trust-ir's
        // Arith.lean uses (`(2 : Int) ^ width`). Backed by the axiom-free
        // `Int.pow` Nat.rec recursion. (Track PP)
        self.init_int_hpow_inst()?;
        // `^` over Nat: HPow was a class but had no Nat instance, so `m ^ n`
        // left the instance arg unfilled. (Track TAC)
        self.init_nat_hpow_inst()?;
        // Bitwise heterogeneous typeclasses (HAnd/HOr/HXor/HShiftLeft/HShiftRight)
        // with Nat instances backed by Nat.land/lor/xor/shiftLeft/shiftRight.
        // Makes `m &&& n`, `m ||| n`, `m ^^^ n`, `m <<< n`, `m >>> n` elaborate
        // for Nat (Track N: trust-ir Basic.lean bitwise section).
        self.init_nat_hand_inst()?;
        self.init_nat_hor_inst()?;
        self.init_nat_hxor_inst()?;
        self.init_nat_hshiftleft_inst()?;
        self.init_nat_hshiftright_inst()?;
        // HAppend heterogeneous typeclass backing the `++` operator, with a
        // String instance (String.append). Makes `a ++ b` on strings elaborate
        // to a closed term instead of leaking a fresh metavariable
        // ("contains free variables"). See DialectInst.qualifiedName /
        // SemError.code in trust-ir.
        self.init_string_happend_inst()?;
        // Parametric `HAppend (List α) (List α) (List α)` instance backed by the
        // axiom-free `List.append` recursor. Makes `xs ++ ys` on lists elaborate
        // to a closed term instead of leaving the instance arg an unfilled
        // metavariable ("contains free variables" — trust-ir Aggregate.lean
        // `setUnion`/`seqConcat`). (Track G)
        self.init_list_happend_inst()?;
        // Register built-in native reducers for @[implemented_by] support.
        // These provide fast-path computation for Nat.decEq, String.decEq, etc.
        self.init_native_reducers();
        // Register arithmetic native reducers for Nat.add/sub/mul/div/mod/pow/blt/
        // ble/beq and bitwise operations (land/lor/xor/shift), plus UInt32 ops.
        self.init_arith_native_reducers();
        // Register Bool.beq and Nat.gcd native reducers (unique to bool_ext;
        // all other Nat ops are in arith with BigNat support). Part of #3251.
        self.init_bool_ext_native_reducers();
        // Register UInt native reducers for UInt8/16/32/64/USize arithmetic,
        // comparisons (beq/blt/ble), and decidable equality.
        self.init_uint_native_reducers();
        // Register UInt/USize conversion reducers for ofNat, cross-width casts, and Fin.val.
        self.init_uint_conv_native_reducers();
        // Register platform-dependent native reducers (getNumBits, getIsWindows, etc.).
        self.init_platform_native_reducers();
        // Register extended String native reducers for Init/Std TC verification.
        self.init_string_native_reducers();
        self.init_string_ext_native_reducers();
        // Register Char native reducers.
        self.init_char_native_reducers();
        // Register Float native reducers for IEEE 754 arithmetic, comparison,
        // and conversion operations (Float.add, Float.mul, Float.ofScientific, etc.).
        self.init_float_native_reducers();
        // Register the exact float→rational decomposition reducers
        // (Float.toRatExact / Float.ulpExact) — real-IEEE-floats Stage A (#3185).
        self.init_float_to_rat_native_reducers();
        // Register Name native reducers for Lean.Name operations
        // (mkStr, mkNum, beq, hash, toString, append).
        self.init_name_native_reducers();
        // Register Decidable instance native reducers for instDecidableNatLt/Le,
        // instDecidableEqNat/Bool/String, and Fin.decEq.
        self.init_decidable_native_reducers();
        // Register extended Decidable native reducers for decide, Decidable combinators
        // (And, Or, Not), and Int comparison instances.
        self.init_decidable_ext_native_reducers();
        // Register instance name aliases (instDecidableEqChar, instDecidableEqUInt8, etc.)
        // that map to existing *.decEq reducer functions.
        self.init_decidable_alias_native_reducers();
        // Register Int native reducers for signed integer arithmetic
        // (add, sub, mul, div, mod, neg, natAbs, toNat, beq, blt, ble, decEq).
        self.init_int_native_reducers();
        // Register signed fixed-width int native reducers (Int8/16/32/64, ISize)
        self.init_sint_native_reducers();
        // Register BitVec and UInt/Int BitVec conversion reducers for
        // toBitVec/ofBitVec/BitVec.ofNat/BitVec.toNat and signed integer
        // toUInt/ofUInt conversions. Part of #3232.
        self.init_bitvec_native_reducers();
        // Register BEq typeclass short-circuit reducer. When BEq.beq is applied
        // with a known instance (instBEqNat, instBEqString, etc.), the reducer
        // bypasses the structure projection and delegates directly to the
        // underlying beq computation. Part of #3210.
        self.init_beq_shortcircuit_native_reducers();
        // Register heterogeneous typeclass short-circuit reducers. When HAdd.hAdd,
        // HSub.hSub, HMul.hMul, etc. are applied with known instances
        // (instHAddNatNatNat, etc.), the reducer bypasses structure projections
        // and delegates directly to the underlying computation. Part of #3210.
        self.init_hetero_shortcircuit_native_reducers();
        // Register Init-specific native reducers for ite/dite, Ord.compare,
        // compareOfLessAndEq, List.length, List.getLast!, Array.size.
        // These short-circuit common Init patterns that cause heartbeat exceeded.
        // Part of #3210.
        self.init_init_native_reducers();
        Ok(())
    }

    /// Initialize algebra prelude: classes, structures, substructures.
    fn init_prelude_algebra(&mut self) -> Result<(), EnvError> {
        self.init_zero()?;
        self.init_one()?;
        self.init_add()?;
        self.init_mul()?;
        self.init_neg()?;
        self.init_sub()?;
        // #35: register the named Nat arithmetic theorems (Nat.mul_comm,
        // Nat.left_distrib, Nat.add_zero, ...) into the prelude env so `ring`
        // and `rw [Nat.*]` resolve them. Best-effort + idempotent (see
        // data_types_nat_lemmas.rs): skips already-seeded add_comm/add_assoc and
        // never aborts prelude init on a single fragile lemma.
        let _ = self.init_nat_arith_lemmas();
        // WS17: the `Semigroup`→`Monoid`→`Group`→`Semiring`→`Ring`→`CommRing`
        // hierarchy is hand-rolled here in a NON-Lean-faithful shape (e.g.
        // `Semigroup` carries bare `op`/`assoc` fields instead of Lean's
        // `extends Mul`), so each stub collides with — and shadows — the real
        // Mathlib structure on import (the `.olean` loader dedups by name).
        // For import verification we suppress them so the genuine structures
        // register through the checked import path with their full field set.
        if !self.suppress_lossy_structure_stubs {
            self.init_semigroup()?;
            self.init_monoid()?;
            self.init_group()?;
            self.init_semiring()?;
            self.init_ring()?;
            self.init_comm_ring()?;
        }
        self.init_array()?;
        self.init_io()?;
        self.init_state_t()?;
        self.init_state_m()?;
        // WS-LEVEL: the hand-rolled `Except` family is SINGLE-universe — the
        // `Except` inductive is `Type u → Type u → Type u` (`level_params = [u]`),
        // and every dependent (`Except.bind`, `ExceptT`, `MonadExcept`, and the
        // `monad_reduce` native reducers) was written against that one-universe
        // signature. Lean 4 core's genuine `Except.{u, v}` is TWO-universe
        // (`Except (ε : Type u) (α : Type v)`). On `.olean` import the loader
        // dedups by name and this prelude stub SHADOWS the real two-universe
        // `Except`, so every Mathlib proof referencing `@Except.{u, v}` /
        // `@Except.ok.{u, v}` / `@Except.error.{u, v}` (2 level args) hits
        // `LevelCountMismatch { expected: 1, got: 2 }` and fails to kernel-verify
        // (74 such rows in the mathverse-full-v2 corpus). Because the whole family
        // is monomorphic-in-`u` and INTERNALLY consistent, the stub cannot be
        // partially replaced — suppressing just the inductive would leave
        // `Except.bind`/`ExceptT` referencing a now-two-universe `Except` with one
        // level (breaking the prelude build). Same lossy-stub shadowing class as
        // WS17/18/19: in import-verification mode suppress the ENTIRE hand-rolled
        // family so the genuine Lean `Except`/`ExceptT`/`MonadExcept` register
        // through the checked import path with their full two-universe signatures.
        // SOUNDNESS: suppression only ever lets the genuine, fully kernel-checked
        // Lean declarations import in the stubs' place; nothing here touches
        // `is_def_eq`/`whnf` or relaxes acceptance. The `monad_reduce` native
        // reducer is an OPTIMIZATION that pattern-matches on `Except.ok`/`.error`
        // and falls through to ordinary δ-reduction on a miss, so a two-universe
        // `Except` simply bypasses the fast path — never a correctness change. The
        // proof-execution lane (stub NOT suppressed) keeps the single-universe
        // `Except` family exactly as before.
        if !self.suppress_lossy_structure_stubs {
            self.init_except_t()?;
        }
        self.init_option_t()?;
        self.init_set()?;
        self.init_list_mem()?;
        self.init_list_perm()?;
        // WS19: `Multiset` is hand-rolled here as a `def` over `Quot` with the
        // relation `List.Perm` applied DIRECTLY
        // (`Multiset α := @Quot (List α) (@List.Perm α)`, see
        // `data_types_multiset.rs::init_multiset_core`), and `Multiset.cons` /
        // `Multiset.nil` / `Multiset.Mem` / `Multiset.foldl` / … are hand-spelled
        // `Quot.lift`/`Quot.mk` `Declaration::Definition`s. Real Lean 4 / Mathlib
        // `Multiset` is `def Multiset α := @Quotient (List α) (List.isSetoid α)`
        // (a `Quotient` over the `List.isSetoid` `Setoid`, whose `.r` is
        // `List.Perm`), and its ops are `Quotient.map`/`Quotient.liftOn`-spelled.
        // Though the carrier is *definitionally* the same quotient, the stub's
        // hand-spelled `Multiset.cons`/`Mem`/`foldl`/… are NOT the Mathlib terms,
        // so on `.olean` import the loader dedups by name and SHADOWS the genuine
        // Mathlib `Multiset.*` family: every Mathlib proof that pattern-matches the
        // real spelling (`Multiset.cons.proof_1`, `Multiset.countP`, `Multiset.Rel`
        // — 123 masked rows + 36 `Unknown constant: Multiset.Rel` in the WS19
        // faildump slice) then fails to kernel-verify against the stub. Same
        // lossy-stub shadowing class as WS17/WS18: in import-verification mode
        // suppress the stub so the genuine `Multiset` family registers through the
        // checked import path. SOUNDNESS: suppression only ever lets the genuine,
        // fully kernel-checked Mathlib declarations import in the stub's place;
        // nothing here touches `is_def_eq`/`whnf` or relaxes acceptance. The
        // proof-execution lane (stub NOT suppressed) keeps the `Quot`-spelled
        // `Multiset` carrier exactly as before. `init_finset` (the only other
        // prelude caller of `init_multiset`) is already co-suppressed below, so no
        // dangling references remain in the import prelude.
        if !self.suppress_lossy_structure_stubs {
            self.init_multiset()?;
        }
        // WS18: `Finset` is hand-rolled here as a `Subtype` *definition*
        // (`Finset α := { s : Multiset α // Multiset.Nodup s }`, see
        // `data_types_finset.rs::init_finset_core`), but Lean 4 / Mathlib's
        // `Finset` is a genuine two-field `structure` (`val : Multiset α`,
        // `nodup : Nodup val`). The stub collides with — and shadows — the real
        // Mathlib structure on import (the `.olean` loader dedups by name), so
        // the real `Finset` inductive (and its constructor/`rec`) never register,
        // `whnf (Finset α)` delta-unfolds to `Subtype …`, and EVERY `Finset.val`
        // / `Finset.nodup` projection — plus every downstream `Finset.*` lemma —
        // fails to kernel-verify. This is the same lossy-stub shadowing class
        // WS17 fixed for `Preorder`/`Semigroup`/…: in import-verification mode we
        // suppress the stub so the genuine `Finset` structure registers through
        // the checked import path with its full constructor + recursor.
        // SOUNDNESS: suppressing a stub only ever lets the genuine, fully
        // kernel-checked Mathlib structure import in its place; nothing here
        // touches `is_def_eq`/`whnf` or relaxes acceptance. In the proof-
        // execution lane (stub NOT suppressed) the `Finset = Subtype` carrier is
        // retained exactly as before.
        if !self.suppress_lossy_structure_stubs {
            self.init_finset()?;
        }
        // WS17: the sub-structure stubs (`Subgroup`/`Subring`/`Subfield`/
        // `Submonoid`/`RingHom`) EXTEND the lossy `Group`/`Ring`/`Field`/`Monoid`
        // stubs and build instances by applying their `.mk`. They are meaningful
        // only when those parents are seeded, and they pull the parents in
        // transitively. In import mode the real Mathlib structures come from the
        // imported closure, so the whole family is suppressed.
        if !self.suppress_lossy_structure_stubs {
            self.init_subgroup()?;
            self.init_subring()?;
            self.init_subfield()?;
            self.init_submonoid()?;
            self.init_ring_hom()?;
        }
        Ok(())
    }

    /// Initialize extended prelude: numerics, classical logic, decidability.
    fn init_prelude_extended(&mut self) -> Result<(), EnvError> {
        self.init_finite()?;
        self.init_nat_card()?;
        // WS18: `Fact` is hand-rolled here as three opaque AXIOMS
        // (`Fact : Prop → Prop`, `Fact.out`, `Fact.mk`; see
        // `algebra_substructures.rs::init_fact`), but Lean 4 / Mathlib's `Fact`
        // is a genuine single-field `class Fact (p : Prop) : Prop where out : p`
        // — a one-constructor structure with a real `.rec`. The axiom stub
        // shadows the real structure on import (dedup by name), so `Fact.rec`
        // never registers, `Fact.casesOn`/`Fact.recOn`/`Fact.noConfusion` fail
        // with "Unknown constant: Fact.rec", and `Fact.out` collides
        // ("Duplicate declaration") with the genuine projection. Same lossy-stub
        // shadowing class as WS17: in import-verification mode suppress the stub
        // so the genuine `Fact` structure registers through the checked import
        // path. SOUNDNESS: identical to the `Finset` case above — suppression
        // only lets the real kernel-checked structure import; the proof-execution
        // lane (stub NOT suppressed) keeps the `Fact` axiom carrier unchanged.
        if !self.suppress_lossy_structure_stubs {
            self.init_fact()?;
        }
        self.init_ge()?;
        // `a > b` desugars to `GT.gt a b` (parser, expr_operators.rs). Without
        // registering the `GT.gt` definition the constant is absent, the bare
        // `>` reference resolves to a placeholder whose type is not a function,
        // and any `>`-using body fails with "too many arguments" — e.g.
        // TrustIr `semICmp`'s `.Sgt`/`.Ugt` arms, which cascade to
        // `semVectorICmp`/`semICmpInst` (Track U). `init_gt` registers the
        // kernel-checked `GT.gt {α} [LT α] : α → α → Prop := LT.lt b a`,
        // mirroring the already-wired `GE.ge`. Idempotent; pulls in `init_lt`.
        self.init_gt()?;
        // Nat ordering lemmas required by linarith proof reconstruction (#2124, #2133).
        // Each init is idempotent and pulls in its own dependencies.
        //
        // WS17: `instPreorderNat`/`instPartialOrderNat`/`instLinearOrderNat`
        // (and the `init_nat_add_ord`/`init_nat_mul_ord` ordered-arith
        // instances) are built by APPLYING the lossy `Preorder.mk`/… stubs, so
        // they are meaningful only when those stubs are seeded. In import-
        // verification mode the stubs are suppressed (the real structures come
        // from the imported closure), so these stub-dependent instances are
        // suppressed too — the genuine Mathlib instances re-mint on import.
        if !self.suppress_lossy_structure_stubs {
            self.init_nat_preorder()?;
            self.init_nat_partial_order()?;
            self.init_nat_linear_order()?;
            self.init_nat_add_ord()?;
            self.init_nat_mul_ord()?;
        }
        // Nat.lt_irrefl, Nat.not_succ_lt_zero, Nat.le_of_succ_le_succ are referenced
        // by derive_false_from_contradictory_le in linarith proof reconstruction (#2133).
        self.init_nat_lt_irrefl()?;
        self.init_nat_not_lt_le()?;
        self.init_nat_succ_base()?;
        self.init_nat_succ_lt()?;
        // Nat.div2 + Nat.div2_lt_self: the recursive-measure foundation for the
        // Nat.bitwise well-founded recursion (Nat.land/Nat.lor/Nat.xor). Defines
        // `Nat.div2 : Nat → Nat` as a parity-carry pair fold and proves
        // `0 < n → Nat.div2 n < n` constructively (Track DD). Idempotent; pulls
        // in its own order-lemma dependencies.
        self.register_nat_div2_lt_self_proof()?;
        self.init_hpow()?;
        self.init_uint_types()?;
        self.init_usize()?;
        self.init_float()?;
        self.init_ofnat()?;
        self.init_ofnat_nat()?;
        self.init_ofnat_uint8()?;
        self.init_ofnat_uint16()?;
        self.init_ofnat_uint32()?;
        self.init_ofnat_uint64()?;
        self.init_ofnat_usize()?;
        // Trust: wrapping machine arithmetic + HAdd/HSub/HMul instances for
        // concrete fixed-width UInts (UInt8/16/32/64; two-language design
        // §1.1) so `x + 1 : UInt64` elaborates against the single-file
        // prelude. USize remains width-abstract and intentionally unwired. The
        // import lane withholds the UInt carrier overlay, so it must withhold
        // every arithmetic declaration and resolver entry layered on it too.
        if !self.suppress_lossy_structure_stubs {
            self.init_uint_arith()?;
        }
        self.init_classical()?;
        self.init_id()?;
        // Monad/Bind/Pure + the Id/IO/StateM/StateT cluster. In the CLOSURE
        // lane these heal (value-free axiom carriers are discharged by
        // `is_axiom_carrier_stub` and `Bind.bind`/`Pure.pure` are replaced by
        // `upgrade_axiom_stubs`), but the incremental lane has no such healing,
        // so stamping Init.Prelude itself left the stubs shadowing the genuine
        // declarations — "existing constant Monad is not checked
        // inductive-family metadata" plus the Monad.toBind/ReaderT/EStateM/
        // Lean.Macro taint cascade (~500 rows in that one module). Import mode
        // suppresses the whole cluster: its only prelude consumers
        // (`List.mapM`, the `ForIn`/`List.forIn` cluster) are already
        // suppressed below, and nothing else in the import-mode prelude
        // references these constants (verified by grep across env/). SOUNDNESS:
        // suppression only lets the genuine, fully kernel-checked Lean
        // declarations import in the stubs' place; the proof-execution lane
        // (default prelude) is byte-identical.
        if !self.suppress_lossy_structure_stubs {
            self.init_monad_classes()?;
        }
        // `List.mapM` references the `Bind.bind` / `Pure.pure` monad-class
        // constants registered by `init_monad_classes`, so it must run *after*
        // it (and after `init_list` registered the `List` inductive +
        // `List.rec`). Unblocks `argIds.mapM Sem.lookupValue` in
        // `Semantics/Control.lean` / `Borrow.lean`. Track ZZ.
        //
        // WS-LEVEL: the hand-rolled `List.mapM` is TWO-universe
        // (`level_params = [u, v]`), but Lean 4 core's genuine `List.mapM.{u, v, w}`
        // is THREE-universe (`{m : Type u → Type v} {β α : Type w}`). On `.olean`
        // import the loader dedups by name and this prelude stub SHADOWS the real
        // three-universe definition, so every Mathlib proof referencing
        // `@List.mapM.{u, v, w}` (3 level args) hits
        // `LevelCountMismatch { expected: 2, got: 3 }` and fails to kernel-verify
        // (31 such rows in the mathverse-full-v2 corpus). Same lossy-stub
        // shadowing class as WS17/18/19: in import-verification mode suppress the
        // stub so the genuine `List.mapM` registers through the checked import
        // path with its full three-universe signature. SOUNDNESS: suppression only
        // ever lets the genuine, fully kernel-checked Lean `List.mapM` import in
        // the stub's place; nothing here touches `is_def_eq`/`whnf` or relaxes
        // acceptance. Nothing else in the prelude references `List.mapM`. The
        // proof-execution lane (stub NOT suppressed) keeps the two-universe
        // `List.mapM` exactly as before.
        if !self.suppress_lossy_structure_stubs {
            self.init_list_mapm()?;
        }
        // For-loop infrastructure: the `ForInStep` inductive, the `ForIn` type
        // class + `ForIn.forIn` method, and the `List` instance. Without these,
        // `for x in (xs : List _) do …` (e.g. trust-ir `Semantics/Memory.lean`
        // `semGEP`) leaves `ForIn.forIn` / `ForInStep.yield` as `UnknownConst`.
        // Must run after `init_monad_classes` (List.forIn references Bind/Pure)
        // and `init_list` (List + List.rec). Track EE.
        //
        // Import mode suppresses the whole cluster: the stub `ForIn` declares
        // its universe params MONAD-FIRST (`{u_m1, u_m2, u_rho, u_alpha}`)
        // where genuine Lean v4.30 is rho/alpha-first with the monad LAST, and
        // its `forIn` carries a `[Monad m]` binder v4.30 no longer has. Unlike
        // Monad/Bind/Pure (value-free axiom carriers the closure loader
        // discharges/upgrades), ForIn/ForInStep are real inductives plus
        // value-bearing definitions, so duplicate-shadowing keeps the stub and
        // every universe-polymorphic `for`-loop instance in the corpus fails
        // its kernel check (PersistentArray.forIn/instForInOfMonad,
        // PersistentHashMap.instForInProdOfMonad). `List.forIn` and
        // `instForInList` do not exist in genuine v4.30 and reference the stub
        // class, so they are withheld together. SOUNDNESS: suppression only
        // lets the genuine, fully kernel-checked Lean declarations import in
        // the stubs' place; the proof-execution lane (default prelude) is
        // byte-identical, and no other prelude init references these members.
        if !self.suppress_lossy_structure_stubs {
            self.init_list_for_in_inst()?;
        }
        // Brick P1 — Lean-core class heads previously unregistered in the
        // prelude, so their surface operators (`id 5`, `<$> <&>`, the
        // `Seq`/`SeqLeft`/`SeqRight` family, `>> <|>`, `=<< >=> <=<`, `∣`,
        // `xs[i]`-family, `{a, b, c}` collection literals) fell through to
        // auto-implicit and failed `TooManyArguments { Sort(u) }` (audit:
        // docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md §1). All class heads and
        // projections are fully kernel-checked inductives/Definitions — NO new
        // axioms; the domain-specific axiom count is unchanged. Instance
        // registrations (`instFunctorOption/List`, `instSeq*Option`,
        // `instDvdNat`, `instInsertList`/`instSingletonList`) and the
        // stub-shaped `Bind` combinators are import-mode-gated inside their
        // own inits (each carries its IMPORT MODE rationale).
        self.init_fun_id()?;
        self.init_fun_comp()?;
        self.init_fun_flip()?;
        self.init_fun_const()?;
        self.init_bool_ops()?;
        self.init_functor_class()?;
        self.init_functor_instances()?;
        self.init_seq_classes()?;
        self.init_seq_option_insts()?;
        // B07: real `Pure`/`Bind` class structures + `Option` instances (real
        // `Option.some`/`Option.bind` bodies). The `List` instances are NOT
        // registered here — Lean core has no List monad instance; the builtin
        // `clean check` lane adds them explicitly (see
        // `data_monad_insts.rs` / `init_monad_list_insts`).
        self.init_pure_bind_classes()?;
        self.init_monad_option_insts()?;
        // B22: identity-monad instances (`Pure Id`/`Bind Id`) with real `fun a
        // => a` / `fun ma f => f ma` bodies. `Id`/`Id.run` are reducible defs
        // (`init_id`), so `Id.run (pure 5)` now reduces to `5` through ordinary
        // kernel delta/beta. Lean core provides `instance : Monad Id`, so this
        // is registered unconditionally (like Option, unlike the Clean-native
        // List lane); import mode withholds it inside the init.
        self.init_monad_id_insts()?;
        self.init_handthen_horelse()?;
        // Brick 3 — `Option` instances behind `>> <|>` (parser RHS unit-thunk
        // lands the operators; these give them something to resolve against).
        self.init_handthen_horelse_option_insts()?;
        self.init_bind_combinators()?;
        self.init_dvd()?;
        self.init_nat_dvd_inst()?;
        self.init_getelem_classes()?;
        // Brick 4 — `List.get` + the `List` `GetElem`/`GetElem?` instances,
        // so `xs[i]` / `xs[i]'h` / `xs[i]?` / `xs[i]!` resolve end-to-end
        // (audit rows c01-c04). Import-mode-gated inside its init.
        self.init_getelem_list_instances()?;
        self.init_insert_singleton()?;
        self.init_list_insert_singleton_inst()?;
        self.init_decidable()?;
        self.init_ite()?;
        self.init_dite()?;
        // `of_decide_eq_true` / `of_decide_eq_false` — the decide soundness +
        // completeness bridges. Back the Trust spec-elab MACHINE-INT equality
        // certified monitor (§1.1): `u64 a == b` decides via `decide (Eq a b)`
        // with the `<Carrier>.decEq` instance and cites these. Axiom-free.
        self.register_of_decide_lemmas()?;
        // Canonical `Decidable True` / `Decidable False` instances. Without
        // them `resolve_decidable(True/False)` falls back to a synthetic sorry
        // and `if True then a else b` never ι-reduces. Must run after
        // `init_decidable` + `init_true_false` (both already initialised above).
        self.init_decidable_true_false()?;
        // Simp-targeted reflexive/ite equalities: `eq_self : (a = a) = True`,
        // `ite_true : (if True then a else b) = a`, `ite_false : (if False then
        // a else b) = b`. Real kernel-checked theorems (`propext`/`Eq.refl`);
        // the `ite_*` bodies type-check only because the kernel reduces the
        // canonical-instance `ite` to its branch. Without these the simp set
        // had no reflexive-equality or ite rule, so `(n = n) = True := by simp`
        // raised NoProgress. Must run after init_ite + init_decidable_true_false
        // (instDecidableTrue/False) above. Axiom closure ⊆ {propext}
        // (FOUNDATIONAL); domain-specific axiom count unchanged.
        self.register_simp_ite_eq_lemmas()?;
        // Constructive `if_pos`/`if_neg` (axiom-free, kernel-checked): the two
        // defining reduction lemmas for `ite` under a *decided* condition with a
        // possibly-symbolic `Decidable` instance. Needed by simp's ite-condition
        // congruence path (`try_simp_ite`): when simp rewrites the condition `c`
        // to `True`/`False`, it collapses `@ite α c inst t e` to its branch via
        // `if_pos`/`if_neg`, keeping the ORIGINAL symbolic instance on the LHS so
        // the rebuilt equation is well-typed (no fresh `Decidable c'` synthesis).
        // Must run after init_ite + init_decidable + init_true_false. Axiom
        // closure: `ite`/`Decidable.rec`/`Eq.refl`/`absurd`/`False` — empty.
        self.register_ite_pos_neg_lemmas()?;
        self.init_decidable_eq()?;
        // Decidable order: registers the axiom-free `instDecidableNatLe` /
        // `instDecidableNatLt` (real `Nat.decLe`/`Nat.decLt` decision procedures)
        // plus the foundational `LE Nat`/`LT Nat` instances, so `if (a ≤ b)` /
        // `if (a < b)` / `decide` over `Nat` orderings resolve their `[LE Nat]` /
        // `[Decidable …]` arguments instead of falling back to a synthetic
        // `sorry`. Depends on `init_decidable_eq` (Decidable class) above.
        self.init_nat_decidable_ord()?;
        // Wrapper order: registers the axiom-free `instLE<T>`/`instLT<T>` and the
        // axiom-free `instDecidable<T>Le`/`instDecidable<T>Lt` (real `<T>.decLe`/
        // `<T>.decLt` decision procedures wrapping `Nat.decLe`/`Nat.decLt` on the
        // `<T>.val` projection) for every `Nat`-wrapper width
        // (UInt8/16/32/64/USize/Float), so `if ((x : UIntN) ≤ y)` /
        // `if ((x : UIntN) < y)` / `decide` resolve their `[LE <T>]` /
        // `[Decidable …]` arguments instead of defaulting to `instLENat` (a
        // `<T>` vs `Nat` type mismatch) or falling back to a synthetic `sorry`.
        // Depends on the wrapper structures (init_uint_types/usize/float) and
        // `init_nat_decidable_ord` (Nat.decLe/Nat.decLt) above.
        self.init_uint_decidable_ord()?;
        // Char.ofNatAux / Char.ofNat / Char.utf8Size — the genuine v4.30 Char
        // bodies (carrier-parity design P2). Deferred to here because they need
        // `dite` (init_dite), `instDecidableOr`/`instDecidableAnd` + `Nat.decLt`
        // (init_decidable_eq / init_nat_decidable_ord above), `Nat.le_trans`, and
        // the BitVec-backed `UInt32` (init_uint_types) — none present when
        // `init_char` seeds the Char skeleton in the core phase. Idempotent;
        // import mode + a Char-less env skip cleanly.
        self.init_char_defs()?;
        // Core `ToString` instances with REAL bodies (B04): `instToStringNat`
        // renders decimal digits via `Nat.repr` (registered here too), which
        // needs `Char.ofNat` from `init_char_defs` just above. The placeholder
        // `fun _ => ""` bodies these replace let the kernel rfl-certify wrong
        // interpolation values (GAP_SWEEP_2026-07-09, literals/p04+p05).
        self.init_to_string_instances()?;
        // Int decidable order: registers the axiom-free `instDecidableIntLe` /
        // `instDecidableIntLt` (real `Int.decLe`/`Int.decLt` decision procedures
        // — thin `Int.decNonNeg` wrappers, see `order_int_dec_le_lt_proof.rs`)
        // plus the foundational `LE Int` / `LT Int` class instances, so
        // `if ((a : Int) ≤ b)` / `if ((a : Int) < b)` / `decide` over `Int`
        // orderings resolve their `[LE Int]` / `[Decidable …]` arguments instead
        // of falling back to a synthetic `sorry` (trk-rr-intord). Depends on
        // `init_int_ord` (instLEInt/instLTInt) and `init_decidable` above.
        self.init_int_decidable_ord()?;
        // BEq (Boolean Equality) typeclass — required by `deriving BEq` on
        // inductives and structures.  Dependencies (Bool, Nat) are already
        // initialised in init_prelude_core.  Part of #3429.
        self.init_beq()?;
        // Note: Hashable IS initialized in the prelude — but only when lossy
        // structure stubs are not suppressed (see init_hashable() call next to
        // init_repr/init_to_string). The stub is universe-unfaithful
        // (`Type u → Type u` vs Lean's `Sort u → Sort (max 1 u)`) with a
        // `Nat`-valued `hash`, so import mode suppresses it and lets the
        // genuine Lean class register through the checked import path.
        // Part of #3396.

        // Well-founded recursion foundation: the `Acc` accessibility
        // inductive, its constructor `Acc.intro`, recursor `Acc.rec`, and the
        // `WellFounded` predicate + `WellFounded.fixF`/`WellFounded.fix`
        // combinators. Previously only initialized on-demand in tests; wiring
        // it into the prelude lets surface-syntax proofs reference `Acc` /
        // `WellFounded` directly (Track EE — `Nat.accNatLt`).
        self.init_well_founded()?;
        // `Nat.lt` well-foundedness witness, built by structural induction on
        // the upper bound (`Nat.rec`) plus the constructive `Nat.le_trans` /
        // `Nat.le_of_succ_le_succ` / `Nat.not_succ_le_zero` theorems above.
        // Registers `Nat.lt_wfLBound`, `Nat.accNatLt`, `Nat.lt_wf` — all
        // sorry-free `Declaration::Theorem`/`Definition`s with empty axiom
        // closures. Depends on `init_well_founded` (Acc) and the Nat ordering
        // lemmas (`init_nat_*` above).
        self.init_nat_lt_wf()?;
        // Real `Nat.testBit : Nat → Nat → Bool` Definition (parity of the
        // i-fold `Nat.div2` of n), discharging the admitted `Nat.testBit`
        // axiom from `init_nat`. Depends on `register_nat_div2_lt_self_proof`
        // (Nat.div2 / Nat.div2Par) above. Step 1 of the bitwise foundation.
        self.register_nat_testbit_def()?;
        // `Nat.eq_of_testBit_eq` — bit-extensionality of Nat (Track HH). Strong
        // induction (Acc.rec over Nat.accNatLt) over the constructive Nat.div2
        // parity foundation + Nat.testBit; registers the supporting lemma chain
        // (Nat.div2Par_zero_or_one, Nat.div2_rejoin, Nat.div2Par_inj_of_toBoolPar,
        // Nat.testBit_zero_eq_false, Nat.eq_zero_of_testBit_all_false). All
        // sorry-free `Declaration::Theorem`s with empty axiom closures.
        self.register_nat_eq_of_testbit_proof()?;
        // `Nat.bitwise` + the discharge of the admitted `Nat.land`/`Nat.lor`/
        // `Nat.xor` axioms to real reducible Definitions `Nat.bitwise and/or/xor`
        // (Track II steps 1-2). Registered in the PRELUDE — before any nn-verify
        // overlay — so the `register_nat_lor_grounded` guard
        // (`get_const("Nat.lor").is_none()`) sees the real `Nat.lor` Definition
        // and returns early instead of admitting an axiom. The bit-extension
        // theorem `Nat.testBit_bitwise` and the `Nat.testBit_and/or/xor`
        // corollaries (step 3) are registered alongside.
        self.register_nat_bitwise_def()?;
        self.register_nat_testbit_bitwise_proof()?;
        // Parseval ladder rung 4a: `Nat.testBit_lt_pow` — bit `n` of any
        // `k < 2^n` is `false`. Plain `Nat.rec` on the bit index over the
        // constructive div2/testBit foundation + `Nat.pow_two_succ` (rung 3).
        self.register_nat_testbit_lt_pow_proof()?;
        // Parseval ladder rung 4b: the bit pattern of `2^n + k` for `k < 2^n`.
        // `Nat.testBit_add_two_pow_self` (bit n is set) and
        // `Nat.testBit_add_two_pow_lo` (bits below n agree with k), plus the
        // supporting div2 helpers, all over rungs 3/4a + div2 foundation.
        self.register_nat_testbit_add_two_pow_proof()?;
        // Nat div/mod value-properties, proven constructively down to the
        // foundational axioms (empty domain-axiom closure): the euclidean
        // identity `Nat.div_add_mod` and the modulus bound `Nat.mod_lt`. These
        // self-prove the Nat sub/order helpers they need by `@Nat.rec`
        // induction over the genuine `Nat.divCore`/`Nat.modCore` structural
        // definitions (data_types_nat.rs); the supporting lemmas register under
        // the private `Nat.divmodAux.` namespace. Depends on the Nat ordering
        // lemmas seeded by the `init_nat_*` calls above. Idempotent.
        self.init_nat_div_mod_lemmas()?;
        // `USize.ofNat : Nat → USize` — the numeric-literal lowering target for
        // `(n : USize)`. A genuine kernel-checked def built from `USize.ofNatLT`
        // + `Nat.mod_lt` + the `Nat.pow_le_pow_right` positivity witness (needs
        // `Nat.mod_lt`, registered just above). Width-abstract carrier, so this
        // is the native-lane analogue of the concrete-width `UInt<w>.ofNat`;
        // olean-supplied under import mode. Idempotent, self-seeding. Fixes
        // GAP_SWEEP literals/p17 (`Unknown constant: USize.ofNat`).
        self.register_usize_of_nat()?;
        // `BitVec.ofNat : (w n : Nat) → BitVec w` + the `instOfNatBitVec` OfNat
        // instance — the numeric-literal path for `def x : BitVec 8 := 5`, which
        // elaborates through OfNat instance synthesis exactly like `Fin`. The
        // exact sibling of `register_usize_of_nat` (built from `BitVec.ofNatLT` +
        // `Nat.mod_lt` + a `Nat.pow_le_pow_right` positivity witness), but with
        // the width `w` an explicit parameter, so it is wired HERE beside its
        // sibling rather than in `init_array`: in the full prelude `init_bitvec`
        // (via `init_uint_type`) and `Nat.mod_lt` both land well before this
        // point, so the deps are present; a guard-only brick at the end of
        // `init_array` (line ~3714) would find them absent and never fire.
        // Idempotent, self-seeding. Zero axioms, `add_decl`-rechecked;
        // olean-supplied under import mode.
        self.register_bitvec_of_nat()?;
        // Universal half-ulp rounding bound, proven constructively down to the
        // foundational axioms (empty domain-axiom closure): the round primitive
        // `Nat.roundHalfEvenMod` (a reducible Definition) plus the two-sided
        // bound headlines `Nat.round_half_even_mod_bound` (general positive
        // modulus) and `Nat.ulp_universal_bound` (the symbolic V = 2^e
        // instantiation). Supporting lemmas register under `Nat.ulpRound.`.
        // Depends on `Nat.div_add_mod`/`Nat.mod_lt` (called above). Idempotent.
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`): this Clean-native
        // nn-verify primitive is built ON TOP of the orientation-divergent
        // `Nat.div_add_mod` (its constructive proofs reduce through it), which is
        // withheld in import mode (see `init_nat_div_mod_lemmas`). It has NO
        // canonical Mathlib counterpart, so it is co-suppressed: in import mode
        // there is no commuted `Nat.div_add_mod` for its proofs to build on, and
        // nothing in an imported `.olean` references it. The non-import lane
        // (`clean check`, the IEEE754 nn-verify ulp surface) is UNCHANGED.
        if !self.suppress_lossy_structure_stubs {
            self.init_nat_ulp_round_lemmas()?;
        }
        // Int ordering lemmas required by `linarith`/`omega` proof
        // reconstruction over `Int` and by surface-syntax term-mode proofs that
        // chain `Int.le` (e.g. the AY pseudo-Boolean OptimumFound gate lemma,
        // which transports a feasible incumbent below a sound structural lower
        // bound). Each registration is idempotent (guards on `get_const`) and
        // self-seeds its own constructive dependencies; all are sorry-free
        // `Declaration::Theorem`s with EMPTY domain-axiom closures
        // (`Int.le a b := Int.NonNeg (Int.sub b a)`, discharged via
        // `Int.NonNeg.add` / `Int.sub_add_sub_cancel` / `Eq.subst`), so wiring
        // them into the prelude preserves the {propext, Quot.sound,
        // Classical.choice} bedrock axiom set. Mirrors the Nat ordering-lemma
        // seeding above (`init_nat_lt_irrefl` … `init_nat_lt_wf`). Depends on
        // `init_int_ord` (instLEInt/instLTInt, pulled in transitively).
        self.register_int_le_refl_proof()?;
        self.register_int_le_trans_proof()?;
        self.register_int_le_antisymm_proof()?;
        self.register_int_add_le_add_left_proof()?;
        self.register_int_add_le_add_right_proof()?;
        // Strict-order lemmas (constructive, depend only on the `le` lemmas above
        // and `init_int_ord`'s `Int.lt a b := Int.le (a+1) b`). Wired in so PB
        // UNSAT / cutting-planes refutation proofs can express the "lower bound
        // exceeds upper bound" contradiction natively as `Int.lt hi lo`.
        self.register_int_le_of_lt_proof()?;
        self.register_int_lt_irrefl_proof()?;
        self.register_int_lt_of_le_of_lt_proof()?;
        self.register_int_lt_of_lt_of_le_proof()?;
        // Multiplicative / distributive / min lemmas + order totality, wired in
        // so the PB cutting-planes refutation ALGEBRA
        // (`proofs/clean-pb/PBCertificateAlgebra.lean`) can express and discharge
        // the scaling, division/rounding (Chvátal–Gomory) and saturation rules
        // natively. Each is an already-kernel-checked, axiom-free
        // `Declaration::Theorem` (closure ⊆ {propext, Quot.sound, Classical.choice});
        // every `register_*` is idempotent and pulls in its own dependencies.
        self.register_int_mul_zero_proof()?;
        self.register_int_mul_one_proof()?;
        self.register_int_one_mul_proof()?;
        self.register_int_left_distrib_proof()?;
        self.register_int_mul_le_mul_of_nonneg_left_proof()?;
        self.register_int_le_total_proof()?;
        self.register_int_lt_trichotomy_proof()?;
        // IMPORT MODE (`suppress_lossy_structure_stubs`): like the Nat min/max
        // case (`init_prelude_core`), Clean's `Int.min` / `Int.max` overlays
        // DIVERGE from genuine Lean 4. Clean spells
        // `Int.min a b := Bool.rec b a (Int.ble a b)` /
        // `Int.max a b := Bool.rec a b (Int.ble a b)` (and `Int.min_def` /
        // `Int.max_def` / `*_def'` proving the characterizing equations against
        // that `Bool.rec(Int.ble)` value), whereas upstream Lean 4 v4.8.0 ships
        // `Int.instMin := minOfLe Int instLEInt Int.decLe` /
        // `Int.instMax := maxOfLe Int instLEInt Int.decLe`
        // (`minOfLe.min x y := ite (LE.le x y) x y`) and its `Int.min_def` /
        // `Int.max_def` are `Max.max Int Int.instMax n m = ite (LE.le n m) m n`.
        // Registering the divergent overlay first makes the import dedup filter
        // DROP the genuine olean `Int.min_def` / `Int.max_def`: the name already
        // carries a value, so neither the inductive-discharge nor the
        // axiom→value upgrade path fires. Mathlib lemmas whose types contain the
        // genuine `Max.max Int Int.instMax … = ite …` shape (e.g.
        // `Nat.max_eq_zero_iff`, `Nat.add_eq_max_iff`) then fail to type-check
        // because the kernel cannot discharge the genuine `Int.max_def` proof
        // against the masking overlay value, masking those rows in
        // `Mathlib/Data/Nat/Defs`. The genuine `Int.instMin` / `Int.instMax`
        // (`minOfLe`/`maxOfLe`) and `Int.min_def` / `Int.max_def` all
        // kernel-verify on their own (probed via `Init.Data.Int.Order`), so
        // withholding the overlay here lets them flow through the checked import
        // path. SOUNDNESS-NEUTRAL: this only WITHHOLDS Clean-native definitions
        // in the import-only prelude; nothing is faked and no axiom is touched.
        // The non-import `try_with_prelude` (used by `clean check` and the PB
        // cutting-planes algebra) is UNCHANGED — the overlay still registers.
        if !self.suppress_lossy_structure_stubs {
            self.register_int_minmax_proofs()?;
            self.register_int_minmax_def_prime()?;
        }
        Ok(())
    }

    /// Create a new environment with a specific mode
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn with_mode(mode: crate::mode::CleanMode) -> Self {
        let mut env = Self {
            mode,
            ..Self::default()
        };
        env.init_sorry()
            .expect("init_sorry should be infallible in a fresh environment");
        env
    }

    /// Get the mode of this environment
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn mode(&self) -> crate::mode::CleanMode {
        self.mode
    }

    /// Enable/disable CUMULATIVE subtyping (Coq/pCIC) for `add_decl` type
    /// checking. Default `false` (Lean-faithful non-cumulative). Enable ONLY when
    /// re-verifying Coq-sourced declarations. See the `cumulative` field docs.
    pub fn set_cumulative(&mut self, cumulative: bool) {
        self.cumulative = cumulative;
    }

    /// Whether cumulative subtyping is enabled for `add_decl` type checking.
    #[must_use]
    pub fn is_cumulative(&self) -> bool {
        self.cumulative
    }

    /// Check if importing from another environment is mode-compatible.
    ///
    /// Returns Ok(()) if import is allowed, Err with explanation otherwise.
    /// Import compatibility follows the mode hierarchy from mode.rs:
    /// - Constructive can import: Constructive
    /// - Cubical can import: Cubical, Constructive
    /// - Classical can import: Classical, Constructive
    /// - SetTheoretic can import: SetTheoretic, Classical, Constructive
    ///
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    #[allow(dead_code)]
    pub(crate) fn check_import_compatibility(
        &self,
        source: &Environment,
    ) -> Result<(), crate::mode::ModeError> {
        if crate::mode::CleanMode::can_import(source.mode, self.mode) {
            Ok(())
        } else {
            Err(crate::mode::ModeError::IncompatibleImport {
                source_mode: source.mode,
                target: self.mode,
            })
        }
    }

    /// Create a new environment with pre-allocated capacity.
    ///
    /// This is useful when loading .olean files where the number of constants
    /// is known in advance. Pre-allocating reduces HashMap resizing overhead.
    ///
    /// `capacity` is the expected number of constants. Other map sizes are
    /// derived from empirical Init/Std ratios (~57K constants → ~6K inductives,
    /// ~12K constructors, ~8K recursors, ~3K simp lemmas, ~2K instances).
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn with_capacity(capacity: usize) -> Self {
        let mut env = Self {
            constants: HashMap::with_capacity(capacity),
            constant_origins: HashMap::with_capacity(capacity),
            declaration_verification: HashMap::with_capacity(capacity),
            codata_origins: HashMap::new(),
            codata_carriers: hashbrown::HashSet::new(),
            inductives: HashMap::with_capacity(capacity / 8),
            constructors: HashMap::with_capacity(capacity / 4),
            recursors: HashMap::with_capacity(capacity / 6),
            quotients: HashMap::with_capacity(8),
            structure_fields: HashMap::with_capacity(capacity / 16),
            structure_field_defaults: HashMap::with_capacity(capacity / 32),
            structure_parents: HashMap::with_capacity(capacity / 32),
            classes: HashMap::with_capacity(capacity / 16),
            instances: HashMap::with_capacity(capacity / 16),
            instance_names: hashbrown::HashSet::with_capacity(capacity / 8),
            simp_lemmas: HashMap::with_capacity(capacity / 16),
            simp_registry_revision: 0,
            export_aliases: HashMap::new(),
            param_names: HashMap::with_capacity(capacity / 4),
            persistent_extensions: HashMap::with_capacity(32),
            extern_bindings: HashMap::with_capacity(capacity / 32),
            implemented_by: HashMap::with_capacity(capacity / 32),
            native_reducers: HashMap::with_capacity(128),
            inline_hints: hashbrown::HashSet::with_capacity(capacity / 16),
            macro_inline_hints: hashbrown::HashSet::with_capacity(capacity / 32),
            options: HashMap::with_capacity(16),
            derive_handlers: HashMap::with_capacity(capacity / 32),
            ..Self::default()
        };
        env.init_sorry()
            .expect("init_sorry should be infallible in a fresh environment");
        env.init_trusted_arith()
            .expect("init_trusted_arith should be infallible in a fresh environment");
        env.init_trusted_ay()
            .expect("init_trusted_ay should be infallible in a fresh environment");
        env.ensure_native_reducers();
        env
    }

    /// Reserve capacity for additional constants.
    ///
    /// Call this before loading a module to avoid HashMap resizing.
    /// Sizes for subsidiary maps are derived from empirical Init/Std ratios.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn reserve_capacity(&mut self, additional: usize) {
        self.constants.reserve(additional);
        self.constant_origins.reserve(additional);
        self.declaration_verification.reserve(additional);
        self.inductives.reserve(additional / 8);
        self.constructors.reserve(additional / 4);
        self.recursors.reserve(additional / 6);
        self.structure_fields.reserve(additional / 16);
        self.classes.reserve(additional / 16);
        self.instances.reserve(additional / 16);
        self.instance_names.reserve(additional / 8);
        self.simp_lemmas.reserve(additional / 16);
        self.param_names.reserve(additional / 4);
    }

    /// Create a new environment with quotient types initialized
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    #[allow(dead_code)]
    pub(crate) fn with_quot() -> Self {
        let mut env = Self::default();
        env.init_quot();
        env
    }

    /// Initialize quotient types in this environment
    ///
    /// This adds the four quotient primitives:
    /// - Quot - the quotient type former
    /// - Quot.mk - constructor
    /// - Quot.lift - eliminator
    /// - Quot.ind - induction principle
    ///
    /// This should be called once before using quotient types.
    /// It's safe to call multiple times (subsequent calls are no-ops).
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn init_quot(&mut self) {
        if self.quot_init {
            return;
        }

        let quot_vals = init_quot_vals();
        for val in quot_vals {
            // Add to quotients map
            self.quotients.insert(val.name.clone(), val.clone());

            // Also add as constants so they can be looked up
            let const_info = ConstantInfo {
                name: val.name.clone(),
                level_params: val.level_params.clone(),
                type_: val.type_.clone(),
                value: None, // Quotient primitives have no value
                is_reducible: false,
                reducibility: Reducibility::Regular(0),
                kind: ConstantKind::Axiom,
            };
            let name = val.name;
            self.constants.insert(name.clone(), const_info);
            // Quotient primitives are installed by the kernel from canonical
            // builders, not imported through an unchecked declaration path.
            self.declaration_verification
                .insert(name, DeclarationVerification::FullKernelCheck);
        }

        self.quot_init = true;
        self.generation += 1;
    }

    /// Check if quotient types have been initialized
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    #[allow(dead_code)]
    pub(crate) fn has_quot(&self) -> bool {
        self.quot_init
    }

    /// Look up a quotient primitive by name.
    ///
    /// Returns quotient metadata including the kind (Quot, QuotMk, QuotLift, QuotInd).
    ///
    /// # Returns
    /// - `Some(&QuotVal)` if `name` is one of the quotient primitives (Quot, Quot.mk, etc.)
    /// - `None` otherwise
    ///
    /// Quotient types are initialized by calling [`Self::init_quot`].
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_quot(&self, name: &Name) -> Option<&QuotVal> {
        self.quotients.get(name)
    }

    /// Get the kind of a quotient primitive, if it exists.
    ///
    /// Convenience method that returns just the kind without the full QuotVal.
    ///
    /// # Returns
    /// - `Some(QuotKind)` if the name is a quotient primitive
    /// - `None` otherwise
    ///
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    #[allow(dead_code)]
    pub(crate) fn get_quot_kind(&self, name: &Name) -> Option<QuotKind> {
        self.quotients.get(name).map(|q| q.kind)
    }

    // Declaration addition methods (add_decl, add_decl_unchecked,
    // add_decl_structural) are in env/decl_add.rs

    /// Look up a constant by name.
    ///
    /// Returns information about the constant including its type and value (if defined).
    /// This includes definitions, axioms, theorems, and the type-level entries for
    /// inductives, constructors, and recursors.
    ///
    /// # Returns
    /// - `Some(&ConstantInfo)` if the constant exists
    /// - `None` if no constant with this name has been declared
    ///
    /// For inductives/constructors/recursors, use the specialized methods
    /// ([`Self::get_inductive`], [`Self::get_constructor`], [`Self::get_recursor`])
    /// to access additional metadata not available in the ConstantInfo.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_const(&self, name: &Name) -> Option<&ConstantInfo> {
        if let Some(ci) = self.constants.get(name) {
            return Some(ci);
        }
        // Lazy fallback: a trusted-closure constant not eagerly loaded. `None` when
        // no source is installed (the default), so behavior is byte-identical to the
        // eager-only path. The eager map always wins (target replay can legitimately
        // shadow a closure name).
        self.lazy_source
            .as_ref()
            .and_then(|source| source.get(name))
    }

    /// Install a lazy [`ConstantSource`] for trusted-closure constants (the
    /// zero-copy mmap loader). Constants in `constants` always take precedence; the
    /// source is consulted only on a miss. Replacing the source drops the previous.
    pub fn set_constant_source(&mut self, source: std::sync::Arc<dyn ConstantSource>) {
        self.lazy_source = Some(source);
    }

    /// Swap the installed lazy source for a fresh view with cleared
    /// memoization (no-op when no source is installed or the source has no
    /// cache — [`ConstantSource::fresh`] returns `None`).
    ///
    /// MEMORY-RECLAIM ONLY: by the `fresh` contract a view swap cannot change
    /// what any name resolves to. Requiring `&mut self` means no outstanding
    /// `&ConstantInfo` borrows from the old view can exist across the swap
    /// (they are tied to a `&Environment` borrow the caller must have ended),
    /// so the old view's memo drops safely.
    pub fn refresh_constant_source_cache(&mut self) {
        if let Some(source) = &self.lazy_source {
            if let Some(fresh) = source.fresh() {
                self.lazy_source = Some(fresh);
            }
        }
    }

    /// Whether a lazy [`ConstantSource`] is installed.
    #[must_use]
    pub fn has_constant_source(&self) -> bool {
        self.lazy_source.is_some()
    }

    /// All constant names served by the lazy [`ConstantSource`] (empty if none).
    /// These are NOT enumerated by [`constants`](Self::constants) (which only
    /// walks owned constants); use this to scan the full imported closure (e.g.
    /// for typeclass instances served lazily by the zero-copy loader).
    #[must_use]
    pub fn lazy_source_names(&self) -> Vec<Name> {
        self.lazy_source
            .as_ref()
            .map(|s| s.names())
            .unwrap_or_default()
    }

    /// Produce a SCRATCH clone of this environment in which the named
    /// `Declaration::Opaque` carrier is re-registered as a TRANSPARENT,
    /// `@[reducible]` `Declaration::Definition` with the SAME body — so it
    /// δ-unfolds during `whnf`/`is_def_eq` (an `Opaque`-kind constant is the one
    /// thing the reducer refuses to unfold; see `tc::def_eq::delta_helpers`).
    /// Used by the Soundness Certificate's opacity-transparency pass (C4') to
    /// detect axioms whose conclusion would reduce to a FALSE prop *if* the
    /// opaque carrier in their type were transparent — the `Rat.abs`-class
    /// masking bug.
    ///
    /// Returns `None` if `name` is absent or is not an `Opaque`-kind constant
    /// carrying a value (nothing to make transparent). The clone is otherwise
    /// byte-identical to `self`, so running the existing refutation scanner over
    /// it isolates exactly the effect of unfolding this one carrier.
    #[must_use]
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn with_opaque_made_transparent(&self, name: &Name) -> Option<Environment> {
        let info = self.constants.get(name)?;
        if info.kind != ConstantKind::Opaque || info.value.is_none() {
            return None;
        }
        let mut scratch = self.clone();
        if let Some(entry) = scratch.constants.get_mut(name) {
            // Same type, same body — only the unfold posture changes: Opaque →
            // reducible Definition. This is a SCRATCH view for refutation only;
            // it is never persisted or type-checked into the real env.
            entry.kind = ConstantKind::Definition;
            entry.reducibility = Reducibility::Reducible;
            entry.is_reducible = true;
        }
        scratch.declaration_verification.remove(name);
        Some(scratch)
    }

    /// Drop never-unfolded proof VALUES from this environment in place to bound
    /// resident memory when it serves only as TRUSTED IMPORTED CONTEXT for
    /// type-checking a *separate* target module (Mathverse Subsumption Engine
    /// WS3 — bounded-memory closure loading).
    ///
    /// For each constant whose [`ConstantKind`] the `policy` selects, the
    /// `value` field is set to `None`. TYPES are always retained (references to
    /// the constant still type-check) and `Definition` values are always
    /// retained (the kernel δ-unfolds them). Inductives, constructors,
    /// recursors and quotient primitives are untouched.
    ///
    /// SOUNDNESS: with [`ProofValueElision::OpaqueOnly`] this is a verdict-
    /// preserving no-op for the type checker. The kernel's only δ-unfold entry
    /// point, [`Environment::unfold_definition`] (`env/unfold.rs`), returns
    /// `None` for any `Opaque`-kind constant, so an `Opaque` value is never read
    /// during `whnf` / `is_def_eq` — dropping it cannot change a result. The
    /// stored TYPE is all the kernel ever consults for such a constant.
    ///
    /// CAUTION: [`ProofValueElision::OpaqueAndTheorem`] also drops `Theorem`
    /// values. This kernel CAN δ-unfold theorems (`unfold_definition` only
    /// blocks `Opaque`/`Axiom`), so that policy is not statically verdict-
    /// preserving and must be validated by an unchanged kernel-verified-count
    /// gate on the target corpus before use.
    ///
    /// This NEVER touches the target module's own decls: they are added to the
    /// environment AFTER this pass, through `add_decl`'s `check_type`, and keep
    /// their values. It also never touches any on-disk `.olean` / `.mathverse`
    /// data — only the resident in-memory map.
    pub fn elide_proof_values(&mut self, policy: ProofValueElision) -> ProofElisionStats {
        let mut stats = ProofElisionStats::default();
        if policy == ProofValueElision::None {
            stats.retained = self.constants.len();
            return stats;
        }
        let mut elided_names = Vec::new();
        for info in self.constants.values_mut() {
            if info.value.is_some() && policy.elides(info.kind) {
                info.value = None;
                elided_names.push(info.name.clone());
                match info.kind {
                    ConstantKind::Opaque => stats.opaque_elided += 1,
                    ConstantKind::Theorem => stats.theorem_elided += 1,
                    // `elides` only returns true for Opaque/Theorem; other
                    // kinds fall through to the retained branch defensively.
                    _ => stats.retained += 1,
                }
            } else {
                stats.retained += 1;
            }
        }
        for name in &elided_names {
            self.declaration_verification.remove(name);
        }
        if stats.total_elided() > 0 {
            self.generation += 1;
        }
        stats
    }

    /// Count the proof VALUES that `policy` has already dropped from this
    /// environment, WITHOUT mutating it.
    ///
    /// Reports, per elided kind, how many constants of that kind now carry no
    /// value (`value == None`) — i.e. the values that load-time elision
    /// ([`crate::env::ProofValueElision`] threaded through the `.olean` loader)
    /// removed. Used to surface bounded-memory stats after a closure load that
    /// elided at registration rather than as a post-pass. Returns all-zero for
    /// [`ProofValueElision::None`].
    #[must_use]
    pub fn count_elided_proof_values(&self, policy: ProofValueElision) -> ProofElisionStats {
        let mut stats = ProofElisionStats::default();
        if policy == ProofValueElision::None {
            stats.retained = self.constants.len();
            return stats;
        }
        for info in self.constants.values() {
            if info.value.is_none() && policy.elides(info.kind) {
                match info.kind {
                    ConstantKind::Opaque => stats.opaque_elided += 1,
                    ConstantKind::Theorem => stats.theorem_elided += 1,
                    _ => stats.retained += 1,
                }
            } else {
                stats.retained += 1;
            }
        }
        stats
    }

    /// Add a Skolem axiom to the environment.
    ///
    /// Skolem constants are opaque witnesses introduced by the clausifier's
    /// Skolemization pass. They have a type but no value. Declaring them
    /// as axioms allows the type checker to accept proof terms that
    /// reference Skolemized terms during superposition proof reconstruction.
    pub fn add_skolem_axiom(&mut self, name: Name, ty: Expr) {
        let info = ConstantInfo {
            name: name.clone(),
            level_params: vec![],
            type_: ty,
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Irreducible,
            kind: ConstantKind::Axiom,
        };
        self.constants.insert(name.clone(), info);
        // A Skolem axiom is an explicit assumption, not a checked proof.
        self.declaration_verification
            .insert(name, DeclarationVerification::Unchecked);
    }

    /// Get the parameter names for a constant (if registered).
    ///
    /// Returns the parameter names in declaration order, used for
    /// named argument matching during elaboration (#1230).
    pub fn get_param_names(&self, name: &Name) -> Option<&[String]> {
        self.param_names.get(name).map(|v| v.as_slice())
    }

    /// Get the binder kinds parallel to [`Self::get_param_names`] (B01).
    ///
    /// `None` for names-only legacy registrations; consumers must then treat
    /// every recorded parameter as explicit (the pre-B01 behavior).
    pub fn get_param_binder_infos(&self, name: &Name) -> Option<&[BinderInfo]> {
        self.param_binder_infos.get(name).map(|v| v.as_slice())
    }

    /// Register parameter names for a constant.
    ///
    /// Called during elaboration when a declaration's binder names are known.
    /// Names-only legacy path: records no binder kinds (see
    /// [`Self::set_param_infos`] for the kind-carrying registration).
    pub(crate) fn set_param_names(&mut self, name: Name, names: Vec<String>) {
        self.param_binder_infos.remove(&name);
        self.param_names.insert(name, names);
    }

    /// Register parameter names WITH binder kinds for a constant (B01).
    ///
    /// Lean ground truth: named arguments bind to the binder with that exact
    /// name while positional arguments fill the remaining *explicit* binders
    /// in order (lean4 `src/Lean/Elab/App.lean`, `ElabAppArgs`). The kinds
    /// recorded here let the elaborator implement that explicit/implicit
    /// distinction for surface declarations.
    pub(crate) fn set_param_infos(&mut self, name: Name, infos: Vec<(String, BinderInfo)>) {
        let (names, kinds): (Vec<String>, Vec<BinderInfo>) = infos.into_iter().unzip();
        self.param_binder_infos.insert(name.clone(), kinds);
        self.param_names.insert(name, names);
    }

    /// Register a persistent environment extension (no entries yet).
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn register_persistent_extension(&mut self, name: Name) -> bool {
        if self.persistent_extensions.contains_key(&name) {
            return false;
        }
        self.persistent_extensions
            .insert(name, PersistentEnvExtensionState::default());
        true
    }

    /// Add entries for a persistent environment extension at a module index.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn add_persistent_extension_entries(
        &mut self,
        name: &Name,
        module_idx: usize,
        entries: Vec<EnvExtensionEntry>,
    ) {
        let state = self.persistent_extensions.entry(name.clone()).or_default();

        if state.imported_entries.len() <= module_idx {
            state.imported_entries.resize_with(module_idx + 1, Vec::new);
        }

        state.imported_entries[module_idx].extend(entries);
    }

    /// Get the persistent extension state for a given extension name.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn get_persistent_extension_state(
        &self,
        name: &Name,
    ) -> Option<&PersistentEnvExtensionState> {
        self.persistent_extensions.get(name)
    }

    /// Get entries for a given extension name and module index.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn get_persistent_extension_module_entries(
        &self,
        name: &Name,
        module_idx: usize,
    ) -> Option<&[EnvExtensionEntry]> {
        self.persistent_extensions
            .get(name)
            .and_then(|state| state.imported_entries.get(module_idx).map(|v| v.as_slice()))
    }

    // ========================================================================
    // Typed persistent extension API (#916)
    // ========================================================================

    /// Get typed extension state (read-only, after materialization).
    ///
    /// Returns `None` if the extension state has not been materialized yet.
    /// Call `materialize_extension_states()` after .olean import, or use
    /// `get_ext_state_or_init()` for lazy initialization.
    pub fn get_ext_state<S: PersistentExtState + 'static>(&self, idx: ExtensionIdx) -> Option<&S> {
        self.extension_states.get_state::<S>(idx)
    }

    /// Get typed extension state with lazy initialization.
    ///
    /// If the extension state hasn't been materialized yet, folds imported
    /// raw entries into typed state before returning.
    pub fn get_ext_state_or_init<S: PersistentExtState + 'static>(
        &mut self,
        idx: ExtensionIdx,
    ) -> Option<&S> {
        self.ensure_ext_initialized(idx);
        self.extension_states.get_state::<S>(idx)
    }

    /// Get mutable typed extension state with lazy initialization.
    pub fn get_ext_state_mut<S: PersistentExtState + 'static>(
        &mut self,
        idx: ExtensionIdx,
    ) -> &mut S {
        self.ensure_ext_initialized(idx);
        self.extension_states.get_state_mut::<S>(idx)
    }

    /// Add a typed entry to a persistent extension.
    ///
    /// The entry is stored in the typed state and will be exported to
    /// .olean via the extension's `export_entries` method.
    pub fn add_ext_entry<S: PersistentExtState + 'static>(
        &mut self,
        idx: ExtensionIdx,
        entry: &S::Entry,
    ) {
        self.ensure_ext_initialized(idx);
        self.extension_states.add_entry::<S>(idx, entry);
        self.generation += 1;
    }

    /// Materialize all typed extension states from imported raw entries.
    ///
    /// Called after .olean import to eagerly initialize all registered
    /// extensions. After this call, `get_ext_state(&self, ...)` works
    /// without needing `&mut self`.
    pub fn materialize_extension_states(&mut self) {
        self.extension_states
            .fold_all_imported(&self.persistent_extensions);
    }

    /// Export all typed extension states to raw entries.
    ///
    /// Returns pairs of (extension_name, entries) suitable for .olean
    /// serialization.
    pub fn export_extension_states(&self) -> Vec<(Name, Vec<EnvExtensionEntry>)> {
        self.extension_states.export_all()
    }

    /// Internal: ensure a specific extension's typed state is initialized.
    fn ensure_ext_initialized(&mut self, idx: ExtensionIdx) {
        if self.extension_states.is_initialized(idx) {
            return;
        }
        let ext_name = {
            let reg = persistent_ext::global_registry()
                .lock()
                .expect("invariant: extension registry mutex not poisoned");
            reg.get_descriptor(idx).map(|d| d.name.clone())
        };
        if let Some(name) = ext_name {
            if let Some(raw_state) = self.persistent_extensions.get(&name) {
                let entries_flat: Vec<EnvExtensionEntry> = raw_state
                    .imported_entries
                    .iter()
                    .flat_map(|m| m.iter())
                    .cloned()
                    .collect();
                self.extension_states
                    .fold_imported_entries(idx, &entries_flat);
            } else {
                self.extension_states.fold_imported_entries(idx, &[]);
            }
        }
    }

    /// Monotonically increasing generation counter (#1279).
    ///
    /// Bumped on every mutation (add_decl, add_inductive, register_instance,
    /// register_simp_lemma, etc.). Used by the type checker cache — and by the
    /// elaborator's per-environment simp lemma-set cache — to detect
    /// environment changes even when the constant count stays the same
    /// (e.g., remove + add).
    pub fn generation(&self) -> u64 {
        self.generation
    }

    /// Look up an inductive type by name.
    ///
    /// Returns the full inductive type metadata including constructor names,
    /// recursion info, and universe parameters.
    ///
    /// # Returns
    /// - `Some(&InductiveVal)` if `name` is a declared inductive type
    /// - `None` otherwise (including for constructors/recursors of that inductive)
    ///
    /// Use [`Self::get_constructor`] to look up specific constructors,
    /// or [`Self::get_recursor`] for the recursor.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_inductive(&self, name: &Name) -> Option<&InductiveVal> {
        self.inductives.get(name)
    }

    /// Look up a constructor by name.
    ///
    /// Returns constructor metadata including the parent inductive type,
    /// field count, and non-parametric argument count.
    ///
    /// # Returns
    /// - `Some(&ConstructorVal)` if `name` is a declared constructor
    /// - `None` otherwise (including for the inductive type name itself)
    ///
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_constructor(&self, name: &Name) -> Option<&ConstructorVal> {
        self.constructors.get(name)
    }

    /// Look up a recursor by name.
    ///
    /// Returns recursor metadata including reduction rules, motive info,
    /// and major premise position.
    ///
    /// # Returns
    /// - `Some(&RecursorVal)` if `name` is a declared recursor
    /// - `None` otherwise
    ///
    /// Recursors are automatically generated for each inductive type.
    /// The recursor name is typically `InductiveName.rec`.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_recursor(&self, name: &Name) -> Option<&RecursorVal> {
        self.recursors.get(name)
    }

    /// Reassemble the [`InductiveDecl`] for the family rooted at `name` from
    /// the environment's inductive side tables (read-only; no checker calls).
    ///
    /// The returned declaration carries the stored (post fixed-index
    /// promotion) `num_params`, the family's `level_params`, and one
    /// [`crate::inductive::InductiveType`] per `all_names` entry with its
    /// constructors in declaration order — i.e. exactly the shape
    /// [`Self::add_inductive`] would re-check. Used by graduation v3 to
    /// re-earn a value-less carrier's kernel certificate in a fresh
    /// environment.
    ///
    /// # Returns
    /// - `Some(InductiveDecl)` when `name` is a declared inductive type and
    ///   every `all_names` sibling and constructor is present in the side
    ///   tables
    /// - `None` otherwise (including for constructors/recursors — resolve
    ///   those to their `inductive_name` first)
    ///
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn inductive_decl_of(&self, name: &Name) -> Option<InductiveDecl> {
        let root = self.inductives.get(name)?;
        let mut types = Vec::with_capacity(root.all_names.len());
        for type_name in &root.all_names {
            let ind = self.inductives.get(type_name)?;
            let mut constructors = Vec::with_capacity(ind.constructor_names.len());
            for ctor_name in &ind.constructor_names {
                let ctor = self.constructors.get(ctor_name)?;
                constructors.push(Constructor {
                    name: ctor.name.clone(),
                    type_: ctor.type_.clone(),
                });
            }
            types.push(InductiveType {
                name: ind.name.clone(),
                type_: ind.type_.clone(),
                constructors,
            });
        }
        Some(InductiveDecl {
            level_params: root.level_params.clone(),
            num_params: root.num_params,
            types,
        })
    }

    // Registration methods (register/extend inductive/constructor/recursor,
    // validate_recursor_metadata, structure field management) are in env/registration.rs

    // Instantiation, unfolding, and height computation methods
    // (instantiate_type, get_max_height, unfold, unfold_with_transparency)
    // are in env/unfold.rs

    /// Iterate over all constants
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn constants(&self) -> impl Iterator<Item = &ConstantInfo> {
        self.constants.values()
    }

    /// Iterate over all inductives
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn inductives(&self) -> impl Iterator<Item = &InductiveVal> {
        self.inductives.values()
    }

    /// Iterate over all constructors
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn constructors(&self) -> impl Iterator<Item = &ConstructorVal> {
        self.constructors.values()
    }

    /// Iterate over all recursors
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn recursors(&self) -> impl Iterator<Item = &RecursorVal> {
        self.recursors.values()
    }

    /// Iterate over all quotient primitives
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn quotients(&self) -> impl Iterator<Item = &QuotVal> {
        self.quotients.values()
    }

    // Serialization methods (to_json, from_json, to_bincode, from_bincode,
    // save_to_file, load_from_file) are in env/serialization.rs

    /// Get the number of constants
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn num_constants(&self) -> usize {
        self.constants.len()
    }

    /// Get the number of inductives
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn num_inductives(&self) -> usize {
        self.inductives.len()
    }

    /// Get the number of constructors
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn num_constructors(&self) -> usize {
        self.constructors.len()
    }

    /// Get the number of recursors
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn num_recursors(&self) -> usize {
        self.recursors.len()
    }

    /// Get the number of quotient primitives
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn num_quotients(&self) -> usize {
        self.quotients.len()
    }

    /// Remove a constant by name (test-only).
    ///
    /// Used to simulate .olean loading gaps where certain constants
    /// (like noConfusionType) are not serialized and must be regenerated.
    #[cfg(test)]
    pub fn remove_constant(&mut self, name: &Name) {
        self.constants.remove(name);
        self.declaration_verification.remove(name);
    }

    /// Drop a constant's stored `value` (proof/definition body), KEEPING its type,
    /// and force it `Opaque` so the reduction path never tries to unfold it.
    ///
    /// SOUNDNESS: sound ONLY for a constant that is never delta-unfolded during
    /// later type-checking — e.g. an opaque theorem whose body is a proof, not a
    /// computational definition. Future `add_decl`s referencing it use its TYPE,
    /// which is retained, so they remain well-typed and accept/reject identically.
    /// Forcing `Opaque` only REMOVES a potential reduction rule (can never make an
    /// unequal pair equal), so it cannot introduce a false accept. Used to bound
    /// peak memory when batch-verifying a large corpus of opaque theorems (the
    /// Metamath import) whose proofs need not be retained after the kernel has
    /// already checked them. Returns `true` if the constant existed.
    /// Remove a constant ENTIRELY (type and value) from the environment.
    ///
    /// SOUNDNESS: this only ever DELETES a declaration; it can never make an
    /// unequal pair equal or a false proof check. A later `add_decl` that
    /// references the removed name fails to type-check (unknown constant) — a
    /// FAILURE, not a false accept. The caller is responsible for removing only
    /// declarations that no later input can reference; misuse loses verifications
    /// (caught by count-equivalence), never gains spurious ones. Used to bound
    /// peak memory when batch-verifying a large corpus (the Metamath import):
    /// once a theorem's schematic type can no longer be reused, dropping it keeps
    /// the resident set bounded instead of growing with the whole corpus.
    /// Returns `true` if the constant existed.
    pub fn forget_decl(&mut self, name: &Name) -> bool {
        let removed = self.constants.remove(name).is_some();
        if removed {
            self.declaration_verification.remove(name);
        }
        removed
    }

    /// Install `decl` as a PROVISIONAL HEADER — a signature staged so later
    /// declarations resolve names independently of source order (Trust I1).
    ///
    /// The declaration must be an [`Declaration::Axiom`]: a header is a name
    /// and a type with no value, and there is no other shape it can take. The
    /// type still goes through the full [`Environment::add_decl`] kernel check,
    /// so a malformed signature is refused here rather than surfacing later as
    /// a mystery in some body that resolved against it.
    ///
    /// SOUNDNESS — this makes the environment NON-AUTHORITATIVE. A staged
    /// header is indistinguishable, to every consumer, from an axiom the user
    /// never wrote, so an environment holding one may not back a certification.
    /// Two mechanisms enforce that, and only the second lives here:
    ///
    ///   1. STRUCTURAL (the real firewall): header-first elaboration keeps the
    ///      staging environment separate from the environment declarations are
    ///      registered into, and never installs a header in the latter. A term
    ///      naming a header therefore fails `add_decl` by unknown-constant.
    ///   2. MARKER (defence in depth, this function): the name is recorded in
    ///      `staged_headers`, and [`Environment::audit_certification`] reports
    ///      a blocking [`CertificationIssue::Staged`] for any reachable member.
    ///      So even if a staging environment escaped, nothing it supports can
    ///      be graded above `Rejected`.
    ///
    /// Discharge a header with [`Environment::discharge_staged_header`] before
    /// registering the real declaration.
    ///
    /// # Errors
    /// Returns [`EnvError`] if `decl` is not an axiom, or if the kernel refuses
    /// the header's type.
    pub fn add_staged_header(&mut self, decl: Declaration) -> Result<(), EnvError> {
        let Declaration::Axiom { ref name, .. } = decl else {
            let offender = match &decl {
                Declaration::Definition { name, .. }
                | Declaration::Axiom { name, .. }
                | Declaration::Theorem { name, .. }
                | Declaration::Opaque { name, .. } => name.clone(),
            };
            return Err(EnvError::InvalidDeclarationShape {
                init: "add_staged_header",
                decl: offender,
                detail: "a staged header is a name and a type with no value, so it must be a \
                         Declaration::Axiom; either pass the signature as an axiom, or register \
                         the complete declaration with add_decl instead",
            });
        };
        let name = name.clone();
        self.add_decl(decl)?;
        self.staged_headers.insert(name);
        Ok(())
    }

    /// True when `name` is currently installed as a provisional header.
    #[must_use]
    pub fn is_staged_header(&self, name: &Name) -> bool {
        self.staged_headers.contains(name)
    }

    /// True when ANY provisional header is installed — i.e. this environment is
    /// not authoritative. Publish gates assert this is `false`.
    #[must_use]
    pub fn has_staged_headers(&self) -> bool {
        !self.staged_headers.is_empty()
    }

    /// Every provisional header currently installed, sorted for determinism.
    #[must_use]
    pub fn staged_header_names(&self) -> Vec<Name> {
        let mut names: Vec<Name> = self.staged_headers.iter().cloned().collect();
        names.sort();
        names
    }

    /// Remove a provisional header and every table entry it could have seeded,
    /// so the real declaration can be registered in its place.
    ///
    /// [`Environment::forget_decl`] is NOT sufficient: it drops the constant and
    /// its verification stamp only, leaving instance / class / parameter-name /
    /// structure-field rows behind. Those are exactly what a header carrying
    /// instance metadata would have written, and a stale row outlives the
    /// header it came from.
    ///
    /// Fail-closed: refuses (returns `false`, changing nothing) for a name that
    /// is not a staged header, so this can never be used to delete a real,
    /// kernel-checked declaration.
    pub fn discharge_staged_header(&mut self, name: &Name) -> bool {
        if !self.staged_headers.remove(name) {
            return false;
        }
        self.constants.remove(name);
        self.declaration_verification.remove(name);
        self.constant_origins.remove(name);
        self.param_names.remove(name);
        self.param_binder_infos.remove(name);
        self.structure_fields.remove(name);
        self.classes.remove(name);
        self.inductives.remove(name);
        self.constructors.remove(name);
        self.recursors.remove(name);
        if self.instance_names.remove(name) {
            for entries in self.instances.values_mut() {
                entries.retain(|entry| &entry.name != name);
            }
        }
        self.private_decls.remove(name);
        self.protected_decls.remove(name);
        self.noncomputable_decls.remove(name);
        self.partial_decls.remove(name);
        self.unsafe_decls.remove(name);
        self.generation += 1;
        true
    }

    pub fn forget_value(&mut self, name: &Name) -> bool {
        if let Some(ci) = self.constants.get_mut(name) {
            ci.value = None;
            ci.reducibility = Reducibility::Opaque;
            // The exact payload that earned any previous verification stamp
            // no longer exists. Missing provenance is the conservative state;
            // certification will report the elided value explicitly.
            self.declaration_verification.remove(name);
            true
        } else {
            false
        }
    }

    /// Drop the proof VALUES of the named constants whose [`ConstantKind`] the
    /// `policy` selects, KEEPING each constant's type+kind. Returns the count
    /// actually elided (per kind) plus the number skipped because the policy
    /// did not select their kind or they had no value.
    ///
    /// This is the streaming counterpart of [`Environment::elide_proof_values`]
    /// (which scans the WHOLE env): here the caller supplies the exact set of
    /// constants whose own `check_type` has just SUCCEEDED, so their value DAG
    /// can be freed immediately to bound peak memory.
    ///
    /// SOUNDNESS: identical to [`Environment::elide_proof_values`] — see that
    /// method's contract. With [`ProofValueElision::OpaqueOnly`] this is a
    /// verdict-preserving no-op for the type checker (the kernel's only
    /// δ-unfold entry point, [`Environment::unfold_definition`], returns `None`
    /// for `Opaque`-kind constants, so an `Opaque` value is never read during
    /// `whnf`/`is_def_eq`). Each elided constant is also forced
    /// [`Reducibility::Opaque`] (matching [`Environment::forget_value`]) so the
    /// lazy-delta path's reducibility-gated unfold cannot consult it either.
    pub fn forget_proof_values_for<'a, I>(
        &mut self,
        names: I,
        policy: ProofValueElision,
    ) -> ProofElisionStats
    where
        I: IntoIterator<Item = &'a Name>,
    {
        let mut stats = ProofElisionStats::default();
        if policy == ProofValueElision::None {
            return stats;
        }
        for name in names {
            let mut elided = false;
            if let Some(ci) = self.constants.get_mut(name) {
                if ci.value.is_some() && policy.elides(ci.kind) {
                    let kind = ci.kind;
                    ci.value = None;
                    ci.reducibility = Reducibility::Opaque;
                    elided = true;
                    match kind {
                        ConstantKind::Opaque => stats.opaque_elided += 1,
                        ConstantKind::Theorem => stats.theorem_elided += 1,
                        _ => stats.retained += 1,
                    }
                } else {
                    stats.retained += 1;
                }
            }
            if elided {
                self.declaration_verification.remove(name);
            }
        }
        if stats.total_elided() > 0 {
            self.generation += 1;
        }
        stats
    }

    /// Insert a fully-formed `ConstantInfo` directly (test-only).
    ///
    /// Bypasses `add_decl`'s `check_type`; used by unit tests that need a
    /// constant of a SPECIFIC `ConstantKind`/value shape (e.g. the proof-value
    /// elision tests) without minting a kernel-valid proof term.
    #[cfg(test)]
    pub(crate) fn add_constant_for_test(&mut self, info: ConstantInfo) {
        let name = info.name.clone();
        self.constants.insert(name.clone(), info);
        self.declaration_verification
            .insert(name, DeclarationVerification::Unchecked);
    }

    /// Cross-crate test-support: insert a fully-formed `ConstantInfo` directly,
    /// bypassing `add_decl`'s `check_type`. Used by downstream crates' tests
    /// that must mint a deliberately ILL-TYPED constant (e.g. to prove the
    /// streaming proof-value elision still FAILS such a constant). Hidden from
    /// docs and NOT for production paths — it is purely a soundness-test fixture
    /// builder. Mirrors `add_constant_for_test`.
    #[doc(hidden)]
    pub fn add_constant_unchecked_for_test(&mut self, info: ConstantInfo) {
        let name = info.name.clone();
        self.constants.insert(name.clone(), info);
        self.declaration_verification
            .insert(name, DeclarationVerification::Unchecked);
    }

    /// Remove a constant that is currently a bare `Declaration::Axiom`, so a
    /// later `add_decl` can register a real, kernel-checked
    /// `Declaration::Definition`/`Theorem` of the SAME type in its place
    /// (discharging the admitted axiom).
    ///
    /// Returns `true` if a constant of the given name existed and was an Axiom
    /// (and has now been removed), `false` otherwise. Never removes a
    /// non-Axiom constant — a Definition/Theorem already in place is left
    /// untouched, which keeps the swap idempotent.
    ///
    /// SOUNDNESS: only an `Axiom` (no value, opaque) is ever removed here. The
    /// caller must immediately re-`add_decl` a declaration whose `type_` is
    /// definitionally the axiom's type, so every previously type-checked term
    /// referencing the constant remains well-typed; the only change is that the
    /// constant gains a reduction rule it did not have before.
    pub(crate) fn discharge_axiom_for_redefinition(&mut self, name: &Name) -> bool {
        if let Some(info) = self.constants.get(name) {
            if matches!(info.kind, ConstantKind::Axiom) {
                self.constants.remove(name);
                self.declaration_verification.remove(name);
                self.generation += 1;
                return true;
            }
        }
        false
    }

    /// Discharge a bare `Declaration::Axiom` *stub* so that the genuine,
    /// kernel-checked inductive/structure of the SAME name (arriving through the
    /// `.olean` import path) can register in its place.
    ///
    /// The import prelude pre-registers a handful of typeclass *carrier* heads
    /// (`Membership`, `Fact`, …) as opaque `Axiom` shims so that hand-rolled
    /// instances (`Set`/`Multiset`/`Finset` membership) resolve before any real
    /// library is loaded. When the authentic Lean class is imported — OR
    /// re-declared from source (the elaborator's `register` structure path calls
    /// this before `add_inductive`) — it arrives as an `Inductive`/`structure`,
    /// whose name (and generated constructor/projection names) collide with the
    /// shims; the loader's name-dedup would otherwise keep the opaque shim and
    /// DROP the genuine inductive, leaving a phantom non-foundational axiom in
    /// `axiom_deps` (and, on the source path, a hard "Duplicate declaration"
    /// error that blocks the real structure entirely).
    ///
    /// Returns `true` iff a constant of the given name existed, was an `Axiom`
    /// (no value), and has now been removed. Never removes a non-`Axiom`
    /// constant; never removes a constant already backed by an inductive (the
    /// loader checks `get_inductive` separately, so this is only reached for the
    /// bare-stub case). The swap is therefore idempotent.
    ///
    /// SOUNDNESS: only a value-free `Axiom` is removed, and the caller MUST
    /// immediately register the genuine inductive of definitionally the same
    /// type through the checked import path. Every term that previously
    /// type-checked against the opaque carrier head remains well-typed (the head
    /// keeps the same Pi type); the only change is that the carrier gains its
    /// real constructors/recursor and stops being counted as a domain axiom.
    /// This makes the foundational-axiom verdict strictly MORE accurate — it
    /// removes a fabricated axiom and never admits a new one.
    #[must_use]
    pub fn discharge_axiom_stub_for_inductive_import(&mut self, name: &Name) -> bool {
        if self.inductives.contains_key(name) {
            return false;
        }
        match self.constants.get(name) {
            Some(info) if matches!(info.kind, ConstantKind::Axiom) && info.value.is_none() => {
                self.constants.remove(name);
                self.declaration_verification.remove(name);
                self.generation += 1;
                true
            }
            _ => false,
        }
    }

    pub fn set_option(&mut self, name: String, value: Option<String>) {
        self.options.insert(name, value);
    }
    #[must_use]
    pub fn get_option(&self, name: &str) -> Option<&Option<String>> {
        self.options.get(name)
    }
    /// Remove a file-level option, restoring it to the unset state.
    ///
    /// Used by per-declaration `set_option ... in <decl>` to restore the
    /// environment after the scoped declaration is elaborated.
    pub fn remove_option(&mut self, name: &str) {
        self.options.remove(name);
    }
}

#[cfg(test)]
mod init_contracts;
#[cfg(test)]
mod test_helpers;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_abstract_interpretation;
#[cfg(test)]
mod tests_abstract_interpretation_framework;
#[cfg(test)]
mod tests_add_decl_audit;
#[cfg(test)]
mod tests_advanced;
#[cfg(test)]
mod tests_advanced2;
#[cfg(test)]
mod tests_ai_proof_search_demo;
#[cfg(test)]
mod tests_algebra_rat_add_assoc;
#[cfg(test)]
mod tests_algebra_rat_add_comm;
#[cfg(test)]
mod tests_algebra_rat_mul_assoc;
#[cfg(test)]
mod tests_all_family;
#[cfg(test)]
mod tests_axiom_audit;
#[cfg(test)]
mod tests_bcp_loop_refinement;
#[cfg(test)]
mod tests_below;
#[cfg(test)]
mod tests_below_eq;
#[cfg(test)]
mod tests_bounded_width_automatizability;
#[cfg(test)]
mod tests_builder_migration_regression;
#[cfg(test)]
mod tests_cast_simp;
#[cfg(test)]
mod tests_cdcl_soundness;
#[cfg(test)]
mod tests_constant_origin;
#[cfg(test)]
mod tests_craig_interpolation;
#[cfg(test)]
mod tests_cutting_planes;
#[cfg(test)]
mod tests_deep_induction;
#[cfg(test)]
mod tests_entropy_clause_quality;
#[cfg(test)]
mod tests_extension_rule;
#[cfg(test)]
mod tests_extension_rule_soundness;
#[cfg(test)]
mod tests_false_axiom_prevention;
#[cfg(test)]
mod tests_feasible_interpolation;
#[cfg(test)]
mod tests_fourier_boolean;
#[cfg(test)]
mod tests_gamma_crown_verify;
#[cfg(test)]
mod tests_gf2_polynomial_calculus;
#[cfg(test)]
mod tests_hit_s1;
#[cfg(test)]
mod tests_hit_susp;
#[cfg(test)]
mod tests_hit_trunc;
#[cfg(test)]
mod tests_init_contracts;
#[cfg(test)]
mod tests_instance_priority_adoption;
#[cfg(test)]
mod tests_int_abs_proofs;
#[cfg(test)]
mod tests_int_dist_proofs;
#[cfg(test)]
mod tests_interpolation_proofs;
#[cfg(test)]
mod tests_isasat_refinement;
#[cfg(test)]
mod tests_issue_1488;
#[cfg(test)]
mod tests_labelled_interpolation_minimality;
#[cfg(test)]
mod tests_learned_clause_minimality;
#[cfg(test)]
mod tests_local_lift;
#[cfg(test)]
mod tests_local_lift_bridge;
#[cfg(test)]
mod tests_masquerade_gate;
#[cfg(test)]
mod tests_metric;
#[cfg(test)]
mod tests_monad_init;
#[cfg(test)]
mod tests_nat_mixed_trans_lemmas;
#[cfg(test)]
mod tests_nat_top_level_ordering;
#[cfg(test)]
mod tests_nested_elim;
#[cfg(test)]
mod tests_nested_elim_param;
#[cfg(test)]
mod tests_nn_acas_xu_e2e;
#[cfg(test)]
mod tests_nn_cert_parser;
#[cfg(test)]
mod tests_nn_verification_c002;
#[cfg(test)]
mod tests_nn_verification_c009;
#[cfg(test)]
mod tests_nn_verify_abstract_domain;
#[cfg(test)]
mod tests_nn_verify_blockwise_crown;
#[cfg(test)]
mod tests_nn_verify_blockwise_crown_demasquerade_3492;
#[cfg(test)]
mod tests_nn_verify_blockwise_crown_ext;
#[cfg(test)]
mod tests_nn_verify_blockwise_crown_ext_carriers;
#[cfg(test)]
mod tests_nn_verify_blockwise_crown_ext_t22_demasquerade_3590;
#[cfg(test)]
mod tests_nn_verify_blockwise_crown_ext_t61_demasquerade_3648;
#[cfg(test)]
mod tests_nn_verify_blockwise_crown_faithful;
#[cfg(test)]
mod tests_nn_verify_blockwise_crown_faithful_succ;
#[cfg(test)]
mod tests_nn_verify_c003_sorry_pi_carriers;
#[cfg(test)]
mod tests_nn_verify_c006_t60_faithful_ext;
#[cfg(test)]
mod tests_nn_verify_c009_sorry_pi_carriers;
#[cfg(test)]
mod tests_nn_verify_cert_complexity;
#[cfg(test)]
mod tests_nn_verify_cert_demasquerade_3592;
#[cfg(test)]
mod tests_nn_verify_certified_eval;
#[cfg(test)]
mod tests_nn_verify_certified_eval_compute;
#[cfg(test)]
mod tests_nn_verify_certified_training;
#[cfg(test)]
mod tests_nn_verify_crown_backward;
#[cfg(test)]
mod tests_nn_verify_crown_layernorm;
#[cfg(test)]
mod tests_nn_verify_crown_layernorm_faithful;
#[cfg(test)]
mod tests_nn_verify_crown_layernorm_faithful_carrier;
#[cfg(test)]
mod tests_nn_verify_dot_product_error;
#[cfg(test)]
mod tests_nn_verify_eclipse_convergence;
#[cfg(test)]
mod tests_nn_verify_fin_sum;
#[cfg(test)]
mod tests_nn_verify_float_rational;
#[cfg(test)]
mod tests_nn_verify_ibp_composition;
#[cfg(test)]
mod tests_nn_verify_ibp_linear;
#[cfg(test)]
mod tests_nn_verify_ibp_width_zero;
#[cfg(test)]
mod tests_nn_verify_interval_arith_rat_neg_le_neg;
#[cfg(test)]
mod tests_nn_verify_interval_arith_rat_sub_le_sub;
#[cfg(test)]
mod tests_nn_verify_interval_arith_width_le_monotone;
#[cfg(test)]
mod tests_nn_verify_interval_arith_width_monotone;
#[cfg(test)]
mod tests_nn_verify_interval_primitives;
#[cfg(test)]
mod tests_nn_verify_lipschitz;
#[cfg(test)]
mod tests_nn_verify_lipschitz_compose;
#[cfg(test)]
mod tests_nn_verify_lipschitz_eclipse;
#[cfg(test)]
mod tests_nn_verify_lipschitz_ext;
#[cfg(test)]
mod tests_nn_verify_matrix_rank;
#[cfg(test)]
mod tests_nn_verify_mccormick;
#[cfg(test)]
mod tests_nn_verify_mccormick_attention;
#[cfg(test)]
mod tests_nn_verify_mccormick_attention_demasquerade_3594;
#[cfg(test)]
mod tests_nn_verify_mccormick_ext;
#[cfg(test)]
mod tests_nn_verify_nullstellensatz;
#[cfg(test)]
mod tests_nn_verify_orbit_crown;
#[cfg(test)]
mod tests_nn_verify_pac_proof;
#[cfg(test)]
mod tests_nn_verify_proof_complexity;
#[cfg(test)]
mod tests_nn_verify_proof_guided_nas;
#[cfg(test)]
mod tests_nn_verify_rat_interval;
#[cfg(test)]
mod tests_nn_verify_rat_ordering;
#[cfg(test)]
mod tests_nn_verify_tier_a_nat_ordering;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_batch3;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_le_refl_max_zero_zero;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_le_refl_min_zero_zero;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_le_refl_zero;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_max_eq_min;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_max_zero_zero_alt;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_min_eq_max;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_min_zero;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_min_zero_zero_alt;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_zero_eq_max;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_zero_eq_min;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_zero_trio;
#[cfg(test)]
mod tests_nn_verify_tier_b_rat_abs;
#[cfg(test)]
mod tests_nn_verify_tier_b_rat_abs_demasquerade_3565;
#[cfg(test)]
mod tests_rat_false_add_axioms;
#[cfg(test)]
mod tests_recursor_authority;
#[cfg(test)]
mod tests_trans_lean_shape;
#[cfg(test)]
mod tests_ws17_import_prelude;
// Batch 4 (#3551): Rat min/max transitivity / idempotence at ground zero.
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_max_le_min_zero_zero;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_max_max_zero_zero;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_max_min_zero_zero;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_min_le_max_zero_zero;
#[cfg(test)]
mod tests_nn_verify_tier_a_rat_min_min_zero_zero;
// #3615: canonical `Rat.min_le_max` tests.
#[cfg(test)]
mod tests_bit_foundation_probe;
#[cfg(test)]
mod tests_nn_verify_rat_min_le_max;
#[cfg(test)]
mod tests_nn_verify_relu;
#[cfg(test)]
mod tests_nn_verify_relu_stability;
#[cfg(test)]
mod tests_nn_verify_robustness_gen;
#[cfg(test)]
mod tests_nn_verify_softmax_c011;
#[cfg(test)]
mod tests_nn_verify_streaming_certs;
#[cfg(test)]
mod tests_nn_verify_zonotope_compress;
#[cfg(test)]
mod tests_nn_verify_zonotope_compress_c001;
#[cfg(test)]
mod tests_nn_verify_zonotope_compress_c001_demasquerade_3586;
#[cfg(test)]
mod tests_nn_verify_zonotope_compress_ext;
#[cfg(test)]
mod tests_nn_verify_zonotope_crown_mat_mul_assoc;
#[cfg(test)]
mod tests_nn_verify_zonotope_to_ibp_demasquerade_3591;
#[cfg(test)]
mod tests_numeric;
#[cfg(test)]
mod tests_ordering;
#[cfg(test)]
mod tests_pb_pigeonhole;
#[cfg(test)]
mod tests_pb_pigeonhole_length_bound;
#[cfg(test)]
mod tests_persistent_ext;
#[cfg(test)]
mod tests_positivity;
#[cfg(test)]
mod tests_proof_builder;
#[cfg(test)]
mod tests_proof_complexity_proofs;
#[cfg(test)]
mod tests_proof_hierarchy;
#[cfg(test)]
mod tests_proof_search;
#[cfg(test)]
mod tests_proof_search_scan;
#[cfg(test)]
mod tests_registries;
#[cfg(test)]
mod tests_resolution_complexity;
#[cfg(test)]
mod tests_shadowing_overlay;
#[cfg(test)]
mod tests_sorry_tracer;
#[cfg(test)]
mod tests_structural_validation;
#[cfg(test)]
mod tests_tensor_ml;
#[cfg(test)]
mod tests_topology;
#[cfg(test)]
mod tests_topology_diff;
#[cfg(test)]
mod tests_topology_harness;
#[cfg(test)]
mod tests_topology_homotopy;
#[cfg(test)]
mod tests_topology_manifold;
#[cfg(test)]
mod tests_tree_width_resolution;
#[cfg(test)]
mod tests_verified_proof_search;
#[cfg(test)]
mod tests_veripb_checker;
#[cfg(test)]
mod tests_width_expansion;
#[cfg(test)]
mod tests_zonotope_false_axiom_prevention;
