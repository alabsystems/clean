// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end graduation pilot: fixture env → graduate → cake-gate verify.
//!
//! Every fixture theorem goes through the REAL kernel `add_decl` path (no
//! `add_decl_structural`), so the pilot exercises genuine type-checking,
//! genuine axiom-closure classification, and genuine shard round-trips.
//! v2 additions: definition-carrying graduation (carry, cascade-on-failure,
//! axiom-laundering rejection, tamper evidence, v1-record back-compat, and a
//! full native-environment conversion re-run of GRADUATION #1).

use std::path::{Path, PathBuf};

use clean_kernel::inductive::{Constructor as IndConstructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};

use super::intake::{
    graduate, graduate_with_base, graduate_with_base_keep_env, CertificateCrossCheck,
    GraduationBaseline, GraduationRequest, RecheckBase,
};
use super::record::{
    expr_canonical_digest, graduation_record_path, AxiomClosure, CarriedDefinition,
    CarriedInductive, CarriedInductiveConstructor, CarriedInductiveMember, CarriedTheorem,
    CorpusPin, EvidenceClass, GateInfo, GraduatedTheorem, GraduationRecord, GraduationResult,
    KernelFacts, KernelVerdict, NoveltyFacts, NoveltyMatchKind, NoveltyVerdict, OnDuplicate,
    PolicyInfo, ProjectInfo, RunProvenance, GRADUATION_MIN_TRUST, GRADUATION_NOTE_PREFIX,
    GRADUATION_SCHEMA_VERSION, GRADUATION_SCHEMA_VERSION_V1, GRADUATION_SCHEMA_VERSION_V2,
    GRADUATION_SCHEMA_VERSION_V3, GRADUATION_SCHEMA_VERSION_V31,
};
use crate::export::kernel_export::{InductiveFamilyMemberExport, KernelShardBuilder};
use crate::provenance::{add_provenance, ProvenanceBuilder, ProvenanceSidecar};
use crate::shard::ShardReader;
use crate::shard_verify::cake_gate::{
    verify_cake_shard, verify_cake_shard_fused, CakeGateError, CakeGateViolation,
};
use crate::types::{DeclKind, ImportConfidence, SourceSystem};

// The focused files below are spliced with `include!` (not `mod`) so that
// every test keeps its pre-split `graduate::tests::*` fully-qualified name —
// the test-name set is pinned byte-identical across the split
// (`cargo test -p clean-mathverse --lib graduate -- --list`).
include!("support.rs");
include!("record.rs");
include!("intake.rs");
include!("cake_gate.rs");
include!("adversarial.rs");
include!("v2_carried.rs");
include!("v3_family.rs");
include!("v3_binder_info.rs");
include!("v3_adversarial.rs");
include!("v3_native.rs");
include!("v31_carried_theorems.rs");
include!("v31_adversarial.rs");
include!("v32_shadow.rs");
include!("determinism.rs");

// The sweep harness is a self-contained inner module (its own imports), so a
// plain `mod` keeps it out of the include!-splice name-pinning above.
mod sweep_census;
