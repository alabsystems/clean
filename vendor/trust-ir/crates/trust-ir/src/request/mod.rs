// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed native verification requests for in-process consumers.
//!
//! tRust can emit a `NativeVerificationBundle` when it already has native MIR
//! and TrustIr values in memory. TrustVc, TrustMc, and TrustWp then consume typed
//! request variants instead of stringly adapter names or ad hoc JSON payloads.
//!
//! This module is split into cohesive submodules; every public item is
//! re-exported here, so external paths such as
//! `crate::request::NativeVerificationBundle` resolve unchanged:
//!
//! * [`consts`] — schema-version, contract, and hardware-vector operation
//!   constants.
//! * [`facts`] — request ids, provenance, replay atoms, semantic-bridge and
//!   Petri-successor report families, and the native compiler-fact bundle.
//! * [`requests`] — typed TrustVc/TrustMc/TrustWp request options and the
//!   [`NativeVerificationRequest`] variant.
//! * [`evidence`] — native evidence artifacts, shared-primitive and
//!   hardware-vector contract descriptors, Petri handoff descriptors, transport
//!   identity, and the hand-rolled SHA-256 manifest-digest infrastructure.
//! * [`bundle`] — the [`NativeVerificationBundle`] aggregate and its
//!   [`NativeVerificationBundleError`] enum.
//! * [`coverage`] — the sealed [`NativeCoverageAttestation`] (per-obligation
//!   verified-solver-result citations, outside every digest), the replay
//!   context they bind
//!   (`NativeVerificationBundle::coverage_replay_context_digest`, `fmt`) and
//!   the [`NativeCoverageResultReplay`] seam a consumer re-verifies them with.
//! * [`digest`] — the stable-digest byte writers and the well-formedness
//!   validation routines.
//!
//! ## Why this module is large, and why it is retained
//!
//! This is the single largest module in the crate. An early audit proposed
//! deleting most of it; that recommendation was **refuted** — the request /
//! evidence / bundle schemas here are the cross-repo handshake that ty, ay, and
//! TrustCg actually consume (TrustVc/TrustMc/TrustWp requests, the native
//! verification bundle, the shared-primitive & hardware-vector contract
//! descriptors, and the manifest-digest infrastructure). Deleting it would break
//! those consumers. It was therefore *split* into the cohesive submodules above
//! (it was once one ~33k-line file) rather than reduced; the submodule list here
//! is the reviewable map of the contract surface. Changes to any schema in here
//! are cross-repo-visible and must be version-bumped, not edited in place.

use crate::ty::SetRepr;
use crate::value::{ClosureTyId, EnumId, FuncTyId, ImportId, RecordId, TyId};
use crate::{
    CastLayoutEvidence, CastOp, Constant, Endianness, FieldOffsetShape, FuncId, Function, Inst,
    LayoutError, Module, ObligationKind, PointerLayoutShape, PointerMetadataShape, Producer,
    ProofCertificate, ProofCertificateRef, ProofDigest, ProofDigestAlgorithm, ProofFormula,
    ProofId, ProofLineageError, ProofLineageId, ProofLineageManifest, ProofObligation,
    ProofReplayIdentity, ProofStatus, SourceSpan, StructId, TargetInfo, Ty, TyLayoutKind,
    TyLayoutShape, TyShape, ValueId,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

mod bundle;
mod consts;
mod coverage;
mod digest;
mod evidence;
mod facts;
mod observed_bundle_checks;
mod observed_compiler_facts;
mod observed_digest;
mod observed_error_retirement;
mod observed_evidence_artifacts;
mod observed_evidence_obligations;
mod observed_evidence_provenance;
mod observed_formula_inventory;
mod observed_identity_checks;
mod observed_identity_equality;
mod observed_identity_prefix;
#[cfg(not(feature = "clean-expr"))]
mod observed_kernel_less_bundle;
#[cfg(not(feature = "clean-expr"))]
mod observed_kernel_less_requests;
mod observed_pre_request;
mod observed_provenance;
mod observed_replay_context;
mod observed_request_certificates;
mod observed_request_lineage;
mod observed_request_metadata;
mod observed_request_modes;
mod observed_request_source;
mod observed_tool_name;
mod observed_vc_collisions;
mod observed_vc_shape;
mod observed_whole_evidence;
mod observed_wire_labels;
mod requests;
mod validated;

#[cfg(feature = "native-transport-json")]
pub mod transport;

#[cfg(feature = "native-validation-observer")]
pub mod validation_observer;

#[cfg(test)]
mod tests;

pub use bundle::*;
pub use consts::*;
pub use coverage::*;
pub use evidence::*;
pub use facts::*;
pub use requests::*;
pub use validated::*;
// `digest` holds only crate-internal stable-digest writers and validation
// helpers; re-export them at crate visibility so sibling submodules and the
// test module reach them, without widening the external surface.
pub(crate) use digest::*;

pub use observed_error_retirement::retire_native_bundle_errors_observed;
pub use observed_request_lineage::NativeRequestLineage;
pub(crate) use observed_tool_name::canonical_tool_name_observed;
