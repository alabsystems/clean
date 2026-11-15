// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `clean-compiler-unvalidated` codegen license, and the read-only views
//! of an emitted module an object lane needs to link it (LX0 of
//! `designs/2026-09-30-clean-trust-unified-vision.md`, §2.3 and §5).
//!
//! # The license
//!
//! The emitter stamps every body `BodyGate::Ungated` (see the "Codegen
//! license" section of [`crate::emit_trust_ir`]), and a v41 consumer refuses
//! such a body unconditionally. The design names a grade below `gate`:
//! `unvalidated`, authority [`CLEAN_COMPILER_UNVALIDATED_AUTHORITY`], minted
//! only after the core's fail-closed self-checks pass. It claims NOTHING about
//! the body; it discloses a trust in Clean's compiler. Decision OD1, which
//! would make it a product lane, is recorded as delegated and provisional, so
//! the callers are the EXPERIMENTAL `clean run --backend trust-cg` and explicit
//! `clean compile --emit obj` paths, compiled only under the non-default
//! `trust-ir-backend` feature. No default
//! path mints it, and trust-cg recognizes it only when told to
//! (`--recognize-authority clean-compiler-unvalidated`).
//!
//! [`restamp_ungated_as_unvalidated`] is narrow on purpose:
//!
//! * it mints exactly one authority, a constant: there is no free-form
//!   authority parameter to launder another claim through;
//! * it re-stamps only `Some(Ungated)` bodies. A body that already carries a
//!   `Gated` claim (the TV pass's `clean-kernel-tv`) keeps it, and is counted;
//! * a body with NO claim (`None`, the pre-v41 state trust-cg permits by
//!   default) is an error. It is never re-stamped, and this module never
//!   writes `None`: that would launder the body into trust-cg's permissive
//!   claim-less default;
//! * bodyless declarations are not codegen subjects and are left alone.
//!
//! Minting only on a module every self-check accepted is the caller's duty;
//! `clean-cli`'s `native_trustcg` holds that witness.

use std::collections::BTreeMap;

use thiserror::Error;
use trust_ir::ty::Ty;
use trust_ir::{BodyGate, Function};

/// The emitted module type, named for callers outside this crate (an object
/// lane passes it between its steps without depending on trust-ir itself).
pub use trust_ir::Module;

/// The gate authority of the `unvalidated` grade (design §2.3): the core's
/// self-checks passed, and nothing is claimed about the body.
pub const CLEAN_COMPILER_UNVALIDATED_AUTHORITY: &str = "clean-compiler-unvalidated";

/// What [`restamp_ungated_as_unvalidated`] did, body by body.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LicenseCensus {
    /// Bodies re-stamped `Gated { clean-compiler-unvalidated }`.
    pub unvalidated: usize,
    /// Bodies that already carried a `Gated` claim, by authority, kept as is.
    pub kept: BTreeMap<String, usize>,
}

/// Why the license could not be minted.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum LaneLicenseError {
    /// A function has a body but no licensing claim at all.
    #[error(
        "function `{0}` has a body but no licensing claim (`body_gate: None`); the \
         clean-compiler-unvalidated lane never licenses a claim-less body"
    )]
    ClaimLessBody(String),
}

/// Re-stamp every `Ungated` body `Gated { clean-compiler-unvalidated }`.
///
/// All or nothing: a claim-less body is reported before anything is
/// rewritten, so on `Err` the module is exactly as it was.
pub fn restamp_ungated_as_unvalidated(
    module: &mut Module,
) -> Result<LicenseCensus, LaneLicenseError> {
    let mut census = LicenseCensus::default();
    for function in module.functions.iter().filter(|f| !f.blocks.is_empty()) {
        match &function.body_gate {
            Some(BodyGate::Ungated) => census.unvalidated += 1,
            Some(BodyGate::Gated { authority, .. }) => {
                *census.kept.entry(authority.clone()).or_default() += 1;
            }
            None => return Err(LaneLicenseError::ClaimLessBody(function.name.clone())),
        }
    }
    for function in module
        .functions
        .iter_mut()
        .filter(|f| !f.blocks.is_empty() && f.body_gate == Some(BodyGate::Ungated))
    {
        // No `GateEvidence` (trust-ir v61): this grade claims nothing about
        // the body, so there is no certified row or judged body for evidence
        // to name. Evidence belongs to evidence-bound authorities such as
        // `clean-kernel-tv`, whose minter stamps it in the same step.
        function.body_gate = Some(BodyGate::Gated {
            authority: CLEAN_COMPILER_UNVALIDATED_AUTHORITY.to_owned(),
            evidence: None,
        });
    }
    Ok(census)
}

/// One slot of a function signature as a C link sees it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbiSlot {
    /// A thin pointer: the boxed `clean_obj*` every runtime value travels as.
    Ptr,
    /// Any other trust-ir type, spelled for a diagnostic.
    Other(String),
}

/// A function's link symbol and its signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkSignature {
    /// The link-time symbol (`Function::name`, normative since v41).
    pub symbol: String,
    /// Parameter slots, in order.
    pub params: Vec<AbiSlot>,
    /// Result slots.
    pub returns: Vec<AbiSlot>,
    /// Whether the declaration is variadic.
    pub vararg: bool,
}

fn slot(ty: &Ty) -> AbiSlot {
    match ty {
        Ty::Ptr => AbiSlot::Ptr,
        other => AbiSlot::Other(format!("{other:?}")),
    }
}

fn signature(module: &Module, function: &Function) -> LinkSignature {
    match module.func_type(function.ty) {
        Some(ft) => LinkSignature {
            symbol: function.name.clone(),
            params: ft.params.iter().map(slot).collect(),
            returns: ft.returns.iter().map(slot).collect(),
            vararg: ft.is_vararg,
        },
        // `validate_module` refuses a dangling type id, so a finalized module
        // never reaches this arm; if one did, every check that reads these
        // slots refuses `Other`, which is the fail-closed answer.
        None => LinkSignature {
            symbol: function.name.clone(),
            params: vec![AbiSlot::Other("unresolved function type".to_owned())],
            returns: vec![AbiSlot::Other("unresolved function type".to_owned())],
            vararg: false,
        },
    }
}

/// Every bodyless declaration: exactly what an object compiled from `module`
/// leaves for the link to resolve.
#[must_use]
pub fn bodyless_declarations(module: &Module) -> Vec<LinkSignature> {
    module
        .functions
        .iter()
        .filter(|f| f.blocks.is_empty())
        .map(|f| signature(module, f))
        .collect()
}

/// The signature of the function DEFINED (with a body) under `symbol`.
#[must_use]
pub fn defined_signature(module: &Module, symbol: &str) -> Option<LinkSignature> {
    module
        .functions
        .iter()
        .find(|f| !f.blocks.is_empty() && f.name == symbol)
        .map(|f| signature(module, f))
}

/// Integer carriers admitted by the experimental direct C scalar boundary.
/// This is a structural check, never declaration or native proof authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarWord {
    /// An unsigned 32-bit integer.
    U32,
    /// An unsigned 64-bit integer.
    U64,
}

impl ScalarWord {
    fn ty(self) -> Ty {
        match self {
            Self::U32 => Ty::U32,
            Self::U64 => Ty::U64,
        }
    }
}

/// Cross-check a native consumer's scalar prototype against its exact emitted
/// definition. The caller must independently establish source custody/type
/// identity and run ordinary module/object checks. Recorded foreign ABI modes,
/// attributes, varargs, alternate conventions and bodyless entries refuse.
/// No legacy `abi: None` record is promoted into a target-ABI certificate.
pub fn check_scalar_c_signature(
    module: &Module,
    symbol: &str,
    params: &[ScalarWord],
    result: ScalarWord,
) -> Result<(), String> {
    let mut definitions = module.functions.iter().filter(|f| f.name == symbol);
    let function = definitions
        .next()
        .ok_or_else(|| format!("scalar entry `{symbol}` is absent"))?;
    let signature = module
        .func_type(function.ty)
        .ok_or("scalar entry type is absent")?;
    let expected: Vec<Ty> = params.iter().map(|slot| slot.ty()).collect();
    if definitions.next().is_some()
        || function.blocks.is_empty()
        || function.calling_conv != trust_ir::CallingConv::C
        || function.linkage != trust_ir::Linkage::External
        || function.visibility != trust_ir::Visibility::Default
        || !function.attrs.is_empty()
        || signature.is_vararg
        || signature.abi.is_some()
        || signature.params != expected
        || signature.returns != [result.ty()]
    {
        return Err(format!("scalar C signature refused for `{symbol}`: expected {expected:?} -> {:?}, a unique defined C body with no ABI overrides; actual {signature:?}", result.ty()));
    }
    Ok(())
}

/// Normative link symbols of every function defined with a body. This is a
/// structural observation, not a native object or declaration certificate.
#[must_use]
pub fn defined_symbols(module: &Module) -> Vec<String> {
    module
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty())
        .map(|f| f.name.clone())
        .collect()
}

#[cfg(test)]
#[path = "emit_trust_ir_lane_tests.rs"]
mod tests;
