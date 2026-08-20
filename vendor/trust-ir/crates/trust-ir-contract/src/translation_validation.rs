// trust-ir-contract/translation_validation: refinement-check data records
//
// The *data* shared across the Trust <-> backend boundary: what a single
// source->target refinement check asserts. The heavyweight machinery that
// operates on these (SimulationRelation, the MIR-walking helpers, and
// `RefinementVc::to_vc` which builds a VerificationCondition) stays in
// trust-types — it depends on the full MIR/VC layer and is not part of the
// cross-repo contract. trust-types re-exports these three types and provides
// `to_vc` via the `RefinementVcToVc` extension trait so existing call sites
// (`rvc.to_vc()`) are unchanged.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{BlockId, Formula};

/// A single translation validation check between a source and target program point.
///
/// Each check asserts that the target behavior at `target_point` refines the
/// source behavior at `source_point` under the simulation relation's variable mapping.
#[derive(Debug, Clone)]
pub struct TranslationCheck {
    /// Source (MIR) program point.
    pub source_point: BlockId,
    /// Target (optimized/compiled) program point.
    pub target_point: BlockId,
    /// What this check validates.
    pub kind: CheckKind,
    /// The formula asserting refinement at this point.
    pub formula: Formula,
    /// Human-readable description.
    pub description: String,
}

/// What aspect of translation a check validates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckKind {
    /// Control flow: target preserves source CFG reachability.
    ControlFlow,
    /// Data flow: target assignments refine source assignments.
    DataFlow,
    /// Termination: target terminates if source terminates.
    Termination,
    /// Return value: target return matches source return.
    ReturnValue,
}

/// A refinement verification condition: asserts that the target program
/// refines the source program at a particular point.
#[derive(Debug, Clone)]
pub struct RefinementVc {
    /// The translation check that generated this VC.
    pub check: TranslationCheck,
    /// The source function name.
    pub source_function: String,
    /// The target function name.
    pub target_function: String,
}
