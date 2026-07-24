// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared types for structured spec-annotation extraction.
//!
//! Every extractor (Rust verification, Scala verification, Move Prover,
//! Boogie/Viper/VeriFast) produces `Vec<StructuredDecl>` records that capture
//! the function/spec name, declaration kind, annotation content, and source
//! location.

use serde::{Deserialize, Serialize};

use crate::types::SourceSystem;

// ---------------------------------------------------------------------------
// DeclKind
// ---------------------------------------------------------------------------

/// Classification of a spec-annotation declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum DeclKind {
    /// A proof function (Verus `proof fn`, Stainless `def lemma`).
    ProofFn,
    /// A specification function (Verus `spec fn`, Move `spec fun`).
    SpecFn,
    /// A broadcast proof function (Verus `broadcast proof fn`).
    BroadcastProofFn,
    /// A `requires(...)` / `#[requires(...)]` precondition.
    Requires,
    /// An `ensures(...)` / `#[ensures(...)]` postcondition.
    Ensures,
    /// A `#[kani::proof]` or similar proof harness annotation.
    ProofHarness,
    /// An `assume(...)` / `kani::assume(...)` assumption.
    Assume,
    /// An `assert(...)` / `kani::assert(...)` assertion.
    Assert,
    /// A `#[variant(...)]` termination measure.
    Variant,
    /// A `#[logic]` / `#[pure]` / `#[trusted]` annotation.
    LogicAnnotation,
    /// A Scala `require(...)` precondition.
    ScalaRequire,
    /// A Scala `ensuring(...)` postcondition.
    ScalaEnsuring,
    /// A `@opaque` / `@extern` Stainless annotation.
    StainlessAnnotation,
    /// A Move `aborts_if` specification.
    AbortsIf,
    /// A Move `spec module { ... }` block.
    SpecModule,
    /// A Boogie `axiom expr;` declaration.
    Axiom,
    /// A Boogie/Viper `procedure`/`method` declaration.
    Procedure,
    /// A Boogie/Viper `function` declaration.
    Function,
    /// A Boogie `type` declaration.
    TypeDecl,
    /// A Viper `predicate` declaration.
    Predicate,
    /// A Viper `domain { ... }` declaration.
    Domain,
    /// A VeriFast specification comment (`//@` or `/*@...@*/`).
    SpecComment,
    /// A VeriFast `lemma` declaration.
    Lemma,
    /// A Scala `Theorem` or `Lemma` (LISA).
    Theorem,
    /// A Scala `val`/`def` declaration (LISA).
    ValDef,
}

// ---------------------------------------------------------------------------
// StructuredDecl
// ---------------------------------------------------------------------------

/// A single extracted spec-annotation declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StructuredDecl {
    /// The name of the declared item (function, spec, axiom, etc.).
    pub name: String,
    /// The kind of declaration.
    pub kind: DeclKind,
    /// The annotation content or signature string.
    /// For attributes like `#[requires(x > 0)]`, this is `"x > 0"`.
    /// For declarations like `proof fn foo(...)`, this is the full signature.
    pub spec_content: String,
    /// Source file path where this declaration was found.
    pub source_file: String,
    /// Source line number (1-based), if available.
    pub source_line: Option<u32>,
    /// Which verification tool produced this declaration.
    pub source_system: SourceSystem,
}
