// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! arXiv natural-language mathematics importer for the Mathverse Engine.
//!
//! Extracts theorem statements, definitions, and proofs from LaTeX source,
//! producing [`ArxivImportedConstant`] records with axiom profiles and trust
//! metadata for downstream formalization.
//!
//! ## Modules
//!
//! - [`types`]: Domain types for arXiv extraction
//! - [`parser`]: LaTeX parser for theorem/definition extraction
//! - [`importer`]: Mathverse Library constant producer (axiomatized)
//! - [`formalize`]: LLM-based formalization types and concept linking
//! - [`validation`]: Semantic alignment validation
//! - [`import_validation`]: Mathlib import whitelist validation and rewriting
//! - [`pipeline`]: End-to-end pipeline orchestration with error categorization
//! - [`mathverse_bridge`]: Export formalized results to `.mathverse` shard format

pub mod error_categories;
pub mod formalize;
pub(crate) mod formalize_prompt;
pub(crate) mod import_validation;
pub mod importer;
pub mod mathverse_bridge;
pub mod parser;
pub mod pipeline;
pub mod postprocess;
pub mod types;
pub mod validation;

pub use error_categories::{ErrorCategory, ErrorDistribution};
pub use formalize::{AdmissionTier, FormalizationResult, PaperFormalization};
pub use importer::{ArxivImportConfig, ArxivImportResult, ArxivImportedConstant, ArxivImporter};
pub use mathverse_bridge::{ArxivMathverseBridge, ArxivProvenance, ExportStats};
pub use pipeline::{BatchResult, PipelineConfig, PipelineStats};
pub use postprocess::postprocess_lean_code;
pub use types::{ArxivDefinition, ArxivPaper, ArxivTheorem, DefinitionKind, TheoremKind};
pub use validation::ValidationReport;
