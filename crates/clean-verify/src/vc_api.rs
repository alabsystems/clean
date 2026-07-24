// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! External verification-condition API for clean-verify integrations.

use crate::{
    vc_artifact::SourceLocation,
    vc_protocol::{
        SmtLib2Translator, VcProtocolError, VcTranslator,
        VerificationCondition as BackendVerificationCondition,
    },
};
use clean_elab::elaborate;
use clean_kernel::{Environment, Expr, TypeChecker};
use clean_parser::parse_expr;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Context attached to a verification condition for reporting and routing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcContext {
    /// Source location where the verification condition originated.
    pub source: SourceLocation,
    /// Function or item associated with the verification condition.
    pub function_name: String,
    /// Human-readable description of the obligation.
    pub description: String,
}

/// A single verification condition exposed to external backends.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerificationCondition {
    /// Assumptions that must hold before discharging the postcondition.
    pub preconditions: Vec<Expr>,
    /// Goal proposition to establish under the preconditions.
    pub postcondition: Expr,
    /// Source and descriptive metadata for the obligation.
    pub context: VcContext,
}

impl VerificationCondition {
    /// Reconstruct the VC as an implication chain `p1 -> ... -> postcondition`.
    pub fn to_expr(&self) -> Expr {
        self.preconditions
            .iter()
            .rev()
            .fold(self.postcondition.clone(), |acc, pre| {
                Expr::arrow(pre.clone(), acc)
            })
    }
}

/// String-based verification-condition input received from an external tool.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcExternalInput {
    /// Language or tool syntax used in the raw clauses.
    pub source_language: String,
    /// Function or item name associated with the submitted VCs.
    pub function_name: String,
    /// Raw preconditions supplied by the external tool.
    pub preconditions: Vec<String>,
    /// Raw postconditions supplied by the external tool.
    pub postconditions: Vec<String>,
    /// Raw loop or inductive invariants supplied by the external tool.
    pub invariants: Vec<String>,
}

impl VcExternalInput {
    /// Construct a new string-based external VC input.
    #[must_use]
    pub fn new(
        source_language: impl Into<String>,
        function_name: impl Into<String>,
        preconditions: Vec<String>,
        postconditions: Vec<String>,
        invariants: Vec<String>,
    ) -> Self {
        Self {
            source_language: source_language.into(),
            function_name: function_name.into(),
            preconditions,
            postconditions,
            invariants,
        }
    }
}

/// Alias retained because some callers use the `ExternalVcInput` spelling.
pub type ExternalVcInput = VcExternalInput;

/// Result of asking a backend to discharge a verification condition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum VcResult {
    /// The backend established that the verification condition is valid.
    Valid,
    /// The backend found a counterexample demonstrating invalidity.
    Invalid { counterexample: String },
    /// The backend could not determine validity.
    Unknown { reason: String },
    /// The backend timed out.
    Timeout,
}

/// Errors produced while converting external string VCs into kernel expressions.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum VcConversionError {
    /// External VC did not identify a function or item name.
    #[error("external VC must include a non-empty function name")]
    MissingFunctionName,
    /// External VC did not contain any obligations to check.
    #[error("external VC must include at least one invariant or postcondition")]
    MissingObligations,
    /// One clause was empty or whitespace.
    #[error("{section} clause {index} is empty")]
    EmptyClause {
        /// Clause section name.
        section: &'static str,
        /// Clause index in that section.
        index: usize,
    },
    /// Lean parsing failed for a clause.
    #[error("failed to parse {section} clause {index} as Lean: {message}")]
    Parse {
        /// Clause section name.
        section: &'static str,
        /// Clause index in that section.
        index: usize,
        /// Parser error message.
        message: String,
    },
    /// Lean elaboration failed for a clause.
    #[error("failed to elaborate {section} clause {index} as Lean: {message}")]
    Elab {
        /// Clause section name.
        section: &'static str,
        /// Clause index in that section.
        index: usize,
        /// Elaborator error message.
        message: String,
    },
}

/// Result type for external VC conversion.
pub type VcConversionResult<T> = Result<T, VcConversionError>;

/// Errors produced while exporting external VCs for other tools.
#[derive(Debug, Error)]
pub enum VcExportError {
    /// JSON serialization failed.
    #[error("failed to serialize VC as JSON: {0}")]
    Json(#[source] serde_json::Error),
    /// SMT-LIB2 translation failed.
    #[error("failed to serialize VC as SMT-LIB2: {0}")]
    SmtLib2(#[source] VcProtocolError),
}

/// Export formats supported for string-boundary VCs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VcExportFormat {
    /// Compact JSON encoding.
    Json,
    /// Minimal protobuf wire encoding.
    Protobuf,
    /// SMT-LIB2 text suitable for solver-oriented backends.
    SmtLib2,
}

impl VcExportFormat {
    /// Serialize one external VC in the requested format.
    pub fn serialize(&self, input: &ExternalVcInput) -> Result<Vec<u8>, VcExportError> {
        match self {
            Self::Json => serde_json::to_vec(input).map_err(VcExportError::Json),
            Self::Protobuf => Ok(encode_external_vc(input)),
            Self::SmtLib2 => Ok(render_smtlib2(input)?.into_bytes()),
        }
    }

    /// Serialize a batch of external VCs in the requested format.
    pub fn serialize_batch(&self, inputs: &[ExternalVcInput]) -> Result<Vec<u8>, VcExportError> {
        match self {
            Self::Json => serde_json::to_vec(inputs).map_err(VcExportError::Json),
            Self::Protobuf => Ok(encode_external_vc_batch(inputs)),
            Self::SmtLib2 => {
                let mut rendered = Vec::with_capacity(inputs.len());
                for input in inputs {
                    rendered.push(render_smtlib2(input)?);
                }
                Ok(rendered.join("\n\n").into_bytes())
            }
        }
    }
}

/// Interface for VC backends used by external integrations.
pub trait VcBackend {
    /// Attempt to discharge a single verification condition.
    fn check_vc(&self, vc: &VerificationCondition) -> VcResult;
}

/// Interface used by external tools to submit string-based VCs into clean-verify.
pub trait ExternalVcProvider {
    /// Submit one external VC input and receive kernel-level VCs to check or export.
    fn submit_external_vc(
        &self,
        input: &ExternalVcInput,
    ) -> VcConversionResult<Vec<VerificationCondition>>;

    /// Submit several external VC inputs and preserve request order.
    fn submit_external_batch(
        &self,
        inputs: &[ExternalVcInput],
    ) -> VcConversionResult<Vec<VerificationCondition>> {
        let mut vcs = Vec::new();
        for input in inputs {
            vcs.extend(self.submit_external_vc(input)?);
        }
        Ok(vcs)
    }
}

/// Converts string-boundary VCs into kernel `Expr` obligations.
#[derive(Clone, Debug)]
pub struct VcConversionPipeline<'env> {
    env: &'env Environment,
    default_source: SourceLocation,
}

impl<'env> VcConversionPipeline<'env> {
    /// Create a conversion pipeline over an existing kernel environment.
    #[must_use]
    pub fn new(env: &'env Environment) -> Self {
        Self {
            env,
            default_source: SourceLocation::default(),
        }
    }

    /// Attach a default source location used for generated VC contexts.
    #[must_use]
    pub fn with_source(mut self, source: SourceLocation) -> Self {
        self.default_source = source;
        self
    }

    /// Convert one external VC input into kernel `Expr`-based verification conditions.
    pub fn convert(
        &self,
        input: &ExternalVcInput,
    ) -> VcConversionResult<Vec<VerificationCondition>> {
        let function_name = input.function_name.trim();
        if function_name.is_empty() {
            return Err(VcConversionError::MissingFunctionName);
        }
        if input.postconditions.is_empty() && input.invariants.is_empty() {
            return Err(VcConversionError::MissingObligations);
        }

        let preconditions = self.convert_section(input, "precondition", &input.preconditions)?;
        let invariants = self.convert_section(input, "invariant", &input.invariants)?;
        let postconditions = self.convert_section(input, "postcondition", &input.postconditions)?;

        let mut vcs = Vec::with_capacity(invariants.len() + postconditions.len());
        for (index, invariant) in invariants.iter().enumerate() {
            vcs.push(self.build_vc(
                function_name,
                format!("invariant {}", index + 1),
                preconditions.clone(),
                invariant.clone(),
            ));
        }

        let mut post_preconditions = preconditions;
        post_preconditions.extend(invariants);
        for (index, postcondition) in postconditions.into_iter().enumerate() {
            vcs.push(self.build_vc(
                function_name,
                format!("postcondition {}", index + 1),
                post_preconditions.clone(),
                postcondition,
            ));
        }
        Ok(vcs)
    }

    fn build_vc(
        &self,
        function_name: &str,
        description: String,
        preconditions: Vec<Expr>,
        postcondition: Expr,
    ) -> VerificationCondition {
        VerificationCondition {
            preconditions,
            postcondition,
            context: VcContext {
                source: self.default_source.clone(),
                function_name: function_name.to_string(),
                description,
            },
        }
    }

    fn convert_section(
        &self,
        input: &ExternalVcInput,
        section: &'static str,
        clauses: &[String],
    ) -> VcConversionResult<Vec<Expr>> {
        clauses
            .iter()
            .enumerate()
            .map(|(index, clause)| self.convert_clause(input, section, index, clause))
            .collect()
    }

    fn convert_clause(
        &self,
        input: &ExternalVcInput,
        section: &'static str,
        index: usize,
        clause: &str,
    ) -> VcConversionResult<Expr> {
        let trimmed = clause.trim();
        if trimmed.is_empty() {
            return Err(VcConversionError::EmptyClause { section, index });
        }
        if is_lean_source_language(&input.source_language) {
            let surface = parse_expr(trimmed).map_err(|err| VcConversionError::Parse {
                section,
                index,
                message: err.to_string(),
            })?;
            return elaborate(self.env, &surface).map_err(|err| VcConversionError::Elab {
                section,
                index,
                message: err.to_string(),
            });
        }

        Ok(Expr::const_str(&format!(
            "ExternalVc.{}.{}.{}.{}",
            sanitize_segment(&input.source_language, "external"),
            sanitize_segment(&input.function_name, "vc"),
            section,
            index + 1
        )))
    }
}

impl ExternalVcProvider for VcConversionPipeline<'_> {
    fn submit_external_vc(
        &self,
        input: &ExternalVcInput,
    ) -> VcConversionResult<Vec<VerificationCondition>> {
        self.convert(input)
    }
}

/// Stub backend that only checks whether the VC is a well-formed proposition.
///
/// It does NOT attempt to prove the proposition, so it never returns
/// [`VcResult::Valid`]: a well-formed Prop can still be false (e.g.
/// `True → False`). A well-formed VC yields [`VcResult::Unknown`]; an
/// ill-formed one also yields `Unknown` with the type error as the reason.
#[derive(Clone, Copy, Debug)]
pub struct KernelVcBackend<'env> {
    env: &'env Environment,
}

impl<'env> KernelVcBackend<'env> {
    /// Create a kernel-backed VC checker over an existing environment.
    #[must_use]
    pub fn new(env: &'env Environment) -> Self {
        Self { env }
    }
}

impl VcBackend for KernelVcBackend<'_> {
    fn check_vc(&self, vc: &VerificationCondition) -> VcResult {
        let tc = TypeChecker::new(self.env);
        let vc_expr = vc.to_expr();

        match tc.check_type(&vc_expr, &Expr::prop()) {
            // Type-checking the VC as a Prop only establishes that it is a
            // well-formed proposition, NOT that the proposition holds. A
            // well-formed Prop can still be false (e.g. `True → False`), so we
            // must not claim `Valid` without discharging an actual proof.
            Ok(()) => VcResult::Unknown {
                reason: "well-formed Prop but no proof attempted (kernel VC stub)".to_string(),
            },
            Err(err) => VcResult::Unknown {
                reason: format!("kernel VC stub could not type-check VC as Prop: {err}"),
            },
        }
    }
}

fn is_lean_source_language(source_language: &str) -> bool {
    matches!(
        source_language.trim().to_ascii_lowercase().as_str(),
        "lean" | "lean4" | "clean"
    )
}

fn sanitize_segment(segment: &str, fallback: &str) -> String {
    let cleaned = segment
        .trim()
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch.to_ascii_lowercase()
            } else {
                '_'
            }
        })
        .collect::<String>()
        .trim_matches('_')
        .to_string();
    if cleaned.is_empty() {
        fallback.to_string()
    } else {
        cleaned
    }
}

fn encode_external_vc(input: &ExternalVcInput) -> Vec<u8> {
    let mut out = Vec::new();
    encode_string_field(1, &input.source_language, &mut out);
    encode_string_field(2, &input.function_name, &mut out);
    for clause in &input.preconditions {
        encode_string_field(3, clause, &mut out);
    }
    for clause in &input.postconditions {
        encode_string_field(4, clause, &mut out);
    }
    for clause in &input.invariants {
        encode_string_field(5, clause, &mut out);
    }
    out
}

fn encode_external_vc_batch(inputs: &[ExternalVcInput]) -> Vec<u8> {
    let mut out = Vec::new();
    for input in inputs {
        let encoded = encode_external_vc(input);
        out.push(0x0A);
        encode_varint(encoded.len(), &mut out);
        out.extend(encoded);
    }
    out
}

fn render_smtlib2(input: &ExternalVcInput) -> Result<String, VcExportError> {
    SmtLib2Translator
        .translate(&BackendVerificationCondition::new(
            input.preconditions.clone(),
            input.postconditions.clone(),
            input.invariants.clone(),
        ))
        .map_err(VcExportError::SmtLib2)
}

fn encode_string_field(field_number: u8, value: &str, out: &mut Vec<u8>) {
    out.push((field_number << 3) | 2);
    encode_varint(value.len(), out);
    out.extend_from_slice(value.as_bytes());
}

fn encode_varint(mut value: usize, out: &mut Vec<u8>) {
    loop {
        let byte = (value & 0x7F) as u8;
        value >>= 7;
        if value == 0 {
            out.push(byte);
            break;
        }
        out.push(byte | 0x80);
    }
}

#[cfg(test)]
mod tests;
