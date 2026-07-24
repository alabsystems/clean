// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enhanced `#print` command implementation.
//!
//! Provides rich declaration printing with support for:
//! - Structured output for different declaration kinds
//! - Full inductive type display with constructors and recursor info
//! - Constructor and recursor detail display
//! - Abbreviated body display for large definitions
//!
//! This module builds on the basic `elab_print` in `commands.rs` with
//! structured result types via `DeclKind` and `PrintResult`.

use crate::error::ElabError;
use clean_kernel::env::ConstantKind;
use clean_kernel::name::Name;
use clean_kernel::Environment;

/// Maximum characters to display for a definition/theorem body before
/// truncating with "...".
const MAX_BODY_DISPLAY: usize = 500;

/// The kind of declaration found in the environment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DeclKind {
    /// A definition with a computable body.
    Definition,
    /// A theorem (proof-irrelevant).
    Theorem,
    /// An axiom (no proof).
    Axiom,
    /// An opaque constant (hidden body).
    Opaque,
    /// An inductive type.
    Inductive,
    /// A constructor of an inductive type.
    Constructor,
    /// A recursor for an inductive type.
    Recursor,
}

impl std::fmt::Display for DeclKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Definition => write!(f, "def"),
            Self::Theorem => write!(f, "theorem"),
            Self::Axiom => write!(f, "axiom"),
            Self::Opaque => write!(f, "opaque"),
            Self::Inductive => write!(f, "inductive"),
            Self::Constructor => write!(f, "constructor"),
            Self::Recursor => write!(f, "recursor"),
        }
    }
}

/// Structured result of a `#print` command.
///
/// Contains the declaration kind, formatted signature, optional body,
/// and any attributes or annotations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrintResult {
    /// What kind of declaration this is.
    pub kind: DeclKind,
    /// The formatted type signature.
    pub signature: String,
    /// The body/value, if applicable (truncated for large definitions).
    pub body: Option<String>,
    /// Additional attributes or annotations.
    pub attributes: Vec<String>,
}

impl std::fmt::Display for PrintResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.kind, self.signature)?;
        if let Some(ref body) = self.body {
            write!(f, " :=\n  {body}")?;
        }
        for attr in &self.attributes {
            write!(f, "\n-- {attr}")?;
        }
        Ok(())
    }
}

/// Print a declaration by name from the environment.
///
/// Searches for the name across constants, inductives, constructors,
/// and recursors. Returns a structured [`PrintResult`] with full
/// declaration information.
///
/// # Errors
///
/// Returns [`ElabError::UnknownIdent`] if no declaration with that name
/// exists in the environment.
pub fn print_declaration(name: &str, env: &Environment) -> Result<PrintResult, ElabError> {
    let n = Name::from_string(name);

    // Try constant lookup first (definitions, theorems, axioms, opaques).
    if let Some(info) = env.get_const(&n) {
        return Ok(format_constant_result(name, info));
    }

    // Try inductive lookup.
    if let Some(ind) = env.get_inductive(&n) {
        return Ok(format_inductive_result(name, ind, env));
    }

    // Try constructor lookup.
    if let Some(ctor) = env.get_constructor(&n) {
        return Ok(format_constructor_result(name, ctor));
    }

    // Try recursor lookup.
    if let Some(rec) = env.get_recursor(&n) {
        return Ok(format_recursor_result(name, rec));
    }

    Err(ElabError::UnknownIdent(name.to_owned()))
}

/// Format a constant (def/theorem/axiom/opaque) into a `PrintResult`.
fn format_constant_result(name: &str, info: &clean_kernel::ConstantInfo) -> PrintResult {
    let kind = match info.kind {
        ConstantKind::Definition => DeclKind::Definition,
        ConstantKind::Theorem => DeclKind::Theorem,
        ConstantKind::Opaque => DeclKind::Opaque,
        ConstantKind::Axiom => DeclKind::Axiom,
    };

    let mut sig = String::new();
    sig.push_str(name);

    // Append universe parameters.
    if !info.level_params.is_empty() {
        sig.push_str(".{");
        for (i, p) in info.level_params.iter().enumerate() {
            if i > 0 {
                sig.push_str(", ");
            }
            sig.push_str(&format!("{p}"));
        }
        sig.push('}');
    }

    sig.push_str(" : ");
    sig.push_str(&format!("{}", info.type_));

    // Format body (truncated if too large).
    let body = info.value.as_ref().map(|val| {
        let val_str = format!("{val}");
        if val_str.len() > MAX_BODY_DISPLAY {
            format!("{}...", &val_str[..MAX_BODY_DISPLAY])
        } else {
            val_str
        }
    });

    let mut attributes = Vec::new();
    if info.is_reducible && kind == DeclKind::Definition {
        attributes.push("reducible".to_owned());
    }
    if !info.level_params.is_empty() {
        attributes.push(format!(
            "universe parameters: {}",
            info.level_params
                .iter()
                .map(|p| format!("{p}"))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }

    PrintResult {
        kind,
        signature: sig,
        body,
        attributes,
    }
}

/// Format an inductive type into a `PrintResult`.
fn format_inductive_result(
    name: &str,
    ind: &clean_kernel::InductiveVal,
    env: &Environment,
) -> PrintResult {
    let mut sig = String::new();
    sig.push_str(name);

    if !ind.level_params.is_empty() {
        sig.push_str(".{");
        for (i, p) in ind.level_params.iter().enumerate() {
            if i > 0 {
                sig.push_str(", ");
            }
            sig.push_str(&format!("{p}"));
        }
        sig.push('}');
    }

    sig.push_str(" : ");
    sig.push_str(&format!("{}", ind.type_));

    // Build constructor list as body.
    let mut body_parts = Vec::new();
    body_parts.push(format!("number of parameters: {}", ind.num_params));

    if ind.num_indices > 0 {
        body_parts.push(format!("number of indices: {}", ind.num_indices));
    }

    body_parts.push("constructors:".to_owned());
    for ctor_name in &ind.constructor_names {
        let ctor_type = env
            .get_constructor(ctor_name)
            .map(|c| format!(" : {}", c.type_))
            .unwrap_or_default();
        body_parts.push(format!("  {ctor_name}{ctor_type}"));
    }

    let mut attributes = Vec::new();
    if ind.is_recursive {
        attributes.push("recursive".to_owned());
    }
    if ind.is_reflexive {
        attributes.push("reflexive".to_owned());
    }
    if ind.is_nested {
        attributes.push("nested".to_owned());
    }

    PrintResult {
        kind: DeclKind::Inductive,
        signature: sig,
        body: Some(body_parts.join("\n")),
        attributes,
    }
}

/// Format a constructor into a `PrintResult`.
fn format_constructor_result(name: &str, ctor: &clean_kernel::ConstructorVal) -> PrintResult {
    let sig = format!("{name} : {}", ctor.type_);

    let mut attributes = Vec::new();
    attributes.push(format!("inductive: {}", ctor.inductive_name));
    attributes.push(format!("num_fields: {}", ctor.num_fields));
    attributes.push(format!("num_params: {}", ctor.num_params));

    PrintResult {
        kind: DeclKind::Constructor,
        signature: sig,
        body: None,
        attributes,
    }
}

/// Format a recursor into a `PrintResult`.
fn format_recursor_result(name: &str, rec: &clean_kernel::RecursorVal) -> PrintResult {
    let sig = format!("{name} : {}", rec.type_);

    let mut attributes = Vec::new();
    attributes.push(format!("inductive: {}", rec.inductive_name));
    attributes.push(format!("num_params: {}", rec.num_params));
    attributes.push(format!("num_indices: {}", rec.num_indices));
    attributes.push(format!("num_motives: {}", rec.num_motives));
    attributes.push(format!("num_minors: {}", rec.num_minors));
    attributes.push(format!("rules: {}", rec.rules.len()));
    if rec.is_k {
        attributes.push("K-like reduction".to_owned());
    }

    PrintResult {
        kind: DeclKind::Recursor,
        signature: sig,
        body: None,
        attributes,
    }
}

#[cfg(test)]
#[path = "print_cmd_tests.rs"]
mod tests;
