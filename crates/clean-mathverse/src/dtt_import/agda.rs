// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Agda JSON export parser for DTT imports.
//!
//! Parses Agda's `--interaction-json` output format and converts declarations
//! to [`DttDeclaration`] with cubical type detection and universe level mapping.
//!
//! ## Agda export format
//!
//! Agda's JSON interaction output provides declarations as objects with fields:
//! - `"name"`: fully qualified name
//! - `"type"`: pretty-printed type string
//! - `"definition"`: definition body (absent for postulates)
//! - `"kind"`: declaration kind (data, record, postulate, function, etc.)
//!
//! ## Cubical detection
//!
//! Cubical Agda primitives (`Glue`, `hcomp`, `transp`, `I`, `PathP`, etc.)
//! are detected by name prefix and keyword matching. Declarations that depend
//! on cubical features get `AxiomProfile::AGDA_CUBICAL` set, meaning they are
//! axiomatized in the Mathverse shard (clean's kernel does not natively support
//! cubical type theory).
//!
//! ## Universe mapping
//!
//! Agda's `Set`, `Set₁`, `Set₂`, ... map to clean `Sort 0`, `Sort 1`, `Sort 2`.
//! `Setω` is mapped to a large universe and flagged for review.

use crate::error::MathverseError;
use crate::types::AxiomProfile;

use super::split_top_level_arrow;
use super::types::{AgdaExport, DttDeclaration, DttExpr, DttSystem};

/// Cubical primitive name prefixes.
const CUBICAL_PREFIXES: &[&str] = &[
    "Agda.Primitive.Cubical.",
    "Agda.Builtin.Cubical.",
    "Cubical.",
];

/// Cubical type keywords in type signatures.
const CUBICAL_KEYWORDS: &[&str] = &[
    "PathP", "Path", "Glue", "hcomp", "transp", "I", "i0", "i1", "hfill", "glue", "unglue",
    "Partial", "PartialP", "Sub", "inS", "outS", "IsOne",
];

/// Parse Agda JSON export into DTT declarations.
///
/// Expects a JSON array of declaration objects. Each object should have
/// at minimum `"name"` and `"type"` fields.
///
/// # Errors
///
/// Returns `MathverseError::Json` if the input is not valid JSON, or
/// `MathverseError::ImportFailed` if required fields are missing.
pub fn parse_agda_json(input: &str) -> Result<Vec<DttDeclaration>, MathverseError> {
    let entries: Vec<AgdaExport> = parse_agda_entries(input)?;
    let mut decls = Vec::with_capacity(entries.len());

    for entry in &entries {
        let type_expr = parse_agda_type(&entry.type_str);
        let value_expr = entry.def_str.as_deref().map(parse_agda_value);
        let is_cubical = detect_cubical(entry);
        let is_axiom = entry.is_postulate || entry.def_str.is_none();

        let mut profile = AxiomProfile::NONE;
        if is_cubical {
            profile |= AxiomProfile::AGDA_CUBICAL;
        }
        if is_axiom {
            profile |= AxiomProfile::AXIOMATIZED;
        }

        decls.push(DttDeclaration {
            name: entry.name.clone(),
            type_expr,
            value_expr,
            system: DttSystem::Agda,
            axiom_profile: profile,
            is_axiom,
            source_file: None,
            module_name: entry.module.clone(),
        });
    }

    Ok(decls)
}

/// Parse Agda JSON entries from raw JSON text.
///
/// Supports two formats:
/// 1. A JSON array of export objects.
/// 2. Newline-delimited JSON objects (NDJSON).
fn parse_agda_entries(input: &str) -> Result<Vec<AgdaExport>, MathverseError> {
    let trimmed = input.trim();

    // Try array format first.
    if trimmed.starts_with('[') {
        let raw: Vec<serde_json::Value> = serde_json::from_str(trimmed)?;
        return raw.iter().map(value_to_agda_export).collect();
    }

    // Fall back to NDJSON (one object per line).
    let mut entries = Vec::new();
    for line in trimmed.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let val: serde_json::Value = serde_json::from_str(line)?;
        entries.push(value_to_agda_export(&val)?);
    }
    Ok(entries)
}

/// Convert a JSON value to an [`AgdaExport`].
fn value_to_agda_export(val: &serde_json::Value) -> Result<AgdaExport, MathverseError> {
    let name = val
        .get("name")
        .and_then(|v| v.as_str())
        .ok_or_else(|| MathverseError::ImportFailed {
            system: "Agda".to_owned(),
            reason: "missing 'name' field".to_owned(),
        })?
        .to_owned();

    let type_str = val
        .get("type")
        .and_then(|v| v.as_str())
        .unwrap_or("Set")
        .to_owned();

    let def_str = val
        .get("definition")
        .and_then(|v| v.as_str())
        .map(|s| s.to_owned());

    let kind = val.get("kind").and_then(|v| v.as_str()).unwrap_or("");
    let is_postulate = kind == "postulate"
        || val
            .get("isPostulate")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);

    let is_cubical = val
        .get("isCubical")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    let module = val
        .get("module")
        .and_then(|v| v.as_str())
        .map(|s| s.to_owned());

    let universe_level = parse_universe_level(&type_str);

    Ok(AgdaExport {
        name,
        type_str,
        def_str,
        is_postulate,
        is_cubical,
        module,
        universe_level,
    })
}

/// Parse a type string into a lightweight DTT expression.
///
/// This is a best-effort parser for Agda's pretty-printed types.
/// Complex expressions are wrapped in `DttExpr::Opaque`.
fn parse_agda_type(type_str: &str) -> DttExpr {
    let trimmed = type_str.trim();

    // Universe sorts: Set, Set₁, Set₂, Setω
    if let Some(level) = parse_set_level(trimmed) {
        return DttExpr::Sort(level);
    }

    // Simple arrow types: A -> B
    if let Some((domain, codomain)) = split_top_level_arrow(trimmed) {
        return DttExpr::Pi {
            binder_name: "_".to_owned(),
            domain: Box::new(parse_agda_type(domain)),
            codomain: Box::new(parse_agda_type(codomain)),
        };
    }

    // Simple name reference (no spaces, no parens).
    if !trimmed.contains(' ') && !trimmed.contains('(') && !trimmed.is_empty() {
        return DttExpr::var(trimmed);
    }

    DttExpr::opaque(trimmed)
}

/// Parse a definition body string into a DTT expression.
fn parse_agda_value(def_str: &str) -> DttExpr {
    let trimmed = def_str.trim();
    if trimmed.is_empty() {
        return DttExpr::opaque("");
    }

    // Simple lambda: \x -> body
    if let Some(rest) = trimmed
        .strip_prefix('\\')
        .or_else(|| trimmed.strip_prefix("λ"))
    {
        if let Some((param, body)) = rest.split_once("->") {
            let param = param.trim();
            let body = body.trim();
            return DttExpr::Lam {
                binder_name: param.to_owned(),
                binder_type: Box::new(DttExpr::opaque("_")),
                body: Box::new(parse_agda_value(body)),
            };
        }
    }

    // Simple name or complex expression.
    if !trimmed.contains(' ') && !trimmed.contains('(') {
        DttExpr::var(trimmed)
    } else {
        DttExpr::opaque(trimmed)
    }
}

/// Detect whether an Agda export uses cubical features.
fn detect_cubical(entry: &AgdaExport) -> bool {
    if entry.is_cubical {
        return true;
    }

    // Check name prefix.
    for prefix in CUBICAL_PREFIXES {
        if entry.name.starts_with(prefix) {
            return true;
        }
    }

    // Check type and definition for cubical keywords.
    let haystack = format!(
        "{} {}",
        entry.type_str,
        entry.def_str.as_deref().unwrap_or("")
    );
    for kw in CUBICAL_KEYWORDS {
        if haystack.contains(kw) {
            return true;
        }
    }

    false
}

/// Parse `Set`, `Set₁`, `Set₂`, `Setω` into universe levels.
///
/// Returns `None` if the string is not a Set-level expression.
fn parse_set_level(s: &str) -> Option<u32> {
    if s == "Set" || s == "Set₀" || s == "Set0" {
        return Some(0);
    }
    if s == "Setω" || s == "Setω₀" {
        // Setω maps to a large universe; use a sentinel.
        return Some(u32::MAX);
    }

    // Set₁, Set₂, ... using Unicode subscripts.
    if let Some(rest) = s.strip_prefix("Set") {
        // Try numeric suffix.
        if let Ok(n) = rest.parse::<u32>() {
            return Some(n);
        }
        // Try Unicode subscript digits.
        if let Some(level) = parse_subscript_digits(rest) {
            return Some(level);
        }
    }

    None
}

/// Parse Unicode subscript digits (₀₁₂₃₄₅₆₇₈₉) into a u32.
fn parse_subscript_digits(s: &str) -> Option<u32> {
    let mut result: u32 = 0;
    let mut found_any = false;
    for ch in s.chars() {
        let digit = match ch {
            '₀' => 0,
            '₁' => 1,
            '₂' => 2,
            '₃' => 3,
            '₄' => 4,
            '₅' => 5,
            '₆' => 6,
            '₇' => 7,
            '₈' => 8,
            '₉' => 9,
            _ => return None,
        };
        result = result.checked_mul(10)?.checked_add(digit)?;
        found_any = true;
    }
    if found_any {
        Some(result)
    } else {
        None
    }
}

/// Parse universe level from a type string (heuristic).
fn parse_universe_level(type_str: &str) -> Option<u32> {
    // Look for Set, Set₁, etc. anywhere in the type string.
    for word in type_str.split_whitespace() {
        if let Some(level) = parse_set_level(word) {
            return Some(level);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_agda_json_basic() {
        let input = r#"[
            {"name": "Nat", "type": "Set", "kind": "data"},
            {"name": "zero", "type": "Nat", "kind": "constructor"},
            {"name": "suc", "type": "Nat -> Nat", "kind": "constructor"}
        ]"#;
        let decls = parse_agda_json(input).expect("parse");
        assert_eq!(decls.len(), 3);
        assert_eq!(decls[0].name, "Nat");
        assert_eq!(decls[0].type_expr, DttExpr::Sort(0));
        assert!(!decls[0].is_cubical());
    }

    #[test]
    fn test_parse_agda_json_postulate() {
        let input = r#"[
            {"name": "trustMe", "type": "Set -> Set", "kind": "postulate"}
        ]"#;
        let decls = parse_agda_json(input).expect("parse");
        assert_eq!(decls.len(), 1);
        assert!(decls[0].is_axiom);
        assert!(decls[0].axiom_profile.has(AxiomProfile::AXIOMATIZED));
    }

    #[test]
    fn test_parse_agda_json_cubical() {
        let input = r#"[
            {"name": "Agda.Primitive.Cubical.primTransp", "type": "I -> Set", "kind": "postulate", "isCubical": true}
        ]"#;
        let decls = parse_agda_json(input).expect("parse");
        assert_eq!(decls.len(), 1);
        assert!(decls[0].is_cubical());
        assert!(decls[0].axiom_profile.has(AxiomProfile::AGDA_CUBICAL));
    }

    #[test]
    fn test_parse_agda_json_with_definition() {
        let input = r#"[
            {"name": "id", "type": "Set -> Set", "definition": "\\x -> x", "kind": "function"}
        ]"#;
        let decls = parse_agda_json(input).expect("parse");
        assert_eq!(decls.len(), 1);
        assert!(decls[0].has_value());
        assert!(!decls[0].is_axiom);
    }

    #[test]
    fn test_parse_agda_json_ndjson() {
        let input = r#"{"name": "A", "type": "Set"}
{"name": "B", "type": "Set"}"#;
        let decls = parse_agda_json(input).expect("parse");
        assert_eq!(decls.len(), 2);
    }

    #[test]
    fn test_parse_set_levels() {
        assert_eq!(parse_set_level("Set"), Some(0));
        assert_eq!(parse_set_level("Set₀"), Some(0));
        assert_eq!(parse_set_level("Set₁"), Some(1));
        assert_eq!(parse_set_level("Set₂"), Some(2));
        assert_eq!(parse_set_level("Set₁₂"), Some(12));
        assert_eq!(parse_set_level("Set0"), Some(0));
        assert_eq!(parse_set_level("Set1"), Some(1));
        assert_eq!(parse_set_level("Setω"), Some(u32::MAX));
        assert_eq!(parse_set_level("Nat"), None);
    }

    #[test]
    fn test_parse_agda_type_arrow() {
        let expr = parse_agda_type("Nat -> Bool");
        match expr {
            DttExpr::Pi {
                domain, codomain, ..
            } => {
                assert_eq!(*domain, DttExpr::var("Nat"));
                assert_eq!(*codomain, DttExpr::var("Bool"));
            }
            _ => panic!("expected Pi, got {expr:?}"),
        }
    }

    #[test]
    fn test_parse_agda_type_unicode_arrow() {
        let expr = parse_agda_type("Nat \u{2192} Bool");
        match expr {
            DttExpr::Pi {
                domain, codomain, ..
            } => {
                assert_eq!(*domain, DttExpr::var("Nat"));
                assert_eq!(*codomain, DttExpr::var("Bool"));
            }
            _ => panic!("expected Pi, got {expr:?}"),
        }
    }

    fn make_export(name: &str, type_str: &str, is_cubical: bool) -> AgdaExport {
        AgdaExport {
            name: name.to_owned(),
            type_str: type_str.to_owned(),
            def_str: None,
            is_postulate: false,
            is_cubical,
            module: None,
            universe_level: None,
        }
    }

    #[test]
    fn test_detect_cubical_variants() {
        // By prefix
        assert!(detect_cubical(&make_export(
            "Agda.Primitive.Cubical.primComp",
            "I -> Set",
            false,
        )));
        // By keyword in type
        assert!(detect_cubical(&make_export(
            "myFunc",
            "PathP (\\i -> Nat) x y",
            false,
        )));
        // By explicit flag
        assert!(detect_cubical(&make_export("x", "Set", true)));
        // Non-cubical
        assert!(!detect_cubical(&make_export(
            "Data.Nat.add",
            "Nat -> Nat -> Nat",
            false,
        )));
    }

    #[test]
    fn test_split_top_level_arrow_nested() {
        // Should not split inside parens.
        let result = split_top_level_arrow("(A -> B) -> C");
        assert!(result.is_some());
        let (domain, codomain) = result.unwrap();
        assert_eq!(domain, "(A -> B)");
        assert_eq!(codomain, "C");
    }

    #[test]
    fn test_parse_subscript_digits() {
        assert_eq!(parse_subscript_digits("₁₂₃"), Some(123));
        assert_eq!(parse_subscript_digits("₀"), Some(0));
        assert_eq!(parse_subscript_digits(""), None);
        assert_eq!(parse_subscript_digits("abc"), None);
    }

    #[test]
    fn test_parse_agda_json_missing_name() {
        let input = r#"[{"type": "Set"}]"#;
        let result = parse_agda_json(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_agda_json_empty_array() {
        let input = "[]";
        let decls = parse_agda_json(input).expect("parse");
        assert!(decls.is_empty());
    }
}
