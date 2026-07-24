// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Idris 2 TT2 IR parser for DTT imports.
//!
//! Parses Idris 2's TT2 intermediate representation format and converts
//! declarations to [`DttDeclaration`] with QTT (quantitative type theory)
//! detection and universe mapping.
//!
//! ## TT2 IR format
//!
//! Idris 2's TT2 IR (from `--dumpcases` or `--dumplifted`) is a simplified
//! representation of compiled definitions. Each entry has:
//! - A qualified name
//! - A type in TT2 syntax
//! - An optional definition body
//! - Metadata (totality, visibility, multiplicity)
//!
//! ## QTT detection
//!
//! Idris 2 uses quantitative type theory: binders carry multiplicities
//! (`0`, `1`, or unrestricted). Declarations that use linear (`1`) or
//! erased (`0`) multiplicities are flagged with `AxiomProfile::IDRIS_QTT`,
//! since clean's type theory does not natively support QTT.
//!
//! ## Universe mapping
//!
//! Idris 2's `Type` maps to `Sort 0`, `Type 1` to `Sort 1`, etc.

use crate::error::MathverseError;
use crate::types::AxiomProfile;

use super::split_top_level_arrow;
use super::types::{DttDeclaration, DttExpr, DttSystem, IdrisTT, IdrisTotality};

/// QTT multiplicity keywords that trigger axiomatization.
const QTT_MARKERS: &[&str] = &[
    "(0 ",
    "(1 ",
    " 0 ",
    " 1 ",
    "lin ",
    "rig0 ",
    "rig1 ",
    "multiplicity",
    "Rig0",
    "Rig1",
    "RigW",
];

/// Parse Idris 2 TT2 IR into DTT declarations.
///
/// Expects a JSON array of TT2 entries. Each entry should have at minimum
/// `"name"` and `"type"` fields.
///
/// # Errors
///
/// Returns `MathverseError::Json` if the input is not valid JSON, or
/// `MathverseError::ImportFailed` if required fields are missing.
pub fn parse_idris_tt(input: &str) -> Result<Vec<DttDeclaration>, MathverseError> {
    let entries = parse_idris_entries(input)?;
    let mut decls = Vec::with_capacity(entries.len());

    for entry in &entries {
        let type_expr = parse_idris_type(&entry.type_tt);
        let value_expr = entry.def_tt.as_deref().map(parse_idris_value);
        let uses_qtt = detect_qtt(entry);
        let is_axiom = entry.is_postulate || entry.def_tt.is_none();

        let mut profile = AxiomProfile::NONE;
        if uses_qtt {
            profile |= AxiomProfile::IDRIS_QTT;
        }
        if is_axiom {
            profile |= AxiomProfile::AXIOMATIZED;
        }

        decls.push(DttDeclaration {
            name: entry.name.clone(),
            type_expr,
            value_expr,
            system: DttSystem::Idris2,
            axiom_profile: profile,
            is_axiom,
            source_file: None,
            module_name: entry.namespace.clone(),
        });
    }

    Ok(decls)
}

/// Parse Idris 2 TT2 entries from raw JSON or text format.
fn parse_idris_entries(input: &str) -> Result<Vec<IdrisTT>, MathverseError> {
    let trimmed = input.trim();

    // Try JSON array format.
    if trimmed.starts_with('[') {
        let raw: Vec<serde_json::Value> = serde_json::from_str(trimmed)?;
        return raw.iter().map(value_to_idris_tt).collect();
    }

    // Try NDJSON format.
    if trimmed.starts_with('{') {
        let mut entries = Vec::new();
        for line in trimmed.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let val: serde_json::Value = serde_json::from_str(line)?;
            entries.push(value_to_idris_tt(&val)?);
        }
        return Ok(entries);
    }

    // Fall back to simple text format: "name : type [= def]" per line.
    parse_idris_text(trimmed)
}

/// Convert a JSON value to an [`IdrisTT`].
fn value_to_idris_tt(val: &serde_json::Value) -> Result<IdrisTT, MathverseError> {
    let name = val
        .get("name")
        .and_then(|v| v.as_str())
        .ok_or_else(|| MathverseError::ImportFailed {
            system: "Idris2".to_owned(),
            reason: "missing 'name' field".to_owned(),
        })?
        .to_owned();

    let type_tt = val
        .get("type")
        .and_then(|v| v.as_str())
        .unwrap_or("Type")
        .to_owned();

    let def_tt = val
        .get("definition")
        .or_else(|| val.get("def"))
        .and_then(|v| v.as_str())
        .map(|s| s.to_owned());

    let is_postulate = val
        .get("isPostulate")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    let uses_qtt = val
        .get("usesQTT")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    let totality = val
        .get("totality")
        .and_then(|v| v.as_str())
        .and_then(parse_totality);

    let namespace = val
        .get("namespace")
        .or_else(|| val.get("module"))
        .and_then(|v| v.as_str())
        .map(|s| s.to_owned());

    Ok(IdrisTT {
        name,
        type_tt,
        def_tt,
        is_postulate,
        uses_qtt,
        totality,
        namespace,
    })
}

/// Parse simple text format: `name : type` or `name : type = def`.
fn parse_idris_text(input: &str) -> Result<Vec<IdrisTT>, MathverseError> {
    let mut entries = Vec::new();

    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with("--") || line.starts_with('#') {
            continue;
        }

        // Split on first ` : `
        let Some((name_part, rest)) = line.split_once(" : ") else {
            continue;
        };

        let name = name_part.trim().to_owned();
        if name.is_empty() {
            continue;
        }

        // Check for ` = ` in the rest (definition body).
        let (type_tt, def_tt) = if let Some((ty, def)) = rest.split_once(" = ") {
            (ty.trim().to_owned(), Some(def.trim().to_owned()))
        } else {
            (rest.trim().to_owned(), None)
        };

        let is_postulate = def_tt.is_none();

        entries.push(IdrisTT {
            name,
            type_tt: type_tt.clone(),
            def_tt,
            is_postulate,
            uses_qtt: type_tt.contains("(0 ") || type_tt.contains("(1 "),
            totality: None,
            namespace: None,
        });
    }

    Ok(entries)
}

/// Parse a TT2 type string into a DTT expression.
fn parse_idris_type(type_str: &str) -> DttExpr {
    let trimmed = type_str.trim();

    // Universe: Type, Type 1, Type 2, ...
    if let Some(level) = parse_type_level(trimmed) {
        return DttExpr::Sort(level);
    }

    // Arrow types: A -> B
    if let Some((domain, codomain)) = split_top_level_arrow(trimmed) {
        return DttExpr::Pi {
            binder_name: "_".to_owned(),
            domain: Box::new(parse_idris_type(domain)),
            codomain: Box::new(parse_idris_type(codomain)),
        };
    }

    // Simple name.
    if !trimmed.contains(' ') && !trimmed.contains('(') && !trimmed.is_empty() {
        return DttExpr::var(trimmed);
    }

    DttExpr::opaque(trimmed)
}

/// Parse a TT2 value string into a DTT expression.
fn parse_idris_value(def_str: &str) -> DttExpr {
    let trimmed = def_str.trim();
    if trimmed.is_empty() {
        return DttExpr::opaque("");
    }

    // Lambda: \x => body
    if let Some(rest) = trimmed.strip_prefix('\\') {
        if let Some((param, body)) = rest.split_once("=>") {
            return DttExpr::Lam {
                binder_name: param.trim().to_owned(),
                binder_type: Box::new(DttExpr::opaque("_")),
                body: Box::new(parse_idris_value(body.trim())),
            };
        }
    }

    if !trimmed.contains(' ') && !trimmed.contains('(') {
        DttExpr::var(trimmed)
    } else {
        DttExpr::opaque(trimmed)
    }
}

/// Detect whether an Idris 2 entry uses QTT features.
fn detect_qtt(entry: &IdrisTT) -> bool {
    if entry.uses_qtt {
        return true;
    }

    let haystack = format!(
        "{} {}",
        entry.type_tt,
        entry.def_tt.as_deref().unwrap_or("")
    );

    for marker in QTT_MARKERS {
        if haystack.contains(marker) {
            return true;
        }
    }

    false
}

/// Parse Idris 2 universe level: `Type` -> 0, `Type 1` -> 1, etc.
fn parse_type_level(s: &str) -> Option<u32> {
    if s == "Type" {
        return Some(0);
    }
    if let Some(rest) = s.strip_prefix("Type ") {
        if let Ok(n) = rest.trim().parse::<u32>() {
            return Some(n);
        }
    }
    None
}

/// Parse totality annotation string.
fn parse_totality(s: &str) -> Option<IdrisTotality> {
    match s {
        "total" | "Total" => Some(IdrisTotality::Total),
        "covering" | "Covering" => Some(IdrisTotality::Covering),
        "partial" | "Partial" => Some(IdrisTotality::Partial),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_idris_tt_json() {
        let input = r#"[
            {"name": "Nat", "type": "Type", "totality": "total"},
            {"name": "Z", "type": "Nat"},
            {"name": "S", "type": "Nat -> Nat"}
        ]"#;
        let decls = parse_idris_tt(input).expect("parse");
        assert_eq!(decls.len(), 3);
        assert_eq!(decls[0].name, "Nat");
        assert_eq!(decls[0].type_expr, DttExpr::Sort(0));
    }

    #[test]
    fn test_parse_idris_tt_postulate() {
        let input = r#"[
            {"name": "believe_me", "type": "a -> b", "isPostulate": true}
        ]"#;
        let decls = parse_idris_tt(input).expect("parse");
        assert_eq!(decls.len(), 1);
        assert!(decls[0].is_axiom);
        assert!(decls[0].axiom_profile.has(AxiomProfile::AXIOMATIZED));
    }

    #[test]
    fn test_parse_idris_tt_qtt() {
        let input = r#"[
            {"name": "linFn", "type": "(1 x : A) -> B x", "usesQTT": true}
        ]"#;
        let decls = parse_idris_tt(input).expect("parse");
        assert_eq!(decls.len(), 1);
        assert!(decls[0].is_qtt());
        assert!(decls[0].axiom_profile.has(AxiomProfile::IDRIS_QTT));
    }

    #[test]
    fn test_parse_idris_tt_with_definition() {
        let input = r#"[
            {"name": "id", "type": "a -> a", "definition": "\\x => x"}
        ]"#;
        let decls = parse_idris_tt(input).expect("parse");
        assert_eq!(decls.len(), 1);
        assert!(decls[0].has_value());
        assert!(!decls[0].is_axiom);
    }

    #[test]
    fn test_parse_idris_text_format() {
        let input = "add : Nat -> Nat -> Nat = plus\nmul : Nat -> Nat -> Nat";
        let decls = parse_idris_tt(input).expect("parse");
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].name, "add");
        assert!(decls[0].has_value());
        assert_eq!(decls[1].name, "mul");
        assert!(!decls[1].has_value());
    }

    #[test]
    fn test_parse_type_level() {
        assert_eq!(parse_type_level("Type"), Some(0));
        assert_eq!(parse_type_level("Type 1"), Some(1));
        assert_eq!(parse_type_level("Type 2"), Some(2));
        assert_eq!(parse_type_level("Nat"), None);
    }

    #[test]
    fn test_parse_idris_type_arrow() {
        let expr = parse_idris_type("Nat -> Bool");
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
    fn test_detect_qtt_by_marker() {
        let entry = IdrisTT {
            name: "linFn".to_owned(),
            type_tt: "(1 x : A) -> B".to_owned(),
            def_tt: None,
            is_postulate: true,
            uses_qtt: false,
            totality: None,
            namespace: None,
        };
        assert!(detect_qtt(&entry));
    }

    #[test]
    fn test_detect_non_qtt() {
        let entry = IdrisTT {
            name: "id".to_owned(),
            type_tt: "a -> a".to_owned(),
            def_tt: Some("\\x => x".to_owned()),
            is_postulate: false,
            uses_qtt: false,
            totality: Some(IdrisTotality::Total),
            namespace: None,
        };
        assert!(!detect_qtt(&entry));
    }

    #[test]
    fn test_parse_totality() {
        assert_eq!(parse_totality("total"), Some(IdrisTotality::Total));
        assert_eq!(parse_totality("covering"), Some(IdrisTotality::Covering));
        assert_eq!(parse_totality("partial"), Some(IdrisTotality::Partial));
        assert_eq!(parse_totality("unknown"), None);
    }

    #[test]
    fn test_parse_idris_tt_ndjson() {
        let input = r#"{"name": "A", "type": "Type"}
{"name": "B", "type": "Type"}"#;
        let decls = parse_idris_tt(input).expect("parse");
        assert_eq!(decls.len(), 2);
    }

    #[test]
    fn test_parse_idris_tt_missing_name() {
        let input = r#"[{"type": "Type"}]"#;
        let result = parse_idris_tt(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_idris_tt_empty() {
        let input = "[]";
        let decls = parse_idris_tt(input).expect("parse");
        assert!(decls.is_empty());
    }

    #[test]
    fn test_parse_idris_value_lambda() {
        let expr = parse_idris_value("\\x => x");
        match expr {
            DttExpr::Lam {
                binder_name, body, ..
            } => {
                assert_eq!(binder_name, "x");
                assert_eq!(*body, DttExpr::var("x"));
            }
            _ => panic!("expected Lam, got {expr:?}"),
        }
    }
}
