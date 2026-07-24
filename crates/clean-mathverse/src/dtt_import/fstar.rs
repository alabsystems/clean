// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! F* extraction format parser for DTT imports.
//!
//! Parses F* extraction output (`--extract` / `--dump_module`) and converts
//! declarations to [`DttDeclaration`] with effect detection and universe mapping.
//!
//! Pure effects (`Tot`, `GTot`) translate directly. Effectful computations
//! (`ST`, `ML`, `Lemma`, `Div`) are axiomatized since clean is purely total.
//! F*'s CIC-family type theory reuses patterns from the Coq importer.

use crate::error::MathverseError;
use crate::types::AxiomProfile;

use super::split_top_level_arrow;
use super::types::{DttDeclaration, DttExpr, DttSystem, FstarExtraction};

/// Effects that are pure (no axiomatization needed).
const PURE_EFFECTS: &[&str] = &["Tot", "GTot", "Pure"];

/// Effects that require axiomatization (side-effectful or divergent).
const EFFECTFUL_KEYWORDS: &[&str] = &[
    "ST",
    "ML",
    "Lemma",
    "Div",
    "Exn",
    "All",
    "Stack",
    "Heap",
    "HyperStack",
    "HyperHeap",
    "Ghost",
];

/// Parse F* extraction output into DTT declarations.
///
/// Expects a JSON array of extraction entries. Each entry should have at
/// minimum `"name"` and `"type"` fields.
///
/// # Errors
///
/// Returns `MathverseError::Json` if the input is not valid JSON, or
/// `MathverseError::ImportFailed` if required fields are missing.
pub fn parse_fstar_extraction(input: &str) -> Result<Vec<DttDeclaration>, MathverseError> {
    let entries = parse_fstar_entries(input)?;
    let mut decls = Vec::with_capacity(entries.len());

    for entry in &entries {
        let type_expr = parse_fstar_type(&entry.type_str);
        let value_expr = entry.def_str.as_deref().map(parse_fstar_value);
        let is_axiom = entry.is_assumed || entry.def_str.is_none();
        let has_effect = detect_effect(entry);

        let mut profile = AxiomProfile::NONE;
        if is_axiom {
            profile |= AxiomProfile::AXIOMATIZED;
        }
        if has_effect {
            profile |= AxiomProfile::AXIOMATIZED;
        }

        decls.push(DttDeclaration {
            name: entry.name.clone(),
            type_expr,
            value_expr,
            system: DttSystem::Fstar,
            axiom_profile: profile,
            is_axiom,
            source_file: None,
            module_name: entry.module.clone(),
        });
    }

    Ok(decls)
}

/// Parse F* entries from raw JSON or text format.
fn parse_fstar_entries(input: &str) -> Result<Vec<FstarExtraction>, MathverseError> {
    let trimmed = input.trim();

    // Try JSON array format.
    if trimmed.starts_with('[') {
        let raw: Vec<serde_json::Value> = serde_json::from_str(trimmed)?;
        return raw.iter().map(value_to_fstar_extraction).collect();
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
            entries.push(value_to_fstar_extraction(&val)?);
        }
        return Ok(entries);
    }

    // Fall back to text format.
    parse_fstar_text(trimmed)
}

/// Convert a JSON value to an [`FstarExtraction`].
fn value_to_fstar_extraction(val: &serde_json::Value) -> Result<FstarExtraction, MathverseError> {
    let name = val
        .get("name")
        .and_then(|v| v.as_str())
        .ok_or_else(|| MathverseError::ImportFailed {
            system: "F*".to_owned(),
            reason: "missing 'name' field".to_owned(),
        })?
        .to_owned();

    let type_str = val
        .get("type")
        .and_then(|v| v.as_str())
        .unwrap_or("Type")
        .to_owned();

    let def_str = val
        .get("definition")
        .or_else(|| val.get("def"))
        .and_then(|v| v.as_str())
        .map(|s| s.to_owned());

    let is_assumed = val
        .get("isAssumed")
        .or_else(|| val.get("assume"))
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    let effect = val
        .get("effect")
        .and_then(|v| v.as_str())
        .map(|s| s.to_owned());

    let module = val
        .get("module")
        .and_then(|v| v.as_str())
        .map(|s| s.to_owned());

    Ok(FstarExtraction {
        name,
        type_str,
        def_str,
        is_assumed,
        effect,
        module,
    })
}

/// Parse simple text format: `val name : type` or `let name : type = def`.
fn parse_fstar_text(input: &str) -> Result<Vec<FstarExtraction>, MathverseError> {
    let mut entries = Vec::new();

    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with("//") || line.starts_with("(*") {
            continue;
        }

        // `assume val name : type`
        if let Some(rest) = line
            .strip_prefix("assume val ")
            .or_else(|| line.strip_prefix("assume "))
        {
            if let Some((name, type_str)) = rest.split_once(" : ") {
                entries.push(FstarExtraction {
                    name: name.trim().to_owned(),
                    type_str: type_str.trim().to_owned(),
                    def_str: None,
                    is_assumed: true,
                    effect: None,
                    module: None,
                });
            }
            continue;
        }

        // `val name : type`
        if let Some(rest) = line.strip_prefix("val ") {
            if let Some((name, type_str)) = rest.split_once(" : ") {
                entries.push(FstarExtraction {
                    name: name.trim().to_owned(),
                    type_str: type_str.trim().to_owned(),
                    def_str: None,
                    is_assumed: false,
                    effect: detect_effect_in_type(type_str),
                    module: None,
                });
            }
            continue;
        }

        // `let name : type = def`
        if let Some(rest) = line.strip_prefix("let ") {
            if let Some((name_and_type, def)) = rest.split_once(" = ") {
                if let Some((name, type_str)) = name_and_type.split_once(" : ") {
                    entries.push(FstarExtraction {
                        name: name.trim().to_owned(),
                        type_str: type_str.trim().to_owned(),
                        def_str: Some(def.trim().to_owned()),
                        is_assumed: false,
                        effect: detect_effect_in_type(type_str),
                        module: None,
                    });
                }
            }
            continue;
        }

        // Generic `name : type [= def]`
        if let Some((name_part, rest)) = line.split_once(" : ") {
            let name = name_part.trim();
            if !name.is_empty() && !name.contains(' ') {
                let (type_str, def_str) = if let Some((ty, def)) = rest.split_once(" = ") {
                    (ty.trim().to_owned(), Some(def.trim().to_owned()))
                } else {
                    (rest.trim().to_owned(), None)
                };
                entries.push(FstarExtraction {
                    name: name.to_owned(),
                    type_str: type_str.clone(),
                    def_str,
                    is_assumed: false,
                    effect: detect_effect_in_type(&type_str),
                    module: None,
                });
            }
        }
    }

    Ok(entries)
}

/// Parse an F* type string into a DTT expression.
///
/// F* types are similar to Lean/Coq (CIC family). Basic translation:
/// - `Type` / `Type0` -> `Sort(0)`
/// - `a -> b` -> `Pi _ : a, b`
/// - Named references stay as `Var`
fn parse_fstar_type(type_str: &str) -> DttExpr {
    let trimmed = type_str.trim();

    // Universe: Type, Type0, Type u, etc.
    if let Some(level) = parse_fstar_universe(trimmed) {
        return DttExpr::Sort(level);
    }

    // Prop (maps to Sort 0 in CIC convention).
    if trimmed == "prop" || trimmed == "Prop" {
        return DttExpr::Sort(0);
    }

    // Arrow types: a -> b
    if let Some((domain, codomain)) = split_top_level_arrow(trimmed) {
        return DttExpr::Pi {
            binder_name: "_".to_owned(),
            domain: Box::new(parse_fstar_type(domain)),
            codomain: Box::new(parse_fstar_type(codomain)),
        };
    }

    // Simple name (no spaces, no parens).
    if !trimmed.contains(' ') && !trimmed.contains('(') && !trimmed.is_empty() {
        return DttExpr::var(trimmed);
    }

    DttExpr::opaque(trimmed)
}

/// Parse an F* value string into a DTT expression.
fn parse_fstar_value(def_str: &str) -> DttExpr {
    let trimmed = def_str.trim();
    if trimmed.is_empty() {
        return DttExpr::opaque("");
    }

    // Lambda: fun (x: t) -> body
    if let Some(rest) = trimmed.strip_prefix("fun ") {
        if let Some((params, body)) = rest.split_once("->") {
            let param = params.trim().trim_matches(|c| c == '(' || c == ')');
            let binder_name = param.split(':').next().unwrap_or("_").trim().to_owned();
            return DttExpr::Lam {
                binder_name,
                binder_type: Box::new(DttExpr::opaque("_")),
                body: Box::new(parse_fstar_value(body.trim())),
            };
        }
    }

    if !trimmed.contains(' ') && !trimmed.contains('(') {
        DttExpr::var(trimmed)
    } else {
        DttExpr::opaque(trimmed)
    }
}

/// Detect whether an F* entry has non-pure effects.
fn detect_effect(entry: &FstarExtraction) -> bool {
    if let Some(ref effect) = entry.effect {
        if PURE_EFFECTS.contains(&effect.as_str()) {
            return false;
        }
        for kw in EFFECTFUL_KEYWORDS {
            if effect.contains(kw) {
                return true;
            }
        }
    }

    // Check type string for effect annotations.
    detect_effect_in_type(&entry.type_str).is_some()
        && !PURE_EFFECTS.contains(
            &detect_effect_in_type(&entry.type_str)
                .unwrap_or_default()
                .as_str(),
        )
}

/// Detect an effect keyword in a type string.
fn detect_effect_in_type(type_str: &str) -> Option<String> {
    for kw in EFFECTFUL_KEYWORDS {
        if type_str.contains(kw) {
            return Some((*kw).to_owned());
        }
    }
    for kw in PURE_EFFECTS {
        if type_str.contains(kw) {
            return Some((*kw).to_owned());
        }
    }
    None
}

/// Parse F* universe: `Type`, `Type0`, `Type 0`, `eqtype`, `Type u`.
fn parse_fstar_universe(s: &str) -> Option<u32> {
    if s == "Type" || s == "Type0" || s == "Type 0" {
        return Some(0);
    }
    if s == "eqtype" {
        return Some(0);
    }
    if let Some(rest) = s.strip_prefix("Type ") {
        if let Ok(n) = rest.trim().parse::<u32>() {
            return Some(n);
        }
    }
    if let Some(rest) = s.strip_prefix("Type") {
        if let Ok(n) = rest.trim().parse::<u32>() {
            return Some(n);
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
    fn test_parse_fstar_json_basic() {
        let input = r#"[
            {"name": "nat", "type": "Type"},
            {"name": "zero", "type": "nat"},
            {"name": "succ", "type": "nat -> nat", "definition": "fun n -> n + 1"}
        ]"#;
        let decls = parse_fstar_extraction(input).expect("parse");
        assert_eq!(decls.len(), 3);
        assert_eq!(decls[0].name, "nat");
        assert_eq!(decls[0].type_expr, DttExpr::Sort(0));
    }

    #[test]
    fn test_parse_fstar_assumed() {
        let input = r#"[
            {"name": "magic", "type": "a -> b", "isAssumed": true}
        ]"#;
        let decls = parse_fstar_extraction(input).expect("parse");
        assert_eq!(decls.len(), 1);
        assert!(decls[0].is_axiom);
        assert!(decls[0].axiom_profile.has(AxiomProfile::AXIOMATIZED));
    }

    #[test]
    fn test_parse_fstar_effect_st() {
        let input = r#"[
            {"name": "read_ref", "type": "ref a -> ST a", "effect": "ST"}
        ]"#;
        let decls = parse_fstar_extraction(input).expect("parse");
        assert_eq!(decls.len(), 1);
        assert!(decls[0].axiom_profile.has(AxiomProfile::AXIOMATIZED));
    }

    #[test]
    fn test_parse_fstar_pure_effect() {
        let input = r#"[
            {"name": "add", "type": "nat -> nat -> nat", "definition": "fun x y -> x + y", "effect": "Tot"}
        ]"#;
        let decls = parse_fstar_extraction(input).expect("parse");
        assert_eq!(decls.len(), 1);
        assert!(!decls[0].is_axiom);
        // Tot is pure, so no AXIOMATIZED bit.
        assert!(!decls[0].axiom_profile.has(AxiomProfile::AXIOMATIZED));
    }

    #[test]
    fn test_parse_fstar_text_val() {
        let input = "val add : nat -> nat -> nat\nassume val magic : a -> b\n";
        let decls = parse_fstar_extraction(input).expect("parse");
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].name, "add");
        // `val` without `= def` has no definition body, so treated as axiom.
        assert!(decls[0].is_axiom);
        assert!(decls[0].axiom_profile.has(AxiomProfile::AXIOMATIZED));
        assert_eq!(decls[1].name, "magic");
        assert!(decls[1].is_axiom);
        assert!(decls[1].axiom_profile.has(AxiomProfile::AXIOMATIZED));
    }

    #[test]
    fn test_parse_fstar_text_let() {
        let input = "let id : a -> a = fun x -> x\n";
        let decls = parse_fstar_extraction(input).expect("parse");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "id");
        assert!(decls[0].has_value());
    }

    #[test]
    fn test_parse_fstar_universe() {
        assert_eq!(parse_fstar_universe("Type"), Some(0));
        assert_eq!(parse_fstar_universe("Type0"), Some(0));
        assert_eq!(parse_fstar_universe("Type 0"), Some(0));
        assert_eq!(parse_fstar_universe("Type 1"), Some(1));
        assert_eq!(parse_fstar_universe("eqtype"), Some(0));
        assert_eq!(parse_fstar_universe("nat"), None);
    }

    #[test]
    fn test_parse_fstar_type_arrow() {
        let expr = parse_fstar_type("nat -> bool");
        match expr {
            DttExpr::Pi {
                domain, codomain, ..
            } => {
                assert_eq!(*domain, DttExpr::var("nat"));
                assert_eq!(*codomain, DttExpr::var("bool"));
            }
            _ => panic!("expected Pi, got {expr:?}"),
        }
    }

    #[test]
    fn test_parse_fstar_type_prop() {
        assert_eq!(parse_fstar_type("Prop"), DttExpr::Sort(0));
    }

    fn make_entry(name: &str, type_str: &str, effect: Option<&str>) -> FstarExtraction {
        FstarExtraction {
            name: name.to_owned(),
            type_str: type_str.to_owned(),
            def_str: None,
            is_assumed: false,
            effect: effect.map(|s| s.to_owned()),
            module: None,
        }
    }

    #[test]
    fn test_detect_effect_variants() {
        assert!(!detect_effect(&make_entry(
            "add",
            "nat -> Tot nat",
            Some("Tot")
        )));
        assert!(detect_effect(&make_entry(
            "read",
            "ref a -> ST a",
            Some("ST")
        )));
        assert!(detect_effect(&make_entry(
            "div",
            "unit -> Div nat",
            Some("Div")
        )));
        assert!(!detect_effect(&make_entry("pure", "a -> a", None)));
    }

    #[test]
    fn test_parse_fstar_edge_cases() {
        // NDJSON
        let ndjson = "{\"name\": \"a\", \"type\": \"Type\"}\n{\"name\": \"b\", \"type\": \"Type\"}";
        assert_eq!(parse_fstar_extraction(ndjson).expect("ndjson").len(), 2);
        // Missing name
        assert!(parse_fstar_extraction(r#"[{"type": "Type"}]"#).is_err());
        // Empty
        assert!(parse_fstar_extraction("[]").expect("empty").is_empty());
    }

    #[test]
    fn test_parse_fstar_value_lambda() {
        let expr = parse_fstar_value("fun (x: nat) -> x");
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
