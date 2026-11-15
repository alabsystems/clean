// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The owned-formula-schema registry ([`OwnedFormulaSchema`]) is DERIVED, not
//! kept by hand.
//!
//! The one-formula rule is decided per schema, and only for a schema trust-ir
//! reads; a schema trust-ir owns but the registry omits would be treated as
//! opaque — its rendering never compared with its payload — which is exactly
//! how `trust-ir.Pred@1` escaped the rule while `smtlib2` was held to it.
//! So this census reads the sources and the wire registry and requires:
//!
//! * every schema a `ProofFormula` carries or is compared against anywhere
//!   in the workspace sources, when it is spelled in trust-ir's own namespace
//!   (`trust-ir.` / `trust_ir.`, test scratch space aside) or is `smtlib2`,
//!   has a registry variant — and every variant is carried somewhere;
//! * every versioned owned schema has a LANDED row in `wire-allocations.toml`,
//!   and every row there that binds a formula schema is a registry variant.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use trust_ir::proof::OwnedFormulaSchema;

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn rust_sources(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            rust_sources(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
}

/// Every `src/` file of every workspace crate (the frontend's included).
fn workspace_sources() -> Vec<(PathBuf, String)> {
    let root = workspace_root();
    let mut files = Vec::new();
    for base in ["crates", "frontend/crates"] {
        let Ok(crates) = std::fs::read_dir(root.join(base)) else {
            continue;
        };
        for krate in crates.flatten() {
            rust_sources(&krate.path().join("src"), &mut files);
        }
    }
    rust_sources(&root.join("frontend/src"), &mut files);
    files.sort();
    files
        .into_iter()
        .map(|path| {
            let text = std::fs::read_to_string(&path).expect("read source");
            (path, text)
        })
        .collect()
}

/// An identifier path or a string literal at the start of `text` (after
/// whitespace): `Some(("ident", false))` or `Some(("lit", true))`.
fn leading_operand(text: &str) -> Option<(&str, bool)> {
    let text = text.trim_start();
    if let Some(rest) = text.strip_prefix('"') {
        return rest.find('"').map(|end| (&rest[..end], true));
    }
    let end = text
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == ':'))
        .unwrap_or(text.len());
    let ident = &text[..end];
    (!ident.is_empty() && ident.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_'))
        .then_some((ident, false))
}

/// `const NAME: &str = "VALUE";` definitions, by NAME (the value may sit on
/// the next line).
fn string_constants(sources: &[(PathBuf, String)]) -> BTreeMap<String, BTreeSet<String>> {
    let mut constants: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (_, text) in sources {
        for (at, _) in text.match_indices("const ") {
            let rest = &text[at + "const ".len()..];
            let Some((name, rest)) = rest.split_once(':') else {
                continue;
            };
            let name = name.trim();
            if name.is_empty() || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
                continue;
            }
            let Some(rest) = rest.trim_start().strip_prefix("&str") else {
                continue;
            };
            let Some(rest) = rest.trim_start().strip_prefix('=') else {
                continue;
            };
            if let Some((value, true)) = leading_operand(rest) {
                constants
                    .entry(name.to_string())
                    .or_default()
                    .insert(value.to_string());
            }
        }
    }
    constants
}

/// Every operand a formula schema is carried as or compared with: the first
/// argument of `ProofFormula::new(`, the `schema:` field of a `ProofFormula {`
/// literal (and of `Self {` inside `impl ProofFormula`), and the right side of
/// `formula.schema ==`/`!=` and `f.schema ==`/`!=`.
fn schema_operands(sources: &[(PathBuf, String)]) -> Vec<(String, String, bool)> {
    let mut operands = Vec::new();
    let mut push = |path: &Path, operand: Option<(&str, bool)>| {
        if let Some((text, literal)) = operand {
            operands.push((path.display().to_string(), text.to_string(), literal));
        }
    };
    for (path, text) in sources {
        for (at, _) in text.match_indices("ProofFormula::new(") {
            push(
                path,
                leading_operand(&text[at + "ProofFormula::new(".len()..]),
            );
        }
        for opener in ["ProofFormula {", "ProofFormula{"] {
            for (at, _) in text.match_indices(opener) {
                let body = &text[at + opener.len()..];
                let body = &body[..body.find('}').unwrap_or(body.len())];
                if let Some(field) = body.find("schema:") {
                    push(path, leading_operand(&body[field + "schema:".len()..]));
                }
            }
        }
        if let Some(start) = text.find("impl ProofFormula {") {
            let tail = &text[start..];
            let end = tail[1..].find("\nimpl ").map_or(tail.len(), |end| end + 1);
            for (at, _) in tail[..end].match_indices("Self {") {
                let body = &tail[at + "Self {".len()..];
                let body = &body[..body.find('}').unwrap_or(body.len())];
                if let Some(field) = body.find("schema:") {
                    push(path, leading_operand(&body[field + "schema:".len()..]));
                }
            }
        }
        for receiver in ["formula.schema", "f.schema"] {
            for (at, _) in text.match_indices(receiver) {
                let rest = text[at + receiver.len()..].trim_start();
                if let Some(rest) = rest.strip_prefix("==").or_else(|| rest.strip_prefix("!=")) {
                    push(path, leading_operand(rest));
                }
            }
        }
    }
    operands
}

/// A schema trust-ir owns by its spelling: `smtlib2`, or trust-ir's own
/// namespace outside the unallocated test scratch space.
fn spelled_as_owned(schema: &str) -> bool {
    schema == "smtlib2"
        || ((schema.starts_with("trust-ir.") || schema.starts_with("trust_ir."))
            && !schema.starts_with("trust-ir.test.")
            && !schema.starts_with("trust_ir.test."))
}

#[test]
fn every_formula_schema_trust_ir_spells_is_registered() {
    let sources = workspace_sources();
    assert!(
        sources.len() > 50,
        "the source scan found {} files",
        sources.len()
    );
    let constants = string_constants(&sources);
    let mut carried: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut unresolved = Vec::new();
    for (path, operand, literal) in schema_operands(&sources) {
        let values: Vec<String> = if literal {
            vec![operand]
        } else {
            let name = operand.rsplit("::").next().unwrap_or(&operand);
            // Only a SCREAMING_CASE name is a constant; a variable (a parsed
            // or copied schema), a type or `_` names no schema.
            if !name.starts_with(|c: char| c.is_ascii_uppercase())
                || name.chars().any(|c| c.is_ascii_lowercase())
            {
                continue;
            }
            match constants.get(name) {
                Some(values) => values.iter().cloned().collect(),
                None => {
                    unresolved.push(format!("{path}: {operand}"));
                    continue;
                }
            }
        };
        for value in values {
            carried.entry(value).or_default().insert(path.clone());
        }
    }
    assert!(
        unresolved.is_empty(),
        "a formula schema constant the census cannot resolve: {unresolved:#?}"
    );
    let owned_by_spelling: BTreeSet<&str> = carried
        .keys()
        .map(String::as_str)
        .filter(|schema| spelled_as_owned(schema))
        .collect();
    let registered: BTreeSet<&str> = OwnedFormulaSchema::ALL
        .iter()
        .map(|owned| owned.name())
        .collect();
    let unregistered: Vec<_> = owned_by_spelling.difference(&registered).collect();
    assert!(
        unregistered.is_empty(),
        "a ProofFormula carries a schema in trust-ir's namespace that OwnedFormulaSchema does \
         not register, so the one-formula rule would treat it as opaque: {unregistered:?} \
         (carried in {:?})",
        unregistered
            .iter()
            .map(|schema| &carried[**schema])
            .collect::<Vec<_>>()
    );
    let uncarried: Vec<_> = registered.difference(&owned_by_spelling).collect();
    assert!(
        uncarried.is_empty(),
        "OwnedFormulaSchema registers a schema no ProofFormula carries: {uncarried:?}"
    );
    // Anti-vacuity: the scan sees foreign schemas too, so it read real
    // constructions rather than only the registry's own spellings.
    assert!(
        carried.contains_key("trust-types.Formula@1"),
        "the scan did not see ProofFormula::trust_types_json's schema: {:?}",
        carried.keys().collect::<Vec<_>>()
    );
}

/// `domain`/`version`/`status`/`binds` of every `digest_domain` row.
fn wire_rows() -> Vec<BTreeMap<String, String>> {
    let text = std::fs::read_to_string(workspace_root().join("wire-allocations.toml"))
        .expect("read wire-allocations.toml");
    let field = |line: &str, key: &str| -> Option<String> {
        let at = line.find(&format!("{key} = "))? + key.len() + 3;
        let rest = &line[at..];
        if let Some(rest) = rest.strip_prefix('"') {
            return rest.find('"').map(|end| rest[..end].to_string());
        }
        let end = rest.find([',', ' ', '}']).unwrap_or(rest.len());
        Some(rest[..end].to_string())
    };
    text.lines()
        .filter(|line| line.trim_start().starts_with("{ domain = "))
        .map(|line| {
            ["domain", "version", "status", "binds"]
                .into_iter()
                .filter_map(|key| field(line, key).map(|value| (key.to_string(), value)))
                .collect()
        })
        .collect()
}

#[test]
fn every_versioned_owned_schema_is_a_landed_wire_row_and_back() {
    let rows = wire_rows();
    assert!(rows.len() > 20, "read {} digest_domain rows", rows.len());
    let spelled = |row: &BTreeMap<String, String>| format!("{}.v{}", row["domain"], row["version"]);
    for owned in OwnedFormulaSchema::ALL {
        let name = owned.name();
        let Some((_, version)) = name.rsplit_once(".v") else {
            continue;
        };
        if !version.bytes().all(|b| b.is_ascii_digit()) {
            continue;
        }
        let row = rows.iter().find(|row| spelled(row) == name);
        assert!(
            row.is_some_and(|row| row["status"] == "landed"),
            "{owned:?} ({name}) has no landed digest_domain row"
        );
    }
    let registered: BTreeSet<&str> = OwnedFormulaSchema::ALL
        .iter()
        .map(|owned| owned.name())
        .collect();
    let formula_rows: Vec<String> = rows
        .iter()
        .filter(|row| {
            let binds = row.get("binds").map_or(String::new(), |b| b.to_lowercase());
            binds.contains("schema") && binds.contains("formula")
        })
        .map(spelled)
        .filter(|name| !name.starts_with("ty.") && !name.starts_with("ay."))
        .collect();
    assert!(
        !formula_rows.is_empty(),
        "no digest_domain row binds a formula schema: the row filter is vacuous"
    );
    for name in &formula_rows {
        assert!(
            registered.contains(name.as_str()),
            "wire-allocations.toml binds formula schema {name}, which OwnedFormulaSchema does \
             not register"
        );
    }
}
