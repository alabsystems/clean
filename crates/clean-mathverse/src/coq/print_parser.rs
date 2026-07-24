// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser for real Coq `Print` command output (from coqtop / Rocq).
//!
//! Converts textual output from `Print nat.`, `Print Nat.add.`, etc. into
//! s-expression strings that [`super::coq::CoqImporter::import_sexp`] and
//! [`super::coq::sexp_to_mutual_inductive`] can consume.

use crate::coq::alpha::{
    import_mutual_inductive, parse_sexp, sexp_to_mutual_inductive, CoqImporter,
};
use crate::coq::real_data::infer_module_path;
use crate::error::MathverseResult;
use crate::shard::ShardWriter;

// ---------------------------------------------------------------------------
// Part 1: Parsed representation of Coq Print output
// ---------------------------------------------------------------------------

/// A single definition extracted from Coq `Print` command output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoqPrintDef {
    /// An inductive type definition.
    Inductive {
        name: String,
        params: Vec<(String, String)>,
        sort: String,
        constructors: Vec<(String, String)>,
    },
    /// A constant or function definition (possibly with a body).
    Definition {
        name: String,
        type_str: String,
        body: Option<String>,
    },
    /// A notation alias (e.g., `Notation identity := @eq`).
    Notation { name: String, target: String },
}

/// Statistics from importing Coq Print output.
#[derive(Clone, Debug, Default)]
pub struct CoqPrintImportStats {
    pub inductives: u32,
    pub definitions: u32,
    pub axioms: u32,
    pub notations_skipped: u32,
    pub parse_failures: u32,
    pub import_failures: u32,
}

// ---------------------------------------------------------------------------
// Part 1 (cont.): Parser for Coq Print output
// ---------------------------------------------------------------------------

/// Parse Coq `Print` command output text into structured definitions.
///
/// Handles `Inductive`, definitions (`name = ...`), notations, and records.
/// Skips `Arguments`, `(where ...)`, and `[Loading ...]` lines.
pub fn parse_coq_print_output(text: &str) -> Vec<CoqPrintDef> {
    let lines: Vec<&str> = text.lines().collect();
    let mut defs = Vec::new();
    let mut i = 0;

    while i < lines.len() {
        let line = lines[i].trim();

        // Skip blank, loading, arguments, where lines.
        if line.is_empty()
            || line.starts_with("[Loading ")
            || line.starts_with("Arguments ")
            || line.starts_with("(where ")
        {
            i += 1;
            continue;
        }

        // Notation lines.
        if line.starts_with("Notation ") {
            if let Some(def) = parse_notation(line) {
                defs.push(def);
            }
            i += 1;
            continue;
        }

        // Record lines — treat as inductive with one constructor.
        if line.starts_with("Record ") {
            let (def, consumed) = parse_record(&lines, i);
            if let Some(d) = def {
                defs.push(d);
            }
            i += consumed;
            continue;
        }

        // Inductive definitions.
        if line.starts_with("Inductive ") {
            let (def, consumed) = parse_inductive(&lines, i);
            if let Some(d) = def {
                defs.push(d);
            }
            i += consumed;
            continue;
        }

        // Definition: `name = ...` or `name =\n...`
        // Check for pattern: a word (possibly with dots) followed by ` = ` or ` =\n`
        if let Some(def_result) = try_parse_definition(&lines, i) {
            defs.push(def_result.0);
            i += def_result.1;
            continue;
        }

        // Unrecognized line — skip.
        i += 1;
    }

    defs
}

/// Collect continuation lines (indented or specific patterns) starting after `start`.
fn collect_block(lines: &[&str], start: usize) -> (String, usize) {
    let mut block = String::new();
    let mut j = start;
    while j < lines.len() {
        let line = lines[j];
        // Continuation: starts with space/tab, or is a type annotation line.
        let trimmed = line.trim();
        if trimmed.is_empty() {
            break;
        }
        // Stop if we hit a new top-level definition.
        if !line.starts_with(' ') && !line.starts_with('\t') {
            // Check if this looks like a new definition start (not a continuation).
            if j > start
                && (trimmed.starts_with("Inductive ")
                    || trimmed.starts_with("Record ")
                    || trimmed.starts_with("Notation ")
                    || trimmed.starts_with("Arguments ")
                    || trimmed.starts_with("[Loading ")
                    || trimmed.starts_with("(where "))
            {
                break;
            }
            // Also break if this looks like a new `name = ` or `name :` definition.
            if j > start && looks_like_new_def(trimmed) {
                break;
            }
        }
        if !block.is_empty() {
            block.push(' ');
        }
        block.push_str(trimmed);
        j += 1;
    }
    (block, j - start)
}

/// Check if a line looks like the start of a new top-level definition.
fn looks_like_new_def(line: &str) -> bool {
    // Pattern: `identifier = ` or `identifier :`
    // An identifier can contain dots and underscores.
    let first_word_end = line.find([' ', '=', ':']).unwrap_or(line.len());
    if first_word_end == 0 || first_word_end >= line.len() {
        return false;
    }
    let first_word = &line[..first_word_end];
    // Must look like an identifier (alphanumeric, dots, underscores).
    if !first_word
        .chars()
        .all(|c| c.is_alphanumeric() || c == '.' || c == '_' || c == '\'')
    {
        return false;
    }
    let rest = line[first_word_end..].trim_start();
    rest.starts_with("= ") || rest.starts_with("=\n") || rest == "="
}

/// Parse a Notation line like `Notation identity := @eq`.
fn parse_notation(line: &str) -> Option<CoqPrintDef> {
    let rest = line.strip_prefix("Notation ")?;
    let parts: Vec<&str> = rest.splitn(3, " := ").collect();
    if parts.len() >= 2 {
        Some(CoqPrintDef::Notation {
            name: parts[0].trim().to_string(),
            target: parts[1].trim().to_string(),
        })
    } else {
        None
    }
}

/// Parse an Inductive definition spanning potentially multiple lines.
fn parse_inductive(lines: &[&str], start: usize) -> (Option<CoqPrintDef>, usize) {
    let (block, consumed) = collect_block(lines, start);

    // Strip trailing period if present.
    let block = block.strip_suffix('.').unwrap_or(&block);

    // Extract: `Inductive name (params) : sort := ctors`
    let rest = match block.strip_prefix("Inductive ") {
        Some(r) => r,
        None => return (None, consumed),
    };

    // Find the `:=` separator.
    let (before_def, after_def) = match rest.find(":=") {
        Some(pos) => (&rest[..pos], rest[pos + 2..].trim()),
        None => return (None, consumed),
    };

    // Parse `name (params) : sort` from before_def.
    let (name, params, sort) = parse_inductive_header(before_def.trim());

    // Parse constructors from after_def.
    let constructors = parse_constructors(after_def);

    (
        Some(CoqPrintDef::Inductive {
            name,
            params,
            sort,
            constructors,
        }),
        consumed,
    )
}

/// Parse the inductive header: `name (A : Type) (B : Prop) : Set`.
fn parse_inductive_header(header: &str) -> (String, Vec<(String, String)>, String) {
    let mut rest = header;

    // Extract name (first token).
    let name_end = rest.find([' ', '(', ':']).unwrap_or(rest.len());
    let name = rest[..name_end].trim().to_string();
    rest = rest[name_end..].trim();

    // Extract parameters in parentheses.
    let mut params = Vec::new();
    while rest.starts_with('(') {
        if let Some(close) = find_matching_paren(rest) {
            let param_str = &rest[1..close];
            // Parse `A : Type` or `A B : Type`
            if let Some(colon_pos) = param_str.find(':') {
                let names_str = param_str[..colon_pos].trim();
                let type_str = param_str[colon_pos + 1..].trim();
                for pname in names_str.split_whitespace() {
                    params.push((pname.to_string(), type_str.to_string()));
                }
            }
            rest = rest[close + 1..].trim();
        } else {
            break;
        }
    }

    // Extract sort after `:`.
    let sort = if let Some(colon_pos) = rest.find(':') {
        rest[colon_pos + 1..].trim().to_string()
    } else {
        "Type".to_string()
    };

    (name, params, sort)
}

/// Find the matching closing parenthesis for an opening `(` at position 0.
fn find_matching_paren(s: &str) -> Option<usize> {
    let mut depth = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Parse constructors from the text after `:=`.
/// Format: `CtorName : type | CtorName2 : type2` or multiline with `|`.
fn parse_constructors(text: &str) -> Vec<(String, String)> {
    let text = text.trim();
    if text.is_empty() {
        return Vec::new();
    }

    let mut ctors = Vec::new();

    // Split on ` | ` but be careful about nested types.
    // Simple approach: split on top-level `|`.
    let parts = split_on_pipe(text);
    for part in parts {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        // Parse `CtorName : type` or `CtorName (args) : type`.
        // Find the constructor name (first identifier token).
        let name_end = part.find([' ', ':', '(']).unwrap_or(part.len());
        let ctor_name = part[..name_end].trim().to_string();
        if ctor_name.is_empty() {
            continue;
        }
        // The rest after the name is the type.
        let rest = part[name_end..].trim();
        let type_str = if let Some(colon_pos) = rest.find(':') {
            rest[colon_pos + 1..].trim().to_string()
        } else {
            rest.to_string()
        };
        ctors.push((ctor_name, type_str));
    }

    ctors
}

/// Split text on top-level `|` separators, respecting parentheses and `match`.
fn split_on_pipe(text: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0;
    let mut last = 0;
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'{' | b'[' => depth += 1,
            b')' | b'}' | b']' if depth > 0 => {
                depth -= 1;
            }
            b'|' if depth == 0 => {
                parts.push(&text[last..i]);
                last = i + 1;
            }
            _ => {}
        }
        i += 1;
    }
    parts.push(&text[last..]);
    parts
}

/// Parse a Record definition (treat as inductive with one constructor).
fn parse_record(lines: &[&str], start: usize) -> (Option<CoqPrintDef>, usize) {
    let (block, consumed) = collect_block(lines, start);
    let block = block.strip_suffix('.').unwrap_or(&block);

    let rest = match block.strip_prefix("Record ") {
        Some(r) => r,
        None => return (None, consumed),
    };

    // Extract: `name (params) : sort := Constructor { fields }`
    let (before_def, _after_def) = match rest.find(":=") {
        Some(pos) => (&rest[..pos], rest[pos + 2..].trim()),
        None => return (None, consumed),
    };

    let (name, params, sort) = parse_inductive_header(before_def.trim());

    // For records, we create a single constructor with the record name as
    // its builder. We don't try to parse fields in detail.
    let ctors = vec![(format!("Build_{name}"), sort.clone())];

    (
        Some(CoqPrintDef::Inductive {
            name,
            params,
            sort,
            constructors: ctors,
        }),
        consumed,
    )
}

/// Try to parse a definition line of the form `name = body \n : type`.
///
/// Handles both `name = body` (inline) and `name =\nbody` (next-line) forms.
fn try_parse_definition(lines: &[&str], start: usize) -> Option<(CoqPrintDef, usize)> {
    let line = lines[start].trim();

    // Check for `name = body` or `name =` (body on next line) patterns.
    let (name, body_start_str) = if let Some(eq_pos) = line.find(" = ") {
        (&line[..eq_pos], line[eq_pos + 3..].to_string())
    } else {
        let name_part = line.strip_suffix(" =")?;
        // `name =` with body on the next line.
        (name_part, String::new())
    };
    let name = name.trim();

    // Validate name: must be identifier-like (alphanumeric, dots, underscores, primes).
    if name.is_empty()
        || !name
            .chars()
            .all(|c| c.is_alphanumeric() || c == '.' || c == '_' || c == '\'')
    {
        return None;
    }
    // Reject if name is a special keyword.
    if name == "end" || name == "match" || name == "let" || name == "in" || name == "with" {
        return None;
    }

    // Collect the full block, tracking body vs. type annotation separately.
    // In Coq Print output, the type annotation line starts with whitespace then `: `.
    let mut body_parts: Vec<String> = Vec::new();
    let mut type_parts: Vec<String> = Vec::new();
    let mut in_type_annotation = false;

    if !body_start_str.is_empty() {
        body_parts.push(body_start_str);
    }

    let mut j = start + 1;
    while j < lines.len() {
        let next_line = lines[j];
        let trimmed = next_line.trim();
        if trimmed.is_empty() {
            break;
        }
        // Stop on new top-level definitions (skip-category lines).
        if trimmed.starts_with("Inductive ")
            || trimmed.starts_with("Record ")
            || trimmed.starts_with("Notation ")
            || trimmed.starts_with("Arguments ")
            || trimmed.starts_with("[Loading ")
            || trimmed.starts_with("(where ")
        {
            break;
        }
        // For non-indented lines, check if this looks like a new `name = ` definition.
        // But only if we already have some body content.
        let has_content = !body_parts.is_empty() || !type_parts.is_empty();
        if !next_line.starts_with(' ')
            && !next_line.starts_with('\t')
            && has_content
            && looks_like_new_def(trimmed)
        {
            break;
        }

        // Detect type annotation line: starts with whitespace, then `: `.
        let stripped = next_line.trim_start();
        if !in_type_annotation
            && (next_line.starts_with(' ') || next_line.starts_with('\t'))
            && stripped.starts_with(": ")
        {
            in_type_annotation = true;
            type_parts.push(stripped[2..].trim().to_string());
        } else if in_type_annotation {
            type_parts.push(trimmed.to_string());
        } else {
            body_parts.push(trimmed.to_string());
        }
        j += 1;
    }

    let type_str = if type_parts.is_empty() {
        // Fallback: try to extract from body using the heuristic.
        let block = body_parts.join(" ");
        extract_type_annotation(&block)
    } else {
        type_parts.join(" ")
    };

    let body = if body_parts.is_empty() {
        None
    } else {
        let body_str = body_parts.join(" ");
        // If we didn't find a separate type annotation, try stripping from body.
        let body_str = if type_parts.is_empty() {
            extract_body(&body_str).unwrap_or(body_str)
        } else {
            body_str
        };
        if body_str.is_empty() {
            None
        } else {
            Some(body_str)
        }
    };

    Some((
        CoqPrintDef::Definition {
            name: name.to_string(),
            type_str,
            body,
        },
        j - start,
    ))
}

/// Extract the type annotation from a definition block.
/// Coq prints type on a line like `     : nat -> nat -> nat`.
fn extract_type_annotation(block: &str) -> String {
    // Look for a ` : ` that appears after the main body.
    // The type annotation in Coq Print output is typically on its own line
    // starting with `: `. After joining lines it becomes ` : type`.
    // Strategy: find the last occurrence of ` : ` that looks like a type annotation.
    // The type annotation line in Coq starts with spaces then `: `.
    // After joining, it appears as ` : type_expression`.
    // We look for ` : ` preceded by something that looks like end-of-body.
    if let Some(pos) = find_type_annotation_pos(block) {
        block[pos + 3..].trim().to_string()
    } else {
        "Prop".to_string()
    }
}

/// Find the position of the type annotation separator in the block.
/// Returns position of ` : ` that starts the type annotation.
fn find_type_annotation_pos(block: &str) -> Option<usize> {
    // The Coq Print output has the type annotation on a separate line that
    // starts with `: `. After line-joining, this becomes ` : type`.
    // We search backwards for ` : ` that looks like a type annotation.
    // The heuristic: the type annotation is the last top-level ` : `
    // that is not inside parentheses/match/etc.
    let mut depth = 0i32;
    let mut last_colon_pos = None;
    let bytes = block.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'{' | b'[' => depth += 1,
            b')' | b'}' | b']' => depth -= 1,
            b':' if depth <= 0 && i > 0 && i + 1 < bytes.len()
                // Check for ` : ` pattern (not `::` or `:=`).
                && bytes[i - 1] == b' ' && bytes[i + 1] == b' ' =>
            {
                // Don't match `:=`.
                if i + 2 < bytes.len() && bytes[i + 1] == b'=' {
                    // skip
                } else {
                    last_colon_pos = Some(i - 1);
                }
            }
            _ => {}
        }
        i += 1;
    }
    last_colon_pos
}

/// Extract the body from a definition block (everything before the type annotation).
fn extract_body(block: &str) -> Option<String> {
    let body = if let Some(pos) = find_type_annotation_pos(block) {
        block[..pos].trim().to_string()
    } else {
        block.trim().to_string()
    };
    if body.is_empty() {
        None
    } else {
        Some(body)
    }
}

// ---------------------------------------------------------------------------
// Part 2: Convert to sexp and import
// ---------------------------------------------------------------------------

/// Convert a parsed Coq Print definition to the sexp format that
/// [`CoqImporter::import_sexp`] accepts.
pub fn coq_print_def_to_sexp(def: &CoqPrintDef) -> Option<String> {
    match def {
        CoqPrintDef::Inductive {
            name,
            params,
            sort,
            constructors,
        } => {
            let sort_sexp = sort_string_to_sexp(sort);
            let mut param_parts = Vec::new();
            for (pname, ptype) in params {
                let pt_sexp = sort_string_to_sexp(ptype);
                param_parts.push(format!("({pname} {pt_sexp})"));
            }
            let params_sexp = format!("(Params {})", param_parts.join(" "));

            let mut ctor_parts = Vec::new();
            for (cname, _ctype) in constructors {
                // Use a simplified type — just the sort. Full CIC reconstruction
                // would require a complete Coq type parser, which is out of scope.
                ctor_parts.push(format!("(Ctor {cname} {sort_sexp})"));
            }

            let body_sexp = format!("(Body {name} {sort_sexp} {})", ctor_parts.join(" "));

            Some(format!("(MutualInductive {params_sexp} {body_sexp})"))
        }
        CoqPrintDef::Definition {
            name,
            type_str,
            body,
        } => {
            let type_sexp = type_string_to_sexp(type_str);
            if let Some(_body) = body {
                // Definition with body — emit CoqConstant with a placeholder value.
                Some(format!("(CoqConstant {name} {type_sexp} (Const {name}))"))
            } else {
                // Definition without body — emit CoqAxiom.
                Some(format!("(CoqAxiom {name} {type_sexp})"))
            }
        }
        CoqPrintDef::Notation { .. } => {
            // Notations are aliases — skip for import.
            None
        }
    }
}

/// Convert a Coq sort string to a sexp sort expression.
fn sort_string_to_sexp(sort: &str) -> String {
    let s = sort.trim();
    if s == "Set" || s == "Prop" {
        format!("(Sort {s})")
    } else if s.starts_with("Type") {
        "(Sort (Type 0))".to_string()
    } else {
        // Default to Type 0 for complex sort expressions.
        "(Sort (Type 0))".to_string()
    }
}

/// Convert a Coq type string to a simplified sexp type expression.
///
/// This is a rough approximation: we map common patterns to sexp forms.
/// For most definitions, we use `(Sort Prop)` as a placeholder since
/// reconstructing full CIC types from printed Coq output is complex.
fn type_string_to_sexp(type_str: &str) -> String {
    let s = type_str.trim();
    if s == "Prop" {
        return "(Sort Prop)".to_string();
    }
    if s == "Set" {
        return "(Sort (Type 0))".to_string();
    }
    if s == "Type" || s.starts_with("Type") {
        return "(Sort (Type 0))".to_string();
    }
    // For arrow types like `nat -> nat -> nat`, construct nested Prod.
    if s.contains(" -> ") {
        let parts: Vec<&str> = s.splitn(2, " -> ").collect();
        if parts.len() == 2 {
            let domain = type_atom_to_sexp(parts[0].trim());
            let codomain = type_string_to_sexp(parts[1].trim());
            return format!("(Prod _ {domain} {codomain})");
        }
    }
    // For `forall ...` types, use Sort Prop as placeholder.
    if s.starts_with("forall ") {
        return "(Sort Prop)".to_string();
    }
    // Single type atom.
    type_atom_to_sexp(s)
}

/// Convert a single type atom (like `nat`, `bool`, `Z`) to a sexp expression.
fn type_atom_to_sexp(atom: &str) -> String {
    let s = atom.trim();
    match s {
        "nat" => "(Ind nat 0)".to_string(),
        "bool" => "(Ind bool 0)".to_string(),
        "Z" => "(Ind Z 0)".to_string(),
        "positive" => "(Ind positive 0)".to_string(),
        "N" => "(Ind N 0)".to_string(),
        "comparison" => "(Ind comparison 0)".to_string(),
        "Prop" => "(Sort Prop)".to_string(),
        "Set" => "(Sort (Type 0))".to_string(),
        "Type" => "(Sort (Type 0))".to_string(),
        _ => format!("(Const {s})"),
    }
}

/// Import parsed Coq Print output into a [`ShardWriter`].
///
/// Each definition is converted to sexp and then imported through the
/// existing CoqImporter pipeline.
pub fn import_coq_print_output(
    text: &str,
    writer: &mut ShardWriter,
) -> MathverseResult<CoqPrintImportStats> {
    let defs = parse_coq_print_output(text);
    let mut stats = CoqPrintImportStats::default();

    for def in &defs {
        let sexp_str = match coq_print_def_to_sexp(def) {
            Some(s) => s,
            None => {
                stats.notations_skipped += 1;
                continue;
            }
        };

        match def {
            CoqPrintDef::Inductive { .. } => match parse_sexp(&sexp_str) {
                Ok(sexp) => match sexp_to_mutual_inductive(&sexp) {
                    Ok(mind) => {
                        let module_path = infer_module_path(&mind.bodies[0].name);
                        match import_mutual_inductive(&mind, module_path, writer) {
                            Ok(_indices) => {
                                stats.inductives += 1;
                            }
                            Err(_) => stats.import_failures += 1,
                        }
                    }
                    Err(_) => stats.parse_failures += 1,
                },
                Err(_) => stats.parse_failures += 1,
            },
            CoqPrintDef::Definition { body, .. } => {
                match CoqImporter.import_sexp(&sexp_str, writer) {
                    Ok(_s) => {
                        if body.is_some() {
                            stats.definitions += 1;
                        } else {
                            stats.axioms += 1;
                        }
                    }
                    Err(_) => stats.import_failures += 1,
                }
            }
            CoqPrintDef::Notation { .. } => {
                stats.notations_skipped += 1;
            }
        }
    }

    Ok(stats)
}

// ---------------------------------------------------------------------------
// Part 3: Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ShardWriter;

    fn read_optional_coq_stdlib_extract() -> Option<String> {
        std::fs::read_to_string("/tmp/coq_stdlib_extract.txt")
            .ok()
            .filter(|text| !text.trim().is_empty())
    }

    #[test]
    fn test_parse_inductive_nat() {
        let input = "Inductive nat : Set :=  O : nat | S : nat -> nat.";
        let defs = parse_coq_print_output(input);
        assert_eq!(defs.len(), 1);
        match &defs[0] {
            CoqPrintDef::Inductive {
                name,
                params,
                sort,
                constructors,
            } => {
                assert_eq!(name, "nat");
                assert!(params.is_empty());
                assert_eq!(sort, "Set");
                assert_eq!(constructors.len(), 2);
                assert_eq!(constructors[0].0, "O");
                assert_eq!(constructors[1].0, "S");
            }
            other => panic!("expected Inductive, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_parametric_inductive_list() {
        let input =
            "Inductive list (A : Type) : Type :=\n    nil : list A | cons : A -> list A -> list A.";
        let defs = parse_coq_print_output(input);
        assert_eq!(defs.len(), 1);
        match &defs[0] {
            CoqPrintDef::Inductive {
                name,
                params,
                sort,
                constructors,
            } => {
                assert_eq!(name, "list");
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].0, "A");
                assert_eq!(params[0].1, "Type");
                assert_eq!(sort, "Type");
                assert_eq!(constructors.len(), 2);
                assert_eq!(constructors[0].0, "nil");
                assert_eq!(constructors[1].0, "cons");
            }
            other => panic!("expected Inductive, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_definition_with_body() {
        let input = "Nat.add =\nfix add (n m : nat) {struct n} : nat :=\n  match n with\n  | 0%nat => m\n  | S p => S (add p m)\n  end\n     : nat -> nat -> nat";
        let defs = parse_coq_print_output(input);
        assert_eq!(defs.len(), 1, "defs: {:?}", defs);
        match &defs[0] {
            CoqPrintDef::Definition {
                name,
                type_str,
                body,
            } => {
                assert_eq!(name, "Nat.add");
                assert_eq!(type_str, "nat -> nat -> nat");
                assert!(body.is_some(), "body should be present");
            }
            other => panic!("expected Definition, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_fun_definition() {
        let input = "not = fun A : Prop => A -> False\n     : Prop -> Prop";
        let defs = parse_coq_print_output(input);
        assert_eq!(defs.len(), 1);
        match &defs[0] {
            CoqPrintDef::Definition {
                name,
                type_str,
                body,
            } => {
                assert_eq!(name, "not");
                assert_eq!(type_str, "Prop -> Prop");
                assert!(body.is_some());
                let b = body.as_ref().expect("body");
                assert!(
                    b.contains("fun A"),
                    "body should contain 'fun A', got: {}",
                    b
                );
            }
            other => panic!("expected Definition, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_multiline_definition() {
        let input = "eq_ind =\nfun (A : Type) (x : A) (P : A -> Prop) (f : P x) (a : A) (e : x = a) =>\nmatch e in (_ = a0) return (P a0) with\n| eq_refl => f\nend\n     : forall [A : Type] (x : A) (P : A -> Prop),\n       P x -> forall a : A, x = a -> P a";
        let defs = parse_coq_print_output(input);
        assert_eq!(defs.len(), 1, "defs: {:?}", defs);
        match &defs[0] {
            CoqPrintDef::Definition {
                name,
                type_str,
                body,
            } => {
                assert_eq!(name, "eq_ind");
                assert!(
                    type_str.contains("forall"),
                    "type should contain 'forall', got: {}",
                    type_str
                );
                assert!(body.is_some());
            }
            other => panic!("expected Definition, got {:?}", other),
        }
    }

    #[test]
    fn test_full_parse_extract_file() {
        let Some(text) = read_optional_coq_stdlib_extract() else {
            return;
        };
        let defs = parse_coq_print_output(&text);
        assert!(
            defs.len() >= 50,
            "expected 50+ definitions from extract, got {}",
            defs.len()
        );

        let inductives = defs
            .iter()
            .filter(|d| matches!(d, CoqPrintDef::Inductive { .. }))
            .count();
        let definitions = defs
            .iter()
            .filter(|d| matches!(d, CoqPrintDef::Definition { .. }))
            .count();
        let notations = defs
            .iter()
            .filter(|d| matches!(d, CoqPrintDef::Notation { .. }))
            .count();

        assert!(
            inductives >= 10,
            "expected 10+ inductives, got {}",
            inductives
        );
        assert!(
            definitions >= 30,
            "expected 30+ definitions, got {}",
            definitions
        );
        assert!(notations >= 3, "expected 3+ notations, got {}", notations);

        // Spot check known definitions.
        let names: Vec<String> = defs
            .iter()
            .map(|d| match d {
                CoqPrintDef::Inductive { name, .. } => name.clone(),
                CoqPrintDef::Definition { name, .. } => name.clone(),
                CoqPrintDef::Notation { name, .. } => name.clone(),
            })
            .collect();
        assert!(names.contains(&"nat".to_string()), "missing nat");
        assert!(names.contains(&"bool".to_string()), "missing bool");
        assert!(names.contains(&"list".to_string()), "missing list");
        assert!(names.contains(&"Nat.add".to_string()), "missing Nat.add");
        assert!(names.contains(&"not".to_string()), "missing not");
    }

    #[test]
    fn test_convert_to_sexp_and_import() {
        let input = "Inductive nat : Set :=  O : nat | S : nat -> nat.";
        let defs = parse_coq_print_output(input);
        assert_eq!(defs.len(), 1);

        let sexp = coq_print_def_to_sexp(&defs[0]);
        assert!(sexp.is_some(), "should produce sexp for nat");
        let sexp_str = sexp.expect("sexp");
        assert!(
            sexp_str.contains("MutualInductive"),
            "sexp should contain MutualInductive"
        );
        assert!(sexp_str.contains("nat"), "sexp should contain nat");

        // Verify it can be parsed by the CoqImporter pipeline.
        let parsed = parse_sexp(&sexp_str);
        assert!(
            parsed.is_ok(),
            "generated sexp should be parseable: {:?}",
            parsed.err()
        );
    }

    #[test]
    fn test_import_real_extract() {
        let Some(text) = read_optional_coq_stdlib_extract() else {
            return;
        };
        let mut writer = ShardWriter::new();
        let stats = import_coq_print_output(&text, &mut writer).expect("import should succeed");

        // We should import a meaningful number of definitions.
        assert!(
            stats.inductives >= 5,
            "expected 5+ inductives, got {}",
            stats.inductives
        );
        assert!(
            stats.definitions >= 20,
            "expected 20+ definitions, got {}",
            stats.definitions
        );
        assert!(
            stats.import_failures <= stats.definitions + stats.inductives,
            "import failures ({}) should not dominate successful imports ({})",
            stats.import_failures,
            stats.definitions + stats.inductives
        );

        // Verify the shard has content.
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        assert!(
            buf.len() > 100,
            "shard should have meaningful content, got {} bytes",
            buf.len()
        );
    }
}
