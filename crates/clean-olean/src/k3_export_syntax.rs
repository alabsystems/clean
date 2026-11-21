// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The syntax and checked tables of the K3 export.

mod base;
mod bodies;
mod declarations;
mod dependencies;
mod expressions;
mod fragment;
mod levels;
mod names;
mod statement_echo;
mod statements;

use crate::ndjson::json::{parse_line, JsonValue};
use crate::ndjson::MAX_LINE_BYTES;
use std::io::{self, BufRead, Read};

pub use declarations::{K3DeclarationIndexRow, K3DeclarationKind};
pub use dependencies::K3DependencyReport;
pub use fragment::K3FragmentClass;
pub use statements::{
    check_k3_accepted_statements, check_k3_base_families, check_k3_fragment_classes,
    K3AcceptedStatementSummary, K3BaseRecognitionSummary, K3FragmentSummary,
};

#[derive(Default)]
struct ExportTables {
    names: names::NameTable,
    levels: levels::LevelTable,
    expressions: expressions::ExpressionTable,
}

struct ExportPrefix<'table> {
    names: &'table names::NameTable,
    levels: &'table levels::LevelTable,
    expressions: &'table expressions::ExpressionTable,
}

const MAX_UNFOLDED_NODES: usize = 1_048_576;

/// A read failure or invalid data in a decompressed K3 export.
#[derive(Debug, thiserror::Error)]
pub enum K3ExportSyntaxError {
    /// The input could not be read through the named line.
    #[error("export line {line}: {source}")]
    Io {
        /// The one-based line being read.
        line: usize,
        /// The underlying read failure.
        #[source]
        source: io::Error,
    },
    /// An input line violated a K3 syntax or table rule.
    #[error("export line {line}: {reason}")]
    Invalid {
        /// The one-based line where the violation was found.
        line: usize,
        /// The failed validation rule.
        reason: String,
    },
}

fn invalid(line: usize, reason: impl Into<String>) -> K3ExportSyntaxError {
    K3ExportSyntaxError::Invalid {
        line,
        reason: reason.into(),
    }
}

/// Check the compact JSON spelling and first-line metadata of a decompressed
/// K3 export. Return the number of LF-terminated objects, including metadata.
///
/// # Errors
///
/// Returns a read or syntax error at the first failing line. Declaration and
/// table validation belong to the full K3 reader.
pub fn check_k3_export_syntax(input: impl BufRead) -> Result<usize, K3ExportSyntaxError> {
    scan_export(input, |_, _| Ok(()))
}

/// The record and explicit name counts from an export with a valid name table.
#[derive(Debug, PartialEq, Eq)]
pub struct K3ExportNameSummary {
    /// All LF-terminated records, including metadata.
    pub records: usize,
    /// Name records, excluding the implicit anonymous name at index zero.
    pub explicit_names: usize,
}

/// Check the K3 export syntax and the explicit name table.
///
/// # Errors
///
/// Returns a read, syntax, or name-table error at the first failing line.
pub fn check_k3_export_names(
    input: impl BufRead,
) -> Result<K3ExportNameSummary, K3ExportSyntaxError> {
    let mut names = names::NameTable::default();
    let records = scan_export(input, |line, entries| names.visit(line, entries))?;
    Ok(K3ExportNameSummary {
        records,
        explicit_names: names.explicit_count(),
    })
}

/// The counts and maximum unfolded size from validated name and level tables.
#[derive(Debug, PartialEq, Eq)]
pub struct K3ExportLevelSummary {
    /// All LF-terminated records, including metadata.
    pub records: usize,
    /// Name records, excluding the implicit anonymous name.
    pub explicit_names: usize,
    /// Level records, excluding the implicit zero.
    pub explicit_levels: usize,
    /// Maximum unfolded level size, including the implicit zero.
    pub max_unfolded_level_nodes: usize,
}

/// Check K3 export syntax, the explicit name table, and the level table.
///
/// # Errors
///
/// Returns a read, syntax, or table error at the first failing line.
pub fn check_k3_export_levels(
    input: impl BufRead,
) -> Result<K3ExportLevelSummary, K3ExportSyntaxError> {
    scan_tables(
        input,
        &mut names::NameTable::default(),
        &mut levels::LevelTable::default(),
        |_, _, _, _| Ok(()),
    )
}

/// The counts and maximum sizes from validated name, level, and expression tables.
#[derive(Debug, PartialEq, Eq)]
pub struct K3ExportExpressionSummary {
    /// The counts and maximum unfolded level size.
    pub tables: K3ExportLevelSummary,
    /// Explicit expression records, including index zero when present.
    pub explicit_expressions: usize,
    /// Maximum unfolded expression size, or zero for an empty expression table.
    pub max_unfolded_expression_nodes: usize,
}

/// Check K3 export syntax and the name, level, and expression tables.
///
/// # Errors
///
/// Returns a read, syntax, or table error at the first failing line.
pub fn check_k3_export_expressions(
    input: impl BufRead,
) -> Result<K3ExportExpressionSummary, K3ExportSyntaxError> {
    scan_expressions(input, &mut ExportTables::default(), |_, _, _| Ok(()))
}

/// Check the export tables and collect each declaration's physical line and kind.
///
/// # Errors
///
/// Returns the first read, syntax, table, or declaration envelope error.
pub fn k3_declaration_index(
    input: impl BufRead,
) -> Result<Vec<K3DeclarationIndexRow>, K3ExportSyntaxError> {
    scan_declarations(input, &mut ExportTables::default(), |_, _, _| Ok(()))
}

/// The checked non-inductive declaration count and complete declaration index.
#[derive(Debug, PartialEq, Eq)]
pub struct K3NonInductiveBodySummary {
    /// Each declaration's physical line and kind, including inductive envelopes.
    pub declarations: Vec<K3DeclarationIndexRow>,
    /// The number of definitions, theorems, opaques, axioms and quotients checked.
    pub checked_bodies: usize,
}

/// Check the name, level and expression tables and all non-inductive declaration bodies.
///
/// # Errors
///
/// Returns the first read, syntax, table, envelope, or non-inductive body error.
pub fn check_k3_non_inductive_bodies(
    input: impl BufRead,
) -> Result<K3NonInductiveBodySummary, K3ExportSyntaxError> {
    let mut validator = bodies::BodyCheck::default();
    let declarations =
        scan_declarations(input, &mut ExportTables::default(), |row, body, prefix| {
            validator.visit(
                row.line,
                row.kind,
                body,
                prefix.names.explicit_count(),
                prefix.expressions.explicit_count(),
            )?;
            Ok(())
        })?;
    Ok(K3NonInductiveBodySummary {
        declarations,
        checked_bodies: validator.checked_count(),
    })
}

/// The checked declaration index and counts for the complete body check.
#[derive(Debug, PartialEq, Eq)]
pub struct K3DeclarationBodySummary {
    /// Each declaration's physical line and kind, with one row per inductive block.
    pub declarations: Vec<K3DeclarationIndexRow>,
    /// The number of checked inductive blocks.
    pub inductive_blocks: usize,
    /// The number of distinct declared names, including inductive members.
    pub declared_names: usize,
}

/// Check the export tables and all declaration bodies and their declared names.
///
/// # Errors
/// Returns the first read, syntax, table, envelope, or declaration body error.
pub fn check_k3_declaration_bodies(
    input: impl BufRead,
) -> Result<K3DeclarationBodySummary, K3ExportSyntaxError> {
    scan_checked_bodies(input, &mut ExportTables::default(), |_, _, _| {})
}

/// A checked declaration index with export names in declaration row order.
pub struct K3DeclarationNameSummary {
    bodies: K3DeclarationBodySummary,
    names: names::NameTable,
    primary_names: Vec<usize>,
}

impl K3DeclarationNameSummary {
    /// The checked bodies and declaration index.
    pub fn bodies(&self) -> &K3DeclarationBodySummary {
        &self.bodies
    }

    /// Compare a declaration's name with the version-1 transcript spelling.
    ///
    /// The index is the zero-based declaration row ordinal.
    pub fn matches_name(&self, index: usize, expected: &str) -> bool {
        self.primary_names
            .get(index)
            .is_some_and(|&name| self.names.matches_echo(name, expected))
    }
}

/// Check the export and retain its primary names for transcript comparison.
///
/// # Errors
/// Returns the first read, syntax, table, envelope, or declaration body error.
pub fn check_k3_declaration_names(
    input: impl BufRead,
) -> Result<K3DeclarationNameSummary, K3ExportSyntaxError> {
    let mut tables = ExportTables::default();
    let mut primary_names = Vec::new();
    let bodies = scan_checked_bodies(input, &mut tables, |_, body, _| {
        primary_names.push(body.name)
    })?;
    Ok(K3DeclarationNameSummary {
        bodies,
        names: tables.names,
        primary_names,
    })
}

fn scan_checked_bodies(
    input: impl BufRead,
    tables: &mut ExportTables,
    mut visit_body: impl FnMut(&JsonValue, bodies::CheckedBody, ExportPrefix<'_>),
) -> Result<K3DeclarationBodySummary, K3ExportSyntaxError> {
    let mut validator = bodies::BodyCheck::all_declarations();
    let declarations = scan_declarations(input, tables, |row, body, prefix| {
        let checked = validator
            .visit(
                row.line,
                row.kind,
                body,
                prefix.names.explicit_count(),
                prefix.expressions.explicit_count(),
            )?
            .ok_or_else(|| invalid(row.line, "declaration body has no primary name"))?;
        visit_body(body, checked, prefix);
        Ok(())
    })?;
    let inductive_blocks = declarations
        .iter()
        .filter(|row| row.kind == K3DeclarationKind::Inductive)
        .count();
    Ok(K3DeclarationBodySummary {
        declarations,
        inductive_blocks,
        declared_names: validator.checked_count(),
    })
}

fn scan_declarations(
    input: impl BufRead,
    tables: &mut ExportTables,
    mut visit: impl FnMut(
        K3DeclarationIndexRow,
        &JsonValue,
        ExportPrefix<'_>,
    ) -> Result<(), K3ExportSyntaxError>,
) -> Result<Vec<K3DeclarationIndexRow>, K3ExportSyntaxError> {
    let mut declarations = Vec::new();
    scan_expressions(input, tables, |line, entries, prefix| {
        let (row, body) = declarations::declaration_envelope(line, entries)?;
        visit(row, &body, prefix)?;
        declarations.push(row);
        Ok(())
    })?;
    Ok(declarations)
}

fn scan_expressions(
    input: impl BufRead,
    tables: &mut ExportTables,
    mut visit_declaration: impl FnMut(
        usize,
        Vec<(String, JsonValue)>,
        ExportPrefix<'_>,
    ) -> Result<(), K3ExportSyntaxError>,
) -> Result<K3ExportExpressionSummary, K3ExportSyntaxError> {
    let ExportTables {
        names,
        levels,
        expressions,
    } = tables;
    let tables = scan_tables(input, names, levels, |line, entries, names, levels| {
        if has_key(&entries, "ie") {
            expressions.visit(line, entries, names.explicit_count(), levels)
        } else if line > 1 {
            visit_declaration(
                line,
                entries,
                ExportPrefix {
                    names,
                    levels,
                    expressions,
                },
            )
        } else {
            Ok(())
        }
    })?;
    Ok(K3ExportExpressionSummary {
        tables,
        explicit_expressions: expressions.explicit_count(),
        max_unfolded_expression_nodes: expressions.max_unfolded_nodes(),
    })
}

fn scan_tables(
    input: impl BufRead,
    names: &mut names::NameTable,
    levels: &mut levels::LevelTable,
    mut visit_other: impl FnMut(
        usize,
        Vec<(String, JsonValue)>,
        &names::NameTable,
        &levels::LevelTable,
    ) -> Result<(), K3ExportSyntaxError>,
) -> Result<K3ExportLevelSummary, K3ExportSyntaxError> {
    let records = scan_export(input, |line, entries| {
        // Classify ambiguous rows in K3 wire order so the exact shape check refuses them.
        if has_key(&entries, "in") {
            names.visit(line, entries)
        } else if has_key(&entries, "il") {
            levels.visit(line, entries, names.explicit_count())
        } else {
            visit_other(line, entries, names, levels)
        }
    })?;
    Ok(K3ExportLevelSummary {
        records,
        explicit_names: names.explicit_count(),
        explicit_levels: levels.explicit_count(),
        max_unfolded_level_nodes: levels.max_unfolded_nodes(),
    })
}

fn exact_fields<'a, const N: usize>(
    line: usize,
    context: impl std::fmt::Display,
    body: &'a JsonValue,
    keys: [&str; N],
) -> Result<[&'a JsonValue; N], K3ExportSyntaxError> {
    let malformed = || {
        invalid(
            line,
            format!("{context} expects exactly the fields {}", keys.join(", ")),
        )
    };
    let JsonValue::Object(fields) = body else {
        return Err(malformed());
    };
    if fields.len() != N {
        return Err(malformed());
    }
    let mut values = [body; N];
    for (value, key) in values.iter_mut().zip(keys) {
        *value = fields
            .iter()
            .find_map(|(field, value)| (field == key).then_some(value))
            .ok_or_else(malformed)?;
    }
    Ok(values)
}

fn require_natural(line: usize, field: &str, value: &JsonValue) -> Result<(), K3ExportSyntaxError> {
    if matches!(value, JsonValue::Number(number) if number.canonical_natural) {
        Ok(())
    } else {
        Err(invalid(line, format!("{field} expects a natural number")))
    }
}

fn has_key(entries: &[(String, JsonValue)], field: &str) -> bool {
    entries.iter().any(|(key, _)| key == field)
}

fn index(value: &JsonValue) -> Option<usize> {
    let JsonValue::Number(number) = value else {
        return None;
    };
    usize::try_from(number.as_u64()?).ok()
}

fn take_pair(
    entries: Vec<(String, JsonValue)>,
    key: &str,
) -> Option<(JsonValue, (String, JsonValue))> {
    let [first, second] = <[_; 2]>::try_from(entries).ok()?;
    if first.0 == key {
        Some((first.1, second))
    } else if second.0 == key {
        Some((second.1, first))
    } else {
        None
    }
}

fn scan_export(
    mut input: impl BufRead,
    mut visit: impl FnMut(usize, Vec<(String, JsonValue)>) -> Result<(), K3ExportSyntaxError>,
) -> Result<usize, K3ExportSyntaxError> {
    let mut bytes = Vec::new();
    let mut records = 0;
    loop {
        let line = records + 1;
        bytes.clear();
        let count = (&mut input)
            .take((MAX_LINE_BYTES + 2) as u64)
            .read_until(b'\n', &mut bytes)
            .map_err(|source| K3ExportSyntaxError::Io { line, source })?;
        if count == 0 {
            return if records == 0 {
                Err(invalid(line, "missing the initial meta record"))
            } else {
                Ok(records)
            };
        }
        let has_lf = bytes.last() == Some(&b'\n');
        let length = count - has_lf as usize;
        if length > MAX_LINE_BYTES {
            return Err(invalid(
                line,
                format!("line exceeds {MAX_LINE_BYTES} bytes"),
            ));
        }
        if !has_lf {
            return Err(invalid(line, "line is not ended by a line feed"));
        }
        let entries = check_line(&bytes[..length], line)?;
        visit(line, entries)?;
        records += 1;
    }
}

fn check_line(bytes: &[u8], line: usize) -> Result<Vec<(String, JsonValue)>, K3ExportSyntaxError> {
    let mut in_string = false;
    for &byte in bytes {
        match byte {
            b'\\' => return Err(invalid(line, "backslash escapes are disallowed")),
            b'"' => in_string = !in_string,
            b' ' | b'\t' | b'\r' | b'\n' if !in_string => {
                return Err(invalid(line, "whitespace outside a string is disallowed"));
            }
            _ => {}
        }
    }

    let value = parse_line(bytes).map_err(|reason| invalid(line, reason.to_string()))?;
    let JsonValue::Object(entries) = value else {
        return Err(invalid(line, "expected one JSON object"));
    };
    check_naturals(&entries, line)?;
    if line == 1 {
        if !is_header(&entries) {
            return Err(invalid(
                line,
                "expected a meta record of format version 3.1.0",
            ));
        }
    } else if entries.iter().any(|(name, _)| name == "meta") {
        return Err(invalid(line, "a second meta record"));
    }
    Ok(entries)
}

fn check_naturals(entries: &[(String, JsonValue)], line: usize) -> Result<(), K3ExportSyntaxError> {
    let mut pending: Vec<_> = entries.iter().map(|(_, value)| value).collect();
    while let Some(value) = pending.pop() {
        match value {
            JsonValue::Number(number) if !number.canonical_natural => {
                return Err(invalid(line, "numbers must be unsigned decimal integers"));
            }
            JsonValue::Array(values) => pending.extend(values),
            JsonValue::Object(entries) => pending.extend(entries.iter().map(|(_, value)| value)),
            _ => {}
        }
    }
    Ok(())
}

fn is_header(entries: &[(String, JsonValue)]) -> bool {
    let [(key, JsonValue::Object(fields))] = entries else {
        return false;
    };
    if key != "meta" {
        return false;
    }
    let Some((_, JsonValue::Object(format))) = fields.iter().find(|(key, _)| key == "format")
    else {
        return false;
    };
    matches!(format.as_slice(), [(key, JsonValue::String(version))] if key == "version" && version == "3.1.0")
}

#[cfg(test)]
mod tests {
    use super::*;

    const META: &str = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n";

    fn expect_invalid(input: &[u8], expected_line: usize, expected_reason: &str) {
        match check_k3_export_syntax(input) {
            Err(K3ExportSyntaxError::Invalid { line, reason }) => {
                assert_eq!(line, expected_line, "{reason}");
                assert!(reason.contains(expected_reason), "{reason}");
            }
            result => panic!("expected syntax error, got {result:?}"),
        }
    }

    #[test]
    fn body_checks_use_the_table_prefix_at_each_declaration() {
        let start = format!(
            r#"{META}{{"ie":0,"bvar":0}}
"#
        );
        let valid = format!(
            r#"{start}{{"axiom":{{"name":0,"levelParams":[],"type":0,"isUnsafe":false}}}}
{{"inductive":null}}
"#
        );
        let summary = check_k3_non_inductive_bodies(valid.as_bytes()).unwrap();
        assert_eq!(summary.checked_bodies, 1);
        assert_eq!(summary.declarations.len(), 2);
        assert_eq!(summary.declarations[1].kind, K3DeclarationKind::Inductive);

        let late_name = format!(
            r#"{start}{{"axiom":{{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}}}
{{"in":1,"str":{{"pre":0,"str":"later"}}}}
"#
        );
        let late_type = format!(
            r#"{start}{{"axiom":{{"name":0,"levelParams":[],"type":1,"isUnsafe":false}}}}
{{"ie":1,"bvar":0}}
"#
        );
        for input in [late_name, late_type] {
            assert_eq!(k3_declaration_index(input.as_bytes()).unwrap().len(), 1);
            let error = check_k3_non_inductive_bodies(input.as_bytes()).unwrap_err();
            assert!(
                matches!(error, K3ExportSyntaxError::Invalid { line: 3, .. }),
                "{error}"
            );
        }
    }

    #[test]
    fn checks_declaration_identities_within_and_across_inductive_blocks() {
        let prefix = format!(
            r#"{META}{{"in":1,"str":{{"pre":0,"str":"I"}}}}
{{"ie":0,"bvar":0}}
"#
        );
        let axiom = r#"{"axiom":{"name":0,"levelParams":[],"type":0,"isUnsafe":false}}"#;
        let ty = concat!(
            r#"{"name":1,"levelParams":[],"type":0,"numParams":0,"numIndices":0,"#,
            r#""all":[],"ctors":[],"numNested":0,"isRec":false,"isUnsafe":false,"isReflexive":false}"#,
        );
        let block = format!(r#"{{"inductive":{{"types":[{ty}],"ctors":[],"recs":[]}}}}"#);
        let valid = format!("{prefix}{axiom}\n{block}\n");
        let summary = check_k3_declaration_bodies(valid.as_bytes()).unwrap();
        assert_eq!(summary.declarations.len(), 2);
        assert_eq!(summary.inductive_blocks, 1);
        assert_eq!(summary.declared_names, 2);

        let duplicate_axiom = axiom.replace(r#""name":0"#, r#""name":1"#);
        let duplicate_block =
            format!(r#"{{"inductive":{{"types":[{ty},{ty}],"ctors":[],"recs":[]}}}}"#);
        for (input, line) in [
            (format!("{prefix}{duplicate_block}\n"), 4),
            (format!("{prefix}{duplicate_axiom}\n{block}\n"), 5),
            (format!("{prefix}{block}\n{duplicate_axiom}\n"), 5),
            (format!("{prefix}{block}\n{block}\n"), 5),
        ] {
            let error = check_k3_declaration_bodies(input.as_bytes()).unwrap_err();
            assert!(
                matches!(error, K3ExportSyntaxError::Invalid { line: actual, ref reason }
                    if actual == line && reason.contains("name 1 is declared twice")),
                "{error}"
            );
            check_k3_non_inductive_bodies(input.as_bytes()).unwrap();
        }
    }

    #[test]
    fn declaration_name_summary_uses_physical_row_order_and_first_type() {
        let prefix = format!(
            r#"{META}{{"in":1,"str":{{"pre":0,"str":"A"}}}}
{{"in":2,"str":{{"pre":0,"str":"β"}}}}
{{"ie":0,"bvar":0}}
{{"axiom":{{"name":0,"levelParams":[],"type":0,"isUnsafe":false}}}}
"#
        );
        let row = |name| {
            format!(
                concat!(
                    r#"{{"name":{name},"levelParams":[],"type":0,"numParams":0,"numIndices":0,"#,
                    r#""all":[],"ctors":[],"numNested":0,"isRec":false,"isUnsafe":false,"isReflexive":false}}"#,
                ),
                name = name,
            )
        };
        for (first, second, expected) in [(1, 2, "[s1:A]"), (2, 1, "[s2:β]")] {
            let block = format!(
                r#"{{"inductive":{{"types":[{},{}],"ctors":[],"recs":[]}}}}"#,
                row(first),
                row(second),
            );
            let input = format!("{prefix}{block}\n");
            let summary = check_k3_declaration_names(input.as_bytes()).unwrap();
            assert_eq!(summary.bodies().declarations[1].line, 6);
            assert_eq!(summary.bodies().inductive_blocks, 1);
            assert_eq!(summary.bodies().declared_names, 3);
            assert!(summary.matches_name(0, "[]"));
            assert!(summary.matches_name(1, expected));
            assert!(!summary.matches_name(1, "[s1:β]"));
            assert!(!summary.matches_name(2, expected));
        }
    }

    #[test]
    fn indexes_declarations_at_their_physical_lines() {
        let input = format!(
            r#"{META}{{"ie":0,"bvar":0}}
{{"def":null}}
{{"il":1,"succ":0}}
{{"inductive":false}}
"#
        );
        assert_eq!(
            k3_declaration_index(input.as_bytes()).unwrap(),
            [
                K3DeclarationIndexRow {
                    line: 3,
                    kind: K3DeclarationKind::Def
                },
                K3DeclarationIndexRow {
                    line: 5,
                    kind: K3DeclarationKind::Inductive
                },
            ]
        );

        let unknown = format!(
            r#"{input}{{"unknown":0}}
"#
        );
        let error = k3_declaration_index(unknown.as_bytes()).unwrap_err();
        assert!(
            matches!(error, K3ExportSyntaxError::Invalid { line: 6, .. }),
            "{error}"
        );
    }

    #[test]
    fn expression_check_uses_tables_in_wire_order() {
        let input = format!(
            r#"{META}{{"ie":0,"bvar":0}}
{{"in":1,"str":{{"str":"u","pre":0}}}}
{{"il":1,"param":1}}
{{"ie":1,"sort":1}}
{{"ie":2,"app":{{"fn":0,"arg":1}}}}
"#
        );
        assert_eq!(
            check_k3_export_expressions(input.as_bytes()).unwrap(),
            K3ExportExpressionSummary {
                tables: K3ExportLevelSummary {
                    records: 6,
                    explicit_names: 1,
                    explicit_levels: 1,
                    max_unfolded_level_nodes: 1,
                },
                explicit_expressions: 3,
                max_unfolded_expression_nodes: 4,
            }
        );
        let early = format!(
            r#"{META}{{"ie":0,"sort":1}}
{{"il":1,"succ":0}}
"#
        );
        assert_eq!(
            check_k3_export_levels(early.as_bytes())
                .unwrap()
                .explicit_levels,
            1
        );
        let error = check_k3_export_expressions(early.as_bytes()).unwrap_err();
        assert!(
            matches!(error, K3ExportSyntaxError::Invalid { line: 2, .. }),
            "{error}"
        );
    }

    #[test]
    fn level_check_uses_names_in_wire_order() {
        let header = format!(
            r#"{META}{{"il":1,"param":0}}
{{"in":1,"str":{{"str":"u","pre":0}}}}
"#
        );
        let input = format!(
            r#"{header}{{"il":2,"param":1}}
{{"il":3,"imax":[1,2]}}
"#
        );
        assert_eq!(
            check_k3_export_levels(input.as_bytes()).unwrap(),
            K3ExportLevelSummary {
                records: 5,
                explicit_names: 1,
                explicit_levels: 3,
                max_unfolded_level_nodes: 3,
            }
        );
        let early = format!(
            r#"{META}{{"il":1,"param":1}}
{{"in":1,"str":{{"str":"u","pre":0}}}}
"#
        );
        assert_eq!(
            check_k3_export_names(early.as_bytes())
                .unwrap()
                .explicit_names,
            1
        );
        let error = check_k3_export_levels(early.as_bytes()).unwrap_err();
        assert!(
            matches!(error, K3ExportSyntaxError::Invalid { line: 2, .. }),
            "{error}"
        );
    }

    #[test]
    fn checks_names_after_compact_syntax() {
        let input = format!(
            r#"{META}{{"in":1,"str":{{"pre":0,"str":"a"}}}}
{{"il":1,"param":1}}
"#
        );
        let summary = check_k3_export_names(input.as_bytes()).unwrap();
        assert_eq!(
            summary,
            K3ExportNameSummary {
                records: 3,
                explicit_names: 1
            }
        );

        let duplicate = format!(
            r#"{input}{{"in":2,"str":{{"pre":0,"str":"a"}}}}
"#
        );
        assert_eq!(check_k3_export_syntax(duplicate.as_bytes()).unwrap(), 4);
        let error = check_k3_export_names(duplicate.as_bytes()).unwrap_err();
        assert!(
            matches!(error, K3ExportSyntaxError::Invalid { line: 4, .. }),
            "{error}"
        );
    }

    #[test]
    fn accepts_plain_strings_input_key_order_and_wide_naturals() {
        let input = concat!(
            r#"{"meta":{"opaque":[18446744073709551616,null,"two words"],"format":{"version":"3.1.0"}}}"#,
            "\n{\"strVal\":\"x\u{2028}y\",\"ie\":0}\n",
        );
        assert_eq!(check_k3_export_syntax(input.as_bytes()).unwrap(), 2);
    }

    #[test]
    fn refuses_missing_lf_or_a_noncompact_object() {
        expect_invalid(META.trim_end().as_bytes(), 1, "line feed");
        expect_invalid(b"", 1, "missing the initial meta");
        for (suffix, reason) in [
            ("\n", "unexpected end"),
            ("{}\r\n", "whitespace"),
            ("{}\t\n", "whitespace"),
            ("{\"x\": 0}\n", "whitespace"),
            ("{\"x\":\"a\\u0062\"}\n", "backslash"),
            ("{\"x\":\"a\tb\"}\n", "control character"),
            ("{\"x\":{\"y\":0,\"y\":1}}\n", "duplicate object key"),
            ("[]\n", "expected one JSON object"),
            ("{}{}\n", "bytes after the JSON value"),
        ] {
            expect_invalid(format!("{META}{suffix}").as_bytes(), 2, reason);
        }
        expect_invalid(&[META.as_bytes(), b"\xff\n"].concat(), 2, "not UTF-8");
    }

    #[test]
    fn refuses_non_natural_tokens_even_in_unused_metadata() {
        for number in ["-0", "-2", "1.5", "1e2"] {
            let input = format!(
                "{{\"meta\":{{\"extra\":[{number}],\"format\":{{\"version\":\"3.1.0\"}}}}}}\n"
            );
            expect_invalid(input.as_bytes(), 1, "unsigned decimal integers");
        }
        expect_invalid(
            format!("{META}{{\"x\":01}}\n").as_bytes(),
            2,
            "unexpected byte",
        );
    }

    #[test]
    fn requires_a_single_initial_31_meta_record() {
        for header in [
            "{}\n",
            "{\"meta\":[],\"format\":{\"version\":\"3.1.0\"}}\n",
            "{\"meta\":{\"format\":{\"version\":\"3.1.1\"}}}\n",
            "{\"meta\":{\"format\":{\"version\":\"3.1.0\",\"extra\":0}}}\n",
            "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}},\"extra\":0}\n",
        ] {
            expect_invalid(header.as_bytes(), 1, "expected a meta record");
        }
        expect_invalid(format!("{META}{META}").as_bytes(), 2, "second meta");
    }

    #[test]
    fn reports_read_failures_on_the_line_being_read() {
        struct BrokenInput;

        impl Read for BrokenInput {
            fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
                Err(io::Error::new(io::ErrorKind::BrokenPipe, "read stopped"))
            }
        }

        let input = META.as_bytes().chain(io::BufReader::new(BrokenInput));
        assert!(matches!(
            check_k3_export_syntax(input),
            Err(K3ExportSyntaxError::Io { line: 2, source })
                if source.kind() == io::ErrorKind::BrokenPipe
        ));
    }
}
