// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compare the reported statements with the validated declaration inputs.

use super::{
    base,
    bodies::Statement,
    dependencies::{self, K3DependencyReport},
    expressions::{ExprRow, ExpressionTable},
    fragment::{self, K3FragmentClass},
    invalid,
    levels::{LevelRow, LevelTable},
    scan_checked_bodies, statement_echo, ExportPrefix, ExportTables, K3DeclarationNameSummary,
    K3ExportSyntaxError,
};
use crate::ndjson::json::JsonValue;
use std::collections::HashMap;
use std::io::BufRead;

/// Checked export declarations and their wire expressions for statement comparison.
pub struct K3AcceptedStatementSummary {
    declarations: K3DeclarationNameSummary,
    statements: Vec<Option<Statement>>,
    levels: Vec<LevelRow>,
    expressions: Vec<ExprRow>,
}

impl K3AcceptedStatementSummary {
    /// The validated declaration index and export names.
    pub fn declarations(&self) -> &K3DeclarationNameSummary {
        &self.declarations
    }

    /// Compare the level parameter count, type echo and value echo at a
    /// zero-based declaration row ordinal.
    ///
    /// # Errors
    ///
    /// Returns an error for an unavailable statement, a wrong count, an
    /// expression with no scoped echo, or a difference in the reported bytes.
    pub fn compare_statement(
        &self,
        index: usize,
        lparams: &str,
        type_echo: &str,
        value_echo: &str,
    ) -> Result<(), K3ExportSyntaxError> {
        let line = self
            .declarations
            .bodies()
            .declarations
            .get(index)
            .ok_or_else(|| {
                invalid(
                    0,
                    format!("declaration row index {index} is outside the export"),
                )
            })?
            .line;
        let statement = self
            .statements
            .get(index)
            .and_then(Option::as_ref)
            .ok_or_else(|| invalid(line, "accepted row has no ordinary statement in the export"))?;
        let count = statement.parameters.len();
        if lparams != count.to_string() {
            return Err(invalid(
                line,
                format!("accepted level parameter count differs from the export count {count}"),
            ));
        }

        let scope: HashMap<_, _> = statement
            .parameters
            .iter()
            .copied()
            .enumerate()
            .map(|(position, name)| (name, position))
            .collect();
        for (field, root, expected) in [
            ("type", statement.ty, type_echo),
            ("value", statement.value, value_echo),
        ] {
            if !statement_echo::matches_expression(
                &self.declarations.names,
                &self.levels,
                &self.expressions,
                &scope,
                root,
                expected,
            ) {
                return Err(invalid(
                    line,
                    format!("accepted {field} echo differs from the export"),
                ));
            }
        }
        Ok(())
    }
}

/// Check an export and retain the wire rows needed to compare accepted statements.
///
/// # Errors
///
/// Returns the first read, syntax, table, envelope or declaration body error.
pub fn check_k3_accepted_statements(
    input: impl BufRead,
) -> Result<K3AcceptedStatementSummary, K3ExportSyntaxError> {
    scan_statement_inputs(input, |_, _, _, _| {})
}

/// Checked statement inputs and the recognition result for each export declaration.
pub struct K3BaseRecognitionSummary {
    statements: K3AcceptedStatementSummary,
    recognised: Vec<Option<Vec<usize>>>,
}

impl K3BaseRecognitionSummary {
    /// The checked declarations and their wire statement inputs.
    pub fn accepted_statements(&self) -> &K3AcceptedStatementSummary {
        &self.statements
    }

    /// The export name IDs made citable by a recognised base block.
    ///
    /// The index is the zero-based declaration row ordinal.
    pub fn recognised_members(&self, index: usize) -> Option<&[usize]> {
        self.recognised.get(index).and_then(Option::as_deref)
    }
}

/// Check the export and recognise base families by their full canonical digests.
///
/// # Errors
///
/// Returns the first read, syntax, table, envelope or declaration body error.
pub fn check_k3_base_families(
    input: impl BufRead,
) -> Result<K3BaseRecognitionSummary, K3ExportSyntaxError> {
    let mut recognised = Vec::new();
    let statements = scan_statement_inputs(input, |body, name, members, prefix| {
        recognised.push(members.filter(|_| {
            let (Some(levels), Some(expressions)) =
                (prefix.levels.echo_rows(), prefix.expressions.echo_rows())
            else {
                return false;
            };
            base::recognises(name, body, prefix.names, levels, expressions)
        }));
    })?;
    Ok(K3BaseRecognitionSummary {
        statements,
        recognised,
    })
}

/// Checked export declarations, base members and independently derived classes.
pub struct K3FragmentSummary {
    base: K3BaseRecognitionSummary,
    classes: Vec<K3FragmentClass>,
}

impl K3FragmentSummary {
    /// The checked statement inputs and base recognition results.
    pub fn base_families(&self) -> &K3BaseRecognitionSummary {
        &self.base
    }

    /// The derived class at a zero-based declaration row ordinal.
    pub fn class(&self, index: usize) -> Option<K3FragmentClass> {
        self.classes.get(index).copied()
    }

    /// Compare reported dependency refusals with direct citations to
    /// earlier refused inside declarations. Reports are in export
    /// declaration order and include an entry for every declaration.
    ///
    /// # Errors
    ///
    /// Returns an error if the reports disagree with the class roster
    /// or any row's dependency obligations.
    pub fn compare_dependency_refusals<'report>(
        &self,
        reports: impl IntoIterator<Item = K3DependencyReport<'report>>,
    ) -> Result<usize, K3ExportSyntaxError> {
        let statements = &self.base.statements;
        let names = statements.declarations();
        let rows = names
            .bodies()
            .declarations
            .iter()
            .copied()
            .zip(names.primary_names.iter().copied())
            .zip(self.classes.iter().copied())
            .zip(&statements.statements)
            .map(|(((row, name), class), statement)| (row, name, class, statement.as_ref()));
        dependencies::compare(&names.names, &statements.expressions, rows, reports)
    }
}

/// Check the export and classify its declarations using earlier citable names.
///
/// # Errors
///
/// Returns the first read, syntax, table, envelope or declaration body error.
pub fn check_k3_fragment_classes(
    input: impl BufRead,
) -> Result<K3FragmentSummary, K3ExportSyntaxError> {
    let base = check_k3_base_families(input)?;
    let statements = &base.statements;
    let rows = statements
        .declarations
        .primary_names
        .iter()
        .copied()
        .zip(&statements.statements)
        .zip(&base.recognised)
        .map(|((name, statement), members)| (name, statement.as_ref(), members.as_deref()));
    let classes = fragment::classify(&statements.expressions, rows);
    Ok(K3FragmentSummary { base, classes })
}

fn scan_statement_inputs(
    input: impl BufRead,
    mut visit_block: impl FnMut(&JsonValue, usize, Option<Vec<usize>>, ExportPrefix<'_>),
) -> Result<K3AcceptedStatementSummary, K3ExportSyntaxError> {
    let mut tables = ExportTables {
        levels: LevelTable::with_echo_rows(),
        expressions: ExpressionTable::with_echo_rows(),
        ..ExportTables::default()
    };
    let mut primary_names = Vec::new();
    let mut statements = Vec::new();
    let bodies = scan_checked_bodies(input, &mut tables, |wire, body, prefix| {
        primary_names.push(body.name);
        statements.push(body.statement);
        visit_block(wire, body.name, body.inductive_members, prefix);
    })?;
    Ok(K3AcceptedStatementSummary {
        declarations: K3DeclarationNameSummary {
            bodies,
            names: tables.names,
            primary_names,
        },
        statements,
        levels: tables
            .levels
            .into_echo_rows()
            .ok_or_else(|| invalid(0, "level rows unavailable for statement comparison"))?,
        expressions: tables
            .expressions
            .into_echo_rows()
            .ok_or_else(|| invalid(0, "expression rows unavailable for statement comparison"))?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binds_dependency_reports_to_export_ordinals_and_type_citations() {
        let export = r#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"A"}}
{"in":2,"str":{"pre":0,"str":"B"}}
{"in":3,"str":{"pre":0,"str":"Unused"}}
{"ie":0,"sort":0}
{"ie":1,"const":{"name":1,"us":[]}}
{"axiom":{"name":3,"levelParams":[],"type":0,"isUnsafe":false}}
{"def":{"name":1,"levelParams":[],"type":0,"value":0,"safety":"safe","hints":"opaque","all":[]}}
{"def":{"name":2,"levelParams":[],"type":1,"value":0,"safety":"safe","hints":"opaque","all":[]}}
"#;
        let summary = check_k3_fragment_classes(export.as_bytes()).unwrap();
        use K3DependencyReport::{Accepted, NonInside, Refused};
        assert_eq!(
            summary
                .compare_dependency_refusals([NonInside, Accepted, Accepted])
                .unwrap(),
            0
        );
        assert_eq!(
            summary
                .compare_dependency_refusals(
                    [NonInside, Refused(""), Refused("dependency:[s1:A]"),]
                )
                .unwrap(),
            1
        );
        let error = summary
            .compare_dependency_refusals([NonInside, Refused(""), Accepted])
            .unwrap_err();
        assert!(
            matches!(error, K3ExportSyntaxError::Invalid { line: 9, ref reason }
                if reason.contains("earlier refused declaration at line 8")),
            "{error}",
        );
    }

    #[test]
    fn derives_classes_from_checked_declaration_order_and_safety() {
        let export = r#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"Seed"}}
{"in":2,"str":{"pre":0,"str":"Early"}}
{"in":3,"str":{"pre":0,"str":"Later"}}
{"in":4,"str":{"pre":0,"str":"Unsafe"}}
{"in":5,"str":{"pre":0,"str":"Partial"}}
{"in":6,"str":{"pre":0,"str":"OpaqueUnsafe"}}
{"in":7,"str":{"pre":0,"str":"OpaqueSafe"}}
{"ie":0,"sort":0}
{"ie":1,"const":{"name":1,"us":[]}}
{"thm":{"name":2,"levelParams":[],"type":0,"value":1,"all":[]}}
{"def":{"name":1,"levelParams":[],"type":0,"value":0,"safety":"safe","hints":"opaque","all":[]}}
{"thm":{"name":3,"levelParams":[],"type":0,"value":1,"all":[]}}
{"def":{"name":4,"levelParams":[],"type":0,"value":0,"safety":"unsafe","hints":"opaque","all":[]}}
{"def":{"name":5,"levelParams":[],"type":0,"value":0,"safety":"partial","hints":"opaque","all":[]}}
{"opaque":{"name":6,"levelParams":[],"type":0,"value":0,"isUnsafe":true,"all":[]}}
{"opaque":{"name":7,"levelParams":[],"type":0,"value":1,"isUnsafe":false,"all":[]}}
"#;
        let summary = check_k3_fragment_classes(export.as_bytes()).unwrap();
        use K3FragmentClass::{Inside, Outside};
        for (index, class) in [Outside, Inside, Inside, Outside, Outside, Outside, Inside]
            .into_iter()
            .enumerate()
        {
            assert_eq!(summary.class(index), Some(class));
        }
        assert_eq!(summary.class(7), None);
    }

    #[test]
    fn leaves_a_shape_valid_namesake_unrecognised() {
        let export = concat!(
            "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n",
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Nat\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"axiom\":{\"name\":0,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}\n",
            r#"{"inductive":{"types":[{"name":1,"levelParams":[],"type":0,"numParams":0,"numIndices":0,"all":[1],"ctors":[],"numNested":0,"isRec":true,"isUnsafe":false,"isReflexive":false}],"ctors":[],"recs":[]}}"#,
            "\n",
        );
        let summary = check_k3_base_families(export.as_bytes()).unwrap();
        assert!(summary
            .accepted_statements()
            .declarations()
            .matches_name(1, "[s3:Nat]"));
        for index in 0..=2 {
            assert_eq!(summary.recognised_members(index), None);
        }
    }

    #[test]
    fn compares_wire_roots_and_ordered_parameters_for_each_declaration() {
        let export = r#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"A"}}
{"in":2,"str":{"pre":0,"str":"B"}}
{"in":3,"str":{"pre":0,"str":"u"}}
{"in":4,"str":{"pre":0,"str":"v"}}
{"il":1,"param":3}
{"il":2,"param":4}
{"ie":0,"sort":1}
{"ie":1,"sort":2}
{"ie":2,"mdata":{"data":false,"expr":1}}
{"def":{"name":1,"levelParams":[3,4],"type":0,"value":2,"safety":"safe","hints":"opaque","all":[]}}
{"thm":{"name":2,"levelParams":[4,3],"type":0,"value":2,"all":[]}}
{"axiom":{"name":0,"levelParams":[],"type":1,"isUnsafe":false}}
"#;
        let summary = check_k3_accepted_statements(export.as_bytes()).unwrap();
        assert!(summary.declarations().matches_name(0, "[s1:A]"));
        let zero = "(sort (p 0))";
        let one = "(sort (p 1))";
        summary.compare_statement(0, "2", zero, one).unwrap();
        summary.compare_statement(1, "2", one, zero).unwrap();
        for (index, count, ty, value, line, reason) in [
            (
                0,
                "18446744073709551616",
                zero,
                one,
                11,
                "level parameter count",
            ),
            (1, "2", zero, one, 12, "type echo"),
            (1, "2", one, one, 12, "value echo"),
            (2, "0", one, one, 13, "no ordinary statement"),
        ] {
            let error = summary
                .compare_statement(index, count, ty, value)
                .unwrap_err();
            assert!(
                matches!(error, K3ExportSyntaxError::Invalid { line: actual, reason: ref text }
                    if actual == line && text.contains(reason)),
                "{error}",
            );
        }
    }
}
