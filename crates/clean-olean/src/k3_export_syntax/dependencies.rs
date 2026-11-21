// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compare transcript dependency reports to direct citations in the export.

use super::{
    bodies::Statement,
    expressions::ExprRow,
    fragment::{ExpressionWalk, K3FragmentClass},
    invalid,
    names::NameTable,
    K3DeclarationIndexRow, K3DeclarationKind, K3ExportSyntaxError,
};
use std::collections::HashMap;

/// The reported outcome relevant to dependency validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum K3DependencyReport<'report> {
    /// The row reports a class outside the decidable fragment or a recognised base family.
    NonInside,
    /// The row reports that the checker accepted the declaration.
    Accepted,
    /// The row reports a refusal with its original version-1 detail.
    Refused(&'report str),
}

pub(super) fn compare<'row, 'report>(
    names: &NameTable,
    expressions: &[ExprRow],
    rows: impl IntoIterator<
        Item = (
            K3DeclarationIndexRow,
            usize,
            K3FragmentClass,
            Option<&'row Statement>,
        ),
    >,
    reports: impl IntoIterator<Item = K3DependencyReport<'report>>,
) -> Result<usize, K3ExportSyntaxError> {
    use K3DependencyReport::{Accepted, NonInside, Refused};
    use K3FragmentClass::{Inside, Outside, Recognised};

    let mut reports = reports.into_iter();
    let mut earlier_refused = HashMap::new();
    let mut walk = None;
    let mut last_line = 0;
    let mut dependency_refusals = 0;
    for (ordinal, (row, name, class, statement)) in rows.into_iter().enumerate() {
        let line = row.line;
        last_line = line;
        let report = reports
            .next()
            .ok_or_else(|| invalid(line, "missing dependency report for export declaration"))?;
        let detail = match (class, report) {
            (Outside | Recognised, NonInside) => continue,
            (Inside, Accepted) => None,
            (Inside, Refused(detail)) => Some(detail),
            _ => {
                return Err(invalid(
                    line,
                    format!(
                        "dependency report does not match the independent {} fragment class",
                        class.as_str()
                    ),
                ));
            }
        };
        let statement = statement
            .filter(|statement| {
                statement.eligible
                    && matches!(row.kind, K3DeclarationKind::Def | K3DeclarationKind::Thm | K3DeclarationKind::Opaque)
            })
            .ok_or_else(|| invalid(line, "inside declaration has no eligible ordinary statement for dependency comparison"))?;
        let dependency = detail.and_then(|text| text.strip_prefix("dependency:"));
        let mut earliest = None;
        let mut named_match = false;
        if !earlier_refused.is_empty()
            && !walk
                .get_or_insert_with(|| ExpressionWalk::new(expressions))
                .visit(statement, ordinal + 1, |citation| {
                    if let Some(&owed) = earlier_refused.get(&citation) {
                        earliest = Some(earliest.map_or(owed, |first: usize| first.min(owed)));
                        named_match = named_match
                            || dependency
                                .is_some_and(|expected| names.matches_echo(citation, expected));
                    }
                    true
                })
        {
            return Err(invalid(
                line,
                "cannot walk the inside declaration's expression rows",
            ));
        }

        match (detail, earliest) {
            (None, Some(owed)) => {
                return Err(invalid(
                    line,
                    format!("accepted row cites earlier refused declaration at line {owed}"),
                ));
            }
            (None, None) => {}
            (Some(_), owed) => {
                match (owed, dependency) {
                    (Some(_), Some(_)) if named_match => dependency_refusals += 1,
                    (Some(owed), None) => {
                        return Err(invalid(
                            line,
                            format!("missing dependency reason for earlier refused declaration at line {owed}"),
                        ));
                    }
                    (_, Some(_)) => {
                        return Err(invalid(
                            line,
                            "dependency reason does not name a directly cited earlier refused declaration",
                        ));
                    }
                    (None, None) => {}
                }
                earlier_refused.insert(name, line);
            }
        }
    }
    if reports.next().is_some() {
        return Err(invalid(
            last_line,
            "extra dependency report after the last export declaration",
        ));
    }
    Ok(dependency_refusals)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ndjson::json::{parse_line, JsonValue};
    use K3DependencyReport::{Accepted, NonInside, Refused};
    use K3FragmentClass::{Inside, Outside, Recognised};

    fn names() -> NameTable {
        let mut names = NameTable::default();
        for (id, text) in ["A", "β", "C", "D"].into_iter().enumerate() {
            let row = format!(r#"{{"in":{},"str":{{"pre":0,"str":"{text}"}}}}"#, id + 1);
            let JsonValue::Object(entries) = parse_line(row.as_bytes()).unwrap() else {
                panic!("expected a name fixture");
            };
            names.visit(id + 2, entries).unwrap();
        }
        names
    }

    fn statement(ty: usize, value: usize) -> Statement {
        Statement {
            parameters: Vec::new(),
            ty,
            value,
            eligible: true,
        }
    }

    fn constant(name: usize) -> ExprRow {
        ExprRow::Const {
            name,
            levels: Vec::new(),
        }
    }

    fn inside(
        line: usize,
        name: usize,
        statement: &Statement,
    ) -> (
        K3DeclarationIndexRow,
        usize,
        K3FragmentClass,
        Option<&Statement>,
    ) {
        (
            K3DeclarationIndexRow {
                line,
                kind: K3DeclarationKind::Def,
            },
            name,
            Inside,
            Some(statement),
        )
    }

    fn expect_error(result: Result<usize, K3ExportSyntaxError>, expected_line: usize, text: &str) {
        let Err(K3ExportSyntaxError::Invalid { line, reason }) = result else {
            panic!("expected refusal at {expected_line} for {text}");
        };
        assert_eq!(line, expected_line);
        assert!(reason.contains(text), "{reason}");
    }

    #[test]
    fn any_direct_owed_name_is_valid_but_an_accept_reports_the_earliest_line() {
        let names = names();
        let expressions = [
            ExprRow::Sort(0),
            constant(1),
            constant(2),
            ExprRow::MData(1),
        ];
        let independent = statement(0, 0);
        let owes_two = statement(2, 3);
        let rows = [
            inside(10, 1, &independent),
            inside(20, 2, &independent),
            inside(30, 3, &owes_two),
        ];
        for name in ["[s1:A]", "[s2:β]"] {
            let detail = format!("dependency:{name}");
            let reports = [Refused(""), Refused("opaque detail"), Refused(&detail)];
            assert_eq!(compare(&names, &expressions, rows, reports).unwrap(), 1);
        }
        expect_error(
            compare(
                &names,
                &expressions,
                rows,
                [Refused(""), Refused(""), Accepted],
            ),
            30,
            "accepted row cites earlier refused declaration at line 10",
        );
        for wrong in ["dependency:[s1:β]", "dependency:", "dependency:[s1:C]"] {
            expect_error(
                compare(
                    &names,
                    &expressions,
                    rows,
                    [Refused(""), Refused(""), Refused(wrong)],
                ),
                30,
                "dependency reason does not name",
            );
        }
        expect_error(
            compare(
                &names,
                &expressions,
                rows,
                [Refused(""), Refused(""), Refused("Dependency:[s1:A]")],
            ),
            30,
            "missing dependency reason for earlier refused declaration at line 10",
        );
    }

    #[test]
    fn neither_self_nor_forward_citations_owe_a_dependency() {
        let names = names();
        let expressions = [
            ExprRow::Sort(0),
            constant(2),
            constant(3),
            ExprRow::App(1, 2),
        ];
        let independent = statement(0, 0);
        let owes_neither = statement(0, 3);
        let rows = [
            inside(10, 1, &independent),
            inside(20, 2, &owes_neither),
            inside(30, 3, &independent),
        ];
        for detail in ["", "custom: unchanged", " dependency:[s1:A]"] {
            assert_eq!(
                compare(
                    &names,
                    &expressions,
                    rows,
                    [Refused(""), Refused(detail), Refused("")]
                )
                .unwrap(),
                0
            );
        }
        for wrong in ["dependency:[s2:β]", "dependency:[s1:C]"] {
            expect_error(
                compare(
                    &names,
                    &expressions,
                    rows,
                    [Refused(""), Refused(wrong), Refused("")],
                ),
                20,
                "dependency reason does not name",
            );
        }
    }

    #[test]
    fn a_later_refusal_owes_its_direct_citation_only() {
        let names = names();
        let expressions = [ExprRow::Sort(0), constant(1), constant(2)];
        let independent = statement(0, 0);
        let owes_first = statement(1, 0);
        let owes_second = statement(0, 2);
        let rows = [
            inside(10, 1, &independent),
            inside(20, 4, &independent),
            inside(30, 2, &owes_first),
            inside(40, 3, &owes_second),
        ];
        let prefix = [Refused(""), Refused("opaque"), Refused("dependency:[s1:A]")];
        for wrong in ["dependency:[s1:A]", "dependency:[s1:D]"] {
            expect_error(
                compare(
                    &names,
                    &expressions,
                    rows,
                    prefix.into_iter().chain([Refused(wrong)]),
                ),
                40,
                "dependency reason does not name",
            );
        }
        assert_eq!(
            compare(
                &names,
                &expressions,
                rows,
                prefix.into_iter().chain([Refused("dependency:[s2:β]")])
            )
            .unwrap(),
            2
        );
    }

    #[test]
    fn checks_report_class_and_cardinality_for_library_callers() {
        let names = names();
        let expressions = [ExprRow::Sort(0)];
        let independent = statement(0, 0);
        let decision = inside(10, 1, &independent);
        let block = K3DeclarationIndexRow {
            line: 20,
            kind: K3DeclarationKind::Inductive,
        };
        let rows = [decision, (block, 2, Recognised, None)];
        for (reports, line, reason) in [
            (vec![Accepted], 20, "missing dependency report"),
            (
                vec![Accepted, NonInside, Accepted],
                20,
                "extra dependency report",
            ),
            (vec![Accepted, Refused("")], 20, "recognised fragment class"),
            (vec![NonInside, NonInside], 10, "inside fragment class"),
        ] {
            expect_error(compare(&names, &expressions, rows, reports), line, reason);
        }
        expect_error(
            compare(
                &names,
                &expressions,
                [(block, 2, Outside, None)],
                [Accepted],
            ),
            20,
            "outside fragment class",
        );
        assert_eq!(
            compare(&names, &expressions, rows, [Accepted, NonInside]).unwrap(),
            0
        );
    }
}
