// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Validate the K3 export's expression rows in wire order.

use super::{
    exact_fields, index, invalid, levels::LevelTable, require_natural, take_pair,
    K3ExportSyntaxError, MAX_UNFOLDED_NODES,
};
use crate::ndjson::json::JsonValue;

#[derive(Debug, PartialEq, Eq)]
pub(super) enum ExprRow {
    BVar(String),
    Sort(usize),
    Const { name: usize, levels: Vec<usize> },
    App(usize, usize),
    Lam(usize, usize),
    Pi(usize, usize),
    Let(usize, usize, usize),
    MData(usize),
    Unsupported,
}

#[derive(Default)]
pub(super) struct ExpressionTable {
    // Each reference contributes the size of its unfolded subtree, including
    // repeated references. Keep one size per earlier row without building terms.
    sizes: Vec<usize>,
    rows: Option<Vec<ExprRow>>,
}

impl ExpressionTable {
    pub(super) fn with_echo_rows() -> Self {
        Self {
            rows: Some(Vec::new()),
            ..Self::default()
        }
    }

    /// The shallow rows indexed by expression ID.
    pub(super) fn into_echo_rows(self) -> Option<Vec<ExprRow>> {
        self.rows
    }

    pub(super) fn echo_rows(&self) -> Option<&[ExprRow]> {
        self.rows.as_deref()
    }

    pub(super) fn visit(
        &mut self,
        line: usize,
        entries: Vec<(String, JsonValue)>,
        explicit_names: usize,
        levels: &LevelTable,
    ) -> Result<(), K3ExportSyntaxError> {
        let (id, (tag, body)) = take_pair(entries, "ie")
            .ok_or_else(|| invalid(line, "expected exactly two fields in an expression record"))?;
        let next = self.explicit_count();
        if index(&id) != Some(next) {
            return Err(invalid(
                line,
                format!("expression record out of sequence (expected index {next})"),
            ));
        }

        let (size, row) = match tag.as_str() {
            "bvar" => match body {
                JsonValue::Number(number) if number.canonical_natural => {
                    (1, ExprRow::BVar(number.text))
                }
                _ => return Err(invalid(line, "ie.bvar expects a natural number")),
            },
            "sort" => {
                let (level, size) = levels.earlier(line, &body)?;
                (size + 1, ExprRow::Sort(level))
            }
            "const" => {
                let [name, us] =
                    exact_fields(line, format_args!("ie.{tag}"), &body, ["name", "us"])?;
                let name = require_name(line, name, explicit_names)?;
                let JsonValue::Array(us) = us else {
                    return Err(invalid(
                        line,
                        "ie.const.us expects an array of level indices",
                    ));
                };
                let mut nodes = 1_usize;
                let retain = self.rows.is_some();
                let mut row_levels = if retain {
                    Vec::with_capacity(us.len())
                } else {
                    Vec::new()
                };
                for level in us {
                    let (id, size) = levels.earlier(line, level)?;
                    nodes = nodes.saturating_add(size);
                    if retain {
                        row_levels.push(id);
                    }
                }
                (
                    nodes,
                    ExprRow::Const {
                        name,
                        levels: row_levels,
                    },
                )
            }
            "app" => {
                let [function, argument] =
                    exact_fields(line, format_args!("ie.{tag}"), &body, ["fn", "arg"])?;
                let (function, function_size) = self.earlier(line, function)?;
                let (argument, argument_size) = self.earlier(line, argument)?;
                (
                    function_size + argument_size + 1,
                    ExprRow::App(function, argument),
                )
            }
            "lam" | "forallE" => {
                let [info, name, ty, body] = exact_fields(
                    line,
                    format_args!("ie.{tag}"),
                    &body,
                    ["binderInfo", "name", "type", "body"],
                )?;
                match info {
                    JsonValue::String(info)
                        if matches!(
                            info.as_str(),
                            "default" | "implicit" | "strictImplicit" | "instImplicit"
                        ) => {}
                    _ => return Err(invalid(line, format!("ie.{tag} has invalid binderInfo"))),
                }
                require_name(line, name, explicit_names)?;
                let (ty, ty_size) = self.earlier(line, ty)?;
                let (body, body_size) = self.earlier(line, body)?;
                let row = if tag == "lam" {
                    ExprRow::Lam(ty, body)
                } else {
                    ExprRow::Pi(ty, body)
                };
                (ty_size + body_size + 1, row)
            }
            "letE" => {
                let [name, ty, value, body, nondep] = exact_fields(
                    line,
                    format_args!("ie.{tag}"),
                    &body,
                    ["name", "type", "value", "body", "nondep"],
                )?;
                require_name(line, name, explicit_names)?;
                if !matches!(nondep, JsonValue::Bool(_)) {
                    return Err(invalid(line, "ie.letE.nondep expects a boolean"));
                }
                let (ty, ty_size) = self.earlier(line, ty)?;
                let (value, value_size) = self.earlier(line, value)?;
                let (body, body_size) = self.earlier(line, body)?;
                (
                    ty_size + value_size + body_size + 1,
                    ExprRow::Let(ty, value, body),
                )
            }
            "natVal" if matches!(&body, JsonValue::String(text) if canonical_decimal(text)) => {
                (1, ExprRow::Unsupported)
            }
            "natVal" => {
                return Err(invalid(
                    line,
                    "ie.natVal expects a string of canonical decimal digits",
                ));
            }
            "strVal" if matches!(body, JsonValue::String(_)) => (1, ExprRow::Unsupported),
            "strVal" => return Err(invalid(line, "ie.strVal expects a string")),
            "proj" => {
                let [name, idx, structure] = exact_fields(
                    line,
                    format_args!("ie.{tag}"),
                    &body,
                    ["typeName", "idx", "struct"],
                )?;
                require_name(line, name, explicit_names)?;
                require_natural(line, "ie.proj.idx", idx)?;
                let (_, size) = self.earlier(line, structure)?;
                (size + 1, ExprRow::Unsupported)
            }
            "mdata" => {
                let [_, expr] =
                    exact_fields(line, format_args!("ie.{tag}"), &body, ["data", "expr"])?;
                let (expr, size) = self.earlier(line, expr)?;
                // Count the direct wire child, then shortcut transparent
                // chains so shared echoes need not rewalk the metadata.
                let child = match self.echo_rows().and_then(|rows| rows.get(expr)) {
                    Some(ExprRow::MData(child)) => *child,
                    _ => expr,
                };
                (size + 1, ExprRow::MData(child))
            }
            _ => {
                return Err(invalid(
                    line,
                    format!("unknown expression record kind {tag:?}"),
                ))
            }
        };
        if size > MAX_UNFOLDED_NODES {
            return Err(invalid(
                line,
                format!("expression has more than {MAX_UNFOLDED_NODES} nodes as a tree"),
            ));
        }
        self.sizes.push(size);
        if let Some(rows) = &mut self.rows {
            rows.push(row);
        }
        Ok(())
    }

    fn earlier(
        &self,
        line: usize,
        operand: &JsonValue,
    ) -> Result<(usize, usize), K3ExportSyntaxError> {
        let id = index(operand).ok_or_else(|| invalid(line, "expected an expression index"))?;
        self.sizes.get(id).map(|&size| (id, size)).ok_or_else(|| {
            invalid(
                line,
                format!("expression {id} is not defined by an earlier row"),
            )
        })
    }

    pub(super) fn explicit_count(&self) -> usize {
        self.sizes.len()
    }

    pub(super) fn max_unfolded_nodes(&self) -> usize {
        self.sizes.iter().copied().max().unwrap_or(0)
    }
}

fn require_name(
    line: usize,
    value: &JsonValue,
    explicit_names: usize,
) -> Result<usize, K3ExportSyntaxError> {
    let id = index(value).ok_or_else(|| invalid(line, "expected a name index"))?;
    if id > explicit_names {
        return Err(invalid(
            line,
            format!("name {id} is not defined by an earlier row"),
        ));
    }
    Ok(id)
}

fn canonical_decimal(text: &str) -> bool {
    match text.as_bytes() {
        [b'0'] => true,
        [b'1'..=b'9', digits @ ..] => digits.iter().all(u8::is_ascii_digit),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ndjson::json::parse_line;

    fn record(text: &str) -> Vec<(String, JsonValue)> {
        let JsonValue::Object(entries) = parse_line(text.as_bytes()).expect("JSON fixture") else {
            panic!("expected a JSON object");
        };
        entries
    }

    #[test]
    fn shortcuts_transparent_metadata_without_changing_wire_sizes() {
        let levels = LevelTable::default();
        let mut table = ExpressionTable::with_echo_rows();
        for (line, row) in [
            (2, r#"{"ie":0,"bvar":0}"#),
            (3, r#"{"ie":1,"mdata":{"expr":0,"data":[]}}"#),
            (4, r#"{"ie":2,"mdata":{"expr":1,"data":false}}"#),
            (5, r#"{"ie":3,"app":{"fn":1,"arg":2}}"#),
        ] {
            table.visit(line, record(row), 0, &levels).unwrap();
        }
        assert_eq!(table.sizes, [1, 2, 3, 6]);
        let wire = table.into_echo_rows().unwrap();
        assert_eq!(wire[1], ExprRow::MData(0));
        assert_eq!(wire[2], ExprRow::MData(0));
        assert_eq!(wire[3], ExprRow::App(1, 2));
    }

    fn expect_invalid(
        table: &mut ExpressionTable,
        levels: &LevelTable,
        text: &str,
        reason_part: &str,
    ) {
        let before = table.explicit_count();
        let echo_count = table.rows.as_ref().map(Vec::len);
        let Err(K3ExportSyntaxError::Invalid { line, reason }) =
            table.visit(23, record(text), 0, levels)
        else {
            panic!("expected K3 refusal for {text}");
        };
        assert_eq!(line, 23);
        assert!(reason.contains(reason_part), "{text}: {reason}");
        assert_eq!(table.explicit_count(), before);
        assert_eq!(table.rows.as_ref().map(Vec::len), echo_count);
    }

    #[test]
    fn checks_all_expression_shapes_and_counts_every_child() {
        let mut levels = LevelTable::default();
        levels
            .visit(2, record(r#"{"il":1,"max":[0,0]}"#), 0)
            .unwrap();
        let mut table = ExpressionTable::with_echo_rows();
        assert_eq!(table.max_unfolded_nodes(), 0);
        for (offset, row) in [
            r#"{"bvar":18446744073709551616,"ie":0}"#,
            r#"{"ie":1,"sort":1}"#,
            r#"{"ie":2,"const":{"us":[1,0,1],"name":1}}"#,
            r#"{"ie":3,"app":{"arg":1,"fn":0}}"#,
            r#"{"ie":4,"lam":{"name":0,"type":1,"body":2,"binderInfo":"instImplicit"}}"#,
            r#"{"ie":5,"forallE":{"name":1,"type":1,"body":3,"binderInfo":"strictImplicit"}}"#,
            r#"{"ie":6,"letE":{"name":0,"type":1,"value":0,"body":5,"nondep":false}}"#,
            r#"{"ie":7,"natVal":"1844674407370955161618446744073709551616"}"#,
            "{\"ie\":8,\"strVal\":\"one\u{2028}two\"}",
            r#"{"ie":9,"proj":{"typeName":1,"idx":18446744073709551616,"struct":6}}"#,
            r#"{"ie":10,"mdata":{"data":[false,{"arbitrary":null}],"expr":9}}"#,
        ]
        .into_iter()
        .enumerate()
        {
            table.visit(offset + 4, record(row), 1, &levels).unwrap();
        }
        assert_eq!(table.sizes, [1, 4, 8, 6, 13, 11, 17, 1, 1, 18, 19]);
        assert_eq!(table.explicit_count(), 11);
        assert_eq!(table.max_unfolded_nodes(), 19);
        assert_eq!(
            table.into_echo_rows().unwrap(),
            [
                ExprRow::BVar("18446744073709551616".to_owned()),
                ExprRow::Sort(1),
                ExprRow::Const {
                    name: 1,
                    levels: vec![1, 0, 1],
                },
                ExprRow::App(0, 1),
                ExprRow::Lam(1, 2),
                ExprRow::Pi(1, 3),
                ExprRow::Let(1, 0, 5),
                ExprRow::Unsupported,
                ExprRow::Unsupported,
                ExprRow::Unsupported,
                ExprRow::MData(9),
            ]
        );
    }

    #[test]
    fn refuses_bad_shapes_ids_and_forward_references() {
        let levels = LevelTable::default();
        let mut table = ExpressionTable::with_echo_rows();
        expect_invalid(
            &mut table,
            &levels,
            r#"{"ie":0,"app":{"fn":0,"arg":0}}"#,
            "expression 0 is not defined",
        );
        table
            .visit(2, record(r#"{"ie":0,"bvar":0}"#), 0, &levels)
            .unwrap();
        for (row, reason) in [
            (r#"{"ie":1}"#, "exactly two fields"),
            (r#"{"ie":1,"sort":0,"extra":0}"#, "exactly two fields"),
            (r#"{"ie":0,"sort":0}"#, "expected index 1"),
            (r#"{"ie":2,"sort":0}"#, "expected index 1"),
            (r#"{"ie":"1","sort":0}"#, "expected index 1"),
            (
                r#"{"ie":1,"bvar":false}"#,
                "ie.bvar expects a natural number",
            ),
            (r#"{"ie":1,"sort":1}"#, "level 1 is not defined"),
            (
                r#"{"ie":1,"const":{"name":1,"us":[]}}"#,
                "name 1 is not defined",
            ),
            (
                r#"{"ie":1,"const":{"name":0,"us":[1]}}"#,
                "level 1 is not defined",
            ),
            (r#"{"ie":1,"const":{"name":0,"us":0}}"#, "expects an array"),
            (r#"{"ie":1,"app":{"fn":0,"other":0}}"#, "exactly the fields"),
            (
                r#"{"ie":1,"app":{"fn":0,"arg":2}}"#,
                "expression 2 is not defined",
            ),
            (
                r#"{"ie":1,"app":{"fn":0,"arg":"0"}}"#,
                "expected an expression index",
            ),
            (
                r#"{"ie":1,"lam":{"name":0,"type":0,"body":0,"binderInfo":"explicit"}}"#,
                "invalid binderInfo",
            ),
            (
                r#"{"ie":1,"letE":{"name":0,"type":0,"value":0,"body":0,"nondep":0}}"#,
                "nondep expects a boolean",
            ),
            (r#"{"ie":1,"natVal":"00"}"#, "canonical decimal digits"),
            (r#"{"ie":1,"natVal":"١"}"#, "canonical decimal digits"),
            (r#"{"ie":1,"natVal":0}"#, "canonical decimal digits"),
            (r#"{"ie":1,"strVal":0}"#, "ie.strVal expects a string"),
            (
                r#"{"ie":1,"proj":{"typeName":0,"idx":"0","struct":0}}"#,
                "idx expects a natural",
            ),
            (r#"{"ie":1,"mdata":{"expr":0}}"#, "exactly the fields"),
            (
                r#"{"ie":1,"mdata":{"data":null,"expr":1}}"#,
                "expression 1 is not defined",
            ),
            (r#"{"ie":1,"fvar":0}"#, "unknown expression record kind"),
        ] {
            expect_invalid(&mut table, &levels, row, reason);
        }
    }

    #[test]
    fn accepts_expression_tree_at_the_cap_and_refuses_one_more_node() {
        let levels = LevelTable::default();
        let mut table = ExpressionTable::with_echo_rows();
        table
            .visit(2, record(r#"{"ie":0,"bvar":0}"#), 0, &levels)
            .unwrap();
        for id in 1..20 {
            let earlier = id - 1;
            let row = format!(r#"{{"ie":{id},"app":{{"fn":{earlier},"arg":{earlier}}}}}"#);
            table.visit(id + 2, record(&row), 0, &levels).unwrap();
        }
        assert_eq!(table.max_unfolded_nodes(), MAX_UNFOLDED_NODES - 1);
        table
            .visit(
                22,
                record(r#"{"ie":20,"mdata":{"data":null,"expr":19}}"#),
                0,
                &levels,
            )
            .unwrap();
        assert_eq!(table.max_unfolded_nodes(), MAX_UNFOLDED_NODES);
        expect_invalid(
            &mut table,
            &levels,
            r#"{"ie":21,"mdata":{"data":null,"expr":20}}"#,
            "more than 1048576 nodes as a tree",
        );
    }

    #[test]
    fn adds_level_sizes_including_repeated_and_wide_constant_lists() {
        let mut levels = LevelTable::default();
        for id in 1..20 {
            let earlier = id - 1;
            let row = format!(r#"{{"il":{id},"max":[{earlier},{earlier}]}}"#);
            levels.visit(id + 1, record(&row), 0).unwrap();
        }
        levels
            .visit(21, record(r#"{"il":20,"succ":19}"#), 0)
            .unwrap();

        let mut table = ExpressionTable::default();
        for (offset, row) in [
            r#"{"ie":0,"sort":19}"#,
            r#"{"ie":1,"const":{"name":0,"us":[18,18,0]}}"#,
        ]
        .into_iter()
        .enumerate()
        {
            table.visit(22 + offset, record(row), 0, &levels).unwrap();
        }
        assert_eq!(table.sizes, [MAX_UNFOLDED_NODES; 2]);
        expect_invalid(
            &mut table,
            &levels,
            r#"{"ie":2,"const":{"name":0,"us":[19,0]}}"#,
            "more than 1048576 nodes as a tree",
        );
        // An unchecked 32-bit sum would wrap this count back to one.
        let us = vec!["20"; 4096].join(",");
        let wide = format!(r#"{{"ie":2,"const":{{"name":0,"us":[{us}]}}}}"#);
        expect_invalid(
            &mut table,
            &levels,
            &wide,
            "more than 1048576 nodes as a tree",
        );
        assert!(table.into_echo_rows().is_none());
    }
}
