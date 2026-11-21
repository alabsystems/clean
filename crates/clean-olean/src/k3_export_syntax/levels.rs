// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Validate the K3 export's level rows in wire order.

use super::{index, invalid, take_pair, K3ExportSyntaxError, MAX_UNFOLDED_NODES};
use crate::ndjson::json::JsonValue;

#[derive(Debug, PartialEq, Eq)]
pub(super) enum LevelRow {
    Zero,
    Succ(usize),
    Max(usize, usize),
    IMax(usize, usize),
    Param(usize),
}

pub(super) struct LevelTable {
    // The K3 reader counts each reference as a separate occurrence in the
    // unfolded tree. Store the size once per ID without unfolding the tree.
    sizes: Vec<usize>,
    rows: Option<Vec<LevelRow>>,
}

impl Default for LevelTable {
    fn default() -> Self {
        Self {
            sizes: vec![1],
            rows: None,
        }
    }
}

impl LevelTable {
    pub(super) fn with_echo_rows() -> Self {
        Self {
            rows: Some(vec![LevelRow::Zero]),
            ..Self::default()
        }
    }

    /// The shallow rows indexed by level ID, including implicit zero.
    pub(super) fn into_echo_rows(self) -> Option<Vec<LevelRow>> {
        self.rows
    }

    pub(super) fn echo_rows(&self) -> Option<&[LevelRow]> {
        self.rows.as_deref()
    }

    pub(super) fn visit(
        &mut self,
        line: usize,
        entries: Vec<(String, JsonValue)>,
        explicit_names: usize,
    ) -> Result<(), K3ExportSyntaxError> {
        let (id, (tag, body)) = take_pair(entries, "il")
            .ok_or_else(|| invalid(line, "expected exactly two fields in a level record"))?;
        let next = self.sizes.len();
        if index(&id) != Some(next) {
            return Err(invalid(
                line,
                format!("level record out of sequence (expected index {next})"),
            ));
        }

        let (size, row) = match tag.as_str() {
            "succ" => {
                let (operand, size) = self.earlier(line, &body)?;
                (size + 1, LevelRow::Succ(operand))
            }
            "max" | "imax" => {
                let wrong_arity =
                    || invalid(line, format!("level {tag} expects two level indices"));
                let JsonValue::Array(operands) = &body else {
                    return Err(wrong_arity());
                };
                let [left, right] = operands.as_slice() else {
                    return Err(wrong_arity());
                };
                let (left, left_size) = self.earlier(line, left)?;
                let (right, right_size) = self.earlier(line, right)?;
                let row = if tag == "max" {
                    LevelRow::Max(left, right)
                } else {
                    LevelRow::IMax(left, right)
                };
                (left_size + right_size + 1, row)
            }
            "param" => {
                let id = index(&body)
                    .ok_or_else(|| invalid(line, "expected a name index for a level parameter"))?;
                if id > explicit_names {
                    return Err(invalid(
                        line,
                        format!("name {id} is not defined by an earlier row"),
                    ));
                }
                (1, LevelRow::Param(id))
            }
            _ => return Err(invalid(line, format!("unknown level record kind {tag:?}"))),
        };
        if size > MAX_UNFOLDED_NODES {
            return Err(invalid(
                line,
                format!("level has more than {MAX_UNFOLDED_NODES} nodes as a tree"),
            ));
        }
        self.sizes.push(size);
        if let Some(rows) = &mut self.rows {
            rows.push(row);
        }
        Ok(())
    }

    pub(super) fn earlier(
        &self,
        line: usize,
        operand: &JsonValue,
    ) -> Result<(usize, usize), K3ExportSyntaxError> {
        let id = index(operand).ok_or_else(|| invalid(line, "expected a level index"))?;
        self.sizes
            .get(id)
            .map(|&size| (id, size))
            .ok_or_else(|| invalid(line, format!("level {id} is not defined by an earlier row")))
    }

    pub(super) fn explicit_count(&self) -> usize {
        self.sizes.len() - 1
    }

    pub(super) fn max_unfolded_nodes(&self) -> usize {
        self.sizes.iter().copied().max().unwrap_or(1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ndjson::json::parse_line;

    fn visit(
        table: &mut LevelTable,
        line: usize,
        text: &str,
        explicit_names: usize,
    ) -> Result<(), K3ExportSyntaxError> {
        let JsonValue::Object(entries) = parse_line(text.as_bytes()).expect("JSON fixture") else {
            panic!("expected a JSON object");
        };
        table.visit(line, entries, explicit_names)
    }

    fn expect_invalid(table: &mut LevelTable, text: &str, explicit_names: usize, expected: &str) {
        let before = table.explicit_count();
        let echo_count = table.rows.as_ref().map(Vec::len);
        let Err(K3ExportSyntaxError::Invalid { line, reason }) =
            visit(table, 11, text, explicit_names)
        else {
            panic!("expected K3 refusal for {text}");
        };
        assert_eq!(line, 11);
        assert!(reason.contains(expected), "{text}: {reason}");
        assert_eq!(table.explicit_count(), before);
        assert_eq!(table.rows.as_ref().map(Vec::len), echo_count);
    }

    #[test]
    fn counts_levels_as_written_including_repeated_operands() {
        assert!(LevelTable::default().into_echo_rows().is_none());
        let mut table = LevelTable::with_echo_rows();
        assert_eq!(table.explicit_count(), 0);
        assert_eq!(table.max_unfolded_nodes(), 1);
        for (offset, (row, names)) in [
            (r#"{"il":1,"param":0}"#, 0),
            (r#"{"succ":0,"il":2}"#, 0),
            (r#"{"imax":[2,2],"il":3}"#, 0),
            (r#"{"il":4,"max":[3,0]}"#, 0),
            (r#"{"il":5,"param":1}"#, 1),
            (r#"{"il":6,"param":1}"#, 1),
        ]
        .into_iter()
        .enumerate()
        {
            visit(&mut table, offset + 2, row, names).expect("valid level");
        }
        assert_eq!(table.sizes.as_slice(), &[1, 1, 2, 5, 7, 1, 1]);
        assert_eq!(table.explicit_count(), 6);
        assert_eq!(table.max_unfolded_nodes(), 7);
        assert_eq!(
            table.into_echo_rows().unwrap(),
            [
                LevelRow::Zero,
                LevelRow::Param(0),
                LevelRow::Succ(0),
                LevelRow::IMax(2, 2),
                LevelRow::Max(3, 0),
                LevelRow::Param(1),
                LevelRow::Param(1),
            ]
        );
    }

    #[test]
    fn refuses_bad_shapes_ids_and_references() {
        let mut table = LevelTable::with_echo_rows();
        for (row, reason) in [
            (r#"{"il":1}"#, "exactly two fields"),
            (r#"{"il":1,"succ":0,"extra":0}"#, "exactly two fields"),
            (r#"{"il":0,"succ":0}"#, "expected index 1"),
            (r#"{"il":2,"succ":0}"#, "expected index 1"),
            (r#"{"il":true,"succ":0}"#, "expected index 1"),
            (
                r#"{"il":18446744073709551616,"succ":0}"#,
                "expected index 1",
            ),
            (r#"{"il":1,"zero":0}"#, "unknown level record kind"),
            (r#"{"il":1,"succ":1}"#, "level 1 is not defined"),
            (r#"{"il":1,"max":[0,2]}"#, "level 2 is not defined"),
            (r#"{"il":1,"imax":[1,0]}"#, "level 1 is not defined"),
            (r#"{"il":1,"max":[0]}"#, "expects two level indices"),
            (r#"{"il":1,"imax":[0,0,0]}"#, "expects two level indices"),
            (
                r#"{"il":1,"max":{"first":0,"second":0}}"#,
                "expects two level indices",
            ),
            (r#"{"il":1,"max":[0,false]}"#, "expected a level index"),
            (
                r#"{"il":1,"succ":18446744073709551616}"#,
                "expected a level index",
            ),
            (r#"{"il":1,"param":"0"}"#, "expected a name index"),
            (r#"{"il":1,"param":2}"#, "name 2 is not defined"),
        ] {
            expect_invalid(&mut table, row, 1, reason);
        }
        visit(&mut table, 20, r#"{"il":1,"succ":0}"#, 0).expect("valid level");
        expect_invalid(&mut table, r#"{"il":1,"param":0}"#, 0, "expected index 2");
    }

    #[test]
    fn accepts_the_exact_tree_cap_and_refuses_one_more_node() {
        let mut table = LevelTable::with_echo_rows();
        for id in 1..20 {
            let earlier = id - 1;
            let row = format!(r#"{{"il":{id},"max":[{earlier},{earlier}]}}"#);
            visit(&mut table, id + 1, &row, 0).expect("level within the tree cap");
        }
        assert_eq!(table.max_unfolded_nodes(), 1_048_575);
        visit(&mut table, 21, r#"{"il":20,"succ":19}"#, 0).expect("level at the tree cap");
        assert_eq!(table.max_unfolded_nodes(), 1_048_576);
        expect_invalid(
            &mut table,
            r#"{"il":21,"succ":20}"#,
            0,
            "more than 1048576 nodes as a tree",
        );
        assert_eq!(table.explicit_count(), 20);
    }
}
