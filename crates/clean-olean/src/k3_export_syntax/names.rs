// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Validate the K3 export's name rows in wire order.

use super::statement_echo::EchoOutput;
use super::{has_key, index, invalid, take_pair, K3ExportSyntaxError};
use crate::ndjson::json::JsonValue;
use hashbrown::{hash_table::Entry, HashTable};
use smallvec::SmallVec;
use std::fmt;
use std::hash::{BuildHasher, RandomState};

#[derive(Eq, Hash, PartialEq)]
enum Component {
    Str(String),
    Num(String),
}

impl Component {
    fn echo_width(&self) -> Option<usize> {
        match self {
            Self::Str(text) => {
                let digits = text.len().checked_ilog10().unwrap_or(0) as usize + 1;
                text.len().checked_add(digits + 2)
            }
            Self::Num(text) => text.len().checked_add(1),
        }
    }

    fn strip_echo<'echo>(&self, echo: &'echo str) -> Option<&'echo str> {
        match self {
            Self::Str(text) => {
                let prefix = echo.strip_suffix(text.as_str())?.strip_suffix(':')?;
                strip_decimal_suffix(prefix, text.len())?.strip_suffix('s')
            }
            Self::Num(text) => echo.strip_suffix(text.as_str())?.strip_suffix('n'),
        }
    }
}

fn strip_decimal_suffix(mut echo: &str, mut number: usize) -> Option<&str> {
    loop {
        let digit = char::from(b'0' + (number % 10) as u8);
        echo = echo.strip_suffix(digit)?;
        number /= 10;
        if number == 0 {
            return Some(echo);
        }
    }
}

#[derive(Default)]
pub(super) struct NameTable {
    // Dense index i holds explicit name ID i + 1. Anonymous ID zero has no row.
    components: Vec<(usize, Component)>,
    // A predecessor ID and tagged component uniquely identify a name. The
    // hash table points into the dense table so each component is stored once.
    indices: HashTable<usize>,
    hash_builder: RandomState,
}

impl NameTable {
    pub(super) fn visit(
        &mut self,
        line: usize,
        entries: Vec<(String, JsonValue)>,
    ) -> Result<(), K3ExportSyntaxError> {
        if !has_key(&entries, "in") {
            return Ok(());
        }
        let (id, (tag, body)) = take_pair(entries, "in")
            .ok_or_else(|| invalid(line, "expected exactly two fields in a name record"))?;
        let next = self.explicit_count() + 1;
        if index(&id) != Some(next) {
            return Err(invalid(
                line,
                format!("name record out of sequence (expected index {next})"),
            ));
        }

        let malformed_body = || invalid(line, "name record body has another shape");
        let JsonValue::Object(fields) = body else {
            return Err(malformed_body());
        };
        let (pre, (key, value)) = take_pair(fields, "pre").ok_or_else(malformed_body)?;
        let component = match (tag.as_str(), key.as_str(), value) {
            ("str", "str", JsonValue::String(text)) => {
                if text
                    .chars()
                    .any(|ch| matches!(ch, '\u{0085}' | '\u{2028}' | '\u{2029}'))
                {
                    return Err(invalid(
                        line,
                        "name component holds U+0085, U+2028 or U+2029",
                    ));
                }
                Component::Str(text)
            }
            ("num", "i", JsonValue::Number(number)) if number.canonical_natural => {
                Component::Num(number.text)
            }
            _ => return Err(malformed_body()),
        };
        let pre = index(&pre)
            .filter(|&pre| pre < next)
            .ok_or_else(|| invalid(line, "name predecessor is not defined by an earlier row"))?;
        let entry = (pre, component);
        let components = &self.components;
        let hash_builder = &self.hash_builder;
        let slot = self.indices.entry(
            hash_builder.hash_one(&entry),
            |&index| components[index] == entry,
            |&index| hash_builder.hash_one(&components[index]),
        );
        let Entry::Vacant(slot) = slot else {
            return Err(invalid(line, "a name an earlier name record gave"));
        };
        slot.insert(components.len());
        self.components.push(entry);
        Ok(())
    }

    pub(super) fn explicit_count(&self) -> usize {
        self.components.len()
    }

    /// Write the canonical name in forward order within the sink's byte budget.
    pub(super) fn write_echo(&self, mut id: usize, out: &mut impl EchoOutput) -> fmt::Result {
        let mut available = out.remaining().checked_sub(2).ok_or(fmt::Error)?;
        let mut ancestors: SmallVec<[&Component; 8]> = SmallVec::new();
        while id != 0 {
            let (pre, component) = self.components.get(id - 1).ok_or(fmt::Error)?;
            available = available
                .checked_sub(component.echo_width().ok_or(fmt::Error)?)
                .ok_or(fmt::Error)?;
            id = *pre;
            if id != 0 {
                available = available.checked_sub(1).ok_or(fmt::Error)?;
            }
            ancestors.push(component);
        }

        out.write_char('[')?;
        for (index, component) in ancestors.into_iter().rev().enumerate() {
            if index != 0 {
                out.write_char(' ')?;
            }
            match component {
                Component::Str(text) => write!(out, "s{}:{text}", text.len())?,
                Component::Num(text) => write!(out, "n{text}")?,
            }
        }
        out.write_char(']')
    }

    /// Match the canonical transcript echo by following predecessors from the
    /// last component. The component bytes may themselves contain separators.
    pub(super) fn matches_echo(&self, mut id: usize, expected: &str) -> bool {
        let Some(mut echo) = expected.strip_suffix(']') else {
            return false;
        };
        while id != 0 {
            let Some((pre, component)) = self.components.get(id - 1) else {
                return false;
            };
            let Some(prefix) = component.strip_echo(echo) else {
                return false;
            };
            id = *pre;
            echo = prefix;
            if id != 0 {
                let Some(prefix) = echo.strip_suffix(' ') else {
                    return false;
                };
                echo = prefix;
            }
        }
        echo == "["
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ndjson::json::parse_line;

    fn visit(table: &mut NameTable, line: usize, text: &str) -> Result<(), K3ExportSyntaxError> {
        let JsonValue::Object(entries) = parse_line(text.as_bytes()).expect("JSON fixture") else {
            panic!("expected a JSON object");
        };
        table.visit(line, entries)
    }

    fn expect_invalid(table: &mut NameTable, text: &str, expected: &str) {
        let Err(K3ExportSyntaxError::Invalid { line, reason }) = visit(table, 11, text) else {
            panic!("expected K3 refusal for {text}");
        };
        assert_eq!(line, 11);
        assert!(reason.contains(expected), "{text}: {reason}");
    }

    #[test]
    fn preserves_structural_names_as_written() {
        let mut table = NameTable::default();
        for (i, row) in [
            r#"{"str":{"str":"a.b","pre":0},"in":1}"#,
            r#"{"in":2,"str":{"pre":0,"str":"a"}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"in":3,"str":{"pre":2,"str":"b"}}"#,
            r#"{"in":4,"str":{"pre":0,"str":"7"}}"#,
            r#"{"in":5,"num":{"i":7,"pre":0}}"#,
            r#"{"in":6,"str":{"pre":0,"str":"․a․b"}}"#,
            r#"{"in":7,"num":{"pre":1,"i":18446744073709551616}}"#,
            r#"{"in":8,"str":{"pre":0,"str":""}}"#,
            r#"{"in":9,"str":{"pre":0,"str":"π"}}"#,
            r#"{"in":10,"str":{"pre":2,"str":"π"}}"#,
        ]
        .into_iter()
        .enumerate()
        {
            visit(&mut table, i + 2, row).expect("valid name table");
        }
        assert_eq!(table.explicit_count(), 10);
        for (id, echo) in [
            (0, "[]"),
            (1, "[s3:a.b]"),
            (3, "[s1:a s1:b]"),
            (4, "[s1:7]"),
            (5, "[n7]"),
            (6, "[s8:․a․b]"),
            (7, "[s3:a.b n18446744073709551616]"),
            (8, "[s0:]"),
            (9, "[s2:π]"),
            (10, "[s1:a s2:π]"),
        ] {
            assert!(table.matches_echo(id, echo), "{id}: {echo}");
        }
        assert!(!table.matches_echo(1, "[s1:a s1:b]"));
        assert!(!table.matches_echo(3, "[s3:a.b]"));
        assert!(!table.matches_echo(4, "[n7]"));
        assert!(!table.matches_echo(5, "[s1:7]"));
        assert!(!table.matches_echo(9, "[s1:π]"));
        assert!(!table.matches_echo(11, "[]"));
        assert!(!table.matches_echo(usize::MAX, "[]"));
        expect_invalid(
            &mut table,
            r#"{"in":11,"num":{"pre":1,"i":18446744073709551616}}"#,
            "earlier name record",
        );
        assert_eq!(table.explicit_count(), 10);
    }

    #[test]
    fn matches_literal_payload_and_refuses_noncanonical_echoes() {
        let mut table = NameTable::default();
        for (line, row) in [
            (2, r#"{"in":1,"str":{"pre":0,"str":"π"}}"#),
            (3, r#"{"in":2,"str":{"pre":1,"str":":] π [ "}}"#),
            (4, r#"{"in":3,"str":{"pre":2,"str":""}}"#),
            (5, r#"{"in":4,"num":{"pre":3,"i":0}}"#),
            (6, r#"{"in":5,"str":{"pre":0,"str":"0123456789"}}"#),
        ] {
            visit(&mut table, line, row).unwrap();
        }
        assert!(table.matches_echo(4, "[s2:π s8::] π [  s0: n0]"));
        assert!(table.matches_echo(5, "[s10:0123456789]"));
        for malformed in [
            "s2:π s8::] π [  s0: n0]",
            "[s2:π s8::] π [  s0: n0",
            "[s2:π s8::] π [  s0: n0] ",
            "[s2:π s8::] π [ s0: n0]",
            "[s2:π s08::] π [  s0: n0]",
            "[s2:π s8::] π [  s0: n00]",
            "[s2:π s8::] π [  s0:  n0]",
        ] {
            assert!(!table.matches_echo(4, malformed), "{malformed}");
        }
        assert!(!table.matches_echo(0, "[s0:]"));
        assert!(!table.matches_echo(3, "[]"));
    }

    #[test]
    fn matches_deep_names_and_retains_duplicate_checks_after_growth() {
        let mut table = NameTable::default();
        let depth = 4096;
        let mut echo = String::from("[");
        for id in 1..=depth {
            let pre = id - 1;
            let row = format!(r#"{{"in":{id},"str":{{"pre":{pre},"str":"π"}}}}"#);
            visit(&mut table, id + 1, &row).unwrap();
            if pre != 0 {
                echo.push(' ');
            }
            echo.push_str("s2:π");
        }
        echo.push(']');
        assert!(table.matches_echo(depth, &echo));
        assert!(!table.matches_echo(depth - 1, &echo));
        let duplicate = format!(r#"{{"in":{},"str":{{"pre":100,"str":"π"}}}}"#, depth + 1);
        expect_invalid(&mut table, &duplicate, "earlier name record");
        assert_eq!(table.explicit_count(), depth);
    }

    #[test]
    fn refuses_invalid_shape_indices_and_duplicate_names() {
        let mut table = NameTable::default();
        visit(&mut table, 2, r#"{"in":1,"str":{"pre":0,"str":"a"}}"#).unwrap();
        for (row, reason) in [
            (r#"{"in":0,"str":{"pre":0,"str":"x"}}"#, "out of sequence"),
            (r#"{"in":1,"str":{"pre":0,"str":"x"}}"#, "out of sequence"),
            (r#"{"in":3,"str":{"pre":0,"str":"x"}}"#, "out of sequence"),
            (r#"{"in":"2","str":{"pre":0,"str":"x"}}"#, "out of sequence"),
            (r#"{"in":2,"str":{"pre":2,"str":"x"}}"#, "predecessor"),
            (r#"{"in":2,"str":{"pre":9,"str":"x"}}"#, "predecessor"),
            (r#"{"in":2,"str":{"pre":"1","str":"x"}}"#, "predecessor"),
            (
                r#"{"in":2,"str":{"pre":0,"str":"a"}}"#,
                "earlier name record",
            ),
            (
                r#"{"in":2,"str":{"pre":0,"str":"x"},"extra":0}"#,
                "exactly two",
            ),
            (r#"{"in":2}"#, "exactly two"),
            (r#"{"in":2,"opaque":{"pre":0,"str":"x"}}"#, "another shape"),
            (r#"{"in":2,"str":[]}"#, "another shape"),
            (r#"{"in":2,"str":{"str":"x"}}"#, "another shape"),
            (
                r#"{"in":2,"str":{"pre":0,"str":"x","extra":0}}"#,
                "another shape",
            ),
            (r#"{"in":2,"num":{"pre":0,"i":"7"}}"#, "another shape"),
        ] {
            expect_invalid(&mut table, row, reason);
            assert_eq!(table.explicit_count(), 1);
        }
        visit(&mut table, 12, r#"{"in":2,"str":{"pre":1,"str":"a"}}"#).unwrap();
        assert_eq!(table.explicit_count(), 2);
    }

    #[test]
    fn refuses_line_separators_in_string_components() {
        let mut table = NameTable::default();
        for separator in ['\u{0085}', '\u{2028}', '\u{2029}'] {
            let record = format!(r#"{{"in":1,"str":{{"pre":0,"str":"a{separator}b"}}}}"#);
            expect_invalid(&mut table, &record, "U+0085, U+2028 or U+2029");
        }
        assert_eq!(table.explicit_count(), 0);
    }
}
