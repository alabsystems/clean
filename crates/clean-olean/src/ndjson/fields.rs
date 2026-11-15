// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed field access over one record object, refusing every field the format
//! does not define for that record.
//!
//! Lean's reader looks a record's fields up by name and ignores the rest. This
//! one consumes them by name and refuses a record that still has a field left
//! (`UnknownField`): an exporter that writes a field this reader does not
//! model is a format this reader does not know.
//!
//! A natural-number field must be spelled as JSON writes a natural
//! (`0|[1-9][0-9]*`). Lean's reader also takes `1e2` for 100 and `-0` for 0;
//! no exporter writes them, and this reader refuses them by name.

use super::error::NdjsonError;
use super::json::JsonValue;

/// The fields of one record object.
pub(crate) struct Fields {
    line: u64,
    record: &'static str,
    entries: Vec<(String, JsonValue)>,
}

impl Fields {
    /// The fields of `value`, which must be an object.
    pub(crate) fn new(
        line: u64,
        record: &'static str,
        value: JsonValue,
    ) -> Result<Self, NdjsonError> {
        match value {
            JsonValue::Object(entries) => Ok(Self {
                line,
                record,
                entries,
            }),
            other => Err(NdjsonError::Field {
                line,
                record,
                field: String::new(),
                problem: format!("expected an object, found {}", other.type_name()),
            }),
        }
    }

    /// A refusal naming `field` of this record.
    pub(crate) fn error(&self, field: &str, problem: impl Into<String>) -> NdjsonError {
        NdjsonError::Field {
            line: self.line,
            record: self.record,
            field: field.to_owned(),
            problem: problem.into(),
        }
    }

    /// Remove `field`, if present.
    pub(crate) fn take_opt(&mut self, field: &str) -> Option<JsonValue> {
        let at = self.entries.iter().position(|(k, _)| k == field)?;
        Some(self.entries.swap_remove(at).1)
    }

    /// Remove `field`, refusing the record when it is absent.
    pub(crate) fn take(&mut self, field: &str) -> Result<JsonValue, NdjsonError> {
        self.take_opt(field)
            .ok_or_else(|| self.error(field, "missing"))
    }

    /// Refuse the record if a field nobody took is left.
    pub(crate) fn finish(self) -> Result<(), NdjsonError> {
        match self.entries.into_iter().next() {
            None => Ok(()),
            Some((field, _)) => Err(NdjsonError::UnknownField {
                line: self.line,
                record: self.record,
                field,
            }),
        }
    }

    pub(crate) fn nat(&mut self, field: &str) -> Result<u64, NdjsonError> {
        let value = self.take(field)?;
        nat_value(self.line, self.record, field, &value)
    }

    /// A natural Clean holds in `u32` (counts, indices): a larger one is a
    /// limit of Clean's representation, declined, not a malformed export.
    pub(crate) fn nat_u32(&mut self, field: &str) -> Result<u32, NdjsonError> {
        let n = self.nat(field)?;
        u32::try_from(n).map_err(|_| NdjsonError::RepresentationLimit {
            line: self.line,
            record: self.record,
            field: field.to_owned(),
            problem: format!("{n} is above {}", u32::MAX),
        })
    }

    pub(crate) fn boolean(&mut self, field: &str) -> Result<bool, NdjsonError> {
        match self.take(field)? {
            JsonValue::Bool(b) => Ok(b),
            other => Err(self.error(
                field,
                format!("expected a boolean, found {}", other.type_name()),
            )),
        }
    }

    pub(crate) fn string(&mut self, field: &str) -> Result<String, NdjsonError> {
        match self.take(field)? {
            JsonValue::String(s) => Ok(s),
            other => Err(self.error(
                field,
                format!("expected a string, found {}", other.type_name()),
            )),
        }
    }

    pub(crate) fn array(&mut self, field: &str) -> Result<Vec<JsonValue>, NdjsonError> {
        match self.take(field)? {
            JsonValue::Array(items) => Ok(items),
            other => Err(self.error(
                field,
                format!("expected an array, found {}", other.type_name()),
            )),
        }
    }

    pub(crate) fn nat_array(&mut self, field: &str) -> Result<Vec<u64>, NdjsonError> {
        let items = self.array(field)?;
        items
            .iter()
            .map(|item| nat_value(self.line, self.record, field, item))
            .collect()
    }
}

/// `value` as a natural that fits in `u64`, spelled canonically. A canonical
/// natural above `u64` is a limit of Clean's representation (declined); any
/// other spelling is malformed (rejected).
pub(crate) fn nat_value(
    line: u64,
    record: &'static str,
    field: &str,
    value: &JsonValue,
) -> Result<u64, NdjsonError> {
    let problem = match value {
        JsonValue::Number(n) => match n.as_u64() {
            Some(v) => return Ok(v),
            None if n.canonical_natural => {
                return Err(NdjsonError::RepresentationLimit {
                    line,
                    record,
                    field: field.to_owned(),
                    problem: format!("{} is above {}", n.text, u64::MAX),
                })
            }
            None => format!("{} is not a natural number spelled `0|[1-9][0-9]*`", n.text),
        },
        other => format!("expected a natural number, found {}", other.type_name()),
    };
    Err(NdjsonError::Field {
        line,
        record,
        field: field.to_owned(),
        problem,
    })
}
