// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The declaration record envelopes of the K3 export.

use super::{invalid, K3ExportSyntaxError};
use crate::ndjson::json::JsonValue;

/// A declaration record kind in the lean4export 3.1.0 wire format.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum K3DeclarationKind {
    /// A definition.
    Def,
    /// A theorem.
    Thm,
    /// An opaque declaration.
    Opaque,
    /// An axiom.
    Axiom,
    /// A quotient primitive declaration.
    Quot,
    /// An inductive block, including its constructors and recursors.
    Inductive,
}

impl K3DeclarationKind {
    /// The kind's spelling in the export and transcript.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Def => "def",
            Self::Thm => "thm",
            Self::Opaque => "opaque",
            Self::Axiom => "axiom",
            Self::Quot => "quot",
            Self::Inductive => "inductive",
        }
    }
}

/// The line and kind of one declaration record identified by its envelope.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct K3DeclarationIndexRow {
    /// The one-based line number in the export.
    pub line: usize,
    /// The record's single top-level declaration kind.
    pub kind: K3DeclarationKind,
}

pub(super) fn declaration_envelope(
    line: usize,
    entries: Vec<(String, JsonValue)>,
) -> Result<(K3DeclarationIndexRow, JsonValue), K3ExportSyntaxError> {
    let Ok([(key, body)]) = <[_; 1]>::try_from(entries) else {
        return Err(invalid(
            line,
            "a declaration record must have exactly one top-level key",
        ));
    };
    let kind = match key.as_str() {
        "def" => K3DeclarationKind::Def,
        "thm" => K3DeclarationKind::Thm,
        "opaque" => K3DeclarationKind::Opaque,
        "axiom" => K3DeclarationKind::Axiom,
        "quot" => K3DeclarationKind::Quot,
        "inductive" => K3DeclarationKind::Inductive,
        other => return Err(invalid(line, format!("unknown declaration kind {other:?}"))),
    };
    Ok((K3DeclarationIndexRow { line, kind }, body))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn indexes_all_six_declaration_envelopes() {
        for (offset, (key, kind)) in [
            ("def", K3DeclarationKind::Def),
            ("thm", K3DeclarationKind::Thm),
            ("opaque", K3DeclarationKind::Opaque),
            ("axiom", K3DeclarationKind::Axiom),
            ("quot", K3DeclarationKind::Quot),
            ("inductive", K3DeclarationKind::Inductive),
        ]
        .into_iter()
        .enumerate()
        {
            let line = offset + 17;
            let (row, body) =
                declaration_envelope(line, vec![(key.to_owned(), JsonValue::Null)]).unwrap();
            assert_eq!(body, JsonValue::Null);
            assert_eq!(row, K3DeclarationIndexRow { line, kind });
            assert_eq!(row.kind.as_str(), key);
        }
    }

    #[test]
    fn refuses_unknown_or_nonsingleton_envelopes() {
        for (keys, expected) in [
            (&[][..], "exactly one top-level key"),
            (&["def", "thm"][..], "exactly one top-level key"),
            (&["def", "extra"][..], "exactly one top-level key"),
            (&["Def"][..], "unknown declaration kind"),
            (&["structure"][..], "unknown declaration kind"),
        ] {
            let entries = keys
                .iter()
                .map(|&key| (key.to_owned(), JsonValue::Null))
                .collect();
            let Err(K3ExportSyntaxError::Invalid { line, reason }) =
                declaration_envelope(25, entries)
            else {
                panic!("expected a K3 refusal for {keys:?}");
            };
            assert_eq!(line, 25);
            assert!(reason.contains(expected), "{keys:?}: {reason}");
        }
    }
}
