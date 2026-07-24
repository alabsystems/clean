// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Document state management
//!
//! Manages open documents and their state, including text content,
//! parsed AST, and elaboration results.

use ropey::Rope;
use std::collections::HashMap;
use tower_lsp::lsp_types::{Position, Range, Url};

/// A document being edited
#[derive(Debug, Clone)]
pub struct Document {
    /// Document URI
    pub uri: Url,
    /// Document version (increments on each edit)
    pub version: i32,
    /// Document text content (as rope for efficient edits)
    pub content: Rope,
    /// Language ID (should be "lean" or "lean4")
    pub language_id: String,
    /// Parsed AST (if available)
    pub parsed: Option<ParsedDocument>,
    /// Elaboration result (if available)
    pub elaborated: Option<ElaboratedDocument>,
    /// Incremental elaboration state (cached results)
    pub incremental_state: IncrementalState,
}

impl Document {
    /// Create a new document
    #[must_use]
    pub fn new(uri: Url, version: i32, content: String, language_id: String) -> Self {
        Self {
            uri,
            version,
            content: Rope::from_str(&content),
            language_id,
            parsed: None,
            elaborated: None,
            incremental_state: IncrementalState::default(),
        }
    }

    /// Get the full text content
    #[must_use]
    pub fn text(&self) -> String {
        self.content.to_string()
    }

    /// Get a line of text (0-indexed)
    #[must_use]
    pub fn line(&self, line_idx: usize) -> Option<String> {
        if line_idx < self.content.len_lines() {
            Some(self.content.line(line_idx).to_string())
        } else {
            None
        }
    }

    /// Get line count
    #[must_use]
    pub fn line_count(&self) -> usize {
        self.content.len_lines()
    }

    /// Apply a text change
    pub fn apply_change(&mut self, range: Option<Range>, text: &str) {
        match range {
            Some(range) => {
                // `position_to_offset` returns a *byte* offset, but ropey's
                // `Rope::remove`/`Rope::insert` index by *char*. Feeding a byte
                // offset straight in overshoots whenever the document contains
                // a multi-byte UTF-8 char and panics (`Char range out of
                // bounds`) on out-of-range client input — so convert to char
                // indices here. `byte_to_char` accepts one-past-the-end and
                // rounds a mid-char byte to its owning char; clamp to
                // `len_bytes()` and enforce `start <= end` so untrusted
                // `change.range` from `didChange` can never trigger a panic.
                let len_bytes = self.content.len_bytes();
                let start_byte = self.position_to_offset(range.start).min(len_bytes);
                let end_byte = self.position_to_offset(range.end).min(len_bytes);
                let start = self.content.byte_to_char(start_byte);
                let end = self.content.byte_to_char(end_byte).max(start);

                // Remove old text
                self.content.remove(start..end);
                // Insert new text
                self.content.insert(start, text);
            }
            None => {
                // Full document replacement - clear incremental state
                self.content = Rope::from_str(text);
                self.incremental_state = IncrementalState::default();
            }
        }

        // Invalidate parsed/elaborated results (but keep incremental state for partial edits)
        // The incremental state will be used to determine which commands need re-elaboration
        self.parsed = None;
        self.elaborated = None;
    }

    /// Convert LSP position to byte offset
    #[must_use]
    pub fn position_to_offset(&self, pos: Position) -> usize {
        let line_idx = pos.line as usize;
        if line_idx >= self.content.len_lines() {
            return self.content.len_bytes();
        }

        let line_start = self.content.line_to_byte(line_idx);
        let line = self.content.line(line_idx);

        // LSP positions are in UTF-16 code units, rope uses bytes
        let mut char_offset = 0;
        let mut utf16_offset = 0u32;

        for ch in line.chars() {
            if utf16_offset >= pos.character {
                break;
            }
            char_offset += ch.len_utf8();
            utf16_offset += ch.len_utf16() as u32;
        }

        line_start + char_offset
    }

    /// Convert byte offset to LSP position
    #[must_use]
    pub fn offset_to_position(&self, offset: usize) -> Position {
        let line = self
            .content
            .byte_to_line(offset.min(self.content.len_bytes()));
        let line_start = self.content.line_to_byte(line);
        let col_bytes = offset.saturating_sub(line_start);

        // Convert byte offset within line to UTF-16 code units
        let line_text = self.content.line(line);
        let mut utf16_col = 0u32;
        let mut byte_count = 0;

        for ch in line_text.chars() {
            if byte_count >= col_bytes {
                break;
            }
            byte_count += ch.len_utf8();
            utf16_col += ch.len_utf16() as u32;
        }

        Position {
            line: line as u32,
            character: utf16_col,
        }
    }
}

/// Parsed document (AST)
#[derive(Debug, Clone)]
pub struct ParsedDocument {
    /// Parse errors
    pub errors: Vec<ParseError>,
    /// Parsed commands/declarations
    pub commands: Vec<ParsedCommand>,
}

/// A parse error
#[derive(Debug, Clone)]
pub struct ParseError {
    /// Byte offset start
    pub start: usize,
    /// Byte offset end
    pub end: usize,
    /// Error message
    pub message: String,
    /// Related source locations (advisory). Empty when the model has no
    /// genuine secondary location to point at; never fabricated.
    pub related: Vec<RelatedLocation>,
}

/// A parsed command/declaration
#[derive(Debug, Clone)]
pub struct ParsedCommand {
    /// Command kind
    pub kind: CommandKind,
    /// Byte offset start
    pub start: usize,
    /// Byte offset end
    pub end: usize,
    /// Name (if named declaration)
    pub name: Option<String>,
    /// Hash of the source text for this command (for incremental checking)
    pub content_hash: u64,
}

/// Kind of top-level command
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommandKind {
    Definition,
    Theorem,
    Lemma,
    Example,
    Inductive,
    Coinductive, // Lean 4.25+ (#191)
    Structure,
    Class,
    Instance,
    Axiom,
    Variable,
    Universe,
    Import,
    Open,
    Namespace,
    Section,
    End,
    Other(String),
}

/// Elaborated document (type-checked)
#[derive(Debug, Clone)]
pub struct ElaboratedDocument {
    /// Type errors
    pub errors: Vec<TypeError>,
    /// Warnings (unused variables, deprecated features, etc.)
    pub warnings: Vec<Warning>,
    /// Declarations with types
    pub declarations: Vec<ElaboratedDecl>,
    /// Hole-local expected-type contexts recorded during elaboration.
    ///
    /// Each entry carries the source range of a hole (`_` or `sorry`) together
    /// with the expected type the elaborator demands at that hole. Consumed by
    /// `$/lean/plainTermGoal` to answer with the hole-local goal rather than the
    /// whole declaration's type.
    pub holes: Vec<HoleContext>,
    /// User-defined widget modules discovered during elaboration.
    ///
    /// Each entry records a declaration carrying the `@[widget_module]`
    /// attribute (the Lean 4 marker for an infoview panel widget). Consumed by
    /// the `Lean.Widget.getWidgets` RPC endpoint, which appends a panel widget
    /// instance for each recorded module alongside the built-in declaration
    /// panels.
    pub widget_modules: Vec<WidgetModule>,
}

/// A user-defined widget module discovered during elaboration.
///
/// Recorded for any declaration decorated with `@[widget_module]`, the Lean 4
/// attribute that registers a definition as an infoview panel widget. The
/// `name` doubles as the widget id reported to the client; the source `range`
/// lets the infoview place the widget panel at the declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WidgetModule {
    /// Declaration name (also used as the widget id).
    pub name: String,
    /// Byte offset start of the declaration.
    pub start: usize,
    /// Byte offset end of the declaration.
    pub end: usize,
}

/// A hole (`_`/`sorry`) and the type expected at its source position.
///
/// Populated from the elaborator for every user-written `_` hole (body-level
/// and nested / sub-term, e.g. `(_ : Nat) + 1`), carrying the precise type the
/// elaborator demanded at that hole. A body-level `sorry` is also recorded,
/// with the declaration's own elaborated type. The hole `range` is narrower
/// than the enclosing declaration range, so `plainTermGoal` can prefer the
/// hole-local goal when the cursor sits on the hole itself.
#[derive(Debug, Clone, Default)]
pub struct HoleContext {
    /// Byte offset start of the hole token.
    pub start: usize,
    /// Byte offset end of the hole token.
    pub end: usize,
    /// Expected type at the hole (pretty-printed).
    pub expected_type: String,
    /// Local hypotheses in scope at the hole, as pretty-printed
    /// `(name, type)` pairs in binder order.
    ///
    /// Mirrors the Lean infoview's local context shown above the goal
    /// turnstile. Each entry is rendered with the same pretty-printer used for
    /// `expected_type`. Empty when no binders are in scope at the hole (e.g. a
    /// top-level body hole), in which case `plainTermGoal` reports only the
    /// expected type.
    pub local_bindings: Vec<(String, String)>,
}

/// Cache entry for a single elaborated command
#[derive(Debug, Clone)]
pub struct ElaboratedCommandCache {
    /// Content hash of the source command (for cache invalidation)
    pub content_hash: u64,
    /// Type errors for this command
    pub errors: Vec<TypeError>,
    /// Warnings for this command
    pub warnings: Vec<Warning>,
    /// Elaborated declaration info (if applicable)
    pub declaration: Option<ElaboratedDecl>,
}

/// Incremental elaboration state
#[derive(Debug, Clone, Default)]
pub struct IncrementalState {
    /// Cached elaboration results keyed by command name or index
    /// Key is (name, content_hash) for named decls, or ("__anon_{idx}", content_hash) for anonymous
    pub cache: HashMap<String, ElaboratedCommandCache>,
    /// Statistics for debugging
    pub stats: IncrementalStats,
}

/// Statistics about incremental checking
#[derive(Debug, Clone, Default)]
pub struct IncrementalStats {
    /// Number of commands in the document
    pub total_commands: usize,
    /// Number of commands that were re-elaborated
    pub elaborated_count: usize,
    /// Number of commands that used cached results
    pub cached_count: usize,
}

/// A related source location for a diagnostic.
///
/// Mirrors the Lean 4 LSP `DiagnosticRelatedInformation` payload: a span in the
/// *same* document together with an explanatory message. The byte offsets are
/// resolved against the owning [`Document`] (so the related location's `uri` is
/// the document's own `uri`) when the diagnostic is built. This is advisory IDE
/// metadata only — it carries no semantic or proof weight, and is populated
/// exclusively from genuine locations the document model already tracks (never
/// fabricated).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct RelatedLocation {
    /// Byte offset start of the related span (within the owning document).
    pub start: usize,
    /// Byte offset end of the related span (within the owning document).
    pub end: usize,
    /// Human-readable description of the related location.
    pub message: String,
}

/// A warning (not a fatal error)
#[derive(Debug, Clone)]
pub struct Warning {
    /// Byte offset start
    pub start: usize,
    /// Byte offset end
    pub end: usize,
    /// Warning message
    pub message: String,
    /// Warning code (for categorization)
    pub code: WarningCode,
    /// Related source locations (advisory). Empty when the model has no
    /// genuine secondary location to point at; never fabricated.
    pub related: Vec<RelatedLocation>,
}

/// Categories of warnings
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WarningCode {
    /// Variable declared but not used
    UnusedVariable,
    /// Import not needed
    UnusedImport,
    /// Using deprecated feature
    DeprecatedFeature,
    /// Code will never be reached
    UnreachableCode,
    /// Incomplete proof (sorry or admit)
    IncompleteProof,
    /// Other warning
    Other,
}

/// A type error
#[derive(Debug, Clone)]
pub struct TypeError {
    /// Byte offset start
    pub start: usize,
    /// Byte offset end
    pub end: usize,
    /// Error message
    pub message: String,
    /// Related source locations (advisory). Empty when the model has no
    /// genuine secondary location to point at; never fabricated.
    pub related: Vec<RelatedLocation>,
}

/// An elaborated declaration
#[derive(Debug, Clone)]
pub struct ElaboratedDecl {
    /// Declaration name
    pub name: String,
    /// Declaration type (pretty-printed)
    pub type_str: String,
    /// Byte offset start
    pub start: usize,
    /// Byte offset end
    pub end: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_document_creation() {
        let uri = Url::parse("file:///test.lean").unwrap();
        let doc = Document::new(
            uri.clone(),
            1,
            "def x := 1\n".to_string(),
            "lean".to_string(),
        );

        assert_eq!(doc.version, 1);
        assert_eq!(doc.text(), "def x := 1\n");
        assert_eq!(doc.line_count(), 2); // includes trailing newline
    }

    #[test]
    fn test_document_line_access() {
        let uri = Url::parse("file:///test.lean").unwrap();
        let doc = Document::new(
            uri,
            1,
            "line1\nline2\nline3".to_string(),
            "lean".to_string(),
        );

        assert_eq!(doc.line(0), Some("line1\n".to_string()));
        assert_eq!(doc.line(1), Some("line2\n".to_string()));
        assert_eq!(doc.line(2), Some("line3".to_string()));
        assert_eq!(doc.line(3), None);
    }

    #[test]
    fn test_document_full_replace() {
        let uri = Url::parse("file:///test.lean").unwrap();
        let mut doc = Document::new(uri, 1, "old content".to_string(), "lean".to_string());

        doc.apply_change(None, "new content");

        assert_eq!(doc.text(), "new content");
    }

    #[test]
    fn test_document_partial_change() {
        let uri = Url::parse("file:///test.lean").unwrap();
        let mut doc = Document::new(uri, 1, "hello world".to_string(), "lean".to_string());

        // Replace "world" with "rust"
        let range = Range {
            start: Position {
                line: 0,
                character: 6,
            },
            end: Position {
                line: 0,
                character: 11,
            },
        };
        doc.apply_change(Some(range), "rust");

        assert_eq!(doc.text(), "hello rust");
    }

    #[test]
    fn test_apply_change_delete_multibyte_char_no_panic() {
        // Regression: apply_change fed byte offsets from position_to_offset
        // straight into ropey's char-indexed Rope::remove/insert. For content
        // with a multi-byte UTF-8 char, deleting it produced end byte offset 2
        // while len_chars()==1, so remove(0..2) panicked with
        // "Char range out of bounds". This must now delete cleanly.
        let uri = Url::parse("file:///test.lean").unwrap();
        // "é" is 1 char but 2 UTF-8 bytes; 1 UTF-16 code unit.
        let mut doc = Document::new(uri, 1, "é".to_string(), "lean".to_string());

        // Delete the single character: range {0,0}..{0,1}, text "".
        let range = Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 1,
            },
        };
        doc.apply_change(Some(range), "");

        assert_eq!(doc.text(), "", "multi-byte char should be deleted");
    }

    #[test]
    fn test_apply_change_insert_after_multibyte_char_no_panic() {
        // Regression for the insert side of the byte-vs-char defect (line 92).
        // Typing a char right after a multi-byte char: content "é" (1 char, 2
        // UTF-8 bytes, 1 UTF-16 unit) with a zero-width range {0,1}..{0,1} and
        // text "x". `position_to_offset({0,1})` returns byte offset 2, but
        // len_chars()==1, so the pre-fix `Rope::insert(2, "x")` unwrapped an
        // `Err(CharIndexOutOfBounds)` and panicked. The byte->char conversion
        // maps byte 2 to char 1, so the insert lands cleanly at the end.
        let uri = Url::parse("file:///test.lean").unwrap();
        let mut doc = Document::new(uri, 1, "é".to_string(), "lean".to_string());

        let range = Range {
            start: Position {
                line: 0,
                character: 1,
            },
            end: Position {
                line: 0,
                character: 1,
            },
        };
        // Must not panic (pre-fix: "Char index out of bounds: char index 2 ...").
        doc.apply_change(Some(range), "x");

        assert_eq!(doc.text(), "éx", "insert after multi-byte char appends 'x'");
    }

    #[test]
    fn test_apply_change_multibyte_edits_and_out_of_range_no_panic() {
        let uri = Url::parse("file:///test.lean").unwrap();
        // "aéb": a=byte 0, é=bytes 1..=2, b=byte 3. UTF-16: a=0, é=1, b=2.
        let mut doc = Document::new(uri, 1, "aéb".to_string(), "lean".to_string());

        // Replace the middle multi-byte char (UTF-16 range 1..2) with "X".
        let range = Range {
            start: Position {
                line: 0,
                character: 1,
            },
            end: Position {
                line: 0,
                character: 2,
            },
        };
        doc.apply_change(Some(range), "X");
        assert_eq!(doc.text(), "aXb", "replace multi-byte char in the middle");

        // Out-of-range end (past the line) plus a multi-byte tail must clamp,
        // not panic. Rebuild with a trailing multi-byte char.
        let uri2 = Url::parse("file:///test2.lean").unwrap();
        let mut doc2 = Document::new(uri2, 1, "xé".to_string(), "lean".to_string());
        let over = Range {
            start: Position {
                line: 0,
                character: 1,
            },
            end: Position {
                line: 0,
                character: 999,
            },
        };
        doc2.apply_change(Some(over), "");
        assert_eq!(doc2.text(), "x", "out-of-range end clamps and deletes tail");
    }

    #[test]
    fn test_position_offset_conversion() {
        let uri = Url::parse("file:///test.lean").unwrap();
        let doc = Document::new(
            uri,
            1,
            "line1\nline2\nline3".to_string(),
            "lean".to_string(),
        );

        // Start of file
        let pos = doc.offset_to_position(0);
        assert_eq!(pos.line, 0);
        assert_eq!(pos.character, 0);

        // Start of line 2
        let pos = doc.offset_to_position(6);
        assert_eq!(pos.line, 1);
        assert_eq!(pos.character, 0);

        // Middle of line 2
        let pos = doc.offset_to_position(9);
        assert_eq!(pos.line, 1);
        assert_eq!(pos.character, 3);
    }

    #[test]
    fn test_utf16_position_handling() {
        let uri = Url::parse("file:///test.lean").unwrap();
        // Emoji takes 4 bytes in UTF-8 but 2 code units in UTF-16
        let doc = Document::new(uri, 1, "a\u{1F600}b".to_string(), "lean".to_string());

        // 'a' is at position 0
        // emoji is at byte 1, but UTF-16 position 1-2
        // 'b' is at byte 5, but UTF-16 position 3
        let pos = doc.offset_to_position(5);
        assert_eq!(pos.character, 3); // 1 (a) + 2 (emoji surrogate pair)
    }

    #[test]
    fn test_position_to_offset_utf16_surrogate_pair() {
        let uri = Url::parse("file:///test.lean").unwrap();
        // "a😀b": bytes a=0, 😀=1..=4, b=5 (len 6); UTF-16 a=0, 😀=1,2, b=3.
        let doc = Document::new(uri, 1, "a\u{1F600}b".to_string(), "lean".to_string());

        let off = |c: u32| {
            doc.position_to_offset(Position {
                line: 0,
                character: c,
            })
        };
        assert_eq!(off(0), 0, "char 0 -> 'a' at byte 0");
        assert_eq!(off(1), 1, "char 1 -> emoji start at byte 1");
        // char 2 points into the middle of the surrogate pair (not a char
        // boundary); the scan rounds up to the next boundary, 'b' at byte 5.
        assert_eq!(
            off(2),
            5,
            "char 2 (mid-surrogate) rounds up to 'b' at byte 5"
        );
        assert_eq!(off(3), 5, "char 3 -> 'b' at byte 5");
        // A character past the line's last unit clamps to the line end.
        assert_eq!(off(4), 6, "char 4 (past end) clamps to byte 6");
    }

    #[test]
    fn test_position_to_offset_bmp_multibyte() {
        let uri = Url::parse("file:///test.lean").unwrap();
        // "x€y": € is 3 UTF-8 bytes but a single UTF-16 unit.
        // bytes x=0, €=1..=3, y=4 (len 5); UTF-16 x=0, €=1, y=2.
        let doc = Document::new(uri, 1, "x\u{20AC}y".to_string(), "lean".to_string());

        let off = |c: u32| {
            doc.position_to_offset(Position {
                line: 0,
                character: c,
            })
        };
        assert_eq!(off(0), 0);
        assert_eq!(off(1), 1, "char 1 -> '€' start at byte 1");
        assert_eq!(off(2), 4, "char 2 -> 'y' at byte 4");
    }

    #[test]
    fn test_position_offset_roundtrip_unicode() {
        let uri = Url::parse("file:///test.lean").unwrap();
        let doc = Document::new(uri, 1, "a\u{1F600}b".to_string(), "lean".to_string());

        // offset_to_position(position_to_offset(p)) is the identity on positions
        // that land on a character boundary (0, 1, 3 — not the mid-surrogate 2).
        for character in [0u32, 1, 3] {
            let pos = Position { line: 0, character };
            let back = doc.offset_to_position(doc.position_to_offset(pos));
            assert_eq!(back, pos, "round-trip failed for character {character}");
        }
    }

    #[test]
    fn test_position_to_offset_line_past_end_clamps() {
        let uri = Url::parse("file:///test.lean").unwrap();
        let doc = Document::new(uri, 1, "a\u{1F600}b".to_string(), "lean".to_string());

        // A line index beyond the document clamps to the total byte length,
        // never an out-of-range offset.
        let pos = doc.position_to_offset(Position {
            line: 5,
            character: 0,
        });
        assert_eq!(
            pos,
            "a\u{1F600}b".len(),
            "out-of-range line clamps to len_bytes"
        );
    }

    #[test]
    fn test_apply_change_reversed_range_no_panic() {
        // A malicious or buggy editor can send a `didChange` whose range has
        // `start` after `end`. The LSP layer does not normalize this, so it
        // reaches `apply_change` directly. Previously `position_to_offset`
        // produced start=5, end=0 and `Rope::remove(5..0)` panicked with
        // "Invalid char range 5..0: start must be <= end". The fix normalizes
        // the offsets so a reversed range is treated as an empty span.
        let uri = Url::parse("file:///test.lean").unwrap();
        let mut doc = Document::new(uri, 1, "hello world".to_string(), "lean".to_string());

        // Reversed range: start (char 5) after end (char 0).
        let range = Range {
            start: Position {
                line: 0,
                character: 5,
            },
            end: Position {
                line: 0,
                character: 0,
            },
        };
        // Must not panic.
        doc.apply_change(Some(range), "");

        // Content is left unchanged (empty span, empty inserted text).
        assert_eq!(doc.text(), "hello world");
    }

    #[test]
    fn test_apply_change_reversed_range_with_insert() {
        // Reversed range carrying replacement text. The fix normalizes the end
        // up to `start` (an empty span), so nothing is removed and the text is
        // inserted at the `start` position — no panic. This is a defensive
        // normalization of malformed client input, not a correct-path edit.
        let uri = Url::parse("file:///test.lean").unwrap();
        let mut doc = Document::new(uri, 1, "hello world".to_string(), "lean".to_string());

        let range = Range {
            start: Position {
                line: 0,
                character: 5,
            },
            end: Position {
                line: 0,
                character: 0,
            },
        };
        doc.apply_change(Some(range), "X");

        // Empty span at start char 5 ("hello|X world"); nothing removed.
        assert_eq!(doc.text(), "helloX world");
    }

    #[test]
    fn test_apply_change_multibyte_no_panic() {
        // Regression for the byte/char mismatch: `position_to_offset` returns a
        // *byte* offset while ropey indexes by *char*. With a multi-byte char
        // in the document, a naive `remove(byte_start..byte_end)` overshoots
        // and panics. The fix converts byte -> char first.
        let uri = Url::parse("file:///test.lean").unwrap();
        // "a€bc": € is 3 UTF-8 bytes, 1 char, 1 UTF-16 unit.
        let mut doc = Document::new(uri, 1, "a\u{20AC}bc".to_string(), "lean".to_string());

        // Replace "bc" (UTF-16 chars 2..4) with "Z". Must not panic and must
        // land on the correct chars despite the byte/char skew.
        let range = Range {
            start: Position {
                line: 0,
                character: 2,
            },
            end: Position {
                line: 0,
                character: 4,
            },
        };
        doc.apply_change(Some(range), "Z");

        assert_eq!(doc.text(), "a\u{20AC}Z");
    }

    #[test]
    fn test_command_kind_eq() {
        assert_eq!(CommandKind::Definition, CommandKind::Definition);
        assert_ne!(CommandKind::Definition, CommandKind::Theorem);
        assert_eq!(
            CommandKind::Other("foo".to_string()),
            CommandKind::Other("foo".to_string())
        );
    }
}
