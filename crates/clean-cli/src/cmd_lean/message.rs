// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One Lean message and the two ways `lean` prints it: Lean's
//! `Message.toString` (the plain stream) and its `--json` line.
//!
//! Both renderings are pinned Lean's, measured on `bin/lean` of each modelled
//! release (2026-10-16):
//!
//! - plain: an information message is its text alone; a warning or an error is
//!   `<file>:<line>:<col>: warning: <text>` (with `-<line>:<col>` after the
//!   start position under `-DprintMessageEndPos=true`); a newline is appended
//!   unless the text already ends with one. Every message goes to stdout.
//! - `--json`, Lean 4.8.0: the object's keys in REVERSE alphabetical order
//!   (`severity`, `pos` with `line` before `column`, `keepFullRange`,
//!   `fileName`, `endPos`, `data`, `caption`).
//! - `--json`, Lean 4.30.0-rc2: keys in alphabetical order, plus `isSilent`
//!   and the message `kind` (`[anonymous]`, or `hasSorry` for the `sorry`
//!   warning).
//!
//! `-E <kind>` (Lean 4.30.0-rc2) prints a message of that kind as an error but
//! does not change the exit status, which pinned Lean computes from the
//! severity the message was logged with (measured: `lean -E hasSorry` on a
//! file whose only message is the `sorry` warning prints `error:` and exits 0).

use super::dialect::LeanDialect;

/// A source position as Lean reports it: 1-based line, 0-based column counted
/// in Unicode scalar values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Pos {
    pub(crate) line: u32,
    pub(crate) column: u32,
}

/// `Lean.MessageSeverity`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Severity {
    Information,
    Warning,
    Error,
}

impl Severity {
    fn json_name(self) -> &'static str {
        match self {
            Self::Information => "information",
            Self::Warning => "warning",
            Self::Error => "error",
        }
    }
}

/// The `kind` Lean 4.30.0-rc2 tags the `declaration uses sorry` warning with.
pub(crate) const KIND_HAS_SORRY: &str = "hasSorry";
/// The `kind` of every other message Clean logs.
pub(crate) const KIND_ANONYMOUS: &str = "[anonymous]";

/// One logged message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LeanMessage {
    pub(crate) severity: Severity,
    pub(crate) pos: Pos,
    pub(crate) end_pos: Option<Pos>,
    pub(crate) kind: &'static str,
    pub(crate) text: String,
}

/// How messages are printed for this run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RenderOptions {
    pub(crate) dialect: LeanDialect,
    /// The file name messages carry (the path as given, or `<stdin>`).
    pub(crate) file_name: String,
    /// `--json`.
    pub(crate) json: bool,
    /// `-DprintMessageEndPos=true`.
    pub(crate) end_pos: bool,
    /// `-E <kind>`: kinds printed as errors.
    pub(crate) error_kinds: Vec<String>,
}

impl LeanMessage {
    /// The severity the message is PRINTED with (`-E` promotes a kind).
    fn printed_severity(&self, options: &RenderOptions) -> Severity {
        if options.error_kinds.iter().any(|kind| kind == self.kind) {
            Severity::Error
        } else {
            self.severity
        }
    }

    /// The bytes `lean` prints for this message, newline included.
    pub(crate) fn render(&self, options: &RenderOptions) -> String {
        if options.json {
            let mut line = self.render_json(options);
            line.push('\n');
            line
        } else {
            self.render_plain(options)
        }
    }

    /// `Message.toString (includeEndPos := printMessageEndPos)`.
    fn render_plain(&self, options: &RenderOptions) -> String {
        let label = match self.printed_severity(options) {
            Severity::Information => None,
            Severity::Warning => Some("warning: "),
            Severity::Error => Some("error: "),
        };
        let mut out = match label {
            None => self.text.clone(),
            Some(label) => {
                let end = match (options.end_pos, self.end_pos) {
                    (true, Some(end)) => format!("-{}:{}", end.line, end.column),
                    _ => String::new(),
                };
                format!(
                    "{}:{}:{}{end}: {label}{}",
                    options.file_name, self.pos.line, self.pos.column, self.text
                )
            }
        };
        if !out.ends_with('\n') {
            out.push('\n');
        }
        out
    }

    /// The `--json` object, one line, no trailing newline.
    fn render_json(&self, options: &RenderOptions) -> String {
        let severity = self.printed_severity(options).json_name();
        let file = json_string(&options.file_name);
        let data = json_string(&self.text);
        match options.dialect {
            LeanDialect::V4_8_0 => {
                let end = self
                    .end_pos
                    .map(|end| {
                        format!(
                            "\"endPos\":{{\"line\":{},\"column\":{}}},",
                            end.line, end.column
                        )
                    })
                    .unwrap_or_default();
                format!(
                    "{{\"severity\":\"{severity}\",\"pos\":{{\"line\":{},\"column\":{}}},\
                     \"keepFullRange\":false,\"fileName\":{file},{end}\"data\":{data},\
                     \"caption\":\"\"}}",
                    self.pos.line, self.pos.column
                )
            }
            LeanDialect::V4_30_0Rc2 | LeanDialect::V4_36_0 => {
                let end = self
                    .end_pos
                    .map(|end| {
                        format!(
                            "\"endPos\":{{\"column\":{},\"line\":{}}},",
                            end.column, end.line
                        )
                    })
                    .unwrap_or_default();
                format!(
                    "{{\"caption\":\"\",\"data\":{data},{end}\"fileName\":{file},\
                     \"isSilent\":false,\"keepFullRange\":false,\"kind\":{},\
                     \"pos\":{{\"column\":{},\"line\":{}}},\"severity\":\"{severity}\"}}",
                    json_string(self.kind),
                    self.pos.column,
                    self.pos.line
                )
            }
        }
    }
}

/// A JSON string literal as Lean's `Json.escape` writes it: `"` `\` newline
/// and carriage return get two-character escapes, every other character below
/// U+0020 a lowercase `\u00xx`, and everything else (non-ASCII included) is
/// written as itself.
pub(crate) fn json_string(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            c if u32::from(c) < 0x20 => out.push_str(&format!("\\u{:04x}", u32::from(c))),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn options(dialect: LeanDialect, json: bool) -> RenderOptions {
        RenderOptions {
            dialect,
            file_name: "a.lean".to_owned(),
            json,
            end_pos: false,
            error_kinds: Vec::new(),
        }
    }

    fn warning() -> LeanMessage {
        LeanMessage {
            severity: Severity::Warning,
            pos: Pos { line: 6, column: 8 },
            end_pos: Some(Pos { line: 6, column: 9 }),
            kind: KIND_HAS_SORRY,
            text: "declaration uses 'sorry'".to_owned(),
        }
    }

    #[test]
    fn test_plain_warning_and_info_match_pinned_lean() {
        let opts = options(LeanDialect::V4_8_0, false);
        assert_eq!(
            warning().render(&opts),
            "a.lean:6:8: warning: declaration uses 'sorry'\n"
        );
        let info = LeanMessage {
            severity: Severity::Information,
            pos: Pos { line: 2, column: 0 },
            end_pos: Some(Pos { line: 2, column: 5 }),
            kind: KIND_ANONYMOUS,
            text: "2\n".to_owned(),
        };
        assert_eq!(info.render(&opts), "2\n");
        let mut end = opts.clone();
        end.end_pos = true;
        assert_eq!(
            warning().render(&end),
            "a.lean:6:8-6:9: warning: declaration uses 'sorry'\n"
        );
    }

    #[test]
    fn test_json_key_order_per_dialect_matches_pinned_lean() {
        // Bytes measured on pinned `lean --json` of each release.
        assert_eq!(
            warning().render(&options(LeanDialect::V4_8_0, true)),
            "{\"severity\":\"warning\",\"pos\":{\"line\":6,\"column\":8},\
             \"keepFullRange\":false,\"fileName\":\"a.lean\",\"endPos\":{\"line\":6,\
             \"column\":9},\"data\":\"declaration uses 'sorry'\",\"caption\":\"\"}\n"
        );
        let mut modern = warning();
        modern.text = "declaration uses `sorry`".to_owned();
        assert_eq!(
            modern.render(&options(LeanDialect::V4_30_0Rc2, true)),
            "{\"caption\":\"\",\"data\":\"declaration uses `sorry`\",\"endPos\":{\"column\":9,\
             \"line\":6},\"fileName\":\"a.lean\",\"isSilent\":false,\"keepFullRange\":false,\
             \"kind\":\"hasSorry\",\"pos\":{\"column\":8,\"line\":6},\"severity\":\"warning\"}\n"
        );
    }

    #[test]
    fn test_error_kind_promotes_printed_severity_only() {
        let mut opts = options(LeanDialect::V4_30_0Rc2, false);
        opts.error_kinds.push(KIND_HAS_SORRY.to_owned());
        assert_eq!(
            warning().render(&opts),
            "a.lean:6:8: error: declaration uses 'sorry'\n"
        );
        assert_eq!(warning().severity, Severity::Warning);
    }

    #[test]
    fn test_json_string_escapes_like_lean() {
        assert_eq!(
            json_string("a\"b\\c\nd\re\tf"),
            "\"a\\\"b\\\\c\\nd\\re\\u0009f\""
        );
        assert_eq!(json_string("❌ α\u{7f}"), "\"❌ α\u{7f}\"");
    }
}
