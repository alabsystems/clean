// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hardcoded names in the pinned C++ inventory's masked and original source.

use std::{collections::BTreeMap, ops::Range, sync::LazyLock};

use regex::{Captures, Regex};
use serde::Serialize;

use super::functions::line_of;
use super::headers::{SPACE, WORD};
use super::{python_word, CppSource};

static GLOBAL_INIT: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(&format!(
        r"\A(?:[{WORD}]+[{SPACE}]*::[{SPACE}]*)?(g_[{WORD}]+)[{SPACE}]*=[{SPACE}]*new(?:_persistent_expr_const)?"
    ))
    .expect("global initializer pattern")
});

static GLOBAL_USE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(&format!(
        r"\A(?:[{WORD}]+[{SPACE}]*::[{SPACE}]*)?(g_[{WORD}]+)"
    ))
    .expect("global use pattern")
});

static LITERAL_CONST: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(&format!(
        r#"\A(?:mk_constant|get|find)[{SPACE}]*\([{SPACE}]*(name[{SPACE}]*[({{][{SPACE}]*)?""#
    ))
    .expect("literal constant pattern")
});

static STRING: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r#""((?:[^"\\\n]|\\.)*)""#).expect("raw string pattern"));

static STRING_AT: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(&format!(
        r#"\A[{SPACE}]*"((?:[^"\\\n]|\\.)*)"[{SPACE}]*(,)?"#
    ))
    .expect("raw string component pattern")
});

/// A hardcoded Lean constant name at its occurrence in the masked source.
#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct CppConstantUse {
    /// One-based LF line of the identifier or literal use site.
    pub line: usize,
    pub constant: String,
}

impl CppSource<'_> {
    /// Extract this file's global constant-name assignments in source order.
    /// A later initializer for the same identifier replaces the earlier one.
    #[must_use]
    pub fn global_constant_names(&self) -> BTreeMap<String, String> {
        let code = self.masked();
        let mut names = BTreeMap::new();
        for initializer in masked_matches(code, 0..code.len(), &GLOBAL_INIT, MatchEnd::Word) {
            let Some(symbol) = initializer.captures.get(1) else {
                continue;
            };
            let identifier = symbol.as_str();
            let start = initializer.end;
            let end = code[start..]
                .find(';')
                .map_or(code.len(), |offset| start + offset);
            let raw = self.raw_slice(start..end).unwrap_or_default();
            let parts: Vec<_> = STRING
                .captures_iter(raw)
                .filter_map(|captures| captures.get(1).map(|part| part.as_str()))
                .collect();
            let name = if parts.is_empty() {
                identifier.to_owned()
            } else {
                parts.join(".")
            };
            names.insert(identifier.to_owned(), name);
        }
        names
    }
}

pub(super) fn constant_uses(
    source: &CppSource<'_>,
    line_starts: &[usize],
    span: Range<usize>,
    local: &BTreeMap<String, String>,
    shared: &BTreeMap<String, String>,
) -> Vec<CppConstantUse> {
    let code = source.masked();
    let mut uses = Vec::new();
    for found in masked_matches(code, span.clone(), &GLOBAL_USE, MatchEnd::Word) {
        let Some(symbol) = found.captures.get(1) else {
            continue;
        };
        let identifier = symbol.as_str();
        let constant = local
            .get(identifier)
            .or_else(|| shared.get(identifier))
            .map_or_else(|| identifier.to_owned(), String::clone);
        uses.push(CppConstantUse {
            line: line_of(line_starts, found.start + symbol.start()),
            constant,
        });
    }
    for found in masked_matches(code, span, &LITERAL_CONST, MatchEnd::BeforeQuote) {
        let raw = source.raw_slice(found.end..code.len()).unwrap_or_default();
        let multipart = found.captures.get(1).is_some();
        uses.push(CppConstantUse {
            line: line_of(line_starts, found.start),
            constant: literal_name(raw, multipart),
        });
    }
    uses.sort_unstable_by(|left, right| {
        (left.line, &left.constant).cmp(&(right.line, &right.constant))
    });
    uses
}

fn literal_name(mut raw: &str, multipart: bool) -> String {
    let mut parts = Vec::new();
    while let Some(captures) = STRING_AT.captures(raw) {
        let (Some(whole), Some(part)) = (captures.get(0), captures.get(1)) else {
            break;
        };
        parts.push(part.as_str());
        if !multipart || captures.get(2).is_none() {
            break;
        }
        raw = &raw[whole.end()..];
    }
    parts.join(".")
}

#[derive(Clone, Copy)]
enum MatchEnd {
    Word,
    BeforeQuote,
}

struct MaskedMatch<'a> {
    start: usize,
    end: usize,
    captures: Captures<'a>,
}

fn masked_matches<'a>(
    code: &'a str,
    span: Range<usize>,
    pattern: &'static Regex,
    match_end: MatchEnd,
) -> impl Iterator<Item = MaskedMatch<'a>> + 'a {
    let fragment = &code[span.clone()];
    let mut previous_is_word = code[..span.start]
        .chars()
        .next_back()
        .is_some_and(python_word);
    let mut next_allowed = 0;
    fragment.char_indices().filter_map(move |(at, ch)| {
        let is_word = python_word(ch);
        // Using the exact Python word boundary here allows the matcher to
        // retry inside an unsuccessful candidate without consuming its text.
        let starts_match = is_word && !previous_is_word && at >= next_allowed;
        previous_is_word = is_word;
        if !starts_match {
            return None;
        }

        let tail = &fragment[at..];
        let captures = pattern.captures(tail)?;
        let end = captures.get(0)?.end();
        let end = match match_end {
            MatchEnd::Word => {
                if tail[end..].chars().next().is_some_and(python_word) {
                    return None;
                }
                end
            }
            // The regex consumes the lookahead quote to verify it. Python's
            // logical match ends immediately before it.
            MatchEnd::BeforeQuote => end - 1,
        };
        next_allowed = at + end;
        Some(MaskedMatch {
            start: span.start + at,
            end: span.start + next_allowed,
            captures,
        })
    })
}

#[cfg(test)]
mod tests {
    use super::{constant_uses, BTreeMap, CppConstantUse, CppSource, Range};

    fn uses(
        source: &CppSource<'_>,
        span: Range<usize>,
        shared: &BTreeMap<String, String>,
    ) -> Vec<CppConstantUse> {
        let starts: Vec<_> = std::iter::once(0)
            .chain(source.masked().match_indices('\n').map(|(at, _)| at + 1))
            .collect();
        constant_uses(
            source,
            &starts,
            span,
            &source.global_constant_names(),
            shared,
        )
    }

    fn projection(uses: &[CppConstantUse]) -> Vec<(usize, &str)> {
        uses.iter()
            .map(|site| (site.line, site.constant.as_str()))
            .collect()
    }

    #[test]
    fn extracts_initializers_through_the_masked_semicolon_or_eof() {
        let source = CppSource::new(concat!(
            "/* α\u{2028} */\n",
            "g_repeat = new name(\"old\");\n",
            "g_repeat = new_persistent_expr_const({\"新\"});\n",
            "g_dotted = new name(\"Root;Part\" /* \"Comment\" */, \"Leaf\");\n",
            "ns::g_bare = new thing();\n",
            "g_invalid = newish(\"ignored\");\n",
            "g_empty = new name(\"\");\n",
            "g_eof = new thing(\"One\")\n",
            "/* \"After\" */\n",
        ));
        assert_eq!(
            source.global_constant_names(),
            BTreeMap::from([
                ("g_repeat".into(), "新".into()),
                ("g_dotted".into(), "Root;Part.Comment.Leaf".into()),
                ("g_bare".into(), "g_bare".into()),
                ("g_empty".into(), "".into()),
                ("g_eof".into(), "One.After".into()),
            ])
        );
    }

    #[test]
    fn maps_raw_literals_and_keeps_local_priority_and_sorted_duplicates() {
        let source = CppSource::new(concat!(
            "/* α\u{2028} */\n",
            "g_same = new thing();\n",
            "g_local = new name(\"Local\", \"Ω\");\n",
            "int f(int x = g_arg) {\n",
            "  ns\n",
            "  ::g_shared; g_same; g_shared; g_unknown; g_local;\n",
            "  g_first::g_second; αg_noise; x\u{0345}g_accent; g_Ω; g_;\n",
            "  find(/* α */\"A\"); get(name{\"Root\", \"Ω\"}); mk_constant(\"Z\", \"ignored\");\n",
            "  get(name(\"Before\", /* α */ \"After\")); find(\"A\\\"B\");\n",
            "  find(\"New\nline\");\n",
            "  get(name(\"\", \"X\"));\n",
            "}\n",
        ));
        let shared = BTreeMap::from([
            ("g_shared".into(), "Other.α".into()),
            ("g_same".into(), "FromOther".into()),
            ("g_local".into(), "Wrong".into()),
        ]);
        let start = source.masked().find("int f(").expect("function start");
        let end = source.masked().rfind('}').expect("function close") + 1;
        assert_eq!(
            projection(&uses(&source, start..end, &shared)),
            [
                (4, "g_arg"),
                (6, "Local.Ω"),
                (6, "Other.α"),
                (6, "Other.α"),
                (6, "g_same"),
                (6, "g_unknown"),
                (7, "g_accent"),
                (7, "g_second"),
                (7, "g_Ω"),
                (8, "A"),
                (8, "Root.Ω"),
                (8, "Z"),
                (9, r#"A\"B"#),
                (9, "Before"),
                (10, ""),
                (12, ".X"),
            ]
        );
    }

    #[test]
    fn respects_masked_endpos_and_reads_raw_literals_beyond_it() {
        let shared = BTreeMap::new();
        let source = CppSource::new("Aget(\"hidden\") g_UnknownSuffix find(\"after\")");
        let end = source.masked().find("Suffix").expect("identifier suffix");
        assert_eq!(
            projection(&uses(&source, 1..end, &shared)),
            [(1, "g_Unknown")]
        );

        let source = CppSource::new("get(\"Data\")");
        assert!(uses(&source, 0..4, &shared).is_empty());
        assert_eq!(projection(&uses(&source, 0..5, &shared)), [(1, "Data")]);
    }
}
