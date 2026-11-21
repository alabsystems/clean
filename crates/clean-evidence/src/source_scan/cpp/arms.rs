// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Switch-arm runs in the pinned C++ inventory's masked source.

use std::{ops::Range, sync::LazyLock};

use regex::Regex;
use serde::Serialize;

use super::functions::{line_of, CppFunctionError};
use super::headers::{SPACE, WORD};
use super::{python_whitespace, python_word};

static CASE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(&format!(
        r"\A(?:case[{SPACE}]+((?:[{WORD}]+[{SPACE}]*::[{SPACE}]*)*[{WORD}]+)|(default))[{SPACE}]*:"
    ))
    .expect("case label pattern")
});

/// A run of adjacent labels in a switch, identified by its first label line.
#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct CppCaseArm {
    /// One-based switch number and the labels joined by +, as in switch1/A+B.
    pub name: String,
    /// One-based LF line of the first label in the masked source.
    pub line: usize,
}

pub(super) fn case_arms(
    code: &str,
    line_starts: &[usize],
    span: Range<usize>,
) -> Result<Vec<CppCaseArm>, CppFunctionError> {
    let mut arms = Vec::new();
    let mut number = 0;
    for (offset, keyword) in code[span.clone()].match_indices("switch") {
        let at = span.start + offset;
        let after_keyword = at + keyword.len();
        let tail = &code[after_keyword..span.end];
        if preceded_by_word(code, at) || tail.chars().next().is_some_and(python_word) {
            continue;
        }
        number += 1;
        let open = tail
            .find('{')
            .ok_or_else(|| CppFunctionError::SwitchWithoutBody {
                line: line_of(line_starts, at),
            })?;
        // Only the opening brace must fall inside the function span. An
        // enclosing scope's opening brace can be part of a captured header.
        append_runs(code, line_starts, after_keyword + open, number, &mut arms)?;
    }
    Ok(arms)
}

fn append_runs(
    code: &str,
    line_starts: &[usize],
    opening: usize,
    number: usize,
    arms: &mut Vec<CppCaseArm>,
) -> Result<(), CppFunctionError> {
    let mut at = opening + 1;
    let mut depth = 0_usize;
    let mut previous_end = None;
    while let Some(&byte) = code.as_bytes().get(at) {
        match byte {
            b'{' => depth += 1,
            b'}' if depth == 0 => return Ok(()),
            b'}' => depth -= 1,
            b'c' | b'd' if depth == 0 => {
                // ASCII label initials are UTF-8 boundaries.
                if let Some((label, end)) = label_at(code, at) {
                    let label = label.chars().filter(|&ch| ch != ' ');
                    let adjacent = previous_end
                        .is_some_and(|last| code[last..at].chars().all(python_whitespace));
                    if let Some(arm) = arms.last_mut().filter(|_| adjacent) {
                        arm.name.push('+');
                        arm.name.extend(label);
                    } else {
                        let mut name = format!("switch{number}/");
                        name.extend(label);
                        arms.push(CppCaseArm {
                            name,
                            line: line_of(line_starts, at),
                        });
                    }
                    previous_end = Some(end);
                    at = end;
                    continue;
                }
            }
            _ => {}
        }
        at += 1;
    }
    Err(CppFunctionError::UnbalancedBraces)
}

fn label_at(code: &str, at: usize) -> Option<(&str, usize)> {
    if preceded_by_word(code, at) {
        return None;
    }
    let tail = &code[at..];
    let captures = CASE.captures(tail)?;
    let end = captures.get(0)?.end();
    // A colon in a qualification cannot terminate a label. Reject the
    // trailing colon of this match if it starts another :: separator.
    if tail.as_bytes().get(end) == Some(&b':') {
        return None;
    }
    let label = captures.get(1).or_else(|| captures.get(2))?.as_str();
    let stem = label.rsplit_once("::").map_or(label, |(_, last)| last);
    Some((stem, at + end))
}

fn preceded_by_word(code: &str, at: usize) -> bool {
    code[..at].chars().next_back().is_some_and(python_word)
}

#[cfg(test)]
mod tests {
    use super::{case_arms, CppCaseArm, CppFunctionError};
    use crate::source_scan::cpp::CppSource;

    fn starts(code: &str) -> Vec<usize> {
        std::iter::once(0)
            .chain(code.match_indices('\n').map(|(at, _)| at + 1))
            .collect()
    }

    fn extract(raw: &str) -> Vec<CppCaseArm> {
        let source = CppSource::new(raw);
        let code = source.masked();
        case_arms(code, &starts(code), 0..code.len()).expect("fixture switch arms")
    }

    fn projection(arms: &[CppCaseArm]) -> Vec<(&str, usize)> {
        arms.iter()
            .map(|arm| (arm.name.as_str(), arm.line))
            .collect()
    }

    #[test]
    fn groups_masked_adjacency_and_keeps_nested_switch_order() {
        let arms = extract(concat!(
            "int f() {\n",
            "  switch (x) {\n",
            "    case K::Alpha: // comment-only gap\n",
            "    case K::Beta: {\n",
            "      switch (y) { case Inner: break; }\n",
            "      case Hidden: break;\n",
            "    }\n",
            "    default: break;\n",
            "  }\n",
            "}\n",
        ));
        assert_eq!(
            projection(&arms),
            [
                ("switch1/Alpha+Beta", 3),
                ("switch1/default", 8),
                ("switch2/Inner", 5),
            ]
        );
    }

    #[test]
    fn uses_python_boundaries_and_keeps_tabs_in_qualified_labels() {
        let arms = extract(concat!(
            "int f() {\n",
            "  αswitch; switchα; switch_1;\n",
            "  x\u{0345}switch (x) {\n",
            "    αcase A: ;\n",
            "    case B::\n",
            "    x\u{0345}case K ::\t D\t :\n",
            "\u{1c}   case 0: ;\n",
            "    default ::\n",
            "    default: ;\n",
            "  }\n",
            "}\n",
        ));
        assert_eq!(
            projection(&arms),
            [("switch1/\tD+0", 6), ("switch1/default", 9)]
        );
    }

    #[test]
    fn counts_empty_switches_and_uses_the_first_opening_brace() {
        let arms = extract(concat!(
            "int f() {\n",
            "  switch (Shape{x}) { default: break; }\n",
            "  switch (x) switch (y) { case A: break; }\n",
            "}\n",
        ));
        assert_eq!(projection(&arms), [("switch2/A", 3), ("switch3/A", 3)]);
    }

    #[test]
    fn bounds_the_opening_by_the_function_and_the_close_by_the_file() {
        let code = "int f(int x) {\n switch (x) case 0: return 0;\n}\nint next() { return 1; }\n";
        let end = code.find("\nint next()").expect("next declaration");
        assert_eq!(
            case_arms(code, &starts(code), 0..end),
            Err(CppFunctionError::SwitchWithoutBody { line: 2 })
        );

        let code = "struct switch {\n int f() {\n   return 0;\n }\n case Outer: break;\n};\n";
        let end = code.find("\n case Outer:").expect("enclosing scope");
        let arms = case_arms(code, &starts(code), 0..end).expect("fixture switch arms");
        assert_eq!(projection(&arms), [("switch1/Outer", 5)]);

        let code = "switch (x) { case A:";
        assert_eq!(
            case_arms(code, &[0], 0..code.len()),
            Err(CppFunctionError::UnbalancedBraces)
        );
    }
}
