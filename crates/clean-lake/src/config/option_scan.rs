// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The fail-closed backstop for gap G50: a `leanOptions` / `moreLeanArgs` /
//! `weakLeanArgs` the `lakefile.lean` line scraper never attributes to a
//! target.
//!
//! The scraper reads `where` blocks one field per line. Lake accepts more
//! layouts than that — `package p { leanOptions := … }`, a declaration
//! written on one line, a field inside a `def` the package later names — and
//! in any of them the options Lake compiles with would otherwise vanish
//! without a diagnostic, so a module Lake refuses would build. This scan
//! finds every mention of the three field names in the lakefile's CODE
//! (comments and string literals blanked) and reports the ones on lines no
//! parsed target field covered. The caller records each as unreadable on the
//! package, and a build then refuses every module rather than guess.

/// The fields that change the language a module is compiled in.
const OPTION_FIELDS: [&str; 3] = ["leanOptions", "moreLeanArgs", "weakLeanArgs"];

/// 0-based line indices of `content` that mention an option field in code
/// and are not marked in `consumed` (one flag per line, as the block parser
/// left it). Each is returned with the trimmed line text.
#[must_use]
pub(crate) fn unattributed_option_mentions(
    content: &str,
    consumed: &[bool],
) -> Vec<(usize, String)> {
    let code = blank_comments_and_strings(content);
    code.lines()
        .zip(content.lines())
        .enumerate()
        .filter(|(index, (code_line, _))| {
            !consumed.get(*index).copied().unwrap_or(false) && mentions_option_field(code_line)
        })
        .map(|(index, (_, original))| (index, original.trim().to_string()))
        .collect()
}

/// Whether `line` names one of [`OPTION_FIELDS`] as a whole identifier.
fn mentions_option_field(line: &str) -> bool {
    let is_ident = |c: char| c.is_alphanumeric() || c == '_' || c == '.' || c == '`' || c == '\'';
    OPTION_FIELDS.iter().any(|field| {
        line.match_indices(field).any(|(at, _)| {
            let before = line[..at].chars().next_back();
            let after = line[at + field.len()..].chars().next();
            !before.is_some_and(is_ident) && !after.is_some_and(is_ident)
        })
    })
}

/// `content` with every comment (`-- …`, nested `/- … -/`) and string literal
/// replaced by spaces, newlines kept, so line numbers still line up.
fn blank_comments_and_strings(content: &str) -> String {
    let chars: Vec<char> = content.chars().collect();
    let mut out = String::with_capacity(content.len());
    let blank = |c: char| if c == '\n' { '\n' } else { ' ' };
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        let next = chars.get(i + 1).copied();
        if c == '-' && next == Some('-') {
            while i < chars.len() && chars[i] != '\n' {
                out.push(' ');
                i += 1;
            }
        } else if c == '/' && next == Some('-') {
            let mut depth = 0_usize;
            while i < chars.len() {
                if chars[i] == '/' && chars.get(i + 1) == Some(&'-') {
                    depth += 1;
                    out.push_str("  ");
                    i += 2;
                } else if chars[i] == '-' && chars.get(i + 1) == Some(&'/') {
                    depth -= 1;
                    out.push_str("  ");
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    out.push(blank(chars[i]));
                    i += 1;
                }
            }
        } else if c == '"' {
            out.push(' ');
            i += 1;
            while i < chars.len() && chars[i] != '"' {
                if chars[i] == '\\' && i + 1 < chars.len() {
                    out.push(blank(chars[i]));
                    i += 1;
                }
                out.push(blank(chars[i]));
                i += 1;
            }
            if i < chars.len() {
                out.push(' ');
                i += 1;
            }
        } else {
            out.push(c);
            i += 1;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_option_scan_ignores_comments_strings_and_longer_identifiers() {
        let content = "-- leanOptions here\n/- moreLeanArgs\n -/\ndef s := \"weakLeanArgs\"\n\
                       def mathlibLeanOptions := 1\nleanOptions2 := 3\n";
        let consumed = vec![false; 7];
        assert!(unattributed_option_mentions(content, &consumed).is_empty());
    }

    #[test]
    fn test_option_scan_reports_unconsumed_and_skips_consumed() {
        let content = "package p { leanOptions := #[] }\n  moreLeanArgs := #[]\n";
        let found = unattributed_option_mentions(content, &[false, true]);
        assert_eq!(
            found,
            vec![(0, "package p { leanOptions := #[] }".to_string())]
        );
    }
}
