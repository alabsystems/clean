// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The line-based import grammar used by the recorded K3 reader.

use super::python_whitespace;
use crate::EvidenceCheckError;

fn mask_comments_and_strings(source: &str) -> String {
    // Python reads Lean source with universal newlines. The digest is checked
    // over the original bytes before this normalization.
    let source = source.replace("\r\n", "\n").replace('\r', "\n");
    let mut chars = source.chars().peekable();
    let mut masked = String::with_capacity(source.len());
    let mut comment_depth = 0;
    let mut in_string = false;
    while let Some(ch) = chars.next() {
        if comment_depth > 0 {
            match (ch, chars.peek()) {
                ('/', Some('-')) => {
                    comment_depth += 1;
                    chars.next();
                    masked.push_str("  ");
                }
                ('-', Some('/')) => {
                    comment_depth -= 1;
                    chars.next();
                    masked.push_str("  ");
                }
                _ => masked.push(if ch == '\n' { '\n' } else { ' ' }),
            }
        } else if in_string {
            if ch == '\\' && chars.next().is_some() {
                masked.push_str("  ");
            } else {
                in_string = ch != '"';
                masked.push(if ch == '\n' { '\n' } else { ' ' });
            }
        } else {
            match (ch, chars.peek()) {
                ('/', Some('-')) => {
                    comment_depth = 1;
                    chars.next();
                    masked.push_str("  ");
                }
                ('-', Some('-')) => {
                    masked.push(' ');
                    while chars.peek().is_some_and(|&next| next != '\n') {
                        chars.next();
                        masked.push(' ');
                    }
                }
                ('"', _) => {
                    in_string = true;
                    masked.push(' ');
                }
                _ => masked.push(ch),
            }
        }
    }
    masked
}

fn after_keyword<'a>(line: &'a str, keyword: &str) -> Option<&'a str> {
    let tail = line.strip_prefix(keyword)?;
    tail.starts_with([' ', '\t'])
        .then(|| tail.trim_start_matches([' ', '\t']))
}

fn operand(line: &str) -> Option<&str> {
    let end = line.find(python_whitespace).unwrap_or(line.len());
    (end > 0).then(|| &line[..end])
}

fn imported_module(line: &str) -> Option<&str> {
    let line = line.trim_start_matches([' ', '\t']);
    let line = after_keyword(line, "public")
        .or_else(|| after_keyword(line, "private"))
        .unwrap_or(line);
    let line = after_keyword(line, "meta").unwrap_or(line);
    let tail = after_keyword(line, "import")?;
    // With no operand following `all`, the Python regex reads `all` itself.
    after_keyword(tail, "all")
        .and_then(operand)
        .or_else(|| operand(tail))
}

fn module_name(module: &str) -> bool {
    module.split('.').all(|part| {
        let mut chars = part.bytes();
        chars
            .next()
            .is_some_and(|first| first.is_ascii_alphabetic() || first == b'_')
            && chars.all(|ch| ch.is_ascii_alphanumeric() || matches!(ch, b'_' | b'\''))
    })
}

pub(super) fn imports(source: &str, relative: &str) -> Result<Vec<String>, EvidenceCheckError> {
    let masked = mask_comments_and_strings(source);
    masked
        .split('\n')
        .filter_map(imported_module)
        .map(|module| {
            if module_name(module) {
                Ok(module.to_owned())
            } else {
                Err(EvidenceCheckError::Invalid(format!(
                    "{relative} imports {module:?}, a name this reader does not follow"
                )))
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::imports;

    #[test]
    fn preserves_line_import_grammar_and_masks_noncode() {
        let source = "import Top\r\n/- outer /- nested -/\nimport Comment\n-/\n\
            def note := \"\nimport String\nescaped \\\" end\"\n\
            -- import LineComment\n  private meta import all One.Two' Ignored.Second\n\
            public import Three\rmeta import Four\nimport all\nimport\u{a0}NotCapture\n\
            import Delimited\u{1c}Ignored\nimported fail\n";
        assert_eq!(
            imports(source, "Probe.lean").unwrap(),
            ["Top", "One.Two'", "Three", "Four", "all", "Delimited"]
        );
    }

    #[test]
    fn refuses_import_operands_outside_the_ascii_module_grammar() {
        for operand in ["«Odd.Name»", "A..B", "A/B", ".A", "1A", "A.β"] {
            let error = imports(&format!("import {operand}\n"), "Probe.lean").unwrap_err();
            assert!(
                error.to_string().contains("does not follow"),
                "{operand}: {error}"
            );
        }
    }
}
