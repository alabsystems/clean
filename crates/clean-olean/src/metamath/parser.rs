// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser for Metamath `.mm` databases.

use super::ast::{CompressedProof, Database, Formula, Proof, Statement};
use super::{MetamathError, MetamathResult};
use std::fs;
use std::path::{Path, PathBuf};

/// Parse a Metamath database from source text.
pub fn parse_database(input: &str) -> MetamathResult<Database> {
    let tokens = lex(input)?;
    let mut parser = Parser::new(tokens, None, Vec::new());
    Ok(Database {
        statements: parser.parse_statements(false)?,
    })
}

/// Parse a Metamath database from a file, recursively expanding `$[ ... $]`.
pub fn parse_database_file(path: impl AsRef<Path>) -> MetamathResult<Database> {
    let path = path.as_ref().to_path_buf();
    parse_database_file_inner(&path, &mut Vec::new())
}

fn parse_database_file_inner(
    path: &Path,
    include_stack: &mut Vec<PathBuf>,
) -> MetamathResult<Database> {
    let canon = path.to_path_buf();
    if include_stack.contains(&canon) {
        return Err(MetamathError::CyclicInclude(path.display().to_string()));
    }
    include_stack.push(canon);
    let input = fs::read_to_string(path)?;
    let tokens = lex(&input)?;
    let base = path.parent().map(Path::to_path_buf);
    let mut parser = Parser::new(tokens, base, include_stack.clone());
    let statements = parser.parse_statements(false)?;
    include_stack.pop();
    Ok(Database { statements })
}

fn lex(input: &str) -> MetamathResult<Vec<String>> {
    let bytes = input.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0usize;
    while i < bytes.len() {
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= bytes.len() {
            break;
        }
        if starts_with(bytes, i, b"$(") {
            i = skip_comment(bytes, i + 2)?;
            continue;
        }
        if bytes[i] == b'$' && i + 1 < bytes.len() && is_sigil_body(bytes[i + 1]) {
            // `bytes[i]` is ASCII `$` and `is_sigil_body` confirmed `bytes[i + 1]`
            // is a single-byte ASCII sigil body, so `i + 2` is a UTF-8 char
            // boundary and this slice cannot panic on multi-byte input.
            let tok = &input[i..i + 2];
            tokens.push(tok.to_string());
            i += 2;
            continue;
        }
        let start = i;
        while i < bytes.len() && !bytes[i].is_ascii_whitespace() {
            if starts_with(bytes, i, b"$(") {
                break;
            }
            if bytes[i] == b'$' && i + 1 < bytes.len() && is_sigil_body(bytes[i + 1]) {
                // Same char-boundary guarantee as above: a confirmed ASCII sigil
                // body means `i + 2` is a valid boundary before slicing.
                break;
            }
            i += 1;
        }
        if start == i {
            return Err(MetamathError::InvalidStatement(
                "lexer stalled on input".to_string(),
            ));
        }
        tokens.push(input[start..i].to_string());
    }
    Ok(tokens)
}

fn starts_with(bytes: &[u8], i: usize, needle: &[u8]) -> bool {
    i + needle.len() <= bytes.len() && &bytes[i..i + needle.len()] == needle
}

/// Returns `true` when `b` is the ASCII body of a Metamath `$x` keyword sigil.
///
/// Every valid sigil body is single-byte ASCII, so callers may use this as a
/// char-boundary guard before slicing `&input[i..i + 2]`: a `true` result means
/// `bytes[i + 1]` is one ASCII byte, hence `i + 2` is a UTF-8 char boundary.
fn is_sigil_body(b: u8) -> bool {
    matches!(
        b,
        b'c' | b'v' | b'd' | b'f' | b'e' | b'a' | b'p' | b'{' | b'}' | b'=' | b'.' | b'[' | b']'
    )
}

fn skip_comment(bytes: &[u8], mut i: usize) -> MetamathResult<usize> {
    let mut depth = 1usize;
    while i < bytes.len() {
        if starts_with(bytes, i, b"$(") {
            depth += 1;
            i += 2;
        } else if starts_with(bytes, i, b"$)") {
            depth -= 1;
            i += 2;
            if depth == 0 {
                return Ok(i);
            }
        } else {
            i += 1;
        }
    }
    Err(MetamathError::UnterminatedComment)
}

struct Parser {
    tokens: Vec<String>,
    index: usize,
    base_dir: Option<PathBuf>,
    include_stack: Vec<PathBuf>,
}

impl Parser {
    fn new(tokens: Vec<String>, base_dir: Option<PathBuf>, include_stack: Vec<PathBuf>) -> Self {
        Self {
            tokens,
            index: 0,
            base_dir,
            include_stack,
        }
    }

    fn parse_statements(&mut self, stop_on_block_end: bool) -> MetamathResult<Vec<Statement>> {
        let mut statements = Vec::new();
        loop {
            let Some(token) = self.peek() else {
                if stop_on_block_end {
                    return Err(MetamathError::UnexpectedEof { context: "block" });
                }
                break;
            };
            match token {
                "$}" if stop_on_block_end => {
                    self.index += 1;
                    break;
                }
                "${" => {
                    self.index += 1;
                    statements.push(Statement::Block(self.parse_statements(true)?));
                }
                "$c" => {
                    self.index += 1;
                    statements.push(Statement::Constants(self.collect_until("$.")?));
                }
                "$v" => {
                    self.index += 1;
                    statements.push(Statement::Variables(self.collect_until("$.")?));
                }
                "$d" => {
                    self.index += 1;
                    statements.push(Statement::Disjoint(self.collect_until("$.")?));
                }
                "$[" => {
                    self.index += 1;
                    let include = self.next_required("include path")?;
                    self.expect("$]")?;
                    let Some(base) = &self.base_dir else {
                        return Err(MetamathError::IncludeWithoutBase(include));
                    };
                    let path = base.join(&include);
                    let nested = parse_database_file_inner(&path, &mut self.include_stack)?;
                    statements.extend(nested.statements);
                }
                _ => statements.push(self.parse_labeled_statement()?),
            }
        }
        Ok(statements)
    }

    fn parse_labeled_statement(&mut self) -> MetamathResult<Statement> {
        let label = self.next_required("label")?;
        let kind = self.next_required("statement kind")?;
        match kind.as_str() {
            "$f" => {
                let typecode = self.next_required("floating typecode")?;
                let variable = self.next_required("floating variable")?;
                self.expect("$.")?;
                Ok(Statement::Floating {
                    label,
                    typecode,
                    variable,
                })
            }
            "$e" => Ok(Statement::Essential {
                label,
                formula: self.parse_formula_until("$.")?,
            }),
            "$a" => Ok(Statement::Axiom {
                label,
                formula: self.parse_formula_until("$.")?,
            }),
            "$p" => {
                let formula = self.parse_formula_until("$=")?;
                let proof = if self.peek() == Some("(") {
                    self.index += 1;
                    let mut labels = Vec::new();
                    while self.peek() != Some(")") {
                        labels.push(self.next_required("compressed proof label")?);
                    }
                    self.expect(")")?;
                    let code = self.collect_until("$.")?.join("");
                    Proof::Compressed(CompressedProof { labels, code })
                } else {
                    Proof::Uncompressed(self.collect_until("$.")?)
                };
                Ok(Statement::Provable {
                    label,
                    formula,
                    proof,
                })
            }
            _ => Err(MetamathError::UnexpectedToken {
                expected: "Metamath statement kind",
                found: kind,
            }),
        }
    }

    fn parse_formula_until(&mut self, end: &'static str) -> MetamathResult<Formula> {
        let tokens = self.collect_until(end)?;
        let Some((typecode, rest)) = tokens.split_first() else {
            return Err(MetamathError::InvalidStatement(
                "expected non-empty formula".to_string(),
            ));
        };
        Ok(Formula {
            typecode: typecode.clone(),
            tokens: rest.to_vec(),
        })
    }

    fn collect_until(&mut self, end: &'static str) -> MetamathResult<Vec<String>> {
        let mut out = Vec::new();
        while let Some(token) = self.peek() {
            if token == end {
                self.index += 1;
                return Ok(out);
            }
            out.push(self.next_required(end)?);
        }
        Err(MetamathError::UnexpectedEof { context: end })
    }

    fn expect(&mut self, expected: &'static str) -> MetamathResult<()> {
        let found = self.next_required(expected)?;
        if found == expected {
            Ok(())
        } else {
            Err(MetamathError::UnexpectedToken { expected, found })
        }
    }

    fn next_required(&mut self, context: &'static str) -> MetamathResult<String> {
        let token = self
            .tokens
            .get(self.index)
            .cloned()
            .ok_or(MetamathError::UnexpectedEof { context })?;
        self.index += 1;
        Ok(token)
    }

    fn peek(&self) -> Option<&str> {
        self.tokens.get(self.index).map(String::as_str)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Mid-token dispatch: a running token `a$` where the byte after `$` is a
    /// UTF-8 multi-byte lead. Previously `&input[i..i + 2]` sliced through the
    /// middle of `é`, panicking (process abort under `panic=abort`). Must now
    /// lex cleanly instead.
    #[test]
    fn lex_mid_token_dollar_before_multibyte_char_does_not_panic() {
        // bytes: 'a' 0x24('$') 0xC3 0xA9  == "a$é"
        let input = "a$\u{e9}";
        assert_eq!(input.as_bytes(), &[0x61, 0x24, 0xC3, 0xA9]);
        let tokens = lex(input).expect("lexing must not panic and must succeed");
        // The whole thing is a single non-whitespace token; `$é` is not a
        // recognized Metamath keyword, so it stays part of the token.
        assert_eq!(tokens, vec!["a$\u{e9}".to_string()]);
    }

    /// Start-of-token dispatch (sibling site): a token that begins with `$`
    /// where the following byte is a UTF-8 multi-byte lead. Previously
    /// `&input[i..i + 2]` at the start-of-token branch sliced a non-char
    /// boundary and panicked. Must now lex cleanly.
    #[test]
    fn lex_start_token_dollar_before_multibyte_char_does_not_panic() {
        // bytes: 0x24('$') 0xC3 0xA9 == "$é"
        let input = "$\u{e9}";
        assert_eq!(input.as_bytes(), &[0x24, 0xC3, 0xA9]);
        let tokens = lex(input).expect("lexing must not panic and must succeed");
        assert_eq!(tokens, vec!["$\u{e9}".to_string()]);
    }

    /// Well-formed keyword tokens must be recognized exactly as before.
    #[test]
    fn lex_recognizes_ascii_keywords_unchanged() {
        let tokens = lex("$c wff $. x").expect("must lex");
        assert_eq!(tokens, vec!["$c", "wff", "$.", "x"]);
    }
}
