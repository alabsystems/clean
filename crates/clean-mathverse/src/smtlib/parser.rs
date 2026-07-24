// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT-LIB2 S-expression parser.
//!
//! Parses `.smt2` files into structured AST. Handles `;` line comments,
//! S-expression commands, quoted symbols (`|...|`), string literals,
//! and the standard SMT-LIB2 command set.

use super::types::{SmtCommand, SmtScript, SmtSort, SmtTerm};
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Error type
// ════════════════════════════════════════════════════════════════════════════

/// Errors raised during SMT-LIB2 parsing.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SmtParseError {
    /// I/O error reading file.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    /// Unexpected token or structure.
    #[error("parse error at position {pos}: {msg}")]
    Syntax { pos: usize, msg: String },
}

pub(crate) type SmtParseResult<T> = Result<T, SmtParseError>;

// ════════════════════════════════════════════════════════════════════════════
// Tokenizer (character-level cursor)
// ════════════════════════════════════════════════════════════════════════════

struct Parser<'a> {
    input: &'a [u8],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input: input.as_bytes(),
            pos: 0,
        }
    }

    fn at_end(&self) -> bool {
        self.pos >= self.input.len()
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn consume(&mut self) -> Option<u8> {
        let ch = self.peek()?;
        self.advance();
        Some(ch)
    }

    fn expect(&mut self, ch: u8) -> SmtParseResult<()> {
        match self.peek() {
            Some(c) if c == ch => {
                self.advance();
                Ok(())
            }
            other => Err(SmtParseError::Syntax {
                pos: self.pos,
                msg: format!(
                    "expected '{}', got '{}'",
                    ch as char,
                    other.map_or("EOF".to_owned(), |c| (c as char).to_string())
                ),
            }),
        }
    }

    /// Skip whitespace and `;` line comments.
    fn skip_ws(&mut self) {
        loop {
            while let Some(ch) = self.peek() {
                if ch.is_ascii_whitespace() {
                    self.advance();
                } else {
                    break;
                }
            }
            if self.peek() == Some(b';') {
                while let Some(ch) = self.consume() {
                    if ch == b'\n' {
                        break;
                    }
                }
                continue;
            }
            break;
        }
    }

    /// Read a symbol: alphanumeric + `_` + `.` + `-` + `+` + `*` + `/` + `@` + `!` + `~` etc.
    fn read_symbol(&mut self) -> SmtParseResult<String> {
        let start = self.pos;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_alphanumeric()
                || ch == b'_'
                || ch == b'.'
                || ch == b'-'
                || ch == b'+'
                || ch == b'*'
                || ch == b'/'
                || ch == b'@'
                || ch == b'!'
                || ch == b'~'
                || ch == b'<'
                || ch == b'>'
                || ch == b'='
                || ch == b'?'
                || ch == b'#'
                || ch == b'$'
                || ch == b'%'
                || ch == b'&'
                || ch == b'^'
                || ch == b':'
            {
                self.advance();
            } else {
                break;
            }
        }
        if self.pos == start {
            return Err(SmtParseError::Syntax {
                pos: self.pos,
                msg: "expected symbol".to_owned(),
            });
        }
        Ok(String::from_utf8_lossy(&self.input[start..self.pos]).into_owned())
    }

    /// Read a quoted symbol: `|...|`.
    fn read_quoted_symbol(&mut self) -> SmtParseResult<String> {
        self.expect(b'|')?;
        let start = self.pos;
        loop {
            match self.consume() {
                Some(b'|') => {
                    return Ok(
                        String::from_utf8_lossy(&self.input[start..self.pos - 1]).into_owned()
                    );
                }
                None => {
                    return Err(SmtParseError::Syntax {
                        pos: start,
                        msg: "unterminated quoted symbol".to_owned(),
                    });
                }
                _ => {}
            }
        }
    }

    /// Read a string literal: `"..."`.
    fn read_string_lit(&mut self) -> SmtParseResult<String> {
        self.expect(b'"')?;
        let start = self.pos;
        loop {
            match self.consume() {
                Some(b'"') => {
                    // SMT-LIB uses `""` for escaped quotes.
                    if self.peek() == Some(b'"') {
                        self.advance();
                        continue;
                    }
                    return Ok(
                        String::from_utf8_lossy(&self.input[start..self.pos - 1]).into_owned()
                    );
                }
                None => {
                    return Err(SmtParseError::Syntax {
                        pos: start,
                        msg: "unterminated string literal".to_owned(),
                    });
                }
                _ => {}
            }
        }
    }

    /// Read a numeral.
    fn read_numeral(&mut self) -> SmtParseResult<String> {
        let start = self.pos;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() || ch == b'.' {
                self.advance();
            } else {
                break;
            }
        }
        Ok(String::from_utf8_lossy(&self.input[start..self.pos]).into_owned())
    }

    /// Read any token (symbol, numeral, string, or quoted symbol).
    fn read_token(&mut self) -> SmtParseResult<String> {
        self.skip_ws();
        match self.peek() {
            Some(b'|') => self.read_quoted_symbol(),
            Some(b'"') => self.read_string_lit(),
            Some(ch) if ch.is_ascii_digit() => self.read_numeral(),
            _ => self.read_symbol(),
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Sort parser
// ════════════════════════════════════════════════════════════════════════════

fn parse_sort(p: &mut Parser<'_>) -> SmtParseResult<SmtSort> {
    p.skip_ws();
    if p.peek() == Some(b'(') {
        p.advance();
        p.skip_ws();
        let name = p.read_token()?;
        let mut params = Vec::new();
        loop {
            p.skip_ws();
            if p.peek() == Some(b')') {
                p.advance();
                break;
            }
            params.push(parse_sort(p)?);
        }
        // Recognize built-in parameterized sorts.
        match name.as_str() {
            "Array" if params.len() == 2 => {
                let elem = params.pop().expect("checked len");
                let idx = params.pop().expect("checked len");
                Ok(SmtSort::Array(Box::new(idx), Box::new(elem)))
            }
            "_" if !params.is_empty() => {
                // Indexed sorts like (_ BitVec 32)
                // params[0] is sort name (parsed as Named), params[1..] are indices
                // Actually in (_ BitVec 32), after `_` we read `BitVec` then `32`.
                // But we already parsed them as sorts. Let's handle the common case.
                Ok(SmtSort::Named(format!(
                    "({name} {})",
                    params
                        .iter()
                        .map(|s| format!("{s:?}"))
                        .collect::<Vec<_>>()
                        .join(" ")
                )))
            }
            _ => Ok(SmtSort::App(name, params)),
        }
    } else {
        let name = p.read_token()?;
        match name.as_str() {
            "Bool" => Ok(SmtSort::Bool),
            "Int" => Ok(SmtSort::Int),
            "Real" => Ok(SmtSort::Real),
            _ => Ok(SmtSort::Named(name)),
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Term parser
// ════════════════════════════════════════════════════════════════════════════

fn parse_term(p: &mut Parser<'_>) -> SmtParseResult<SmtTerm> {
    p.skip_ws();

    if p.at_end() {
        return Err(SmtParseError::Syntax {
            pos: p.pos,
            msg: "unexpected end of input in term".to_owned(),
        });
    }

    // String literal.
    if p.peek() == Some(b'"') {
        let s = p.read_string_lit()?;
        return Ok(SmtTerm::StringLit(s));
    }

    // Bitvector literal: #b... or #x...
    if p.peek() == Some(b'#') {
        let start = p.pos;
        p.advance();
        match p.peek() {
            Some(b'b') | Some(b'x') => {
                p.advance();
                while let Some(ch) = p.peek() {
                    if ch.is_ascii_alphanumeric() {
                        p.advance();
                    } else {
                        break;
                    }
                }
                let lit = String::from_utf8_lossy(&p.input[start..p.pos]).into_owned();
                return Ok(SmtTerm::BvLit(lit));
            }
            _ => {
                // Not a bv literal — it will be consumed as part of a symbol.
                p.pos = start;
            }
        }
    }

    // Parenthesized expression.
    if p.peek() == Some(b'(') {
        p.advance();
        p.skip_ws();

        if p.peek() == Some(b')') {
            p.advance();
            return Ok(SmtTerm::App("".to_owned(), Vec::new()));
        }

        // Check for special forms.
        let head_start = p.pos;
        let head = p.read_token()?;

        match head.as_str() {
            "let" => return parse_let(p),
            "forall" => return parse_quantifier(p, true),
            "exists" => return parse_quantifier(p, false),
            "!" => return parse_annotated(p),
            "_" => {
                // Indexed identifier: (_ op idx...)
                let op = p.read_token()?;
                p.skip_ws();
                let mut indices = vec![p.read_token()?];
                loop {
                    p.skip_ws();
                    if p.peek() == Some(b')') {
                        p.advance();
                        break;
                    }
                    indices.push(p.read_token()?);
                }
                let indexed_name = format!("(_ {op} {})", indices.join(" "));
                // Check if this is followed by arguments (another paren-application).
                return Ok(SmtTerm::Symbol(indexed_name));
            }
            "as" => {
                // Qualified identifier: (as name sort)
                let name = p.read_token()?;
                p.skip_ws();
                skip_sexp(p);
                p.skip_ws();
                p.expect(b')')?;
                return Ok(SmtTerm::Symbol(name));
            }
            _ => {
                // Regular function application: (head arg1 arg2 ...)
                // Check if head was a parenthesized expression itself — e.g. `((_ extract 7 0) x)`.
                // In that case we'd need to re-parse. But for simplicity, treat head as the function name.
                let _ = head_start; // suppress unused warning
                let mut args = Vec::new();
                loop {
                    p.skip_ws();
                    if p.peek() == Some(b')') {
                        p.advance();
                        break;
                    }
                    if p.at_end() {
                        break;
                    }
                    args.push(parse_term(p)?);
                }
                return Ok(SmtTerm::App(head, args));
            }
        }
    }

    // Numeral (possibly negative with preceding `-`).
    if let Some(ch) = p.peek() {
        if ch.is_ascii_digit() {
            let num = p.read_numeral()?;
            if num.contains('.') {
                return Ok(SmtTerm::RealLit(num));
            }
            return Ok(SmtTerm::IntLit(num.parse().unwrap_or(0)));
        }
    }

    // Symbol.
    let sym = p.read_token()?;
    match sym.as_str() {
        "true" => Ok(SmtTerm::BoolLit(true)),
        "false" => Ok(SmtTerm::BoolLit(false)),
        _ => Ok(SmtTerm::Symbol(sym)),
    }
}

fn parse_let(p: &mut Parser<'_>) -> SmtParseResult<SmtTerm> {
    p.skip_ws();
    p.expect(b'(')?;
    let mut bindings = Vec::new();
    loop {
        p.skip_ws();
        if p.peek() == Some(b')') {
            p.advance();
            break;
        }
        p.expect(b'(')?;
        p.skip_ws();
        let name = p.read_token()?;
        p.skip_ws();
        let val = parse_term(p)?;
        p.skip_ws();
        p.expect(b')')?;
        bindings.push((name, val));
    }
    p.skip_ws();
    let body = parse_term(p)?;
    p.skip_ws();
    p.expect(b')')?;
    Ok(SmtTerm::Let(bindings, Box::new(body)))
}

fn parse_quantifier(p: &mut Parser<'_>, is_forall: bool) -> SmtParseResult<SmtTerm> {
    p.skip_ws();
    p.expect(b'(')?;
    let mut vars = Vec::new();
    loop {
        p.skip_ws();
        if p.peek() == Some(b')') {
            p.advance();
            break;
        }
        p.expect(b'(')?;
        p.skip_ws();
        let name = p.read_token()?;
        p.skip_ws();
        let sort = parse_sort(p)?;
        p.skip_ws();
        p.expect(b')')?;
        vars.push((name, sort));
    }
    p.skip_ws();
    let body = parse_term(p)?;
    p.skip_ws();
    p.expect(b')')?;
    if is_forall {
        Ok(SmtTerm::Forall(vars, Box::new(body)))
    } else {
        Ok(SmtTerm::Exists(vars, Box::new(body)))
    }
}

fn parse_annotated(p: &mut Parser<'_>) -> SmtParseResult<SmtTerm> {
    p.skip_ws();
    let inner = parse_term(p)?;
    let mut attrs = Vec::new();
    loop {
        p.skip_ws();
        if p.peek() == Some(b')') {
            p.advance();
            break;
        }
        if p.at_end() {
            break;
        }
        let key = p.read_token()?;
        p.skip_ws();
        // Attribute value: could be a symbol, numeral, or S-expression.
        let value = if p.peek() == Some(b'(') {
            skip_sexp(p);
            String::new()
        } else if p.peek() == Some(b')') {
            String::new()
        } else {
            p.read_token().unwrap_or_default()
        };
        attrs.push((key, value));
    }
    Ok(SmtTerm::Annotated(Box::new(inner), attrs))
}

/// Skip an entire S-expression (used for things we don't need to parse).
fn skip_sexp(p: &mut Parser<'_>) {
    p.skip_ws();
    if p.peek() == Some(b'(') {
        let mut depth = 1u32;
        p.advance();
        while !p.at_end() && depth > 0 {
            match p.consume() {
                Some(b'(') => depth += 1,
                Some(b')') => depth -= 1,
                Some(b'"') => {
                    // Skip string literal.
                    loop {
                        match p.consume() {
                            Some(b'"') => {
                                if p.peek() != Some(b'"') {
                                    break;
                                }
                                p.advance();
                            }
                            None => break,
                            _ => {}
                        }
                    }
                }
                Some(b'|') => {
                    // Skip quoted symbol.
                    while let Some(ch) = p.consume() {
                        if ch == b'|' {
                            break;
                        }
                    }
                }
                _ => {}
            }
        }
    } else {
        // Skip a single token.
        let _ = p.read_token();
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Sorted variable list parser (for declare-fun params, define-fun params)
// ════════════════════════════════════════════════════════════════════════════

fn parse_sort_list(p: &mut Parser<'_>) -> SmtParseResult<Vec<SmtSort>> {
    p.skip_ws();
    p.expect(b'(')?;
    let mut sorts = Vec::new();
    loop {
        p.skip_ws();
        if p.peek() == Some(b')') {
            p.advance();
            break;
        }
        sorts.push(parse_sort(p)?);
    }
    Ok(sorts)
}

fn parse_sorted_var_list(p: &mut Parser<'_>) -> SmtParseResult<Vec<(String, SmtSort)>> {
    p.skip_ws();
    p.expect(b'(')?;
    let mut vars = Vec::new();
    loop {
        p.skip_ws();
        if p.peek() == Some(b')') {
            p.advance();
            break;
        }
        p.expect(b'(')?;
        p.skip_ws();
        let name = p.read_token()?;
        p.skip_ws();
        let sort = parse_sort(p)?;
        p.skip_ws();
        p.expect(b')')?;
        vars.push((name, sort));
    }
    Ok(vars)
}

// ════════════════════════════════════════════════════════════════════════════
// Command parser
// ════════════════════════════════════════════════════════════════════════════

fn parse_command(p: &mut Parser<'_>) -> SmtParseResult<SmtCommand> {
    p.skip_ws();
    p.expect(b'(')?;
    p.skip_ws();
    let cmd = p.read_token()?;

    let result = match cmd.as_str() {
        "set-logic" => {
            p.skip_ws();
            let logic = p.read_token()?;
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::SetLogic(logic))
        }
        "declare-sort" => {
            p.skip_ws();
            let name = p.read_token()?;
            p.skip_ws();
            let arity_str = p.read_token()?;
            let arity: u32 = arity_str.parse().unwrap_or(0);
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::DeclareSort(name, arity))
        }
        "define-sort" => {
            p.skip_ws();
            let name = p.read_token()?;
            p.skip_ws();
            // Parse parameter list.
            p.expect(b'(')?;
            let mut params = Vec::new();
            loop {
                p.skip_ws();
                if p.peek() == Some(b')') {
                    p.advance();
                    break;
                }
                params.push(p.read_token()?);
            }
            p.skip_ws();
            let sort = parse_sort(p)?;
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::DefineSort(name, params, sort))
        }
        "declare-fun" => {
            p.skip_ws();
            let name = p.read_token()?;
            p.skip_ws();
            let param_sorts = parse_sort_list(p)?;
            p.skip_ws();
            let ret_sort = parse_sort(p)?;
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::DeclareFun(name, param_sorts, ret_sort))
        }
        "declare-const" => {
            p.skip_ws();
            let name = p.read_token()?;
            p.skip_ws();
            let sort = parse_sort(p)?;
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::DeclareConst(name, sort))
        }
        "define-fun" => {
            p.skip_ws();
            let name = p.read_token()?;
            p.skip_ws();
            let params = parse_sorted_var_list(p)?;
            p.skip_ws();
            let ret_sort = parse_sort(p)?;
            p.skip_ws();
            let body = parse_term(p)?;
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::DefineFun(name, params, ret_sort, body))
        }
        "assert" => {
            p.skip_ws();
            let term = parse_term(p)?;
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::Assert(term))
        }
        "check-sat" => {
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::CheckSat)
        }
        "push" => {
            p.skip_ws();
            let n: u32 = p
                .read_token()
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(1);
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::Push(n))
        }
        "pop" => {
            p.skip_ws();
            let n: u32 = p
                .read_token()
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(1);
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::Pop(n))
        }
        "set-info" => {
            p.skip_ws();
            let key = p.read_token()?;
            p.skip_ws();
            // Value could be a string literal, symbol, or S-expression.
            let value = if p.peek() == Some(b'"') {
                p.read_string_lit()?
            } else if p.peek() == Some(b'(') {
                skip_sexp(p);
                String::new()
            } else if p.peek() == Some(b')') {
                String::new()
            } else {
                p.read_token().unwrap_or_default()
            };
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::SetInfo(key, value))
        }
        "set-option" => {
            p.skip_ws();
            let key = p.read_token()?;
            p.skip_ws();
            let value = if p.peek() == Some(b')') {
                String::new()
            } else if p.peek() == Some(b'"') {
                p.read_string_lit()?
            } else {
                p.read_token().unwrap_or_default()
            };
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::SetOption(key, value))
        }
        "get-model" | "get-value" | "get-unsat-core" | "get-proof" | "get-assertions"
        | "get-assignment" | "get-info" | "get-option" => {
            // Skip remaining content.
            skip_to_close_paren(p);
            Ok(SmtCommand::GetInfo(cmd))
        }
        "exit" => {
            p.skip_ws();
            p.expect(b')')?;
            Ok(SmtCommand::Exit)
        }
        _ => {
            // Unknown command — skip content.
            skip_to_close_paren(p);
            Ok(SmtCommand::Unknown(cmd))
        }
    };

    result
}

/// Skip to the matching `)` for the current open paren.
fn skip_to_close_paren(p: &mut Parser<'_>) {
    let mut depth = 1u32;
    while !p.at_end() && depth > 0 {
        match p.consume() {
            Some(b'(') => depth += 1,
            Some(b')') => depth -= 1,
            Some(b'"') => loop {
                match p.consume() {
                    Some(b'"') => {
                        if p.peek() != Some(b'"') {
                            break;
                        }
                        p.advance();
                    }
                    None => break,
                    _ => {}
                }
            },
            Some(b'|') => {
                while let Some(ch) = p.consume() {
                    if ch == b'|' {
                        break;
                    }
                }
            }
            _ => {}
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Public API
// ════════════════════════════════════════════════════════════════════════════

/// Parse an SMT-LIB2 script from text.
///
/// # Errors
///
/// Returns `SmtParseError` on syntax errors. Unrecognized commands are
/// represented as `SmtCommand::Unknown` rather than producing errors.
pub fn parse_smtlib(text: &str) -> SmtParseResult<SmtScript> {
    let mut p = Parser::new(text);
    let mut script = SmtScript::default();

    loop {
        p.skip_ws();
        if p.at_end() {
            break;
        }
        if p.peek() != Some(b'(') {
            // Skip stray characters.
            p.advance();
            continue;
        }
        match parse_command(&mut p) {
            Ok(cmd) => {
                if let SmtCommand::SetLogic(ref logic) = cmd {
                    script.logic = Some(logic.clone());
                }
                script.commands.push(cmd);
            }
            Err(_) => {
                // Best-effort: skip to next top-level command.
                skip_to_close_paren(&mut p);
            }
        }
    }

    Ok(script)
}

/// Parse an SMT-LIB2 file from disk.
///
/// # Errors
///
/// Returns `SmtParseError::Io` on read failure, or parse errors.
pub fn parse_smtlib_file(path: &std::path::Path) -> SmtParseResult<SmtScript> {
    let text = std::fs::read_to_string(path)?;
    parse_smtlib(&text)
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_empty() {
        let script = parse_smtlib("").expect("should parse");
        assert!(script.is_empty());
    }

    #[test]
    fn test_parse_comments_only() {
        let script = parse_smtlib("; This is a comment\n; Another\n").expect("should parse");
        assert!(script.is_empty());
    }

    #[test]
    fn test_parse_set_logic() {
        let script = parse_smtlib("(set-logic QF_LIA)\n").expect("should parse");
        assert_eq!(script.logic, Some("QF_LIA".to_owned()));
        assert_eq!(script.commands.len(), 1);
    }

    #[test]
    fn test_parse_declare_fun() {
        let script = parse_smtlib("(declare-fun x () Int)\n").expect("should parse");
        assert_eq!(script.commands.len(), 1);
        match &script.commands[0] {
            SmtCommand::DeclareFun(name, params, ret) => {
                assert_eq!(name, "x");
                assert!(params.is_empty());
                assert_eq!(*ret, SmtSort::Int);
            }
            other => panic!("expected DeclareFun, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_declare_const() {
        let script = parse_smtlib("(declare-const y Bool)\n").expect("should parse");
        match &script.commands[0] {
            SmtCommand::DeclareConst(name, sort) => {
                assert_eq!(name, "y");
                assert_eq!(*sort, SmtSort::Bool);
            }
            other => panic!("expected DeclareConst, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_assert() {
        let script = parse_smtlib("(assert (> x 0))\n").expect("should parse");
        assert_eq!(script.assert_count(), 1);
        match &script.commands[0] {
            SmtCommand::Assert(term) => {
                assert!(matches!(term, SmtTerm::App(op, _) if op == ">"));
            }
            other => panic!("expected Assert, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_check_sat() {
        let script = parse_smtlib("(check-sat)\n").expect("should parse");
        assert!(script.has_check_sat());
    }

    #[test]
    fn test_parse_full_script() {
        let input = "\
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-const y Int)
(assert (> x 0))
(assert (= (+ x y) 10))
(check-sat)
";
        let script = parse_smtlib(input).expect("should parse");
        assert_eq!(script.logic, Some("QF_LIA".to_owned()));
        assert_eq!(script.commands.len(), 6);
        assert_eq!(script.declaration_count(), 2);
        assert_eq!(script.assert_count(), 2);
        assert!(script.has_check_sat());
    }

    #[test]
    fn test_parse_define_fun() {
        let input = "(define-fun max ((a Int) (b Int)) Int (ite (>= a b) a b))\n";
        let script = parse_smtlib(input).expect("should parse");
        match &script.commands[0] {
            SmtCommand::DefineFun(name, params, ret, _body) => {
                assert_eq!(name, "max");
                assert_eq!(params.len(), 2);
                assert_eq!(*ret, SmtSort::Int);
            }
            other => panic!("expected DefineFun, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_forall() {
        let input = "(assert (forall ((x Int)) (>= x 0)))\n";
        let script = parse_smtlib(input).expect("should parse");
        match &script.commands[0] {
            SmtCommand::Assert(SmtTerm::Forall(vars, _body)) => {
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].0, "x");
                assert_eq!(vars[0].1, SmtSort::Int);
            }
            other => panic!("expected Assert(Forall), got {other:?}"),
        }
    }

    #[test]
    fn test_parse_let() {
        let input = "(assert (let ((a 1) (b 2)) (= (+ a b) 3)))\n";
        let script = parse_smtlib(input).expect("should parse");
        match &script.commands[0] {
            SmtCommand::Assert(SmtTerm::Let(bindings, _body)) => {
                assert_eq!(bindings.len(), 2);
                assert_eq!(bindings[0].0, "a");
            }
            other => panic!("expected Assert(Let), got {other:?}"),
        }
    }

    #[test]
    fn test_parse_push_pop() {
        let input = "(push 1)\n(pop 1)\n";
        let script = parse_smtlib(input).expect("should parse");
        assert_eq!(script.commands.len(), 2);
        assert!(matches!(&script.commands[0], SmtCommand::Push(1)));
        assert!(matches!(&script.commands[1], SmtCommand::Pop(1)));
    }

    #[test]
    fn test_parse_set_info() {
        let input = "(set-info :status sat)\n";
        let script = parse_smtlib(input).expect("should parse");
        match &script.commands[0] {
            SmtCommand::SetInfo(key, value) => {
                assert_eq!(key, ":status");
                assert_eq!(value, "sat");
            }
            other => panic!("expected SetInfo, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_declare_sort() {
        let input = "(declare-sort Pair 0)\n";
        let script = parse_smtlib(input).expect("should parse");
        match &script.commands[0] {
            SmtCommand::DeclareSort(name, arity) => {
                assert_eq!(name, "Pair");
                assert_eq!(*arity, 0);
            }
            other => panic!("expected DeclareSort, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_bool_literals() {
        let input = "(assert (and true false))\n";
        let script = parse_smtlib(input).expect("should parse");
        match &script.commands[0] {
            SmtCommand::Assert(SmtTerm::App(op, args)) => {
                assert_eq!(op, "and");
                assert_eq!(args.len(), 2);
                assert!(matches!(&args[0], SmtTerm::BoolLit(true)));
                assert!(matches!(&args[1], SmtTerm::BoolLit(false)));
            }
            other => panic!("expected Assert(App(and, ...)), got {other:?}"),
        }
    }

    #[test]
    fn test_script_declared_names() {
        let input = "(declare-fun f () Int)\n(declare-const g Bool)\n";
        let script = parse_smtlib(input).expect("should parse");
        let names = script.declared_names();
        assert_eq!(names.len(), 2);
        assert_eq!(names[0].0, "f");
        assert_eq!(names[1].0, "g");
    }
}
