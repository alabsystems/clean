// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TPTP file parser.
//!
//! Parses `.p` and `.ax` TPTP problem files into structured AST. Handles
//! `%` line comments, `/* ... */` block comments, `include('path').`
//! directives, and `fof/cnf/tff/thf(name, role, formula).` entries.
//!
//! Focus: FOF and TFF sub-languages. CNF is parsed as flat disjunctions.
//! THF is accepted at the entry level but formula parsing may not cover
//! all higher-order constructs.

use super::types::{
    TptpFile, TptpFormula, TptpInclude, TptpLanguage, TptpRole, TptpTerm, TptpType,
};
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Error type
// ════════════════════════════════════════════════════════════════════════════

/// Errors raised during TPTP parsing.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum TptpParseError {
    /// I/O error reading file.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    /// Unexpected token or structure.
    #[error("parse error at position {pos}: {msg}")]
    Syntax { pos: usize, msg: String },
    /// Unknown language tag.
    #[error("unknown language `{lang}`")]
    UnknownLanguage { lang: String },
    /// Unknown role.
    #[error("unknown role `{role}`")]
    UnknownRole { role: String },
}

pub(crate) type TptpParseResult<T> = Result<T, TptpParseError>;

// ════════════════════════════════════════════════════════════════════════════
// Tokenizer (character-level)
// ════════════════════════════════════════════════════════════════════════════

/// Lightweight cursor into the input text.
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

    fn peek_at(&self, offset: usize) -> Option<u8> {
        self.input.get(self.pos + offset).copied()
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn consume(&mut self) -> Option<u8> {
        let ch = self.peek()?;
        self.advance();
        Some(ch)
    }

    fn expect(&mut self, ch: u8) -> TptpParseResult<()> {
        match self.peek() {
            Some(c) if c == ch => {
                self.advance();
                Ok(())
            }
            other => Err(TptpParseError::Syntax {
                pos: self.pos,
                msg: format!(
                    "expected '{}', got '{}'",
                    ch as char,
                    other.map_or("EOF".to_owned(), |c| (c as char).to_string())
                ),
            }),
        }
    }

    /// Skip whitespace and comments.
    fn skip_ws(&mut self) {
        loop {
            // Whitespace
            while let Some(ch) = self.peek() {
                if ch.is_ascii_whitespace() {
                    self.advance();
                } else {
                    break;
                }
            }
            // Line comment: % ...
            if self.peek() == Some(b'%') {
                while let Some(ch) = self.consume() {
                    if ch == b'\n' {
                        break;
                    }
                }
                continue;
            }
            // Block comment: /* ... */
            if self.peek() == Some(b'/') && self.peek_at(1) == Some(b'*') {
                self.advance(); // /
                self.advance(); // *
                loop {
                    match self.consume() {
                        Some(b'*') if self.peek() == Some(b'/') => {
                            self.advance();
                            break;
                        }
                        None => break, // unterminated block comment
                        _ => {}
                    }
                }
                continue;
            }
            break;
        }
    }

    /// Read an identifier: [a-zA-Z0-9_]+
    fn read_ident(&mut self) -> TptpParseResult<String> {
        let start = self.pos;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_alphanumeric() || ch == b'_' {
                self.advance();
            } else {
                break;
            }
        }
        if self.pos == start {
            return Err(TptpParseError::Syntax {
                pos: self.pos,
                msg: "expected identifier".to_owned(),
            });
        }
        Ok(String::from_utf8_lossy(&self.input[start..self.pos]).into_owned())
    }

    /// Read a single-quoted atom: 'content'.
    fn read_quoted(&mut self) -> TptpParseResult<String> {
        self.expect(b'\'')?;
        let start = self.pos;
        loop {
            match self.consume() {
                Some(b'\\') => {
                    // Escaped character — skip next.
                    self.advance();
                }
                Some(b'\'') => {
                    let content = String::from_utf8_lossy(&self.input[start..self.pos - 1]);
                    return Ok(content.into_owned());
                }
                None => {
                    return Err(TptpParseError::Syntax {
                        pos: start,
                        msg: "unterminated quoted atom".to_owned(),
                    });
                }
                _ => {}
            }
        }
    }

    /// Read a name: either an unquoted lowercase identifier or a single-quoted atom.
    fn read_name(&mut self) -> TptpParseResult<String> {
        self.skip_ws();
        if self.peek() == Some(b'\'') {
            self.read_quoted()
        } else {
            self.read_ident()
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// File-level parser
// ════════════════════════════════════════════════════════════════════════════

/// Parse a TPTP file from its text content.
///
/// # Errors
///
/// Returns `TptpParseError` if the file contains syntax errors in the
/// annotated formula entries. Unparseable entries are skipped with a
/// best-effort approach; structurally broken files produce errors.
pub fn parse_tptp(text: &str) -> TptpParseResult<TptpFile> {
    let mut p = Parser::new(text);
    let mut includes = Vec::new();
    let mut formulas = Vec::new();

    loop {
        p.skip_ws();
        if p.at_end() {
            break;
        }

        // Read keyword (fof, cnf, tff, thf, include).
        let kw_start = p.pos;
        let kw = match p.read_ident() {
            Ok(kw) => kw,
            Err(_) => {
                // Skip unrecognized character and try again.
                p.advance();
                continue;
            }
        };

        match kw.as_str() {
            "include" => {
                p.skip_ws();
                p.expect(b'(')?;
                p.skip_ws();
                let path = p.read_quoted()?;
                // Optional formula selection list — skip it.
                p.skip_ws();
                if p.peek() == Some(b',') {
                    skip_until_close_paren(&mut p);
                } else {
                    p.expect(b')')?;
                }
                p.skip_ws();
                let _ = p.expect(b'.');
                includes.push(TptpInclude { path });
            }
            "fof" | "cnf" | "tff" | "thf" => {
                let language = match kw.as_str() {
                    "fof" => TptpLanguage::Fof,
                    "cnf" => TptpLanguage::Cnf,
                    "tff" => TptpLanguage::Tff,
                    "thf" => TptpLanguage::Thf,
                    _ => unreachable!(),
                };

                match parse_annotated_formula(&mut p, language) {
                    Ok(formula) => formulas.push(formula),
                    Err(_) => {
                        // Best-effort: skip to the next `.` at top level.
                        skip_to_dot(&mut p, kw_start);
                    }
                }
            }
            _ => {
                // Unknown top-level keyword — skip the entire entry.
                skip_to_dot(&mut p, kw_start);
            }
        }
    }

    Ok(TptpFile { includes, formulas })
}

/// Parse a TPTP file from disk.
///
/// # Errors
///
/// Returns `TptpParseError::Io` on read failure, or parse errors.
pub fn parse_tptp_file(path: &std::path::Path) -> TptpParseResult<TptpFile> {
    let text = std::fs::read_to_string(path)?;
    parse_tptp(&text)
}

// ════════════════════════════════════════════════════════════════════════════
// Annotated formula parser
// ════════════════════════════════════════════════════════════════════════════

/// Parse `(name, role, formula).` after the language keyword.
fn parse_annotated_formula(
    p: &mut Parser<'_>,
    language: TptpLanguage,
) -> TptpParseResult<TptpFormula> {
    p.skip_ws();
    p.expect(b'(')?;

    // Name.
    p.skip_ws();
    let name = p.read_name()?;

    // Comma + role.
    p.skip_ws();
    p.expect(b',')?;
    p.skip_ws();
    let role_str = p.read_ident()?;
    let role = TptpRole::from_str_tptp(&role_str).ok_or_else(|| TptpParseError::UnknownRole {
        role: role_str.clone(),
    })?;

    // Comma + formula.
    p.skip_ws();
    p.expect(b',')?;
    p.skip_ws();

    // For TFF type declarations: `tff(name, type, sym: type_expr).`
    // We parse these as Atom("sym : type_string") for now.
    let formula = if role == TptpRole::Type {
        parse_type_declaration(p)?
    } else {
        parse_formula(p)?
    };

    // Optional annotation after formula (skip).
    p.skip_ws();
    if p.peek() == Some(b',') {
        skip_until_close_paren(p);
    } else {
        p.expect(b')')?;
    }
    p.skip_ws();
    let _ = p.expect(b'.');

    Ok(TptpFormula {
        name,
        language,
        role,
        formula,
    })
}

/// Parse a TFF type declaration: `symbol : type_expr`.
/// Returns an Atom with the symbol name (type info is discarded for now).
fn parse_type_declaration(p: &mut Parser<'_>) -> TptpParseResult<TptpTerm> {
    let sym = p.read_name()?;
    p.skip_ws();
    if p.peek() == Some(b':') {
        p.advance();
        p.skip_ws();
        // Parse the type expression but represent it as an Atom for simplicity.
        let _ty = parse_tptp_type_expr(p)?;
    }
    Ok(TptpTerm::Atom(sym))
}

// ════════════════════════════════════════════════════════════════════════════
// Formula parser (recursive descent, precedence climbing)
// ════════════════════════════════════════════════════════════════════════════

/// Parse a TPTP formula.
fn parse_formula(p: &mut Parser<'_>) -> TptpParseResult<TptpTerm> {
    parse_iff(p)
}

/// Biconditional: `P <=> Q` (lowest precedence binary).
fn parse_iff(p: &mut Parser<'_>) -> TptpParseResult<TptpTerm> {
    let mut lhs = parse_implies(p)?;
    loop {
        p.skip_ws();
        if p.peek() == Some(b'<') && p.peek_at(1) == Some(b'=') && p.peek_at(2) == Some(b'>') {
            p.advance();
            p.advance();
            p.advance();
            p.skip_ws();
            let rhs = parse_implies(p)?;
            lhs = TptpTerm::Iff(Box::new(lhs), Box::new(rhs));
        } else {
            break;
        }
    }
    Ok(lhs)
}

/// Implication: `P => Q` (right-associative).
fn parse_implies(p: &mut Parser<'_>) -> TptpParseResult<TptpTerm> {
    let lhs = parse_or(p)?;
    p.skip_ws();
    if p.peek() == Some(b'=') && p.peek_at(1) == Some(b'>') {
        p.advance();
        p.advance();
        p.skip_ws();
        let rhs = parse_implies(p)?; // right-associative
        Ok(TptpTerm::Implies(Box::new(lhs), Box::new(rhs)))
    } else {
        Ok(lhs)
    }
}

/// Disjunction: `P | Q`.
fn parse_or(p: &mut Parser<'_>) -> TptpParseResult<TptpTerm> {
    let mut lhs = parse_and(p)?;
    loop {
        p.skip_ws();
        if p.peek() == Some(b'|') {
            p.advance();
            p.skip_ws();
            let rhs = parse_and(p)?;
            lhs = TptpTerm::Or(Box::new(lhs), Box::new(rhs));
        } else {
            break;
        }
    }
    Ok(lhs)
}

/// Conjunction: `P & Q`.
fn parse_and(p: &mut Parser<'_>) -> TptpParseResult<TptpTerm> {
    let mut lhs = parse_unary(p)?;
    loop {
        p.skip_ws();
        if p.peek() == Some(b'&') {
            p.advance();
            p.skip_ws();
            let rhs = parse_unary(p)?;
            lhs = TptpTerm::And(Box::new(lhs), Box::new(rhs));
        } else {
            break;
        }
    }
    Ok(lhs)
}

/// Unary: `~ P`, quantifiers, or atomic.
fn parse_unary(p: &mut Parser<'_>) -> TptpParseResult<TptpTerm> {
    p.skip_ws();
    match p.peek() {
        // Negation.
        Some(b'~') => {
            p.advance();
            p.skip_ws();
            let inner = parse_unary(p)?;
            Ok(TptpTerm::Not(Box::new(inner)))
        }
        // Universal quantifier: ! [X, Y] : body
        Some(b'!') => {
            p.advance();
            p.skip_ws();
            let vars = parse_var_list(p)?;
            p.skip_ws();
            p.expect(b':')?;
            p.skip_ws();
            let body = parse_unary(p)?;
            Ok(TptpTerm::ForAll(vars, Box::new(body)))
        }
        // Existential quantifier: ? [X] : body
        Some(b'?') => {
            p.advance();
            p.skip_ws();
            let vars = parse_var_list(p)?;
            p.skip_ws();
            p.expect(b':')?;
            p.skip_ws();
            let body = parse_unary(p)?;
            Ok(TptpTerm::Exists(vars, Box::new(body)))
        }
        _ => parse_equality(p),
    }
}

/// Equality / disequality or atomic term.
fn parse_equality(p: &mut Parser<'_>) -> TptpParseResult<TptpTerm> {
    let lhs = parse_atomic(p)?;
    p.skip_ws();

    // Check for `!=`
    if p.peek() == Some(b'!') && p.peek_at(1) == Some(b'=') {
        p.advance();
        p.advance();
        p.skip_ws();
        let rhs = parse_atomic(p)?;
        return Ok(TptpTerm::Neq(Box::new(lhs), Box::new(rhs)));
    }

    // Check for `=` (but not `=>`)
    if p.peek() == Some(b'=') && p.peek_at(1) != Some(b'>') {
        p.advance();
        p.skip_ws();
        let rhs = parse_atomic(p)?;
        return Ok(TptpTerm::Eq(Box::new(lhs), Box::new(rhs)));
    }

    Ok(lhs)
}

/// Atomic: parenthesized formula, `$true`, `$false`, variable, function/predicate application.
fn parse_atomic(p: &mut Parser<'_>) -> TptpParseResult<TptpTerm> {
    p.skip_ws();

    // Parenthesized formula.
    if p.peek() == Some(b'(') {
        p.advance();
        p.skip_ws();
        let inner = parse_formula(p)?;
        p.skip_ws();
        p.expect(b')')?;
        return Ok(inner);
    }

    // Dollar-prefixed built-ins: $true, $false, $i, etc.
    if p.peek() == Some(b'$') {
        p.advance();
        let name = p.read_ident()?;
        return match name.as_str() {
            "true" => Ok(TptpTerm::True),
            "false" => Ok(TptpTerm::False),
            _ => Ok(TptpTerm::Atom(format!("${name}"))),
        };
    }

    // Single-quoted atom.
    if p.peek() == Some(b'\'') {
        let name = p.read_quoted()?;
        p.skip_ws();
        if p.peek() == Some(b'(') {
            let args = parse_arg_list(p)?;
            return Ok(TptpTerm::Func(name, args));
        }
        return Ok(TptpTerm::Atom(name));
    }

    // Identifier: uppercase => variable, lowercase => atom/function.
    let name = p.read_ident()?;

    // Check for function application.
    p.skip_ws();
    if p.peek() == Some(b'(') {
        let args = parse_arg_list(p)?;
        return Ok(TptpTerm::Func(name, args));
    }

    // Variable if starts with uppercase.
    if name.as_bytes()[0].is_ascii_uppercase() {
        Ok(TptpTerm::Var(name))
    } else {
        Ok(TptpTerm::Atom(name))
    }
}

/// Parse `[X, Y, Z]` variable list.
fn parse_var_list(p: &mut Parser<'_>) -> TptpParseResult<Vec<String>> {
    p.skip_ws();
    p.expect(b'[')?;
    let mut vars = Vec::new();
    loop {
        p.skip_ws();
        if p.peek() == Some(b']') {
            p.advance();
            break;
        }
        let var = p.read_ident()?;
        vars.push(var);
        p.skip_ws();
        // Optional type annotation: `: type` — skip it.
        if p.peek() == Some(b':') {
            p.advance();
            p.skip_ws();
            let _ty = parse_tptp_type_expr(p)?;
        }
        p.skip_ws();
        if p.peek() == Some(b',') {
            p.advance();
        }
    }
    Ok(vars)
}

/// Parse `(arg1, arg2, ...)` argument list.
fn parse_arg_list(p: &mut Parser<'_>) -> TptpParseResult<Vec<TptpTerm>> {
    p.expect(b'(')?;
    let mut args = Vec::new();
    loop {
        p.skip_ws();
        if p.peek() == Some(b')') {
            p.advance();
            break;
        }
        let arg = parse_formula(p)?;
        args.push(arg);
        p.skip_ws();
        if p.peek() == Some(b',') {
            p.advance();
        }
    }
    Ok(args)
}

// ════════════════════════════════════════════════════════════════════════════
// Type expression parser (minimal TFF types)
// ════════════════════════════════════════════════════════════════════════════

/// Parse a TFF type expression.
fn parse_tptp_type_expr(p: &mut Parser<'_>) -> TptpParseResult<TptpType> {
    let first = parse_type_atom(p)?;
    p.skip_ws();

    // Arrow type: `t1 > t2`.
    if p.peek() == Some(b'>') {
        p.advance();
        p.skip_ws();
        let rhs = parse_tptp_type_expr(p)?; // right-associative
        return Ok(TptpType::Arrow(Box::new(first), Box::new(rhs)));
    }

    // Product type: `t1 * t2`.
    if p.peek() == Some(b'*') {
        let mut parts = vec![first];
        while p.peek() == Some(b'*') {
            p.advance();
            p.skip_ws();
            parts.push(parse_type_atom(p)?);
            p.skip_ws();
        }
        // Check if product is followed by `>` (function from product).
        if p.peek() == Some(b'>') {
            p.advance();
            p.skip_ws();
            let rhs = parse_tptp_type_expr(p)?;
            return Ok(TptpType::Arrow(
                Box::new(TptpType::Product(parts)),
                Box::new(rhs),
            ));
        }
        return Ok(TptpType::Product(parts));
    }

    Ok(first)
}

/// Parse a type atom: `$o`, `$i`, `$int`, `$rat`, `$real`, named, or parenthesized.
fn parse_type_atom(p: &mut Parser<'_>) -> TptpParseResult<TptpType> {
    p.skip_ws();

    if p.peek() == Some(b'(') {
        p.advance();
        p.skip_ws();
        let inner = parse_tptp_type_expr(p)?;
        p.skip_ws();
        p.expect(b')')?;
        return Ok(inner);
    }

    if p.peek() == Some(b'$') {
        p.advance();
        let name = p.read_ident()?;
        return match name.as_str() {
            "o" | "oType" => Ok(TptpType::Bool),
            "i" | "iType" | "tType" => Ok(TptpType::Individual),
            "int" => Ok(TptpType::Int),
            "rat" => Ok(TptpType::Rat),
            "real" => Ok(TptpType::Real),
            _ => Ok(TptpType::Named(format!("${name}"))),
        };
    }

    let name = p.read_ident()?;
    Ok(TptpType::Named(name))
}

// ════════════════════════════════════════════════════════════════════════════
// Helpers
// ════════════════════════════════════════════════════════════════════════════

/// Skip to the next unbalanced `)` (handles nesting).
fn skip_until_close_paren(p: &mut Parser<'_>) {
    let mut depth = 1u32;
    while !p.at_end() && depth > 0 {
        match p.consume() {
            Some(b'(') => depth += 1,
            Some(b')') => depth -= 1,
            Some(b'\'') => {
                // Skip quoted content.
                while let Some(ch) = p.consume() {
                    if ch == b'\'' {
                        break;
                    }
                    if ch == b'\\' {
                        p.advance();
                    }
                }
            }
            _ => {}
        }
    }
}

/// Skip to the next `.` at balanced depth, starting from `_start_pos`.
fn skip_to_dot(p: &mut Parser<'_>, _start_pos: usize) {
    let mut depth = 0i32;
    while !p.at_end() {
        match p.consume() {
            Some(b'(') => depth += 1,
            Some(b')') => depth -= 1,
            Some(b'.') if depth <= 0 => break,
            Some(b'\'') => {
                while let Some(ch) = p.consume() {
                    if ch == b'\'' {
                        break;
                    }
                    if ch == b'\\' {
                        p.advance();
                    }
                }
            }
            _ => {}
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_empty_file() {
        let file = parse_tptp("").expect("should parse empty");
        assert!(file.is_empty());
        assert!(file.includes.is_empty());
    }

    #[test]
    fn test_parse_comment_only() {
        let file = parse_tptp("% This is a comment\n").expect("should parse");
        assert!(file.is_empty());
    }

    #[test]
    fn test_parse_block_comment() {
        let file = parse_tptp("/* block comment */").expect("should parse");
        assert!(file.is_empty());
    }

    #[test]
    fn test_parse_include() {
        let file = parse_tptp("include('Axioms/SET006+0.ax').\n").expect("should parse");
        assert_eq!(file.includes.len(), 1);
        assert_eq!(file.includes[0].path, "Axioms/SET006+0.ax");
    }

    #[test]
    fn test_parse_fof_axiom() {
        let input = "fof(commutativity, axiom, ![X,Y]: f(X,Y) = f(Y,X)).\n";
        let file = parse_tptp(input).expect("should parse");
        assert_eq!(file.formulas.len(), 1);
        let f = &file.formulas[0];
        assert_eq!(f.name, "commutativity");
        assert_eq!(f.language, TptpLanguage::Fof);
        assert_eq!(f.role, TptpRole::Axiom);
        match &f.formula {
            TptpTerm::ForAll(vars, _) => {
                assert_eq!(vars, &["X", "Y"]);
            }
            other => panic!("expected ForAll, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_fof_conjecture() {
        let input = "fof(goal, conjecture, p(a) => q(b)).\n";
        let file = parse_tptp(input).expect("should parse");
        assert_eq!(file.formulas.len(), 1);
        let f = &file.formulas[0];
        assert_eq!(f.role, TptpRole::Conjecture);
        assert!(matches!(&f.formula, TptpTerm::Implies(_, _)));
    }

    #[test]
    fn test_parse_cnf() {
        let input = "cnf(clause1, axiom, p(X) | ~q(X)).\n";
        let file = parse_tptp(input).expect("should parse");
        assert_eq!(file.formulas.len(), 1);
        assert_eq!(file.formulas[0].language, TptpLanguage::Cnf);
        assert!(matches!(&file.formulas[0].formula, TptpTerm::Or(_, _)));
    }

    #[test]
    fn test_parse_negation() {
        let input = "fof(neg, axiom, ~p(a)).\n";
        let file = parse_tptp(input).expect("should parse");
        assert!(matches!(&file.formulas[0].formula, TptpTerm::Not(_)));
    }

    #[test]
    fn test_parse_iff() {
        let input = "fof(bi, axiom, p(X) <=> q(X)).\n";
        let file = parse_tptp(input).expect("should parse");
        assert!(matches!(&file.formulas[0].formula, TptpTerm::Iff(_, _)));
    }

    #[test]
    fn test_parse_equality() {
        let input = "fof(eq, axiom, X = Y).\n";
        let file = parse_tptp(input).expect("should parse");
        assert!(matches!(&file.formulas[0].formula, TptpTerm::Eq(_, _)));
    }

    #[test]
    fn test_parse_disequality() {
        let input = "fof(neq, axiom, X != Y).\n";
        let file = parse_tptp(input).expect("should parse");
        assert!(matches!(&file.formulas[0].formula, TptpTerm::Neq(_, _)));
    }

    #[test]
    fn test_parse_true_false() {
        let input = "fof(tf, axiom, $true & $false).\n";
        let file = parse_tptp(input).expect("should parse");
        match &file.formulas[0].formula {
            TptpTerm::And(l, r) => {
                assert_eq!(**l, TptpTerm::True);
                assert_eq!(**r, TptpTerm::False);
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_exists() {
        let input = "fof(ex, axiom, ?[X]: p(X)).\n";
        let file = parse_tptp(input).expect("should parse");
        match &file.formulas[0].formula {
            TptpTerm::Exists(vars, _) => {
                assert_eq!(vars, &["X"]);
            }
            other => panic!("expected Exists, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_quoted_name() {
        let input = "fof('my problem', axiom, 'quoted_pred'(a)).\n";
        let file = parse_tptp(input).expect("should parse");
        assert_eq!(file.formulas[0].name, "my problem");
        match &file.formulas[0].formula {
            TptpTerm::Func(name, args) => {
                assert_eq!(name, "quoted_pred");
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected Func, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_nested_formula() {
        let input = "fof(nested, axiom, (p(X) & q(X)) => r(X)).\n";
        let file = parse_tptp(input).expect("should parse");
        assert!(matches!(&file.formulas[0].formula, TptpTerm::Implies(_, _)));
    }

    #[test]
    fn test_parse_multiple_formulas() {
        let input = "\
            fof(ax1, axiom, p(a)).\n\
            fof(ax2, axiom, q(b)).\n\
            fof(goal, conjecture, p(a) & q(b)).\n";
        let file = parse_tptp(input).expect("should parse");
        assert_eq!(file.formulas.len(), 3);
        assert_eq!(file.count_by_role(TptpRole::Axiom), 2);
        assert_eq!(file.count_by_role(TptpRole::Conjecture), 1);
        assert!(file.has_conjectures());
    }

    #[test]
    fn test_parse_tff_type() {
        let input = "tff(sort_decl, type, color: $tType).\n";
        let file = parse_tptp(input).expect("should parse");
        assert_eq!(file.formulas.len(), 1);
        assert_eq!(file.formulas[0].language, TptpLanguage::Tff);
        assert_eq!(file.formulas[0].role, TptpRole::Type);
    }

    #[test]
    fn test_parse_formula_with_annotation() {
        // Some TPTP entries have a source annotation after the formula.
        let input = "fof(ax, axiom, p(a), file('source.ax', ax)).\n";
        let file = parse_tptp(input).expect("should parse");
        assert_eq!(file.formulas.len(), 1);
        assert_eq!(file.formulas[0].name, "ax");
    }

    #[test]
    fn test_parse_function_application() {
        let input = "fof(fn, axiom, f(g(X), h(Y, Z)) = a).\n";
        let file = parse_tptp(input).expect("should parse");
        match &file.formulas[0].formula {
            TptpTerm::Eq(lhs, _rhs) => match lhs.as_ref() {
                TptpTerm::Func(name, args) => {
                    assert_eq!(name, "f");
                    assert_eq!(args.len(), 2);
                }
                other => panic!("expected Func, got {other:?}"),
            },
            other => panic!("expected Eq, got {other:?}"),
        }
    }
}
