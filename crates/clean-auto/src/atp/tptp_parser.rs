// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TPTP FOF/CNF parser.
//!
//! Parses a subset of TPTP syntax sufficient for CASC competition:
//! - `fof(name, role, formula).` declarations
//! - `cnf(name, role, clause).` declarations
//! - Roles: axiom, hypothesis, conjecture, negated_conjecture
//! - Connectives: `&`, `|`, `=>`, `<=>`, `~`
//! - Quantifiers: `!` (forall), `?` (exists)
//! - Equality: `=`, `!=`
//! - Comments: `%` line comments, `/* ... */` block comments
//!
//! Reference: <http://www.tptp.org/TPTP/SyntaxBNF.html>

pub use super::tptp_types::*;

/// Parser state.
struct Parser<'a> {
    input: &'a [u8],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Parser {
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

    fn advance(&mut self) -> Option<u8> {
        let ch = self.input.get(self.pos).copied()?;
        self.pos += 1;
        Some(ch)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            while self.pos < self.input.len() && self.input[self.pos].is_ascii_whitespace() {
                self.pos += 1;
            }
            if self.pos < self.input.len() && self.input[self.pos] == b'%' {
                while self.pos < self.input.len() && self.input[self.pos] != b'\n' {
                    self.pos += 1;
                }
                continue;
            }
            if self.pos + 1 < self.input.len()
                && self.input[self.pos] == b'/'
                && self.input[self.pos + 1] == b'*'
            {
                self.pos += 2;
                while self.pos + 1 < self.input.len()
                    && !(self.input[self.pos] == b'*' && self.input[self.pos + 1] == b'/')
                {
                    self.pos += 1;
                }
                if self.pos + 1 < self.input.len() {
                    self.pos += 2;
                }
                continue;
            }
            break;
        }
    }

    fn expect_char(&mut self, expected: u8) -> Result<(), TptpParseError> {
        self.skip_whitespace_and_comments();
        match self.advance() {
            Some(ch) if ch == expected => Ok(()),
            Some(ch) => Err(TptpParseError::Expected {
                expected: String::from(expected as char),
                found: String::from(ch as char),
                pos: self.pos - 1,
            }),
            None => Err(TptpParseError::UnexpectedEof(self.pos)),
        }
    }

    fn read_lower_word(&mut self) -> Result<String, TptpParseError> {
        self.skip_whitespace_and_comments();
        let start = self.pos;
        if self.peek() == Some(b'\'') {
            self.advance();
            let word_start = self.pos;
            while self.pos < self.input.len() && self.input[self.pos] != b'\'' {
                if self.input[self.pos] == b'\\' {
                    self.pos += 1;
                }
                self.pos += 1;
            }
            let word = std::str::from_utf8(&self.input[word_start..self.pos])
                .unwrap_or("")
                .to_string();
            if self.pos < self.input.len() {
                self.pos += 1;
            }
            return Ok(word);
        }
        if self.at_end() {
            return Err(TptpParseError::UnexpectedEof(self.pos));
        }
        while self.pos < self.input.len()
            && (self.input[self.pos].is_ascii_alphanumeric() || self.input[self.pos] == b'_')
        {
            self.pos += 1;
        }
        if self.pos == start {
            return Err(TptpParseError::UnexpectedChar(
                self.input[start] as char,
                start,
            ));
        }
        Ok(std::str::from_utf8(&self.input[start..self.pos])
            .unwrap_or("")
            .to_string())
    }

    fn read_variable(&mut self) -> Result<String, TptpParseError> {
        self.skip_whitespace_and_comments();
        let start = self.pos;
        if self.at_end() {
            return Err(TptpParseError::UnexpectedEof(self.pos));
        }
        if !self.input[self.pos].is_ascii_uppercase() {
            return Err(TptpParseError::UnexpectedChar(
                self.input[self.pos] as char,
                self.pos,
            ));
        }
        while self.pos < self.input.len()
            && (self.input[self.pos].is_ascii_alphanumeric() || self.input[self.pos] == b'_')
        {
            self.pos += 1;
        }
        Ok(std::str::from_utf8(&self.input[start..self.pos])
            .unwrap_or("")
            .to_string())
    }

    fn read_name(&mut self) -> Result<String, TptpParseError> {
        self.skip_whitespace_and_comments();
        if self.at_end() {
            return Err(TptpParseError::UnexpectedEof(self.pos));
        }
        if self.input[self.pos].is_ascii_digit() {
            let start = self.pos;
            while self.pos < self.input.len() && self.input[self.pos].is_ascii_digit() {
                self.pos += 1;
            }
            return Ok(std::str::from_utf8(&self.input[start..self.pos])
                .unwrap_or("")
                .to_string());
        }
        self.read_lower_word()
    }

    fn parse_role(&mut self) -> Result<TptpRole, TptpParseError> {
        let word = self.read_lower_word()?;
        match word.as_str() {
            "axiom" | "lemma" | "definition" | "type" | "plain" => Ok(TptpRole::Axiom),
            "hypothesis" | "assumption" => Ok(TptpRole::Hypothesis),
            "conjecture" | "theorem" => Ok(TptpRole::Conjecture),
            "negated_conjecture" => Ok(TptpRole::NegatedConjecture),
            other => Ok(TptpRole::Other(other.to_string())),
        }
    }

    fn parse_term(&mut self) -> Result<FofTerm, TptpParseError> {
        self.skip_whitespace_and_comments();
        if self.at_end() {
            return Err(TptpParseError::UnexpectedEof(self.pos));
        }
        let ch = self.input[self.pos];
        if ch.is_ascii_uppercase() {
            return Ok(FofTerm::Var(self.read_variable()?));
        }
        let name = if ch == b'$' {
            self.advance();
            format!("${}", self.read_lower_word()?)
        } else {
            self.read_lower_word()?
        };
        self.skip_whitespace_and_comments();
        if self.peek() == Some(b'(') {
            self.advance();
            let args = self.parse_comma_separated_terms()?;
            self.expect_char(b')')?;
            Ok(FofTerm::Func(name, args))
        } else {
            Ok(FofTerm::Func(name, vec![]))
        }
    }

    fn parse_comma_separated_terms(&mut self) -> Result<Vec<FofTerm>, TptpParseError> {
        let mut args = Vec::new();
        if self.peek() != Some(b')') {
            args.push(self.parse_term()?);
            while {
                self.skip_whitespace_and_comments();
                self.peek() == Some(b',')
            } {
                self.advance();
                args.push(self.parse_term()?);
            }
        }
        Ok(args)
    }

    fn parse_formula(&mut self) -> Result<FofFormula, TptpParseError> {
        self.parse_iff()
    }

    fn parse_iff(&mut self) -> Result<FofFormula, TptpParseError> {
        let mut left = self.parse_implies()?;
        loop {
            self.skip_whitespace_and_comments();
            if self.pos + 2 < self.input.len()
                && self.input[self.pos] == b'<'
                && self.input[self.pos + 1] == b'='
                && self.input[self.pos + 2] == b'>'
            {
                self.pos += 3;
                let right = self.parse_implies()?;
                left = FofFormula::Iff(Box::new(left), Box::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_implies(&mut self) -> Result<FofFormula, TptpParseError> {
        let left = self.parse_or()?;
        self.skip_whitespace_and_comments();
        if self.pos + 1 < self.input.len()
            && self.input[self.pos] == b'='
            && self.input[self.pos + 1] == b'>'
        {
            self.pos += 2;
            let right = self.parse_implies()?;
            Ok(FofFormula::Implies(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    fn parse_or(&mut self) -> Result<FofFormula, TptpParseError> {
        let mut left = self.parse_and()?;
        loop {
            self.skip_whitespace_and_comments();
            if self.peek() == Some(b'|') {
                self.advance();
                left = FofFormula::Or(Box::new(left), Box::new(self.parse_and()?));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<FofFormula, TptpParseError> {
        let mut left = self.parse_unary()?;
        loop {
            self.skip_whitespace_and_comments();
            if self.peek() == Some(b'&') {
                self.advance();
                left = FofFormula::And(Box::new(left), Box::new(self.parse_unary()?));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<FofFormula, TptpParseError> {
        self.skip_whitespace_and_comments();
        if self.at_end() {
            return Err(TptpParseError::UnexpectedEof(self.pos));
        }
        match self.input[self.pos] {
            b'~' => {
                self.advance();
                Ok(FofFormula::Not(Box::new(self.parse_unary()?)))
            }
            b'!' => {
                self.advance();
                self.expect_char(b'[')?;
                let vars = self.parse_var_list()?;
                self.expect_char(b']')?;
                self.expect_char(b':')?;
                Ok(FofFormula::Forall(vars, Box::new(self.parse_unary()?)))
            }
            b'?' => {
                self.advance();
                self.expect_char(b'[')?;
                let vars = self.parse_var_list()?;
                self.expect_char(b']')?;
                self.expect_char(b':')?;
                Ok(FofFormula::Exists(vars, Box::new(self.parse_unary()?)))
            }
            _ => self.parse_atomic(),
        }
    }

    fn parse_var_list(&mut self) -> Result<Vec<String>, TptpParseError> {
        let mut vars = vec![self.read_variable()?];
        while {
            self.skip_whitespace_and_comments();
            self.peek() == Some(b',')
        } {
            self.advance();
            vars.push(self.read_variable()?);
        }
        Ok(vars)
    }

    fn parse_atomic(&mut self) -> Result<FofFormula, TptpParseError> {
        self.skip_whitespace_and_comments();
        if self.at_end() {
            return Err(TptpParseError::UnexpectedEof(self.pos));
        }
        if self.input[self.pos] == b'(' {
            self.advance();
            let f = self.parse_formula()?;
            self.expect_char(b')')?;
            return Ok(f);
        }
        if self.input[self.pos] == b'$' {
            return self.parse_dollar_atom();
        }
        self.parse_term_then_maybe_eq()
    }

    fn parse_dollar_atom(&mut self) -> Result<FofFormula, TptpParseError> {
        self.advance(); // skip $
        let word = self.read_lower_word()?;
        match word.as_str() {
            "true" => Ok(FofFormula::True),
            "false" => Ok(FofFormula::False),
            _ => {
                let name = format!("${word}");
                self.skip_whitespace_and_comments();
                if self.peek() == Some(b'(') {
                    self.advance();
                    let args = self.parse_comma_separated_terms()?;
                    self.expect_char(b')')?;
                    Ok(FofFormula::Predicate(name, args))
                } else {
                    Ok(FofFormula::Predicate(name, vec![]))
                }
            }
        }
    }

    fn parse_term_then_maybe_eq(&mut self) -> Result<FofFormula, TptpParseError> {
        let first_term = self.parse_term()?;
        self.skip_whitespace_and_comments();
        if self.pos + 1 < self.input.len()
            && self.input[self.pos] == b'!'
            && self.input[self.pos + 1] == b'='
        {
            self.pos += 2;
            return Ok(FofFormula::NotEqual(first_term, self.parse_term()?));
        }
        if self.peek() == Some(b'=') && self.input.get(self.pos + 1) != Some(&b'>') {
            self.advance();
            return Ok(FofFormula::Equal(first_term, self.parse_term()?));
        }
        match first_term {
            FofTerm::Func(name, args) => Ok(FofFormula::Predicate(name, args)),
            FofTerm::Var(name) => Ok(FofFormula::Predicate(name, vec![])),
        }
    }

    fn parse_cnf_literal(&mut self) -> Result<FofFormula, TptpParseError> {
        self.skip_whitespace_and_comments();
        if self.peek() == Some(b'~') {
            self.advance();
            Ok(FofFormula::Not(Box::new(self.parse_atomic()?)))
        } else {
            self.parse_atomic()
        }
    }

    fn parse_cnf_clause(&mut self) -> Result<FofFormula, TptpParseError> {
        let mut lit = self.parse_cnf_literal()?;
        while {
            self.skip_whitespace_and_comments();
            self.peek() == Some(b'|')
        } {
            self.advance();
            lit = FofFormula::Or(Box::new(lit), Box::new(self.parse_cnf_literal()?));
        }
        Ok(lit)
    }

    /// Skip an optional annotation section (after formula, before closing paren).
    fn skip_annotation(&mut self) {
        self.skip_whitespace_and_comments();
        if self.peek() != Some(b',') {
            return;
        }
        self.advance();
        let mut depth = 0i32;
        while self.pos < self.input.len() {
            match self.input[self.pos] {
                b'(' | b'[' => depth += 1,
                b')' if depth == 0 => break,
                b')' | b']' => depth -= 1,
                _ => {}
            }
            self.pos += 1;
        }
    }

    /// Parse one `fof(...)` or `cnf(...)` declaration. Returns `None` for
    /// skipped declarations (e.g. `include`).
    fn parse_declaration(&mut self) -> Result<Option<TptpFormula>, TptpParseError> {
        let keyword = self.read_lower_word()?;
        let is_cnf = match keyword.as_str() {
            "fof" => false,
            "cnf" => true,
            "include" => {
                while self.pos < self.input.len() && self.input[self.pos] != b'.' {
                    self.pos += 1;
                }
                if self.pos < self.input.len() {
                    self.pos += 1;
                }
                return Ok(None);
            }
            _ => {
                return Err(TptpParseError::Expected {
                    expected: "fof or cnf".to_string(),
                    found: keyword,
                    pos: self.pos,
                });
            }
        };
        self.expect_char(b'(')?;
        let name = self.read_name()?;
        self.expect_char(b',')?;
        let role = self.parse_role()?;
        self.expect_char(b',')?;
        let formula = if is_cnf {
            self.skip_whitespace_and_comments();
            if self.peek() == Some(b'(') {
                self.advance();
                let clause = self.parse_cnf_clause()?;
                self.expect_char(b')')?;
                clause
            } else {
                self.parse_cnf_clause()?
            }
        } else {
            self.parse_formula()?
        };
        self.skip_annotation();
        self.expect_char(b')')?;
        self.expect_char(b'.')?;
        Ok(Some(TptpFormula {
            _name: name,
            role,
            formula,
            is_cnf,
        }))
    }

    fn parse_problem(&mut self) -> Result<TptpProblem, TptpParseError> {
        let mut formulas = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.at_end() {
                break;
            }
            if let Some(tf) = self.parse_declaration()? {
                formulas.push(tf);
            }
        }
        Ok(TptpProblem { formulas })
    }
}

/// Parse a TPTP problem from a string.
pub fn parse_tptp(input: &str) -> Result<TptpProblem, TptpParseError> {
    let mut parser = Parser::new(input);
    parser.parse_problem()
}
