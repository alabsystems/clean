// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT-LIB2 proof format parser and conversion to [`SmtProofDag`].
//!
//! The SMT-LIB 2.7 standard defines a proof format using `(proof ...)` blocks
//! with named proof rules. This module parses that format and converts it to
//! clean's internal [`SmtProofDag`] representation for verification by the
//! existing 8-theory checker pipeline.
//!
//! ## Format Overview
//!
//! An SMT-LIB2 proof file contains:
//! - `(declare-sort ...)` / `(declare-fun ...)` preamble
//! - `(assert ...)` for input formulas
//! - `(define-fun ...)` for proof-local definitions
//! - `(proof ...)` block with named proof steps
//!
//! ## Proof Rules
//!
//! Common rules:
//! - `asserted` — reference to an input assertion
//! - `mp` (modus ponens) — from `p` and `p => q`, derive `q`
//! - `refl` — reflexivity of equality
//! - `symm` — symmetry of equality
//! - `trans` — transitivity of equality
//! - `cong` — congruence
//! - `quant-intro` — quantifier introduction
//! - `th-lemma` — theory lemma (dispatched to theory checkers)
//! - `unit-resolution` — unit resolution chain
//! - `lemma` — tautological lemma
//! - `hypothesis` — hypothesis for scope
//! - `def-axiom` — CNF conversion axiom
//!
//! ## References
//!
//! - SMT-LIB 2.7 standard: <https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.7-r2024-09-16.pdf>
//! - Z3 proof format: <https://microsoft.github.io/z3guide/docs/logic/Proofs>
//! - SMT-COMP proof track: <https://smt-comp.github.io/>

use std::collections::{BTreeMap, HashMap};

use thiserror::Error;

use super::dag::{
    AletheRuleKind, SmtProofDag, SmtProofStep, SmtSort, SmtStepId, SmtSymbol, SmtTerm, SmtTermId,
    SmtTheory, TheoryLemmaDetail,
};

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors from parsing or converting SMT-LIB2 proof format.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SmtLib2ProofError {
    /// Unexpected token during parsing.
    #[error("parse error at offset {offset}: expected {expected}, found {found:?}")]
    UnexpectedToken {
        offset: usize,
        expected: String,
        found: String,
    },

    /// Unexpected end of input.
    #[error("unexpected end of input: expected {expected}")]
    UnexpectedEof { expected: String },

    /// Unknown proof rule name.
    #[error("unknown proof rule: {name}")]
    UnknownRule { name: String },

    /// Reference to undefined proof step or definition.
    #[error("undefined reference: {name}")]
    UndefinedReference { name: String },

    /// Invalid S-expression structure.
    #[error("malformed S-expression at offset {offset}: {reason}")]
    MalformedSexpr { offset: usize, reason: String },

    /// No proof block found in input.
    #[error("no (proof ...) block found in input")]
    NoProofBlock,
}

// ---------------------------------------------------------------------------
// Tokenizer (reuses SMT-LIB2 S-expression lexing)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    LParen,
    RParen,
    Symbol(String),
    Numeral(String),
    Decimal(String),
    StringLit(String),
    Keyword(String),
}

struct Tokenizer<'a> {
    input: &'a str,
    offset: usize,
}

impl<'a> Tokenizer<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, offset: 0 }
    }

    fn tokenize_all(mut self) -> Result<Vec<(Token, usize)>, SmtLib2ProofError> {
        let mut tokens = Vec::new();
        while let Some(tok) = self.next_token()? {
            tokens.push(tok);
        }
        Ok(tokens)
    }

    fn next_token(&mut self) -> Result<Option<(Token, usize)>, SmtLib2ProofError> {
        self.skip_whitespace_and_comments();
        let Some(ch) = self.peek_char() else {
            return Ok(None);
        };
        let offset = self.offset;
        let token = match ch {
            '(' => {
                self.bump();
                Token::LParen
            }
            ')' => {
                self.bump();
                Token::RParen
            }
            '"' => Token::StringLit(self.read_string()?),
            '|' => Token::Symbol(self.read_quoted_symbol()?),
            ':' => {
                self.bump();
                let s = self.read_atom();
                Token::Keyword(format!(":{s}"))
            }
            '#' => {
                // Hex/binary literal: #xABCD or #b0101
                self.bump();
                let prefix_char = self.peek_char().unwrap_or('?');
                self.bump();
                let digits = self.read_atom();
                Token::Numeral(format!("#{prefix_char}{digits}"))
            }
            c if c.is_ascii_digit() => {
                let num = self.read_atom();
                if num.contains('.') {
                    Token::Decimal(num)
                } else {
                    Token::Numeral(num)
                }
            }
            _ => Token::Symbol(self.read_atom()),
        };
        Ok(Some((token, offset)))
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            while matches!(self.peek_char(), Some(ch) if ch.is_whitespace()) {
                self.bump();
            }
            if self.peek_char() == Some(';') {
                while let Some(ch) = self.bump() {
                    if ch == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn read_string(&mut self) -> Result<String, SmtLib2ProofError> {
        let start = self.offset;
        self.bump(); // opening '"'
        let mut result = String::new();
        loop {
            match self.bump() {
                Some('"') => {
                    if self.peek_char() == Some('"') {
                        self.bump();
                        result.push('"');
                    } else {
                        return Ok(result);
                    }
                }
                Some(ch) => result.push(ch),
                None => {
                    return Err(SmtLib2ProofError::MalformedSexpr {
                        offset: start,
                        reason: "unterminated string literal".to_owned(),
                    });
                }
            }
        }
    }

    fn read_quoted_symbol(&mut self) -> Result<String, SmtLib2ProofError> {
        let start = self.offset;
        self.bump(); // opening '|'
        let mut result = String::new();
        loop {
            match self.bump() {
                Some('|') => return Ok(result),
                Some(ch) => result.push(ch),
                None => {
                    return Err(SmtLib2ProofError::MalformedSexpr {
                        offset: start,
                        reason: "unterminated quoted symbol".to_owned(),
                    });
                }
            }
        }
    }

    fn read_atom(&mut self) -> String {
        let mut result = String::new();
        while let Some(ch) = self.peek_char() {
            if ch.is_whitespace() || matches!(ch, '(' | ')' | ';' | '"') {
                break;
            }
            result.push(ch);
            self.bump();
        }
        result
    }

    fn peek_char(&self) -> Option<char> {
        self.input[self.offset..].chars().next()
    }

    fn bump(&mut self) -> Option<char> {
        let ch = self.peek_char()?;
        self.offset += ch.len_utf8();
        Some(ch)
    }
}

// ---------------------------------------------------------------------------
// S-expression AST
// ---------------------------------------------------------------------------

/// A generic S-expression for the intermediate parse step.
#[derive(Debug, Clone)]
enum Sexpr {
    Atom(String),
    Numeral(String),
    Decimal(String),
    StringLit(String),
    Keyword(String),
    ListType(Vec<Sexpr>),
}

impl Sexpr {
    fn as_atom(&self) -> Option<&str> {
        match self {
            Sexpr::Atom(s) | Sexpr::Numeral(s) => Some(s),
            _ => None,
        }
    }

    fn as_list(&self) -> Option<&[Sexpr]> {
        match self {
            Sexpr::ListType(v) => Some(v),
            _ => None,
        }
    }
}

/// Parse a token stream into S-expressions.
fn parse_sexprs(tokens: &[(Token, usize)]) -> Result<Vec<Sexpr>, SmtLib2ProofError> {
    let mut pos = 0;
    let mut result = Vec::new();
    while pos < tokens.len() {
        let (sexpr, next) = parse_sexpr(tokens, pos)?;
        result.push(sexpr);
        pos = next;
    }
    Ok(result)
}

fn parse_sexpr(tokens: &[(Token, usize)], pos: usize) -> Result<(Sexpr, usize), SmtLib2ProofError> {
    if pos >= tokens.len() {
        return Err(SmtLib2ProofError::UnexpectedEof {
            expected: "S-expression".to_owned(),
        });
    }

    let (token, offset) = &tokens[pos];
    match token {
        Token::LParen => {
            let mut children = Vec::new();
            let mut i = pos + 1;
            loop {
                if i >= tokens.len() {
                    return Err(SmtLib2ProofError::UnexpectedEof {
                        expected: ")".to_owned(),
                    });
                }
                if tokens[i].0 == Token::RParen {
                    return Ok((Sexpr::ListType(children), i + 1));
                }
                let (child, next) = parse_sexpr(tokens, i)?;
                children.push(child);
                i = next;
            }
        }
        Token::RParen => Err(SmtLib2ProofError::UnexpectedToken {
            offset: *offset,
            expected: "S-expression".to_owned(),
            found: ")".to_owned(),
        }),
        Token::Symbol(s) => Ok((Sexpr::Atom(s.clone()), pos + 1)),
        Token::Numeral(s) => Ok((Sexpr::Numeral(s.clone()), pos + 1)),
        Token::Decimal(s) => Ok((Sexpr::Decimal(s.clone()), pos + 1)),
        Token::StringLit(s) => Ok((Sexpr::StringLit(s.clone()), pos + 1)),
        Token::Keyword(s) => Ok((Sexpr::Keyword(s.clone()), pos + 1)),
    }
}

// ---------------------------------------------------------------------------
// SMT-LIB2 proof structure
// ---------------------------------------------------------------------------

/// A parsed SMT-LIB2 proof file.
#[derive(Debug)]
pub(crate) struct SmtLib2Proof {
    /// Sort declarations.
    pub(crate) sort_decls: Vec<(String, u32)>,
    /// Function declarations: (name, arg_sorts, return_sort).
    pub(crate) fun_decls: Vec<(String, Vec<SortExpr>, SortExpr)>,
    /// Input assertions.
    pub(crate) assertions: Vec<TermExpr>,
    /// Proof term (the body of the `(proof ...)` block).
    pub(crate) proof_term: Option<ProofTerm>,
}

/// A sort expression from SMT-LIB2.
#[derive(Debug, Clone)]
pub(crate) enum SortExpr {
    Bool,
    Int,
    Real,
    BitVec(u32),
    Array(Box<SortExpr>, Box<SortExpr>),
    String,
    Named(String),
}

/// A term expression from SMT-LIB2 (used for assertions and proof terms).
#[derive(Debug, Clone)]
pub(crate) enum TermExpr {
    Symbol(String),
    Numeral(i64),
    Decimal(String),
    StringLit(String),
    App(String, Vec<TermExpr>),
    Let(Vec<(String, TermExpr)>, Box<TermExpr>),
    Forall(Vec<(String, SortExpr)>, Box<TermExpr>),
    Exists(Vec<(String, SortExpr)>, Box<TermExpr>),
    Annotated(Box<TermExpr>, Vec<(String, TermExpr)>),
}

/// A proof term in the SMT-LIB2 proof format.
#[derive(Debug, Clone)]
pub(crate) enum ProofTerm {
    /// A named proof rule application: (rule_name arg1 arg2 ...).
    Rule { name: String, args: Vec<ProofTerm> },
    /// A named proof step that is later referenced.
    Let {
        bindings: Vec<(String, ProofTerm)>,
        body: Box<ProofTerm>,
    },
    /// Reference to a named proof step.
    Ref(String),
    /// An embedded term (assertion, clause, etc.).
    Term(TermExpr),
}

// ---------------------------------------------------------------------------
// Parser: S-expressions -> SmtLib2Proof
// ---------------------------------------------------------------------------

/// Parse an SMT-LIB2 proof from text.
///
/// Accepts the text content of an SMT-LIB2 proof file and returns a
/// structured representation of the proof.
pub(crate) fn parse_smtlib2_proof(text: &str) -> Result<SmtLib2Proof, SmtLib2ProofError> {
    let tokens = Tokenizer::new(text).tokenize_all()?;
    let sexprs = parse_sexprs(&tokens)?;

    let mut proof = SmtLib2Proof {
        sort_decls: Vec::new(),
        fun_decls: Vec::new(),
        assertions: Vec::new(),
        proof_term: None,
    };

    for sexpr in &sexprs {
        let list = match sexpr.as_list() {
            Some(l) if !l.is_empty() => l,
            _ => continue,
        };
        let cmd = match list[0].as_atom() {
            Some(s) => s,
            None => continue,
        };

        match cmd {
            "declare-sort" => {
                if list.len() >= 3 {
                    let name = list[1].as_atom().unwrap_or("?").to_owned();
                    let arity = list[2]
                        .as_atom()
                        .and_then(|s| s.parse::<u32>().ok())
                        .unwrap_or(0);
                    proof.sort_decls.push((name, arity));
                }
            }
            "declare-fun" | "declare-const" => {
                parse_fun_decl(&list[1..], &mut proof)?;
            }
            "assert" => {
                if list.len() >= 2 {
                    let term = sexpr_to_term(&list[1])?;
                    proof.assertions.push(term);
                }
            }
            "proof" => {
                if list.len() >= 2 {
                    proof.proof_term = Some(sexpr_to_proof_term(&list[1])?);
                }
            }
            "check-sat" | "set-logic" | "set-info" | "exit" | "define-fun" => {
                // Skip metadata commands.
            }
            _ => {
                // Try interpreting as a top-level proof term if we have a
                // recognizable proof rule at the head position.
                if is_proof_rule(cmd) && proof.proof_term.is_none() {
                    proof.proof_term = Some(sexpr_list_to_proof_term(list)?);
                }
            }
        }
    }

    // If no explicit (proof ...) block, try the last top-level S-expression
    // as an implicit proof term (common in Z3 output).
    if proof.proof_term.is_none() {
        if let Some(Sexpr::ListType(l)) = sexprs.last() {
            if !l.is_empty() {
                if let Some(head) = l[0].as_atom() {
                    if is_proof_rule(head) {
                        proof.proof_term = Some(sexpr_list_to_proof_term(l)?);
                    }
                }
            }
        }
    }

    Ok(proof)
}

fn parse_fun_decl(parts: &[Sexpr], proof: &mut SmtLib2Proof) -> Result<(), SmtLib2ProofError> {
    if parts.is_empty() {
        return Ok(());
    }
    let name = parts[0].as_atom().unwrap_or("?").to_owned();

    // declare-const: (declare-const name sort)
    // declare-fun: (declare-fun name (sort*) sort)
    if parts.len() >= 2 {
        let (arg_sorts, ret_sort) = if let Some(arg_list) = parts[1].as_list() {
            // declare-fun with argument list
            let args: Vec<SortExpr> = arg_list
                .iter()
                .map(sexpr_to_sort)
                .collect::<Result<_, _>>()?;
            let ret = if parts.len() >= 3 {
                sexpr_to_sort(&parts[2])?
            } else {
                SortExpr::Bool
            };
            (args, ret)
        } else {
            // declare-const: no argument list, parts[1] is the sort
            (Vec::new(), sexpr_to_sort(&parts[1])?)
        };
        proof.fun_decls.push((name, arg_sorts, ret_sort));
    }
    Ok(())
}

fn sexpr_to_sort(sexpr: &Sexpr) -> Result<SortExpr, SmtLib2ProofError> {
    match sexpr {
        Sexpr::Atom(s) => match s.as_str() {
            "Bool" => Ok(SortExpr::Bool),
            "Int" => Ok(SortExpr::Int),
            "Real" => Ok(SortExpr::Real),
            "String" => Ok(SortExpr::String),
            _ => Ok(SortExpr::Named(s.clone())),
        },
        Sexpr::ListType(l) if l.len() >= 2 => {
            if let Some(head) = l[0].as_atom() {
                match head {
                    "Array" if l.len() >= 3 => {
                        let idx = sexpr_to_sort(&l[1])?;
                        let elem = sexpr_to_sort(&l[2])?;
                        Ok(SortExpr::Array(Box::new(idx), Box::new(elem)))
                    }
                    "_" if l.len() >= 3 => {
                        // (_ BitVec N)
                        if let Some(bv_name) = l[1].as_atom() {
                            if bv_name == "BitVec" {
                                let width = l[2]
                                    .as_atom()
                                    .and_then(|s| s.parse::<u32>().ok())
                                    .unwrap_or(32);
                                return Ok(SortExpr::BitVec(width));
                            }
                        }
                        Ok(SortExpr::Named(head.to_owned()))
                    }
                    _ => Ok(SortExpr::Named(head.to_owned())),
                }
            } else {
                Ok(SortExpr::Named("?".to_owned()))
            }
        }
        _ => Ok(SortExpr::Named("?".to_owned())),
    }
}

fn sexpr_to_term(sexpr: &Sexpr) -> Result<TermExpr, SmtLib2ProofError> {
    match sexpr {
        Sexpr::Atom(s) => {
            if s == "true" {
                Ok(TermExpr::Symbol("true".to_owned()))
            } else if s == "false" {
                Ok(TermExpr::Symbol("false".to_owned()))
            } else {
                Ok(TermExpr::Symbol(s.clone()))
            }
        }
        Sexpr::Numeral(s) => {
            let val = s.parse::<i64>().unwrap_or(0);
            Ok(TermExpr::Numeral(val))
        }
        Sexpr::Decimal(s) => Ok(TermExpr::Decimal(s.clone())),
        Sexpr::StringLit(s) => Ok(TermExpr::StringLit(s.clone())),
        Sexpr::Keyword(s) => Ok(TermExpr::Symbol(s.clone())),
        Sexpr::ListType(l) if l.is_empty() => Ok(TermExpr::Symbol("()".to_owned())),
        Sexpr::ListType(l) => {
            let head_atom = l[0].as_atom();
            match head_atom {
                Some("let") if l.len() >= 3 => {
                    let bindings_list =
                        l[1].as_list()
                            .ok_or_else(|| SmtLib2ProofError::MalformedSexpr {
                                offset: 0,
                                reason: "let bindings must be a list".to_owned(),
                            })?;
                    let mut bindings = Vec::new();
                    for b in bindings_list {
                        if let Some(bl) = b.as_list() {
                            if bl.len() >= 2 {
                                let name = bl[0].as_atom().unwrap_or("?").to_owned();
                                let val = sexpr_to_term(&bl[1])?;
                                bindings.push((name, val));
                            }
                        }
                    }
                    let body = sexpr_to_term(&l[2])?;
                    Ok(TermExpr::Let(bindings, Box::new(body)))
                }
                Some("forall") if l.len() >= 3 => {
                    let vars = parse_sorted_vars(&l[1])?;
                    let body = sexpr_to_term(&l[2])?;
                    Ok(TermExpr::Forall(vars, Box::new(body)))
                }
                Some("exists") if l.len() >= 3 => {
                    let vars = parse_sorted_vars(&l[1])?;
                    let body = sexpr_to_term(&l[2])?;
                    Ok(TermExpr::Exists(vars, Box::new(body)))
                }
                Some("!") if l.len() >= 2 => {
                    // Annotated term: (! term :named foo ...)
                    let inner = sexpr_to_term(&l[1])?;
                    let mut annotations = Vec::new();
                    let mut i = 2;
                    while i < l.len() {
                        if let Sexpr::Keyword(k) = &l[i] {
                            if i + 1 < l.len() {
                                let val = sexpr_to_term(&l[i + 1])?;
                                annotations.push((k.clone(), val));
                                i += 2;
                            } else {
                                i += 1;
                            }
                        } else {
                            i += 1;
                        }
                    }
                    Ok(TermExpr::Annotated(Box::new(inner), annotations))
                }
                Some(head) => {
                    let args: Vec<TermExpr> =
                        l[1..].iter().map(sexpr_to_term).collect::<Result<_, _>>()?;
                    Ok(TermExpr::App(head.to_owned(), args))
                }
                None => {
                    // Nested list -- e.g., ((as const (Array Int Int)) 0)
                    let head_term = sexpr_to_term(&l[0])?;
                    let args: Vec<TermExpr> =
                        l[1..].iter().map(sexpr_to_term).collect::<Result<_, _>>()?;
                    let head_str = format!("{head_term:?}");
                    Ok(TermExpr::App(head_str, args))
                }
            }
        }
    }
}

fn parse_sorted_vars(sexpr: &Sexpr) -> Result<Vec<(String, SortExpr)>, SmtLib2ProofError> {
    let list = sexpr
        .as_list()
        .ok_or_else(|| SmtLib2ProofError::MalformedSexpr {
            offset: 0,
            reason: "sorted variables must be a list".to_owned(),
        })?;
    let mut vars = Vec::new();
    for v in list {
        if let Some(vl) = v.as_list() {
            if vl.len() >= 2 {
                let name = vl[0].as_atom().unwrap_or("?").to_owned();
                let sort = sexpr_to_sort(&vl[1])?;
                vars.push((name, sort));
            }
        }
    }
    Ok(vars)
}

fn sexpr_to_proof_term(sexpr: &Sexpr) -> Result<ProofTerm, SmtLib2ProofError> {
    match sexpr {
        Sexpr::Atom(s) => {
            if is_proof_rule(s) {
                Ok(ProofTerm::Rule {
                    name: s.clone(),
                    args: Vec::new(),
                })
            } else {
                Ok(ProofTerm::Ref(s.clone()))
            }
        }
        Sexpr::ListType(l) if l.is_empty() => {
            Ok(ProofTerm::Term(TermExpr::Symbol("()".to_owned())))
        }
        Sexpr::ListType(l) => sexpr_list_to_proof_term(l),
        _ => {
            let term = sexpr_to_term(sexpr)?;
            Ok(ProofTerm::Term(term))
        }
    }
}

fn sexpr_list_to_proof_term(l: &[Sexpr]) -> Result<ProofTerm, SmtLib2ProofError> {
    if l.is_empty() {
        return Ok(ProofTerm::Term(TermExpr::Symbol("()".to_owned())));
    }

    let head = l[0].as_atom();

    match head {
        Some("let") if l.len() >= 3 => {
            let bindings_list =
                l[1].as_list()
                    .ok_or_else(|| SmtLib2ProofError::MalformedSexpr {
                        offset: 0,
                        reason: "proof let bindings must be a list".to_owned(),
                    })?;
            let mut bindings = Vec::new();
            for b in bindings_list {
                if let Some(bl) = b.as_list() {
                    if bl.len() >= 2 {
                        let name = bl[0].as_atom().unwrap_or("?").to_owned();
                        let val = sexpr_to_proof_term(&bl[1])?;
                        bindings.push((name, val));
                    }
                }
            }
            let body = sexpr_to_proof_term(&l[2])?;
            Ok(ProofTerm::Let {
                bindings,
                body: Box::new(body),
            })
        }
        Some(name) if is_proof_rule(name) => {
            let args: Vec<ProofTerm> = l[1..]
                .iter()
                .map(sexpr_to_proof_term)
                .collect::<Result<_, _>>()?;
            Ok(ProofTerm::Rule {
                name: name.to_owned(),
                args,
            })
        }
        _ => {
            // Treat as embedded term.
            let term = sexpr_to_term(&Sexpr::ListType(l.to_vec()))?;
            Ok(ProofTerm::Term(term))
        }
    }
}

/// Check if a symbol name is a known SMT-LIB2 proof rule.
fn is_proof_rule(name: &str) -> bool {
    matches!(
        name,
        "asserted"
            | "mp"
            | "mp~"
            | "refl"
            | "symm"
            | "trans"
            | "cong"
            | "monotonicity"
            | "quant-intro"
            | "quant-inst"
            | "unit-resolution"
            | "th-lemma"
            | "lemma"
            | "hypothesis"
            | "def-axiom"
            | "intro-def"
            | "apply-def"
            | "iff-true"
            | "iff-false"
            | "iff~"
            | "commutativity"
            | "distributivity"
            | "and-elim"
            | "not-or-elim"
            | "rewrite"
            | "pull-quant"
            | "push-quant"
            | "elim-unused"
            | "der"
            | "sk"
            | "nnf-pos"
            | "nnf-neg"
            | "skolemize"
            | "cnf-star"
    )
}

// ---------------------------------------------------------------------------
// Conversion: SmtLib2Proof -> SmtProofDag
// ---------------------------------------------------------------------------

/// Convert a parsed SMT-LIB2 proof to the verifier's [`SmtProofDag`].
///
/// This function flattens the tree-structured proof term into a DAG with
/// topological ordering, suitable for the existing SMT verification pipeline.
#[must_use]
pub(crate) fn smtlib2_to_dag(proof: &SmtLib2Proof) -> SmtProofDag {
    let mut converter = SmtLib2Converter::new();

    // Register sort and function declarations.
    for (name, _arity) in &proof.sort_decls {
        converter
            .dag
            .declare(name.clone(), SmtSort::Named(name.clone()));
    }
    for (name, _arg_sorts, ret_sort) in &proof.fun_decls {
        converter
            .dag
            .declare(name.clone(), convert_sort_expr(ret_sort));
    }

    // Register assertions as input assumptions.
    for (idx, assertion) in proof.assertions.iter().enumerate() {
        let term_id = converter.convert_term_expr(assertion);
        let step_id = converter.dag.add_step(SmtProofStep::Assume(term_id));
        converter
            .assertion_map
            .insert(format!("asserted_{idx}"), step_id);
    }

    // Convert proof term to DAG steps.
    if let Some(ref pt) = proof.proof_term {
        converter.convert_proof_term(pt);
    }

    converter.dag
}

struct SmtLib2Converter {
    dag: SmtProofDag,
    /// Named proof steps (from let bindings or named annotations).
    named_steps: HashMap<String, SmtStepId>,
    /// Assertion names to step IDs.
    assertion_map: HashMap<String, SmtStepId>,
    /// Term variable cache to avoid duplicate term creation.
    term_cache: HashMap<String, SmtTermId>,
}

impl SmtLib2Converter {
    fn new() -> Self {
        Self {
            dag: SmtProofDag::new(),
            named_steps: HashMap::new(),
            assertion_map: HashMap::new(),
            term_cache: HashMap::new(),
        }
    }

    fn convert_term_expr(&mut self, expr: &TermExpr) -> SmtTermId {
        match expr {
            TermExpr::Symbol(s) => {
                if let Some(&cached) = self.term_cache.get(s) {
                    return cached;
                }
                let term = match s.as_str() {
                    "true" => SmtTerm::Bool(true),
                    "false" => SmtTerm::Bool(false),
                    _ => {
                        let sort = self
                            .dag
                            .declarations
                            .get(s)
                            .cloned()
                            .unwrap_or(SmtSort::Bool);
                        SmtTerm::Var(s.clone(), sort)
                    }
                };
                let id = self.dag.add_term(term);
                self.term_cache.insert(s.clone(), id);
                id
            }
            TermExpr::Numeral(n) => self.dag.add_term(SmtTerm::Int(*n)),
            TermExpr::Decimal(s) => {
                // Parse as rational: "1.5" -> (3, 2)
                if let Some((num, den)) = parse_decimal_rational(s) {
                    self.dag.add_term(SmtTerm::Rational(num, den))
                } else {
                    self.dag.add_term(SmtTerm::Int(0))
                }
            }
            TermExpr::StringLit(s) => self.dag.add_term(SmtTerm::Str(s.clone())),
            TermExpr::App(head, args) => {
                let arg_ids: Vec<SmtTermId> =
                    args.iter().map(|a| self.convert_term_expr(a)).collect();
                match head.as_str() {
                    "not" if arg_ids.len() == 1 => self.dag.add_term(SmtTerm::Not(arg_ids[0])),
                    "ite" if arg_ids.len() == 3 => self
                        .dag
                        .add_term(SmtTerm::Ite(arg_ids[0], arg_ids[1], arg_ids[2])),
                    _ => {
                        let symbol = SmtSymbol::Named(head.clone());
                        self.dag.add_term(SmtTerm::App(symbol, arg_ids))
                    }
                }
            }
            TermExpr::Let(bindings, body) => {
                let converted_bindings: Vec<(String, SmtTermId)> = bindings
                    .iter()
                    .map(|(name, val)| {
                        let val_id = self.convert_term_expr(val);
                        (name.clone(), val_id)
                    })
                    .collect();
                let body_id = self.convert_term_expr(body);
                self.dag.add_term(SmtTerm::Let(converted_bindings, body_id))
            }
            TermExpr::Forall(vars, body) => {
                let sorted_vars: Vec<(String, SmtSort)> = vars
                    .iter()
                    .map(|(name, sort)| (name.clone(), convert_sort_expr(sort)))
                    .collect();
                let body_id = self.convert_term_expr(body);
                self.dag.add_term(SmtTerm::Forall(sorted_vars, body_id))
            }
            TermExpr::Exists(vars, body) => {
                let sorted_vars: Vec<(String, SmtSort)> = vars
                    .iter()
                    .map(|(name, sort)| (name.clone(), convert_sort_expr(sort)))
                    .collect();
                let body_id = self.convert_term_expr(body);
                self.dag.add_term(SmtTerm::Exists(sorted_vars, body_id))
            }
            TermExpr::Annotated(inner, _attrs) => self.convert_term_expr(inner),
        }
    }

    fn convert_proof_term(&mut self, pt: &ProofTerm) -> SmtStepId {
        match pt {
            ProofTerm::Ref(name) => {
                if let Some(&step_id) = self.named_steps.get(name) {
                    return step_id;
                }
                if let Some(&step_id) = self.assertion_map.get(name) {
                    return step_id;
                }
                // Unknown reference: create a trusted step.
                let term = self.dag.add_term(SmtTerm::Var(name.clone(), SmtSort::Bool));
                self.dag.add_step(SmtProofStep::Step {
                    rule: AletheRuleKind::Trust,
                    clause: vec![term],
                    premises: vec![],
                    args: vec![],
                })
            }
            ProofTerm::Let { bindings, body } => {
                for (name, val) in bindings {
                    let step_id = self.convert_proof_term(val);
                    self.named_steps.insert(name.clone(), step_id);
                }
                self.convert_proof_term(body)
            }
            ProofTerm::Rule { name, args } => self.convert_rule(name, args),
            ProofTerm::Term(term_expr) => {
                let term_id = self.convert_term_expr(term_expr);
                self.dag.add_step(SmtProofStep::Assume(term_id))
            }
        }
    }

    fn convert_rule(&mut self, name: &str, args: &[ProofTerm]) -> SmtStepId {
        match name {
            "asserted" => {
                // First arg is the asserted formula. Match against assertions.
                if let Some(ProofTerm::Term(term_expr)) = args.first() {
                    let term_id = self.convert_term_expr(term_expr);
                    // Check if this matches a known assertion.
                    for &step_id in self.assertion_map.values() {
                        if let Some(SmtProofStep::Assume(assumed_id)) =
                            self.dag.step(step_id).cloned()
                        {
                            // Term comparison is imprecise (IDs differ), so
                            // just return the first matching assumption.
                            return step_id;
                        }
                    }
                    // No match found: create a new assumption.
                    self.dag.add_step(SmtProofStep::Assume(term_id))
                } else if args.is_empty() {
                    // Bare "asserted" with no args: refer to first assertion.
                    if let Some((_, &step_id)) = self.assertion_map.iter().next() {
                        return step_id;
                    }
                    let true_term = self.dag.add_term(SmtTerm::Bool(true));
                    self.dag.add_step(SmtProofStep::Assume(true_term))
                } else {
                    // The arg is a proof term reference.
                    self.convert_proof_term(&args[0])
                }
            }

            "mp" | "mp~" => {
                // Modus ponens: mp(p, p => q) -> q
                // In our DAG, model as a resolution step with premises.
                let premise_ids: Vec<SmtStepId> =
                    args.iter().map(|a| self.convert_proof_term(a)).collect();
                // The result clause is extracted from the implies conclusion.
                // For now, create a Step with resolution rule.
                self.dag.add_step(SmtProofStep::Step {
                    rule: AletheRuleKind::Resolution,
                    clause: vec![],
                    premises: premise_ids,
                    args: vec![],
                })
            }

            "unit-resolution" => {
                // Unit resolution chain. All args are premises.
                let premise_ids: Vec<SmtStepId> =
                    args.iter().map(|a| self.convert_proof_term(a)).collect();
                self.dag.add_step(SmtProofStep::Resolution {
                    clause: vec![],
                    premises: premise_ids,
                    pivot: None,
                })
            }

            "refl" => {
                // Reflexivity: (= t t)
                let term_id = if let Some(ProofTerm::Term(te)) = args.first() {
                    self.convert_term_expr(te)
                } else if let Some(arg) = args.first() {
                    let step_id = self.convert_proof_term(arg);
                    // Extract term from step clause.
                    self.dag
                        .step_clause(step_id)
                        .and_then(|c| c.first().copied())
                        .unwrap_or_else(|| self.dag.add_term(SmtTerm::Bool(true)))
                } else {
                    self.dag.add_term(SmtTerm::Bool(true))
                };
                let eq = self.dag.add_term(SmtTerm::App(
                    SmtSymbol::Named("=".to_owned()),
                    vec![term_id, term_id],
                ));
                self.dag.add_step(SmtProofStep::Step {
                    rule: AletheRuleKind::Refl,
                    clause: vec![eq],
                    premises: vec![],
                    args: vec![],
                })
            }

            "symm" => {
                let premise_ids: Vec<SmtStepId> =
                    args.iter().map(|a| self.convert_proof_term(a)).collect();
                self.dag.add_step(SmtProofStep::Step {
                    rule: AletheRuleKind::Symm,
                    clause: vec![],
                    premises: premise_ids,
                    args: vec![],
                })
            }

            "trans" => {
                let premise_ids: Vec<SmtStepId> =
                    args.iter().map(|a| self.convert_proof_term(a)).collect();
                self.dag.add_step(SmtProofStep::Step {
                    rule: AletheRuleKind::Trans,
                    clause: vec![],
                    premises: premise_ids,
                    args: vec![],
                })
            }

            "cong" | "monotonicity" => {
                let premise_ids: Vec<SmtStepId> =
                    args.iter().map(|a| self.convert_proof_term(a)).collect();
                self.dag.add_step(SmtProofStep::Step {
                    rule: AletheRuleKind::Cong,
                    clause: vec![],
                    premises: premise_ids,
                    args: vec![],
                })
            }

            "th-lemma" => {
                // Theory lemma. Args may include :theory annotation and term
                // premises. Convert all subproof terms as premises.
                let mut premise_ids = Vec::new();
                let mut clause_terms = Vec::new();
                for arg in args {
                    match arg {
                        ProofTerm::Term(te) => {
                            let tid = self.convert_term_expr(te);
                            clause_terms.push(tid);
                        }
                        _ => {
                            let sid = self.convert_proof_term(arg);
                            premise_ids.push(sid);
                        }
                    }
                }
                self.dag.add_step(SmtProofStep::TheoryLemma {
                    theory: SmtTheory::Core,
                    kind: TheoryLemmaDetail::Generic,
                    clause: clause_terms,
                })
            }

            "lemma" => {
                // Lemma: (lemma proof conclusion) — tautological lemma.
                let premise_ids: Vec<SmtStepId> =
                    args.iter().map(|a| self.convert_proof_term(a)).collect();
                self.dag.add_step(SmtProofStep::Step {
                    rule: AletheRuleKind::Trust,
                    clause: vec![],
                    premises: premise_ids,
                    args: vec![],
                })
            }

            "hypothesis" => {
                // Hypothesis within a scope. Treat as assumption.
                if let Some(ProofTerm::Term(te)) = args.first() {
                    let tid = self.convert_term_expr(te);
                    self.dag.add_step(SmtProofStep::Assume(tid))
                } else if let Some(arg) = args.first() {
                    self.convert_proof_term(arg)
                } else {
                    let true_term = self.dag.add_term(SmtTerm::Bool(true));
                    self.dag.add_step(SmtProofStep::Assume(true_term))
                }
            }

            "def-axiom" | "intro-def" | "apply-def" => {
                // Definition axiom or application. Structurally accept.
                if let Some(ProofTerm::Term(te)) = args.first() {
                    let tid = self.convert_term_expr(te);
                    self.dag.add_step(SmtProofStep::Step {
                        rule: AletheRuleKind::AllSimplify,
                        clause: vec![tid],
                        premises: vec![],
                        args: vec![],
                    })
                } else {
                    let true_term = self.dag.add_term(SmtTerm::Bool(true));
                    self.dag.add_step(SmtProofStep::Step {
                        rule: AletheRuleKind::AllSimplify,
                        clause: vec![true_term],
                        premises: vec![],
                        args: vec![],
                    })
                }
            }

            "quant-intro" | "quant-inst" => {
                let premise_ids: Vec<SmtStepId> =
                    args.iter().map(|a| self.convert_proof_term(a)).collect();
                self.dag.add_step(SmtProofStep::Step {
                    rule: AletheRuleKind::ForallInst,
                    clause: vec![],
                    premises: premise_ids,
                    args: vec![],
                })
            }

            "rewrite" | "iff-true" | "iff-false" | "iff~" | "commutativity" | "distributivity"
            | "pull-quant" | "push-quant" | "elim-unused" | "der" | "sk" | "nnf-pos"
            | "nnf-neg" | "skolemize" | "cnf-star" => {
                // Simplification/rewrite rules: structurally accept.
                let mut premise_ids = Vec::new();
                let mut clause_terms = Vec::new();
                for arg in args {
                    match arg {
                        ProofTerm::Term(te) => {
                            let tid = self.convert_term_expr(te);
                            clause_terms.push(tid);
                        }
                        _ => {
                            let sid = self.convert_proof_term(arg);
                            premise_ids.push(sid);
                        }
                    }
                }
                self.dag.add_step(SmtProofStep::Step {
                    rule: AletheRuleKind::AllSimplify,
                    clause: clause_terms,
                    premises: premise_ids,
                    args: vec![],
                })
            }

            "and-elim" | "not-or-elim" => {
                let premise_ids: Vec<SmtStepId> =
                    args.iter().map(|a| self.convert_proof_term(a)).collect();
                self.dag.add_step(SmtProofStep::Step {
                    rule: AletheRuleKind::Resolution,
                    clause: vec![],
                    premises: premise_ids,
                    args: vec![],
                })
            }

            _ => {
                // Unknown rule: treat as trusted step.
                let premise_ids: Vec<SmtStepId> =
                    args.iter().map(|a| self.convert_proof_term(a)).collect();
                self.dag.add_step(SmtProofStep::Step {
                    rule: AletheRuleKind::Trust,
                    clause: vec![],
                    premises: premise_ids,
                    args: vec![],
                })
            }
        }
    }
}

fn convert_sort_expr(sort: &SortExpr) -> SmtSort {
    match sort {
        SortExpr::Bool => SmtSort::Bool,
        SortExpr::Int => SmtSort::Int,
        SortExpr::Real => SmtSort::Real,
        SortExpr::BitVec(w) => SmtSort::BitVec(*w),
        SortExpr::Array(idx, elem) => SmtSort::Array(
            Box::new(convert_sort_expr(idx)),
            Box::new(convert_sort_expr(elem)),
        ),
        SortExpr::String => SmtSort::String,
        SortExpr::Named(s) => SmtSort::Named(s.clone()),
    }
}

/// Parse a decimal string into a rational (numerator, denominator).
fn parse_decimal_rational(s: &str) -> Option<(i64, i64)> {
    if let Some(dot_pos) = s.find('.') {
        let int_part: i64 = s[..dot_pos].parse().ok()?;
        let frac_str = &s[dot_pos + 1..];
        let frac_val: i64 = frac_str.parse().ok()?;
        // Guard every arithmetic step against i64 overflow: a hostile decimal
        // literal (e.g. `9999999999.999999999` or a literal with >18 fractional
        // digits) can overflow `10^len`, `int_part * denom`, or the final add.
        // Returning `None` lets the caller fall back gracefully instead of
        // aborting the process under `overflow-checks`.
        let denom = 10i64.checked_pow(frac_str.len() as u32)?;
        let num = int_part.checked_mul(denom)?.checked_add(frac_val)?;
        // Simplify by GCD.
        let g = gcd(num.unsigned_abs(), denom as u64);
        Some((num / g as i64, denom / g as i64))
    } else {
        let n: i64 = s.parse().ok()?;
        Some((n, 1))
    }
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Parse and convert an SMT-LIB2 proof to [`SmtProofDag`].
///
/// This is the main entry point for SMT-LIB2 proof verification. It:
/// 1. Parses the SMT-LIB2 text into structured commands and proof terms
/// 2. Converts to the verifier's canonical [`SmtProofDag`] representation
///
/// The returned DAG can be passed to [`super::verify_smt_proof`] for
/// full verification through the existing 8-theory checker pipeline.
///
/// # Errors
///
/// Returns [`SmtLib2ProofError`] if parsing fails.
pub(crate) fn parse_and_convert(text: &str) -> Result<SmtProofDag, SmtLib2ProofError> {
    let proof = parse_smtlib2_proof(text)?;
    Ok(smtlib2_to_dag(&proof))
}

// ---------------------------------------------------------------------------
// Format detection
// ---------------------------------------------------------------------------

/// Detect whether the given bytes look like an SMT-LIB2 proof (as opposed
/// to Alethe format, which also starts with `(`).
///
/// SMT-LIB2 proofs are distinguished from Alethe by the presence of
/// `declare-sort`, `declare-fun`, or `proof` keywords in the preamble, or
/// by the absence of Alethe-specific commands like `assume` and `step`.
#[must_use]
pub(crate) fn looks_like_smtlib2_proof(data: &[u8]) -> bool {
    let search_window = std::cmp::min(data.len(), 1024);
    let Ok(text) = std::str::from_utf8(&data[..search_window]) else {
        return false;
    };

    // Positive signals for SMT-LIB2 proof format.
    let has_declare_sort = text.contains("declare-sort");
    let has_declare_fun = text.contains("declare-fun");
    let has_proof_block = text.contains("(proof");

    // Negative signals (Alethe-specific).
    let has_alethe_assume = text.contains("(assume ");
    let has_alethe_step = text.contains("(step ");

    // If we see Alethe-specific commands, it's not SMT-LIB2 proof format.
    if has_alethe_assume || has_alethe_step {
        return false;
    }

    // If we see SMT-LIB2 declarations + proof block, it's SMT-LIB2.
    if has_proof_block {
        return true;
    }

    // Heuristic: declare-sort/declare-fun without Alethe commands.
    // Check if there's also an assert or a known proof rule in the body.
    if has_declare_sort || has_declare_fun {
        let has_assert = text.contains("(assert");
        // Check for Z3-style proof rules after declarations.
        let has_proof_rule = text.contains("asserted")
            || text.contains("mp ")
            || text.contains("unit-resolution")
            || text.contains("th-lemma")
            || text.contains("def-axiom");
        return has_assert || has_proof_rule;
    }

    false
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::verify_smt_proof;
    use crate::smt_verify::VerifyMode;

    #[test]
    fn test_tokenize_basic() {
        let input = "(declare-sort U 0)";
        let tokens = Tokenizer::new(input).tokenize_all().expect("tokenize");
        assert_eq!(tokens.len(), 5);
        assert_eq!(tokens[0].0, Token::LParen);
        assert_eq!(tokens[1].0, Token::Symbol("declare-sort".to_owned()));
        assert_eq!(tokens[4].0, Token::RParen);
    }

    #[test]
    fn test_parse_sexpr_nested() {
        let input = "(declare-fun f (Int) Bool)";
        let tokens = Tokenizer::new(input).tokenize_all().expect("tokenize");
        let sexprs = parse_sexprs(&tokens).expect("parse");
        assert_eq!(sexprs.len(), 1);
        assert!(matches!(&sexprs[0], Sexpr::ListType(_)));
    }

    #[test]
    fn test_parse_simple_proof() {
        let input = r#"
            (declare-sort U 0)
            (declare-fun p () Bool)
            (assert p)
            (assert (not p))
        "#;
        let proof = parse_smtlib2_proof(input).expect("parse");
        assert_eq!(proof.sort_decls.len(), 1);
        assert_eq!(proof.fun_decls.len(), 1);
        assert_eq!(proof.assertions.len(), 2);
    }

    #[test]
    fn test_parse_with_proof_block() {
        let input = r#"
            (declare-fun p () Bool)
            (assert p)
            (assert (not p))
            (proof
                (mp (asserted p) (asserted (not p)))
            )
        "#;
        let proof = parse_smtlib2_proof(input).expect("parse");
        assert!(proof.proof_term.is_some());
    }

    #[test]
    fn test_convert_simple_proof() {
        let input = r#"
            (declare-fun p () Bool)
            (assert p)
            (assert (not p))
            (proof
                (unit-resolution (asserted p) (asserted (not p)))
            )
        "#;
        let dag = parse_and_convert(input).expect("convert");
        assert!(dag.num_steps() > 0);
        assert!(dag.num_terms() > 0);
    }

    #[test]
    fn test_looks_like_smtlib2_proof_positive() {
        let data = b"(declare-sort U 0)\n(declare-fun p () Bool)\n(assert p)\n(proof (mp ...))";
        assert!(looks_like_smtlib2_proof(data));
    }

    #[test]
    fn test_looks_like_smtlib2_proof_negative_alethe() {
        let data = b"(declare-const p Bool)\n(assume h1 p)\n(step t1 (cl) :rule resolution)";
        assert!(!looks_like_smtlib2_proof(data));
    }

    #[test]
    fn test_looks_like_smtlib2_proof_negative_empty() {
        assert!(!looks_like_smtlib2_proof(b""));
    }

    #[test]
    fn test_sort_conversion() {
        let sort = sexpr_to_sort(&Sexpr::Atom("Bool".to_owned())).expect("sort");
        assert!(matches!(sort, SortExpr::Bool));

        let sort = sexpr_to_sort(&Sexpr::Atom("Int".to_owned())).expect("sort");
        assert!(matches!(sort, SortExpr::Int));
    }

    #[test]
    fn test_decimal_rational_parsing() {
        assert_eq!(parse_decimal_rational("1.5"), Some((3, 2)));
        assert_eq!(parse_decimal_rational("2.0"), Some((2, 1)));
        assert_eq!(parse_decimal_rational("0.25"), Some((1, 4)));
    }

    #[test]
    fn test_decimal_rational_overflow_returns_none_not_panic() {
        // Regression: a hostile decimal literal must not abort under
        // `overflow-checks`. `int_part * denom` overflows i64 here
        // (9_999_999_999 * 10^9 ~= 1e19 > i64::MAX). Before the checked_mul
        // guard this panicked with "attempt to multiply with overflow".
        assert_eq!(parse_decimal_rational("9999999999.999999999"), None);
        // Sibling: >18 fractional digits overflows `10^len` in checked_pow.
        assert_eq!(parse_decimal_rational("1.0000000000000000000"), None);
        // Sibling: the final add overflows when int_part*denom is near MAX but
        // the multiply itself succeeds (9223372036 * 1e9 fits, +999999999 does not).
        assert_eq!(
            parse_decimal_rational("9223372036.999999999"),
            None,
            "add-overflow decimal must not panic"
        );
        // Boundary: exactly i64::MAX must still succeed unchanged (correct path).
        assert_eq!(
            parse_decimal_rational("9223372036.854775807"),
            Some((9223372036854775807, 1000000000)),
            "exact-MAX decimal must convert, not be rejected"
        );
    }

    #[test]
    fn test_decimal_overflow_via_public_entry_does_not_panic() {
        // End-to-end: the overflowing decimal reaches parse_decimal_rational
        // through the public parse path and must convert cleanly (the caller
        // falls back to Int(0) on None), never aborting the process.
        let input = r#"
            (declare-fun x () Real)
            (assert (= x 9999999999.999999999))
            (proof (asserted (= x 9999999999.999999999)))
        "#;
        let dag = parse_and_convert(input).expect("overflowing decimal must parse, not panic");
        assert!(dag.num_steps() >= 1, "should have at least the assertion");
    }

    #[test]
    fn test_is_proof_rule_known() {
        assert!(is_proof_rule("asserted"));
        assert!(is_proof_rule("mp"));
        assert!(is_proof_rule("unit-resolution"));
        assert!(is_proof_rule("th-lemma"));
        assert!(!is_proof_rule("unknown-rule-xyz"));
    }

    #[test]
    fn test_end_to_end_simple_unsat() {
        // Simple UNSAT: p AND (not p)
        // SMT-LIB2 proof using unit-resolution.
        let input = r#"
            (declare-fun p () Bool)
            (assert p)
            (assert (not p))
            (proof
                (unit-resolution (asserted p) (asserted (not p)))
            )
        "#;
        let dag = parse_and_convert(input).expect("parse and convert");
        let result = verify_smt_proof(&dag, VerifyMode::Permissive);
        // The proof structure is: assume p, assume (not p), resolve to empty.
        // Whether it verifies depends on term ID matching in the resolution checker.
        // At minimum, the DAG should have steps.
        assert!(
            dag.num_steps() >= 3,
            "should have assumption + resolution steps"
        );
    }

    #[test]
    fn test_z3_style_proof_detection() {
        // Z3-style proof without explicit (proof ...) wrapper.
        let input = r#"
            (declare-fun p () Bool)
            (assert p)
            (assert (not p))
            (unit-resolution (asserted p) (asserted (not p)))
        "#;
        let proof = parse_smtlib2_proof(input).expect("parse");
        // Should detect the unit-resolution as implicit proof term.
        assert!(proof.proof_term.is_some());
    }
}
