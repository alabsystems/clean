// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared SMT certificate to clean proof replay bridge.
//!
//! Provides a common SMT-LIB AST representation used by all program
//! verification importers that produce SMT verification conditions. The
//! bridge translates SMT sorts and terms into clean kernel `Expr` types
//! for downstream type checking and trust tracking.
//!
//! Importers that use this bridge: Dafny (Boogie → Z3), Why3 (WhyML → SMT),
//! PVS (PVS → Yices/Z3), KeY/Frama-C/SPARK (JML/ACSL/SPARK → SMT).

use clean_kernel::{Expr, Level, Name};

use super::cert_replay::Certificate;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from SMT bridge operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SmtBridgeError {
    /// Failed to parse an SMT-LIB expression.
    #[error("SMT parse error: {reason}")]
    ParseError { reason: String },

    /// The SMT logic is not supported for clean translation.
    #[error("unsupported SMT logic: {logic}")]
    UnsupportedLogic { logic: String },

    /// Translation from SMT to clean failed.
    #[error("SMT-to-clean translation failed: {reason}")]
    TranslationFailed { reason: String },
}

// ---------------------------------------------------------------------------
// SMT sorts
// ---------------------------------------------------------------------------

/// SMT-LIB sort (type) representation.
///
/// Covers the core SMT-LIB2 theory sorts used by program verification tools.
/// Higher-order sorts and parametric datatypes are represented as
/// `Uninterpreted` with the sort name for forward compatibility.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SmtSort {
    /// Boolean sort.
    Bool,
    /// Mathematical integer sort.
    Int,
    /// Real number sort.
    Real,
    /// Fixed-width bitvector sort.
    BitVec(u32),
    /// Array sort with index and element sorts.
    Array(Box<SmtSort>, Box<SmtSort>),
    /// Uninterpreted (user-defined) sort.
    Uninterpreted(String),
}

impl SmtSort {
    /// Convenience constructor for `Array` sort.
    #[must_use]
    pub fn array(index: SmtSort, element: SmtSort) -> Self {
        Self::Array(Box::new(index), Box::new(element))
    }

    /// Convenience constructor for `Uninterpreted` sort.
    #[must_use]
    pub fn uninterpreted(name: impl Into<String>) -> Self {
        Self::Uninterpreted(name.into())
    }
}

// ---------------------------------------------------------------------------
// SMT terms
// ---------------------------------------------------------------------------

/// Quantifier kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Quantifier {
    /// Universal quantification.
    ForAll,
    /// Existential quantification.
    Exists,
}

/// SMT literal value.
#[derive(Clone, Debug, PartialEq)]
#[non_exhaustive]
pub enum SmtLiteral {
    /// Boolean literal.
    Bool(bool),
    /// Integer literal.
    Int(i64),
    /// Real literal (approximated as f64 for transport; exact rationals
    /// should be encoded as `App("/_", [Int(num), Int(den)])` in the
    /// full pipeline).
    Real(f64),
    /// Bitvector literal with value and width.
    BitVec(u64, u32),
    /// String literal.
    String(String),
}

/// SMT-LIB term (expression) representation.
///
/// This is an intermediate AST used to carry verification conditions from
/// program verification tools before translation to clean `Expr`.
#[derive(Clone, Debug, PartialEq)]
#[non_exhaustive]
pub enum SmtTerm {
    /// Variable reference.
    Var(String),
    /// Literal constant.
    Literal(SmtLiteral),
    /// Function/operator application.
    App(String, Vec<SmtTerm>),
    /// Let binding: `(let ((x e1) (y e2)) body)`.
    Let(Vec<(String, SmtTerm)>, Box<SmtTerm>),
    /// Quantified formula.
    Quant(Quantifier, Vec<(String, SmtSort)>, Box<SmtTerm>),
}

impl SmtTerm {
    /// Create a boolean literal term.
    #[must_use]
    pub fn bool_(value: bool) -> Self {
        Self::Literal(SmtLiteral::Bool(value))
    }

    /// Create an integer literal term.
    #[must_use]
    pub fn int(value: i64) -> Self {
        Self::Literal(SmtLiteral::Int(value))
    }

    /// Create a variable reference term.
    #[must_use]
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into())
    }

    /// Create a function application term.
    #[must_use]
    pub fn app(name: impl Into<String>, args: Vec<SmtTerm>) -> Self {
        Self::App(name.into(), args)
    }
}

// ---------------------------------------------------------------------------
// Assertion and VC bundle
// ---------------------------------------------------------------------------

/// A single named SMT assertion (verification condition clause).
#[derive(Clone, Debug)]
pub struct SmtAssertion {
    /// Optional name (from `(assert (! ... :named <name>))` in SMT-LIB).
    pub name: Option<String>,
    /// The asserted term.
    pub term: SmtTerm,
    /// Source line number in the original program, if known.
    pub source_line: Option<u32>,
}

/// A bundle of SMT verification conditions with optional proof certificate.
///
/// Represents the complete output of a program verification tool's VC
/// generation phase: the SMT logic, declared sorts, verification condition
/// assertions, and the (optional) proof certificate from the solver.
#[derive(Clone, Debug)]
pub struct SmtVcBundle {
    /// SMT-LIB logic string (e.g. "QF_LIA", "AUFBV", "ALL").
    pub logic: String,
    /// Sort declarations (uninterpreted sorts used in the VCs).
    pub sorts: Vec<SmtSort>,
    /// Verification condition assertions.
    pub assertions: Vec<SmtAssertion>,
    /// Proof certificate from the SMT solver, if available.
    pub certificate: Option<Certificate>,
}

impl SmtVcBundle {
    /// Create a new VC bundle with the given logic.
    #[must_use]
    pub fn new(logic: impl Into<String>) -> Self {
        Self {
            logic: logic.into(),
            sorts: Vec::new(),
            assertions: Vec::new(),
            certificate: None,
        }
    }

    /// Builder: add a sort declaration.
    #[must_use]
    pub fn with_sort(mut self, sort: SmtSort) -> Self {
        self.sorts.push(sort);
        self
    }

    /// Builder: add a verification condition assertion.
    #[must_use]
    pub fn with_assertion(mut self, assertion: SmtAssertion) -> Self {
        self.assertions.push(assertion);
        self
    }

    /// Builder: attach a proof certificate.
    #[must_use]
    pub fn with_certificate(mut self, cert: Certificate) -> Self {
        self.certificate = Some(cert);
        self
    }

    /// Number of verification condition assertions in this bundle.
    #[must_use]
    pub fn assertion_count(&self) -> usize {
        self.assertions.len()
    }
}

// ---------------------------------------------------------------------------
// Sort translation
// ---------------------------------------------------------------------------

/// Translate an SMT sort to a clean kernel `Expr` type.
///
/// Maps SMT-LIB sorts to their clean/Mathlib counterparts:
/// - `Bool` → `Prop`
/// - `Int` → `Int` (the Lean integer type)
/// - `Real` → `Real` (requires Mathlib)
/// - `BitVec(n)` → `BitVec n` (applied constant)
/// - `Array(I, E)` → `I → E` (function type / arrow)
/// - `Uninterpreted(name)` → opaque constant reference
///
/// # Errors
///
/// Returns `SmtBridgeError::TranslationFailed` for sort patterns that cannot
/// be represented in the clean kernel type system (currently: none, but
/// reserved for future extensions like dependent sorts).
pub fn translate_smt_sort_to_clean(sort: &SmtSort) -> Result<Expr, SmtBridgeError> {
    match sort {
        SmtSort::Bool => Ok(Expr::prop()),

        SmtSort::Int => Ok(Expr::const_str("Int")),

        SmtSort::Real => Ok(Expr::const_str("Real")),

        SmtSort::BitVec(width) => {
            let bv_const = Expr::const_str("BitVec");
            // BitVec is a function Nat → Type; apply it to the width literal.
            let width_lit = Expr::nat_lit(u64::from(*width));
            Ok(Expr::app(bv_const, width_lit))
        }

        SmtSort::Array(index_sort, elem_sort) => {
            let index_ty = translate_smt_sort_to_clean(index_sort)?;
            let elem_ty = translate_smt_sort_to_clean(elem_sort)?;
            Ok(Expr::arrow(index_ty, elem_ty))
        }

        SmtSort::Uninterpreted(name) => {
            Ok(Expr::const_(Name::from_string(name), Vec::<Level>::new()))
        }
    }
}

// ---------------------------------------------------------------------------
// SMT-LIB2 sort parser
// ---------------------------------------------------------------------------

/// Parse an SMT-LIB2 sort expression from a string.
///
/// Supports the following sort syntax:
/// - `Bool`, `Int`, `Real` — base sorts
/// - `(_ BitVec N)` — bitvector sort with width N
/// - `(Array S1 S2)` — array sort with index and element sorts
/// - `<identifier>` — uninterpreted sort
///
/// # Examples
///
/// ```text
/// parse_smtlib2_sort("Int") => Ok(SmtSort::Int)
/// parse_smtlib2_sort("(Array Int Bool)") => Ok(SmtSort::Array(Int, Bool))
/// parse_smtlib2_sort("(_ BitVec 32)") => Ok(SmtSort::BitVec(32))
/// ```
///
/// # Errors
///
/// Returns `SmtBridgeError::ParseError` if the input is not a valid sort.
pub fn parse_smtlib2_sort(input: &str) -> Result<SmtSort, SmtBridgeError> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Err(SmtBridgeError::ParseError {
            reason: "empty sort expression".to_string(),
        });
    }

    // Base sorts.
    match trimmed {
        "Bool" => return Ok(SmtSort::Bool),
        "Int" => return Ok(SmtSort::Int),
        "Real" => return Ok(SmtSort::Real),
        _ => {}
    }

    // Parenthesized sorts.
    if trimmed.starts_with('(') {
        if !trimmed.ends_with(')') {
            return Err(SmtBridgeError::ParseError {
                reason: format!("unmatched parenthesis in sort: {trimmed}"),
            });
        }
        let inner = &trimmed[1..trimmed.len() - 1].trim();
        return parse_compound_sort(inner);
    }

    // Uninterpreted sort (bare identifier).
    if is_valid_smt_identifier(trimmed) {
        return Ok(SmtSort::Uninterpreted(trimmed.to_string()));
    }

    Err(SmtBridgeError::ParseError {
        reason: format!("invalid sort expression: {trimmed}"),
    })
}

/// Parse a compound (parenthesized) sort expression.
fn parse_compound_sort(inner: &str) -> Result<SmtSort, SmtBridgeError> {
    // BitVec: `_ BitVec N`
    if let Some(rest) = inner.strip_prefix("_ BitVec") {
        let width_str = rest.trim();
        let width: u32 = width_str.parse().map_err(|_| SmtBridgeError::ParseError {
            reason: format!("invalid BitVec width: {width_str}"),
        })?;
        return Ok(SmtSort::BitVec(width));
    }

    // Array: `Array S1 S2`
    if let Some(rest) = inner.strip_prefix("Array") {
        let rest = rest.trim();
        let (s1_str, s2_str) = split_smt_args(rest)?;
        let s1 = parse_smtlib2_sort(&s1_str)?;
        let s2 = parse_smtlib2_sort(&s2_str)?;
        return Ok(SmtSort::array(s1, s2));
    }

    Err(SmtBridgeError::ParseError {
        reason: format!("unknown compound sort: ({inner})"),
    })
}

/// Split a string into two top-level SMT-LIB arguments, respecting nested
/// parentheses.
fn split_smt_args(input: &str) -> Result<(String, String), SmtBridgeError> {
    let trimmed = input.trim();
    let mut depth = 0i32;
    let mut split_pos = None;

    for (i, ch) in trimmed.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ' ' | '\t' | '\n' if depth == 0 && split_pos.is_none() => {
                // First top-level whitespace after the first argument.
                // But we need to skip leading whitespace of the first arg.
                let first = trimmed[..i].trim();
                if !first.is_empty() {
                    split_pos = Some(i);
                }
            }
            _ => {}
        }
    }

    let pos = split_pos.ok_or_else(|| SmtBridgeError::ParseError {
        reason: format!("expected two sort arguments, got: {trimmed}"),
    })?;

    let first = trimmed[..pos].trim().to_string();
    let second = trimmed[pos..].trim().to_string();

    if second.is_empty() {
        return Err(SmtBridgeError::ParseError {
            reason: format!("expected two sort arguments, got: {trimmed}"),
        });
    }

    Ok((first, second))
}

/// Check if a string is a valid SMT-LIB identifier (simple symbol).
fn is_valid_smt_identifier(s: &str) -> bool {
    !s.is_empty()
        && !s.starts_with(|c: char| c.is_ascii_digit())
        && s.chars().all(|c| {
            c.is_alphanumeric() || c == '_' || c == '.' || c == '-' || c == '!' || c == '\''
        })
}

// ---------------------------------------------------------------------------
// SMT-LIB2 term parser
// ---------------------------------------------------------------------------

/// Parse an SMT-LIB2 term expression from a string.
///
/// Supports the following term syntax:
/// - `true`, `false` — boolean literals
/// - `<integer>` — integer literals (including negative with `-`)
/// - `<identifier>` — variable references
/// - `(<op> <args>...)` — function application
/// - `(let ((<var> <term>)...) <body>)` — let bindings
/// - `(forall ((<var> <sort>)...) <body>)` — universal quantification
/// - `(exists ((<var> <sort>)...) <body>)` — existential quantification
///
/// # Examples
///
/// ```text
/// parse_smtlib2_term("true") => Ok(SmtTerm::Literal(SmtLiteral::Bool(true)))
/// parse_smtlib2_term("(and (= x 1) (> y 0))") => Ok(SmtTerm::App("and", [...]))
/// ```
///
/// # Errors
///
/// Returns `SmtBridgeError::ParseError` if the input is not a valid term.
pub fn parse_smtlib2_term(input: &str) -> Result<SmtTerm, SmtBridgeError> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Err(SmtBridgeError::ParseError {
            reason: "empty term expression".to_string(),
        });
    }

    // Boolean literals.
    if trimmed == "true" {
        return Ok(SmtTerm::bool_(true));
    }
    if trimmed == "false" {
        return Ok(SmtTerm::bool_(false));
    }

    // Integer literals (including negative).
    if let Ok(n) = trimmed.parse::<i64>() {
        return Ok(SmtTerm::int(n));
    }

    // Parenthesized expressions.
    if trimmed.starts_with('(') {
        if !trimmed.ends_with(')') {
            return Err(SmtBridgeError::ParseError {
                reason: format!("unmatched parenthesis in term: {trimmed}"),
            });
        }
        let inner = trimmed[1..trimmed.len() - 1].trim();
        return parse_compound_term(inner);
    }

    // Variable reference.
    if is_valid_smt_identifier(trimmed) {
        return Ok(SmtTerm::var(trimmed));
    }

    Err(SmtBridgeError::ParseError {
        reason: format!("invalid term expression: {trimmed}"),
    })
}

/// Parse a compound (parenthesized) term expression.
fn parse_compound_term(inner: &str) -> Result<SmtTerm, SmtBridgeError> {
    if inner.is_empty() {
        return Err(SmtBridgeError::ParseError {
            reason: "empty parenthesized expression".to_string(),
        });
    }

    // Split into operator and arguments.
    let tokens = tokenize_sexp(inner)?;
    if tokens.is_empty() {
        return Err(SmtBridgeError::ParseError {
            reason: "empty s-expression".to_string(),
        });
    }

    let op = &tokens[0];

    // Let binding: (let ((x e1) ...) body)
    if op == "let" {
        if tokens.len() != 3 {
            return Err(SmtBridgeError::ParseError {
                reason: format!(
                    "let expects 2 arguments (bindings body), got {}",
                    tokens.len() - 1
                ),
            });
        }
        let bindings = parse_let_bindings(&tokens[1])?;
        let body = parse_smtlib2_term(&tokens[2])?;
        return Ok(SmtTerm::Let(bindings, Box::new(body)));
    }

    // Quantifiers: (forall ((x Int) ...) body) / (exists ...)
    if op == "forall" || op == "exists" {
        if tokens.len() != 3 {
            return Err(SmtBridgeError::ParseError {
                reason: format!(
                    "{op} expects 2 arguments (vars body), got {}",
                    tokens.len() - 1
                ),
            });
        }
        let quantifier = if op == "forall" {
            Quantifier::ForAll
        } else {
            Quantifier::Exists
        };
        let vars = parse_sorted_vars(&tokens[1])?;
        let body = parse_smtlib2_term(&tokens[2])?;
        return Ok(SmtTerm::Quant(quantifier, vars, Box::new(body)));
    }

    // Negated integer literal: (- N)
    if op == "-" && tokens.len() == 2 {
        if let Ok(n) = tokens[1].parse::<i64>() {
            return Ok(SmtTerm::int(-n));
        }
    }

    // Function application: (op args...)
    let args: Vec<SmtTerm> = tokens[1..]
        .iter()
        .map(|t| parse_smtlib2_term(t))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(SmtTerm::app(op.as_str(), args))
}

/// Tokenize an s-expression into top-level tokens, respecting nesting.
///
/// Each token is either a bare symbol or a complete parenthesized sub-expression.
fn tokenize_sexp(input: &str) -> Result<Vec<String>, SmtBridgeError> {
    let mut tokens = Vec::new();
    let mut depth = 0i32;
    let mut current_start: Option<usize> = None;
    let chars: Vec<char> = input.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        let ch = chars[i];
        match ch {
            '(' => {
                if depth == 0 {
                    // Flush any accumulated bare token.
                    if let Some(start) = current_start.take() {
                        let token: String = chars[start..i].iter().collect();
                        let token = token.trim().to_string();
                        if !token.is_empty() {
                            tokens.push(token);
                        }
                    }
                    current_start = Some(i);
                }
                depth += 1;
            }
            ')' => {
                depth -= 1;
                if depth == 0 {
                    if let Some(start) = current_start.take() {
                        let token: String = chars[start..=i].iter().collect();
                        tokens.push(token.trim().to_string());
                    }
                } else if depth < 0 {
                    return Err(SmtBridgeError::ParseError {
                        reason: "unmatched closing parenthesis".to_string(),
                    });
                }
            }
            ' ' | '\t' | '\n' | '\r' if depth == 0 => {
                if let Some(start) = current_start.take() {
                    let token: String = chars[start..i].iter().collect();
                    let token = token.trim().to_string();
                    if !token.is_empty() {
                        tokens.push(token);
                    }
                }
            }
            _ => {
                if current_start.is_none() && depth == 0 {
                    current_start = Some(i);
                }
            }
        }
        i += 1;
    }

    // Flush trailing token.
    if let Some(start) = current_start {
        let token: String = chars[start..].iter().collect();
        let token = token.trim().to_string();
        if !token.is_empty() {
            tokens.push(token);
        }
    }

    Ok(tokens)
}

/// Parse let bindings: `((x e1) (y e2) ...)`.
fn parse_let_bindings(input: &str) -> Result<Vec<(String, SmtTerm)>, SmtBridgeError> {
    let trimmed = input.trim();
    if !trimmed.starts_with('(') || !trimmed.ends_with(')') {
        return Err(SmtBridgeError::ParseError {
            reason: format!("let bindings must be parenthesized: {trimmed}"),
        });
    }
    let inner = &trimmed[1..trimmed.len() - 1];
    let binding_tokens = tokenize_sexp(inner)?;

    let mut bindings = Vec::new();
    for bt in &binding_tokens {
        let bt = bt.trim();
        if !bt.starts_with('(') || !bt.ends_with(')') {
            return Err(SmtBridgeError::ParseError {
                reason: format!("each let binding must be parenthesized: {bt}"),
            });
        }
        let binding_inner = &bt[1..bt.len() - 1];
        let parts = tokenize_sexp(binding_inner)?;
        if parts.len() != 2 {
            return Err(SmtBridgeError::ParseError {
                reason: format!("let binding expects (var term), got {parts:?}"),
            });
        }
        let var_name = parts[0].clone();
        let term = parse_smtlib2_term(&parts[1])?;
        bindings.push((var_name, term));
    }

    Ok(bindings)
}

/// Parse sorted variable bindings: `((x Int) (y Bool) ...)`.
fn parse_sorted_vars(input: &str) -> Result<Vec<(String, SmtSort)>, SmtBridgeError> {
    let trimmed = input.trim();
    if !trimmed.starts_with('(') || !trimmed.ends_with(')') {
        return Err(SmtBridgeError::ParseError {
            reason: format!("sorted vars must be parenthesized: {trimmed}"),
        });
    }
    let inner = &trimmed[1..trimmed.len() - 1];
    let var_tokens = tokenize_sexp(inner)?;

    let mut vars = Vec::new();
    for vt in &var_tokens {
        let vt = vt.trim();
        if !vt.starts_with('(') || !vt.ends_with(')') {
            return Err(SmtBridgeError::ParseError {
                reason: format!("each sorted var must be parenthesized: {vt}"),
            });
        }
        let var_inner = &vt[1..vt.len() - 1];
        let parts = tokenize_sexp(var_inner)?;
        if parts.len() != 2 {
            return Err(SmtBridgeError::ParseError {
                reason: format!("sorted var expects (name sort), got {parts:?}"),
            });
        }
        let var_name = parts[0].clone();
        let sort = parse_smtlib2_sort(&parts[1])?;
        vars.push((var_name, sort));
    }

    Ok(vars)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::ExprKind;

    #[test]
    fn test_smt_sort_bool_translates_to_prop() {
        let expr =
            translate_smt_sort_to_clean(&SmtSort::Bool).expect("Bool translation should succeed");
        assert!(
            matches!(expr.kind(), ExprKind::Sort(level) if level == &Level::zero()),
            "Bool should translate to Prop (Sort 0)"
        );
    }

    #[test]
    fn test_smt_sort_int_translates_to_const() {
        let expr =
            translate_smt_sort_to_clean(&SmtSort::Int).expect("Int translation should succeed");
        match expr.kind() {
            ExprKind::Const(name, _) => {
                assert_eq!(name.to_string(), "Int");
            }
            other => panic!("expected Const, got {other:?}"),
        }
    }

    #[test]
    fn test_smt_sort_real_translates_to_const() {
        let expr =
            translate_smt_sort_to_clean(&SmtSort::Real).expect("Real translation should succeed");
        match expr.kind() {
            ExprKind::Const(name, _) => {
                assert_eq!(name.to_string(), "Real");
            }
            other => panic!("expected Const, got {other:?}"),
        }
    }

    #[test]
    fn test_smt_sort_bitvec_translates_to_app() {
        let expr = translate_smt_sort_to_clean(&SmtSort::BitVec(32))
            .expect("BitVec(32) translation should succeed");
        match expr.kind() {
            ExprKind::App(func, arg) => {
                match func.kind() {
                    ExprKind::Const(name, _) => assert_eq!(name.to_string(), "BitVec"),
                    other => panic!("expected Const(BitVec), got {other:?}"),
                }
                match arg.kind() {
                    ExprKind::Lit(clean_kernel::Literal::Nat(n)) => {
                        assert_eq!(n.to_u64(), Some(32));
                    }
                    other => panic!("expected Lit(Nat(32)), got {other:?}"),
                }
            }
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn test_smt_sort_array_translates_to_arrow() {
        let arr = SmtSort::array(SmtSort::Int, SmtSort::Bool);
        let expr =
            translate_smt_sort_to_clean(&arr).expect("Array(Int, Bool) translation should succeed");
        // Arrow is represented as Pi with default binder info.
        match expr.kind() {
            ExprKind::Pi(_, from, _to) => match from.kind() {
                ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Int"),
                other => panic!("expected Const(Int) as domain, got {other:?}"),
            },
            other => panic!("expected Pi (arrow), got {other:?}"),
        }
    }

    #[test]
    fn test_smt_sort_uninterpreted_translates_to_const() {
        let expr = translate_smt_sort_to_clean(&SmtSort::uninterpreted("MySort"))
            .expect("Uninterpreted sort translation should succeed");
        match expr.kind() {
            ExprKind::Const(name, _) => {
                assert_eq!(name.to_string(), "MySort");
            }
            other => panic!("expected Const, got {other:?}"),
        }
    }

    #[test]
    fn test_smt_term_constructors() {
        let t = SmtTerm::bool_(true);
        assert_eq!(t, SmtTerm::Literal(SmtLiteral::Bool(true)));

        let i = SmtTerm::int(42);
        assert_eq!(i, SmtTerm::Literal(SmtLiteral::Int(42)));

        let v = SmtTerm::var("x");
        assert_eq!(v, SmtTerm::Var("x".into()));

        let a = SmtTerm::app("+", vec![SmtTerm::var("x"), SmtTerm::int(1)]);
        match a {
            SmtTerm::App(name, args) => {
                assert_eq!(name, "+");
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn test_smt_let_and_quant() {
        let let_term = SmtTerm::Let(
            vec![("x".into(), SmtTerm::int(5))],
            Box::new(SmtTerm::var("x")),
        );
        match &let_term {
            SmtTerm::Let(bindings, body) => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "x");
                assert_eq!(**body, SmtTerm::var("x"));
            }
            other => panic!("expected Let, got {other:?}"),
        }

        let forall = SmtTerm::Quant(
            Quantifier::ForAll,
            vec![("n".into(), SmtSort::Int)],
            Box::new(SmtTerm::app(">=", vec![SmtTerm::var("n"), SmtTerm::int(0)])),
        );
        match &forall {
            SmtTerm::Quant(q, vars, _body) => {
                assert_eq!(*q, Quantifier::ForAll);
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].0, "n");
                assert_eq!(vars[0].1, SmtSort::Int);
            }
            other => panic!("expected Quant, got {other:?}"),
        }
    }

    #[test]
    fn test_smt_vc_bundle_builder() {
        let bundle = SmtVcBundle::new("QF_LIA")
            .with_sort(SmtSort::uninterpreted("State"))
            .with_assertion(SmtAssertion {
                name: Some("vc_1".into()),
                term: SmtTerm::bool_(true),
                source_line: Some(42),
            });

        assert_eq!(bundle.logic, "QF_LIA");
        assert_eq!(bundle.sorts.len(), 1);
        assert_eq!(bundle.assertion_count(), 1);
        assert!(bundle.certificate.is_none());
    }

    // -----------------------------------------------------------------------
    // parse_smtlib2_sort tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_parse_sort_bool() {
        assert_eq!(parse_smtlib2_sort("Bool").unwrap(), SmtSort::Bool);
    }

    #[test]
    fn test_parse_sort_int() {
        assert_eq!(parse_smtlib2_sort("Int").unwrap(), SmtSort::Int);
    }

    #[test]
    fn test_parse_sort_real() {
        assert_eq!(parse_smtlib2_sort("Real").unwrap(), SmtSort::Real);
    }

    #[test]
    fn test_parse_sort_bitvec() {
        assert_eq!(
            parse_smtlib2_sort("(_ BitVec 32)").unwrap(),
            SmtSort::BitVec(32)
        );
        assert_eq!(
            parse_smtlib2_sort("(_ BitVec 8)").unwrap(),
            SmtSort::BitVec(8)
        );
        assert_eq!(
            parse_smtlib2_sort("(_ BitVec 256)").unwrap(),
            SmtSort::BitVec(256)
        );
    }

    #[test]
    fn test_parse_sort_array() {
        let result = parse_smtlib2_sort("(Array Int Bool)").unwrap();
        assert_eq!(result, SmtSort::array(SmtSort::Int, SmtSort::Bool));
    }

    #[test]
    fn test_parse_sort_nested_array() {
        let result = parse_smtlib2_sort("(Array Int (Array Int Bool))").unwrap();
        let expected = SmtSort::array(SmtSort::Int, SmtSort::array(SmtSort::Int, SmtSort::Bool));
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parse_sort_uninterpreted() {
        assert_eq!(
            parse_smtlib2_sort("MySort").unwrap(),
            SmtSort::Uninterpreted("MySort".to_string())
        );
    }

    #[test]
    fn test_parse_sort_empty_errors() {
        let result = parse_smtlib2_sort("");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_sort_unmatched_paren_errors() {
        let result = parse_smtlib2_sort("(Array Int Bool");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_sort_invalid_bitvec_width_errors() {
        let result = parse_smtlib2_sort("(_ BitVec abc)");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_sort_whitespace_handling() {
        assert_eq!(parse_smtlib2_sort("  Int  ").unwrap(), SmtSort::Int);
        assert_eq!(
            parse_smtlib2_sort("  (Array  Int  Bool)  ").unwrap(),
            SmtSort::array(SmtSort::Int, SmtSort::Bool)
        );
    }

    // -----------------------------------------------------------------------
    // parse_smtlib2_term tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_parse_term_true() {
        assert_eq!(parse_smtlib2_term("true").unwrap(), SmtTerm::bool_(true));
    }

    #[test]
    fn test_parse_term_false() {
        assert_eq!(parse_smtlib2_term("false").unwrap(), SmtTerm::bool_(false));
    }

    #[test]
    fn test_parse_term_integer() {
        assert_eq!(parse_smtlib2_term("42").unwrap(), SmtTerm::int(42));
        assert_eq!(parse_smtlib2_term("0").unwrap(), SmtTerm::int(0));
        assert_eq!(parse_smtlib2_term("-5").unwrap(), SmtTerm::int(-5));
    }

    #[test]
    fn test_parse_term_variable() {
        assert_eq!(parse_smtlib2_term("x").unwrap(), SmtTerm::var("x"));
        assert_eq!(
            parse_smtlib2_term("my_var").unwrap(),
            SmtTerm::var("my_var")
        );
    }

    #[test]
    fn test_parse_term_simple_app() {
        let result = parse_smtlib2_term("(+ x 1)").unwrap();
        match result {
            SmtTerm::App(op, args) => {
                assert_eq!(op, "+");
                assert_eq!(args.len(), 2);
                assert_eq!(args[0], SmtTerm::var("x"));
                assert_eq!(args[1], SmtTerm::int(1));
            }
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_term_nested_app() {
        let result = parse_smtlib2_term("(and (= x 1) (> y 0))").unwrap();
        match result {
            SmtTerm::App(op, args) => {
                assert_eq!(op, "and");
                assert_eq!(args.len(), 2);
                // First arg: (= x 1)
                match &args[0] {
                    SmtTerm::App(op2, args2) => {
                        assert_eq!(op2, "=");
                        assert_eq!(args2.len(), 2);
                    }
                    other => panic!("expected App for first arg, got {other:?}"),
                }
                // Second arg: (> y 0)
                match &args[1] {
                    SmtTerm::App(op2, args2) => {
                        assert_eq!(op2, ">");
                        assert_eq!(args2.len(), 2);
                    }
                    other => panic!("expected App for second arg, got {other:?}"),
                }
            }
            other => panic!("expected App(and), got {other:?}"),
        }
    }

    #[test]
    fn test_parse_term_let() {
        let result = parse_smtlib2_term("(let ((x 5)) x)").unwrap();
        match result {
            SmtTerm::Let(bindings, body) => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "x");
                assert_eq!(bindings[0].1, SmtTerm::int(5));
                assert_eq!(*body, SmtTerm::var("x"));
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_term_let_multiple_bindings() {
        let result = parse_smtlib2_term("(let ((x 1) (y 2)) (+ x y))").unwrap();
        match result {
            SmtTerm::Let(bindings, body) => {
                assert_eq!(bindings.len(), 2);
                assert_eq!(bindings[0].0, "x");
                assert_eq!(bindings[1].0, "y");
                match *body {
                    SmtTerm::App(ref op, ref args) => {
                        assert_eq!(op, "+");
                        assert_eq!(args.len(), 2);
                    }
                    ref other => panic!("expected App body, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_term_forall() {
        let result = parse_smtlib2_term("(forall ((n Int)) (>= n 0))").unwrap();
        match result {
            SmtTerm::Quant(q, vars, body) => {
                assert_eq!(q, Quantifier::ForAll);
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].0, "n");
                assert_eq!(vars[0].1, SmtSort::Int);
                match *body {
                    SmtTerm::App(ref op, _) => assert_eq!(op, ">="),
                    ref other => panic!("expected App body, got {other:?}"),
                }
            }
            other => panic!("expected Quant, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_term_exists() {
        let result = parse_smtlib2_term("(exists ((x Bool)) x)").unwrap();
        match result {
            SmtTerm::Quant(q, vars, body) => {
                assert_eq!(q, Quantifier::Exists);
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].0, "x");
                assert_eq!(vars[0].1, SmtSort::Bool);
                assert_eq!(*body, SmtTerm::var("x"));
            }
            other => panic!("expected Quant, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_term_negated_literal() {
        let result = parse_smtlib2_term("(- 42)").unwrap();
        assert_eq!(result, SmtTerm::int(-42));
    }

    #[test]
    fn test_parse_term_empty_errors() {
        assert!(parse_smtlib2_term("").is_err());
    }

    #[test]
    fn test_parse_term_unmatched_paren_errors() {
        assert!(parse_smtlib2_term("(+ x 1").is_err());
    }

    #[test]
    fn test_parse_term_deeply_nested() {
        let result = parse_smtlib2_term("(or (and (= a b) (= c d)) (not e))").unwrap();
        match result {
            SmtTerm::App(op, args) => {
                assert_eq!(op, "or");
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_term_nullary_app() {
        // A function with no arguments.
        let result = parse_smtlib2_term("(f)").unwrap();
        match result {
            SmtTerm::App(op, args) => {
                assert_eq!(op, "f");
                assert!(args.is_empty());
            }
            other => panic!("expected App, got {other:?}"),
        }
    }

    #[test]
    fn test_tokenize_sexp_basic() {
        let tokens = tokenize_sexp("and (= x 1) (> y 0)").unwrap();
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0], "and");
        assert_eq!(tokens[1], "(= x 1)");
        assert_eq!(tokens[2], "(> y 0)");
    }
}
