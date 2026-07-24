// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser for SageMath SOS certificate text format.
//!
//! Parses the structured text format into [`SageSosCertificate`], reusing
//! [`Polynomial`] and [`Monomial`] from `smt_verify::nra`.

use std::collections::BTreeMap;

use num_rational::Rational64;

use crate::smt_verify::nra::{Monomial, Polynomial};

/// A parsed SOS certificate from SageMath.
///
/// Represents the decomposition: `target = sum_i squares[i]^2`.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct SageSosCertificate {
    /// Variable names declared in the certificate.
    pub(crate) variables: Vec<String>,
    /// The target polynomial that should equal the sum of squares.
    pub(crate) target: Polynomial,
    /// The polynomial factors whose squares sum to the target.
    pub(crate) squares: Vec<Polynomial>,
}

/// Errors during SOS certificate parsing.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum SosParseError {
    #[error("missing SOS_CERTIFICATE header")]
    MissingHeader,
    #[error("missing VARIABLES declaration")]
    MissingVariables,
    #[error("missing TARGET declaration")]
    MissingTarget,
    #[error("missing SQUARES count")]
    MissingSquaresCount,
    #[error("invalid SQUARES count: {0}")]
    InvalidSquaresCount(String),
    #[error("expected {expected} square terms, found {found}")]
    SquareCountMismatch { expected: usize, found: usize },
    #[error("invalid polynomial expression at line {line}: {detail}")]
    InvalidPolynomial { line: usize, detail: String },
    #[error("invalid coefficient: {0}")]
    InvalidCoefficient(String),
    #[error("invalid exponent: {0}")]
    InvalidExponent(String),
    #[error("undeclared variable: {0}")]
    UndeclaredVariable(String),
}

/// Parse a SageMath SOS certificate from text.
///
/// See module docs for format specification.
pub(crate) fn parse_sage_sos(input: &str) -> Result<SageSosCertificate, SosParseError> {
    let lines: Vec<&str> = input.lines().map(str::trim).collect();

    // Find and validate header
    let header_found = lines.contains(&"SOS_CERTIFICATE");
    if !header_found {
        return Err(SosParseError::MissingHeader);
    }

    // Parse VARIABLES
    let variables = parse_field(&lines, "VARIABLES:").ok_or(SosParseError::MissingVariables)?;
    let var_names: Vec<String> = variables
        .split_whitespace()
        .map(|s| s.to_string())
        .collect();

    // Parse TARGET
    let target_str = parse_field(&lines, "TARGET:").ok_or(SosParseError::MissingTarget)?;
    let target = parse_polynomial(&target_str, &var_names, 0)?;

    // Parse SQUARES count
    let squares_str = parse_field(&lines, "SQUARES:").ok_or(SosParseError::MissingSquaresCount)?;
    let num_squares: usize = squares_str
        .trim()
        .parse()
        .map_err(|_| SosParseError::InvalidSquaresCount(squares_str.to_string()))?;

    // Parse each Q_i
    let mut squares = Vec::with_capacity(num_squares);
    for i in 1..=num_squares {
        let prefix = format!("Q{i}:");
        let qi_str = parse_field(&lines, &prefix).ok_or(SosParseError::SquareCountMismatch {
            expected: num_squares,
            found: i - 1,
        })?;
        let qi = parse_polynomial(&qi_str, &var_names, 0)?;
        squares.push(qi);
    }

    Ok(SageSosCertificate {
        variables: var_names,
        target,
        squares,
    })
}

/// Extract the value portion after a field prefix like "VARIABLES:".
fn parse_field(lines: &[&str], prefix: &str) -> Option<String> {
    for line in lines {
        if let Some(rest) = line.strip_prefix(prefix) {
            return Some(rest.trim().to_string());
        }
    }
    None
}

/// Parse a polynomial expression string into a `Polynomial`.
///
/// Supports:
/// - Integer and rational coefficients: `3`, `-2`, `(1/2)`, `(-3/4)`
/// - Variables with optional exponents: `x`, `x^2`, `x^4`
/// - Multiplication: `x*y`, `x^2*y^2`
/// - Addition/subtraction: `x^2 + y^2 - z^2`
///
/// Grammar (informal):
/// ```text
/// poly   ::= term (('+' | '-') term)*
/// term   ::= coeff? factor ('*' factor)*
/// factor ::= var ('^' nat)?
/// coeff  ::= int | '(' int '/' nat ')'
/// ```
pub(crate) fn parse_polynomial(
    input: &str,
    variables: &[String],
    line_num: usize,
) -> Result<Polynomial, SosParseError> {
    let input = input.trim();
    if input.is_empty() {
        return Ok(Polynomial::zero());
    }

    let tokens = tokenize(input, line_num)?;
    let terms = parse_terms(&tokens, variables, line_num)?;
    Ok(Polynomial::new(terms))
}

// -- Tokenizer --

#[derive(Clone, Debug, PartialEq)]
enum Token {
    /// Integer literal
    Int(i64),
    /// Rational literal (numerator, denominator)
    Rat(i64, i64),
    /// Variable name
    Var(String),
    Plus,
    Minus,
    Star,
    Caret,
}

fn tokenize(input: &str, line_num: usize) -> Result<Vec<Token>, SosParseError> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = input.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        match chars[i] {
            ' ' | '\t' => {
                i += 1;
            }
            '+' => {
                tokens.push(Token::Plus);
                i += 1;
            }
            '-' => {
                // Distinguish unary minus from subtraction operator.
                // Unary minus: at start, or after +, -, *, (, ^
                let is_unary = tokens.is_empty()
                    || matches!(
                        tokens.last(),
                        Some(Token::Plus | Token::Minus | Token::Star | Token::Caret)
                    );

                if is_unary {
                    // Consume digits to form a negative number
                    i += 1;
                    // Skip whitespace after minus
                    while i < chars.len() && chars[i] == ' ' {
                        i += 1;
                    }
                    if i < chars.len() && chars[i] == '(' {
                        // Negative rational: -(n/d)
                        i += 1; // skip '('
                        let (num, next) = read_integer(&chars, i, line_num)?;
                        i = next;
                        skip_whitespace(&chars, &mut i);
                        if i >= chars.len() || chars[i] != '/' {
                            return Err(SosParseError::InvalidPolynomial {
                                line: line_num,
                                detail: "expected '/' in rational".into(),
                            });
                        }
                        i += 1; // skip '/'
                        skip_whitespace(&chars, &mut i);
                        let (den, next) = read_integer(&chars, i, line_num)?;
                        i = next;
                        skip_whitespace(&chars, &mut i);
                        if i >= chars.len() || chars[i] != ')' {
                            return Err(SosParseError::InvalidPolynomial {
                                line: line_num,
                                detail: "expected ')' closing rational".into(),
                            });
                        }
                        i += 1;
                        tokens.push(Token::Rat(-num, den));
                    } else if i < chars.len() && chars[i].is_ascii_digit() {
                        let (num, next) = read_integer(&chars, i, line_num)?;
                        i = next;
                        tokens.push(Token::Int(-num));
                    } else {
                        // Unary minus before a variable: push -1 coefficient
                        tokens.push(Token::Int(-1));
                        tokens.push(Token::Star);
                    }
                } else {
                    tokens.push(Token::Minus);
                    i += 1;
                }
            }
            '*' => {
                tokens.push(Token::Star);
                i += 1;
            }
            '^' => {
                tokens.push(Token::Caret);
                i += 1;
            }
            '(' => {
                // Rational: (n/d)
                i += 1;
                skip_whitespace(&chars, &mut i);
                let negative = if i < chars.len() && chars[i] == '-' {
                    i += 1;
                    skip_whitespace(&chars, &mut i);
                    true
                } else {
                    false
                };
                let (num, next) = read_integer(&chars, i, line_num)?;
                i = next;
                skip_whitespace(&chars, &mut i);
                if i >= chars.len() || chars[i] != '/' {
                    return Err(SosParseError::InvalidPolynomial {
                        line: line_num,
                        detail: "expected '/' in rational".into(),
                    });
                }
                i += 1;
                skip_whitespace(&chars, &mut i);
                let (den, next) = read_integer(&chars, i, line_num)?;
                i = next;
                skip_whitespace(&chars, &mut i);
                if i >= chars.len() || chars[i] != ')' {
                    return Err(SosParseError::InvalidPolynomial {
                        line: line_num,
                        detail: "expected ')' closing rational".into(),
                    });
                }
                i += 1;
                let sign_num = if negative { -num } else { num };
                tokens.push(Token::Rat(sign_num, den));
            }
            c if c.is_ascii_digit() => {
                let (num, next) = read_integer(&chars, i, line_num)?;
                i = next;
                tokens.push(Token::Int(num));
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                let start = i;
                while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                let name: String = chars[start..i].iter().collect();
                tokens.push(Token::Var(name));
            }
            other => {
                return Err(SosParseError::InvalidPolynomial {
                    line: line_num,
                    detail: format!("unexpected character: '{other}'"),
                });
            }
        }
    }

    Ok(tokens)
}

fn read_integer(
    chars: &[char],
    start: usize,
    line_num: usize,
) -> Result<(i64, usize), SosParseError> {
    let mut i = start;
    while i < chars.len() && chars[i].is_ascii_digit() {
        i += 1;
    }
    if i == start {
        return Err(SosParseError::InvalidPolynomial {
            line: line_num,
            detail: "expected integer".into(),
        });
    }
    let s: String = chars[start..i].iter().collect();
    let value: i64 = s
        .parse()
        .map_err(|_| SosParseError::InvalidCoefficient(s))?;
    Ok((value, i))
}

fn skip_whitespace(chars: &[char], i: &mut usize) {
    while *i < chars.len() && chars[*i] == ' ' {
        *i += 1;
    }
}

// -- Term parser --

/// Parse token stream into polynomial terms.
///
/// Strategy: split on Plus/Minus at the top level, then parse each
/// segment as a product of coefficient and monomial factors.
fn parse_terms(
    tokens: &[Token],
    variables: &[String],
    line_num: usize,
) -> Result<Vec<(Rational64, Monomial)>, SosParseError> {
    if tokens.is_empty() {
        return Ok(vec![]);
    }

    // Split into signed segments.
    // Each segment: (sign, sub-token-slice)
    let mut segments: Vec<(i64, Vec<&Token>)> = Vec::new();
    let mut current_sign: i64 = 1;
    let mut current_tokens: Vec<&Token> = Vec::new();

    for token in tokens {
        match token {
            Token::Plus => {
                if !current_tokens.is_empty() {
                    segments.push((current_sign, current_tokens));
                    current_tokens = Vec::new();
                }
                current_sign = 1;
            }
            Token::Minus => {
                if !current_tokens.is_empty() {
                    segments.push((current_sign, current_tokens));
                    current_tokens = Vec::new();
                }
                current_sign = -1;
            }
            _ => {
                current_tokens.push(token);
            }
        }
    }
    if !current_tokens.is_empty() {
        segments.push((current_sign, current_tokens));
    }

    let mut terms = Vec::new();
    for (sign, seg) in &segments {
        let (coeff, mono) = parse_product(seg, variables, line_num)?;
        let signed_coeff = if *sign < 0 { -coeff } else { coeff };
        terms.push((signed_coeff, mono));
    }

    Ok(terms)
}

/// Parse a product segment (between +/- operators) into coefficient * monomial.
fn parse_product(
    tokens: &[&Token],
    variables: &[String],
    line_num: usize,
) -> Result<(Rational64, Monomial), SosParseError> {
    // Split by Star tokens into factors
    let mut factors: Vec<Vec<&Token>> = Vec::new();
    let mut current: Vec<&Token> = Vec::new();
    for tok in tokens {
        match tok {
            Token::Star => {
                if !current.is_empty() {
                    factors.push(current);
                    current = Vec::new();
                }
            }
            _ => current.push(tok),
        }
    }
    if !current.is_empty() {
        factors.push(current);
    }

    let mut coeff = Rational64::from_integer(1);
    let mut var_factors: Vec<(String, u32)> = Vec::new();
    let mut has_explicit_coeff = false;

    for factor in &factors {
        match factor.as_slice() {
            [Token::Int(n)] => {
                coeff *= Rational64::from_integer(*n);
                has_explicit_coeff = true;
            }
            [Token::Rat(num, den)] => {
                if *den == 0 {
                    return Err(SosParseError::InvalidCoefficient(format!("{num}/{den}")));
                }
                coeff *= Rational64::new(*num, *den);
                has_explicit_coeff = true;
            }
            [Token::Var(name)] => {
                if !variables.contains(name) {
                    return Err(SosParseError::UndeclaredVariable(name.clone()));
                }
                var_factors.push((name.clone(), 1));
            }
            [Token::Var(name), Token::Caret, Token::Int(exp)] => {
                if !variables.contains(name) {
                    return Err(SosParseError::UndeclaredVariable(name.clone()));
                }
                if *exp < 0 {
                    return Err(SosParseError::InvalidExponent(exp.to_string()));
                }
                var_factors.push((name.clone(), *exp as u32));
            }
            // Handle Int*Var sequence within a single factor (e.g. after unary minus)
            [Token::Int(n), Token::Var(name)] => {
                if !variables.contains(name) {
                    return Err(SosParseError::UndeclaredVariable(name.clone()));
                }
                coeff *= Rational64::from_integer(*n);
                has_explicit_coeff = true;
                var_factors.push((name.clone(), 1));
            }
            _ => {
                return Err(SosParseError::InvalidPolynomial {
                    line: line_num,
                    detail: format!("unrecognized factor: {factor:?}"),
                });
            }
        }
    }

    let _ = has_explicit_coeff; // May be used later for validation
    let monomial = Monomial::new(var_factors);
    Ok((coeff, monomial))
}
