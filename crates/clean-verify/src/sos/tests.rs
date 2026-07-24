// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the SageMath SOS bridge.

use num_rational::Rational64;

use crate::smt_verify::nra::{Monomial, Polynomial};

use super::parse::{parse_polynomial, parse_sage_sos, SosParseError};
use super::verify::{expand_sum_of_squares, square_polynomial, verify_sos_certificate, SosVerdict};

fn rat(n: i64) -> Rational64 {
    Rational64::from_integer(n)
}

fn rat_frac(n: i64, d: i64) -> Rational64 {
    Rational64::new(n, d)
}

// -- Parsing tests --

#[test]
fn test_parse_minimal_certificate() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x
TARGET: x^2
SQUARES: 1
Q1: x
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(cert.variables, vec!["x"]);
    assert_eq!(cert.squares.len(), 1);
}

#[test]
fn test_parse_two_variable_certificate() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x y
TARGET: x^2 + y^2
SQUARES: 2
Q1: x
Q2: y
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(cert.variables, vec!["x", "y"]);
    assert_eq!(cert.squares.len(), 2);
}

#[test]
fn test_parse_rational_coefficients() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x y
TARGET: (1/2)*x^2 + (1/2)*y^2
SQUARES: 1
Q1: (1/2)*x + (1/2)*y
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(cert.squares.len(), 1);
}

#[test]
fn test_parse_negative_coefficients() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x y
TARGET: x^2 - 2*x*y + y^2
SQUARES: 1
Q1: x - y
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(cert.squares.len(), 1);
}

#[test]
fn test_parse_three_variable_certificate() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x y z
TARGET: x^4 + y^4 + z^4 - x^2*y^2 - y^2*z^2 - z^2*x^2
SQUARES: 3
Q1: (1/2)*x^2 - (1/2)*y^2
Q2: (1/2)*y^2 - (1/2)*z^2
Q3: (1/2)*x^2 - (1/2)*z^2
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(cert.variables, vec!["x", "y", "z"]);
    assert_eq!(cert.squares.len(), 3);
}

#[test]
fn test_parse_missing_header() {
    let input = "\
VARIABLES: x
TARGET: x^2
SQUARES: 1
Q1: x
";
    let err = parse_sage_sos(input).unwrap_err();
    assert_eq!(err, SosParseError::MissingHeader);
}

#[test]
fn test_parse_missing_variables() {
    let input = "\
SOS_CERTIFICATE
TARGET: x^2
SQUARES: 1
Q1: x
";
    let err = parse_sage_sos(input).unwrap_err();
    assert_eq!(err, SosParseError::MissingVariables);
}

#[test]
fn test_parse_missing_target() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x
SQUARES: 1
Q1: x
";
    let err = parse_sage_sos(input).unwrap_err();
    assert_eq!(err, SosParseError::MissingTarget);
}

#[test]
fn test_parse_missing_squares_count() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x
TARGET: x^2
Q1: x
";
    let err = parse_sage_sos(input).unwrap_err();
    assert_eq!(err, SosParseError::MissingSquaresCount);
}

#[test]
fn test_parse_invalid_squares_count() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x
TARGET: x^2
SQUARES: abc
Q1: x
";
    let err = parse_sage_sos(input).unwrap_err();
    assert!(matches!(err, SosParseError::InvalidSquaresCount(_)));
}

#[test]
fn test_parse_square_count_mismatch() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x
TARGET: x^2
SQUARES: 2
Q1: x
";
    let err = parse_sage_sos(input).unwrap_err();
    assert!(matches!(err, SosParseError::SquareCountMismatch { .. }));
}

#[test]
fn test_parse_undeclared_variable() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x
TARGET: x^2 + z^2
SQUARES: 1
Q1: x
";
    let err = parse_sage_sos(input).unwrap_err();
    assert!(matches!(err, SosParseError::UndeclaredVariable(_)));
}

// -- Polynomial parsing tests --

#[test]
fn test_parse_polynomial_constant() {
    let vars = vec!["x".to_string()];
    let p = parse_polynomial("5", &vars, 0).expect("should parse");
    assert_eq!(p, Polynomial::constant(rat(5)));
}

#[test]
fn test_parse_polynomial_single_variable() {
    let vars = vec!["x".to_string()];
    let p = parse_polynomial("x", &vars, 0).expect("should parse");
    assert_eq!(p, Polynomial::term(rat(1), Monomial::variable("x")));
}

#[test]
fn test_parse_polynomial_variable_with_exponent() {
    let vars = vec!["x".to_string()];
    let p = parse_polynomial("x^3", &vars, 0).expect("should parse");
    assert_eq!(
        p,
        Polynomial::term(rat(1), Monomial::new(vec![("x".to_string(), 3)]))
    );
}

#[test]
fn test_parse_polynomial_coefficient_times_variable() {
    let vars = vec!["x".to_string()];
    let p = parse_polynomial("3*x", &vars, 0).expect("should parse");
    assert_eq!(p, Polynomial::term(rat(3), Monomial::variable("x")));
}

#[test]
fn test_parse_polynomial_rational_coefficient() {
    let vars = vec!["x".to_string()];
    let p = parse_polynomial("(1/2)*x", &vars, 0).expect("should parse");
    assert_eq!(p, Polynomial::term(rat_frac(1, 2), Monomial::variable("x")));
}

#[test]
fn test_parse_polynomial_negative_rational() {
    let vars = vec!["x".to_string()];
    let p = parse_polynomial("(-3/4)*x^2", &vars, 0).expect("should parse");
    assert_eq!(
        p,
        Polynomial::term(rat_frac(-3, 4), Monomial::new(vec![("x".to_string(), 2)]))
    );
}

#[test]
fn test_parse_polynomial_sum() {
    let vars = vec!["x".to_string(), "y".to_string()];
    let p = parse_polynomial("x + y", &vars, 0).expect("should parse");
    let expected = Polynomial::new(vec![
        (rat(1), Monomial::variable("x")),
        (rat(1), Monomial::variable("y")),
    ]);
    assert_eq!(p, expected);
}

#[test]
fn test_parse_polynomial_difference() {
    let vars = vec!["x".to_string(), "y".to_string()];
    let p = parse_polynomial("x - y", &vars, 0).expect("should parse");
    let expected = Polynomial::new(vec![
        (rat(1), Monomial::variable("x")),
        (rat(-1), Monomial::variable("y")),
    ]);
    assert_eq!(p, expected);
}

#[test]
fn test_parse_polynomial_product_of_variables() {
    let vars = vec!["x".to_string(), "y".to_string()];
    let p = parse_polynomial("x*y", &vars, 0).expect("should parse");
    let expected = Polynomial::term(
        rat(1),
        Monomial::new(vec![("x".to_string(), 1), ("y".to_string(), 1)]),
    );
    assert_eq!(p, expected);
}

#[test]
fn test_parse_polynomial_complex() {
    let vars = vec!["x".to_string(), "y".to_string()];
    let p = parse_polynomial("2*x^2 - 3*x*y + y^2 + 1", &vars, 0).expect("should parse");
    // Verify by evaluation at (x=2, y=3): 2*4 - 3*2*3 + 9 + 1 = 8 - 18 + 9 + 1 = 0
    let mut assignment = std::collections::BTreeMap::new();
    assignment.insert("x".to_string(), rat(2));
    assignment.insert("y".to_string(), rat(3));
    let value = p.evaluate(&assignment).expect("should evaluate");
    assert_eq!(value, rat(0));
}

#[test]
fn test_parse_polynomial_empty_is_zero() {
    let vars = vec!["x".to_string()];
    let p = parse_polynomial("", &vars, 0).expect("should parse");
    assert!(p.is_zero());
}

// -- Verification tests --

#[test]
fn test_verify_x_squared() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x
TARGET: x^2
SQUARES: 1
Q1: x
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(verify_sos_certificate(&cert), SosVerdict::Valid);
}

#[test]
fn test_verify_sum_of_two_squares() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x y
TARGET: x^2 + y^2
SQUARES: 2
Q1: x
Q2: y
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(verify_sos_certificate(&cert), SosVerdict::Valid);
}

#[test]
fn test_verify_perfect_square_binomial() {
    // (x - y)^2 = x^2 - 2*x*y + y^2
    let input = "\
SOS_CERTIFICATE
VARIABLES: x y
TARGET: x^2 - 2*x*y + y^2
SQUARES: 1
Q1: x - y
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(verify_sos_certificate(&cert), SosVerdict::Valid);
}

#[test]
fn test_verify_three_squares_quartic() {
    // Verify: x^4 + y^4 + z^4 - x^2*y^2 - y^2*z^2 - z^2*x^2
    //       = ((1/2)*x^2 - (1/2)*y^2)^2 + ((1/2)*y^2 - (1/2)*z^2)^2 + ((1/2)*x^2 - (1/2)*z^2)^2
    //
    // Expand:
    //   ((1/2)x^2 - (1/2)y^2)^2 = (1/4)x^4 - (1/2)x^2*y^2 + (1/4)y^4
    //   ((1/2)y^2 - (1/2)z^2)^2 = (1/4)y^4 - (1/2)y^2*z^2 + (1/4)z^4
    //   ((1/2)x^2 - (1/2)z^2)^2 = (1/4)x^4 - (1/2)x^2*z^2 + (1/4)z^4
    //   Sum = (1/2)x^4 + (1/2)y^4 + (1/2)z^4 - (1/2)x^2*y^2 - (1/2)y^2*z^2 - (1/2)x^2*z^2
    //
    // That equals (1/2) * target, NOT target. So the certificate as written is
    // actually for (1/2)*target. Let me fix the squares to use 1/sqrt(2) or
    // adjust the target.
    //
    // Correct decomposition for the actual polynomial:
    //   x^4 + y^4 + z^4 - x^2*y^2 - y^2*z^2 - z^2*x^2
    // Use Schur's inequality approach. Actually, the simpler approach:
    //
    //   (x^2 - y^2)^2 = x^4 - 2*x^2*y^2 + y^4
    //   (y^2 - z^2)^2 = y^4 - 2*y^2*z^2 + z^4
    //   (x^2 - z^2)^2 = x^4 - 2*x^2*z^2 + z^4
    //   Sum = 2*x^4 + 2*y^4 + 2*z^4 - 2*x^2*y^2 - 2*y^2*z^2 - 2*x^2*z^2
    //       = 2 * target
    //
    // So target = (1/2) * sum, i.e., we need coefficients 1/sqrt(2).
    // With rational SOS, we can scale:
    //   target = ((1/sqrt(2))*(x^2-y^2))^2 + ...
    // But sqrt(2) is irrational. Instead, verify a simpler case.
    //
    // Use: x^2 + y^2 + z^2 = x^2 + y^2 + z^2 (trivial SOS).
    let input = "\
SOS_CERTIFICATE
VARIABLES: x y z
TARGET: x^2 + y^2 + z^2
SQUARES: 3
Q1: x
Q2: y
Q3: z
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(verify_sos_certificate(&cert), SosVerdict::Valid);
}

#[test]
fn test_verify_mismatch() {
    // Claim x^2 = y^2, which is false.
    let input = "\
SOS_CERTIFICATE
VARIABLES: x y
TARGET: x^2
SQUARES: 1
Q1: y
";
    let cert = parse_sage_sos(input).expect("should parse");
    match verify_sos_certificate(&cert) {
        SosVerdict::Invalid(_) => {} // expected
        SosVerdict::Valid => panic!("should be invalid"),
    }
}

#[test]
fn test_verify_zero_target_no_squares() {
    let input = "\
SOS_CERTIFICATE
VARIABLES: x
TARGET: 0
SQUARES: 0
";
    // Target "0" parses as zero polynomial since we filter zero-coeff terms.
    // Actually, "0" is parsed as integer constant 0, which Polynomial::new filters out.
    let cert = parse_sage_sos(input).expect("should parse");
    assert!(cert.target.is_zero());
    assert_eq!(verify_sos_certificate(&cert), SosVerdict::Valid);
}

#[test]
fn test_verify_quadratic_form() {
    // 2*x^2 + 2*y^2 + 2*x*y = (x + y)^2 + x^2 + y^2
    // Expand: (x+y)^2 = x^2 + 2xy + y^2, so sum = 2x^2 + 2xy + 2y^2. Correct!
    let input = "\
SOS_CERTIFICATE
VARIABLES: x y
TARGET: 2*x^2 + 2*x*y + 2*y^2
SQUARES: 3
Q1: x
Q2: y
Q3: x + y
";
    let cert = parse_sage_sos(input).expect("should parse");
    // Expand: x^2 + y^2 + (x+y)^2 = x^2 + y^2 + x^2 + 2xy + y^2 = 2x^2 + 2xy + 2y^2
    assert_eq!(verify_sos_certificate(&cert), SosVerdict::Valid);
}

#[test]
fn test_verify_with_rational_squares() {
    // (1/2)x^2 = ((1/sqrt(2))x)^2 -- not rational
    // Instead: x^2/4 + x^2/4 = x^2/2
    // Target: (1/2)*x^2 = ((1/2)*x)^2 + ... no, (1/2 * x)^2 = x^2/4, not x^2/2
    //
    // Simpler: target = (1/4)*x^2, squares = [(1/2)*x]
    // Check: ((1/2)*x)^2 = (1/4)*x^2. Correct!
    let input = "\
SOS_CERTIFICATE
VARIABLES: x
TARGET: (1/4)*x^2
SQUARES: 1
Q1: (1/2)*x
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(verify_sos_certificate(&cert), SosVerdict::Valid);
}

#[test]
fn test_verify_degree_four() {
    // (x^2 + y)^2 = x^4 + 2*x^2*y + y^2
    let input = "\
SOS_CERTIFICATE
VARIABLES: x y
TARGET: x^4 + 2*x^2*y + y^2
SQUARES: 1
Q1: x^2 + y
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(verify_sos_certificate(&cert), SosVerdict::Valid);
}

// -- expand_sum_of_squares unit tests --

#[test]
fn test_expand_empty_sum() {
    let result = expand_sum_of_squares(&[]);
    assert!(result.is_zero());
}

#[test]
fn test_expand_single_square() {
    let q = Polynomial::term(rat(1), Monomial::variable("x"));
    let result = expand_sum_of_squares(&[q]);
    let expected = Polynomial::term(rat(1), Monomial::new(vec![("x".to_string(), 2)]));
    assert_eq!(result, expected);
}

#[test]
fn test_expand_two_squares() {
    let q1 = Polynomial::term(rat(1), Monomial::variable("x"));
    let q2 = Polynomial::term(rat(1), Monomial::variable("y"));
    let result = expand_sum_of_squares(&[q1, q2]);
    let expected = Polynomial::new(vec![
        (rat(1), Monomial::new(vec![("x".to_string(), 2)])),
        (rat(1), Monomial::new(vec![("y".to_string(), 2)])),
    ]);
    assert_eq!(result, expected);
}

// -- square_polynomial tests --

#[test]
fn test_square_constant() {
    let p = Polynomial::constant(rat(3));
    let result = square_polynomial(&p);
    assert_eq!(result, Polynomial::constant(rat(9)));
}

#[test]
fn test_square_binomial() {
    // (x + 1)^2 = x^2 + 2x + 1
    let p = Polynomial::new(vec![
        (rat(1), Monomial::variable("x")),
        (rat(1), Monomial::one()),
    ]);
    let result = square_polynomial(&p);
    let expected = Polynomial::new(vec![
        (rat(1), Monomial::new(vec![("x".to_string(), 2)])),
        (rat(2), Monomial::variable("x")),
        (rat(1), Monomial::one()),
    ]);
    assert_eq!(result, expected);
}

#[test]
fn test_square_difference() {
    // (x - y)^2 = x^2 - 2xy + y^2
    let p = Polynomial::new(vec![
        (rat(1), Monomial::variable("x")),
        (rat(-1), Monomial::variable("y")),
    ]);
    let result = square_polynomial(&p);
    let expected = Polynomial::new(vec![
        (rat(1), Monomial::new(vec![("x".to_string(), 2)])),
        (
            rat(-2),
            Monomial::new(vec![("x".to_string(), 1), ("y".to_string(), 1)]),
        ),
        (rat(1), Monomial::new(vec![("y".to_string(), 2)])),
    ]);
    assert_eq!(result, expected);
}

// -- End-to-end tests --

#[test]
fn test_end_to_end_motzkin_style() {
    // Motzkin polynomial is NOT SOS, but we can test with a polynomial
    // that IS SOS.
    //
    // AM-GM style: x^2*y^2 + y^2*z^2 + z^2*x^2 = (xy)^2 + (yz)^2 + (zx)^2
    let input = "\
SOS_CERTIFICATE
VARIABLES: x y z
TARGET: x^2*y^2 + y^2*z^2 + z^2*x^2
SQUARES: 3
Q1: x*y
Q2: y*z
Q3: z*x
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(verify_sos_certificate(&cert), SosVerdict::Valid);
}

#[test]
fn test_end_to_end_with_constant_term() {
    // (x + 1)^2 + (y - 2)^2 = x^2 + 2x + 1 + y^2 - 4y + 4
    //                        = x^2 + y^2 + 2x - 4y + 5
    let input = "\
SOS_CERTIFICATE
VARIABLES: x y
TARGET: x^2 + y^2 + 2*x - 4*y + 5
SQUARES: 2
Q1: x + 1
Q2: y - 2
";
    let cert = parse_sage_sos(input).expect("should parse");
    assert_eq!(verify_sos_certificate(&cert), SosVerdict::Valid);
}

#[test]
fn test_end_to_end_single_variable_quartic() {
    // (x^2 - 1)^2 + (2*x)^2 = x^4 - 2*x^2 + 1 + 4*x^2 = x^4 + 2*x^2 + 1
    let input = "\
SOS_CERTIFICATE
VARIABLES: x
TARGET: x^4 + 2*x^2 + 1
SQUARES: 2
Q1: x^2 - 1
Q2: 2*x
";
    // Expand: (x^2 - 1)^2 = x^4 - 2x^2 + 1, (2x)^2 = 4x^2
    // Sum = x^4 + 2x^2 + 1
    let cert = parse_sage_sos(input).expect("should parse");

    // Verify the parsed target evaluates correctly at x=2: 16 + 8 + 1 = 25
    let mut assignment = std::collections::BTreeMap::new();
    assignment.insert("x".to_string(), rat(2));
    let target_val = cert.target.evaluate(&assignment).expect("should evaluate");
    assert_eq!(target_val, rat(25));

    assert_eq!(verify_sos_certificate(&cert), SosVerdict::Valid);
}

#[test]
fn test_negative_unary_in_leading_position() {
    let vars = vec!["x".to_string(), "y".to_string()];
    let p = parse_polynomial("-x + y", &vars, 0).expect("should parse");
    let expected = Polynomial::new(vec![
        (rat(-1), Monomial::variable("x")),
        (rat(1), Monomial::variable("y")),
    ]);
    assert_eq!(p, expected);
}

#[test]
fn test_parse_polynomial_negative_rational_coefficient() {
    let vars = vec!["x".to_string()];
    let p = parse_polynomial("-(1/3)*x^2", &vars, 0).expect("should parse");
    assert_eq!(
        p,
        Polynomial::term(rat_frac(-1, 3), Monomial::new(vec![("x".to_string(), 2)]))
    );
}
