// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Literal inference regressions against the ordinary, non-`cfg(test)` library.
//!
//! With release debug assertions disabled, public inference uses the production
//! fast path, while retained-certificate inference uses the certificate path.
//! Debug inference delegates to the certificate path, so a debug run alone does
//! not compare those distinct call paths. These fixtures are regressions, not a
//! universal source-refinement proof.

use clean_kernel::cert::ProofCert;
use clean_kernel::expr::{BigNat, Literal};
use clean_kernel::{Environment, Expr, ExprKind, Name, TypeChecker};

#[test]
fn test_literal_types_agree_with_retained_certificates() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let fixtures = [
        (Literal::Nat(BigNat::Small(0)), "Nat"),
        (Literal::Nat(BigNat::Small(u64::MAX)), "Nat"),
        (Literal::Nat(BigNat::Big(vec![0, 1])), "Nat"),
        (Literal::String("".into()), "String"),
        (Literal::String("42".into()), "String"),
        (Literal::String("λ\0🦀".into()), "String"),
    ];

    for (literal, name) in fixtures {
        let input = Expr::from_kind(ExprKind::Lit(literal.clone()));
        let expected = Expr::const_(Name::from_string(name), vec![]);
        let inferred = tc.infer_type(&input).expect("literal inference");
        let (certified, certificate) = tc
            .infer_type_with_cert(&input)
            .expect("literal inference retaining its certificate");

        assert_eq!(inferred, expected);
        assert_eq!(certified, expected);
        let ProofCert::Lit { lit, type_ } = &certificate else {
            panic!("literal inference must retain a literal certificate");
        };
        assert_eq!(lit, &literal, "the certificate must preserve the payload");
        assert_eq!(type_.as_ref(), &expected);
    }
}
