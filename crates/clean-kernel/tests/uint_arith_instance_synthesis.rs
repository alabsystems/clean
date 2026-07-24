// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end elaboration checks for the fixed-width UInt arithmetic prelude.

use clean_elab::ElabCtx;
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::name::Name;
use clean_kernel::{Environment, TypeChecker};
use clean_parser::parse_expr;

#[test]
fn fixed_width_uint_x_plus_one_synthesizes_arithmetic_and_literal_support() {
    let env = Environment::with_prelude();

    for width in ["UInt8", "UInt16", "UInt32", "UInt64"] {
        let source = format!("fun (x : {width}) => x + 1");
        let surface = parse_expr(&source).unwrap_or_else(|error| panic!("parse {source}: {error}"));
        let mut elaborator = ElabCtx::new(&env);
        let term = elaborator
            .elaborate(&surface)
            .unwrap_or_else(|error| panic!("elaborate {source}: {error}"));

        let constants = term.collect_constants();
        let add_instance = Name::from_string(&format!("instHAdd{width}"));
        assert!(
            constants.contains(&add_instance),
            "{source} must synthesize {add_instance}; term: {term}"
        );
        // `instOfNat<width>` is reducible, so elaboration projects and reduces
        // it to the canonical carrier constructor rather than retaining the
        // dictionary constant in the final term. Reaching `<width>.ofNat` is
        // the observable evidence that the width-specific resolver entry won.
        let literal_constructor = Name::from_string(&format!("{width}.ofNat"));
        assert!(
            constants.contains(&literal_constructor),
            "{source} must resolve its literal through {literal_constructor}; term: {term}"
        );

        let carrier = Expr::const_(Name::from_string(width), vec![]);
        let expected_type = Expr::pi(BinderInfo::Default, carrier.clone(), carrier);
        let checker = TypeChecker::with_mode(&env, env.mode());
        let inferred = checker
            .infer_type(&term)
            .unwrap_or_else(|error| panic!("kernel-check {source}: {error}"));
        assert!(
            checker.is_def_eq(&inferred, &expected_type),
            "{source} inferred {inferred}, expected {expected_type}"
        );
    }
}
