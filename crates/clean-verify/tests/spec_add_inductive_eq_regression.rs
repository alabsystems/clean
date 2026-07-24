// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_elab::ElabCtx;
use clean_parser::parse_expr;
use clean_verify::test_utils::build_spec_with_stack;

#[test]
fn spec_add_inductive_registers_parameterized_type() {
    let mut spec = build_spec_with_stack();
    assert!(
        spec.definitions().contains_key("Nat"),
        "Nat should be registered in core spec"
    );
    assert!(
        spec.definitions().contains_key("Nat.zero"),
        "Nat.zero should be registered in core spec"
    );
    spec.add_inductive(
        r"inductive EqTest (A : Type) : A -> A -> Type
| refl : forall (x : A), EqTest A x x",
        "Parameterized inductive registration regression test for #821 (NotAFunction)",
    )
    .expect("EqTest inductive should register");
    assert!(
        spec.definitions().contains_key("EqTest"),
        "EqTest should be registered after add_inductive"
    );
    assert!(
        spec.definitions().contains_key("EqTest.refl"),
        "EqTest.refl should be registered after add_inductive"
    );

    let surface =
        parse_expr("EqTest Nat Nat.zero Nat.zero").expect("EqTest application should parse");
    let mut ctx = ElabCtx::new(spec.env());
    let result = ctx.elaborate(&surface);
    assert!(
        result.is_ok(),
        "EqTest application should elaborate (env registration path): {:?}",
        result
    );
}
