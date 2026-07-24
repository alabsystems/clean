// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for `mutual … end` blocks of *inductive* declarations
//! (bug #31: such blocks silently registered 0 declarations).
//!
//! These go through the FULL surface pipeline (`elaborate_decl_and_register`),
//! the same one `clean check` uses, and assert:
//!   - both cross-referencing inductive TYPES and their CONSTRUCTORS register,
//!   - the registered types are usable in `def`s (values kernel-infer),
//!   - a genuinely-broken family (constructor referencing an undefined type) is
//!     REJECTED loudly rather than silently dropped,
//!   - a plain single `inductive` is unaffected.

use crate::elaborate_decl_and_register;
use clean_kernel::{BigNat, Environment, Expr, ExprKind, Name, TypeChecker};
use clean_parser::parse_file;

/// Elaborate + register every decl in `code`, panicking on the first failure.
fn elab_all(code: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    for (i, decl) in decls.iter().enumerate() {
        elaborate_decl_and_register(&mut env, decl)
            .unwrap_or_else(|e| panic!("decl {i} failed to elaborate: {e:?}"));
    }
    env
}

const EVEN_ODD_SRC: &str = r#"
mutual
inductive Even where
  | zero
  | succ : Odd -> Even
inductive Odd where
  | succ : Even -> Odd
end
"#;

#[test]
fn test_mutual_inductive_registers_both_types() {
    let env = elab_all(EVEN_ODD_SRC);
    assert!(
        env.get_inductive(&Name::from_string("Even")).is_some(),
        "Even inductive must register"
    );
    assert!(
        env.get_inductive(&Name::from_string("Odd")).is_some(),
        "Odd inductive must register"
    );
    // The mutual family must be linked: each type sees the other in all_names.
    let even = env
        .get_inductive(&Name::from_string("Even"))
        .expect("Even present");
    assert_eq!(even.all_names.len(), 2, "Even belongs to a 2-type family");
}

#[test]
fn test_mutual_inductive_registers_constructors() {
    let env = elab_all(EVEN_ODD_SRC);
    for ctor in ["Even.zero", "Even.succ", "Odd.succ"] {
        assert!(
            env.get_constructor(&Name::from_string(ctor)).is_some(),
            "constructor {ctor} must register"
        );
    }
}

#[test]
fn test_mutual_inductive_constructors_usable_in_defs() {
    // The whole followup file from bug #31: the constructors must be usable to
    // build cross-referencing values that kernel-infer against their types.
    let src = format!(
        "{EVEN_ODD_SRC}\n\
         def e0 : Even := Even.zero\n\
         def o1 : Odd := Odd.succ Even.zero\n\
         def e2 : Even := Even.succ (Odd.succ Even.zero)\n"
    );
    let env = elab_all(&src);
    let tc = TypeChecker::new(&env);
    for name in ["e0", "o1", "e2"] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} must register"));
        let value = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{name} must have a value"));
        let inferred = tc
            .infer_type(value)
            .unwrap_or_else(|e| panic!("infer_type({name}) failed: {e:?}"));
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "{name}: inferred value type not def-eq to declared type"
        );
    }
}

/// Ordinary mutual recursors expose the complete minor telescope on every
/// member, but each `RecursorVal.rules` stores only that member's constructor
/// slice. Match lowering must concatenate those slices in `all_names` order;
/// it must not mistake ordinary sibling rules for restored nested companions.
#[test]
fn test_ordinary_mutual_matches_aggregate_member_rule_slices() {
    let src = format!(
        "{EVEN_ODD_SRC}\n\
         def evenTag : Even -> Nat\n\
           | Even.zero => 0\n\
           | Even.succ _ => 1\n\
         def oddTag : Odd -> Nat\n\
           | Odd.succ _ => 2\n\
         def oddTagDo : Odd -> Id Nat := fun x => do\n\
           match x with\n\
           | Odd.succ _ => return 3\n"
    );
    let env = elab_all(&src);
    let tc = TypeChecker::new(&env);

    let even_zero = Expr::const_(Name::from_string("Even.zero"), vec![]);
    let odd_succ_zero = Expr::app(
        Expr::const_(Name::from_string("Odd.succ"), vec![]),
        even_zero.clone(),
    );
    let even_succ = Expr::app(
        Expr::const_(Name::from_string("Even.succ"), vec![]),
        odd_succ_zero.clone(),
    );
    let cases = [
        ("evenTag", even_zero, 0),
        ("evenTag", even_succ, 1),
        ("oddTag", odd_succ_zero.clone(), 2),
        ("oddTagDo", odd_succ_zero, 3),
    ];
    for (function, arg, expected) in cases {
        let value = Expr::app(Expr::const_(Name::from_string(function), vec![]), arg);
        assert!(
            matches!(tc.whnf(&value).kind(), ExprKind::Lit(clean_kernel::Literal::Nat(BigNat::Small(n))) if *n == expected),
            "{function} must reduce through the ordinary mutual minor ordering"
        );
    }
}

#[test]
fn test_mutual_inductive_broken_member_is_rejected() {
    // `Baz` is undefined: the family is ill-formed and MUST be rejected — not
    // silently dropped (the soundness-adjacent silent-accept bug).
    let src = r#"
mutual
inductive Foo where
  | mk : Baz -> Foo
inductive Bar where
  | mk : Foo -> Bar
end
"#;
    let mut env = Environment::with_prelude();
    let decls = parse_file(src).expect("should parse");
    let result = decls
        .iter()
        .try_for_each(|decl| elaborate_decl_and_register(&mut env, decl).map(|_| ()));
    assert!(
        result.is_err(),
        "a mutual block with an undefined type reference must be REJECTED, not silently accepted"
    );
    // And nothing from the rejected family may leak into the environment.
    assert!(
        env.get_inductive(&Name::from_string("Foo")).is_none(),
        "rejected Foo must not be registered"
    );
    assert!(
        env.get_inductive(&Name::from_string("Bar")).is_none(),
        "rejected Bar must not be registered"
    );
}

#[test]
fn test_single_inductive_still_registers() {
    let env = elab_all("inductive Wrap where\n  | mk : Nat -> Wrap\n");
    assert!(
        env.get_inductive(&Name::from_string("Wrap")).is_some(),
        "single inductive must still register"
    );
    assert!(
        env.get_constructor(&Name::from_string("Wrap.mk")).is_some(),
        "single inductive constructor must still register"
    );
}
