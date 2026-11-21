// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Source annotation/carrier controls. Authored without executing Rust or Lean.
use crate::test_support::file_verdicts::{assert_all_accepted, run_modules_env_messages};
use clean_kernel::env::{CompilerExternArity, CompilerExternEntry, CompilerExternMetadata};
use clean_kernel::{Environment, ExprKind, Name};

fn accepted(source: &str) -> Environment {
    let (env, verdicts) = run_modules_env_messages(&[source]);
    assert_all_accepted(&verdicts, source);
    env
}

fn domain(env: &Environment, subject: &str) -> clean_kernel::Expr {
    let info = env
        .get_const(&Name::from_string(subject))
        .expect("actual registered target");
    let ExprKind::Pi(_, domain, _) = info.type_.kind() else {
        panic!("declared telescope")
    };
    domain.as_ref().clone()
}

#[test]
fn fresh_source_borrowed_domains_remain_exact_mdata_after_registration() {
    let env = accepted(
        "def borrowedIdentity (s : @& String) : String := s\n\
        axiom borrowedArrow : @& String → Nat\n\
        axiom ordinaryArrow : String → Nat\n\
        axiom borrowedArray : @& Array Nat → Nat\n",
    );
    for subject in ["borrowedIdentity", "borrowedArrow", "borrowedArray"] {
        let ty = domain(&env, subject);
        let ExprKind::MData(map, _) = ty.kind() else {
            panic!("lost actual @& domain on {subject}: {ty:?}")
        };
        assert_eq!(
            map,
            &vec![(
                Name::from_string("borrowed"),
                clean_kernel::MDataValue::Bool(true)
            )]
        );
    }
    assert!(!matches!(
        domain(&env, "ordinaryArrow").kind(),
        ExprKind::MData(_, _)
    ));
    let restored =
        Environment::from_dag_bincode(&env.to_dag_bincode().expect("encode")).expect("restore");
    assert_eq!(
        domain(&restored, "borrowedIdentity"),
        domain(&env, "borrowedIdentity")
    );
}

#[test]
fn source_extern_metadata_and_actual_borrowing_travel_independently() {
    let env = accepted(
        "@[extern llvm \"same\" c \"different\"]\n\
        axiom arbitraryName (s : @& String) : Nat\n\
        @[extern \"lean_string_utf8_byte_size\"]\n\
        axiom ownedDespiteSymbol (s : String) : Nat\n",
    );
    let metadata = env
        .extern_metadata(&Name::from_string("arbitraryName"))
        .expect("carrier")
        .expect("registered");
    let CompilerExternMetadata::Complete(descriptor) = metadata else {
        panic!("lost descriptor")
    };
    assert_eq!(descriptor.arity, CompilerExternArity::Unspecified);
    assert_eq!(
        descriptor.entries,
        vec![
            CompilerExternEntry::Standard {
                backend: Name::from_string("llvm"),
                symbol: "same".into()
            },
            CompilerExternEntry::Standard {
                backend: Name::from_string("c"),
                symbol: "different".into()
            },
        ]
    );
    assert!(matches!(
        domain(&env, "arbitraryName").kind(),
        ExprKind::MData(_, _)
    ));
    assert!(!matches!(
        domain(&env, "ownedDespiteSymbol").kind(),
        ExprKind::MData(_, _)
    ));
}

#[test]
fn borrowed_wrapper_is_not_a_way_to_turn_a_value_into_a_type() {
    let env = Environment::with_prelude();
    let mut ctx = crate::ElabCtx::new(&env);
    let surface = clean_parser::parse_expr("@& 3").expect("the annotation parses");
    assert!(
        ctx.elaborate(&surface).is_err(),
        "borrowed data is still not a type"
    );
}
