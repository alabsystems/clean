// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::env::{Declaration, EnvError, Environment};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

// Lean's list-backed String constructor, without an optional conversion alias.
fn list_string(text: &str) -> Expr {
    let mut chars = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        c("Char"),
    );
    for ch in text.chars().rev() {
        chars = Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [
                c("Char"),
                Expr::app(c("Char.ofNat"), Expr::nat_lit(u64::from(u32::from(ch)))),
                chars,
            ],
        );
    }
    Expr::app(c("String.mk"), chars)
}

#[test]
fn list_backed_string_literals_do_not_require_of_list_alias() {
    let mut env = Environment::with_prelude();
    assert!(env.forget_decl(&Name::from_string("String.ofList")));
    let tc = TypeChecker::new(&env);
    for text in ["", "enum", "struct", "héllo", "😀\0"] {
        let constructor = list_string(text);
        let ty = tc
            .infer_type(&constructor)
            .expect("constructor is well typed");
        assert!(tc.is_def_eq(&ty, &c("String")));
        assert!(tc.is_def_eq(&Expr::str_lit(text), &constructor), "{text:?}");
        assert!(tc.is_def_eq(&constructor, &Expr::str_lit(text)), "{text:?}");
        assert!(!tc.is_def_eq(&Expr::str_lit("different"), &constructor));
    }
}

#[test]
fn missing_character_definition_does_not_authorize_literal_expansion() {
    let mut env = Environment::with_prelude();
    assert!(env.forget_decl(&Name::from_string("String.ofList")));
    assert!(env.forget_decl(&Name::from_string("Char.ofNat")));
    let tc = TypeChecker::new(&env);
    assert!(!tc.is_def_eq(&Expr::str_lit("enum"), &list_string("enum")));
}

fn constant_string_function(name: &str) -> Declaration {
    let list_char = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        c("Char"),
    );
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, list_char.clone(), c("String")),
        value: Expr::lam(BinderInfo::Default, list_char, Expr::str_lit("")),
        is_reducible: true,
    }
}

#[test]
fn unreviewed_conversion_alias_does_not_authorize_literal_expansion() {
    let mut env = Environment::with_prelude();
    let alias = Name::from_string("String.ofList");
    assert!(env.forget_decl(&alias));
    env.add_decl(constant_string_function("String.ofList"))
        .expect("well-typed conversion function");
    assert!(!env.native_fold_authorized(&alias));
    let tc = TypeChecker::new(&env);
    assert!(!tc.is_def_eq(&Expr::str_lit("enum"), &list_string("enum")));
    assert!(tc.is_def_eq(&Expr::str_lit("enum"), &Expr::str_lit("enum")));
}

#[test]
fn function_body_cannot_authorize_a_constructor_expansion() {
    let mut env = Environment::with_prelude();
    assert!(env.forget_decl(&Name::from_string("String.ofList")));
    assert!(env.forget_decl(&Name::from_string("String.mk")));
    match env.add_decl(constant_string_function("String.mk")) {
        Ok(()) => {
            let tc = TypeChecker::new(&env);
            assert!(!tc.is_def_eq(&Expr::str_lit("enum"), &list_string("enum")));
        }
        Err(EnvError::DuplicateName(name)) => assert_eq!(name, Name::from_string("String.mk")),
        Err(error) => panic!("unexpected replacement refusal: {error:?}"),
    }
}
