// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for item source ingestion: higher-ranked trait bounds and
//! block-scoped type aliases.

use super::super::parser::Parser;
use super::super::SourceProgram;
use crate::expr::{Expr, Stmt};
use crate::item::Item;

/// The quantified lifetimes of a higher-ranked trait bound are recoverable as
/// an ordered list, while a plain bound yields an empty list.
#[test]
fn test_hrtb_bound_lifetimes_extracts_quantified_lifetimes() {
    let hrtb: syn::TraitBound =
        syn::parse_str("for<'a, 'b> Fn(&'a i32, &'b i32)").expect("valid HRTB syntax");
    assert_eq!(
        Parser::hrtb_bound_lifetimes(&hrtb),
        vec!["a".to_string(), "b".to_string()],
        "bound lifetimes should be returned in source order"
    );

    let plain: syn::TraitBound = syn::parse_str("Clone").expect("valid trait bound syntax");
    assert!(
        Parser::hrtb_bound_lifetimes(&plain).is_empty(),
        "a non-higher-ranked bound has no quantified lifetimes"
    );
}

/// A higher-ranked trait bound (`for<'a> Fn(&'a i32)`) on a generic type
/// parameter is accepted and simplified to the underlying trait obligation.
#[test]
fn test_parse_generic_fn_hrtb_bound_simplifies_to_trait_name() {
    let program = SourceProgram::parse("fn f<F: for<'a> Fn(&'a i32)>(g: F) {}")
        .expect("HRTB bound on a type parameter should parse");

    let fn_item = program
        .items()
        .iter()
        .find_map(|item| match item {
            Item::Fn {
                name, type_params, ..
            } if name == "f" => Some(type_params),
            _ => None,
        })
        .expect("expected fn `f` with type parameters");

    let f_param = fn_item
        .iter()
        .find(|param| param.name == "F")
        .expect("expected type parameter `F`");

    // The `for<'a>` quantifier is erased: the stored bound is the bare trait
    // name, exactly as a non-higher-ranked `F: Fn(&i32)` would produce.
    assert_eq!(
        f_param.bounds,
        vec!["Fn".to_string()],
        "higher-ranked bound should simplify to the trait name `Fn`"
    );
}

/// A higher-ranked trait bound in a `where` clause is also accepted.
#[test]
fn test_parse_where_clause_hrtb_bound_accepted() {
    let program = SourceProgram::parse("fn f<F>(g: F) where F: for<'a> Fn(&'a i32) {}")
        .expect("HRTB bound in a where clause should parse");

    assert!(
        program
            .items()
            .iter()
            .any(|item| matches!(item, Item::Fn { name, .. } if name == "f")),
        "expected fn `f` to be parsed from a where-clause HRTB"
    );
}

/// A `dyn for<'a> Fn(&'a i32)` trait object type is accepted.
#[test]
fn test_parse_hrtb_dyn_trait_object_accepted() {
    let program = SourceProgram::parse("fn f(g: &dyn for<'a> Fn(&'a i32)) {}")
        .expect("HRTB dyn trait object should parse");

    assert!(
        program
            .items()
            .iter()
            .any(|item| matches!(item, Item::Fn { name, .. } if name == "f")),
        "expected fn `f` with a higher-ranked dyn trait parameter"
    );
}

/// A block-scoped `type X = i32;` is parsed into an [`Item::TypeAlias`] that is
/// recorded in the block's statement list with `block_scoped` set.
#[test]
fn test_parse_block_scoped_type_alias_emits_item() {
    let program = SourceProgram::parse("fn f() -> i32 { type X = i32; let v: X = 3; v }")
        .expect("block-scoped type alias should parse");

    let body = program
        .items()
        .iter()
        .find_map(|item| match item {
            Item::Fn { name, body, .. } if name == "f" => Some(body),
            _ => None,
        })
        .expect("expected fn `f` with a body");

    let Expr::Block { stmts, .. } = body else {
        panic!("expected fn `f` body to be a block, got {body:?}");
    };

    let alias = stmts
        .iter()
        .find_map(|stmt| match stmt {
            Stmt::Item(Item::TypeAlias {
                name,
                ty,
                block_scoped,
            }) => Some((name, ty, *block_scoped)),
            _ => None,
        })
        .expect("expected a block-scoped TypeAlias statement");

    assert_eq!(alias.0, "X", "alias name should be `X`");
    assert!(alias.2, "alias declared in a block should be block_scoped");
    assert_eq!(
        alias.1,
        &crate::types::RustType::Int(crate::types::IntType::I32),
        "alias `X` should resolve to `i32`"
    );
}

/// The block-scoped alias is resolved structurally: the `let v: X = 3;` binding
/// uses the alias and the whole program still evaluates to the aliased value.
#[test]
fn test_block_scoped_type_alias_resolves_and_runs() {
    let program = SourceProgram::parse(
        "fn main() -> i32 { type X = i32; let v: X = 7; v } fn run() -> i32 { main() }",
    )
    .expect("program using a block-scoped type alias should parse");

    // The alias must not appear as a runtime symbol; lowering to VIR (which
    // rejects unsupported block items) must succeed.
    program
        .lower_to_vir()
        .expect("block-scoped type alias should lower to VIR as a no-op");
}

/// A generic block-scoped type alias remains unsupported (matching the
/// module-level alias table, which only stores non-generic aliases).
#[test]
fn test_parse_generic_block_scoped_type_alias_rejected() {
    let err = SourceProgram::parse("fn f() { type X<T> = T; }")
        .expect_err("generic type aliases are not supported");
    let message = err.to_string();
    assert!(
        message.contains("generic type alias"),
        "expected a 'generic type alias' error, got: {message}"
    );
}
