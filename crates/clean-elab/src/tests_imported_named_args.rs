// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Named arguments on an olean-IMPORTED constant bind by the binder names of
//! its type, recorded at import (`clean_olean::type_binder_names`) because
//! the kernel keeps none (`LT.lt (self := i)`,
//! `compare_of_injective_eq_compareOfLessAndEq`, measured 2026-09-12). The
//! import is simulated the way the loader leaves it: a kernel declaration with
//! no surface parameter table, plus its recorded type binder names.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};
use clean_parser::parse_file;

fn imported_axiom(env: &mut Environment) {
    // axiom myRel : {α : Type} → (a b : α) → Prop
    let ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("myRel"),
        level_params: vec![],
        type_: ty,
    })
    .expect("axiom myRel");
}

fn record_names(env: &mut Environment, names: &[&str]) {
    env.get_ext_state_mut::<clean_olean::TypeBinderNameState>(clean_olean::type_binder_name_idx())
        .names
        .insert(
            Name::from_string("myRel"),
            names.iter().map(|n| Name::from_string(n)).collect(),
        );
}

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

#[test]
fn test_named_args_on_imported_constant_bind_by_recorded_type_names() {
    let mut env = Environment::with_prelude();
    imported_axiom(&mut env);
    record_names(&mut env, &["α", "a", "b"]);
    // Out-of-order named arguments land in their named slots.
    let src = "theorem t : myRel (b := (2 : Nat)) (a := 1) = myRel 1 2 := rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("named arguments must bind by the recorded names: {e}");
    }
}

#[test]
fn test_named_args_on_imported_constant_without_names_stay_refused() {
    let mut env = Environment::with_prelude();
    imported_axiom(&mut env);
    let src = "theorem t : myRel (b := (2 : Nat)) (a := 1) = myRel 1 2 := rfl\n";
    let err = elab(&mut env, src).expect("no recorded names: the call must be refused");
    assert!(err.contains("binder names"), "got: {err}");
}

#[test]
fn test_named_arg_with_an_unknown_name_is_refused() {
    let mut env = Environment::with_prelude();
    imported_axiom(&mut env);
    record_names(&mut env, &["α", "a", "b"]);
    let src = "theorem t : myRel (c := (2 : Nat)) 1 = myRel 1 2 := rfl\n";
    let err = elab(&mut env, src).expect("an unknown name must be refused");
    assert!(err.contains("unknown named argument"), "got: {err}");
}
