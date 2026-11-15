// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Name literals: `` `foo `` and ``` ``foo ```.
//!
//! `` `N.f `` is the `Lean.Name` value `Name.str (Name.str .anonymous "N") "f"`.
//! It used to elaborate to the declaration `N.f` ITSELF (a quoted identifier
//! went back through `syntax_to_surface` as the identifier), so with `import
//! Lean`, ``s.contains `foo`` read "expected Lean.Name, got Nat".
//!
//! ``` ``f ``` is Lean's `doubleQuotedName`: the name RESOLVED to the one
//! declaration `f` names in scope (`realizeGlobalConstNoOverload`). The lexer
//! used to split it into an empty quote applied to `` `f ``, so every use read
//! "Too many arguments" (upstream tests/elab/2077.lean,
//! ``` .toUnfold.contains <| ``foo ```).
//!
//! Ground truth, pinned v4.30.0-rc2: inside `namespace N` with `N.f` declared,
//! ``` ``f ``` equals `` `N.f `` by `rfl`; an unknown name is `Unknown
//! constant`; under `open N in` with both a root `f` and `N.f`, ``` ``f ``` is
//! `ambiguous identifier`.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Environment, Expr, Name};
use clean_parser::parse_file;

fn elab(env: &mut Environment, src: &str) -> Result<(), String> {
    let decls = parse_file(src).map_err(|e| format!("parse: {e:?}"))?;
    for d in &decls {
        elaborate_decl_and_register_with_warning(env, d).map_err(|e| format!("{e:?}"))?;
    }
    Ok(())
}

fn value(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .and_then(|info| info.value.clone())
        .unwrap_or_else(|| panic!("{name} should be registered with a value"))
}

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Clean's prelude plus `Lean.Name` exactly as Lean's prelude declares its
/// kernel shape: `anonymous | str (pre : Name) (s : String) | num (pre : Name)
/// (i : Nat)`.
fn env_with_lean_name() -> Environment {
    let mut env = Environment::with_prelude();
    let name_ty = c("Lean.Name");
    let arrow = |dom: Expr, cod: Expr| Expr::pi(BinderInfo::Default, dom, cod);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string("Lean.Name"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Lean.Name.anonymous"),
                    type_: name_ty.clone(),
                },
                Constructor {
                    name: Name::from_string("Lean.Name.str"),
                    type_: arrow(name_ty.clone(), arrow(c("String"), name_ty.clone())),
                },
                Constructor {
                    name: Name::from_string("Lean.Name.num"),
                    type_: arrow(name_ty.clone(), arrow(c("Nat"), name_ty.clone())),
                },
            ],
        }],
    })
    .expect("Lean.Name should declare");
    env
}

/// `Name.str (Name.str .anonymous "N") "f"`.
fn quoted_n_f() -> Expr {
    let inner = Expr::app(
        Expr::app(c("Lean.Name.str"), c("Lean.Name.anonymous")),
        Expr::str_lit("N"),
    );
    Expr::app(Expr::app(c("Lean.Name.str"), inner), Expr::str_lit("f"))
}

#[test]
fn test_single_quoted_name_is_a_name_value_not_the_declaration() {
    let mut env = env_with_lean_name();
    let src = "namespace N\n\
               def f : Nat := 1\n\
               end N\n\
               def viaSingle := `N.f\n";
    if let Err(e) = elab(&mut env, src) {
        panic!("`N.f must elaborate as a Lean.Name literal: {e}");
    }
    assert_eq!(
        value(&env, "viaSingle"),
        quoted_n_f(),
        "`N.f is the NAME `N.f, not the declaration N.f"
    );
}

#[test]
fn test_double_quoted_name_is_the_resolved_declaration() {
    let mut env = env_with_lean_name();
    let src = "namespace N\n\
               def f : Nat := 1\n\
               def viaDouble := ``f\n\
               end N\n";
    if let Err(e) = elab(&mut env, src) {
        panic!("``f inside `namespace N` must elaborate to the name `N.f: {e}");
    }
    assert_eq!(
        value(&env, "N.viaDouble"),
        quoted_n_f(),
        "``f must quote the RESOLVED name N.f"
    );
}

#[test]
fn test_double_quoted_name_refuses_an_unknown_constant() {
    let mut env = env_with_lean_name();
    let refused = elab(&mut env, "def bad := ``noSuchDeclaration\n");
    assert!(
        refused
            .as_ref()
            .is_err_and(|e| e.contains("unknown constant")),
        "an unresolvable ``name is `unknown constant`, as in Lean: {refused:?}"
    );
}

#[test]
fn test_double_quoted_name_refuses_an_ambiguous_one() {
    let mut env = env_with_lean_name();
    let src = "def f : Nat := 0\n\
               namespace N\n\
               def f : Nat := 1\n\
               end N\n\
               open N in\n\
               def which := ``f\n";
    let refused = elab(&mut env, src);
    assert!(
        refused
            .as_ref()
            .is_err_and(|e| e.contains("ambiguous identifier")),
        "under `open N in`, ``f names both `f` and `N.f`: Lean refuses it: {refused:?}"
    );
}
