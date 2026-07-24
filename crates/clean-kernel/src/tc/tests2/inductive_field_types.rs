// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for inductive field type handling (nested, higher-order, self-referencing).
//!
//! Extracted from mutual_inductive.rs for file-size compliance.

use super::*;

/// Create an environment with Nat registered.
fn make_nat_env() -> (Environment, Expr) {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    let nat_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat,
            type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::pi(BinderInfo::Default, nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    };
    env.add_inductive(nat_decl).expect("add Nat");
    (env, nat_ref)
}

#[test]
fn test_nested_inductive_wrapper() {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};
    use crate::level::Level;

    let mut env = Environment::new();
    let u = Name::from_string("u");
    let wrapped = Name::from_string("Wrapped");

    // Wrapped : Sort u -> Type u, mirroring Lean's PLift. The `succ u` result
    // is provably nonzero, so Wrapped keeps large elimination under the elim
    // gate ([R1]); a `Sort u` result would make it Prop-only.
    let wrapped_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
    );
    let wrapped_a_inner = Expr::app(
        Expr::const_(wrapped.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(1),
    );
    let wrap_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::param(u.clone()))),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), wrapped_a_inner),
    );

    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: wrapped.clone(),
            type_: wrapped_type,
            constructors: vec![Constructor {
                name: Name::from_string("Wrapped.wrap"),
                type_: wrap_type,
            }],
        }],
    };
    env.add_inductive(decl).expect("add Wrapped");

    for suffix in &["rec", "casesOn", "recOn"] {
        let name = Name::from_string(&format!("Wrapped.{suffix}"));
        assert!(env.get_recursor(&name).is_some(), "{name} should exist");
    }

    let rec = env
        .get_recursor(&Name::from_string("Wrapped.rec"))
        .expect("Wrapped.rec");
    assert_eq!(rec.num_params, 1);
    assert_eq!(rec.num_minors, 1);
    assert_eq!(rec.rules[0].num_fields, 1);
    assert!(
        !rec.rules[0].recursive_fields[0],
        "alpha field not recursive"
    );
}

#[test]
fn test_inductive_with_function_type_field() {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let (mut env, nat_ref) = make_nat_env();
    let ho = Name::from_string("HO");
    let ho_ref = Expr::const_(ho.clone(), vec![]);
    let nat_to_nat = Expr::pi(BinderInfo::Default, nat_ref.clone(), nat_ref);
    let mk_type = Expr::pi(BinderInfo::Default, nat_to_nat, ho_ref);

    let ho_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ho,
            type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            constructors: vec![Constructor {
                name: Name::from_string("HO.mk"),
                type_: mk_type,
            }],
        }],
    };
    env.add_inductive(ho_decl).expect("add HO");

    let rec = env
        .get_recursor(&Name::from_string("HO.rec"))
        .expect("HO.rec");
    assert_eq!(rec.num_minors, 1);
    assert_eq!(rec.rules[0].num_fields, 1);
    assert!(
        !rec.rules[0].recursive_fields[0],
        "function field not recursive"
    );
}

/// Add Unit to an environment, returning its ref.
fn add_unit(env: &mut Environment) -> Expr {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let unit = Name::from_string("Unit");
    let unit_ref = Expr::const_(unit.clone(), vec![]);
    let unit_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: unit,
            type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            constructors: vec![Constructor {
                name: Name::from_string("Unit.unit"),
                type_: unit_ref.clone(),
            }],
        }],
    };
    env.add_inductive(unit_decl).expect("add Unit");
    unit_ref
}

#[test]
fn test_inductive_with_self_referencing_function() {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let (mut env, nat_ref) = make_nat_env();
    let unit_ref = add_unit(&mut env);

    let stream = Name::from_string("Stream");
    let stream_ref = Expr::const_(stream.clone(), vec![]);
    let thunk_type = Expr::pi(BinderInfo::Default, unit_ref, stream_ref.clone());
    let cons_type = Expr::pi(
        BinderInfo::Default,
        nat_ref,
        Expr::pi(BinderInfo::Default, thunk_type, stream_ref),
    );

    let stream_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: stream,
            type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            constructors: vec![Constructor {
                name: Name::from_string("Stream.cons"),
                type_: cons_type,
            }],
        }],
    };
    env.add_inductive(stream_decl).expect("add Stream");

    let rec = env
        .get_recursor(&Name::from_string("Stream.rec"))
        .expect("Stream.rec");
    assert_eq!(rec.num_minors, 1);
    assert_eq!(rec.rules[0].num_fields, 2);
    assert!(!rec.rules[0].recursive_fields[0], "Nat field not recursive");
    assert!(rec.rules[0].recursive_fields[1], "thunk field is recursive");
}
