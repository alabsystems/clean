// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public prelude headers measured on genuine Lean430,435 and436-rc2.
//! A class takes its carrier explicitly; its constructor infers that carrier.

use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Name};

const FAMILIES: [&str; 6] = ["Neg", "Repr", "ToString", "Min", "Max", "Ord"];

fn first_mode(ty: &Expr) -> BinderInfo {
    let ExprKind::Pi(mode, _, _) = ty.kind() else {
        panic!("the initialized class header must have a carrier binder");
    };
    mode.info
}

#[test]
fn public_class_constants_take_explicit_carriers() {
    let env = Environment::with_prelude();
    let actual: Vec<_> = FAMILIES
        .iter()
        .map(|name| {
            let info = env
                .get_const(&Name::from_string(name))
                .expect("initialized class constant");
            (*name, first_mode(&info.type_))
        })
        .collect();
    let expected: Vec<_> = FAMILIES
        .iter()
        .map(|name| (*name, BinderInfo::Default))
        .collect();
    assert_eq!(actual, expected);
}

#[test]
fn public_inductive_headers_take_explicit_carriers() {
    let env = Environment::with_prelude();
    let actual: Vec<_> = FAMILIES
        .iter()
        .map(|name| {
            let info = env
                .get_inductive(&Name::from_string(name))
                .expect("initialized class inductive");
            (*name, first_mode(&info.type_))
        })
        .collect();
    let expected: Vec<_> = FAMILIES
        .iter()
        .map(|name| (*name, BinderInfo::Default))
        .collect();
    assert_eq!(actual, expected);
}

#[test]
fn public_class_constructors_infer_the_carrier() {
    let env = Environment::with_prelude();
    let actual: Vec<_> = FAMILIES
        .iter()
        .map(|name| {
            let info = env
                .get_constructor(&Name::from_string(name).str("mk"))
                .expect("initialized class constructor");
            (*name, first_mode(&info.type_))
        })
        .collect();
    let expected: Vec<_> = FAMILIES
        .iter()
        .map(|name| (*name, BinderInfo::Implicit))
        .collect();
    assert_eq!(actual, expected);
}
