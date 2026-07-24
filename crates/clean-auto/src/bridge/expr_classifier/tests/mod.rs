// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the shared expression classifier.
//!
//! Split into submodules by category:
//! - connective: Eq, Ne, And, Or, Not, Iff, True, False, BEq, MData, Implies, Atom
//! - comparison: Lt, Le, Gt, Ge (direct, typeclass, bare aliases)
//! - arithmetic: Add, Sub, Mul, Div, Mod, Neg (direct, typeclass, H-forms)
//! - quantifier: Forall, Exists (including MData predicate stripping)

mod arithmetic;
mod comparison;
mod connective;
mod quantifier;

use super::*;
use clean_kernel::name::Name;
use clean_kernel::Level;

pub(super) fn mk_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

pub(super) fn mk_const_u(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

pub(super) fn mk_fvar(id: u64) -> Expr {
    Expr::fvar(clean_kernel::FVarId::new(id))
}

pub(super) fn app2(f: Expr, a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(f, a), b)
}

pub(super) fn app3(f: Expr, a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::app(Expr::app(Expr::app(f, a), b), c)
}

#[test]
fn test_name_eq_str_matches_dotted_components_without_allocation() {
    let name = Name::from_string("Nat.add");
    assert!(name_eq_str(&name, "Nat.add"));
    assert!(!name_eq_str(&name, "Nat.mul"));

    let numbered = Name::from_string("Nat.1");
    assert!(name_eq_str(&numbered, "Nat.1"));
}
