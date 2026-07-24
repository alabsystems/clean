// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantically honest fixture helpers for proof-reconstruction success tests.
//!
//! These helpers create ay terms that faithfully represent the intended
//! arithmetic semantics: real variables map to FVars, constants use native ay
//! integer/rational constructors, and raw comparison builders preserve
//! unsimplified atoms without pretending ay variables are constants.

use super::super::super::VariableMapping;
use ay::Sort;
use ay_core::TermStore;
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

/// Helper: register an Int variable in both the term store and variable mapping.
pub(in super::super) fn register_int_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    id: u64,
) -> ay_core::TermId {
    let tid = terms.mk_var(name, Sort::Int);
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var(name, Expr::fvar(FVarId::new(id)), int_ty);
    tid
}

pub(in super::super) fn register_int_const(
    terms: &mut TermStore,
    _map: &mut VariableMapping,
    _name: &str,
    value: u64,
) -> ay_core::TermId {
    terms.mk_int(num_bigint::BigInt::from(value))
}

/// Helper: register a Real variable in both the term store and variable mapping.
pub(in super::super) fn register_real_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    id: u64,
) -> ay_core::TermId {
    let tid = terms.mk_var(name, Sort::Real);
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    map.register_var(name, Expr::fvar(FVarId::new(id)), real_ty);
    tid
}

/// Helper: create an integer-valued Real constant via Constant::Rational.
///
/// ay's LRA theory stores real constants as `Constant::Rational(n/1)` even for
/// integer values. This tests the Rational→Int translation path in
/// `term_translate.rs`.
pub(in super::super) fn mk_real_int_const(terms: &mut TermStore, value: i64) -> ay_core::TermId {
    use num_rational::BigRational;

    let rat = BigRational::from(num_bigint::BigInt::from(value));
    terms.mk_rational(rat)
}

/// Create a raw `<=` predicate via `mk_app` that bypasses constant-folding.
///
/// `terms.mk_le(a, b)` constant-folds when both `a` and `b` are native ay
/// constants, collapsing the atom to `True`/`False` and erasing the structure
/// that `as_not`/`parse_bound` need. This helper uses a raw `Symbol::Named`
/// application instead, preserving the comparison structure for test fixtures
/// that use native `register_int_const` / `mk_real_int_const` constants.
pub(in super::super) fn mk_raw_le(
    terms: &mut TermStore,
    lhs: ay_core::TermId,
    rhs: ay_core::TermId,
) -> ay_core::TermId {
    terms.mk_app(
        ay_core::Symbol::Named("<=".to_string()),
        vec![lhs, rhs],
        Sort::Bool,
    )
}

/// Create a raw `<` predicate via `mk_app` that bypasses constant-folding.
pub(in super::super) fn mk_raw_lt(
    terms: &mut TermStore,
    lhs: ay_core::TermId,
    rhs: ay_core::TermId,
) -> ay_core::TermId {
    terms.mk_app(
        ay_core::Symbol::Named("<".to_string()),
        vec![lhs, rhs],
        Sort::Bool,
    )
}

/// Create a raw `>=` predicate via `mk_app` that bypasses constant-folding.
pub(in super::super) fn mk_raw_ge(
    terms: &mut TermStore,
    lhs: ay_core::TermId,
    rhs: ay_core::TermId,
) -> ay_core::TermId {
    terms.mk_app(
        ay_core::Symbol::Named(">=".to_string()),
        vec![lhs, rhs],
        Sort::Bool,
    )
}

/// Create a raw `>` predicate via `mk_app` that bypasses constant-folding.
pub(in super::super) fn mk_raw_gt(
    terms: &mut TermStore,
    lhs: ay_core::TermId,
    rhs: ay_core::TermId,
) -> ay_core::TermId {
    terms.mk_app(
        ay_core::Symbol::Named(">".to_string()),
        vec![lhs, rhs],
        Sort::Bool,
    )
}
