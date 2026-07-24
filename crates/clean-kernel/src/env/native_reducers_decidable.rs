// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native reducers for Decidable proposition instances.
//!
//! Provides fast-path computation for decidable ordering and equality
//! instances that would otherwise require expensive delta/iota reduction
//! chains through recursive definitions:
//!
//! - `instDecidableNatLt` — `(a b : Nat) -> Decidable (Nat.lt a b)`
//! - `instDecidableNatLe` — `(a b : Nat) -> Decidable (Nat.le a b)`
//! - `instDecidableEqNat` — `(a b : Nat) -> Decidable (a = b)` (alias)
//! - `instDecidableEqBool` — `(a b : Bool) -> Decidable (a = b)` (alias)
//! - `instDecidableEqString` — `(a b : String) -> Decidable (a = b)` (alias)
//! - `instDecidableEqFin` — `{n : Nat} -> (a b : Fin n) -> Decidable (a = b)`
//! - `Fin.decEq` — same as instDecidableEqFin
//!
//! These reducers are critical for .olean verification performance. Without
//! them, `instDecidableNatLt 3 5` requires unfolding through Nat.rec and
//! multiple iota reduction steps. With native reducers, it's O(1).
//!
//! Reference: Lean 4 type_checker.cpp native reduction, Init.Prelude Decidable.

use crate::env::native_reducers::mk_dec_is_true;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;
use std::sync::LazyLock;

/// Well-known names for Decidable native reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static INST_DECIDABLE_NAT_LT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableNatLt"));
    pub(crate) static INST_DECIDABLE_NAT_LE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableNatLe"));
    pub(crate) static INST_DECIDABLE_EQ_NAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableEqNat"));
    pub(crate) static INST_DECIDABLE_EQ_BOOL: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableEqBool"));
    pub(crate) static INST_DECIDABLE_EQ_STRING: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableEqString"));
    pub(crate) static INST_DECIDABLE_EQ_FIN: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableEqFin"));
    pub(crate) static FIN_DEC_EQ: LazyLock<Name> = LazyLock::new(|| Name::from_string("Fin.decEq"));
}

/// Decidable type/constructor name constants.
static NAT_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat"));
static BOOL_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool"));
static STRING_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("String"));

/// Extract a Nat value from an expression literal.
fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

/// Extract a Bool value from a constructor expression.
fn get_bool_val(e: &Expr) -> Option<bool> {
    let head = e.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
        static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
        if *name == *BOOL_TRUE {
            return Some(true);
        }
        if *name == *BOOL_FALSE {
            return Some(false);
        }
    }
    None
}

/// Extract a String value from an expression literal.
fn get_string_val(e: &Expr) -> Option<&str> {
    match e.kind() {
        ExprKind::Lit(Literal::String(s)) => Some(s),
        _ => None,
    }
}

/// Native reducer for `instDecidableNatLt`.
///
/// `(a b : Nat) -> Decidable (Nat.lt a b)` — compares two Nat literals.
pub(crate) fn reduce_inst_decidable_nat_lt(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_val(args[0])?;
    let b = get_nat_val(args[1])?;
    Some(super::native_reducers::mk_nat_lt_dec(
        args[0],
        args[1],
        a < b,
    ))
}

/// Native reducer for `instDecidableNatLe`.
///
/// `(a b : Nat) -> Decidable (Nat.le a b)` — compares two Nat literals.
pub(crate) fn reduce_inst_decidable_nat_le(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_val(args[0])?;
    let b = get_nat_val(args[1])?;
    Some(super::native_reducers::mk_nat_le_dec(
        args[0],
        args[1],
        a <= b,
    ))
}

/// Native reducer for `instDecidableEqNat`.
///
/// `(a b : Nat) -> Decidable (a = b)` — equivalent to `Nat.decEq`.
pub(crate) fn reduce_inst_decidable_eq_nat(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_val(args[0])?;
    let b = get_nat_val(args[1])?;
    if a == b {
        Some(mk_dec_is_true(&NAT_NAME, args[0]))
    } else {
        Some(super::native_reducers::mk_nat_dec_is_false(
            args[0], args[1],
        ))
    }
}

/// Native reducer for `instDecidableEqBool`.
///
/// `(a b : Bool) -> Decidable (a = b)` — equivalent to `Bool.decEq`.
pub(crate) fn reduce_inst_decidable_eq_bool(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bool_val(args[0])?;
    let b = get_bool_val(args[1])?;
    if a == b {
        Some(mk_dec_is_true(&BOOL_NAME, args[0]))
    } else {
        Some(super::native_reducers::mk_bool_dec_is_false(
            args[0], args[1],
        ))
    }
}

/// Native reducer for `instDecidableEqString`.
///
/// `(a b : String) -> Decidable (a = b)` — equivalent to `String.decEq`.
pub(crate) fn reduce_inst_decidable_eq_string(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_string_val(args[0])?;
    let b = get_string_val(args[1])?;
    if a == b {
        // Equal strings: `@Eq.refl String s` is a genuine, sorry-free proof.
        Some(mk_dec_is_true(&STRING_NAME, args[0]))
    } else {
        // Distinct strings need `List Char` disequality (not yet built); decline
        // rather than launder a `Decidable.isFalse sorryAx`.
        None
    }
}

/// Native reducer for `instDecidableEqFin` / `Fin.decEq`.
///
/// `{n : Nat} -> (a b : Fin n) -> Decidable (a = b)`.
///
/// Declines: a sound witness must build `@Eq (Fin n) a b` (an applied type, not
/// an atomic constant) and disprove it via the proof-irrelevant `@Fin.val n`
/// projection. The previous body built `@Eq Nat …`/`isFalse sorryAx`, which is
/// both type-incorrect and axiom-laundering, so we decline until a real Fin
/// disproof is wired. Sound by omission; the kernel falls back to iota.
pub(crate) fn reduce_fin_dec_eq(_args: &[&Expr]) -> Option<Expr> {
    None
}

/// Register all Decidable native reducers on the environment.
impl Environment {
    pub(crate) fn init_decidable_native_reducers(&mut self) {
        self.register_native_reducer(
            names::INST_DECIDABLE_NAT_LT.clone(),
            reduce_inst_decidable_nat_lt,
        );
        self.register_native_reducer(
            names::INST_DECIDABLE_NAT_LE.clone(),
            reduce_inst_decidable_nat_le,
        );
        self.register_native_reducer(
            names::INST_DECIDABLE_EQ_NAT.clone(),
            reduce_inst_decidable_eq_nat,
        );
        self.register_native_reducer(
            names::INST_DECIDABLE_EQ_BOOL.clone(),
            reduce_inst_decidable_eq_bool,
        );
        self.register_native_reducer(
            names::INST_DECIDABLE_EQ_STRING.clone(),
            reduce_inst_decidable_eq_string,
        );
        self.register_native_reducer(names::INST_DECIDABLE_EQ_FIN.clone(), reduce_fin_dec_eq);
        self.register_native_reducer(names::FIN_DEC_EQ.clone(), reduce_fin_dec_eq);
    }
}
