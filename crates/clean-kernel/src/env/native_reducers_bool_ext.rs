// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Bool and Nat native reducers for the kernel type checker.
//!
//! Provides fast-path native reducers for:
//! - `Bool.beq` (boolean equality)
//! - `Nat.gcd` (greatest common divisor)
//!
//! Other Nat operations (div, mod, beq, ble, pow, land, lor, xor,
//! shiftLeft, shiftRight) are registered in `native_reducers_arith.rs`
//! which provides BigNat-capable implementations.
//!
//! These complement the existing native reducers in `native_reducers.rs` (decEq,
//! String ops) and `native_reducers_arith.rs` (Nat arithmetic/comparison/bitwise).
//! The WHNF reduction path in `tc/reduction/nat.rs` already handles these
//! operations, but native reducers provide a faster path that fires before
//! delta unfolding.
//!
//! Part of #3134. Deduplication: Part of #3251.

use crate::env::native_reducers_arith::get_nat_val;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use std::sync::LazyLock;

/// Well-known names for extended native reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    // Bool
    pub(crate) static BOOL_BEQ: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.beq"));

    // Nat arithmetic (unique to this module)
    pub(crate) static NAT_GCD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.gcd"));
}

/// Extract a Bool value from a constructor expression.
/// `Bool.true` -> Some(true), `Bool.false` -> Some(false)
pub(crate) fn get_bool_val(e: &Expr) -> Option<bool> {
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

/// Build a Bool constant expression.
pub(crate) fn mk_bool(val: bool) -> Expr {
    static BOOL_TRUE_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
    static BOOL_FALSE_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
    if val {
        Expr::const_(BOOL_TRUE_NAME.clone(), vec![])
    } else {
        Expr::const_(BOOL_FALSE_NAME.clone(), vec![])
    }
}

// === Bool reducers ===

/// Native reducer for `Bool.beq : Bool → Bool → Bool`.
pub(crate) fn reduce_bool_beq(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_bool_val(args[0])?;
    let b = get_bool_val(args[1])?;
    Some(mk_bool(a == b))
}

// === Nat.gcd reducer ===

/// Euclidean GCD for u64.
pub(crate) fn nat_gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Native reducer for `Nat.gcd : Nat → Nat → Nat`.
pub(crate) fn reduce_nat_gcd(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let a = get_nat_val(args[0])?;
    let b = get_nat_val(args[1])?;
    Some(Expr::nat_lit(nat_gcd(a, b)))
}

/// Register Bool.beq and Nat.gcd native reducers on the environment.
///
/// All other Nat operations (div, mod, beq, ble, pow, land, lor, xor,
/// shiftLeft, shiftRight) are registered in `init_arith_native_reducers`
/// which provides BigNat-capable implementations. Part of #3251.
impl Environment {
    pub(crate) fn init_bool_ext_native_reducers(&mut self) {
        // Bool
        self.register_native_reducer(names::BOOL_BEQ.clone(), reduce_bool_beq);

        // Nat.gcd (unique to this module — no arith equivalent)
        self.register_native_reducer(names::NAT_GCD.clone(), reduce_nat_gcd);
    }
}

#[cfg(test)]
#[path = "native_reducers_bool_ext_tests.rs"]
mod tests;
