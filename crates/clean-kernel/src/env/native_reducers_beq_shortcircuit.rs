// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! BEq typeclass short-circuit native reducers.
//!
//! When proof-by-reflection terms invoke `@BEq.beq Nat instBEqNat a b`,
//! the type checker must:
//! 1. Unfold `BEq.beq` to a structure projection
//! 2. Project from `instBEqNat` structure to get `Nat.beq`
//! 3. Apply `Nat.beq a b` (which then hits native reducer)
//!
//! Steps 1-2 waste heartbeat on structure projection. This module registers
//! a native reducer for `BEq.beq` that recognizes known instances and
//! delegates directly to the underlying `beq` computation, saving 2-4
//! WHNF steps per invocation.
//!
//! Similarly for `Ord.compare`, `LT.lt` projections with known instances.
//!
//! Part of #3210: reduce heartbeat usage for Init .olean type-checking.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;
use std::sync::LazyLock;

/// Well-known names for BEq short-circuit reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    // BEq.beq function
    pub(crate) static BEQ_BEQ: LazyLock<Name> = LazyLock::new(|| Name::from_string("BEq.beq"));

    // Known BEq instances
    pub(crate) static INST_BEQ_NAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instBEqNat"));
    pub(crate) static INST_BEQ_BOOL: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instBEqBool"));
    pub(crate) static INST_BEQ_STRING: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instBEqString"));
    pub(crate) static INST_BEQ_CHAR: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instBEqChar"));
    pub(crate) static INST_BEQ_INT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instBEqInt"));
    pub(crate) static INST_BEQ_UINT8: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instBEqUInt8"));
    pub(crate) static INST_BEQ_UINT16: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instBEqUInt16"));
    pub(crate) static INST_BEQ_UINT32: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instBEqUInt32"));
    pub(crate) static INST_BEQ_UINT64: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instBEqUInt64"));
    pub(crate) static INST_BEQ_USIZE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instBEqUSize"));
    pub(crate) static INST_BEQ_FIN: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instBEqFin"));
}

/// Build `Bool.true` constant.
fn mk_bool_true() -> Expr {
    static NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
    Expr::const_(NAME.clone(), vec![])
}

/// Build `Bool.false` constant.
fn mk_bool_false() -> Expr {
    static NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
    Expr::const_(NAME.clone(), vec![])
}

/// Build a Bool constant from a boolean value.
fn mk_bool(val: bool) -> Expr {
    if val {
        mk_bool_true()
    } else {
        mk_bool_false()
    }
}

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

/// Extract a Char value (as u32 code point) from a `Char.mk …` expression.
///
/// Delegates to [`super::native_reducers_char::char_code_point`], which handles
/// BOTH the pure-clean 1-field `Char.mk <nat>` and the real-olean 2-field
/// `Char.mk (UInt32.ofBitVec (BitVec…)) valid` constructor shapes (and bare Nat
/// literals); declines otherwise.
fn get_char_val(e: &Expr) -> Option<u32> {
    super::native_reducers_char::char_code_point(e).map(|n| n as u32)
}

/// Get the name of an instance argument (a 0-arg Const).
fn get_instance_name(e: &Expr) -> Option<&Name> {
    // Instance arguments are typically Const(instName, levels)
    // possibly with additional type arguments applied
    let head = e.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        return Some(name);
    }
    None
}

/// Native reducer for `BEq.beq`.
///
/// Signature: `BEq.beq : {α : Type u} → [inst : BEq α] → α → α → Bool`
/// Args after head extraction: [α, inst, a, b]
///
/// Recognizes known instances and delegates to the underlying `beq` logic:
/// - `instBEqNat` → `Nat.beq` (compare Nat literals)
/// - `instBEqBool` → Bool equality
/// - `instBEqString` → String equality
/// - `instBEqChar` → Char equality
/// - `instBEqUInt8/16/32/64/USize` → UInt equality (Nat literal comparison)
/// - `instBEqFin` → Fin equality (Nat literal comparison, skips bound arg)
fn reduce_beq_beq(args: &[&Expr]) -> Option<Expr> {
    // Need at least 4 args: [α, inst, a, b]
    if args.len() < 4 {
        return None;
    }
    let inst_name = get_instance_name(args[1])?;

    // instBEqNat: Nat.beq
    if *inst_name == *names::INST_BEQ_NAT {
        let a = get_nat_val(args[2])?;
        let b = get_nat_val(args[3])?;
        return Some(mk_bool(a == b));
    }

    // instBEqBool: Bool equality
    if *inst_name == *names::INST_BEQ_BOOL {
        let a = get_bool_val(args[2])?;
        let b = get_bool_val(args[3])?;
        return Some(mk_bool(a == b));
    }

    // instBEqString: String.beq
    if *inst_name == *names::INST_BEQ_STRING {
        let a = get_string_val(args[2])?;
        let b = get_string_val(args[3])?;
        return Some(mk_bool(a == b));
    }

    // instBEqChar: Char equality (compare code points)
    if *inst_name == *names::INST_BEQ_CHAR {
        let a = get_char_val(args[2])?;
        let b = get_char_val(args[3])?;
        return Some(mk_bool(a == b));
    }

    // instBEqUInt8/16/32/64/USize: UInt equality (compare Nat literals)
    if *inst_name == *names::INST_BEQ_UINT8
        || *inst_name == *names::INST_BEQ_UINT16
        || *inst_name == *names::INST_BEQ_UINT32
        || *inst_name == *names::INST_BEQ_UINT64
        || *inst_name == *names::INST_BEQ_USIZE
    {
        let a = get_nat_val(args[2])?;
        let b = get_nat_val(args[3])?;
        return Some(mk_bool(a == b));
    }

    // instBEqInt: Int equality
    if *inst_name == *names::INST_BEQ_INT {
        // Int values need special handling — delegate to get_int_val
        let a = get_int_val(args[2])?;
        let b = get_int_val(args[3])?;
        return Some(mk_bool(a == b));
    }

    // instBEqFin: Fin.beq (ignore the Nat bound in args[0])
    // BEq.beq args for Fin: [Fin n, instBEqFin n, a, b]
    // But instBEqFin takes n as an argument: @instBEqFin n
    // The actual values a, b are Nat literals after WHNF
    if *inst_name == *names::INST_BEQ_FIN {
        let a = get_nat_val(args[2])?;
        let b = get_nat_val(args[3])?;
        return Some(mk_bool(a == b));
    }

    None
}

/// Extract an Int value from an expression.
///
/// Lean 4 Int constructors: `Int.ofNat n` (non-negative) and
/// `Int.negSucc n` (= -(n+1)).
fn get_int_val(e: &Expr) -> Option<i64> {
    static INT_OF_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.ofNat"));
    static INT_NEG_SUCC: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.negSucc"));

    let head = e.get_app_fn();
    let args = e.get_app_args();
    if let ExprKind::Const(name, _) = head.kind() {
        if *name == *INT_OF_NAT && args.len() == 1 {
            let n = get_nat_val(args[0])?;
            return i64::try_from(n).ok();
        }
        if *name == *INT_NEG_SUCC && args.len() == 1 {
            let n = get_nat_val(args[0])?;
            let pos = i64::try_from(n).ok()?;
            return pos.checked_add(1).map(|v| -v);
        }
    }
    // Bare Nat literal (implicit Int.ofNat)
    if let Some(n) = get_nat_val(e) {
        return i64::try_from(n).ok();
    }
    None
}

/// Register the BEq short-circuit native reducer.
impl Environment {
    pub(crate) fn init_beq_shortcircuit_native_reducers(&mut self) {
        self.register_native_reducer(names::BEQ_BEQ.clone(), reduce_beq_beq);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;

    fn setup_env() -> Environment {
        let mut env = Environment::new();
        env.init_beq_shortcircuit_native_reducers();
        env
    }

    /// Test BEq.beq with instBEqNat on equal Nat literals.
    #[test]
    fn test_beq_beq_nat_equal() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instBEqNat"), vec![]);
        let a = Expr::nat_lit(42);
        let b = Expr::nat_lit(42);
        let result = reduce_beq_beq(&[&nat_type, &inst, &a, &b]);
        assert!(result.is_some(), "BEq.beq instBEqNat 42 42 should reduce");
        let val = get_bool_val(&result.unwrap());
        assert_eq!(val, Some(true));
    }

    /// Test BEq.beq with instBEqNat on unequal Nat literals.
    #[test]
    fn test_beq_beq_nat_not_equal() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instBEqNat"), vec![]);
        let a = Expr::nat_lit(1);
        let b = Expr::nat_lit(2);
        let result = reduce_beq_beq(&[&nat_type, &inst, &a, &b]);
        assert!(result.is_some(), "BEq.beq instBEqNat 1 2 should reduce");
        let val = get_bool_val(&result.unwrap());
        assert_eq!(val, Some(false));
    }

    /// Test BEq.beq with instBEqBool.
    #[test]
    fn test_beq_beq_bool_equal() {
        let bool_type = Expr::const_(Name::from_string("Bool"), vec![]);
        let inst = Expr::const_(Name::from_string("instBEqBool"), vec![]);
        let t = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let result = reduce_beq_beq(&[&bool_type, &inst, &t, &t]);
        assert!(
            result.is_some(),
            "BEq.beq instBEqBool true true should reduce"
        );
        let val = get_bool_val(&result.unwrap());
        assert_eq!(val, Some(true));
    }

    /// Test BEq.beq with instBEqBool on unequal values.
    #[test]
    fn test_beq_beq_bool_not_equal() {
        let bool_type = Expr::const_(Name::from_string("Bool"), vec![]);
        let inst = Expr::const_(Name::from_string("instBEqBool"), vec![]);
        let t = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let f = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let result = reduce_beq_beq(&[&bool_type, &inst, &t, &f]);
        assert!(result.is_some());
        let val = get_bool_val(&result.unwrap());
        assert_eq!(val, Some(false));
    }

    /// Test BEq.beq with instBEqString.
    #[test]
    fn test_beq_beq_string_equal() {
        let str_type = Expr::const_(Name::from_string("String"), vec![]);
        let inst = Expr::const_(Name::from_string("instBEqString"), vec![]);
        let a = Expr::str_lit("hello");
        let b = Expr::str_lit("hello");
        let result = reduce_beq_beq(&[&str_type, &inst, &a, &b]);
        assert!(
            result.is_some(),
            "BEq.beq instBEqString should reduce equal strings"
        );
        let val = get_bool_val(&result.unwrap());
        assert_eq!(val, Some(true));
    }

    /// Test BEq.beq with instBEqString on unequal strings.
    #[test]
    fn test_beq_beq_string_not_equal() {
        let str_type = Expr::const_(Name::from_string("String"), vec![]);
        let inst = Expr::const_(Name::from_string("instBEqString"), vec![]);
        let a = Expr::str_lit("hello");
        let b = Expr::str_lit("world");
        let result = reduce_beq_beq(&[&str_type, &inst, &a, &b]);
        assert!(result.is_some());
        let val = get_bool_val(&result.unwrap());
        assert_eq!(val, Some(false));
    }

    /// Test BEq.beq with instBEqUInt32.
    #[test]
    fn test_beq_beq_uint32_equal() {
        let u32_type = Expr::const_(Name::from_string("UInt32"), vec![]);
        let inst = Expr::const_(Name::from_string("instBEqUInt32"), vec![]);
        let a = Expr::nat_lit(100);
        let b = Expr::nat_lit(100);
        let result = reduce_beq_beq(&[&u32_type, &inst, &a, &b]);
        assert!(result.is_some(), "BEq.beq instBEqUInt32 should reduce");
        let val = get_bool_val(&result.unwrap());
        assert_eq!(val, Some(true));
    }

    /// Test BEq.beq with instBEqChar.
    #[test]
    fn test_beq_beq_char_equal() {
        let char_type = Expr::const_(Name::from_string("Char"), vec![]);
        let inst = Expr::const_(Name::from_string("instBEqChar"), vec![]);
        let a = Expr::app(Expr::const_str("Char.mk"), Expr::nat_lit(65)); // 'A'
        let b = Expr::app(Expr::const_str("Char.mk"), Expr::nat_lit(65)); // 'A'
        let result = reduce_beq_beq(&[&char_type, &inst, &a, &b]);
        assert!(
            result.is_some(),
            "BEq.beq instBEqChar should reduce equal chars"
        );
        let val = get_bool_val(&result.unwrap());
        assert_eq!(val, Some(true));
    }

    /// Test BEq.beq returns None for unknown instances.
    #[test]
    fn test_beq_beq_unknown_instance_returns_none() {
        let ty = Expr::const_(Name::from_string("MyType"), vec![]);
        let inst = Expr::const_(Name::from_string("instBEqMyType"), vec![]);
        let a = Expr::nat_lit(1);
        let b = Expr::nat_lit(1);
        let result = reduce_beq_beq(&[&ty, &inst, &a, &b]);
        assert!(result.is_none(), "Unknown instance should return None");
    }

    /// Test BEq.beq returns None for insufficient args.
    #[test]
    fn test_beq_beq_insufficient_args_returns_none() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instBEqNat"), vec![]);
        let a = Expr::nat_lit(1);
        let result = reduce_beq_beq(&[&nat_type, &inst, &a]);
        assert!(result.is_none(), "3 args should return None (need 4)");
    }

    /// Test BEq.beq returns None for non-literal Nat args.
    #[test]
    fn test_beq_beq_nat_non_literal_returns_none() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instBEqNat"), vec![]);
        let a = Expr::const_(Name::from_string("x"), vec![]);
        let b = Expr::nat_lit(1);
        let result = reduce_beq_beq(&[&nat_type, &inst, &a, &b]);
        assert!(result.is_none(), "Non-literal should return None");
    }

    /// Test BEq.beq reducer is registered.
    #[test]
    fn test_beq_shortcircuit_registered() {
        let env = setup_env();
        assert!(
            env.get_native_reducer(&names::BEQ_BEQ).is_some(),
            "BEq.beq reducer should be registered"
        );
    }

    /// Test BEq.beq with instBEqInt on equal values.
    #[test]
    fn test_beq_beq_int_equal() {
        let int_type = Expr::const_(Name::from_string("Int"), vec![]);
        let inst = Expr::const_(Name::from_string("instBEqInt"), vec![]);
        let a = Expr::app(Expr::const_str("Int.ofNat"), Expr::nat_lit(5));
        let b = Expr::app(Expr::const_str("Int.ofNat"), Expr::nat_lit(5));
        let result = reduce_beq_beq(&[&int_type, &inst, &a, &b]);
        assert!(
            result.is_some(),
            "BEq.beq instBEqInt should reduce equal Ints"
        );
        let val = get_bool_val(&result.unwrap());
        assert_eq!(val, Some(true));
    }

    /// Test BEq.beq with instBEqFin on equal values.
    #[test]
    fn test_beq_beq_fin_equal() {
        // instBEqFin takes a Nat bound argument: @instBEqFin n
        let inst = Expr::app(
            Expr::const_(Name::from_string("instBEqFin"), vec![]),
            Expr::nat_lit(10), // bound
        );
        let fin_type = Expr::app(
            Expr::const_(Name::from_string("Fin"), vec![]),
            Expr::nat_lit(10),
        );
        let a = Expr::nat_lit(3);
        let b = Expr::nat_lit(3);
        let result = reduce_beq_beq(&[&fin_type, &inst, &a, &b]);
        assert!(
            result.is_some(),
            "BEq.beq instBEqFin should reduce equal Fin values"
        );
        let val = get_bool_val(&result.unwrap());
        assert_eq!(val, Some(true));
    }
}
