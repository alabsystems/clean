// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance name aliases for decidable equality native reducers.
//!
//! In Lean 4's .olean files, decidable equality appears under two name forms:
//!
//! 1. **Function form:** `Char.decEq`, `UInt8.decEq`, `Float.decEq`, etc.
//! 2. **Instance form:** `instDecidableEqChar`, `instDecidableEqUInt8`, etc.
//!
//! Both forms refer to the same Decidable computation. The native reducers in
//! `native_reducers_char.rs`, `native_reducers_uint.rs`, and
//! `native_reducers_float.rs` register the function form, but NOT the instance
//! form. When the type checker encounters `instDecidableEqChar`, it falls
//! through to expensive delta/iota reduction instead of hitting the fast path.
//!
//! This module registers the instance name aliases, pointing them at the
//! existing reducer functions. This closes the gap for proof-by-reflection
//! terms in Init that use the instance form.
//!
//! Part of #3210.

use crate::env::native_reducers_char::reduce_char_dec_eq;
use crate::env::native_reducers_float::reduce_float_dec_eq;
use crate::env::native_reducers_uint::{
    reduce_uint16_dec_eq, reduce_uint32_dec_eq, reduce_uint64_dec_eq, reduce_uint8_dec_eq,
};
use crate::env::Environment;

/// Instance name aliases for decidable equality.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static INST_DECIDABLE_EQ_CHAR: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableEqChar"));
    pub(crate) static INST_DECIDABLE_EQ_UINT8: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableEqUInt8"));
    pub(crate) static INST_DECIDABLE_EQ_UINT16: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableEqUInt16"));
    pub(crate) static INST_DECIDABLE_EQ_UINT32: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableEqUInt32"));
    pub(crate) static INST_DECIDABLE_EQ_UINT64: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableEqUInt64"));
    pub(crate) static INST_DECIDABLE_EQ_USIZE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableEqUSize"));
    pub(crate) static INST_DECIDABLE_EQ_FLOAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instDecidableEqFloat"));
}

/// Also register `Nat.decEq` and `Bool.decEq` as aliases for the existing
/// `instDecidableEqNat` and `instDecidableEqBool` reducers in the decidable
/// module. These function-form names may also appear in .olean files.
pub(crate) mod extra_names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static NAT_DEC_EQ: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.decEq"));
    pub(crate) static BOOL_DEC_EQ: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Bool.decEq"));
    pub(crate) static STRING_DEC_EQ: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.decEq"));
}

/// Register all decidable equality instance name aliases.
impl Environment {
    pub(crate) fn init_decidable_alias_native_reducers(&mut self) {
        // Instance name aliases → existing reducer functions
        self.register_native_reducer(names::INST_DECIDABLE_EQ_CHAR.clone(), reduce_char_dec_eq);
        self.register_native_reducer(names::INST_DECIDABLE_EQ_UINT8.clone(), reduce_uint8_dec_eq);
        self.register_native_reducer(
            names::INST_DECIDABLE_EQ_UINT16.clone(),
            reduce_uint16_dec_eq,
        );
        self.register_native_reducer(
            names::INST_DECIDABLE_EQ_UINT32.clone(),
            reduce_uint32_dec_eq,
        );
        self.register_native_reducer(
            names::INST_DECIDABLE_EQ_UINT64.clone(),
            reduce_uint64_dec_eq,
        );
        // USize decidable-equality is NOT natively reduced: v4.30's USize is
        // backed by a Platform-dependent width (`System.Platform.numBits`), so
        // the kernel is provably stuck on concrete USize comparisons — matching
        // Lean. The old width-64 reducer was the def-eq excess removed in the
        // carrier BitVec-parity pass (design Q6). `instDecidableEqUSize` now
        // reduces only through its faithful-opaque definition, not a shortcut.
        self.register_native_reducer(names::INST_DECIDABLE_EQ_FLOAT.clone(), reduce_float_dec_eq);

        // Function-form aliases for reducers that were only registered
        // under instance names in native_reducers_decidable.rs
        self.register_native_reducer(
            extra_names::NAT_DEC_EQ.clone(),
            super::native_reducers_decidable::reduce_inst_decidable_eq_nat,
        );
        self.register_native_reducer(
            extra_names::BOOL_DEC_EQ.clone(),
            super::native_reducers_decidable::reduce_inst_decidable_eq_bool,
        );
        self.register_native_reducer(
            extra_names::STRING_DEC_EQ.clone(),
            super::native_reducers_decidable::reduce_inst_decidable_eq_string,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;
    use crate::expr::Expr;

    #[test]
    fn test_decidable_aliases_registered() {
        let mut env = Environment::new();
        env.init_char_native_reducers();
        env.init_uint_native_reducers();
        env.init_float_native_reducers();
        env.init_decidable_native_reducers();
        env.init_decidable_alias_native_reducers();

        // Instance name aliases
        assert!(
            env.get_native_reducer(&names::INST_DECIDABLE_EQ_CHAR)
                .is_some(),
            "instDecidableEqChar should be registered"
        );
        assert!(
            env.get_native_reducer(&names::INST_DECIDABLE_EQ_UINT8)
                .is_some(),
            "instDecidableEqUInt8 should be registered"
        );
        assert!(
            env.get_native_reducer(&names::INST_DECIDABLE_EQ_UINT16)
                .is_some(),
            "instDecidableEqUInt16 should be registered"
        );
        assert!(
            env.get_native_reducer(&names::INST_DECIDABLE_EQ_UINT32)
                .is_some(),
            "instDecidableEqUInt32 should be registered"
        );
        assert!(
            env.get_native_reducer(&names::INST_DECIDABLE_EQ_UINT64)
                .is_some(),
            "instDecidableEqUInt64 should be registered"
        );
        // `instDecidableEqUSize` is intentionally NOT natively registered: v4.30's
        // USize is width-abstract (`System.Platform.numBits`), so the kernel is
        // provably stuck on concrete USize decEq — the width-64 shortcut was the
        // def-eq excess removed in the carrier BitVec-parity pass (design
        // 2026-07-03 §1.5 / Q6). Assert its ABSENCE so a re-introduced shortcut
        // regresses this pin.
        assert!(
            env.get_native_reducer(&names::INST_DECIDABLE_EQ_USIZE)
                .is_none(),
            "instDecidableEqUSize must NOT be natively reduced (width-abstract USize)"
        );
        assert!(
            env.get_native_reducer(&names::INST_DECIDABLE_EQ_FLOAT)
                .is_some(),
            "instDecidableEqFloat should be registered"
        );

        // Function-form aliases
        assert!(
            env.get_native_reducer(&extra_names::NAT_DEC_EQ).is_some(),
            "Nat.decEq should be registered"
        );
        assert!(
            env.get_native_reducer(&extra_names::BOOL_DEC_EQ).is_some(),
            "Bool.decEq should be registered"
        );
        assert!(
            env.get_native_reducer(&extra_names::STRING_DEC_EQ)
                .is_some(),
            "String.decEq should be registered"
        );
    }

    #[test]
    fn test_inst_decidable_eq_char_reduces() {
        // Char.mk 65 == Char.mk 65 should be Decidable.isTrue
        let a = Expr::app(Expr::const_str("Char.mk"), Expr::nat_lit(65));
        let b = Expr::app(Expr::const_str("Char.mk"), Expr::nat_lit(65));
        let result = reduce_char_dec_eq(&[&a, &b]);
        assert!(
            result.is_some(),
            "instDecidableEqChar should reduce equal chars"
        );
    }

    #[test]
    fn test_inst_decidable_eq_uint8_reduces() {
        // `UInt8.ofNat 42` — the v4.30 carrier operand form (`get_uint_ctor_val`
        // peels `<T>.ofNat`/`<T>.ofBitVec`, no longer the old Fin `<T>.mk`;
        // design 2026-07-03 §2.3a). `@Eq UInt8 (UInt8.ofNat 42) (UInt8.ofNat 42)`.
        let a = Expr::app(Expr::const_str("UInt8.ofNat"), Expr::nat_lit(42));
        let b = Expr::app(Expr::const_str("UInt8.ofNat"), Expr::nat_lit(42));
        let result = reduce_uint8_dec_eq(&[&a, &b]);
        assert!(
            result.is_some(),
            "instDecidableEqUInt8 should reduce equal values"
        );
    }

    #[test]
    fn test_inst_decidable_eq_float_reduces() {
        // Float values are `Float.mk <bits>`; equality is structural on the bits.
        let bits = f64::to_bits(std::f64::consts::PI);
        let mk = |n: u64| Expr::app(Expr::const_str("Float.mk"), Expr::nat_lit(n));
        let a = mk(bits);
        let b = mk(bits);
        let result = reduce_float_dec_eq(&[&a, &b]);
        assert!(
            result.is_some(),
            "instDecidableEqFloat should reduce equal values"
        );
    }
}
