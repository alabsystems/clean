// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Nat and UInt32 arithmetic native reducers.

#[cfg(test)]
mod tests {
    use crate::env::native_reducers_arith::*;
    use crate::env::Environment;
    use crate::expr::{BigNat, Expr, ExprKind, Literal};
    use crate::name::Name;

    // --- Nat.add ---

    #[test]
    fn test_nat_add_basic() {
        let result = reduce_nat_add(&[&Expr::nat_lit(1), &Expr::nat_lit(2)]);
        let result = result.expect("Nat.add 1 2 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(3));
        } else {
            panic!("Expected Nat literal 3, got {:?}", result);
        }
    }

    #[test]
    fn test_nat_add_zero() {
        let result = reduce_nat_add(&[&Expr::nat_lit(0), &Expr::nat_lit(5)]);
        let result = result.expect("Nat.add 0 5 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(5));
        } else {
            panic!("Expected Nat literal 5, got {:?}", result);
        }
    }

    // --- Nat.sub ---

    #[test]
    fn test_nat_sub_basic() {
        let result = reduce_nat_sub(&[&Expr::nat_lit(5), &Expr::nat_lit(3)]);
        let result = result.expect("Nat.sub 5 3 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(2));
        } else {
            panic!("Expected Nat literal 2, got {:?}", result);
        }
    }

    #[test]
    fn test_nat_sub_truncates_to_zero() {
        let result = reduce_nat_sub(&[&Expr::nat_lit(3), &Expr::nat_lit(10)]);
        let result = result.expect("Nat.sub 3 10 should reduce to 0");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0, got {:?}", result);
        }
    }

    // --- Nat.mul ---

    #[test]
    fn test_nat_mul_basic() {
        let result = reduce_nat_mul(&[&Expr::nat_lit(3), &Expr::nat_lit(7)]);
        let result = result.expect("Nat.mul 3 7 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(21));
        } else {
            panic!("Expected Nat literal 21, got {:?}", result);
        }
    }

    // --- Nat.blt ---

    #[test]
    fn test_nat_blt_true() {
        let result = reduce_nat_blt(&[&Expr::nat_lit(2), &Expr::nat_lit(5)]);
        let result = result.expect("Nat.blt 2 5 should reduce");
        let head = result.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            assert_eq!(name.to_string(), "Bool.true");
        } else {
            panic!("Expected Bool.true, got {:?}", head);
        }
    }

    #[test]
    fn test_nat_blt_false() {
        let result = reduce_nat_blt(&[&Expr::nat_lit(5), &Expr::nat_lit(2)]);
        let result = result.expect("Nat.blt 5 2 should reduce");
        let head = result.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            assert_eq!(name.to_string(), "Bool.false");
        } else {
            panic!("Expected Bool.false, got {:?}", head);
        }
    }

    // --- UInt32.add ---

    #[test]
    fn test_uint32_add_basic() {
        let result = reduce_uint32_add(&[&Expr::nat_lit(1), &Expr::nat_lit(2)]);
        let result = result.expect("UInt32.add 1 2 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(3));
        } else {
            panic!("Expected Nat literal 3, got {:?}", result);
        }
    }

    #[test]
    fn test_uint32_add_overflow_wraps() {
        let max = u64::from(u32::MAX);
        let result = reduce_uint32_add(&[&Expr::nat_lit(max), &Expr::nat_lit(1)]);
        let result = result.expect("UInt32.add overflow should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0, got {:?}", result);
        }
    }

    #[test]
    fn test_uint32_add_overflow_wraps_large() {
        let max = u64::from(u32::MAX);
        let result = reduce_uint32_add(&[&Expr::nat_lit(max), &Expr::nat_lit(2)]);
        let result = result.expect("UInt32.add overflow should wrap");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(1));
        } else {
            panic!("Expected Nat literal 1, got {:?}", result);
        }
    }

    // --- UInt32.mul ---

    #[test]
    fn test_uint32_mul_basic() {
        let result = reduce_uint32_mul(&[&Expr::nat_lit(6), &Expr::nat_lit(7)]);
        let result = result.expect("UInt32.mul 6 7 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(42));
        } else {
            panic!("Expected Nat literal 42, got {:?}", result);
        }
    }

    #[test]
    fn test_uint32_mul_overflow_wraps() {
        let half = 1u64 << 31;
        let result = reduce_uint32_mul(&[&Expr::nat_lit(half), &Expr::nat_lit(2)]);
        let result = result.expect("UInt32.mul overflow should wrap");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0, got {:?}", result);
        }
    }

    // --- UInt32.sub ---

    #[test]
    fn test_uint32_sub_basic() {
        let result = reduce_uint32_sub(&[&Expr::nat_lit(10), &Expr::nat_lit(3)]);
        let result = result.expect("UInt32.sub 10 3 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(7));
        } else {
            panic!("Expected Nat literal 7, got {:?}", result);
        }
    }

    #[test]
    fn test_uint32_sub_wraps_underflow() {
        let result = reduce_uint32_sub(&[&Expr::nat_lit(0), &Expr::nat_lit(1)]);
        let result = result.expect("UInt32.sub underflow should wrap");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(u64::from(u32::MAX)));
        } else {
            panic!("Expected Nat literal u32::MAX, got {:?}", result);
        }
    }

    // --- Edge cases ---

    #[test]
    fn test_wrong_arg_count_returns_none() {
        assert!(reduce_nat_add(&[&Expr::nat_lit(1)]).is_none());
        assert!(reduce_nat_sub(&[&Expr::nat_lit(1)]).is_none());
        assert!(reduce_nat_mul(&[&Expr::nat_lit(1)]).is_none());
        assert!(reduce_nat_blt(&[&Expr::nat_lit(1)]).is_none());
        assert!(reduce_uint32_add(&[&Expr::nat_lit(1)]).is_none());
        assert!(reduce_uint32_sub(&[&Expr::nat_lit(1)]).is_none());
        assert!(reduce_uint32_mul(&[&Expr::nat_lit(1)]).is_none());

        assert!(reduce_nat_add(&[]).is_none());
        assert!(reduce_uint32_add(&[]).is_none());
    }

    #[test]
    fn test_non_literal_arg_returns_none() {
        let var = Expr::const_(Name::from_string("x"), vec![]);
        assert!(reduce_nat_add(&[&var, &Expr::nat_lit(1)]).is_none());
        assert!(reduce_nat_add(&[&Expr::nat_lit(1), &var]).is_none());
        assert!(reduce_uint32_add(&[&var, &Expr::nat_lit(1)]).is_none());
        assert!(reduce_uint32_mul(&[&Expr::nat_lit(1), &var]).is_none());
    }

    // --- Nat.div ---

    #[test]
    fn test_nat_div_basic() {
        let result = reduce_nat_div(&[&Expr::nat_lit(10), &Expr::nat_lit(3)]);
        let result = result.expect("Nat.div 10 3 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(3));
        } else {
            panic!("Expected Nat literal 3");
        }
    }

    #[test]
    fn test_nat_div_by_zero() {
        let result = reduce_nat_div(&[&Expr::nat_lit(10), &Expr::nat_lit(0)]);
        let result = result.expect("Nat.div by 0 should reduce to 0");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0");
        }
    }

    // --- Nat.mod ---

    #[test]
    fn test_nat_mod_basic() {
        let result = reduce_nat_mod(&[&Expr::nat_lit(10), &Expr::nat_lit(3)]);
        let result = result.expect("Nat.mod 10 3 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(1));
        } else {
            panic!("Expected Nat literal 1");
        }
    }

    #[test]
    fn test_nat_mod_by_zero() {
        let result = reduce_nat_mod(&[&Expr::nat_lit(7), &Expr::nat_lit(0)]);
        let result = result.expect("Nat.mod by 0 should reduce to a");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(7));
        } else {
            panic!("Expected Nat literal 7");
        }
    }

    // --- Nat.pow ---

    #[test]
    fn test_nat_pow_basic() {
        let result = reduce_nat_pow(&[&Expr::nat_lit(2), &Expr::nat_lit(10)]);
        let result = result.expect("Nat.pow 2 10 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(1024));
        } else {
            panic!("Expected Nat literal 1024");
        }
    }

    #[test]
    fn test_nat_pow_zero_exponent() {
        let result = reduce_nat_pow(&[&Expr::nat_lit(5), &Expr::nat_lit(0)]);
        let result = result.expect("Nat.pow 5 0 should reduce to 1");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(1));
        } else {
            panic!("Expected Nat literal 1");
        }
    }

    #[test]
    fn test_nat_pow_bignat_result() {
        // 2^64 now produces a BigNat instead of returning None
        let result = reduce_nat_pow(&[&Expr::nat_lit(2), &Expr::nat_lit(64)]);
        let result = result.expect("2^64 should produce BigNat, not None");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n, &BigNat::from_limbs(vec![0, 1])); // 2^64 = [0, 1] in limbs
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_nat_pow_huge_exponent_returns_none() {
        // Very large exponent should still return None (exceeds 1024 bits)
        let result = reduce_nat_pow(&[&Expr::nat_lit(2), &Expr::nat_lit(2048)]);
        assert!(result.is_none(), "2^2048 should exceed 1024-bit limit");
    }

    // --- Nat.beq ---

    #[test]
    fn test_nat_beq_equal() {
        let result = reduce_nat_beq(&[&Expr::nat_lit(42), &Expr::nat_lit(42)]);
        let result = result.expect("Nat.beq should reduce");
        if let ExprKind::Const(name, _) = result.kind() {
            assert_eq!(name.to_string(), "Bool.true");
        } else {
            panic!("Expected Bool.true");
        }
    }

    #[test]
    fn test_nat_beq_not_equal() {
        let result = reduce_nat_beq(&[&Expr::nat_lit(1), &Expr::nat_lit(2)]);
        let result = result.expect("Nat.beq should reduce");
        if let ExprKind::Const(name, _) = result.kind() {
            assert_eq!(name.to_string(), "Bool.false");
        } else {
            panic!("Expected Bool.false");
        }
    }

    #[test]
    fn test_nat_ble_three_limb_big_nat_returns_none() {
        let big = Expr::bignat_lit(BigNat::from_limbs(vec![0, 0, 1]));
        let result = reduce_nat_ble(&[&big, &Expr::nat_lit(0)]);
        assert!(
            result.is_none(),
            "Nat.ble native reducer should leave 3-limb BigNat comparisons unreduced"
        );
    }

    // --- Nat.ble ---

    #[test]
    fn test_nat_ble_true() {
        let result = reduce_nat_ble(&[&Expr::nat_lit(3), &Expr::nat_lit(5)]);
        let result = result.expect("Nat.ble should reduce");
        if let ExprKind::Const(name, _) = result.kind() {
            assert_eq!(name.to_string(), "Bool.true");
        } else {
            panic!("Expected Bool.true");
        }
    }

    #[test]
    fn test_nat_ble_equal() {
        let result = reduce_nat_ble(&[&Expr::nat_lit(5), &Expr::nat_lit(5)]);
        let result = result.expect("Nat.ble should reduce");
        if let ExprKind::Const(name, _) = result.kind() {
            assert_eq!(name.to_string(), "Bool.true");
        } else {
            panic!("Expected Bool.true for <=");
        }
    }

    #[test]
    fn test_nat_ble_false() {
        let result = reduce_nat_ble(&[&Expr::nat_lit(6), &Expr::nat_lit(5)]);
        let result = result.expect("Nat.ble should reduce");
        if let ExprKind::Const(name, _) = result.kind() {
            assert_eq!(name.to_string(), "Bool.false");
        } else {
            panic!("Expected Bool.false");
        }
    }

    // --- Nat bitwise ---

    #[test]
    fn test_nat_land() {
        let result = reduce_nat_land(&[&Expr::nat_lit(0b1100), &Expr::nat_lit(0b1010)]);
        let result = result.expect("Nat.land should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0b1000));
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_nat_lor() {
        let result = reduce_nat_lor(&[&Expr::nat_lit(0b1100), &Expr::nat_lit(0b1010)]);
        let result = result.expect("Nat.lor should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0b1110));
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_nat_lxor() {
        let result = reduce_nat_lxor(&[&Expr::nat_lit(0b1100), &Expr::nat_lit(0b1010)]);
        let result = result.expect("Nat.xor should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0b0110));
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_nat_shift_left() {
        let result = reduce_nat_shift_left(&[&Expr::nat_lit(1), &Expr::nat_lit(10)]);
        let result = result.expect("Nat.shiftLeft should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(1024));
        } else {
            panic!("Expected Nat literal 1024");
        }
    }

    #[test]
    fn test_nat_shift_right() {
        let result = reduce_nat_shift_right(&[&Expr::nat_lit(1024), &Expr::nat_lit(5)]);
        let result = result.expect("Nat.shiftRight should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(32));
        } else {
            panic!("Expected Nat literal 32");
        }
    }

    #[test]
    fn test_nat_shift_left_bignat_result() {
        // 1 << 64 now produces a BigNat instead of returning None
        let result = reduce_nat_shift_left(&[&Expr::nat_lit(1), &Expr::nat_lit(64)]);
        let result = result.expect("1 << 64 should produce BigNat, not None");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n, &BigNat::from_limbs(vec![0, 1])); // 2^64 = [0, 1] in limbs
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_nat_shift_left_huge_shift_returns_none() {
        // Shift > 1024 should return None (exceeds 1024-bit limit)
        let result = reduce_nat_shift_left(&[&Expr::nat_lit(1), &Expr::nat_lit(2048)]);
        assert!(result.is_none(), "1 << 2048 should exceed 1024-bit limit");
    }

    #[test]
    fn test_nat_shift_left_zero_large_shift() {
        let result = reduce_nat_shift_left(&[&Expr::nat_lit(0), &Expr::nat_lit(100)]);
        let result = result.expect("0 << 100 should reduce to 0");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0");
        }
    }

    #[test]
    fn test_nat_shift_right_large_shift() {
        let result = reduce_nat_shift_right(&[&Expr::nat_lit(100), &Expr::nat_lit(100)]);
        let result = result.expect("100 >> 100 should reduce to 0");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0");
        }
    }

    #[test]
    fn test_registration_on_environment() {
        let mut env = Environment::new();
        env.init_arith_native_reducers();

        assert!(env.get_native_reducer(&names::NAT_ADD).is_some());
        assert!(env.get_native_reducer(&names::NAT_SUB).is_some());
        assert!(env.get_native_reducer(&names::NAT_MUL).is_some());
        assert!(env.get_native_reducer(&names::NAT_DIV).is_some());
        assert!(env.get_native_reducer(&names::NAT_MOD).is_some());
        assert!(env.get_native_reducer(&names::NAT_POW).is_some());
        assert!(env.get_native_reducer(&names::NAT_BLT).is_some());
        assert!(env.get_native_reducer(&names::NAT_BLE).is_some());
        assert!(env.get_native_reducer(&names::NAT_BEQ).is_some());
        assert!(env.get_native_reducer(&names::NAT_LAND).is_some());
        assert!(env.get_native_reducer(&names::NAT_LOR).is_some());
        assert!(env.get_native_reducer(&names::NAT_LXOR).is_some());
        assert!(env.get_native_reducer(&names::NAT_SHIFT_LEFT).is_some());
        assert!(env.get_native_reducer(&names::NAT_SHIFT_RIGHT).is_some());
        assert!(env.get_native_reducer(&names::UINT32_ADD).is_some());
        assert!(env.get_native_reducer(&names::UINT32_SUB).is_some());
        assert!(env.get_native_reducer(&names::UINT32_MUL).is_some());
    }

    // --- BigNat tests (Part of #3248) ---

    /// Create a BigNat::Big expression from two limbs (value = hi << 64 | lo).
    fn big_nat_expr(lo: u64, hi: u64) -> Expr {
        Expr::bignat_lit(BigNat::from_limbs(vec![lo, hi]))
    }

    #[test]
    fn test_nat_beq_bignat_equal() {
        let a = big_nat_expr(1, 1);
        let b = big_nat_expr(1, 1);
        let result = reduce_nat_beq(&[&a, &b]).expect("BigNat beq should reduce");
        if let ExprKind::Const(name, _) = result.kind() {
            assert_eq!(name.to_string(), "Bool.true");
        } else {
            panic!("Expected Bool.true");
        }
    }

    #[test]
    fn test_nat_beq_bignat_not_equal() {
        let a = big_nat_expr(1, 1);
        let b = big_nat_expr(2, 1);
        let result = reduce_nat_beq(&[&a, &b]).expect("BigNat beq should reduce");
        if let ExprKind::Const(name, _) = result.kind() {
            assert_eq!(name.to_string(), "Bool.false");
        } else {
            panic!("Expected Bool.false");
        }
    }

    #[test]
    fn test_nat_beq_bignat_vs_small() {
        let big = big_nat_expr(42, 1);
        let small = Expr::nat_lit(42);
        let result = reduce_nat_beq(&[&big, &small]).expect("BigNat vs Small should reduce");
        if let ExprKind::Const(name, _) = result.kind() {
            assert_eq!(name.to_string(), "Bool.false");
        } else {
            panic!("Expected Bool.false");
        }
    }

    #[test]
    fn test_nat_blt_bignat_less() {
        let small = Expr::nat_lit(u64::MAX);
        let big = big_nat_expr(0, 1); // 2^64
        let result = reduce_nat_blt(&[&small, &big]).expect("Small < Big should reduce");
        if let ExprKind::Const(name, _) = result.kind() {
            assert_eq!(name.to_string(), "Bool.true");
        } else {
            panic!("Expected Bool.true");
        }
    }

    #[test]
    fn test_nat_blt_bignat_not_less() {
        let big = big_nat_expr(0, 1); // 2^64
        let small = Expr::nat_lit(u64::MAX);
        let result = reduce_nat_blt(&[&big, &small]).expect("Big > Small should reduce");
        if let ExprKind::Const(name, _) = result.kind() {
            assert_eq!(name.to_string(), "Bool.false");
        } else {
            panic!("Expected Bool.false");
        }
    }

    #[test]
    fn test_nat_ble_bignat_equal() {
        let a = big_nat_expr(5, 2);
        let b = big_nat_expr(5, 2);
        let result = reduce_nat_ble(&[&a, &b]).expect("BigNat ble should reduce");
        if let ExprKind::Const(name, _) = result.kind() {
            assert_eq!(name.to_string(), "Bool.true");
        } else {
            panic!("Expected Bool.true");
        }
    }

    #[test]
    fn test_nat_add_bignat_overflow() {
        let a = Expr::nat_lit(u64::MAX);
        let b = Expr::nat_lit(1);
        let result = reduce_nat_add(&[&a, &b]).expect("u64::MAX + 1 should produce BigNat");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n, &BigNat::from_limbs(vec![0, 1]));
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_nat_add_two_bignats() {
        let a = big_nat_expr(u64::MAX, 0);
        let b = big_nat_expr(u64::MAX, 0);
        let result = reduce_nat_add(&[&a, &b]).expect("BigNat + BigNat should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n, &BigNat::from_limbs(vec![u64::MAX - 1, 1]));
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_nat_sub_bignat_to_small() {
        let big = big_nat_expr(0, 1); // 2^64
        let one = Expr::nat_lit(1);
        let result = reduce_nat_sub(&[&big, &one]).expect("2^64 - 1 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(u64::MAX));
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_nat_sub_bignat_saturates_to_zero() {
        let small = Expr::nat_lit(42);
        let big = big_nat_expr(0, 1);
        let result = reduce_nat_sub(&[&small, &big]).expect("Small - Big should saturate to 0");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0");
        }
    }

    #[test]
    fn test_nat_mul_bignat_overflow() {
        let a = Expr::nat_lit(u64::MAX);
        let b = Expr::nat_lit(2);
        let result = reduce_nat_mul(&[&a, &b]).expect("u64::MAX * 2 should produce BigNat");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n, &BigNat::from_limbs(vec![u64::MAX - 1, 1]));
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_nat_mul_bignat_zero() {
        let big = big_nat_expr(42, 1);
        let zero = Expr::nat_lit(0);
        let result = reduce_nat_mul(&[&big, &zero]).expect("BigNat * 0 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0");
        }
    }

    // --- BigNat div/mod/pow/bitwise/shift tests (Part of #3248) ---
    // These test the previously-broken reducers that returned None for BigNat values.

    #[test]
    fn test_nat_div_bignat_by_small() {
        // (2^64) / 2 = 2^63
        let big = big_nat_expr(0, 1); // 2^64
        let two = Expr::nat_lit(2);
        let result = reduce_nat_div(&[&big, &two]).expect("BigNat div should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(1u64 << 63));
        } else {
            panic!("Expected Nat literal 2^63");
        }
    }

    #[test]
    fn test_nat_div_bignat_by_bignat() {
        // (2^64 + 4) / (2^64 + 4) = 1
        let a = big_nat_expr(4, 1);
        let b = big_nat_expr(4, 1);
        let result = reduce_nat_div(&[&a, &b]).expect("BigNat / BigNat should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(1));
        } else {
            panic!("Expected Nat literal 1");
        }
    }

    #[test]
    fn test_nat_div_small_by_bignat() {
        // 42 / (2^64) = 0
        let small = Expr::nat_lit(42);
        let big = big_nat_expr(0, 1);
        let result = reduce_nat_div(&[&small, &big]).expect("Small / Big should reduce to 0");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0");
        }
    }

    #[test]
    fn test_nat_div_bignat_by_zero() {
        let big = big_nat_expr(42, 1);
        let zero = Expr::nat_lit(0);
        let result = reduce_nat_div(&[&big, &zero]).expect("BigNat / 0 should reduce to 0");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0");
        }
    }

    #[test]
    fn test_nat_mod_bignat_by_small() {
        // (2^64 + 3) % 4 = 3 (since 2^64 % 4 = 0, so (2^64 + 3) % 4 = 3)
        let big = big_nat_expr(3, 1); // 2^64 + 3
        let four = Expr::nat_lit(4);
        let result = reduce_nat_mod(&[&big, &four]).expect("BigNat mod should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(3));
        } else {
            panic!("Expected Nat literal 3");
        }
    }

    #[test]
    fn test_nat_mod_bignat_by_zero() {
        let big = big_nat_expr(42, 1);
        let zero = Expr::nat_lit(0);
        let result = reduce_nat_mod(&[&big, &zero]).expect("BigNat mod 0 should return self");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n, &BigNat::from_limbs(vec![42, 1]));
        } else {
            panic!("Expected BigNat");
        }
    }

    #[test]
    fn test_nat_pow_bignat_base() {
        // (2^64)^1 = 2^64
        let big = big_nat_expr(0, 1); // 2^64
        let one = Expr::nat_lit(1);
        let result = reduce_nat_pow(&[&big, &one]).expect("BigNat^1 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n, &BigNat::from_limbs(vec![0, 1]));
        } else {
            panic!("Expected BigNat 2^64");
        }
    }

    #[test]
    fn test_nat_pow_bignat_zero_exp() {
        // (2^64)^0 = 1
        let big = big_nat_expr(0, 1);
        let zero = Expr::nat_lit(0);
        let result = reduce_nat_pow(&[&big, &zero]).expect("BigNat^0 should reduce to 1");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(1));
        } else {
            panic!("Expected Nat literal 1");
        }
    }

    #[test]
    fn test_nat_land_bignat() {
        // BigNat AND: (2^64 + 0xFF) & 0xFF = 0xFF
        let big = big_nat_expr(0xFF, 1);
        let mask = Expr::nat_lit(0xFF);
        let result = reduce_nat_land(&[&big, &mask]).expect("BigNat land should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0xFF));
        } else {
            panic!("Expected Nat literal 0xFF");
        }
    }

    #[test]
    fn test_nat_land_two_bignats() {
        // (2^64 + 0xFF) & (2^64 + 0x0F) = 2^64 + 0x0F
        let a = big_nat_expr(0xFF, 1);
        let b = big_nat_expr(0x0F, 1);
        let result = reduce_nat_land(&[&a, &b]).expect("BigNat land should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n, &BigNat::from_limbs(vec![0x0F, 1]));
        } else {
            panic!("Expected BigNat");
        }
    }

    #[test]
    fn test_nat_lor_bignat() {
        // 0xFF | (2^64) = 2^64 + 0xFF
        let small = Expr::nat_lit(0xFF);
        let big = big_nat_expr(0, 1);
        let result = reduce_nat_lor(&[&small, &big]).expect("BigNat lor should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n, &BigNat::from_limbs(vec![0xFF, 1]));
        } else {
            panic!("Expected BigNat");
        }
    }

    #[test]
    fn test_nat_lxor_bignat() {
        // (2^64 + 0xFF) ^ (2^64 + 0x0F) = 0xF0
        let a = big_nat_expr(0xFF, 1);
        let b = big_nat_expr(0x0F, 1);
        let result = reduce_nat_lxor(&[&a, &b]).expect("BigNat xor should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0xF0));
        } else {
            panic!("Expected Nat literal 0xF0");
        }
    }

    #[test]
    fn test_nat_shift_left_bignat_value() {
        // (2^64) << 1 = 2^65 = [0, 2]
        let big = big_nat_expr(0, 1);
        let one = Expr::nat_lit(1);
        let result = reduce_nat_shift_left(&[&big, &one]).expect("BigNat << 1 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n, &BigNat::from_limbs(vec![0, 2]));
        } else {
            panic!("Expected BigNat 2^65");
        }
    }

    #[test]
    fn test_nat_shift_right_bignat_to_small() {
        // (2^64) >> 1 = 2^63
        let big = big_nat_expr(0, 1);
        let one = Expr::nat_lit(1);
        let result = reduce_nat_shift_right(&[&big, &one]).expect("BigNat >> 1 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(1u64 << 63));
        } else {
            panic!("Expected Nat literal 2^63");
        }
    }

    #[test]
    fn test_nat_shift_right_bignat_to_zero() {
        // (2^64) >> 65 = 0
        let big = big_nat_expr(0, 1);
        let shift = Expr::nat_lit(65);
        let result = reduce_nat_shift_right(&[&big, &shift]).expect("BigNat >> 65 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0");
        }
    }
}
