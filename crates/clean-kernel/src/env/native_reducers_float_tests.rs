// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Float native reducers.

#[cfg(test)]
mod tests {
    use crate::env::native_reducers_float::*;
    use crate::env::Environment;
    use crate::expr::{Expr, ExprKind, Literal};
    use crate::name::Name;

    /// A non-special decimal test value (exactly `3.14`) that happens to be
    /// near, but is deliberately not, `f64::consts::PI`. Built as `314 / 100`
    /// so the source contains no `3.14` literal that could be misread as an
    /// approximation of pi.
    const NEAR_PI: f64 = 314.0 / 100.0;

    /// Helper: create a Float bit pattern Nat from an f64 value.
    fn float_bits(f: f64) -> Expr {
        Expr::nat_lit(f.to_bits())
    }

    /// Helper: extract f64 from a `Float`-valued reducer result.
    ///
    /// Float-returning reducers now yield the canonical `Float.mk <bits>`
    /// constructor form (so the result is `Float`-typed, not a bare `Nat` that
    /// collapses `Float` to `Nat` in the kernel). Accept both that form and the
    /// bare-`Nat` intermediate form for robustness.
    fn result_f64(e: &Expr) -> f64 {
        match e.kind() {
            ExprKind::Lit(Literal::Nat(n)) => f64::from_bits(n.to_u64().unwrap()),
            ExprKind::App(f, arg) => match (f.kind(), arg.kind()) {
                (ExprKind::Const(name, _), ExprKind::Lit(Literal::Nat(n)))
                    if name.to_string() == "Float.mk" =>
                {
                    f64::from_bits(n.to_u64().unwrap())
                }
                _ => panic!("Expected Float.mk <Nat> or Nat literal, got {:?}", e),
            },
            _ => panic!("Expected Float.mk <Nat> or Nat literal, got {:?}", e),
        }
    }

    /// Helper: extract Bool from a result.
    fn result_bool(e: &Expr) -> bool {
        if let ExprKind::Const(name, _) = e.get_app_fn().kind() {
            name.to_string() == "Bool.true"
        } else {
            panic!("Expected Bool constant, got {:?}", e);
        }
    }

    // --- Float arithmetic ---

    #[test]
    fn test_float_add_basic() {
        let a = float_bits(1.5);
        let b = float_bits(2.5);
        let result = reduce_float_add(&[&a, &b]).expect("Float.add should reduce");
        assert!((result_f64(&result) - 4.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_sub_basic() {
        let a = float_bits(5.0);
        let b = float_bits(2.0);
        let result = reduce_float_sub(&[&a, &b]).expect("Float.sub should reduce");
        assert!((result_f64(&result) - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_mul_basic() {
        let a = float_bits(3.0);
        let b = float_bits(4.0);
        let result = reduce_float_mul(&[&a, &b]).expect("Float.mul should reduce");
        assert!((result_f64(&result) - 12.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_div_basic() {
        let a = float_bits(10.0);
        let b = float_bits(4.0);
        let result = reduce_float_div(&[&a, &b]).expect("Float.div should reduce");
        assert!((result_f64(&result) - 2.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_div_by_zero() {
        let a = float_bits(1.0);
        let b = float_bits(0.0);
        let result = reduce_float_div(&[&a, &b]).expect("Float.div should reduce");
        assert!(result_f64(&result).is_infinite());
    }

    #[test]
    fn test_float_neg() {
        let a = float_bits(NEAR_PI);
        let result = reduce_float_neg(&[&a]).expect("Float.neg should reduce");
        assert!((result_f64(&result) + NEAR_PI).abs() < f64::EPSILON);
    }

    // --- Float comparison ---

    #[test]
    fn test_float_beq_equal() {
        let a = float_bits(1.0);
        let b = float_bits(1.0);
        let result = reduce_float_beq(&[&a, &b]).expect("Float.beq should reduce");
        assert!(result_bool(&result));
    }

    #[test]
    fn test_float_beq_not_equal() {
        let a = float_bits(1.0);
        let b = float_bits(2.0);
        let result = reduce_float_beq(&[&a, &b]).expect("Float.beq should reduce");
        assert!(!result_bool(&result));
    }

    #[test]
    fn test_float_beq_nan() {
        let a = float_bits(f64::NAN);
        let b = float_bits(f64::NAN);
        let result = reduce_float_beq(&[&a, &b]).expect("Float.beq should reduce");
        assert!(!result_bool(&result), "NaN != NaN");
    }

    #[test]
    fn test_float_blt_true() {
        let a = float_bits(1.0);
        let b = float_bits(2.0);
        let result = reduce_float_blt(&[&a, &b]).expect("Float.blt should reduce");
        assert!(result_bool(&result));
    }

    #[test]
    fn test_float_blt_false() {
        let a = float_bits(2.0);
        let b = float_bits(1.0);
        let result = reduce_float_blt(&[&a, &b]).expect("Float.blt should reduce");
        assert!(!result_bool(&result));
    }

    #[test]
    fn test_float_ble_equal() {
        let a = float_bits(1.0);
        let b = float_bits(1.0);
        let result = reduce_float_ble(&[&a, &b]).expect("Float.ble should reduce");
        assert!(result_bool(&result));
    }

    // --- Float conversion ---

    #[test]
    fn test_float_of_nat() {
        let n = Expr::nat_lit(42);
        let result = reduce_float_of_nat(&[&n]).expect("Float.ofNat should reduce");
        assert!((result_f64(&result) - 42.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_of_int_positive() {
        // Int.ofNat 42 -> 42.0
        let int_val = Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(42),
        );
        let result = reduce_float_of_int(&[&int_val]).expect("Float.ofInt should reduce");
        assert!((result_f64(&result) - 42.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_of_int_negative() {
        // Int.negSucc 0 represents -1
        let int_val = Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(0),
        );
        let result = reduce_float_of_int(&[&int_val]).expect("Float.ofInt should reduce");
        assert!((result_f64(&result) - (-1.0)).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_of_int_neg_succ_large() {
        // Int.negSucc 99 represents -100
        let int_val = Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(99),
        );
        let result = reduce_float_of_int(&[&int_val]).expect("Float.ofInt should reduce");
        assert!((result_f64(&result) - (-100.0)).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_of_int_zero() {
        // Int.ofNat 0 -> 0.0
        let int_val = Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(0),
        );
        let result = reduce_float_of_int(&[&int_val]).expect("Float.ofInt should reduce");
        assert!((result_f64(&result) - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_of_int_bare_nat() {
        // Bare Nat literal treated as Int.ofNat
        let n = Expr::nat_lit(7);
        let result = reduce_float_of_int(&[&n]).expect("Float.ofInt should reduce bare Nat");
        assert!((result_f64(&result) - 7.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_of_int_insufficient_args() {
        assert!(reduce_float_of_int(&[]).is_none());
    }

    #[test]
    fn test_float_of_int_non_int_returns_none() {
        let var = Expr::const_(Name::from_string("x"), vec![]);
        assert!(reduce_float_of_int(&[&var]).is_none());
    }

    #[test]
    fn test_float_of_scientific_positive_exponent() {
        let m = Expr::nat_lit(15);
        let s = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let e = Expr::nat_lit(2);
        let result =
            reduce_float_of_scientific(&[&m, &s, &e]).expect("Float.ofScientific should reduce");
        assert!((result_f64(&result) - 1500.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_of_scientific_negative_exponent() {
        let m = Expr::nat_lit(314);
        let s = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let e = Expr::nat_lit(2);
        let result =
            reduce_float_of_scientific(&[&m, &s, &e]).expect("Float.ofScientific should reduce");
        assert!((result_f64(&result) - NEAR_PI).abs() < 1e-10);
    }

    #[test]
    fn test_float_to_string() {
        let a = float_bits(NEAR_PI);
        let result = reduce_float_to_string(&[&a]).expect("Float.toString should reduce");
        if let ExprKind::Lit(Literal::String(s)) = result.kind() {
            assert!(s.starts_with("3.14"), "Expected 3.14..., got {}", s);
        } else {
            panic!("Expected String literal, got {:?}", result);
        }
    }

    #[test]
    fn test_float_to_string_nan() {
        let a = float_bits(f64::NAN);
        let result = reduce_float_to_string(&[&a]).expect("Float.toString should reduce");
        if let ExprKind::Lit(Literal::String(s)) = result.kind() {
            assert_eq!(&**s, "NaN");
        } else {
            panic!("Expected String literal");
        }
    }

    #[test]
    fn test_float_to_uint8() {
        let a = float_bits(42.7);
        let result = reduce_float_to_uint8(&[&a]).expect("Float.toUInt8 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(42));
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_float_to_uint8_overflow() {
        let a = float_bits(1000.0);
        let result = reduce_float_to_uint8(&[&a]).expect("Float.toUInt8 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(u8::MAX as u64));
        } else {
            panic!("Expected Nat literal u8::MAX for overflow");
        }
    }

    #[test]
    fn test_float_to_uint16() {
        let a = float_bits(1024.75);
        let result = reduce_float_to_uint16(&[&a]).expect("Float.toUInt16 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(1024));
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_float_to_uint16_overflow() {
        let a = float_bits(100000.0);
        let result = reduce_float_to_uint16(&[&a]).expect("Float.toUInt16 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(u16::MAX as u64));
        } else {
            panic!("Expected Nat literal u16::MAX for overflow");
        }
    }

    #[test]
    fn test_float_to_uint32() {
        let a = float_bits(42.7);
        let result = reduce_float_to_uint32(&[&a]).expect("Float.toUInt32 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(42));
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_float_to_uint32_nan() {
        let a = float_bits(f64::NAN);
        let result = reduce_float_to_uint32(&[&a]).expect("Float.toUInt32 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0 for NaN");
        }
    }

    #[test]
    fn test_float_to_uint32_overflow() {
        let a = float_bits(1e15);
        let result = reduce_float_to_uint32(&[&a]).expect("Float.toUInt32 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(u32::MAX as u64));
        } else {
            panic!("Expected Nat literal u32::MAX for overflow");
        }
    }

    #[test]
    fn test_float_to_uint64() {
        let a = float_bits(4096.5);
        let result = reduce_float_to_uint64(&[&a]).expect("Float.toUInt64 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(4096));
        } else {
            panic!("Expected Nat literal");
        }
    }

    #[test]
    fn test_float_to_uint64_negative() {
        let a = float_bits(-1.0);
        let result = reduce_float_to_uint64(&[&a]).expect("Float.toUInt64 should reduce");
        if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0 for negative Float");
        }
    }

    // --- Float functions ---

    #[test]
    fn test_float_sqrt() {
        let a = float_bits(4.0);
        let result = reduce_float_sqrt(&[&a]).expect("Float.sqrt should reduce");
        assert!((result_f64(&result) - 2.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_abs_positive() {
        let a = float_bits(NEAR_PI);
        let result = reduce_float_abs(&[&a]).expect("Float.abs should reduce");
        assert!((result_f64(&result) - NEAR_PI).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_abs_negative() {
        let a = float_bits(-NEAR_PI);
        let result = reduce_float_abs(&[&a]).expect("Float.abs should reduce");
        assert!((result_f64(&result) - NEAR_PI).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_ceil() {
        let a = float_bits(2.3);
        let result = reduce_float_ceil(&[&a]).expect("Float.ceil should reduce");
        assert!((result_f64(&result) - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_floor() {
        let a = float_bits(2.7);
        let result = reduce_float_floor(&[&a]).expect("Float.floor should reduce");
        assert!((result_f64(&result) - 2.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_round() {
        let a = float_bits(2.5);
        let result = reduce_float_round(&[&a]).expect("Float.round should reduce");
        assert!((result_f64(&result) - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_float_is_nan_true() {
        let a = float_bits(f64::NAN);
        let result = reduce_float_is_nan(&[&a]).expect("Float.isNaN should reduce");
        assert!(result_bool(&result));
    }

    #[test]
    fn test_float_is_nan_false() {
        let a = float_bits(1.0);
        let result = reduce_float_is_nan(&[&a]).expect("Float.isNaN should reduce");
        assert!(!result_bool(&result));
    }

    #[test]
    fn test_float_is_inf_true() {
        let a = float_bits(f64::INFINITY);
        let result = reduce_float_is_inf(&[&a]).expect("Float.isInf should reduce");
        assert!(result_bool(&result));
    }

    #[test]
    fn test_float_is_inf_false() {
        let a = float_bits(1.0);
        let result = reduce_float_is_inf(&[&a]).expect("Float.isInf should reduce");
        assert!(!result_bool(&result));
    }

    #[test]
    fn test_float_is_finite_true() {
        let a = float_bits(1.0);
        let result = reduce_float_is_finite(&[&a]).expect("Float.isFinite should reduce");
        assert!(result_bool(&result));
    }

    #[test]
    fn test_float_is_finite_nan() {
        let a = float_bits(f64::NAN);
        let result = reduce_float_is_finite(&[&a]).expect("Float.isFinite should reduce");
        assert!(!result_bool(&result));
    }

    // --- Edge cases ---

    #[test]
    fn test_float_ops_insufficient_args() {
        assert!(reduce_float_add(&[&Expr::nat_lit(0)]).is_none());
        assert!(reduce_float_add(&[]).is_none());
        assert!(reduce_float_neg(&[]).is_none());
        assert!(reduce_float_beq(&[&Expr::nat_lit(0)]).is_none());
        assert!(reduce_float_of_scientific(&[&Expr::nat_lit(0)]).is_none());
    }

    #[test]
    fn test_float_ops_non_literal_returns_none() {
        let var = Expr::const_(Name::from_string("x"), vec![]);
        assert!(reduce_float_add(&[&var, &Expr::nat_lit(0)]).is_none());
        assert!(reduce_float_neg(&[&var]).is_none());
        assert!(reduce_float_of_nat(&[&var]).is_none());
    }

    // --- Registration ---

    #[test]
    fn test_float_reducers_registered() {
        let mut env = Environment::new();
        env.init_float_native_reducers();

        assert!(env.get_native_reducer(&names::FLOAT_ADD).is_some());
        assert!(env.get_native_reducer(&names::FLOAT_SUB).is_some());
        assert!(env.get_native_reducer(&names::FLOAT_MUL).is_some());
        assert!(env.get_native_reducer(&names::FLOAT_DIV).is_some());
        assert!(env.get_native_reducer(&names::FLOAT_NEG).is_some());
        assert!(env.get_native_reducer(&names::FLOAT_BEQ).is_some());
        assert!(env.get_native_reducer(&names::FLOAT_BLT).is_some());
        assert!(env.get_native_reducer(&names::FLOAT_BLE).is_some());
        assert!(env.get_native_reducer(&names::FLOAT_DEC_EQ).is_some());
        assert!(env.get_native_reducer(&names::FLOAT_OF_NAT).is_some());
        assert!(env.get_native_reducer(&names::FLOAT_OF_INT).is_some());
        assert!(env
            .get_native_reducer(&names::FLOAT_OF_SCIENTIFIC)
            .is_some());
        assert!(env.get_native_reducer(&names::FLOAT_TO_STRING).is_some());
        assert!(env.get_native_reducer(&names::FLOAT_SQRT).is_some());
        assert!(env.get_native_reducer(&names::FLOAT_IS_NAN).is_some());
    }

    /// `Float.decEq` is *structural on the bit pattern* and sorry-free, and its
    /// output type-checks against the prelude (which now defines `Float`,
    /// `Float.mk`, and `Float.val`). This pins the respec the previous f64-based
    /// reducer got wrong: `+0.0` and `-0.0` have distinct bits so they are
    /// `isFalse` (distinct under `@Eq Float`), and two NaNs with identical bits
    /// are `isTrue` — the opposite of IEEE `==`.
    #[test]
    fn test_float_dec_eq_is_structural_and_sound() {
        use crate::tc::TypeChecker;
        fn mentions_sorry(e: &Expr) -> bool {
            match e.kind() {
                ExprKind::Const(n, _) => {
                    let s = n.to_string();
                    s == "sorryAx" || s == "sorry"
                }
                ExprKind::App(f, a) => mentions_sorry(f) || mentions_sorry(a),
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    mentions_sorry(t) || mentions_sorry(b)
                }
                ExprKind::Let(_, t, v, b, _) => {
                    mentions_sorry(t) || mentions_sorry(v) || mentions_sorry(b)
                }
                _ => false,
            }
        }
        fn is_dec(e: &Expr, ctor: &str) -> bool {
            matches!(e.get_app_fn().kind(),
                ExprKind::Const(name, _) if *name == Name::from_string(ctor))
        }
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let mk = |bits: u64| {
            Expr::app(
                Expr::const_(Name::from_string("Float.mk"), vec![]),
                Expr::nat_lit(bits),
            )
        };
        let pos_zero = 0u64;
        let neg_zero = (-0.0f64).to_bits(); // 0x8000_0000_0000_0000
        let nan = f64::NAN.to_bits();
        let cases = [
            (pos_zero, pos_zero, true),  // +0.0 = +0.0
            (nan, nan, true),            // bit-identical NaN = NaN (≠ IEEE ==)
            (pos_zero, neg_zero, false), // +0.0 ≠ -0.0 (≠ IEEE ==)
            (1u64, 2u64, false),
        ];
        for (x, y, want_true) in cases {
            let a = mk(x);
            let b = mk(y);
            let term = reduce_float_dec_eq(&[&a, &b]).expect("Float.decEq reduces on mk-form");
            assert!(
                !mentions_sorry(&term),
                "Float.decEq must be sorry-free: {term:?}"
            );
            assert!(
                is_dec(
                    &term,
                    if want_true {
                        "Decidable.isTrue"
                    } else {
                        "Decidable.isFalse"
                    }
                ),
                "Float.decEq({x:#x}, {y:#x}) wrong constructor",
            );
            let _ = tc
                .infer_type(&term)
                .unwrap_or_else(|e| panic!("Float.decEq output type-checks: {e:?}"));
        }
    }

    /// Track Z: `init_float_arith_ops` registers the `Float.toUInt{8,16,32,64}`
    /// constants (not just the native reducers) so trust-ir `Semantics/Cast.lean`
    /// `semCast`'s `v.toUInt64.toNat` resolves the dot-method instead of failing
    /// with "Unknown projection field toUInt64 on structure Float". Each must be a
    /// genuine `Float → UIntN` constant whose type kernel-checks, and the whole
    /// thing must stay axiom-free (the placeholder body is `UIntN.mk Nat.zero`, an
    /// Opaque, not an Axiom).
    #[test]
    fn test_float_to_uint_constants_registered() {
        use crate::name::Name;
        let mut env = Environment::with_prelude();
        env.init_float_arith_ops()
            .expect("init_float_arith_ops succeeds");

        for (width, uint_ty) in [
            ("8", "UInt8"),
            ("16", "UInt16"),
            ("32", "UInt32"),
            ("64", "UInt64"),
        ] {
            let cname = Name::from_string(&format!("Float.toUInt{width}"));
            let info = env
                .get_const(&cname)
                .unwrap_or_else(|| panic!("Float.toUInt{width} must be registered"));
            // Type is `Float → UIntN`: a Pi from Float to the unsigned width.
            match info.type_.kind() {
                ExprKind::Pi(_, dom, cod) => {
                    assert!(
                        matches!(dom.kind(), ExprKind::Const(n, _) if n.to_string() == "Float"),
                        "Float.toUInt{width} domain must be Float, got {:?}",
                        dom.kind()
                    );
                    assert!(
                        matches!(cod.kind(), ExprKind::Const(n, _) if n.to_string() == uint_ty),
                        "Float.toUInt{width} codomain must be {uint_ty}, got {:?}",
                        cod.kind()
                    );
                }
                other => panic!("Float.toUInt{width} type must be a Pi, got {other:?}"),
            }
        }

        // No axiom debt introduced: the conversions are Opaque placeholders, so
        // none of them appear as kernel axioms.
        for width in ["8", "16", "32", "64"] {
            let cname = Name::from_string(&format!("Float.toUInt{width}"));
            let info = env.get_const(&cname).expect("registered above");
            assert_ne!(
                info.kind,
                crate::env::types::ConstantKind::Axiom,
                "Float.toUInt{width} must not be an Axiom (it is an Opaque placeholder)"
            );
        }
    }
}
