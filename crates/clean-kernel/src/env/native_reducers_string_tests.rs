// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended String native reducers.

use super::*;
use crate::expr::{ExprKind, Literal};
use crate::name::Name;

// === String.get tests ===

#[test]
fn test_reduce_string_get_ascii() {
    let s = Expr::str_lit("hello");
    let pos = Expr::nat_lit(0);
    let result = reduce_string_get(&[&s, &pos]);
    assert!(result.is_some(), "String.get should reduce");
    let result = result.unwrap();
    // Should be Char.mk 104 ('h')
    let args = result.get_app_args();
    if let Some(n_expr) = args.first() {
        let n = get_nat_val(n_expr).expect("should be nat");
        assert_eq!(n, 104, "Expected 'h' (104), got {n}");
    } else {
        panic!("Expected Char.mk with arg");
    }
}

#[test]
fn test_reduce_string_get_second_char() {
    let s = Expr::str_lit("hello");
    let pos = Expr::nat_lit(1);
    let result = reduce_string_get(&[&s, &pos]);
    assert!(result.is_some());
    let result = result.unwrap();
    let args = result.get_app_args();
    let n = get_nat_val(args[0]).unwrap();
    assert_eq!(n, 101, "Expected 'e' (101), got {n}");
}

#[test]
fn test_reduce_string_get_out_of_bounds() {
    let s = Expr::str_lit("hi");
    let pos = Expr::nat_lit(10);
    let result = reduce_string_get(&[&s, &pos]);
    assert!(result.is_some());
    let result = result.unwrap();
    let args = result.get_app_args();
    let n = get_nat_val(args[0]).unwrap();
    assert_eq!(n, 0, "Out of bounds should return '\\0'");
}

#[test]
fn test_reduce_string_get_unicode() {
    let s = Expr::str_lit("caf\u{00e9}");
    let pos = Expr::nat_lit(3);
    let result = reduce_string_get(&[&s, &pos]);
    assert!(result.is_some());
    let result = result.unwrap();
    let args = result.get_app_args();
    let n = get_nat_val(args[0]).unwrap();
    assert_eq!(n, 0xe9, "Expected e-acute (0xe9), got {n:#x}");
}

// === String.next tests ===

#[test]
fn test_reduce_string_next_ascii() {
    let s = Expr::str_lit("hello");
    let pos = Expr::nat_lit(0);
    let result = reduce_string_next(&[&s, &pos]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(1));
    } else {
        panic!("Expected Nat literal");
    }
}

#[test]
fn test_reduce_string_next_unicode() {
    let s = Expr::str_lit("caf\u{00e9}");
    let pos = Expr::nat_lit(3);
    let result = reduce_string_next(&[&s, &pos]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(5));
    } else {
        panic!("Expected Nat literal");
    }
}

#[test]
fn test_reduce_string_next_past_end() {
    let s = Expr::str_lit("hi");
    let pos = Expr::nat_lit(10);
    let result = reduce_string_next(&[&s, &pos]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(11));
    } else {
        panic!("Expected Nat literal");
    }
}

// === String.prev tests ===

#[test]
fn test_reduce_string_prev_at_start() {
    let s = Expr::str_lit("hello");
    let pos = Expr::nat_lit(0);
    let result = reduce_string_prev(&[&s, &pos]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(0));
    } else {
        panic!("Expected Nat literal 0");
    }
}

#[test]
fn test_reduce_string_prev_ascii() {
    let s = Expr::str_lit("hello");
    let pos = Expr::nat_lit(3);
    let result = reduce_string_prev(&[&s, &pos]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
        assert_eq!(n.to_u64(), Some(2));
    } else {
        panic!("Expected Nat literal 2");
    }
}

// === String.atEnd tests ===

#[test]
fn test_reduce_string_at_end_false() {
    let s = Expr::str_lit("hello");
    let pos = Expr::nat_lit(0);
    let result = reduce_string_at_end(&[&s, &pos]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.false"));
    } else {
        panic!("Expected Bool.false");
    }
}

#[test]
fn test_reduce_string_at_end_true() {
    let s = Expr::str_lit("hi");
    let pos = Expr::nat_lit(2);
    let result = reduce_string_at_end(&[&s, &pos]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.true"));
    } else {
        panic!("Expected Bool.true");
    }
}

// === String.extract tests ===

#[test]
fn test_reduce_string_extract_basic() {
    let s = Expr::str_lit("hello world");
    let start = Expr::nat_lit(0);
    let stop = Expr::nat_lit(5);
    let result = reduce_string_extract(&[&s, &start, &stop]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
        assert_eq!(&**r, "hello");
    } else {
        panic!("Expected string literal");
    }
}

#[test]
fn test_reduce_string_extract_empty() {
    let s = Expr::str_lit("hello");
    let start = Expr::nat_lit(3);
    let stop = Expr::nat_lit(3);
    let result = reduce_string_extract(&[&s, &start, &stop]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
        assert_eq!(&**r, "");
    } else {
        panic!("Expected empty string literal");
    }
}

// === String.intercalate tests ===

#[test]
fn test_reduce_string_intercalate_empty_list() {
    let sep = Expr::str_lit(", ");
    let nil = Expr::const_(
        Name::from_string("List.nil"),
        vec![crate::level::Level::succ(crate::level::Level::zero())],
    );
    let nil_string = Expr::app(nil, Expr::const_(Name::from_string("String"), vec![]));
    let result = reduce_string_intercalate(&[&sep, &nil_string]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
        assert_eq!(&**r, "");
    } else {
        panic!("Expected empty string literal");
    }
}

// === String.isPrefixOf tests ===

#[test]
fn test_reduce_string_is_prefix_of_true() {
    let prefix = Expr::str_lit("hel");
    let s = Expr::str_lit("hello");
    let result = reduce_string_is_prefix_of(&[&prefix, &s]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.true"));
    } else {
        panic!("Expected Bool.true");
    }
}

#[test]
fn test_reduce_string_is_prefix_of_false() {
    let prefix = Expr::str_lit("world");
    let s = Expr::str_lit("hello");
    let result = reduce_string_is_prefix_of(&[&prefix, &s]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.false"));
    } else {
        panic!("Expected Bool.false");
    }
}

// === String.front tests ===

#[test]
fn test_reduce_string_front() {
    let s = Expr::str_lit("hello");
    let result = reduce_string_front(&[&s]);
    assert!(result.is_some());
    let result = result.unwrap();
    let args = result.get_app_args();
    let n = get_nat_val(args[0]).unwrap();
    assert_eq!(n, 104, "Expected 'h' (104)");
}

#[test]
fn test_reduce_string_front_empty() {
    let s = Expr::str_lit("");
    let result = reduce_string_front(&[&s]);
    assert!(result.is_some());
    let result = result.unwrap();
    let args = result.get_app_args();
    let n = get_nat_val(args[0]).unwrap();
    assert_eq!(n, 0, "Empty string front should return '\\0'");
}

// === String.singleton tests ===

#[test]
fn test_reduce_string_singleton() {
    let c = mk_char_expr('A');
    let result = reduce_string_singleton(&[&c]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::String(s)) = result.unwrap().kind() {
        assert_eq!(&**s, "A");
    } else {
        panic!("Expected string literal");
    }
}

// === String.take / String.drop tests ===

#[test]
fn test_reduce_string_take() {
    let s = Expr::str_lit("hello");
    let n = Expr::nat_lit(3);
    let result = reduce_string_take(&[&s, &n]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
        assert_eq!(&**r, "hel");
    } else {
        panic!("Expected string literal");
    }
}

#[test]
fn test_reduce_string_drop() {
    let s = Expr::str_lit("hello");
    let n = Expr::nat_lit(3);
    let result = reduce_string_drop(&[&s, &n]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
        assert_eq!(&**r, "lo");
    } else {
        panic!("Expected string literal");
    }
}

// === String.toLower / String.toUpper tests ===

#[test]
fn test_reduce_string_to_lower() {
    let s = Expr::str_lit("Hello");
    let result = reduce_string_to_lower(&[&s]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
        assert_eq!(&**r, "hello");
    } else {
        panic!("Expected string literal");
    }
}

#[test]
fn test_reduce_string_to_upper() {
    let s = Expr::str_lit("Hello");
    let result = reduce_string_to_upper(&[&s]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
        assert_eq!(&**r, "HELLO");
    } else {
        panic!("Expected string literal");
    }
}

// === String.hash tests ===

#[test]
fn test_reduce_string_hash_deterministic() {
    let s = Expr::str_lit("hello");
    let r1 = reduce_string_hash(&[&s]);
    let r2 = reduce_string_hash(&[&s]);
    assert!(r1.is_some());
    assert!(r2.is_some());
    // Same input should give same hash
    let h1 = get_nat_val(&r1.unwrap()).unwrap();
    let h2 = get_nat_val(&r2.unwrap()).unwrap();
    assert_eq!(h1, h2, "Hash should be deterministic");
}

#[test]
fn test_reduce_string_hash_different_strings() {
    let s1 = Expr::str_lit("hello");
    let s2 = Expr::str_lit("world");
    let h1 = get_nat_val(&reduce_string_hash(&[&s1]).unwrap()).unwrap();
    let h2 = get_nat_val(&reduce_string_hash(&[&s2]).unwrap()).unwrap();
    assert_ne!(h1, h2, "Different strings should have different hashes");
}

#[test]
fn test_reduce_string_hash_empty() {
    let s = Expr::str_lit("");
    let result = reduce_string_hash(&[&s]);
    assert!(result.is_some());
    let h = get_nat_val(&result.unwrap()).unwrap();
    // MurmurHash64A("", seed=11) — matches Lean 4's lean_string_hash.
    // Computed: h=11, finalize → h ^= h>>47 → h *= M → h ^= h>>47
    let expected = murmur_hash_64a(b"", 11);
    assert_eq!(
        h, expected,
        "Empty string hash should match MurmurHash64A(\"\", 11)"
    );
}

// --- MurmurHash64A unit tests (Part of #3249) ---
// Verifies our Rust MurmurHash64A matches the reference C implementation
// from Lean 4 src/runtime/hash.cpp.

#[test]
fn test_murmur_hash_64a_known_values() {
    // MurmurHash64A is deterministic: verify specific byte inputs.
    // These are self-consistent tests; if we ever get Lean 4 reference values,
    // we can replace with exact cross-validated hashes.
    let h1 = murmur_hash_64a(b"hello", 11);
    let h2 = murmur_hash_64a(b"hello", 11);
    assert_eq!(h1, h2, "Same input must produce same hash");

    let h3 = murmur_hash_64a(b"world", 11);
    assert_ne!(h1, h3, "Different input must produce different hash");

    // Seed matters
    let h4 = murmur_hash_64a(b"hello", 7);
    assert_ne!(h1, h4, "Different seeds must produce different hashes");
}

#[test]
fn test_murmur_hash_64a_8_byte_aligned() {
    // Test with exactly 8 bytes (exercises the main loop without tail)
    let h = murmur_hash_64a(b"12345678", 11);
    let h2 = murmur_hash_64a(b"12345678", 11);
    assert_eq!(h, h2);
}

#[test]
fn test_murmur_hash_64a_16_bytes() {
    // Test with 16 bytes (two full 8-byte blocks, no tail)
    let h = murmur_hash_64a(b"1234567890abcdef", 11);
    let h2 = murmur_hash_64a(b"1234567890abcdef", 11);
    assert_eq!(h, h2);
}

#[test]
fn test_string_hash_uses_seed_11() {
    // Lean 4 lean_string_hash uses seed=11. Verify the reducer matches
    // direct MurmurHash64A(bytes, 11) call.
    let s = Expr::str_lit("hello");
    let reducer_hash = get_nat_val(&reduce_string_hash(&[&s]).unwrap()).unwrap();
    let direct_hash = murmur_hash_64a(b"hello", 11);
    assert_eq!(
        reducer_hash, direct_hash,
        "String.hash reducer must use MurmurHash64A with seed 11"
    );
}

// --- Lean 4 cross-validated String.hash reference values (Part of #3249) ---
// These values are computed from Lean 4's exact C implementation of
// MurmurHash64A (src/runtime/hash.cpp) with seed 11 (src/runtime/object.cpp:2415).
// Cross-validated against a compiled C reference program.

#[test]
fn test_string_hash_lean4_reference_hello() {
    let s = Expr::str_lit("hello");
    let h = get_nat_val(&reduce_string_hash(&[&s]).unwrap()).unwrap();
    assert_eq!(
        h, 9821865621596011261,
        "String.hash(\"hello\") must match Lean 4"
    );
}

#[test]
fn test_string_hash_lean4_reference_world() {
    let s = Expr::str_lit("world");
    let h = get_nat_val(&reduce_string_hash(&[&s]).unwrap()).unwrap();
    assert_eq!(
        h, 18410667061337751906,
        "String.hash(\"world\") must match Lean 4"
    );
}

#[test]
fn test_string_hash_lean4_reference_empty() {
    let s = Expr::str_lit("");
    let h = get_nat_val(&reduce_string_hash(&[&s]).unwrap()).unwrap();
    assert_eq!(
        h, 9877294847684254529,
        "String.hash(\"\") must match Lean 4"
    );
}

#[test]
fn test_string_hash_lean4_reference_nat() {
    let s = Expr::str_lit("Nat");
    let h = get_nat_val(&reduce_string_hash(&[&s]).unwrap()).unwrap();
    assert_eq!(
        h, 7337748955408223552,
        "String.hash(\"Nat\") must match Lean 4"
    );
}

// === Registration test ===

#[test]
fn test_string_native_reducers_registered() {
    let mut env = Environment::new();
    env.init_string_native_reducers();

    assert!(env.get_native_reducer(&names::STRING_GET).is_some());
    assert!(env.get_native_reducer(&names::STRING_NEXT).is_some());
    assert!(env.get_native_reducer(&names::STRING_PREV).is_some());
    assert!(env.get_native_reducer(&names::STRING_UTF8_AT_END).is_some());
    assert!(env
        .get_native_reducer(&names::STRING_UTF8_EXTRACT)
        .is_some());
    assert!(env.get_native_reducer(&names::STRING_INTERCALATE).is_some());
    assert!(env
        .get_native_reducer(&names::STRING_IS_PREFIX_OF)
        .is_some());
    assert!(env.get_native_reducer(&names::STRING_FRONT).is_some());
    assert!(env.get_native_reducer(&names::STRING_DEC_LT).is_some());
    assert!(env.get_native_reducer(&names::STRING_HASH).is_some());
    assert!(env.get_native_reducer(&names::STRING_SINGLETON).is_some());
    assert!(env.get_native_reducer(&names::STRING_TAKE).is_some());
    assert!(env.get_native_reducer(&names::STRING_DROP).is_some());
    assert!(env.get_native_reducer(&names::STRING_TO_LOWER).is_some());
    assert!(env.get_native_reducer(&names::STRING_TO_UPPER).is_some());
}

// === Regression: non-char-boundary byte positions must NOT panic the kernel ===

#[test]
fn test_string_reducers_decline_on_non_char_boundary() {
    // "é" is 2 bytes (0xC3 0xA9); byte position 1 is INTERIOR (not a char boundary).
    // Slicing `s[1..]` would panic the trusted kernel mid-whnf; the reducers must
    // instead decline (return None) so the kernel falls back to definitional
    // unfolding. Witnessed by `String.get/next/prev "é" ⟨1⟩`.
    let s = Expr::str_lit("é");
    let interior = Expr::nat_lit(1);
    assert!(
        reduce_string_get(&[&s, &interior]).is_none(),
        "String.get at an interior UTF-8 byte must decline, not panic"
    );
    assert!(
        reduce_string_next(&[&s, &interior]).is_none(),
        "String.next at an interior UTF-8 byte must decline, not panic"
    );
    assert!(
        reduce_string_prev(&[&s, &interior]).is_none(),
        "String.prev at an interior UTF-8 byte must decline, not panic"
    );
}

#[test]
fn test_string_reducers_still_reduce_on_valid_boundary() {
    // The guard must not break valid char-boundary reductions. "aé": 'a' at byte 0
    // (1 byte), 'é' at byte 1 (2 bytes), len 3.
    let s = Expr::str_lit("aé");
    assert_eq!(
        reduce_string_next(&[&s, &Expr::nat_lit(0)]),
        Some(Expr::nat_lit(1)),
        "next past 'a' -> byte 1"
    );
    assert_eq!(
        reduce_string_next(&[&s, &Expr::nat_lit(1)]),
        Some(Expr::nat_lit(3)),
        "next past 'é' -> byte 3"
    );
    assert!(reduce_string_get(&[&s, &Expr::nat_lit(0)]).is_some());
    assert_eq!(
        reduce_string_prev(&[&s, &Expr::nat_lit(3)]),
        Some(Expr::nat_lit(1)),
        "prev from end -> start of 'é' at byte 1"
    );
}
