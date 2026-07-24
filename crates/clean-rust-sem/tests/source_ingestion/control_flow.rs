// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceProgram, Value};

#[test]
fn test_source_program_runs_logical_and() {
    let source = r#"
        fn main() -> u32 {
            let a: bool = true;
            let b: bool = true;
            if a && b {
                1u32
            } else {
                0u32
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("&& should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(1)));
}

#[test]
fn test_source_program_runs_logical_or() {
    let source = r#"
        fn main() -> u32 {
            let a: bool = false;
            let b: bool = true;
            if a || b {
                1u32
            } else {
                0u32
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("|| should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(1)));
}

#[test]
fn test_source_program_logical_and_short_circuits() {
    let source = r#"
        fn main() -> u32 {
            let a: bool = false;
            let b: bool = true;
            if a && b {
                1u32
            } else {
                0u32
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("&& short-circuit should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(0)));
}

#[test]
fn test_source_program_runs_compound_assignment() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 10u32;
            x += 5u32;
            x -= 3u32;
            x *= 2u32;
            x
        }
    "#;

    let program = SourceProgram::parse(source).expect("compound assignment should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(24)));
}

#[test]
fn test_source_program_runs_const_block_expression() {
    let source = r#"
        fn main() -> u32 {
            let answer: u32 = const {
                let base: u32 = 40u32;
                base + 2u32
            };
            answer
        }
    "#;

    let program = SourceProgram::parse(source).expect("const block expression should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_while_loop_with_mutation() {
    let source = r#"
        fn main() -> u32 {
            let mut sum: u32 = 0u32;
            let mut i: u32 = 1u32;
            while i <= 5u32 {
                sum += i;
                i += 1u32;
            }
            sum
        }
    "#;

    let program = SourceProgram::parse(source).expect("while loop with mutation should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(15)));
}

#[test]
fn test_source_program_runs_tuple_struct_pattern_match() {
    let source = r#"
        struct Pair(u32, u32);

        fn main() -> u32 {
            let pair = Pair(40u32, 2u32);
            match pair {
                Pair(a, b) => a + b,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("tuple struct pattern match should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_block_local_tuple_struct_pattern_match() {
    let source = r#"
        fn main() -> u32 {
            struct Point(u32, u32);
            let p = Point(10u32, 32u32);
            match p {
                Point(x, y) => x + y,
            }
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("block-local tuple struct pattern should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_type_alias_tuple_struct_pattern_match() {
    let source = r#"
        struct Pair(u32, u32);
        type PairAlias = Pair;

        fn main() -> u32 {
            let pair = PairAlias(40u32, 2u32);
            match pair {
                PairAlias(a, b) => a + b,
            }
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("type-alias tuple struct pattern should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_let_destructure_tuple_struct() {
    let source = r#"
        struct Pair(u32, u32);

        fn main() -> u32 {
            let pair = Pair(40u32, 2u32);
            let Pair(a, b) = pair;
            a + b
        }
    "#;

    let program = SourceProgram::parse(source).expect("let destructure tuple struct should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_if_let_enum() {
    let source = r#"
        enum Maybe {
            Nothing,
            Just(u32),
        }

        fn main() -> u32 {
            let value = Maybe::Just(42u32);
            if let Maybe::Just(inner) = value {
                inner
            } else {
                0u32
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("if let should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_if_let_no_match_takes_else() {
    let source = r#"
        enum Maybe {
            Nothing,
            Just(u32),
        }

        fn main() -> u32 {
            let value = Maybe::Nothing;
            if let Maybe::Just(inner) = value {
                inner
            } else {
                99u32
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("if let else branch should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(99)));
}

#[test]
fn test_source_program_runs_while_let_enum() {
    let source = r#"
        enum Maybe {
            Nothing,
            Just(u32),
        }

        fn main() -> u32 {
            let mut sum: u32 = 0u32;
            let mut count: u32 = 3u32;
            while let Maybe::Just(n) = Maybe::Just(count) {
                if n == 0u32 {
                    break;
                }
                sum += n;
                count -= 1u32;
            }
            sum
        }
    "#;

    let program = SourceProgram::parse(source).expect("while let should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(6)));
}

#[test]
fn test_source_program_runs_let_else_tuple_pattern() {
    let source = r#"
        fn main() -> u32 {
            let pair = (40u32, 2u32);
            let (a, 2u32) = pair else {
                return 0u32;
            };
            a + 2u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("let-else tuple pattern should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_let_else_tuple_pattern_mismatch_diverges() {
    let source = r#"
        fn main() -> u32 {
            let pair = (40u32, 1u32);
            let (a, 2u32) = pair else {
                return 99u32;
            };
            a
        }
    "#;

    let program = SourceProgram::parse(source).expect("let-else tuple mismatch should still parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(99)));
}

#[test]
fn test_source_program_runs_slice_pattern_exact() {
    let source = r#"
        fn main() -> u32 {
            let arr = [10u32, 20u32, 12u32];
            match arr {
                [a, b, c] => a + b + c,
                _ => 0u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("exact slice pattern should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_slice_pattern_with_rest() {
    let source = r#"
        fn main() -> u32 {
            let arr = [10u32, 20u32, 12u32, 100u32];
            match arr {
                [first, .., last] => first + last,
                _ => 0u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("slice pattern with .. should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(110)));
}

#[test]
fn test_source_program_runs_slice_pattern_prefix_only() {
    let source = r#"
        fn main() -> u32 {
            let arr = [42u32, 100u32, 200u32];
            match arr {
                [first, ..] => first,
                _ => 0u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("prefix slice pattern should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_slice_pattern_empty() {
    let source = r#"
        fn main() -> u32 {
            let arr: [u32; 3] = [1u32, 2u32, 3u32];
            match arr {
                [] => 0u32,
                _ => 42u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("empty slice pattern should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_negative_range_pattern() {
    let source = r#"
        fn main() -> u32 {
            let x: i32 = -3i32;
            match x {
                -10i32..=0i32 => 42u32,
                _ => 0u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("negative range pattern should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_signed_min_range_pattern() {
    let source = r#"
        fn main() -> u32 {
            let x: i8 = i8::MIN;
            match x {
                -128i8..=-1i8 => 42u32,
                _ => 0u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("signed minimum range pattern should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_rejects_negative_unsigned_range_pattern() {
    let source = r#"
        fn main() -> u32 {
            let x: u8 = 0u8;
            match x {
                -1u8..=0u8 => 42u32,
                _ => 0u32,
            }
        }
    "#;

    let err =
        SourceProgram::parse(source).expect_err("negative unsigned range pattern should fail");
    match err {
        clean_rust_sem::source::SourceError::Invalid { context, detail } => {
            assert_eq!(context, "literal");
            assert!(detail.contains("unsigned integer literal"));
            assert!(detail.contains("cannot be negated"));
        }
        other => panic!("expected invalid literal error, got {other:?}"),
    }
}

#[test]
fn test_source_program_rejects_out_of_range_isize_range_pattern() {
    let source = r#"
        fn main() -> u32 {
            let x: isize = 0isize;
            match x {
                -9223372036854775809isize..=-1isize => 42u32,
                _ => 0u32,
            }
        }
    "#;

    let err =
        SourceProgram::parse(source).expect_err("out-of-range negative isize range should fail");
    match err {
        clean_rust_sem::source::SourceError::Invalid { context, detail } => {
            assert_eq!(context, "integer literal");
            assert!(detail.contains("out of range"));
            assert!(detail.contains("isize"));
        }
        other => panic!("expected invalid integer literal error, got {other:?}"),
    }
}

#[test]
fn test_source_program_rejects_out_of_range_isize_literal() {
    let source = r#"
        fn main() -> isize {
            9223372036854775808isize
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("out-of-range isize literal should fail");
    match err {
        clean_rust_sem::source::SourceError::Invalid { context, detail } => {
            assert_eq!(context, "integer literal");
            assert!(detail.contains("out of range"));
            assert!(detail.contains("isize"));
        }
        other => panic!("expected invalid integer literal error, got {other:?}"),
    }
}

#[test]
fn test_source_program_rejects_out_of_range_usize_literal() {
    let source = r#"
        fn main() -> usize {
            18446744073709551616usize
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("out-of-range usize literal should fail");
    match err {
        clean_rust_sem::source::SourceError::Invalid { context, detail } => {
            assert_eq!(context, "integer literal");
            assert!(detail.contains("out of range"));
            assert!(detail.contains("usize"));
        }
        other => panic!("expected invalid integer literal error, got {other:?}"),
    }
}
