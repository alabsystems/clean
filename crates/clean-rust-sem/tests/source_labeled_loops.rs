// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for labeled loop break/continue in source-ingested programs.

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

#[test]
fn test_source_labeled_break_outer_loop() {
    let source = r#"
        fn main() -> u32 {
            let mut result = 0u32;
            'outer: loop {
                let mut inner_count = 0u32;
                loop {
                    inner_count += 1u32;
                    if inner_count == 3u32 {
                        break 'outer;
                    }
                }
                // This should never execute
                result = 99u32;
            }
            result
        }
    "#;

    let program = SourceProgram::parse(source).expect("labeled break should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    // break 'outer exits the outer loop, result stays 0
    assert_eq!(result.value(), Some(Value::u32(0)));
}

#[test]
fn test_source_labeled_break_with_value() {
    let source = r#"
        fn main() -> u32 {
            let result = 'outer: loop {
                let mut i = 0u32;
                loop {
                    i += 1u32;
                    if i == 5u32 {
                        break 'outer 42u32;
                    }
                }
            };
            result
        }
    "#;

    let program = SourceProgram::parse(source).expect("labeled break with value should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_labeled_continue_outer() {
    let source = r#"
        fn main() -> u32 {
            let mut sum = 0u32;
            let mut outer_count = 0u32;
            'outer: while outer_count < 5u32 {
                outer_count += 1u32;
                let mut inner_count = 0u32;
                while inner_count < 3u32 {
                    inner_count += 1u32;
                    if inner_count == 2u32 {
                        continue 'outer;
                    }
                }
                // Only reached if inner loop completes without continue 'outer
                // This never happens because inner_count always hits 2
                sum += 10u32;
            }
            // outer_count increments 5 times, but sum stays 0
            // because continue 'outer skips the sum += 10 every time
            outer_count + sum
        }
    "#;

    let program = SourceProgram::parse(source).expect("labeled continue should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(5)));
}

#[test]
fn test_source_labeled_for_loop_break() {
    let source = r#"
        fn main() -> u32 {
            let mut found = 0u32;
            let matrix = [[1u32, 2u32, 3u32], [4u32, 5u32, 6u32], [7u32, 8u32, 9u32]];
            'search: for row in matrix {
                for val in row {
                    if val == 5u32 {
                        found = val;
                        break 'search;
                    }
                }
            }
            found
        }
    "#;

    let program = SourceProgram::parse(source).expect("labeled for break should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(5)));
}

#[test]
fn test_source_unlabeled_break_still_innermost() {
    // Verify that unlabeled break in the presence of labeled loops
    // still targets only the innermost loop.
    let source = r#"
        fn main() -> u32 {
            let mut result = 0u32;
            'outer: loop {
                let mut i = 0u32;
                loop {
                    i += 1u32;
                    if i == 3u32 {
                        break;  // breaks inner loop only
                    }
                }
                result = i;
                break 'outer;
            }
            result
        }
    "#;

    let program = SourceProgram::parse(source).expect("mixed break should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    // Inner break exits inner loop with i=3, then result=3, then break 'outer
    assert_eq!(result.value(), Some(Value::u32(3)));
}
