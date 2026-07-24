// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceProgram, Value};

#[test]
fn test_source_program_runs_matches_macro() {
    let source = r#"
        fn main() -> u32 {
            let ok: Result<u32, u32> = Result::Ok(42u32);
            if matches!(ok, Result::Ok(42u32)) {
                42u32
            } else {
                0u32
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("matches!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_matches_macro_with_guard() {
    let source = r#"
        fn main() -> u32 {
            let ok: Result<u32, u32> = Result::Ok(42u32);
            if matches!(ok, Result::Ok(value) if value > 40u32) {
                42u32
            } else {
                0u32
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("matches! guard should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_core_qualified_matches_macro() {
    let source = r#"
        fn main() -> u32 {
            let ok: Result<u32, u32> = Result::Ok(42u32);
            if core::matches!(ok, Result::Ok(42u32)) {
                42u32
            } else {
                0u32
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("core::matches!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_matches_macro_with_or_pattern_and_trailing_comma() {
    let source = r#"
        struct Pair(u32, u32);

        fn main() -> u32 {
            let pair = Pair(20u32, 22u32);
            if matches!(pair, Pair(20u32, 22u32) | Pair(21u32, 21u32),) {
                42u32
            } else {
                0u32
            }
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("matches! or-pattern with trailing comma should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
