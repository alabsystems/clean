// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceProgram, Value};

#[test]
fn test_source_program_runs_dbg_macro() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 42u32;
            dbg!(x)
        }
    "#;

    let program = SourceProgram::parse(source).expect("dbg!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_dbg_macro_with_single_arg_trailing_comma() {
    let source = r#"
        fn main() -> u32 {
            dbg!(42u32,)
        }
    "#;

    let program = SourceProgram::parse(source).expect("dbg!(expr,) should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_dbg_macro_with_multiple_args() {
    let source = r#"
        fn main() -> u32 {
            let pair = dbg!(20u32, 22u32);
            pair.0 + pair.1
        }
    "#;

    let program = SourceProgram::parse(source).expect("dbg!(a, b) should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
