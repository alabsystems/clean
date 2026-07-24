// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceProgram, Value};

#[test]
fn test_source_program_parses_try_operator() {
    let source = r#"
        fn try_it(x: Result<u32, u32>) -> Result<u32, u32> {
            let val: u32 = x?;
            Result::Ok(val)
        }

        fn main() -> u32 {
            let ok: Result<u32, u32> = Result::Ok(42u32);
            let result: Result<u32, u32> = try_it(ok);
            match result {
                Result::Ok(v) => v,
                Result::Err(_e) => 0u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("? operator should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}
