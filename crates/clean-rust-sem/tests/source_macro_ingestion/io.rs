// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceProgram, Value};

#[test]
fn test_source_program_skips_println_statement() {
    let source = r#"
        fn main() -> u32 {
            println!("computing...");
            let x: u32 = 41u32;
            println!("x = {}", x);
            x + 1u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("println! statements should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_eprintln_and_write_statements() {
    let source = r#"
        fn main() -> u32 {
            eprintln!("debug info");
            eprint!("no newline");
            print!("stdout");
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("I/O macros should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_std_qualified_io_macros() {
    let source = r#"
        fn main() -> u32 {
            std::println!("computing...");
            std::eprint!("still computing");
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("std-qualified I/O macros should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
