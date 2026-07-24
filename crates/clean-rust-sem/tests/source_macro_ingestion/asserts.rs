// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceProgram, Value};

#[test]
fn test_source_program_runs_assert_macro_passing() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 42u32;
            assert!(x == 42u32);
            x
        }
    "#;

    let program = SourceProgram::parse(source).expect("assert!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_core_qualified_assert_macro_passing() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 42u32;
            core::assert!(x == 42u32);
            x
        }
    "#;

    let program = SourceProgram::parse(source).expect("core::assert!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_assert_macro_aborts_on_false() {
    let source = r#"
        fn main() -> u32 {
            assert!(false);
            0u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("assert!(false) should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Panic(_)),
        "assert!(false) should abort, got: {result:?}"
    );
}

#[test]
fn test_source_program_runs_assert_eq_macro_passing() {
    let source = r#"
        fn main() -> u32 {
            let a: u32 = 42u32;
            let b: u32 = 42u32;
            assert_eq!(a, b);
            a
        }
    "#;

    let program = SourceProgram::parse(source).expect("assert_eq!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_assert_eq_macro_aborts_on_unequal() {
    let source = r#"
        fn main() -> u32 {
            assert_eq!(1u32, 2u32);
            0u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("assert_eq! with unequal args should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Panic(_)),
        "assert_eq!(1, 2) should abort, got: {result:?}"
    );
}

#[test]
fn test_source_program_runs_assert_ne_macro_passing() {
    let source = r#"
        fn main() -> u32 {
            assert_ne!(1u32, 2u32);
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("assert_ne!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_debug_assert_passing() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 42u32;
            debug_assert!(x == 42u32);
            x
        }
    "#;

    let program = SourceProgram::parse(source).expect("debug_assert!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_debug_assert_aborts_on_false() {
    let source = r#"
        fn main() -> u32 {
            debug_assert!(false);
            0u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("debug_assert!(false) should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Panic(_)),
        "debug_assert!(false) should abort, got: {result:?}"
    );
}

#[test]
fn test_source_program_runs_debug_assert_eq_passing() {
    let source = r#"
        fn main() -> u32 {
            let a: u32 = 42u32;
            let b: u32 = 42u32;
            debug_assert_eq!(a, b);
            a
        }
    "#;

    let program = SourceProgram::parse(source).expect("debug_assert_eq!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_debug_assert_ne_passing() {
    let source = r#"
        fn main() -> u32 {
            debug_assert_ne!(1u32, 2u32);
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("debug_assert_ne!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}
