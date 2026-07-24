// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceError, SourceProgram, Value};

#[test]
fn test_source_program_cfg_macro_returns_false() {
    let source = r#"
        fn main() -> u32 {
            if cfg!(target_os = "linux") {
                1u32
            } else {
                42u32
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("cfg!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_env_macro_returns_empty_string() {
    let source = r#"
        fn main() -> bool {
            let value = env!("CLEAN_TEST_ENV");
            value.is_empty()
        }
    "#;

    let program = SourceProgram::parse(source).expect("env!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_program_env_macro_accepts_custom_error_message() {
    let source = r#"
        fn main() -> bool {
            let value = env!("CLEAN_TEST_ENV", "expected compile-time env var");
            value.is_empty()
        }
    "#;

    let program = SourceProgram::parse(source).expect("env!(..., \"message\") should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_program_env_macro_rejects_non_string_custom_error_argument() {
    let source = r#"
        fn main() {
            let _ = env!("CLEAN_TEST_ENV", 42u32);
        }
    "#;

    let err =
        SourceProgram::parse(source).expect_err("env! should reject non-string custom messages");
    assert!(matches!(
        &err,
        SourceError::Unsupported {
            context: "macro",
            ..
        }
    ));
    assert!(
        err.to_string()
            .contains("env! expects string-literal arguments"),
        "unexpected error: {err}"
    );
}

#[test]
fn test_source_program_option_env_macro_returns_none() {
    let source = r#"
        fn main() -> bool {
            match option_env!("CLEAN_UNSET") {
                Option::None => true,
                Option::Some(_) => false,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("option_env!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_program_option_env_macro_rejects_non_string_argument() {
    let source = r#"
        fn main() {
            let _ = option_env!(42u32);
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("option_env! should reject non-string args");
    assert!(matches!(
        &err,
        SourceError::Unsupported {
            context: "macro",
            ..
        }
    ));
    assert!(
        err.to_string()
            .contains("option_env! expects a string-literal argument"),
        "unexpected error: {err}"
    );
}

#[test]
fn test_source_program_include_str_macro_returns_empty_string() {
    let source = r#"
        fn main() -> bool {
            let text = include_str!("Cargo.toml");
            text.is_empty()
        }
    "#;

    let program = SourceProgram::parse(source).expect("include_str!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_program_include_bytes_macro_returns_empty_byte_array() {
    let source = r#"
        fn main() -> bool {
            let bytes = include_bytes!("Cargo.toml");
            bytes.is_empty() && bytes.len() == 0usize
        }
    "#;

    let program = SourceProgram::parse(source).expect("include_bytes!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_program_include_str_macro_rejects_multiple_arguments() {
    let source = r#"
        fn main() {
            let _ = include_str!("a", "b");
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("include_str! should reject extra args");
    assert!(matches!(
        &err,
        SourceError::Unsupported {
            context: "macro",
            ..
        }
    ));
    assert!(
        err.to_string()
            .contains("include_str! expects exactly 1 string-literal argument"),
        "unexpected error: {err}"
    );
}

#[test]
fn test_source_program_include_bytes_macro_rejects_non_string_argument() {
    let source = r#"
        fn main() {
            let _ = include_bytes!(42u32);
        }
    "#;

    let err =
        SourceProgram::parse(source).expect_err("include_bytes! should reject non-string args");
    assert!(matches!(
        &err,
        SourceError::Unsupported {
            context: "macro",
            ..
        }
    ));
    assert!(
        err.to_string()
            .contains("include_bytes! expects a string-literal argument"),
        "unexpected error: {err}"
    );
}

#[test]
fn test_source_program_compile_error_panics() {
    let source = r#"
        fn main() -> u32 {
            compile_error!("not supported");
            0u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("compile_error! should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Panic(_)),
        "compile_error! should abort, got: {result:?}"
    );
}

#[test]
fn test_source_program_source_location_macros_return_placeholders() {
    let source = r#"
        fn main() -> bool {
            column!() == 0u32
                && line!() == 0u32
                && file!().is_empty()
                && module_path!().is_empty()
        }
    "#;

    let program = SourceProgram::parse(source).expect("source-location macros should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_program_source_location_macros_reject_arguments() {
    for (invocation, expected) in [
        ("column!(1u32)", "column! expects no arguments"),
        ("line!(1u32)", "line! expects no arguments"),
        ("file!(\"src/main.rs\")", "file! expects no arguments"),
        (
            "module_path!(\"crate::source_macro_ingestion\")",
            "module_path! expects no arguments",
        ),
    ] {
        let source = format!(
            r#"
                fn main() {{
                    let _ = {invocation};
                }}
            "#
        );

        let err = SourceProgram::parse(&source)
            .expect_err("source-location macros should reject argument lists");
        assert!(matches!(
            &err,
            SourceError::Unsupported {
                context: "macro",
                ..
            }
        ));
        assert!(
            err.to_string().contains(expected),
            "unexpected error for `{invocation}`: {err}"
        );
    }
}
