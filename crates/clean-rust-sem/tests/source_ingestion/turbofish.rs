// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceError, SourceProgram, Value};
use clean_rust_sem::expr::{Expr, Item};
use clean_rust_sem::{RustType, UintType};

fn main_final_expr(program: &SourceProgram) -> &Expr {
    let main_item = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::Fn { name, .. } if name == "main"))
        .expect("expected main function");
    let Item::Fn { body, .. } = main_item else {
        unreachable!("main lookup is restricted to Item::Fn");
    };
    let Expr::Block { expr, .. } = body else {
        panic!("expected main body block, got {body:?}");
    };
    expr.as_deref().expect("expected main final expression")
}

#[test]
fn test_source_program_runs_generic_function_call_with_turbofish() {
    let source = r#"
        fn identity<T>(x: T) -> T {
            x
        }

        fn main() -> u32 {
            identity::<u32>(42u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("generic function turbofish should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_records_function_call_turbofish_type_args() {
    let source = r#"
        fn identity<T>(x: T) -> T {
            x
        }

        fn main() -> u32 {
            identity::<u32>(42u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("generic function turbofish should parse");
    let expr = main_final_expr(&program);
    let Expr::Call { type_args, .. } = expr else {
        panic!("expected function call expression, got {expr:?}");
    };

    assert_eq!(type_args, &vec![RustType::Uint(UintType::U32)]);
}

#[test]
fn test_source_program_runs_generic_associated_function_call_with_turbofish() {
    let source = r#"
        struct Wrapper<T> {
            inner: T,
        }

        impl<T> Wrapper<T> {
            fn wrap<U>(value: U) -> U {
                value
            }
        }

        fn main() -> u32 {
            Wrapper::<u32>::wrap::<u32>(42u32)
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("generic associated function turbofish should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_records_associated_function_turbofish_type_args() {
    let source = r#"
        struct Wrapper<T> {
            inner: T,
        }

        impl<T> Wrapper<T> {
            fn wrap<U>(value: U) -> U {
                value
            }
        }

        fn main() -> bool {
            Wrapper::<u32>::wrap::<bool>(true)
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("generic associated function turbofish should parse");
    let expr = main_final_expr(&program);
    let Expr::Call { type_args, .. } = expr else {
        panic!("expected associated function call expression, got {expr:?}");
    };

    assert_eq!(type_args, &vec![RustType::Bool]);
}

#[test]
fn test_source_program_runs_generic_method_call_with_turbofish() {
    let source = r#"
        struct Wrapper {
            seed: u32,
        }

        impl Wrapper {
            fn keep<T>(&self, value: T) -> T {
                value
            }
        }

        fn main() -> u32 {
            let wrapper = Wrapper { seed: 0u32 };
            wrapper.keep::<u32>(42u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("generic method turbofish should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_records_method_turbofish_type_args() {
    let source = r#"
        struct Wrapper {
            seed: u32,
        }

        impl Wrapper {
            fn keep<T>(&self, value: T) -> T {
                value
            }
        }

        fn main() -> u32 {
            let wrapper = Wrapper { seed: 0u32 };
            wrapper.keep::<u32>(42u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("generic method turbofish should parse");
    let expr = main_final_expr(&program);
    let Expr::MethodCall { type_args, .. } = expr else {
        panic!("expected method call expression, got {expr:?}");
    };

    assert_eq!(type_args, &vec![RustType::Uint(UintType::U32)]);
}

#[test]
fn test_source_program_rejects_const_generic_argument_in_turbofish_call() {
    let source = r#"
        fn identity<T>(x: T) -> T {
            x
        }

        fn main() -> u32 {
            identity::<3>(42u32)
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("const generic turbofish should fail closed");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "call expression");
            assert!(
                detail.contains("const generic arguments"),
                "detail should mention const generic arguments, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

#[test]
fn test_source_program_records_named_struct_turbofish_type_args() {
    let source = r#"
        struct Wrapper<T> {
            value: T,
        }

        fn main() -> Wrapper<u32> {
            Wrapper::<u32> { value: 42u32 }
        }
    "#;

    let program = SourceProgram::parse(source).expect("generic struct turbofish should parse");
    let expr = main_final_expr(&program);
    let Expr::Struct { type_args, .. } = expr else {
        panic!("expected struct expression, got {expr:?}");
    };
    assert_eq!(type_args, &vec![RustType::Uint(UintType::U32)]);

    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert!(matches!(
        result.value(),
        Some(Value::Struct { name, .. }) if name == "Wrapper"
    ));
}

#[test]
fn test_source_program_records_tuple_struct_turbofish_type_args() {
    let source = r#"
        struct Wrapper<T>(T);

        fn main() -> Wrapper<u32> {
            Wrapper::<u32>(42u32)
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("generic tuple struct turbofish should parse");
    let expr = main_final_expr(&program);
    let Expr::Struct { type_args, .. } = expr else {
        panic!("expected tuple struct constructor expression, got {expr:?}");
    };
    assert_eq!(type_args, &vec![RustType::Uint(UintType::U32)]);

    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert!(matches!(
        result.value(),
        Some(Value::Struct { name, .. }) if name == "Wrapper"
    ));
}

#[test]
fn test_source_program_records_tuple_enum_variant_turbofish_type_args() {
    let source = r#"
        enum MyOption<T> {
            Some(T),
            None,
        }

        fn main() -> MyOption<u32> {
            MyOption::<u32>::Some(42u32)
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("generic tuple enum variant turbofish should parse");
    let expr = main_final_expr(&program);
    let Expr::EnumVariant { type_args, .. } = expr else {
        panic!("expected enum variant expression, got {expr:?}");
    };
    assert_eq!(type_args, &vec![RustType::Uint(UintType::U32)]);

    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert!(matches!(
        result.value(),
        Some(Value::Enum { name, variant, .. }) if name == "MyOption" && variant == "Some"
    ));
}

#[test]
fn test_source_program_records_struct_enum_variant_turbofish_type_args() {
    let source = r#"
        enum Message<T> {
            Value { inner: T },
        }

        fn main() -> Message<u32> {
            Message::<u32>::Value { inner: 42u32 }
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("generic struct enum variant turbofish should parse");
    let expr = main_final_expr(&program);
    let Expr::EnumVariant { type_args, .. } = expr else {
        panic!("expected enum variant expression, got {expr:?}");
    };
    assert_eq!(type_args, &vec![RustType::Uint(UintType::U32)]);

    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert!(matches!(
        result.value(),
        Some(Value::Enum { name, variant, .. }) if name == "Message" && variant == "Value"
    ));
}

#[test]
fn test_source_program_records_unit_enum_variant_turbofish_type_args() {
    let source = r#"
        enum MyOption<T> {
            None,
        }

        fn main() -> MyOption<u32> {
            MyOption::<u32>::None
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("generic unit enum variant turbofish should parse");
    let expr = main_final_expr(&program);
    let Expr::EnumVariant { type_args, .. } = expr else {
        panic!("expected enum variant expression, got {expr:?}");
    };
    assert_eq!(type_args, &vec![RustType::Uint(UintType::U32)]);

    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert!(matches!(
        result.value(),
        Some(Value::Enum { name, variant, .. }) if name == "MyOption" && variant == "None"
    ));
}

#[test]
fn test_source_program_rejects_unit_enum_variant_type_arg_arity_mismatch() {
    let source = r#"
        enum MyOption<T> {
            None,
        }

        fn main() -> MyOption<u32> {
            MyOption::<u32, bool>::None
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("unit enum variant arity mismatch should still parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert!(
        matches!(&result, clean_rust_sem::expr::EvalResult::Error(msg) if msg.contains("MyOption") && msg.contains("type args")),
        "expected enum type arg mismatch error, got {result:?}"
    );
}
