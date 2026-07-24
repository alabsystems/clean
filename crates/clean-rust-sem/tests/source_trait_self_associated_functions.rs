// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

#[test]
fn test_trait_default_method_self_associated_function_path_value_uses_trait_item() {
    let source = r#"
        trait Factory {
            fn seed() -> u32;

            fn load() -> u32 {
                let seed = Self::seed;
                seed()
            }
        }

        struct Counter;

        impl Counter {
            fn seed() -> u32 {
                1u32
            }
        }

        impl Factory for Counter {
            fn seed() -> u32 {
                42u32
            }
        }

        fn main() -> u32 {
            <Counter as Factory>::load()
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("trait default Self::seed path value should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_trait_impl_method_self_associated_function_prefers_inherent_item() {
    let source = r#"
        trait Factory {
            fn seed() -> u32;
            fn load() -> u32;
        }

        struct Counter;

        impl Counter {
            fn seed() -> u32 {
                1u32
            }
        }

        impl Factory for Counter {
            fn seed() -> u32 {
                42u32
            }

            fn load() -> u32 {
                Self::seed()
            }
        }

        fn main() -> u32 {
            <Counter as Factory>::load()
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("trait impl Self::seed() should parse and prefer inherent resolution");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(1)));
}

#[test]
fn test_trait_impl_method_self_associated_function_path_value_falls_back_to_trait_item() {
    let source = r#"
        trait Factory {
            fn seed() -> u32;
            fn load() -> u32;
        }

        struct Counter;

        impl Factory for Counter {
            fn seed() -> u32 {
                42u32
            }

            fn load() -> u32 {
                let seed = Self::seed;
                seed()
            }
        }

        fn main() -> u32 {
            <Counter as Factory>::load()
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("trait impl Self::seed path value should parse and fall back to the trait item");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
