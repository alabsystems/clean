// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceError, SourceProgram, Value};

#[test]
fn test_source_program_runs_trait_impl_method() {
    let source = r#"
        trait Greeter {
            fn greet(self) -> u32;
        }

        struct Counter {
            value: u32,
        }

        impl Counter {
            fn get(self) -> u32 {
                self.value
            }

            fn increment(self) -> Counter {
                Counter { value: self.value + 1u32 }
            }
        }

        impl Greeter for Counter {
            fn greet(self) -> u32 {
                self.value + 10u32
            }
        }

        fn main() -> u32 {
            let c = Counter { value: 32u32 };
            c.greet()
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait impl should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_rejects_trait_impl_for_undefined_trait() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Greeter for Counter {
            fn greet(self) -> u32 {
                self.value + 10u32
            }
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let err =
        SourceProgram::parse(source).expect_err("trait impl with no trait definition should fail");

    match err {
        SourceError::Invalid { context, detail } => {
            assert_eq!(context, "impl");
            assert!(
                detail.contains("undefined trait `Greeter`"),
                "detail should mention the missing trait definition, got: {detail}"
            );
        }
        other => panic!("expected invalid error for missing trait definition, got {other:?}"),
    }
}
