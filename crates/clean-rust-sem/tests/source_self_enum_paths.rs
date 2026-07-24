// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

#[test]
fn test_self_unit_enum_variant_path_runs_in_inherent_impl() {
    let source = r#"
        enum Flag {
            Ready,
            Busy,
        }

        impl Flag {
            fn ready() -> Self {
                Self::Ready
            }

            fn code(flag: Self) -> u32 {
                match flag {
                    Self::Ready => 42u32,
                    Self::Busy => 0u32,
                }
            }
        }

        fn main() -> u32 {
            Flag::code(Flag::ready())
        }
    "#;

    let program = SourceProgram::parse(source).expect("inherent Self::Variant should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_self_tuple_enum_variant_constructor_runs_in_inherent_impl() {
    let source = r#"
        enum Packet {
            Pair(u32, u32),
        }

        impl Packet {
            fn pair() -> Self {
                Self::Pair(40u32, 2u32)
            }

            fn total(value: Self) -> u32 {
                match value {
                    Self::Pair(left, right) => left + right,
                }
            }
        }

        fn main() -> u32 {
            Packet::total(Packet::pair())
        }
    "#;

    let program = SourceProgram::parse(source).expect("inherent Self::TupleVariant should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_self_struct_enum_variant_constructor_runs_in_inherent_impl() {
    let source = r#"
        enum Packet {
            Pair { left: u32, right: u32 },
        }

        impl Packet {
            fn pair() -> Self {
                Self::Pair {
                    left: 40u32,
                    right: 2u32,
                }
            }

            fn total(value: Self) -> u32 {
                match value {
                    Self::Pair { left, right } => left + right,
                }
            }
        }

        fn main() -> u32 {
            Packet::total(Packet::pair())
        }
    "#;

    let program = SourceProgram::parse(source).expect("inherent Self::StructVariant should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_self_tuple_enum_variant_constructor_path_value_runs_in_inherent_impl() {
    let source = r#"
        enum Packet {
            Pair(u32, u32),
        }

        impl Packet {
            fn pair() -> Self {
                let ctor = Self::Pair;
                ctor(40u32, 2u32)
            }

            fn total(value: Self) -> u32 {
                match value {
                    Self::Pair(left, right) => left + right,
                }
            }
        }

        fn main() -> u32 {
            Packet::total(Packet::pair())
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("inherent Self::TupleVariant path value should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}
