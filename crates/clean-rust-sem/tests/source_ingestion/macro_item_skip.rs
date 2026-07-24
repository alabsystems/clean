// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for silently skipping item-position macro invocations during
//! source ingestion. Covers top-level, impl-block, trait-impl, and
//! block-scoped macro invocations.

use super::{Interpreter, SourceProgram, Value};

#[test]
fn test_source_program_skips_top_level_macro_invocations() {
    let source = r#"
        custom_derive! {
            struct Foo { x: u32 }
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("top-level macro invocations should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_impl_block_macro_invocations() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            generate_methods!(Counter);

            fn get_value(&self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            let c = Counter { value: 42u32 };
            c.get_value()
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("impl-block macro invocations should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_trait_impl_macro_invocations() {
    let source = r#"
        trait Adder {
            fn add(self, x: u32) -> u32;
        }

        struct Widget {
            v: u32,
        }

        impl Adder for Widget {
            delegate_methods!();

            fn add(self, x: u32) -> u32 {
                self.v + x
            }
        }

        fn main() -> u32 {
            let w = Widget { v: 32u32 };
            w.add(10u32)
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("trait-impl macro invocations should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_trait_body_macro_invocations() {
    let source = r#"
        trait Logger {
            generate_log_methods!();

            fn log(&self) -> u32;
        }

        struct Widget {
            v: u32,
        }

        impl Logger for Widget {
            fn log(&self) -> u32 {
                self.v
            }
        }

        fn main() -> u32 {
            let w = Widget { v: 42u32 };
            w.log()
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("trait-body macro invocations should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_trait_body_macro_with_regular_items() {
    let source = r#"
        trait Ops {
            delegate!();

            fn required(&self) -> u32;

            fn default_op(&self) -> u32 {
                10u32
            }
        }

        struct Counter {
            value: u32,
        }

        impl Ops for Counter {
            fn required(&self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            let c = Counter { value: 32u32 };
            let r = c.required();
            let c2 = Counter { value: 0u32 };
            let d = c2.default_op();
            r + d
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("trait-body macros mixed with methods should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_extern_crate_declarations() {
    let source = r#"
        extern crate alloc;

        fn main() -> u32 {
            42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("extern crate declarations should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_mod_declarations() {
    let source = r#"
        mod inner {
            pub fn helper() -> u32 {
                10u32
            }
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("inline mod declarations should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_extern_blocks() {
    let source = r#"
        extern "C" {
            fn foreign_helper(x: i32) -> i32;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("extern blocks should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_trait_aliases() {
    let source = r#"
        trait ReadWrite = Clone + Send;

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait aliases should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_block_level_extern_crate() {
    let source = r#"
        fn main() -> u32 {
            extern crate alloc;
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("block-level extern crate should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_block_level_mod() {
    let source = r#"
        fn main() -> u32 {
            mod nested {
                pub fn f() -> u32 { 0u32 }
            }
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("block-level mod should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_block_level_extern_blocks() {
    let source = r#"
        fn main() -> u32 {
            extern "C" {
                fn foreign_helper(x: i32) -> i32;
            }
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("block-level extern block should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_block_level_trait_aliases() {
    let source = r#"
        fn main() -> u32 {
            trait ReadWrite = Clone + Send;
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("block-level trait alias should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_block_level_macro_invocations() {
    let source = r#"
        fn main() -> u32 {
            bitflags! {
                struct Flags: u32 {
                    const A = 0b00000001;
                }
            }
            42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("block-level macro invocations should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_multiple_top_level_macro_invocations() {
    let source = r#"
        bitflags! {
            struct Flags: u32 {
                const A = 0b00000001;
                const B = 0b00000010;
            }
        }

        lazy_static! {
            static ref GLOBAL: u32 = 42;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("multiple top-level macros should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
