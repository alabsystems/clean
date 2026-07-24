// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceProgram, Value};

#[test]
fn test_source_program_parses_tuple_struct_definition() {
    let source = r#"
        struct Pair(u32, u32);

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("tuple struct should parse");
    let items = program.items();
    assert_eq!(items.len(), 2);
}

#[test]
fn test_source_program_runs_tuple_struct_constructor_from_prescan() {
    let source = r#"
        fn main() -> u32 {
            let pair = Pair(40u32, 2u32);
            pair.0 + pair.1
        }

        struct Pair(u32, u32);
    "#;

    let program = SourceProgram::parse(source).expect("tuple struct constructor should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_top_level_type_alias_from_prescan() {
    let source = r#"
        fn main() -> u32 {
            let pair: PairAlias = Pair(40u32, 2u32);
            pair.0 + pair.1
        }

        type PairAlias = Pair;
        struct Pair(u32, u32);
    "#;

    let program = SourceProgram::parse(source).expect("type alias should parse before use");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_type_alias_enum_variant_constructor_from_prescan() {
    let source = r#"
        fn main() -> u32 {
            let value = Maybe::Some(42u32);
            match value {
                Option::Some(n) => n,
                Option::None => 0u32,
            }
        }

        type Maybe = Option<u32>;
    "#;

    let program = SourceProgram::parse(source).expect("type alias enum constructor should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_type_alias_tuple_struct_constructor_from_prescan() {
    let source = r#"
        fn main() -> u32 {
            let pair = PairAlias(40u32, 2u32);
            pair.0 + pair.1
        }

        type PairAlias = Pair;
        struct Pair(u32, u32);
    "#;

    let program =
        SourceProgram::parse(source).expect("type-alias tuple struct constructor should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_block_local_tuple_struct_from_prescan() {
    let source = r#"
        fn main() -> u32 {
            let pair = Pair(40u32, 2u32);
            struct Pair(u32, u32);
            pair.0 + pair.1
        }
    "#;

    let program = SourceProgram::parse(source).expect("block-local tuple struct should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_block_local_type_alias_from_prescan() {
    let source = r#"
        fn main() -> u32 {
            let pair: PairAlias = Pair(40u32, 2u32);
            type PairAlias = Pair;
            struct Pair(u32, u32);
            pair.0 + pair.1
        }
    "#;

    let program = SourceProgram::parse(source).expect("block-local type alias should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_block_local_enum_variant_from_prescan() {
    let source = r#"
        fn main() -> u32 {
            let value = Flag::Ready;
            enum Flag {
                Ready,
            }
            match value {
                Flag::Ready => 42u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("block-local enum should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
