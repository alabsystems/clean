// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, NamedTempFile, SourceProgram, Value};

#[test]
fn test_source_program_parse_and_run_main_with_inherent_method() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn get(self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            let counter = Counter { value: 41u32 };
            counter.get() + 1u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("source should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_from_file_runs_main() {
    let source = r#"
        struct Point {
            x: u32,
            y: u32,
        }

        fn main() -> u32 {
            let point = Point { x: 40u32, y: 2u32 };
            point.x + point.y
        }
    "#;

    let file = NamedTempFile::new().expect("temp file");
    std::fs::write(file.path(), source).expect("write source");

    let program = SourceProgram::from_file(file.path()).expect("file source should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_variable_assignment() {
    let source = r#"
        fn main() -> u32 {
            let mut value: u32 = 1u32;
            value = 2u32;
            value
        }
    "#;

    let program = SourceProgram::parse(source).expect("assignment should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(2)));
}

#[test]
fn test_source_program_runs_non_capturing_closure() {
    let source = r#"
        fn main() -> u32 {
            let f = |x: u32| -> u32 { x + 1u32 };
            f(41u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("closure source should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_capturing_closure() {
    let source = r#"
        fn main() -> u32 {
            let offset: u32 = 1u32;
            let f = |x: u32| -> u32 { x + offset };
            f(41u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("capturing closure should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_untyped_closure_param() {
    let source = r#"
        fn main() -> u32 {
            let f = |x: u32| -> u32 { x };
            f(42u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("identity closure should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_inferred_closure_param() {
    // Closure with inferred (untyped) parameter — the most common pattern in real Rust
    let source = r#"
        fn main() -> u32 {
            let f = |x| -> u32 { x };
            f(42u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("inferred param closure should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_multi_inferred_closure_params() {
    // Multiple untyped parameters
    let source = r#"
        fn main() -> u32 {
            let add = |a, b: u32| -> u32 { a + b };
            add(10u32, 32u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("mixed param closure should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_inferred_closure_with_capture() {
    // Untyped param + captured variable
    let source = r#"
        fn main() -> u32 {
            let base: u32 = 40u32;
            let add_base = |x| -> u32 { x + base };
            add_base(2u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("inferred capture closure should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_move_closure_captures_by_value() {
    // `move` closure captures `base` by value
    let source = r#"
        fn main() -> u32 {
            let base: u32 = 40u32;
            let add_base = move |x: u32| -> u32 { x + base };
            add_base(2u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("move closure should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_move_closure_no_captures() {
    // `move` closure with no captures behaves identically to non-move
    let source = r#"
        fn main() -> u32 {
            let f = move |x: u32| -> u32 { x + 1u32 };
            f(41u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("move closure without captures should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_move_closure_capture_by_value_flag() {
    // Verify the AST records `capture_by_value: true` for move closures
    use clean_rust_sem::expr::{Expr, Item, Stmt};

    let source = r#"
        fn main() -> u32 {
            let x: u32 = 1u32;
            let f = move || -> u32 { x };
            f()
        }
    "#;

    let program = SourceProgram::parse(source).expect("move closure should parse");
    let items = program.items();
    // The first item is `fn main()` — dig into its body to find the closure
    let Item::Fn { body, .. } = &items[0] else {
        panic!("expected fn item");
    };
    let Expr::Block { stmts, .. } = body else {
        panic!("expected block");
    };
    // stmt[1] is `let f = move || -> u32 { x };`
    let Stmt::Let {
        init: Some(init), ..
    } = &stmts[1]
    else {
        panic!("expected let with init");
    };
    let Expr::Closure {
        capture_by_value, ..
    } = init.as_ref()
    else {
        panic!("expected closure expr");
    };
    assert!(
        *capture_by_value,
        "move closure should have capture_by_value: true"
    );
}

#[test]
fn test_source_program_non_move_closure_capture_by_value_flag() {
    // Verify the AST records `capture_by_value: false` for non-move closures
    use clean_rust_sem::expr::{Expr, Item, Stmt};

    let source = r#"
        fn main() -> u32 {
            let x: u32 = 1u32;
            let f = || -> u32 { x };
            f()
        }
    "#;

    let program = SourceProgram::parse(source).expect("non-move closure should parse");
    let items = program.items();
    let Item::Fn { body, .. } = &items[0] else {
        panic!("expected fn item");
    };
    let Expr::Block { stmts, .. } = body else {
        panic!("expected block");
    };
    let Stmt::Let {
        init: Some(init), ..
    } = &stmts[1]
    else {
        panic!("expected let with init");
    };
    let Expr::Closure {
        capture_by_value, ..
    } = init.as_ref()
    else {
        panic!("expected closure expr");
    };
    assert!(
        !*capture_by_value,
        "non-move closure should have capture_by_value: false"
    );
}

#[test]
fn test_source_program_move_closure_with_block_local_stays_fn() {
    use clean_rust_sem::expr::{Expr, Item, Stmt};
    use clean_rust_sem::types::ClosureKind;

    let source = r#"
        fn main() -> u32 {
            let f = move || -> u32 {
                let block_local: u32 = 41u32;
                block_local + 1u32
            };
            f()
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("move closure with block-local binding should parse");
    let items = program.items();
    let Item::Fn { body, .. } = &items[0] else {
        panic!("expected fn item");
    };
    let Expr::Block { stmts, .. } = body else {
        panic!("expected block");
    };
    let Stmt::Let {
        init: Some(init), ..
    } = &stmts[0]
    else {
        panic!("expected let with init");
    };

    let mut interpreter = Interpreter::new();
    let result = interpreter.eval(init.as_ref());
    match result.value() {
        Some(Value::Closure { kind, captures, .. }) => {
            assert_eq!(kind, ClosureKind::Fn);
            assert!(captures.is_empty());
        }
        other => panic!("expected closure value, got {:?}", other),
    }
}

#[test]
fn test_source_program_parses_string_literal() {
    let source = r#"
        fn main() -> &str {
            "hello world"
        }
    "#;

    let program = SourceProgram::parse(source).expect("string literal should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::Str("hello world".to_string())));
}

#[test]
fn test_source_program_parses_byte_literal() {
    let source = r#"
        fn main() -> u8 {
            b'A'
        }
    "#;

    let program = SourceProgram::parse(source).expect("byte literal should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u8(b'A')));
}

#[test]
fn test_source_program_parses_byte_string_literal() {
    let source = r#"
        fn main() -> u8 {
            let bytes = b"hi";
            bytes[1usize]
        }
    "#;

    let program = SourceProgram::parse(source).expect("byte string literal should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u8(b'i')));
}

#[test]
fn test_source_program_use_declarations_are_silently_skipped() {
    let source = r#"
        use std::collections::HashMap;
        use std::io::{self, Write};
        use std::path::PathBuf;

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("use declarations should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_use_registers_imported_type_as_nominal() {
    // After `use foo::bar::MyStruct;`, the parser should recognize `MyStruct`
    // as a nominal type (uppercase leaf names get registered).
    let source = r#"
        use std::collections::BTreeSet;

        struct Wrapper {
            value: u32,
        }

        impl Wrapper {
            fn get(self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            let w = Wrapper { value: 99u32 };
            w.get()
        }
    "#;

    let program = SourceProgram::parse(source).expect("program with use declarations should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(99)));
}

#[test]
fn test_source_program_use_group_and_rename_parse() {
    let source = r#"
        use std::collections::{HashMap, BTreeMap};
        use std::path::Path as StdPath;

        fn main() -> u32 {
            7u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("grouped/renamed use should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_source_program_runs_infer_type_annotation() {
    // `let x: _ = val;` uses `Type::Infer` — extremely common in real Rust
    let source = r#"
        fn main() -> u32 {
            let x: _ = 42u32;
            x
        }
    "#;

    let program = SourceProgram::parse(source).expect("infer type annotation should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_use_glob_silently_skipped() {
    let source = r#"
        use std::collections::*;

        fn main() -> u32 {
            55u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("glob use should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(55)));
}
