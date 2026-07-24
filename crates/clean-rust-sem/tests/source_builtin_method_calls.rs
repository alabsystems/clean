// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for built-in method-call ingestion.
//!
//! These exercise source-level method syntax on runtime values that are already
//! modeled by the interpreter, without requiring user-defined impl blocks.

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::values::EnumPayload;
use clean_rust_sem::{SourceProgram, Value};

#[path = "source_builtin_method_calls/option_basics.rs"]
mod option_basics;
#[path = "source_builtin_method_calls/option_fallbacks.rs"]
mod option_fallbacks;
#[path = "source_builtin_method_calls/option_result_borrowed_views.rs"]
mod option_result_borrowed_views;
#[path = "source_builtin_method_calls/option_result_flatten.rs"]
mod option_result_flatten;
#[path = "source_builtin_method_calls/option_result_map_or.rs"]
mod option_result_map_or;
#[path = "source_builtin_method_calls/option_result_zero_arg_arity.rs"]
mod option_result_zero_arg_arity;
#[path = "source_builtin_method_calls/result_basics.rs"]
mod result_basics;
#[path = "source_builtin_method_calls/result_fallbacks.rs"]
mod result_fallbacks;

#[test]
fn test_vec_len_parses_and_runs() {
    let source = r#"
        fn main() -> usize {
            let v = Vec::with_capacity(8u32);
            v.len()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec::len() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::usize(0)));
}

#[test]
fn test_vec_new_len_chain_parses_and_runs() {
    let source = r#"
        fn main() -> usize {
            Vec::new().len()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec::new().len() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::usize(0)));
}

#[test]
fn test_array_len_parses_and_runs() {
    let source = r#"
        fn main() -> usize {
            let values = [10u32, 20u32, 30u32];
            values.len()
        }
    "#;
    let program = SourceProgram::parse(source).expect("[..].len() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::usize(3)));
}

#[test]
fn test_string_len_parses_and_runs() {
    let source = r#"
        fn main() -> usize {
            let s = String::from("rust");
            s.len()
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::len() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::usize(4)));
}

#[test]
fn test_vec_is_empty_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            Vec::with_capacity(8u32).is_empty()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec::is_empty() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_array_is_empty_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let values = [10u32, 20u32, 30u32];
            values.is_empty()
        }
    "#;
    let program = SourceProgram::parse(source).expect("[..].is_empty() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(false)));
}

#[test]
fn test_string_is_empty_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            String::new().is_empty()
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::is_empty() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_str_literal_len_parses_and_runs() {
    let source = r#"
        fn main() -> usize {
            "hello".len()
        }
    "#;
    let program = SourceProgram::parse(source).expect("string literal len() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::usize(5)));
}

#[test]
fn test_str_literal_is_empty_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            "".is_empty()
        }
    "#;
    let program = SourceProgram::parse(source).expect("string literal is_empty() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_vec_contains_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let v = Vec::with_capacity(0u32);
            v.contains(42u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec::contains() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(false)));
}

#[test]
fn test_array_contains_found_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let values = [10u32, 20u32, 30u32];
            values.contains(20u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("[..].contains() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_array_contains_not_found_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let values = [10u32, 20u32, 30u32];
            values.contains(99u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("[..].contains(missing) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(false)));
}

#[test]
fn test_string_contains_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let s = String::from("hello world");
            s.contains("world")
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::contains() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_string_contains_not_found_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let s = String::from("hello world");
            s.contains("xyz")
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::contains(missing) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(false)));
}

#[test]
fn test_str_literal_contains_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            "hello".contains("ell")
        }
    "#;
    let program = SourceProgram::parse(source).expect("str literal contains() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_builtin_contains_rejects_no_arguments() {
    let source = r#"
        fn main() -> bool {
            let s = String::from("hi");
            s.contains()
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::contains() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `contains` takes 1 arg, got 0")
    );
}

#[test]
fn test_builtin_is_empty_rejects_arguments() {
    let source = r#"
        fn main() -> bool {
            let s = String::from("hi");
            s.is_empty(1u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::is_empty(args) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `is_empty` takes 0 args, got 1")
    );
}

#[test]
fn test_builtin_len_rejects_arguments() {
    let source = r#"
        fn main() -> usize {
            let s = String::from("hi");
            s.len(1u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::len(args) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `len` takes 0 args, got 1")
    );
}

#[test]
fn test_array_len_rejects_arguments() {
    let source = r#"
        fn main() -> usize {
            let values = [1u32, 2u32];
            values.len(1u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("[..].len(args) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `len` takes 0 args, got 1")
    );
}

#[test]
fn test_array_is_empty_rejects_arguments() {
    let source = r#"
        fn main() -> bool {
            let values = [1u32, 2u32];
            values.is_empty(1u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("[..].is_empty(args) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `is_empty` takes 0 args, got 1")
    );
}

#[test]
fn test_str_literal_is_empty_non_empty_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            "hello".is_empty()
        }
    "#;
    let program =
        SourceProgram::parse(source).expect("non-empty str literal is_empty() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(false)));
}

// --- starts_with ---

#[test]
fn test_string_starts_with_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let s = String::from("hello world");
            s.starts_with("hello")
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::starts_with() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_string_starts_with_no_match_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let s = String::from("hello world");
            s.starts_with("world")
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::starts_with(miss) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(false)));
}

#[test]
fn test_str_literal_starts_with_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            "hello".starts_with("he")
        }
    "#;
    let program = SourceProgram::parse(source).expect("str literal starts_with() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

// --- ends_with ---

#[test]
fn test_string_ends_with_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let s = String::from("hello world");
            s.ends_with("world")
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::ends_with() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_string_ends_with_no_match_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let s = String::from("hello world");
            s.ends_with("hello")
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::ends_with(miss) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(false)));
}

#[test]
fn test_str_literal_ends_with_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            "hello".ends_with("lo")
        }
    "#;
    let program = SourceProgram::parse(source).expect("str literal ends_with() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_builtin_starts_with_rejects_no_arguments() {
    let source = r#"
        fn main() -> bool {
            let s = String::from("hi");
            s.starts_with()
        }
    "#;
    let program = SourceProgram::parse(source).expect("starts_with() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `starts_with` takes 1 arg, got 0")
    );
}

#[test]
fn test_builtin_ends_with_rejects_no_arguments() {
    let source = r#"
        fn main() -> bool {
            let s = String::from("hi");
            s.ends_with()
        }
    "#;
    let program = SourceProgram::parse(source).expect("ends_with() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `ends_with` takes 1 arg, got 0")
    );
}

// --- first / last ---

#[test]
fn test_array_first_parses_and_runs() {
    let source = r#"
        fn main() -> u32 {
            let values = [10u32, 20u32, 30u32];
            values.first()
        }
    "#;
    let program = SourceProgram::parse(source).expect("[..].first() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Box::new(EnumPayload::Tuple(vec![Value::u32(10)])),
        })
    );
}

#[test]
fn test_array_last_parses_and_runs() {
    let source = r#"
        fn main() -> u32 {
            let values = [10u32, 20u32, 30u32];
            values.last()
        }
    "#;
    let program = SourceProgram::parse(source).expect("[..].last() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Box::new(EnumPayload::Tuple(vec![Value::u32(30)])),
        })
    );
}

#[test]
fn test_vec_first_empty_parses_and_runs() {
    let source = r#"
        fn main() -> u32 {
            let v = Vec::new();
            v.first()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec::first() empty should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            payload: Box::new(EnumPayload::Unit),
        })
    );
}

#[test]
fn test_vec_last_empty_parses_and_runs() {
    let source = r#"
        fn main() -> u32 {
            let v = Vec::new();
            v.last()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec::last() empty should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            payload: Box::new(EnumPayload::Unit),
        })
    );
}

#[test]
fn test_builtin_first_rejects_arguments() {
    let source = r#"
        fn main() -> u32 {
            let values = [1u32, 2u32];
            values.first(0u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("[..].first(args) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `first` takes 0 args, got 1")
    );
}

#[test]
fn test_builtin_last_rejects_arguments() {
    let source = r#"
        fn main() -> u32 {
            let values = [1u32, 2u32];
            values.last(0u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("[..].last(args) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `last` takes 0 args, got 1")
    );
}

// --- push_str / push / pop ---

#[test]
fn test_string_push_str_parses_and_runs() {
    let source = r#"
        fn main() -> String {
            let mut s = String::from("ru");
            s.push_str("st");
            s
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::push_str() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Str("rust".to_string())));
}

#[test]
fn test_string_push_char_parses_and_runs() {
    let source = r#"
        fn main() -> String {
            let mut s = String::from("ru");
            s.push('s');
            s.push('t');
            s
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::push(char) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Str("rust".to_string())));
}

#[test]
fn test_string_pop_parses_and_runs() {
    let source = r#"
        fn main() -> (Option<char>, String) {
            let mut s = String::from("rust");
            let last = s.pop();
            (last, s)
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::pop() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![
            Value::Enum {
                name: "Option".to_string(),
                variant: "Some".to_string(),
                payload: Box::new(EnumPayload::Tuple(vec![Value::Char('t')])),
            },
            Value::Str("rus".to_string()),
        ]))
    );
}

#[test]
fn test_string_pop_empty_parses_and_runs() {
    let source = r#"
        fn main() -> (Option<char>, String) {
            let mut s = String::new();
            let last = s.pop();
            (last, s)
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::pop() empty should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(
        result.value(),
        Some(Value::Tuple(vec![
            Value::Enum {
                name: "Option".to_string(),
                variant: "None".to_string(),
                payload: Box::new(EnumPayload::Unit),
            },
            Value::Str(String::new()),
        ]))
    );
}

#[test]
fn test_builtin_push_str_rejects_no_arguments() {
    let source = r#"
        fn main() {
            let mut s = String::from("hi");
            s.push_str();
        }
    "#;
    let program = SourceProgram::parse(source).expect("push_str() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `push_str` takes 1 arg, got 0")
    );
}

#[test]
fn test_builtin_push_rejects_non_char_argument() {
    let source = r#"
        fn main() {
            let mut s = String::from("hi");
            s.push("!");
        }
    "#;
    let program = SourceProgram::parse(source).expect("push(non-char) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "str::push expects a char argument")
    );
}

#[test]
fn test_builtin_pop_rejects_arguments() {
    let source = r#"
        fn main() {
            let mut s = String::from("hi");
            s.pop('!');
        }
    "#;
    let program = SourceProgram::parse(source).expect("pop(args) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `pop` takes 0 args, got 1")
    );
}

// --- Vec::push / Vec::pop ---

#[test]
fn test_vec_push_parses_and_runs() {
    let source = r#"
        fn main() -> usize {
            let mut v = Vec::new();
            v.push(10u32);
            v.push(20u32);
            v.push(30u32);
            v.len()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec::push() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::usize(3)));
}

#[test]
fn test_vec_push_preserves_element_values() {
    let source = r#"
        fn main() -> u32 {
            let mut v = Vec::new();
            v.push(42u32);
            v[0]
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec::push + index should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_vec_pop_returns_last_element() {
    let source = r#"
        fn main() -> u32 {
            let mut v = Vec::new();
            v.push(10u32);
            v.push(20u32);
            v.pop().unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec::pop().unwrap() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(20)));
}

#[test]
fn test_vec_pop_empty_returns_none() {
    let source = r#"
        fn main() -> bool {
            let mut v: Vec<u32> = Vec::new();
            v.pop().is_none()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec::pop().is_none() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_vec_push_pop_round_trip() {
    let source = r#"
        fn main() -> usize {
            let mut v = Vec::new();
            v.push(1u32);
            v.push(2u32);
            v.push(3u32);
            v.pop();
            v.pop();
            v.len()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec push/pop round trip should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::usize(1)));
}
