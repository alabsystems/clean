// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Unsupported computational block syntax must not vanish before interpretation
//! or proof-obligation generation. This does not implement macro expansion.
use clean_rust_sem::{eval::Interpreter, values::Value, SourceProgram};

#[test]
fn unsupported_statement_macro_cannot_erase_a_source_effect() {
    let source = r#"macro_rules! early_exit { () => { return 99u64; }; }
        fn main()->u64 { early_exit!(); 7u64 }"#;
    let error =
        SourceProgram::parse(source).expect_err("unexpanded computational statement must refuse");
    assert!(
        error
            .to_string()
            .contains("unsupported macro `early_exit!`"),
        "{error}"
    );
}

#[test]
fn unsupported_block_item_invocation_and_module_cannot_disappear() {
    for source in [
        "fn main()->u64 { generated_items! { fn hidden()->u64 { 9 } } 7u64 }",
        "fn main()->u64 { mod hidden { pub fn compute()->u64 { 9 } } 7u64 }",
    ] {
        SourceProgram::parse(source)
            .expect_err("unsupported computational item requires a named refusal");
    }
}

#[test]
fn supported_assertions_retain_their_effects() {
    let passing = SourceProgram::parse("fn main()->u64 { assert!(true); 7u64 }").unwrap();
    assert_eq!(
        passing.run(&mut Interpreter::new()).value(),
        Some(Value::u64(7))
    );
    let failing = SourceProgram::parse("fn main()->u64 { assert!(false); 7u64 }").unwrap();
    assert!(matches!(
        failing.run(&mut Interpreter::new()),
        clean_rust_sem::expr::EvalResult::Panic(_)
    ));
}

#[test]
fn explicit_noncomputational_macro_definition_and_supported_type_alias_stay_accepted() {
    let source = r#"fn main()->u64 { macro_rules! unused { () => { 99u64 }; }
        type Word=u64; let value:Word=7u64; value }"#;
    let program = SourceProgram::parse(source)
        .expect("declarations with no expansion preserve the existing supported path");
    assert_eq!(
        program.run(&mut Interpreter::new()).value(),
        Some(Value::u64(7))
    );
}
