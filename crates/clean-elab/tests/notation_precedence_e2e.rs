// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file_with_diagnostics;

#[test]
fn named_precedences_have_the_same_kernel_checked_values_as_lean() {
    // Both upstream 4.30.0-rc2 and 4.36.0 accept the first value in each row
    // and reject the other by reflexivity. At min=0 Clean accepted 123.
    let declarations = r#"
def pair (a b : Nat) := a * 10 + b
def marker (x : Nat) := x + 1
def twice (x : Nat) := x + x
infixl:5 " ⋇ " => pair
infixr:min " ⋈ " => pair
infixr:min1 " ⋉ " => pair
prefix:lead "⁂" => marker
"#;
    for (expr, correct, wrong) in [
        ("1 ⋇ 2 ⋈ 3", 33, 123),
        ("1 ⋈ 2 ⋉ 3", 33, 123),
        ("⁂twice 3", 7, 8),
    ] {
        for value in [correct, wrong] {
            let source = format!("{declarations}\ntheorem result : ({expr}) = {value} := rfl");
            let parsed = parse_file_with_diagnostics(&source).expect("notation parses");
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut env = Environment::with_prelude();
            let mut context = FileContext::new();
            let (proof, setup) = parsed.decls.split_last().expect("test has a theorem");
            for declaration in setup {
                let decl = preprocess_decl_with_context(declaration, &mut context);
                elaborate_decl_and_register_with_context(&mut env, &decl, &mut context)
                    .expect("definitions and notation elaborate");
            }
            let proof = preprocess_decl_with_context(proof, &mut context);
            let checked = elaborate_decl_and_register_with_context(&mut env, &proof, &mut context);
            assert_eq!(
                checked.is_ok(),
                value == correct,
                "{expr} = {value}: {checked:?}"
            );
            assert_eq!(
                env.get_const(&Name::from_string("result")).is_some(),
                value == correct
            );
        }
    }
}
