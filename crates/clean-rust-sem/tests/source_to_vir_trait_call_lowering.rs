// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for trait-qualified call lowering to VIR.

use clean_rust_sem::vir::{Constant, Term};
use clean_rust_sem::{Operand, SourceProgram};

#[test]
fn test_trait_method_call_uses_canonical_trait_function_name() {
    let source = r#"
        trait Greeter {
            fn greet(self) -> u32;
        }

        struct Counter {
            value: u32,
        }

        impl Greeter for Counter {
            fn greet(self) -> u32 {
                self.value + 1u32
            }
        }

        fn main() -> u32 {
            let counter = Counter { value: 41u32 };
            counter.greet()
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait-method source should parse");
    let lowered = program
        .lower_to_vir()
        .expect("trait method should lower to VIR");
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let has_trait_call = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                ..
            } if name == "<Counter as Greeter>::greet"
        )
    });
    assert!(
        has_trait_call,
        "trait method call should use the canonical trait-qualified callee name"
    );
    assert!(
        lowered
            .functions
            .contains_key("<Counter as Greeter>::greet"),
        "lowered program should retain the trait impl body under its canonical name: {:?}",
        lowered.functions.keys().collect::<Vec<_>>()
    );
}
