// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the parsed-source borrow-checking entrypoint.

use clean_rust_sem::SourceProgram;

#[test]
fn test_source_program_check_borrows_covers_all_lowered_functions() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn get(&self) -> u32 {
                self.value
            }
        }

        fn helper(x: &u32) -> u32 {
            *x
        }

        fn main() -> u32 {
            let counter: Counter = Counter { value: 7u32 };
            let local: u32 = counter.get();
            helper(&local)
        }
    "#;

    let program = SourceProgram::parse(source).expect("source should parse");
    let analyses = program
        .check_borrows()
        .expect("source should lower and run NLL");

    assert!(
        analyses.contains_key("main"),
        "parsed-source NLL results should include `main`: {:?}",
        analyses.keys().collect::<Vec<_>>()
    );
    assert!(
        analyses.contains_key("helper"),
        "parsed-source NLL results should include top-level helpers: {:?}",
        analyses.keys().collect::<Vec<_>>()
    );
    assert!(
        analyses.contains_key("Counter::get"),
        "parsed-source NLL results should include inherent methods: {:?}",
        analyses.keys().collect::<Vec<_>>()
    );
    assert!(
        analyses.values().all(|result| result.errors.is_empty()),
        "well-formed parsed functions should stay NLL-clean: {:?}",
        analyses
            .iter()
            .map(|(name, result)| (name, &result.errors))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_source_program_check_borrows_reports_per_function_conflicts() {
    let source = r#"
        fn borrowed_then_written() -> u32 {
            let mut x: u32 = 1u32;
            let r = &x;
            x = 2u32;
            *r
        }

        fn main() -> u32 {
            borrowed_then_written()
        }
    "#;

    let program = SourceProgram::parse(source).expect("source should parse");
    let analyses = program
        .check_borrows()
        .expect("source should lower and run NLL");
    let helper = analyses
        .get("borrowed_then_written")
        .expect("per-function borrow results should include the helper body");
    let main = analyses
        .get("main")
        .expect("per-function borrow results should include `main`");

    assert!(
        helper
            .errors
            .iter()
            .any(|err| matches!(err, clean_rust_sem::NllError::AssignWhileBorrowed { .. })),
        "the conflicting helper body should surface its own NLL error: {:?}",
        helper.errors
    );
    assert!(
        main.errors.is_empty(),
        "non-borrowing caller bodies should not inherit callee conflicts: {:?}",
        main.errors
    );
}

#[test]
fn test_source_program_check_borrows_handles_trait_method_calls() {
    let source = r#"
        trait Readable {
            fn read(&self) -> u32;
        }

        struct Counter {
            value: u32,
        }

        impl Readable for Counter {
            fn read(&self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            let counter: Counter = Counter { value: 9u32 };
            counter.read()
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait-method source should parse");
    let analyses = program
        .check_borrows()
        .expect("trait-method calls should lower and run NLL");

    assert!(
        analyses.contains_key("main"),
        "parsed-source NLL results should include `main`: {:?}",
        analyses.keys().collect::<Vec<_>>()
    );
    assert!(
        analyses.contains_key("<Counter as Readable>::read"),
        "parsed-source NLL results should include trait impl bodies under their canonical name: {:?}",
        analyses.keys().collect::<Vec<_>>()
    );
    assert!(
        analyses.values().all(|result| result.errors.is_empty()),
        "trait-method lowering should stay NLL-clean: {:?}",
        analyses
            .iter()
            .map(|(name, result)| (name, &result.errors))
            .collect::<Vec<_>>()
    );
}
