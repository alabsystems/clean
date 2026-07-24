// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for dynamic dispatch through `dyn Trait` trait objects.
//!
//! A method call `obj.method(args)` where `obj` has a `dyn Trait` type (bare or
//! behind `&`/`&mut`/`Box`/`Pin`) erases the concrete implementing type, so the
//! method signature is recovered from the trait *declaration* and the call is
//! lowered as a virtual call against a synthetic `<dyn Trait>::method` callee
//! with no registered body. This is a sound over-approximation: the borrow/move
//! analysis treats the dispatch as consuming the trait-object receiver and each
//! argument, and havocing the destination, so no stale value survives. It is
//! intentionally incomplete (the concrete impl body is never inlined) but never
//! unsound.

use clean_rust_sem::nll::NllError;
use clean_rust_sem::vir::{Constant, Operand, Term};
use clean_rust_sem::SourceProgram;

/// `&dyn Trait` method dispatch lowers to a virtual call and is NLL-clean.
#[test]
fn test_ref_dyn_trait_method_call_lowers_to_virtual_call() {
    let source = r#"
        trait Greeter {
            fn greet(&self) -> u32;
        }
        struct Counter { value: u32 }
        impl Greeter for Counter {
            fn greet(&self) -> u32 { self.value + 1u32 }
        }
        fn run(g: &dyn Greeter) -> u32 {
            g.greet()
        }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    let lowered = program
        .lower_to_vir()
        .expect("calling a method on `&dyn Trait` should lower to VIR");
    let body = lowered
        .functions
        .get("run")
        .expect("lowered program should contain `run`");

    let has_virtual_call = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                ..
            } if name == "<dyn Greeter>::greet"
        )
    });
    assert!(
        has_virtual_call,
        "dynamic dispatch should emit a virtual `<dyn Greeter>::greet` callee; got: {:?}",
        body.blocks
            .iter()
            .map(|bb| &bb.terminator)
            .collect::<Vec<_>>()
    );

    let analyses = lowered.check_borrows();
    assert!(
        analyses
            .get("run")
            .expect("borrow analyses should include `run`")
            .errors
            .is_empty(),
        "a `&dyn Trait` method dispatch should stay NLL-clean"
    );
}

/// `Box<dyn Trait>` method dispatch lowers (the trait object is reached through
/// the `Box` wrapper).
#[test]
fn test_box_dyn_trait_method_call_lowers() {
    let source = r#"
        trait Greeter {
            fn greet(&self) -> u32;
        }
        struct Counter { value: u32 }
        impl Greeter for Counter {
            fn greet(&self) -> u32 { self.value + 1u32 }
        }
        fn run(g: Box<dyn Greeter>) -> u32 {
            g.greet()
        }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    program
        .lower_to_vir()
        .expect("calling a method on `Box<dyn Trait>` should lower to VIR");
}

/// A dynamic dispatch that takes the trait object argument propagates the move:
/// the explicit argument is materialized at the trait method's declared
/// parameter type.
#[test]
fn test_dyn_trait_method_call_with_args_lowers() {
    let source = r#"
        trait Adder {
            fn add(&self, n: u32) -> u32;
        }
        struct Base { base: u32 }
        impl Adder for Base {
            fn add(&self, n: u32) -> u32 { self.base + n }
        }
        fn run(a: &dyn Adder) -> u32 {
            a.add(7u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    let lowered = program
        .lower_to_vir()
        .expect("dynamic dispatch with arguments should lower to VIR");
    let body = lowered.functions.get("run").expect("run lowered");
    let has_two_arg_call = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                args,
                ..
            } if name == "<dyn Adder>::add" && args.len() == 2
        )
    });
    assert!(
        has_two_arg_call,
        "dynamic dispatch should pass the receiver plus one explicit argument"
    );
}

/// SOUNDNESS: a by-value (`self`) dynamic dispatch *moves* the trait object.
/// Holding a live borrow across that dispatch must be flagged as
/// `MoveWhileBorrowed`, proving the lowering soundly invalidates the receiver
/// (it never under-approximates relative to a non-`dyn` by-value method call).
#[test]
fn test_dyn_by_value_dispatch_while_borrowed_is_flagged() {
    let source = r#"
        trait Consume { fn eat(self) -> u32; }
        struct C { v: u32 }
        impl Consume for C { fn eat(self) -> u32 { self.v } }
        fn observe(g: &Box<dyn Consume>) -> u32 { 0u32 }
        fn run(b: Box<dyn Consume>) -> u32 {
            let r = &b;
            let x = b.eat();
            observe(r) + x
        }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    let lowered = program
        .lower_to_vir()
        .expect("by-value dynamic dispatch should lower to VIR");
    let analyses = lowered.check_borrows();
    let errors = &analyses.get("run").expect("run analysis").errors;
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, NllError::MoveWhileBorrowed { .. })),
        "moving a trait object via by-value dispatch while borrowed must be flagged; got: {errors:?}"
    );
}

/// A by-value (`self`) dynamic dispatch with no outstanding borrow lowers and
/// is NLL-clean (the single move of the trait object is unobjectionable).
#[test]
fn test_dyn_by_value_dispatch_clean() {
    let source = r#"
        trait Consume { fn eat(self) -> u32; }
        struct C { v: u32 }
        impl Consume for C { fn eat(self) -> u32 { self.v } }
        fn run(b: Box<dyn Consume>) -> u32 {
            b.eat()
        }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    let lowered = program
        .lower_to_vir()
        .expect("by-value dynamic dispatch should lower to VIR");
    let analyses = lowered.check_borrows();
    assert!(
        analyses.get("run").expect("run analysis").errors.is_empty(),
        "a single by-value dynamic dispatch should be NLL-clean"
    );
}
