// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests verifying that the VIR lowering emits `Stmt::Retag`
//! at the correct program points for Stacked Borrows / Tree Borrows semantics.

use clean_rust_sem::{Body, Mutability, RetagKind, SourceProgram, Stmt};

fn lowered_main(source: &str) -> Body {
    let program = SourceProgram::parse(source).expect("source should parse");
    program
        .lower_to_vir()
        .expect("source should lower to VIR")
        .functions
        .get("main")
        .cloned()
        .expect("lowered program should contain `main`")
}

fn has_retag(body: &Body, kind: RetagKind) -> bool {
    body.blocks.iter().any(|bb| {
        bb.statements
            .iter()
            .any(|stmt| matches!(stmt, Stmt::Retag { kind: k, .. } if *k == kind))
    })
}

#[test]
fn test_shared_borrow_emits_default_retag() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 42u32;
            let r = &x;
            *r
        }
    "#;
    let body = lowered_main(source);
    assert!(
        has_retag(&body, RetagKind::Default),
        "shared borrow `&x` should emit Stmt::Retag with RetagKind::Default: {body:#?}"
    );
}

#[test]
fn test_mutable_borrow_emits_default_retag() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let r = &mut x;
            *r = 2u32;
            x
        }
    "#;
    let body = lowered_main(source);
    assert!(
        has_retag(&body, RetagKind::Default),
        "mutable borrow `&mut x` should emit Stmt::Retag with RetagKind::Default: {body:#?}"
    );
}

#[test]
fn test_mut_method_receiver_emits_two_phase_retag() {
    let source = r#"
        struct Acc { total: u32 }
        impl Acc {
            fn add(&mut self, n: u32) -> u32 {
                self.total = self.total + n;
                self.total
            }
        }
        fn main() -> u32 {
            let mut a = Acc { total: 0u32 };
            a.add(5u32)
        }
    "#;
    let body = lowered_main(source);
    assert!(
        has_retag(&body, RetagKind::TwoPhase),
        "method call with `&mut self` should emit Stmt::Retag with RetagKind::TwoPhase: {body:#?}"
    );
}

#[test]
fn test_fn_entry_retag_for_reference_parameter() {
    let source = r#"
        fn takes_ref(r: &u32) -> u32 {
            *r
        }
        fn main() -> u32 {
            let x: u32 = 10u32;
            takes_ref(&x)
        }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    let lowered = program.lower_to_vir().expect("source should lower to VIR");
    let takes_ref_body = lowered
        .functions
        .get("takes_ref")
        .expect("lowered program should contain `takes_ref`");
    assert!(
        has_retag(takes_ref_body, RetagKind::FnEntry),
        "function with reference parameter should emit Stmt::Retag with RetagKind::FnEntry: {takes_ref_body:#?}"
    );
}

#[test]
fn test_ref_to_raw_cast_emits_raw_retag() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 10u32;
            let r: &u32 = &x;
            let p: *const u32 = r as *const u32;
            unsafe { *p }
        }
    "#;
    let body = lowered_main(source);
    assert!(
        has_retag(&body, RetagKind::Raw(Mutability::Shared)),
        "ref-to-raw cast should emit Stmt::Retag with RetagKind::Raw(Shared): {body:#?}"
    );
}
