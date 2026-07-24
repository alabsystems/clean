// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for return-site cleanup: Drop + StorageDead emission before Term::Return.

use clean_rust_sem::vir::Term;
use clean_rust_sem::{Body, Place, RustType, SourceProgram, Stmt};

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

fn local_id(body: &Body, name: &str) -> u32 {
    body.locals
        .iter()
        .enumerate()
        .find_map(|(idx, decl)| (decl.name.as_deref() == Some(name)).then_some(idx as u32))
        .expect("named local should exist")
}

fn anonymous_local_of_named_type(body: &Body, type_name: &str) -> u32 {
    body.locals
        .iter()
        .enumerate()
        .find_map(|(idx, decl)| match &decl.ty {
            RustType::Named { name, .. } if decl.name.is_none() && name == type_name => {
                Some(idx as u32)
            }
            _ => None,
        })
        .expect("anonymous local of the requested nominal type should exist")
}

fn has_storage_dead(body: &Body, local: u32) -> bool {
    body.blocks.iter().any(|bb| {
        bb.statements
            .iter()
            .any(|stmt| matches!(stmt, Stmt::StorageDead(dead) if *dead == local))
    })
}

fn has_drop_terminator(body: &Body, local: u32) -> bool {
    body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Drop {
                place: Place::Local(drop_local),
                ..
            } if *drop_local == local
        )
    })
}

#[test]
fn test_return_cleans_nested_non_copy_locals_before_return() {
    let source = r#"
        struct MyString { data: u32 }

        fn main() -> u32 {
            let outer: MyString = MyString { data: 1u32 };
            {
                let inner: MyString = MyString { data: 2u32 };
                return 7u32;
            }
        }
    "#;

    let body = lowered_main(source);
    let outer = local_id(&body, "outer");
    let inner = local_id(&body, "inner");

    assert!(
        has_drop_terminator(&body, inner),
        "early return should drop nested non-Copy local before returning: {body:#?}"
    );
    assert!(
        has_storage_dead(&body, inner),
        "early return should emit StorageDead for nested non-Copy local: {body:#?}"
    );
    assert!(
        has_drop_terminator(&body, outer),
        "early return should drop outer non-Copy local before returning: {body:#?}"
    );
    assert!(
        has_storage_dead(&body, outer),
        "early return should emit StorageDead for outer non-Copy local: {body:#?}"
    );
}

#[test]
fn test_return_cleans_return_expr_temporary_before_return() {
    let source = r#"
        struct MyString { data: u32 }

        fn consume(value: MyString) -> u32 {
            value.data
        }

        fn main() -> u32 {
            return consume(MyString { data: 7u32 });
        }
    "#;

    let body = lowered_main(source);
    let temp = anonymous_local_of_named_type(&body, "MyString");

    assert!(
        has_drop_terminator(&body, temp),
        "return cleanup should drop non-Copy temporaries created for the return expression: {body:#?}"
    );
    assert!(
        has_storage_dead(&body, temp),
        "return cleanup should emit StorageDead for non-Copy temporaries created for the return expression: {body:#?}"
    );
}

#[test]
fn test_return_in_then_branch_preserves_outer_binding_for_else_branch() {
    let source = r#"
        struct MyString { data: u32 }

        fn main() -> u32 {
            let outer: MyString = MyString { data: 9u32 };
            let cond: bool = false;
            if cond {
                return 1u32;
            } else {
                outer.data
            }
        }
    "#;

    let body = lowered_main(source);

    assert_eq!(
        body.locals[local_id(&body, "outer") as usize]
            .name
            .as_deref(),
        Some("outer"),
        "outer binding should still lower in the sibling branch after an early return"
    );
    assert!(
        body.blocks
            .iter()
            .any(|bb| matches!(&bb.terminator, Term::SwitchInt { .. })),
        "branching return test should still lower as an if-expression CFG"
    );
}
