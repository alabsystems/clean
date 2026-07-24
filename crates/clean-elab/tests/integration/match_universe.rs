// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Match elaboration universe-level regression tests.
//!
//! Tests that match/casesOn elaboration correctly infers universe levels
//! for universe-polymorphic inductives, rather than hardcoding Level::zero().

/// #3053: eliminator_levels fell back to Level::zero() for non-Sort branch types
/// and for scrutinee types without explicit Const levels. The fix allocates
/// fresh universe parameters (matching elab_app.rs) so unification can solve
/// the correct levels.
#[test]
fn test_issue3053_higher_universe_match_rebox() {
    use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
    use clean_kernel::env::Environment;
    use clean_parser::parse_file;

    let mut env = Environment::new();
    let mut file_ctx = FileContext::new();

    let decls = parse_file(
        r"universe u
inductive Wrap (α : Type u) : Type (u + 1)
| mk : α → Wrap α

inductive Box (α : Type u) : Type (u + 1)
| mk : α → Box α

def rebox (w : Wrap (Type u)) : Box (Type u) :=
  match w with
  | Wrap.mk x => Box.mk x",
    )
    .unwrap();

    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "Higher-universe declaration {i} should elaborate: {:?}",
            result.err()
        );
    }

    use clean_kernel::Name;
    assert!(
        env.get_const(&Name::from_string("rebox")).is_some(),
        "rebox should be registered in the environment"
    );
}
