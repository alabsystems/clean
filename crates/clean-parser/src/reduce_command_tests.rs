// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `#reduce` is its own command (Lean 4.30.0-rc2 `Lean.reduceCmd`), not
//! `#eval`, and neither `#whnf` nor `#norm_num` is a command of pinned Lean
//! without Mathlib.

use crate::{parse_file, SurfaceDecl};

fn only(code: &str) -> SurfaceDecl {
    let mut decls = parse_file(code).unwrap_or_else(|e| panic!("`{code}` must parse: {e:?}"));
    assert_eq!(decls.len(), 1, "`{code}`: {decls:?}");
    decls.remove(0)
}

#[test]
fn test_parse_reduce_is_not_eval() {
    match only("#reduce Σ a, a") {
        SurfaceDecl::Reduce {
            reduce_proofs: false,
            reduce_types: false,
            ..
        } => {}
        other => panic!("`#reduce` must parse as `Reduce`, got {other:?}"),
    }
}

#[test]
fn test_parse_reduce_flags_in_lean_order() {
    for (code, proofs, types) in [
        ("#reduce (proofs := true) 1", true, false),
        ("#reduce (types := true) 1", false, true),
        ("#reduce (proofs := true) (types := true) 1", true, true),
    ] {
        match only(code) {
            SurfaceDecl::Reduce {
                reduce_proofs,
                reduce_types,
                ..
            } => assert_eq!((reduce_proofs, reduce_types), (proofs, types), "{code}"),
            other => panic!("`{code}` must parse as `Reduce`, got {other:?}"),
        }
    }
}

#[test]
fn test_parse_reduce_flag_other_than_true_is_no_flag() {
    // `(proofs := false)` is not Lean's flag (only `true` is), and the flags
    // out of order are not flags either; pinned Lean fails on each with
    // `unexpected token ':='`. Neither may become a `#reduce` of the bare
    // value (the named-argument reading did, and was accepted).
    for code in [
        "#reduce (proofs := false) 1",
        "#reduce (proofs := false)",
        "#reduce (types := true) (proofs := true)",
        "#reduce (types := true) (proofs := true) 1",
    ] {
        let decls = parse_file(code).unwrap_or_default();
        assert!(
            !decls
                .iter()
                .any(|d| matches!(d, SurfaceDecl::Reduce { .. })),
            "`{code}` must not parse as a `#reduce`: {decls:?}"
        );
    }
}

#[test]
fn test_parse_whnf_and_norm_num_are_unknown_commands() {
    // Pinned Lean: `unexpected token '#'; expected command` for both. They
    // used to be parsed as `#eval`, which ran the term and accepted.
    for (code, command) in [("#whnf 1", "#whnf"), ("#norm_num 1 + 1", "#norm_num")] {
        match only(code) {
            SurfaceDecl::RawDecl { content, .. } => {
                assert!(
                    content.contains(command),
                    "the refusal names the command: {content}"
                );
            }
            other => panic!("`{code}` must be the unknown-command refusal, got {other:?}"),
        }
    }
}
