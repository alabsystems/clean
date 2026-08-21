// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// **`spans-and-tags`, CLOSED at the KIND level.** The clause CONTENT is still
/// erased — that is what makes the digest producer-invariant — but the erasure
/// is no longer unbounded: an annotation kind the reader has not declared inert
/// is a refusal.
#[test]
fn spans_are_erased_but_an_undeclared_clause_is_now_refused() {
    // (1) THE BOUNDARY, unchanged: a `#loc` does not reach the core module.
    let with_loc = PARAM_PTR.replace("ret %1", "ret %1  ; #loc: 1 2 3");
    assert_ne!(with_loc, PARAM_PTR);
    assert_eq!(
        canon(&ir_mint::read_emitted(&with_loc).expect("a")),
        canon(&ir_mint::read_emitted(PARAM_PTR).expect("b")),
        "a `#loc` clause must not reach the core module — erasing it is what makes the digest \
         producer-invariant"
    );

    // (2) THE CLOSURE. Until 2026-08-20 the reader dropped every `  ; #…`
    // suffix whatever it said, so a producer that started annotating an
    // instruction with something trust-bearing would have been erased in
    // silence — the exact failure the exhaustive-enum flag shows one level in.
    let undeclared = PARAM_PTR.replace("ret %1", "ret %1  ; #exhaustive: true");
    let e = ir_mint::read_emitted(&undeclared)
        .map(|_| ())
        .expect_err("an undeclared annotation kind must be refused, not dropped");
    assert!(
        format!("{e}").contains("exhaustive"),
        "the refusal must name the clause it will not erase: {e}"
    );

    // The allowlist is FIVE and each entry is inert for a stated reason; a lane
    // that could grow silently would be no lane at all.
    assert_eq!(
        ir_mint::CLAUSE_KINDS.len(),
        5,
        "{:?}",
        ir_mint::CLAUSE_KINDS
    );
    for k in ir_mint::CLAUSE_KINDS {
        let ok = PARAM_PTR.replace("ret %1", &format!("ret %1  ; #{k}: x"));
        ir_mint::read_emitted(&ok)
            .unwrap_or_else(|e| panic!("a declared clause kind `#{k}` must read: {e}"));
    }

    // …and the KIND SET is pinned, so a body that stops carrying one is
    // refused by the interface lane rather than accepted as the same artifact.
    let t = witness_tags(
        "m::f",
        r#"{"block":0,"index":0,"ssa":0,"ty":"ptr"}"#,
        r#""load:None""#,
        r#""loc""#,
    );
    ir_mint::project(&with_loc, &t).expect("the pinned clause set must be accepted");
    let e = ir_mint::project(PARAM_PTR, &t)
        .map(|_| ())
        .expect_err("a body carrying NO annotation where the pin says `#loc` must be refused");
    assert!(
        format!("{e}").contains("annotation clause kinds"),
        "unexpected refusal: {e}"
    );
}
