// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! B03 sub-defect 3: multi-segment qualified names (p02, p03), plus the
//! block pinning WHICH unknown-identifier diagnostic each rejection gets --
//! typo, section-variable leak and self-reference must not merge.

use crate::common::*;

// =========================================================================
// Sub-defect 3 — multi-segment qualified names (p02, p03)
// =========================================================================

/// `namespaces_scoping/p02_namespace_nested`: 3-segment reference `A.B.y`
/// to a member declared via nested `namespace A / namespace B` blocks.
/// Lean resolves `A.B.y` as one identifier (`Lean/ResolveName.lean`).
#[test]
fn test_three_segment_reference_nested_namespace_form() {
    let env = elaborate_module(
        r"
namespace A
namespace B
def y : Nat := 5
end B
end A
theorem pin02 : A.B.y = 5 := rfl
",
    )
    .expect("p02 shape: `A.B.y` must resolve through nested namespace blocks");
    assert_axiom_free(&env, &["A.B.y", "pin02"]);
}

/// `namespaces_scoping/p03_namespace_dotted`: same member declared via the
/// dotted `namespace A.B` form.
#[test]
fn test_three_segment_reference_dotted_namespace_form() {
    let env = elaborate_module(
        r"
namespace A.B
def z : Nat := 7
end A.B
theorem pin03 : A.B.z = 7 := rfl
",
    )
    .expect("p03 shape: `A.B.z` must resolve through the dotted `namespace A.B` form");
    assert_axiom_free(&env, &["A.B.z", "pin03"]);
}

/// Reference form `B.c` written INSIDE `namespace A` must resolve
/// namespace-relatively to `A.B.c` (Lean `resolveUsingNamespace` prepends
/// the current namespace outward before trying the root).
#[test]
fn test_partial_chain_reference_inside_parent_namespace() {
    let env = elaborate_module(
        r"
namespace A
namespace B
def c : Nat := 9
end B
def useBc : Nat := B.c
end A
theorem pin_bc : A.useBc = 9 := rfl
",
    )
    .expect("`B.c` inside `namespace A` must resolve to `A.B.c`");
    assert_axiom_free(&env, &["A.B.c", "A.useBc", "pin_bc"]);
}

/// Reference form: bare `c` written INSIDE `namespace A.B` resolves to
/// `A.B.c`, and the 3-segment `A.B.useC` pin certifies the value.
#[test]
fn test_bare_reference_inside_dotted_namespace() {
    let env = elaborate_module(
        r"
namespace A.B
def c : Nat := 4
def useC : Nat := c
end A.B
theorem pin_c : A.B.useC = 4 := rfl
",
    )
    .expect("bare `c` inside `namespace A.B` must resolve to `A.B.c`");
    assert_axiom_free(&env, &["A.B.c", "A.B.useC", "pin_c"]);
}

/// Four segments through a deeper nesting, exercising the chain reassembly
/// past the 3-segment case.
#[test]
fn test_four_segment_reference() {
    let env = elaborate_module(
        r"
namespace A
namespace B
namespace C
def d : Nat := 3
end C
end B
end A
theorem pin4 : A.B.C.d = 3 := rfl
",
    )
    .expect("`A.B.C.d` (4 segments) must resolve");
    assert_axiom_free(&env, &["A.B.C.d", "pin4"]);
}

/// A WRONG 3-segment reference stays loud: `A.B.nope` (no such member) in a
/// def body must reject with an unknown-identifier error, never auto-bind
/// or register anything.
#[test]
fn test_three_segment_unknown_member_rejected_loud() {
    let err = expect_rejected(
        r"
namespace A.B
def c : Nat := 4
end A.B
def q : Nat := A.B.nope
",
        "`A.B.nope` (unknown member of an existing namespace)",
    );
    assert!(
        err.to_lowercase().contains("unknown identifier") || err.contains("UnknownIdent"),
        "rejection must be a loud unknown-identifier error, got: {err}"
    );
}

/// The wrong VALUE through a 3-segment reference is unprovable (the pin
/// resolves to the real declaration, not to some auto-bound stand-in).
#[test]
fn test_three_segment_wrong_value_unprovable() {
    expect_rejected(
        r"
namespace A.B
def z : Nat := 7
end A.B
theorem bad : A.B.z = 8 := rfl
",
        "`A.B.z = 8 := rfl` (wrong value through 3-segment reference)",
    );
}

/// `_root_` composes with multi-segment references: inside `namespace X`
/// that shadows the whole `A.B` chain, `_root_.A.B.c` still forces the root
/// declaration (Lean `rootNamespace` handling in `Lean/ResolveName.lean`).
#[test]
fn test_root_escape_multi_segment() {
    let env = elaborate_module(
        r"
namespace A.B
def c : Nat := 1
end A.B
namespace X.A.B
def c : Nat := 2
end X.A.B
namespace X
def useRoot : Nat := _root_.A.B.c
def useLocal : Nat := A.B.c
end X
theorem pin_root : X.useRoot = 1 := rfl
theorem pin_local : X.useLocal = 2 := rfl
",
    )
    .expect("`_root_.A.B.c` must force the root chain; bare `A.B.c` stays namespace-relative");
    assert_axiom_free(&env, &["X.useRoot", "X.useLocal", "pin_root", "pin_local"]);
}

// =========================================================================
// Which unknown-identifier diagnostic — the three cases must not merge
// =========================================================================
//
// The rejections above are all "loud unknown identifier", and that is the
// property they exist to pin. But three different questions reach the same
// failure, and answering the wrong one is worse than saying nothing: a
// self-reference offered `Quotient.ind` — the theorem name nearest `gcd` —
// which is a name-distance answer to a question nobody asked. Trust ruling
// v7/D3 requires a refusal to carry the fix WITH OPTIONS, so the elaborator
// now sorts them. These pins keep the sorting honest in BOTH directions:
// each case gets its own diagnostic, and none swallows another.

/// A typo is still a typo: the ordinary nearest-theorem list must survive the
/// recursion-aware branch, or that branch has taken over a case it does not
/// own. This is the CONTROL for the two pins below.
#[test]
fn test_ordinary_typo_keeps_the_nearest_theorem_suggestions() {
    let err = expect_rejected(
        "def uses_typo (n : Nat) : Nat := succc n",
        "typo'd body identifier `succc`, which is not this declaration's name",
    );
    assert!(
        err.contains("nearest theorem names"),
        "an ordinary typo must keep the name-distance suggestions, got: {err}"
    );
    assert!(
        !err.contains("the name being defined"),
        "the recursion refusal fired on an identifier that is NOT the \
         declaration's name, got: {err}"
    );
}

/// The self-reference case: the unresolved identifier IS the name being
/// defined, so the report is the recursion fragment and the ways across it —
/// never a nearest-theorem guess. Refusal is unchanged: `selfRef` does not
/// register either way, only the message moved.
#[test]
fn test_self_reference_reports_the_recursion_fragment_not_a_typo() {
    let err = expect_rejected(
        "def selfRef (a b : Nat) : Nat := if b == 0 then a else selfRef b (a % b)",
        "a self-reference whose recursion no lowering accepted",
    );
    for needle in [
        "the name being defined",
        "structural recursion",
        "termination_by",
        "2 parameter(s)",
        "proof position",
    ] {
        assert!(
            err.contains(needle),
            "the recursion refusal must carry the fragment and the fix \
             (v7/D3); missing `{needle}` in: {err}"
        );
    }
    assert!(
        !err.contains("nearest theorem"),
        "a self-reference is not a typo: {err}"
    );
}

/// The same, one namespace deep, where the declaration's canonical name
/// (`Deep.selfRef`) and the identifier as written (`selfRef`) differ. The
/// match is on the name AS WRITTEN in the declaration, under the same
/// `_root_.` normalization recursion DETECTION uses — two answers to "is this
/// identifier the name being defined?" would let the diagnostic and the
/// lowering disagree.
#[test]
fn test_self_reference_inside_a_namespace_still_names_the_declaration() {
    let err = expect_rejected(
        r"
namespace Deep
def selfRef (a b : Nat) : Nat := if b == 0 then a else selfRef b (a % b)
end Deep
",
        "a self-reference inside a namespace",
    );
    assert!(
        err.contains("`selfRef` is the name being defined"),
        "the refusal must name the declaration, got: {err}"
    );
    assert!(
        !err.contains("nearest theorem"),
        "a self-reference is not a typo: {err}"
    );
}

/// A theorem that cites itself is the same defect at the proof seam, and gets
/// the same refusal — a proof that assumes itself is not a missing lemma.
#[test]
fn test_self_citing_theorem_gets_the_recursion_refusal() {
    let err = expect_rejected(
        "theorem selfCite (n : Nat) : n = n := selfCite n",
        "a theorem whose proof cites itself",
    );
    assert!(
        err.contains("`selfCite` is the name being defined"),
        "the refusal must name the theorem, got: {err}"
    );
}
