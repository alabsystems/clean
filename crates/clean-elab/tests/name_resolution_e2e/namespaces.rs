// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! B03 sub-defects 1 and 2: innermost-namespace-first resolution (p21, p18)
//! and the absence of auto-bound implicits in term bodies (p20, p23).

use crate::common::*;

// =========================================================================
// Sub-defect 1 — innermost-namespace-first resolution (p21, p18)
// =========================================================================

/// SILENT_WRONG_SUSPECT-15 (`namespaces_scoping/p21_shadow_inner_wins`):
/// inside `namespace Bar`, a bare `w` must resolve to `Bar.w` (= 2), NOT the
/// root `w` (= 1). Lean: `Lean/ResolveName.lean` `resolveUsingNamespace`
/// walks the current namespace outward BEFORE the root-stage candidates.
/// The rfl VALUE pin is the witness — before B03, clean kernel-certified
/// `Bar.useW = 1`.
#[test]
fn test_inner_namespace_shadows_root_value_pin() {
    let env = elaborate_module(
        r"
def w : Nat := 1
namespace Bar
def w : Nat := 2
def useW : Nat := w
end Bar
theorem pin21 : Bar.useW = 2 := rfl
",
    )
    .expect("p21 shape: inner-namespace `w` must win over root `w`");
    assert_axiom_free(&env, &["w", "Bar.w", "Bar.useW", "pin21"]);
}

/// The negative face of the same pin: the ROOT value must be UNPROVABLE.
/// If `Bar.useW = 1` still kernel-checks by rfl, resolution regressed to
/// root-first.
#[test]
fn test_inner_namespace_root_value_unprovable() {
    expect_rejected(
        r"
def w : Nat := 1
namespace Bar
def w : Nat := 2
def useW : Nat := w
end Bar
theorem bad : Bar.useW = 1 := rfl
",
        "`Bar.useW = 1 := rfl` (root-w reading of the p21 shape)",
    );
}

/// `namespaces_scoping/p18_root_escape`: `_root_.g` forces root resolution
/// even when the current namespace declares its own `g`
/// (`Lean/ResolveName.lean`: the `_root_` prefix bypasses the namespace
/// walk). rfl value pins on both readings.
#[test]
fn test_root_escape_forces_root_value_pin() {
    let env = elaborate_module(
        r"
def g : Nat := 5
namespace Foo
def g : Nat := 7
def h : Nat := _root_.g
def i : Nat := g
end Foo
theorem pin_h : Foo.h = 5 := rfl
theorem pin_i : Foo.i = 7 := rfl
",
    )
    .expect("p18 shape: `_root_.g` must force the root; bare `g` stays namespace-local");
    assert_axiom_free(&env, &["Foo.h", "Foo.i", "pin_h", "pin_i"]);
}

/// Resolution still falls through to the root when the namespace has no
/// matching member (the walk ends at the root stage, Lean
/// `resolveGlobalNameCore`'s anonymous-namespace step).
#[test]
fn test_namespace_walk_falls_back_to_root() {
    let env = elaborate_module(
        r"
def base : Nat := 11
namespace Quux
def useBase : Nat := base
end Quux
theorem pin_fb : Quux.useBase = 11 := rfl
",
    )
    .expect("bare `base` inside `Quux` must fall back to the root `base`");
    assert_axiom_free(&env, &["Quux.useBase", "pin_fb"]);
}

// =========================================================================
// Sub-defect 2 — no auto-bound implicits in term bodies (p20, p23)
// =========================================================================

/// OVER_ACCEPT-04 (`namespaces_scoping/p23_body_autobind_reject`): a typo'd
/// identifier in a def BODY is a loud unknown-identifier error — Lean's
/// auto-bound implicits apply to signatures only
/// (`Lean/Elab/MutualDef.lean` `elabHeaders` under `withAutoBoundImplicit`).
#[test]
fn test_body_typo_ident_rejected_loud() {
    let err = expect_rejected(
        "def f2 : Nat := m + 1",
        "p23 shape: typo'd body identifier `m`",
    );
    assert!(
        err.to_lowercase().contains("unknown identifier") || err.contains("UnknownIdent"),
        "rejection must be a loud unknown-identifier error, got: {err}"
    );
}

/// OVER_ACCEPT-03 (`namespaces_scoping/p20_section_var_leak_reject`): a
/// section variable is out of scope after `end`; the body reference must be
/// a loud unknown-identifier error, not a silently auto-bound implicit that
/// changes the definition's arity.
#[test]
fn test_section_variable_leak_rejected_loud() {
    let err = expect_rejected(
        r"
section
variable (n : Nat)
end
def f : Nat := n + 1
",
        "p20 shape: section variable `n` referenced after `end`",
    );
    assert!(
        err.to_lowercase().contains("unknown identifier") || err.contains("UnknownIdent"),
        "rejection must be a loud unknown-identifier error, got: {err}"
    );
}

/// A typo'd identifier in a THEOREM PROOF body (term-mode) is equally loud.
#[test]
fn test_proof_body_typo_rejected_loud() {
    let err = expect_rejected(
        "theorem t : (1 : Nat) = 1 := rfll",
        "typo'd proof-term identifier `rfll`",
    );
    assert!(
        err.to_lowercase().contains("unknown identifier") || err.contains("UnknownIdent"),
        "rejection must be a loud unknown-identifier error, got: {err}"
    );
}

/// Section variables referenced INSIDE the section still work (p11 shape):
/// the variable is prepended as a real binder, not auto-bound.
#[test]
fn test_section_variable_inside_section_still_works() {
    let env = elaborate_module(
        r"
section
variable (n : Nat)
def addOne : Nat := n + 1
end
theorem pin11 : addOne 3 = 4 := rfl
",
    )
    .expect("p11 shape: section variable used inside its section must elaborate");
    assert_axiom_free(&env, &["addOne", "pin11"]);
}

/// SIGNATURE-position auto-implicits stay intact
/// (`attributes_options/p15` shape): `α`/`β` in binder types auto-bind
/// exactly as before (Lean header elaboration under
/// `withAutoBoundImplicit`).
#[test]
fn test_signature_auto_implicit_intact() {
    let env = elaborate_module(
        r"
def constFn (a : α) (b : β) : α := a
theorem pin_cf : constFn (3 : Nat) (5 : Nat) = 3 := rfl
",
    )
    .expect("signature auto-implicits (binder types) must keep working");
    assert_axiom_free(&env, &["constFn", "pin_cf"]);
}
