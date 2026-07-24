// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! B03 gap sweep brick — name-resolution core
//! (docs/plans/GAP_SWEEP_2026-07-09.md §3, rows namespaces_scoping
//! p02/p03/p20/p21/p23).
//!
//! End-to-end (parse → elaborate → kernel re-check) pins for the three B03
//! sub-defects:
//!
//! 1. **Innermost-namespace-first resolution** (`Lean/ResolveName.lean`
//!    `resolveGlobalName`/`resolveUsingNamespace`: candidates from the current
//!    namespace outward win over the root; `_root_.x` forces the root). The
//!    silent-wrong witness SILENT_WRONG_SUSPECT-15 (`p21_shadow_inner_wins`)
//!    is pinned by VALUE: `Bar.useW` must equal the namespace `Bar.w = 2`,
//!    never the root `w = 1`.
//! 2. **No auto-bound implicits in term bodies** (`Lean/Elab/MutualDef.lean`
//!    `elabHeaders` runs under `withAutoBoundImplicit` — headers ONLY;
//!    validity rules in `Lean/Elab/Binders.lean`; an unknown identifier in a
//!    def/theorem VALUE position is a loud `unknown identifier`). OVER_ACCEPT
//!    rows p20 (section-variable leak) and p23 (typo'd body ident) must
//!    REJECT; signature-position auto-implicits stay intact.
//! 3. **Multi-segment qualified names** — Lean resolves `A.B.y` as ONE
//!    identifier via `resolveGlobalName`; clean's parser splits it into a
//!    projection chain, which must be reassembled and resolved through the
//!    namespace chain (declaration forms `namespace A namespace B` and
//!    `namespace A.B`; reference forms `A.B.c`, `B.c` inside `A`, `c` inside
//!    `A.B`) — rows p02/p03.
//!
//! Axiom hygiene: every positive declaration below has an EMPTY transitive
//! axiom closure (the `rfl` pins would fail otherwise; asserted explicitly).

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on top
/// of the default prelude. Err carries the first failure.
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// Assert `source` fails somewhere in parse/elab/kernel (fail-closed), and
/// return the failure text for shape assertions.
fn expect_rejected(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => {
            panic!("{what} must be rejected (fail-closed), but it elaborated and kernel-checked")
        }
        Err(e) => e,
    }
}

fn axiom_closure(env: &Environment, name: &str) -> Vec<String> {
    env.axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .iter()
        .map(std::string::ToString::to_string)
        .collect()
}

fn assert_axiom_free(env: &Environment, names: &[&str]) {
    for name in names {
        assert!(
            axiom_closure(env, name).is_empty(),
            "{name} must have an EMPTY transitive axiom closure (no sorry, no new axioms)"
        );
    }
}

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
