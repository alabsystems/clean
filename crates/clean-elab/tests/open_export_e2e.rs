// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! B13 gap sweep brick — `open` / `export` / `scoped` command semantics
//! (docs/plans/GAP_SWEEP_2026-07-09.md §3, rows namespaces_scoping
//! p05/p07/p08/p09/p10/p14/p16/p22).
//!
//! End-to-end (parse → elaborate → kernel re-check → register) pins for the
//! standalone `open`/`export`/`scoped` command forms. Ground truth:
//! `Lean/Elab/BuiltinCommand.lean` (`elabOpen`, `elabExport`) and
//! `Lean/ResolveName.lean` (`OpenDecl`).
//!
//! Root cause fixed by B13: the `clean check` / compile / export-cert / repl
//! drivers elaborated each declaration WITHOUT threading the file context, so
//! a STANDALONE `open Foo` / `export Foo (x)` mutated a throwaway namespace
//! state that was discarded before the next declaration — the aliases never
//! reached the use site, which then auto-bound (`{x : Nat}`) and kernel-failed
//! (namespaces_scoping/p05,p07,p09,p14,p22). This test drives the SAME
//! context-threaded path the drivers now use.
//!
//! Every positive value pin is a `theorem … := rfl` whose transitive axiom
//! closure is EMPTY (asserted), so an accept verdict is value-certified.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, ElabResult,
    FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + preprocess + elaborate + kernel-check + register every decl in
/// `source` on top of the default prelude, threading a single [`FileContext`]
/// so standalone `open`/`export` aliases persist across declarations (exactly
/// the driver contract of `clean check` after B13). Err carries the first
/// failure (whole-call error OR an inner `Failed` leaf inside a block).
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
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

/// Assert `source` fails somewhere in parse/elab/kernel (fail-closed) and
/// return the failure text for shape assertions.
fn expect_rejected(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => {
            panic!("{what} must be rejected (fail-closed), but it elaborated and kernel-checked")
        }
        Err(e) => e,
    }
}

/// Same as [`elaborate_module`] but returns the per-top-level-decl results so a
/// caller can assert an administrative command elaborated to `Skipped` without
/// registering a constant.
fn elaborate_results(source: &str) -> Vec<Result<ElabResult, ElabError>> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("parse_file should succeed");
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect()
}

fn assert_axiom_free(env: &Environment, names: &[&str]) {
    for name in names {
        let closure: Vec<String> = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"))
            .iter()
            .map(std::string::ToString::to_string)
            .collect();
        assert!(
            closure.is_empty(),
            "{name} must have an EMPTY transitive axiom closure (no sorry, no new axioms), got {closure:?}"
        );
    }
}

// =========================================================================
// Standalone simple `open` (p05, p22)
// =========================================================================

/// p05_open_plain: `open Foo` after `end Foo` brings `Foo.x` into scope as a
/// bare `x` for the REST OF THE FILE, and the value is certified (`x = 3`).
#[test]
fn test_standalone_open_plain_value_pin() {
    let env = elaborate_module(
        r"
namespace Foo
def x : Nat := 3
end Foo
open Foo
theorem pin05 : x = 3 := rfl
",
    )
    .expect("p05: standalone `open Foo` must expose `x` and certify `x = 3`");
    assert_axiom_free(&env, &["Foo.x", "pin05"]);
}

/// p22_open_then_def: the standalone open persists across a `def` AND a later
/// `theorem` — `y := x + 1` sees the alias, and `y = 4` is certified.
#[test]
fn test_standalone_open_persists_across_def_and_theorem() {
    let env = elaborate_module(
        r"
namespace Foo
def x : Nat := 3
end Foo
open Foo
def y : Nat := x + 1
theorem pin22 : y = 4 := rfl
",
    )
    .expect("p22: standalone open must persist across def + theorem");
    assert_axiom_free(&env, &["Foo.x", "y", "pin22"]);
}

/// Multiple standalone opens accumulate; names from BOTH opened namespaces are
/// visible until file end.
#[test]
fn test_multiple_standalone_opens_accumulate() {
    let env = elaborate_module(
        r"
namespace A
def a : Nat := 1
end A
namespace B
def b : Nat := 2
end B
open A
open B
theorem pin_ab : a + b = 3 := rfl
",
    )
    .expect("multiple standalone opens must both be in force");
    assert_axiom_free(&env, &["pin_ab"]);
}

// =========================================================================
// Selective `open Foo (x)` (p09) + loud negative
// =========================================================================

/// p09_open_only: `open Foo (x)` brings ONLY `x`, not `z`.
#[test]
fn test_open_selective_brings_only_listed() {
    let env = elaborate_module(
        r"
namespace Foo
def x : Nat := 3
def z : Nat := 9
end Foo
open Foo (x)
theorem pin09 : x = 3 := rfl
",
    )
    .expect("p09: `open Foo (x)` must expose `x` and certify `x = 3`");
    assert_axiom_free(&env, &["Foo.x", "pin09"]);

    // The unlisted `z` must NOT be shortened — a bare `z` is unknown.
    expect_rejected(
        r"
namespace Foo
def x : Nat := 3
def z : Nat := 9
end Foo
open Foo (x)
def usesZ : Nat := z
",
        "unlisted `z` under `open Foo (x)`",
    );
}

/// Loud negative: `open Foo (nope)` names a member that does not exist — Lean
/// `elabOpenOnly` resolves each ident and errors. The old code silently
/// skipped it.
#[test]
fn test_open_selective_unknown_is_loud() {
    let err = expect_rejected(
        r"
namespace Foo
def x : Nat := 3
end Foo
open Foo (nope)
",
        "`open Foo (nope)` with a nonexistent member",
    );
    assert!(
        err.contains("nope") || err.contains("not found"),
        "selective-open error should name the missing member, got: {err}"
    );
}

// =========================================================================
// Renaming `open Foo renaming x → y` (p07) + explicit-only + loud negative
// =========================================================================

/// p07_open_renaming: `open Foo renaming x → xx` exposes `xx` (= `Foo.x`), and
/// the value is certified.
#[test]
fn test_open_renaming_value_pin() {
    let env = elaborate_module(
        r"
namespace Foo
def x : Nat := 3
end Foo
open Foo renaming x → xx
theorem pin07 : xx = 3 := rfl
",
    )
    .expect("p07: `open Foo renaming x → xx` must expose `xx = 3`");
    assert_axiom_free(&env, &["Foo.x", "pin07"]);
}

/// Renaming is EXPLICIT-ONLY: it imports ONLY the renamed pairs, never the
/// rest of the namespace (Lean `elabOpenRenaming`). Neither the original name
/// `x` nor the sibling `z` becomes visible.
#[test]
fn test_open_renaming_is_explicit_only() {
    expect_rejected(
        r"
namespace Foo
def x : Nat := 3
def z : Nat := 9
end Foo
open Foo renaming x → xx
def usesZ : Nat := z
",
        "sibling `z` under a renaming-only open",
    );
    expect_rejected(
        r"
namespace Foo
def x : Nat := 3
end Foo
open Foo renaming x → xx
def usesX : Nat := x
",
        "original name `x` after it was renamed to `xx`",
    );
}

/// Loud negative: renaming a nonexistent source name errors.
#[test]
fn test_open_renaming_unknown_source_is_loud() {
    expect_rejected(
        r"
namespace Foo
def x : Nat := 3
end Foo
open Foo renaming nope → n
",
        "`open Foo renaming nope → n` with a nonexistent source",
    );
}

// =========================================================================
// Hiding `open Foo hiding z` (p08 — was a parser misparse) + loud negative
// =========================================================================

/// p08_open_hiding: `open Foo hiding z` PARSES (previously it misparsed —
/// `hiding` swallowed the next declaration's keyword) and brings everything
/// except `z`; `x` is certified while `z` stays qualified-only.
#[test]
fn test_open_hiding_parses_and_hides() {
    let env = elaborate_module(
        r"
namespace Foo
def x : Nat := 3
def z : Nat := 9
end Foo
open Foo hiding z
theorem pin08 : x = 3 := rfl
",
    )
    .expect("p08: `open Foo hiding z` must parse and expose `x`");
    assert_axiom_free(&env, &["Foo.x", "pin08"]);

    // The hidden `z` must NOT be shortened.
    expect_rejected(
        r"
namespace Foo
def x : Nat := 3
def z : Nat := 9
end Foo
open Foo hiding z
def usesZ : Nat := z
",
        "hidden `z` under `open Foo hiding z`",
    );
}

/// Loud negative: hiding a name that does not exist errors (Lean
/// `elabOpenHiding` resolves each hidden ident).
#[test]
fn test_open_hiding_unknown_is_loud() {
    expect_rejected(
        r"
namespace Foo
def x : Nat := 3
end Foo
open Foo hiding nope
",
        "`open Foo hiding nope` with a nonexistent member",
    );
}

// =========================================================================
// `export Foo (x)` (p14) — current-namespace alias + loud negative
// =========================================================================

/// p14_export: `export Foo (x)` at the root registers `x ↦ Foo.x` (Lean
/// `addAlias currNamespace ++ id`), visible bare for the rest of the file; the
/// value is certified.
#[test]
fn test_export_root_value_pin() {
    let env = elaborate_module(
        r"
namespace Foo
def x : Nat := 3
end Foo
export Foo (x)
theorem pin14 : x = 3 := rfl
",
    )
    .expect("p14: `export Foo (x)` at root must expose bare `x = 3`");
    assert_axiom_free(&env, &["Foo.x", "pin14"]);
}

/// `export` INSIDE a namespace registers the alias under the CURRENT namespace
/// (`Bar.x ↦ Foo.x`): a bare `x` resolves from within `Bar` (outward walk),
/// and the alias survives `end Bar` as the qualified `Bar.x`.
#[test]
fn test_export_in_namespace_qualifies_and_survives() {
    let env = elaborate_module(
        r"
namespace Foo
def x : Nat := 3
end Foo
namespace Bar
export Foo (x)
def useHere : Nat := x
end Bar
theorem pin_qual : Bar.x = 3 := rfl
theorem pin_here : Bar.useHere = 3 := rfl
",
    )
    .expect("export inside `Bar` must register `Bar.x ↦ Foo.x` and resolve bare within `Bar`");
    assert_axiom_free(&env, &["Bar.useHere", "pin_qual", "pin_here"]);
}

/// Loud negative: exporting a nonexistent name errors (the old silent skip hid
/// typos).
#[test]
fn test_export_unknown_is_loud() {
    expect_rejected(
        r"
namespace Foo
def x : Nat := 3
end Foo
export Foo (nope)
",
        "`export Foo (nope)` with a nonexistent member",
    );
}

// =========================================================================
// Scope-end boundaries — opens are consumed at scope / file end
// =========================================================================

/// An `open` inside a `section` is rolled back at `end` (Lean pushes/pops a
/// Scope per section). A bare name from the opened namespace is unknown AFTER
/// the section closes.
#[test]
fn test_open_in_section_does_not_leak() {
    // In force inside the section:
    let env = elaborate_module(
        r"
namespace Foo
def x : Nat := 3
end Foo
section
open Foo
def insideSection : Nat := x
end
theorem pin_inside : insideSection = 3 := rfl
",
    )
    .expect("open inside a section must be in force within the section");
    assert_axiom_free(&env, &["insideSection", "pin_inside"]);

    // Leaked past `end`:
    expect_rejected(
        r"
namespace Foo
def x : Nat := 3
end Foo
section
open Foo
end
def afterSection : Nat := x
",
        "`open Foo` inside a section leaking past `end`",
    );
}

/// An `open` inside a `namespace` block is rolled back at `end` (the namespace
/// is an alias-scope boundary). A bare name is unknown after the block closes.
#[test]
fn test_open_in_namespace_does_not_leak() {
    expect_rejected(
        r"
namespace Src
def s : Nat := 7
end Src
namespace Wrap
open Src
end Wrap
def afterWrap : Nat := s
",
        "`open Src` inside `namespace Wrap` leaking past `end Wrap`",
    );
}

// =========================================================================
// `scoped notation` / `open scoped` (p10)
// =========================================================================

/// p10 (half 1): a `scoped notation` DECLARATION is not honestly implementable
/// (no namespace-gated notation registry), so it is rejected LOUDLY as an
/// `Unsupported` feature rather than silently dropped from the declaration
/// count (which previously let its token auto-bind at the use site).
#[test]
fn test_scoped_notation_is_loud_unsupported() {
    let results = elaborate_results(
        r#"
namespace Foo
scoped notation "two" => (2 : Nat)
end Foo
"#,
    );
    // The namespace block surfaces the inner failure as a `Failed` leaf; assert
    // the scoped-notation declaration did NOT silently vanish.
    let mut failures = Vec::new();
    for r in results.iter().flatten() {
        collect_failures(r, &mut failures);
    }
    let direct_unsupported = results
        .iter()
        .any(|r| matches!(r, Err(ElabError::Unsupported { .. })));
    assert!(
        direct_unsupported || failures.iter().any(|f| f.contains("scoped notation")),
        "`scoped notation` must be a LOUD unsupported error (never silently dropped); \
         results = {results:?}, failures = {failures:?}"
    );
}

/// p10 (half 2): `open scoped Foo` merely activates a namespace's scoped
/// notations — clean honors none, so it hides nothing and stays a tolerated
/// administrative no-op (faithful to the valid Lean program `open scoped Foo`;
/// it must NOT over-reject). It elaborates to `Skipped` and registers nothing.
#[test]
fn test_open_scoped_is_administrative_noop() {
    let results = elaborate_results(
        r"
namespace Foo
def x : Nat := 3
end Foo
open scoped Foo
",
    );
    // `namespace Foo` → Multiple, `open scoped Foo` → Skipped; none Err.
    assert!(
        results.iter().all(std::result::Result::is_ok),
        "`open scoped Foo` must not over-reject a valid Lean program: {results:?}"
    );
    assert!(
        matches!(results.last(), Some(Ok(ElabResult::Skipped))),
        "`open scoped Foo` must elaborate to an administrative Skipped, got {:?}",
        results.last()
    );
}

// =========================================================================
// Protected names under a simple open (p16)
// =========================================================================

/// p16_protected_open_reject: `open Foo` does NOT shorten a `protected def
/// Foo.x` (Lean skips protected names in `OpenDecl.simple`), so a bare `x`
/// after the open is unknown. The FULLY-QUALIFIED `Foo.x` still resolves.
#[test]
fn test_protected_not_shortened_by_simple_open() {
    // Bare `x` must reject...
    let err = expect_rejected(
        r"
namespace Foo
protected def x : Nat := 3
end Foo
open Foo
def y : Nat := x
",
        "bare `x` for a protected `Foo.x` under a simple `open Foo`",
    );
    assert!(
        err.contains("protected") || err.contains('x'),
        "protected diagnostic should mention the name/protection, got: {err}"
    );

    // ...but the qualified name works and certifies.
    let env = elaborate_module(
        r"
namespace Foo
protected def x : Nat := 3
end Foo
open Foo
theorem pin16 : Foo.x = 3 := rfl
",
    )
    .expect("qualified `Foo.x` must resolve even under a simple `open Foo`");
    assert_axiom_free(&env, &["pin16"]);
}

// =========================================================================
// Unknown / empty simple open stays a tolerated no-op
// =========================================================================

/// `open NonExistent` (a namespace with zero members) is a tolerated no-op —
/// clean's import lanes legitimately open namespaces whose members arrive
/// later, so an EMPTY simple open must not error.
#[test]
fn test_open_unknown_namespace_is_tolerated_noop() {
    let results = elaborate_results("open ThisNamespaceDoesNotExist\n");
    assert!(
        results.iter().all(std::result::Result::is_ok),
        "empty/unknown simple open must be a tolerated no-op: {results:?}"
    );
}

// =========================================================================
// Term-level `open X in <term>` / `open scoped X in <term>`
// =========================================================================
//
// The TERM form (`def z : Nat := open Nat in succ zero`) mirrors the DECL
// form: it opens the namespace for the SUB-TERM's name resolution and pops
// the scope afterward. Previously the parser desugared it lossily to
// `App(Ident("open"), [body])`, discarding the namespace, so `open` failed as
// an unknown identifier (`UnknownIdentWithSuggestions { name: "open" }`) — the
// #1 source-elab failure in real `Mathlib/Logic/Basic.lean`.

/// Non-scoped term-level `open Foo in <term>` in VALUE position (the real
/// Mathlib shape `theorem … := open … in …`): the opened `Foo.x` resolves as
/// a bare `x` inside the sub-term, and the resulting value is certified.
#[test]
fn test_term_open_in_resolves_and_certifies_value() {
    let env = elaborate_module(
        r"
namespace Foo
def x : Nat := 3
end Foo
def zt : Nat := open Foo in x
theorem pin_term_open : zt = 3 := rfl
",
    )
    .expect("term-level `open Foo in x` must resolve `x` from `Foo` and certify `zt = 3`");
    assert_axiom_free(&env, &["zt", "pin_term_open"]);
}

/// The opened name is scoped to the sub-term only: it must NOT leak past the
/// `open … in`. A bare `x` OUTSIDE the sub-term stays unbound and the
/// declaration fails closed (proving the scope is popped).
#[test]
fn test_term_open_in_does_not_leak_past_subterm() {
    // Inside the `open Foo in …` the bare `x` resolves to `Foo.x`; the second
    // `x`, added AFTER the sub-term, is outside the opened scope and unbound.
    let err = expect_rejected(
        r"
namespace Foo
def x : Nat := 3
end Foo
def leaky : Nat := (open Foo in x) + x
",
        "a bare `x` outside the `open Foo in …` sub-term",
    );
    assert!(
        !err.is_empty(),
        "leaked-open failure must carry a diagnostic"
    );
}

/// Scoped term-level `open scoped Foo in <term>` in value position also
/// elaborates: the sub-term `Foo.x` (fully qualified) resolves and the value
/// is certified. (Mathlib's `theorem … := open scoped Classical in Decidable.…`
/// shape.)
#[test]
fn test_term_open_scoped_in_elaborates() {
    let env = elaborate_module(
        r"
namespace Foo
def x : Nat := 3
end Foo
def zs : Nat := open scoped Foo in Foo.x
theorem pin_term_open_scoped : zs = 3 := rfl
",
    )
    .expect("`open scoped Foo in Foo.x` must elaborate and certify `zs = 3`");
    assert_axiom_free(&env, &["zs", "pin_term_open_scoped"]);
}
