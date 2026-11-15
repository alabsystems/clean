// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module-local `private` theorems and axioms (G21,
//! `designs/2026-10-08-private-name-mangling.md`). In a module the driver
//! named, a private theorem is registered as `_private.<module>.0.<name>`, its
//! plain name resolves in that module only (Lean's private step), and Lean's
//! `checkNotAlreadyDeclared` rules refuse a private/public pair of one name.
//! Every expectation below was measured on Lean 4.8.0 (2026-10-08).

use crate::test_support::file_verdicts::{run_file, run_modules, run_named_file};

type Verdicts = [(String, Result<(), String>)];

/// The verdict of the LAST declaration named `name` (or ending in `.name`):
/// a refused redeclaration comes after the accepted original.
fn last_verdict<'a>(verdicts: &'a Verdicts, name: &str) -> &'a Result<(), String> {
    let dotted = format!(".{name}");
    &verdicts
        .iter()
        .rev()
        .find(|(n, _)| n == name || n.ends_with(&dotted))
        .unwrap_or_else(|| panic!("`{name}` must have a verdict; got {verdicts:?}"))
        .1
}

fn accepted(verdicts: &Verdicts, name: &str) -> bool {
    last_verdict(verdicts, name).is_ok()
}

fn refused_with(verdicts: &Verdicts, name: &str, text: &str) -> bool {
    last_verdict(verdicts, name)
        .as_ref()
        .err()
        .is_some_and(|e| e.contains(text))
}

fn no_failures(verdicts: &Verdicts) -> bool {
    verdicts.iter().all(|(_, v)| v.is_ok())
}

const SIBLING_A: &str = "private theorem helper : True := True.intro\n\
                         theorem a_ok : True := helper\n";
const SIBLING_B: &str = "private theorem helper : True := True.intro\n\
                         theorem b_ok : True := helper\n";

/// The G21 repro: two siblings each declare `private theorem helper`, and an
/// importer of both elaborates (Lean 4.8.0 builds it; clean-r2 refused B with
/// `Duplicate declaration: helper`).
#[test]
fn test_private_theorem_siblings_with_one_name_both_elaborate() {
    let verdicts = run_modules(&[
        SIBLING_A,
        SIBLING_B,
        "theorem c_ok : True := a_ok\ntheorem c_ok2 : True := b_ok\n",
    ]);
    assert!(no_failures(&verdicts), "{verdicts:?}");
}

/// The twin: the importer's plain `helper` reaches neither sibling's private
/// theorem (Lean 4.8.0: `unknown identifier 'helper'`).
#[test]
fn test_private_theorem_is_not_visible_to_an_importer() {
    let verdicts = run_modules(&[SIBLING_A, SIBLING_B, "theorem g21_twin : True := helper\n"]);
    // `UnknownIdent` / `UnknownIdentWithSuggestions`, both rendered
    // `Unknown identifier: helper`; no suggestion names a mangled sibling.
    assert!(
        refused_with(&verdicts, "g21_twin", "UnknownIdent")
            && refused_with(&verdicts, "g21_twin", "\"helper\"")
            && !refused_with(&verdicts, "g21_twin", "_private"),
        "{verdicts:?}"
    );
}

/// A sibling's private theorem through a TACTIC: `rw [helper2]` and `simp
/// only [helper2]` reached it by its plain name (clean-r2 accepted both;
/// Lean 4.8.0: `unknown identifier`), as do `exact` and the term.
#[test]
fn test_private_theorem_is_not_reached_from_an_importers_tactics() {
    let verdicts = run_modules(&[
        "def d (n : Nat) : Nat := n\n\
         private theorem helper2 (n : Nat) : d n = n := rfl\n\
         theorem a_ok : True := True.intro\n",
        "theorem c_rw (n : Nat) : d n = n := by rw [helper2]\n\
         theorem c_simp (n : Nat) : d n = n := by simp only [helper2]\n\
         theorem c_exact (n : Nat) : d n = n := by exact helper2 n\n\
         theorem c_term (n : Nat) : d n = n := helper2 n\n",
    ]);
    for name in ["c_rw", "c_simp", "c_exact", "c_term"] {
        assert!(!accepted(&verdicts, name), "{name}: {verdicts:?}");
    }
}

/// An importer's public `theorem Foo.t` beside an imported private `Foo.t`
/// (Lean 4.8.0 accepts; the two are distinct constants).
#[test]
fn test_public_theorem_over_an_imported_private_one_is_accepted() {
    let verdicts = run_modules(&[
        "private theorem Foo.t : True := True.intro\ntheorem a_ok : True := Foo.t\n",
        "theorem Foo.t : 1 = 1 := rfl\ntheorem use_t : 1 = 1 := Foo.t\n",
    ]);
    assert!(no_failures(&verdicts), "{verdicts:?}");
}

/// An imported `@[simp] private` lemma stays in the simp set, as in Lean
/// (measured: `Pkg/H.lean`, `simp [Foo.q]` closes `Foo.q = 2`).
#[test]
fn test_imported_private_simp_lemma_fires_in_the_importer() {
    let verdicts = run_modules(&[
        "def pd (n : Nat) : Nat := n + 1\n\
         @[simp] private theorem pd_one : pd 1 = 2 := rfl\n\
         def q : Nat := pd 1\n",
        "theorem h : q = 2 := by simp [q]\n",
    ]);
    assert!(accepted(&verdicts, "h"), "{verdicts:?}");
}

/// In its own module, a private theorem is reached everywhere and by every
/// route: term, `exact`, `simp`, `simp only`, `rw`, `attribute [simp]`,
/// inside and after its namespace, through `open` and `_root_`, a dotted name
/// with `open Foo`, dot notation, and a `where` helper.
#[test]
fn test_private_theorem_resolves_by_every_route_in_its_own_module() {
    let verdicts = run_named_file(
        "def d (n : Nat) : Nat := n\n\
         private theorem p (n : Nat) : d n = n := rfl\n\
         theorem t_term (n : Nat) : d n = n := p n\n\
         theorem t_exact (n : Nat) : d n = n := by exact p n\n\
         theorem t_simp (n : Nat) : d n = n := by simp [p]\n\
         theorem t_simp_only (n : Nat) : d n = n := by simp only [p]\n\
         theorem t_rw (n : Nat) : d n = n := by rw [p]\n\
         attribute [simp] p\n\
         theorem t_attr (n : Nat) : d n = n := by simp\n\
         namespace N\n\
         private theorem q : d 2 = 2 := rfl\n\
         theorem t_in : d 2 = 2 := q\n\
         end N\n\
         theorem t_after : d 2 = 2 := N.q\n\
         theorem t_root : d 2 = 2 := _root_.N.q\n\
         open N in\n\
         theorem t_open : d 2 = 2 := q\n\
         private theorem Foo.bar : d 3 = 3 := rfl\n\
         open Foo\n\
         theorem t_nspriv : d 3 = 3 := bar\n\
         structure S where\n  a : Nat\n\
         private theorem S.self (s : S) : s.a = s.a := rfl\n\
         theorem t_dot (s : S) : s.a = s.a := s.self\n\
         private theorem withHelper : d 4 = 4 := go\n\
         where go : d 4 = 4 := rfl\n\
         theorem t_where : d 4 = 4 := withHelper.go\n",
        "Pkg.A",
    );
    assert!(no_failures(&verdicts), "{verdicts:?}");
    // The kernel name is Lean's, not the plain one.
    assert!(
        verdicts.iter().any(|(n, _)| n == "_private.Pkg.A.0.p"),
        "{verdicts:?}"
    );
}

/// Lean's `checkNotAlreadyDeclared` texts for a private/public pair of one
/// name in one module (ThE, ThF, ThG, ThH).
#[test]
fn test_private_redeclarations_are_refused_with_leans_messages() {
    let cases = [
        (
            "private theorem x : True := True.intro\ntheorem x : True := True.intro\n",
            "x",
            "a private declaration 'x' has already been declared",
        ),
        (
            "theorem y : True := True.intro\nprivate theorem y : True := True.intro\n",
            "y",
            "a non-private declaration 'y' has already been declared",
        ),
        (
            "private theorem z : True := True.intro\nprivate theorem z : True := True.intro\n",
            "z",
            "private declaration 'z' has already been declared",
        ),
        (
            "namespace N\nprivate theorem w : True := True.intro\nend N\n\
             theorem N.w : True := True.intro\n",
            "w",
            "a private declaration 'N.w' has already been declared",
        ),
    ];
    for (src, name, message) in cases {
        let verdicts = run_named_file(src, "M");
        assert!(
            refused_with(&verdicts, name, message),
            "{src}: {verdicts:?}"
        );
    }
}

/// An imported public `Foo.uses_ax`, then this module's `private theorem
/// Foo.uses_ax` (Lean 4.8.0: "a non-private declaration 'Foo.uses_ax' has
/// already been declared").
#[test]
fn test_private_theorem_over_an_imported_public_one_is_refused() {
    let verdicts = run_modules(&[
        "theorem Foo.uses_ax : True := True.intro\n",
        "namespace Foo\nprivate theorem uses_ax : True := trivial\nend Foo\n",
    ]);
    assert!(
        refused_with(
            &verdicts,
            "uses_ax",
            "a non-private declaration 'Foo.uses_ax' has already been declared"
        ),
        "{verdicts:?}"
    );
}

const PRIVATE_AXIOM: &str = "namespace Foo\n\
                             private axiom ax : 1 = 1\n\
                             theorem uses_ax : 1 = 1 := ax\n\
                             end Foo\n";

/// `#print axioms` prints the mangled name, as Lean 4.8.0 does: a
/// `#guard_msgs` expecting `[_private.PrivPrint.0.Foo.ax]` passes and one
/// expecting `[Foo.ax]` is refused (clean-r2 had the two inverted).
#[test]
fn test_print_axioms_names_a_private_axiom_as_lean_does() {
    let lean_text = format!(
        "{PRIVATE_AXIOM}/-- info: 'Foo.uses_ax' depends on axioms: \
         [_private.PrivPrint.0.Foo.ax] -/\n#guard_msgs in\n#print axioms Foo.uses_ax\n"
    );
    let verdicts = run_named_file(&lean_text, "PrivPrint");
    assert!(no_failures(&verdicts), "{verdicts:?}");
    let plain_text = format!(
        "{PRIVATE_AXIOM}/-- info: 'Foo.uses_ax' depends on axioms: [Foo.ax] -/\n\
         #guard_msgs in\n#print axioms Foo.uses_ax\n"
    );
    let verdicts = run_named_file(&plain_text, "PrivPrint");
    assert!(!no_failures(&verdicts), "{verdicts:?}");
    let own = "private theorem pt : True := True.intro\n\
               /-- info: '_private.PrivGuard.0.pt' does not depend on any axioms -/\n\
               #guard_msgs in\n#print axioms pt\n";
    let verdicts = run_named_file(own, "PrivGuard");
    assert!(no_failures(&verdicts), "{verdicts:?}");
}

/// `#check` of a private theorem still prints its user-facing name (Lean
/// 4.8.0: `pt : pd 1 = 2`).
#[test]
fn test_check_prints_a_private_theorem_by_its_user_name() {
    let verdicts = run_named_file(
        "private def pd (n : Nat) : Nat := n + 1\n\
         private theorem pt : pd 1 = 2 := rfl\n\
         /-- info: pt : pd 1 = 2 -/\n#guard_msgs in\n#check pt\n",
        "PrivGuard",
    );
    assert!(no_failures(&verdicts), "{verdicts:?}");
}

/// `#print` resolves its name as Lean's does, so it reaches this module's
/// private theorem inside its namespace (Lean 4.8.0 prints it; Clean refused
/// `#print pt` there as an unknown identifier). The printed text is brick B4's.
#[test]
fn test_print_reaches_a_private_theorem_inside_its_namespace() {
    let verdicts = run_named_file(
        "namespace Foo
private theorem pt : True := True.intro
#print pt
end Foo
",
        "PrivPrint",
    );
    assert!(no_failures(&verdicts), "{verdicts:?}");
}

/// A context with no module name keeps the plain-name regime
/// (`docs/DECISIONS.md`, 2026-10-08).
#[test]
fn test_unnamed_context_keeps_plain_private_names() {
    let verdicts = run_file("private theorem helper : True := True.intro\n");
    assert!(
        verdicts.iter().any(|(n, v)| n == "helper" && v.is_ok()),
        "{verdicts:?}"
    );
}

/// A module names its OWN private declarations in an explicit `open` /
/// `export` list, a `renaming` and a `hiding` (Lean 4.8.0's
/// `resolveQualifiedName` private step; this file builds under Lean 4.8.0 as
/// `r3fix2/or/Pkg/O2.lean`, 2026-10-09: `Foo.Col` holds only private names,
/// so it is a namespace only through its `namespace` command, as in Lean). The sibling twin: an importer's `open Foo (bar)` reaches no other
/// module's private `Foo.bar` (Lean 4.8.0: "unknown constant 'Foo.bar'",
/// probes `Pkg/OB1`–`OB3`; the public `open Foo (pub)` control `OB4` builds).
#[test]
fn test_explicit_open_and_export_reach_this_modules_private_names() {
    let own = "namespace Foo\n\
               private def bar : Nat := 1\n\
               private theorem bar_eq : bar = 1 := rfl\n\
               private inductive Col where\n  | red | green\n\
               end Foo\n\
               namespace Q\nprivate def qq : Nat := 5\nend Q\n";
    let verdicts = run_named_file(
        &format!(
            "{own}\
             section\nopen Foo (bar bar_eq)\ntheorem o1 : bar = 1 := bar_eq\nend\n\
             section\nopen Foo renaming bar → baz\ntheorem o2 : baz = 1 := rfl\nend\n\
             section\nopen Foo hiding bar\ntheorem o3 : True := True.intro\nend\n\
             namespace Foo.Col\nend Foo.Col\n\
             section\nopen Foo.Col (red)\ntheorem o4 : red = Foo.Col.red := rfl\nend\n\
             export Q (qq)\ntheorem n1 : qq = 5 := rfl\n"
        ),
        "Pkg.O2",
    );
    assert!(verdicts.iter().all(|(_, v)| v.is_ok()), "{verdicts:?}");
    let importer = |text: &str| {
        run_modules(&[
            "namespace Foo\nprivate def bar : Nat := 1\ndef pub : Nat := 2\nend Foo\n",
            text,
        ])
    };
    for (label, text) in [
        (
            "open",
            "open Foo (bar)\ntheorem twin : True := True.intro\n",
        ),
        (
            "renaming",
            "open Foo renaming bar → baz\ntheorem twin : True := True.intro\n",
        ),
        (
            "export",
            "export Foo (bar)\ntheorem twin : True := True.intro\n",
        ),
    ] {
        let verdicts = importer(text);
        assert!(
            verdicts.iter().any(|(_, v)| v.is_err()),
            "{label}: a sibling's private name must stay unreachable: {verdicts:?}"
        );
    }
    let control = importer("open Foo (pub)\ntheorem ctl : pub = 2 := rfl\n");
    assert!(control.iter().all(|(_, v)| v.is_ok()), "{control:?}");
}
