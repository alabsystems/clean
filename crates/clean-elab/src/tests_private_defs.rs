// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module-local `private` definitions (G21 brick B2,
//! `designs/2026-10-08-private-name-mangling.md`): `def`, `abbrev`, `opaque`,
//! `partial def`, `instance` and `mutual` defs get Lean's
//! `_private.<module>.0.<name>`, as theorems and axioms did in B1
//! (`tests_private_names.rs`). Every expectation below was measured on Lean
//! 4.8.0 on 2026-10-08 (probe package `r3p/b2oracle`).

use crate::test_support::file_verdicts::{run_modules, run_named_file};

type Verdicts = [(String, Result<(), String>)];

/// The verdict of the LAST declaration named `name` (or ending in `.name`).
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

/// Some verdict, whatever its label, is a refusal carrying `text` (an
/// anonymous instance's refusal is labelled before its name is minted).
fn any_refused_with(verdicts: &Verdicts, text: &str) -> bool {
    verdicts
        .iter()
        .any(|(_, v)| v.as_ref().err().is_some_and(|e| e.contains(text)))
}

fn no_failures(verdicts: &Verdicts) -> bool {
    verdicts.iter().all(|(_, v)| v.is_ok())
}

const SIBLING_A: &str = "private def helper (n : Nat) : Nat := n + 1\n\
                         theorem a_ok : helper 1 = 2 := rfl\n";
const SIBLING_B: &str = "private def helper (n : Nat) : Nat := n + 2\n\
                         theorem b_ok : helper 1 = 3 := rfl\n";

/// G21's shape with `def`s (`Pkg/TC.lean`): two siblings each declare a
/// different `private def helper`, and an importer of both elaborates. Clean
/// refused B with `Duplicate declaration: helper` before B2.
#[test]
fn test_private_def_siblings_with_one_name_both_elaborate() {
    let verdicts = run_modules(&[SIBLING_A, SIBLING_B, "theorem c_ok : True := True.intro\n"]);
    assert!(no_failures(&verdicts), "{verdicts:?}");
}

/// The twin (`Pkg/TTwin2.lean`): the importer's plain `helper` reaches
/// neither sibling's private def (Lean 4.8.0: `unknown identifier 'helper'`).
#[test]
fn test_private_def_is_not_visible_to_an_importer() {
    let verdicts = run_modules(&[SIBLING_A, SIBLING_B, "def twin : Nat := helper 1\n"]);
    assert!(
        refused_with(&verdicts, "twin", "UnknownIdent")
            && refused_with(&verdicts, "twin", "\"helper\"")
            && !refused_with(&verdicts, "twin", "_private"),
        "{verdicts:?}"
    );
}

const LEAK_A: &str = "namespace Foo\n\
                      private def pd (n : Nat) : Nat := n + 1\n\
                      def q : Nat := pd 1\n\
                      end Foo\n";

/// An importer reaches an imported module's private def by no route (Lean
/// 4.8.0, `Pkg/TLU.lean` / `TLS` / `TLT`: `unknown constant 'Foo.pd'`,
/// `unknown identifier 'Foo.pd'`). Before B2 Clean ACCEPTED `unfold Foo.pd`
/// and `simp only [Foo.q, Foo.pd]` (the tactic resolver read the plain name).
/// The control (`TLOk`): the public `Foo.q` itself reduces and unfolds.
#[test]
fn test_private_def_is_not_reached_from_an_importers_tactics() {
    let verdicts = run_modules(&[
        LEAK_A,
        "theorem c_unfold : Foo.q = 2 := by unfold Foo.q; unfold Foo.pd; rfl\n\
         theorem c_simp : Foo.q = 2 := by simp only [Foo.q, Foo.pd]\n\
         theorem c_term : Foo.pd 1 = 2 := rfl\n\
         theorem c_ok : Foo.q = 2 := rfl\n\
         theorem c_unf_ok : Foo.q = 2 := by unfold Foo.q; rfl\n",
    ]);
    for name in ["c_unfold", "c_simp", "c_term"] {
        assert!(!accepted(&verdicts, name), "{name}: {verdicts:?}");
    }
    for name in ["c_ok", "c_unf_ok"] {
        assert!(accepted(&verdicts, name), "{name}: {verdicts:?}");
    }
}

/// In its own module a private def is reached by every route, and each
/// definition form registers under Lean's kernel name: structural recursion,
/// course-of-values recursion, a `where` helper reused later as `withGo.go`
/// (Lean `#check @withGo.go` prints `withGo.go`), `partial`, `abbrev`,
/// `opaque`, `unfold` / `simp` / `simp only` arguments, a `mutual` pair,
/// well-founded recursion and dot notation (all accepted by Lean 4.8.0,
/// `Pkg/TRec.lean`, `Pkg/P2.lean`).
#[test]
fn test_private_defs_resolve_by_every_route_in_their_own_module() {
    let verdicts = run_named_file(
        "private def recf : Nat → Nat\n  | 0 => 0\n  | n+1 => recf n + 2\n\
         theorem recf_two : recf 2 = 4 := rfl\n\
         private def fib : Nat → Nat\n  | 0 => 0\n  | 1 => 1\n  | n+2 => fib (n+1) + fib n\n\
         theorem fib5 : fib 5 = 5 := rfl\n\
         private def withGo (n : Nat) : Nat := go n\n\
         where go (k : Nat) : Nat := k + 1\n\
         theorem wg : withGo 1 = 2 := rfl\n\
         theorem wg2 : withGo.go 1 = 2 := rfl\n\
         private partial def loop (n : Nat) : Nat := loop n\n\
         private def useLoop : Nat → Nat := loop\n\
         private abbrev pa : Nat := 5\n\
         theorem pa5 : pa = 5 := rfl\n\
         private opaque po : Nat\n\
         def usePo : Nat := po\n\
         private def pdz (n : Nat) : Nat := n\n\
         theorem pdz_unf : pdz 3 = 3 := by unfold pdz; rfl\n\
         theorem pdz_simp : pdz 3 = 3 := by simp [pdz]\n\
         theorem pdz_simp_only : pdz 3 = 3 := by simp only [pdz]\n\
         mutual\n\
         private def isEven : Nat → Bool\n  | 0 => true\n  | n+1 => isOdd n\n\
         private def isOdd : Nat → Bool\n  | 0 => false\n  | n+1 => isEven n\n\
         end\n\
         def useEven : Bool := isEven 3\n\
         private def wf (n : Nat) : Nat := if h : n = 0 then 0 else wf (n - 1) + 1\n\
         termination_by n\n\
         decreasing_by simp_wf; omega\n\
         theorem wf0 : wf 0 = 0 := by unfold wf; rfl\n\
         structure S where\n  a : Nat\n\
         private def S.g (s : S) : Nat := s.a + 1\n\
         theorem t_dot : (S.mk 1).g = 2 := rfl\n\
         namespace Foo\n\
         private def inNs (n : Nat) : Nat := n\n\
         theorem t_in : inNs 2 = 2 := rfl\n\
         end Foo\n\
         theorem t_after : Foo.inNs 2 = 2 := rfl\n",
        "Pkg.A",
    );
    assert!(no_failures(&verdicts), "{verdicts:?}");
    for kernel in [
        "_private.Pkg.A.0.recf",
        "_private.Pkg.A.0.fib",
        "_private.Pkg.A.0.withGo",
        "_private.Pkg.A.0.withGo.go",
        "_private.Pkg.A.0.useLoop",
        "_private.Pkg.A.0.pa",
        "_private.Pkg.A.0.pdz",
        "_private.Pkg.A.0.wf",
        "_private.Pkg.A.0.S.g",
        "_private.Pkg.A.0.Foo.inNs",
    ] {
        assert!(
            verdicts.iter().any(|(n, _)| n == kernel),
            "{kernel}: {verdicts:?}"
        );
    }
    // No private def kept its plain name.
    for plain in [
        "recf",
        "fib",
        "withGo",
        "withGo.go",
        "pa",
        "pdz",
        "Foo.inNs",
    ] {
        assert!(
            !verdicts.iter().any(|(n, _)| n == plain),
            "{plain}: {verdicts:?}"
        );
    }
}

/// Lean's `checkNotAlreadyDeclared` texts for a private/public pair of one
/// def name in one module (`Pkg/E.lean`, `F`, `G`, `G2`).
#[test]
fn test_private_def_redeclarations_are_refused_with_leans_messages() {
    let cases = [
        (
            "private def x : Nat := 1\ndef x : Nat := 2\n",
            "x",
            "a private declaration 'x' has already been declared",
        ),
        (
            "def y : Nat := 1\nprivate def y : Nat := 2\n",
            "y",
            "a non-private declaration 'y' has already been declared",
        ),
        (
            "private def z : Nat := 1\nprivate def z : Nat := 2\n",
            "z",
            "private declaration 'z' has already been declared",
        ),
        (
            "private abbrev z : Nat := 1\nprivate opaque z : Nat\n",
            "z",
            "private declaration 'z' has already been declared",
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

/// Two anonymous private instances of one class: Lean 4.8.0 freshens the
/// PUBLIC `instKNat` and only then makes it private, so the second collides
/// ("private declaration 'instKNat' has already been declared") and a public
/// one after it is "a private declaration 'instKNat' …" (`Pkg/Inst2.lean`) —
/// never a silent `instKNat_1`.
#[test]
fn test_anonymous_private_instances_follow_leans_naming() {
    let verdicts = run_named_file(
        "class K (α : Type) where k : α\n\
         private instance : K Nat := ⟨1⟩\n\
         private instance : K Nat := ⟨2⟩\n",
        "M",
    );
    assert!(
        any_refused_with(
            &verdicts,
            "\"private declaration 'instKNat' has already been declared"
        ),
        "{verdicts:?}"
    );
    let verdicts = run_named_file(
        "class K (α : Type) where k : α\n\
         private instance : K Nat := ⟨1⟩\n\
         instance : K Nat := ⟨3⟩\n",
        "M",
    );
    assert!(
        any_refused_with(
            &verdicts,
            "a private declaration 'instKNat' has already been declared"
        ),
        "{verdicts:?}"
    );
}

/// An anonymous private instance is `_private.M.0.instClsNat` and stays
/// active, in its module and in an importer, where a later public instance
/// of the importer wins (Lean 4.8.0, `Pkg/TI.lean`, `TIU`).
#[test]
fn test_private_instance_is_active_in_its_module_and_an_importer() {
    let own = run_named_file(
        "class Cls (α : Type) where c : α\n\
         private instance : Cls Nat := ⟨42⟩\n\
         theorem c42 : (Cls.c : Nat) = 42 := rfl\n\
         private instance namedI : Cls Bool := ⟨true⟩\n\
         theorem cb : (Cls.c : Bool) = true := rfl\n",
        "TI",
    );
    assert!(no_failures(&own), "{own:?}");
    assert!(
        own.iter().any(|(n, _)| n == "_private.TI.0.instClsNat")
            && own.iter().any(|(n, _)| n == "_private.TI.0.namedI"),
        "{own:?}"
    );
    let verdicts = run_modules(&[
        "class Cls (α : Type) where c : α\n\
         private instance : Cls Nat := ⟨42⟩\n",
        "theorem c42' : (Cls.c : Nat) = 42 := rfl\n\
         instance : Cls Nat := ⟨7⟩\n\
         theorem c7 : (Cls.c : Nat) = 7 := rfl\n",
    ]);
    assert!(no_failures(&verdicts), "{verdicts:?}");
}

/// `#print axioms` of a private def prints its kernel name, as Lean 4.8.0
/// does (`Pkg/PAGuard2.lean`); a `#guard_msgs` expecting the plain name is
/// refused (`Pkg/PAGuard.lean`). `#check` shows private defs by their
/// user-facing names, in the type too (`Pkg/TCheck.lean`).
#[test]
fn test_private_def_messages_print_as_lean_does() {
    let lean_text = "private axiom ax : 1 = 1\n\
                     private def pdx : 1 = 1 := ax\n\
                     /-- info: '_private.PAGuard2.0.pdx' depends on axioms: \
                     [_private.PAGuard2.0.ax] -/\n\
                     #guard_msgs in\n#print axioms pdx\n";
    let verdicts = run_named_file(lean_text, "PAGuard2");
    assert!(no_failures(&verdicts), "{verdicts:?}");
    let plain_text = "private axiom ax : 1 = 1\n\
                      private def pdx : 1 = 1 := ax\n\
                      /-- info: 'pdx' depends on axioms: [_private.PAGuard.0.ax] -/\n\
                      #guard_msgs in\n#print axioms pdx\n";
    let verdicts = run_named_file(plain_text, "PAGuard");
    assert!(!no_failures(&verdicts), "{verdicts:?}");
    let check = "private def pd (n : Nat) : Nat := n + 1\n\
                 private theorem pt : pd 1 = 2 := rfl\n\
                 /-- info: pt : pd 1 = 2 -/\n#guard_msgs in\n#check pt\n\
                 /-- info: pd 1 : Nat -/\n#guard_msgs in\n#check pd 1\n";
    let verdicts = run_named_file(check, "TCheck");
    assert!(no_failures(&verdicts), "{verdicts:?}");
}

/// `private abbrev` keeps its `private`: the parser dropped every modifier
/// written before `abbrev`, so a private abbreviation was public and an
/// importer could name it (the B1 release build accepted `def t_ab : Nat :=
/// pab` below). Lean 4.8.0: `unknown identifier 'pab'` (`Pkg/AbB.lean`); the
/// in-module use and an importer's unrelated declaration are accepted.
#[test]
fn test_private_abbrev_is_private_to_its_module() {
    let own = "private abbrev pab : Nat := 5\ntheorem pab5 : pab = 5 := rfl\n";
    let verdicts = run_named_file(own, "Pkg.AbA");
    assert!(no_failures(&verdicts), "{verdicts:?}");
    assert!(
        verdicts.iter().any(|(n, _)| n == "_private.Pkg.AbA.0.pab"),
        "{verdicts:?}"
    );
    let verdicts = run_modules(&[own, "def t_ab : Nat := pab\ndef t_ok : Nat := 1\n"]);
    assert!(
        refused_with(&verdicts, "t_ab", "pab"),
        "an importer must not name a private abbrev: {verdicts:?}"
    );
    assert!(accepted(&verdicts, "t_ok"), "{verdicts:?}");
}
