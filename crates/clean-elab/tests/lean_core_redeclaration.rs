// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A declaration whose full name is a Lean 4.8.0 core (`Init`) constant is
//! refused, as Lean refuses it ("already declared"), whether or not Clean's
//! prelude models the constant; and Lean keywords are never names.
//!
//! Measured 2026-09-26/27 against Lean 4.8.0, where every build before this
//! change (db37ea99b, e3f696689, 3f45fb7c6) accepted the redeclaration and
//! computed with the USER's body: `def Nat.lcm := fun x y => x + y + 7` then
//! `Nat.lcm 4 6 = 17 := rfl` (Lean: `Nat.lcm 4 6 = 12`, and the `def` is an
//! error), and likewise for `List.getLast!`, `bne`,
//! `EmptyCollection.emptyCollection` read back through `∅`, `SDiff.sdiff`
//! through `\`, and more. An anonymous `instance : Hashable String` was named
//! `instHashableString` — Lean's core instance — so `@Hashable.hash String
//! instHashableString "a" = 7` was proved about the user's instance.
//!
//! Every statement a case expects to hold was checked with Lean 4.8.0 too.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

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

/// Parse, elaborate, kernel-check and register `source` with ONE file
/// context (the `clean check` driver contract).
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
            return Err(failures.join("\n"));
        }
    }
    Ok(env)
}

fn refused(source: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => panic!("Lean 4.8.0 refuses this; Clean accepted it:\n{source}"),
        Err(error) => error,
    }
}

/// Every declaration form, at the root, through a namespace block, a dotted
/// name, `_root_`, `private`/`protected` and `mutual`, for core constants
/// Clean does not model (`Nat.lcm`, `bne`, …) and ones it does (`Nat.add`,
/// `Bool`).
#[test]
fn core_constant_redeclarations_are_refused_in_every_form() {
    let names = [
        "Nat.lcm",
        "Nat.nextPowerOfTwo",
        "Int.fmod",
        "List.getLast!",
        "Option.get!",
        "bne",
        "strictAnd",
        "EmptyCollection.emptyCollection",
        "SDiff.sdiff",
        "instHashableString",
        "Nat.add",
        "Bool",
    ];
    for name in names {
        let (parent, last) = name.rsplit_once('.').unwrap_or(("", name));
        let mut forms = vec![
            format!("def {name} : Nat := 1"),
            format!("theorem {name} : True := trivial"),
            format!("abbrev {name} : Nat := 1"),
            format!("opaque {name} : Nat"),
            format!("axiom {name} : True"),
            format!("structure {name} where\n  x : Nat"),
            format!("inductive {name} where\n  | a"),
            format!("class {name} where\n  x : Nat"),
            format!("instance {name} : Inhabited Nat := ⟨1⟩"),
            format!("private def {name} : Nat := 1"),
            format!("protected def {name} : Nat := 1"),
            format!("namespace Zq\ndef _root_.{name} : Nat := 1\nend Zq"),
            format!("mutual\ndef {name} : Nat := 1\nend"),
        ];
        if !parent.is_empty() {
            forms.push(format!(
                "namespace {parent}\ndef {last} : Nat := 1\nend {parent}"
            ));
        }
        for form in forms {
            let error = refused(&format!("{form}\n"));
            assert!(
                error.contains("has already been declared"),
                "`{name}` must be refused as already declared:\n{form}\n{error}"
            );
        }
    }
}

/// The measured false theorems: each setup is now refused, so nothing about
/// the user's function can be proved under the core name.
#[test]
fn the_measured_false_theorems_are_refused() {
    for (setup, statement) in [
        ("def Nat.lcm : Nat → Nat → Nat := fun x y => x + y + 7", "Nat.lcm 4 6 = 17"),
        ("def List.getLast! : List Nat → Nat := fun _ => 7", "List.getLast! [1, 2] = 7"),
        (
            "def EmptyCollection.emptyCollection : List Nat := [7, 7]",
            "(∅ : List Nat).length = 2",
        ),
        (
            "instance : SDiff Nat := ⟨fun a b => a - b⟩\ndef SDiff.sdiff : Nat → Nat → Nat := fun x y => x + y + 7",
            "(5 : Nat) \\ 2 = 14",
        ),
        ("def bne : Nat → Nat → Bool := fun _ _ => true", "bne 3 3 = true"),
        (
            "instance : Hashable String := ⟨fun _ => 7⟩",
            "@Hashable.hash String instHashableString \"a\" = 7",
        ),
    ] {
        let error = refused(&format!("{setup}\ntheorem t : {statement} := rfl\n"));
        assert!(!error.contains("parse error"), "must parse: {error}");
    }
}

/// Names that are NOT core constants stay the user's (Lean 4.8.0 accepts
/// each, with the value stated): the same spelling under another namespace,
/// a fresh sibling name, and an anonymous instance, which takes a fresh name
/// instead of the core instance's.
#[test]
fn names_outside_core_stay_declarable() {
    for (setup, statement) in [
        (
            "namespace Zq\ndef Nat.lcm : Nat → Nat → Nat := fun x y => x + y + 7\nend Zq",
            "Zq.Nat.lcm 4 6 = 17",
        ),
        (
            "def Nat.lcm' : Nat → Nat → Nat := fun x y => x + y + 7",
            "Nat.lcm' 4 6 = 17",
        ),
        (
            "def bne' : Nat → Nat → Bool := fun _ _ => true",
            "bne' 3 3 = true",
        ),
        (
            "instance : Hashable String := ⟨fun _ => 7⟩",
            "hash \"a\" = 7",
        ),
    ] {
        elaborate_module(&format!("{setup}\ntheorem t : {statement} := rfl\n"))
            .unwrap_or_else(|e| panic!("Lean 4.8.0 accepts this:\n{setup}\n{statement}\n{e}"));
    }
}

/// A Lean keyword is never a name: every binding site refuses it at parse
/// time, while the escaped spelling is an ordinary identifier, a dotted name
/// containing the keyword is one identifier, and an `inductive` constructor
/// may be spelled so (Lean reads constructor names with `rawIdent`). An
/// unescaped `nomatch` is always the keyword, even with `«nomatch»` bound.
#[test]
fn lean_keywords_are_never_names() {
    for bad in [
        "def f (nomatch : Nat → Nat) (a : Nat) : Nat := nomatch a",
        "def f (a : Nat) : Nat := (fun (nomatch : Nat → Nat) => nomatch a) (· + 7)",
        "def f (a : Nat) : Nat := let nomatch : Nat → Nat := fun x => x + 7; nomatch a",
        "def nomatch : Nat → Nat := fun x => x + 7",
        "def f (a : Nat) : Nat := match a with\n  | at => at",
        "def f (a : Nat) : Nat := Id.run do\n  let using := a\n  return using",
        "theorem f : ∀ x : Nat, x = x := by\n  intro nofun\n  rfl",
        "section\nvariable (for : Nat)\nend",
        "structure S where\n  nomatch : Nat",
        "notation \"NN\" nomatch => nomatch + 1",
        "def f (a : Nat) : Nat := (fun («nomatch» : Nat → Nat) => nomatch a) (· + 7)",
    ] {
        refused(&format!("{bad}\n"));
    }
    for (setup, statement) in [
        ("def «nomatch» (n : Nat) : Nat := n + 1", "«nomatch» 3 = 4"),
        ("def Foo.nomatch (n : Nat) : Nat := n + 2", "Foo.nomatch 3 = 5"),
        (
            "inductive T where\n  | nomatch : T\n  | at : T\ndef T.toNat : T → Nat\n  | .nomatch => 1\n  | .at => 2",
            "T.toNat T.nomatch + T.toNat .at = 3",
        ),
        ("def g (x : Nat) : Nat := x", "(fun («nomatch» : Nat → Nat) => «nomatch» 3) g = 3"),
        ("def h (x : False) : Nat := nomatch x", "h = h"),
    ] {
        elaborate_module(&format!("{setup}\ntheorem t : {statement} := rfl\n"))
            .unwrap_or_else(|e| panic!("Lean 4.8.0 accepts this:\n{setup}\n{statement}\n{e}"));
    }
}

/// The rule consults the environment, as Lean's does: one built WITHOUT the
/// prelude (`Environment::new()`, a Lean `prelude` file's world — here the
/// shape of `clean-verify`'s kernel-foundation units) holds no core constant,
/// so `inductive Nat` and `def Nat.add` are declarable there, and the same
/// declarations are refused over the prelude.
#[test]
fn a_bare_environment_holds_no_core_constant() {
    let foundation = [
        "inductive Nat : Type\n| zero : Nat\n| succ : Nat → Nat",
        "def Nat.add (n : Nat) (m : Nat) : Nat := match m with\n| Nat.zero => n\n| Nat.succ k => Nat.succ (Nat.add n k)",
    ];
    let mut bare = Environment::new();
    for src in foundation {
        let decls = parse_file(src).expect("parses");
        clean_elab::elaborate_decl_and_register(&mut bare, &decls[0])
            .unwrap_or_else(|e| panic!("a bare environment holds no `Nat`: {e}"));
    }
    assert!(!bare.models_lean_init());
    assert!(Environment::with_prelude().models_lean_init());
    for src in foundation {
        let error = refused(&format!("{src}\n"));
        assert!(error.contains("has already been declared"), "{error}");
    }
}
