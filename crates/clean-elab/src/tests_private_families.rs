// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module-local `private` inductive families (G21 brick B3,
//! `designs/2026-10-08-private-name-mangling.md`): a `private` `inductive`,
//! `structure`, `class` or `mutual` inductive member is
//! `_private.<module>.0.<name>`, and so is every name derived from it
//! (constructors, recursors, projections). Every expectation below was
//! measured on Lean 4.8.0 on 2026-10-09 (probe package `r3p/b3oracle`,
//! files named per test).

use clean_kernel::Name;

use crate::test_support::file_verdicts::{run_modules, run_named_file, run_named_file_env};

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

fn no_failures(verdicts: &Verdicts) -> bool {
    verdicts.iter().all(|(_, v)| v.is_ok())
}

fn n(s: &str) -> Name {
    Name::from_string(s)
}

/// `Pkg/S1.lean` without its `private` field (Clean's parser has no field
/// modifiers yet): a private structure, inductive, indexed family, class and
/// instance, used by every in-module route Lean 4.8.0 accepts.
const OWN_FAMILIES: &str = "namespace Foo\n\
     private structure S where\n  x : Nat\n  y : Nat\n\
     def pubS : S := ⟨1, 2⟩\n\
     def S.sum (s : S) : Nat := s.x + s.y\n\
     private def S.psum (s : S) : Nat := s.x + s.y\n\
     theorem in_mod2 : pubS.psum = 3 := rfl\n\
     theorem fx : pubS.x = 1 := rfl\n\
     theorem fy : S.y pubS = 2 := rfl\n\
     theorem anon : pubS = ⟨1, 2⟩ := rfl\n\
     theorem inst : pubS = { x := 1, y := 2 } := rfl\n\
     theorem mk : pubS = S.mk 1 2 := rfl\n\
     theorem upd : { pubS with x := 5 }.x = 5 := rfl\n\
     private inductive Col where\n  | r | g\n\
     def colN : Col → Nat\n  | .r => 0\n  | Col.g => 1\n\
     theorem colN_g : colN Col.g = 1 := rfl\n\
     def pubCol : Col := .r\n\
     private class Cls (α : Type) where\n  c : α\n\
     private instance : Cls Nat := ⟨4⟩\n\
     theorem cls4 : (Cls.c : Nat) = 4 := rfl\n\
     private inductive Tree where\n  | leaf : Tree\n  | node : Tree → Tree → Tree\n\
     def nodeCount : Tree → Nat\n  | Tree.leaf => 0\n  | .node a b => nodeCount a + nodeCount b + 1\n\
     theorem nc : nodeCount (Tree.node Tree.leaf Tree.leaf) = 1 := rfl\n\
     end Foo\n";

/// In its own module a private family is reached by every route Lean 4.8.0
/// accepts (`Pkg/S1.lean`), and each registers under Lean's kernel name:
/// `_private.Pkg.S1.0.Foo.S`, its constructor `…Foo.S.mk` (Lean's `#print
/// Foo.S` prints `_private.Pkg.S1.0.Foo.S.mk : Nat → Nat → Foo.S`), its
/// projections, the constructors `…Foo.Col.r` / `.g` and the class. No plain
/// name is left behind.
#[test]
fn test_private_families_resolve_by_every_route_in_their_own_module() {
    let (env, verdicts) = run_named_file_env(OWN_FAMILIES, "Pkg.S1");
    assert!(no_failures(&verdicts), "{verdicts:?}");
    for inductive in [
        "_private.Pkg.S1.0.Foo.S",
        "_private.Pkg.S1.0.Foo.Col",
        "_private.Pkg.S1.0.Foo.Cls",
        "_private.Pkg.S1.0.Foo.Tree",
    ] {
        assert!(env.get_inductive(&n(inductive)).is_some(), "{inductive}");
    }
    for ctor in [
        "_private.Pkg.S1.0.Foo.S.mk",
        "_private.Pkg.S1.0.Foo.Col.r",
        "_private.Pkg.S1.0.Foo.Col.g",
        "_private.Pkg.S1.0.Foo.Tree.node",
    ] {
        assert!(env.get_constructor(&n(ctor)).is_some(), "{ctor}");
    }
    for constant in [
        "_private.Pkg.S1.0.Foo.S.x",
        "_private.Pkg.S1.0.Foo.S.y",
        "_private.Pkg.S1.0.Foo.Cls.c",
        "_private.Pkg.S1.0.Foo.S.psum",
        // A PUBLIC method on a private structure keeps its public name.
        "Foo.S.sum",
    ] {
        assert!(env.get_const(&n(constant)).is_some(), "{constant}");
    }
    for plain in [
        "Foo.S",
        "Foo.S.mk",
        "Foo.S.x",
        "Foo.Col",
        "Foo.Col.r",
        "Foo.Cls",
    ] {
        let plain = n(plain);
        assert!(
            env.get_inductive(&plain).is_none()
                && env.get_constructor(&plain).is_none()
                && env.get_const(&plain).is_none(),
            "{plain} must not be registered"
        );
    }
}

/// Lean 4.8.0's quirk (`Pkg/S1q.lean`): a PUBLIC `def S.sum` on a private
/// `S` is no field-notation target, even in its own module — "invalid field
/// 'sum', the environment does not contain '_private.Pkg.S1q.0.Foo.S.sum'".
/// Clean accepted `pubS.sum` before B3 (the structure kept its plain name).
/// The control: the method applied by name.
#[test]
fn test_public_method_on_a_private_structure_is_no_field_target() {
    let verdicts = run_named_file(
        "namespace Foo\n\
         private structure S where\n  x : Nat\n  y : Nat\n\
         def pubS : S := ⟨1, 2⟩\n\
         def S.sum (s : S) : Nat := s.x + s.y\n\
         theorem in_mod : pubS.sum = 3 := rfl\n\
         theorem by_name : S.sum pubS = 3 := rfl\n\
         end Foo\n",
        "Pkg.S1q",
    );
    assert!(!accepted(&verdicts, "in_mod"), "{verdicts:?}");
    assert!(
        refused_with(&verdicts, "in_mod", "sum"),
        "the refusal names the field: {verdicts:?}"
    );
    assert!(accepted(&verdicts, "by_name"), "{verdicts:?}");
}

/// The module an importer elaborates after: a private structure reachable
/// only through public terms of its type.
const IMPORTED: &str = "namespace Foo\n\
     private structure S where\n  x : Nat\n  y : Nat\n\
     def pubS : S := ⟨1, 2⟩\n\
     def S.sum (s : S) : Nat := s.x + s.y\n\
     private inductive Col where\n  | r | g\n\
     def colN : Col → Nat\n  | .r => 0\n  | .g => 1\n\
     def pubCol : Col := .r\n\
     private class Cls (α : Type) where\n  c : α\n\
     private instance : Cls Nat := ⟨4⟩\n\
     end Foo\n";

/// From an importer, Lean 4.8.0 refuses another module's private structure
/// through its type with its own messages (`Pkg/S2`–`S5`, `S8`–`S10`), and
/// the importer's plain names reach none of the family. Controls Lean accepts
/// (`Pkg/S7`, `S11`): a public function of the private type, and a relative
/// constructor `.g` read off the expected type.
#[test]
fn test_private_structure_is_refused_from_an_importer_as_lean_does() {
    let verdicts = run_modules(&[
        IMPORTED,
        "theorem s2 : Foo.pubS.x = 1 := rfl\n\
         theorem s3 : Foo.pubS = ⟨1, 2⟩ := rfl\n\
         theorem s4 : Foo.pubS.sum = 3 := rfl\n\
         theorem s5 : Foo.pubS = { x := 1, y := 2 } := rfl\n\
         theorem s8 : Foo.colN Foo.Col.g = 1 := rfl\n\
         def s9 (s : Foo.S) : Nat := 0\n\
         theorem s10 : (Foo.Cls.c : Nat) = 4 := rfl\n\
         theorem ok_fn : Foo.colN Foo.pubCol = 0 := rfl\n\
         theorem ok_rel : Foo.colN .g = 1 := rfl\n",
    ]);
    assert!(
        refused_with(
            &verdicts,
            "s2",
            "field 'x' from structure '_private.M0.0.Foo.S' is private"
        ),
        "{verdicts:?}"
    );
    assert!(
        refused_with(
            &verdicts,
            "s3",
            "invalid ⟨...⟩ notation, constructor for `_private.M0.0.Foo.S` is marked as private"
        ),
        "{verdicts:?}"
    );
    assert!(
        refused_with(
            &verdicts,
            "s5",
            "invalid {...} notation, constructor for `_private.M0.0.Foo.S` is marked as private"
        ),
        "{verdicts:?}"
    );
    for name in ["s4", "s8", "s9", "s10"] {
        assert!(!accepted(&verdicts, name), "{name}: {verdicts:?}");
    }
    for name in ["ok_fn", "ok_rel"] {
        assert!(accepted(&verdicts, name), "{name}: {verdicts:?}");
    }
}

/// G21's shape with families (`Pkg/SA`, `SB`, `SC`): two siblings each
/// declare a private structure `P` and a private inductive `Col`, and an
/// importer of both elaborates (Lean 4.8.0 builds `SC`). The twin
/// (`Pkg/STwin`): the importer's `P.mk` reaches neither (Lean: "unknown
/// identifier 'P.mk'").
#[test]
fn test_private_family_siblings_with_one_name_both_elaborate() {
    let sibling = |tag: &str| {
        format!(
            "private structure P where\n  v : Nat\n\
             private inductive Col where\n  | r | g\n\
             theorem {tag}_ok : (P.mk 1).v = 1 := rfl\n\
             theorem {tag}_col : Col.r = Col.r := rfl\n"
        )
    };
    let (a, b) = (sibling("a"), sibling("b"));
    let verdicts = run_modules(&[
        a.as_str(),
        b.as_str(),
        "theorem c_ok : True := True.intro\n",
    ]);
    assert!(no_failures(&verdicts), "{verdicts:?}");
    let verdicts = run_modules(&[
        a.as_str(),
        b.as_str(),
        "theorem twin : (P.mk 1).v = 1 := rfl\n",
    ]);
    assert!(
        refused_with(&verdicts, "twin", "UnknownIdent")
            && !refused_with(&verdicts, "twin", "_private"),
        "{verdicts:?}"
    );
}

/// Lean's `checkNotAlreadyDeclared` texts for families (`Pkg/RD`–`RD4`):
/// a private and a public family of one name, a private family and a private
/// def of its name, and a public def named like a private constructor.
#[test]
fn test_private_family_redeclarations_are_refused_with_leans_messages() {
    let cases = [
        (
            "private structure X where\n  a : Nat\nstructure X where\n  a : Nat\n",
            "X",
            "a private declaration 'X' has already been declared",
        ),
        (
            "structure Y where\n  a : Nat\nprivate structure Y where\n  a : Nat\n",
            "Y",
            "a non-private declaration 'Y' has already been declared",
        ),
        (
            "private inductive Z where\n  | z\nprivate def Z : Nat := 1\n",
            "Z",
            "private declaration 'Z' has already been declared",
        ),
        (
            "private inductive W where\n  | z\ndef W.z : Nat := 1\n",
            "W.z",
            "a private declaration 'W.z' has already been declared",
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

/// A `mutual` block of private inductives (`Pkg/Mu`), an indexed private
/// family with implicit parameters, and a private parameterised structure
/// (`Pkg/Ind`) and a private `extends` chain (`Pkg/Ext`): accepted by Lean
/// 4.8.0, and registered under module-local names.
#[test]
fn test_private_mutual_indexed_and_extending_families() {
    let (env, verdicts) = run_named_file_env(
        "mutual\n\
         private inductive Ev : Type where\n  | zero : Ev\n  | succ : Od → Ev\n\
         private inductive Od : Type where\n  | succ : Ev → Od\n\
         end\n\
         def evZero : Ev := Ev.zero\n\
         def evTwo : Ev := .succ (.succ .zero)\n\
         namespace Foo\n\
         private inductive Vec (α : Type) : Nat → Type where\n  \
           | nil : Vec α 0\n  | cons : α → Vec α n → Vec α (n + 1)\n\
         def vlen : Vec α n → Nat\n  | .nil => 0\n  | .cons _ v => vlen v + 1\n\
         theorem vlen2 : vlen (Vec.cons 1 (Vec.cons 2 Vec.nil)) = 2 := rfl\n\
         private structure Box (α : Type) where\n  val : α\n\
         def unbox (b : Box Nat) : Nat := b.val\n\
         theorem ub : unbox ⟨3⟩ = 3 := rfl\n\
         theorem ub2 : unbox { val := 4 } = 4 := rfl\n\
         end Foo\n\
         private structure P1 where\n  a : Nat\n\
         private structure P2 extends P1 where\n  b : Nat\n\
         def p2 : P2 := { a := 1, b := 2 }\n\
         theorem p2a : p2.a = 1 := rfl\n\
         theorem p2b : p2.toP1.a = 1 := rfl\n",
        "Pkg.Fam",
    );
    assert!(no_failures(&verdicts), "{verdicts:?}");
    for inductive in [
        "_private.Pkg.Fam.0.Ev",
        "_private.Pkg.Fam.0.Od",
        "_private.Pkg.Fam.0.Foo.Vec",
        "_private.Pkg.Fam.0.Foo.Box",
        "_private.Pkg.Fam.0.P1",
        "_private.Pkg.Fam.0.P2",
    ] {
        assert!(env.get_inductive(&n(inductive)).is_some(), "{inductive}");
    }
    for plain in ["Ev", "Od", "Foo.Vec", "Foo.Box", "P1", "P2"] {
        assert!(env.get_inductive(&n(plain)).is_none(), "{plain}");
    }
}

/// Without a module name (unit tests, the REPL, Trust islands) a private
/// family keeps its plain name and the private mark (`docs/DECISIONS.md`
/// R42), and in-module use is unchanged.
#[test]
fn test_unnamed_context_keeps_plain_family_names() {
    let mut env = clean_kernel::Environment::with_prelude();
    let decls = clean_parser::parse_file(
        "private structure S where\n  x : Nat\n\
         def pubS : S := ⟨1⟩\n\
         theorem fx : pubS.x = 1 := rfl\n",
    )
    .expect("fixture must parse");
    let mut file_ctx = crate::FileContext::new();
    for decl in &decls {
        let processed = crate::preprocess_decl_with_context(decl, &mut file_ctx);
        crate::elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .expect("declaration must elaborate");
    }
    assert!(env.get_inductive(&n("S")).is_some());
    assert!(env.is_private(&n("S")));
    assert!(env.get_const(&n("fx")).is_some());
}

/// `Pkg/E.lean` of the G21 B3 review probes: a private structure reached by
/// an importer only through public terms of its type.
const REVIEW_E: &str = "namespace Foo\n\
     private structure S where\n  x : Nat\n  y : Nat\n\
     def pubS : S := ⟨1, 2⟩\n\
     abbrev PubT := S\n\
     end Foo\n";

/// The routes into another module's private structure the B3 review found
/// open (probes `Pkg/G1`–`G20`, Lean 4.8.0 `lake env lean`, 2026-10-09).
/// Lean refuses a numeric projection on a `structure` with the FIELD's name
/// (`.1` is `x`), and a `⟨...⟩` PATTERN with the term's `⟨...⟩` text, in a
/// `match`, an equation, a `let` and a `fun` binder alike. Controls Lean
/// accepts: the named constructor `.mk` as a term (`G9`) and as a pattern
/// (`G10`), the `obtain` / `cases` tactics (`G18`, `G19`), and matches on
/// several discriminants or on a pair, whose `⟨...⟩` / tuple encoding is not
/// the private structure's (`GX`: `g21`–`g23`).
#[test]
fn test_private_structure_projection_index_and_anon_patterns_are_refused() {
    let verdicts = run_modules(&[
        REVIEW_E,
        "def g1 : Nat := Foo.pubS.1\n\
         def g2 : Nat := Foo.pubS.2\n\
         theorem g14 : Foo.pubS.1 = 1 := rfl\n\
         def g20 : Nat := (Foo.pubS).2 + 0\n\
         def g3 : Nat := match Foo.pubS with | ⟨a, _⟩ => a\n\
         def g4 : Foo.PubT → Nat | ⟨a, _⟩ => a\n\
         def g5 : Nat := let ⟨a, _⟩ := Foo.pubS; a\n\
         def g16 : Nat := (fun (s : Foo.PubT) => match s with | ⟨a, _⟩ => a) Foo.pubS\n\
         def g17 : Foo.PubT → Nat := fun ⟨a, _⟩ => a\n\
         def g9 : Foo.PubT := .mk 3 4\n\
         def g10 : Nat := match Foo.pubS with | .mk a _ => a\n\
         theorem g18 : True := by\n  obtain ⟨a, b⟩ := Foo.pubS\n  trivial\n\
         theorem g19 : True := by\n  cases h : Foo.pubS with\n  | mk a b => trivial\n\
         def g21 (s : Foo.PubT) (n : Nat) : Nat := match s, n with | _, 0 => 0 | _, _ => 1\n\
         def g22 : Foo.PubT → Nat → Nat\n  | _, 0 => 0\n  | _, _ => 1\n\
         def g23 (p : Foo.PubT × Nat) : Nat := match p with | ⟨_, n⟩ => n\n",
    ]);
    let field = |f: &str| format!("field '{f}' from structure '_private.M0.0.Foo.S' is private");
    for (name, f) in [("g1", "x"), ("g2", "y"), ("g14", "x"), ("g20", "y")] {
        assert!(
            refused_with(&verdicts, name, &field(f)),
            "{name}: {verdicts:?}"
        );
    }
    let anon = "invalid ⟨...⟩ notation, constructor for `_private.M0.0.Foo.S` is marked as private";
    for name in ["g3", "g4", "g5", "g16", "g17"] {
        assert!(refused_with(&verdicts, name, anon), "{name}: {verdicts:?}");
    }
    for name in ["g9", "g10", "g18", "g19", "g21", "g22", "g23"] {
        assert!(accepted(&verdicts, name), "{name}: {verdicts:?}");
    }
}

/// In its OWN module the same projections and patterns are accepted (Lean
/// 4.8.0 checks only names private to ANOTHER module).
#[test]
fn test_own_private_structure_projection_index_and_anon_patterns_are_accepted() {
    let verdicts = run_named_file(
        &format!(
            "{REVIEW_E}\
             def g1 : Nat := Foo.pubS.1\n\
             theorem g14 : Foo.pubS.1 = 1 := rfl\n\
             def g3 : Nat := match Foo.pubS with | ⟨a, _⟩ => a\n\
             def g4 : Foo.PubT → Nat | ⟨a, _⟩ => a\n\
             def g5 : Nat := let ⟨a, _⟩ := Foo.pubS; a\n\
             def g17 : Foo.PubT → Nat := fun ⟨a, _⟩ => a\n"
        ),
        "Pkg.E",
    );
    assert!(no_failures(&verdicts), "{verdicts:?}");
}

/// Sibling modules each deriving for their own `private inductive Col`
/// (`Pkg/DA`, `DB`, importer `DC`): Lean 4.8.0 names the derived instance by
/// the user-facing type name, a PUBLIC name, so the importer is refused
/// ("environment already contains 'instDecidableEqCol.proof_2' from
/// Pkg.DA"). Clean names its derived instance from `Col` too, so the second
/// sibling's derivation collides; a framed mangled name gave each its own
/// instance and accepted the importer.
#[test]
fn test_private_siblings_deriving_one_instance_name_collide() {
    let sibling = "private inductive Col where\n  | red | green\n  deriving DecidableEq, Repr\n\
                   theorem dec : Col.red ≠ Col.green := by decide\n";
    let (env, verdicts) = run_named_file_env(sibling, "Pkg.DA");
    assert!(no_failures(&verdicts), "{verdicts:?}");
    assert!(
        env.get_const(&n("_private.Pkg.DA.0.Col")).is_some()
            || env.get_inductive(&n("_private.Pkg.DA.0.Col")).is_some(),
        "the private family keeps its module-local name"
    );
    let mut env = env;
    let second = crate::test_support::file_verdicts::run_named_file_in(&mut env, sibling, "Pkg.DB");
    assert!(
        !no_failures(&second),
        "the second sibling's derivation must collide: {second:?}"
    );
}
