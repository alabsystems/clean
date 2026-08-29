// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the imported-notation harvester and the seeded parse.

use super::NotationSeed;
use crate::surface::{NotationKind, Projection, SurfaceDecl, SurfaceExpr};
use crate::tactic_patterns::TacticPatterns;
use crate::Parser;

/// Assert an expansion is exactly the UNAPPLIED dotted name `Top.top`.
///
/// The property under test is "the recovered command did not absorb the line
/// below it", and the falsifier is an application spine — so the `App` check
/// is asserted separately and first. The positive shape is asked of the TERM:
/// `Top.top` is a `Proj`, not an `Ident("Top.top")`, which is what the first
/// version of these two tests wrongly assumed.
fn assert_unapplied_top_top(expansion: &SurfaceExpr) {
    assert!(
        !matches!(expansion, SurfaceExpr::App(..)),
        "expansion must not have absorbed the following line, got {expansion:?}"
    );
    let SurfaceExpr::Proj(_, base, Projection::Named(field)) = expansion else {
        panic!("expected the dotted name `Top.top`, got {expansion:?}");
    };
    assert!(
        matches!(&**base, SurfaceExpr::Ident(_, n) if n == "Top"),
        "projection base should be `Top`, got {base:?}"
    );
    assert_eq!(field, "top");
}

/// Harvest a module source and return the seed.
fn harvest(source: &str) -> NotationSeed {
    let mut seed = NotationSeed::new();
    seed.harvest_module_source(source);
    seed
}

/// Parse `source` with `seed` installed, returning how many top-level
/// declarations came back as recovered `RawDecl`s.
fn seeded_rawdecls(seed: &NotationSeed, source: &str) -> usize {
    let patterns = TacticPatterns::default();
    let report = Parser::parse_file_seeded(source, &patterns, seed).expect("file parses");
    report
        .decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::RawDecl { .. }))
        .count()
}

#[test]
fn test_harvest_infix_notation_yields_one_entry() {
    let seed = harvest("infixr:26 \" ⥤ \" => Functor\n");
    assert_eq!(seed.len(), 1, "one infixr command must be harvested");
    let entry = &seed.entries()[0];
    assert!(matches!(entry.kind, NotationKind::Infixr));
    assert_eq!(entry.precedence, Some(26));
    assert!(entry.scope_ns.is_none(), "plain notation is unscoped");
}

#[test]
fn test_harvest_local_notation_is_not_exported() {
    // Lean's `local notation` does not survive the file it is declared in.
    // 496 of Mathlib's notation commands are `local`.
    let seed = harvest("local notation \"‖\" e \"‖\" => norm e\n");
    assert_eq!(seed.len(), 0, "`local` notation must never be exported");
}

#[test]
fn test_harvest_notation3_is_not_treated_as_core_notation() {
    let seed = harvest("notation3 \"∑ \"(...)\", \"r => Finset.sum r\n");
    assert_eq!(
        seed.len(),
        0,
        "`notation3` is Mathlib's extended-binder command, not core `notation`"
    );
}

#[test]
fn test_harvest_scoped_notation_records_its_namespace() {
    let source = "namespace Cat\n\nscoped infixr:10 \" ⟶ \" => Quiver.Hom\n\nend Cat\n";
    let seed = harvest(source);
    assert_eq!(seed.len(), 1);
    assert_eq!(seed.entries()[0].scope_ns.as_deref(), Some("Cat"));
}

#[test]
fn test_harvest_nested_namespace_records_the_full_path() {
    let source =
        "namespace Outer\nnamespace Inner\nscoped postfix:max \"ᵒᵖ\" => Opposite\nend Inner\nend Outer\n";
    let seed = harvest(source);
    assert_eq!(seed.len(), 1);
    assert_eq!(seed.entries()[0].scope_ns.as_deref(), Some("Outer.Inner"));
}

#[test]
fn test_harvest_section_does_not_extend_the_namespace_path() {
    let source = "namespace N\nsection Foo\nscoped prefix:max \"↥\" => Coe\nend Foo\nend N\n";
    let seed = harvest(source);
    assert_eq!(seed.len(), 1);
    assert_eq!(
        seed.entries()[0].scope_ns.as_deref(),
        Some("N"),
        "a `section` inside a namespace must not become part of the path"
    );
}

#[test]
fn test_harvest_ignores_notation_quoted_in_a_docstring() {
    let source = "/--\nDeclare it with `notation \"⊥\" => Bot.bot`, like this:\n\n  notation \"⊤\" => Top.top\n-/\ndef unrelated : Nat := 0\n";
    let seed = harvest(source);
    assert_eq!(
        seed.len(),
        0,
        "a notation quoted inside `/- … -/` is prose, not a declaration"
    );
}

#[test]
fn test_harvest_ignores_notation_after_a_line_comment_marker() {
    let seed = harvest("-- notation \"⊤\" => Top.top\ndef d : Nat := 0\n");
    assert_eq!(seed.len(), 0);
}

#[test]
fn test_harvest_strips_an_attribute_prefix() {
    // `@[inherit_doc]` prefixes 100+ of Mathlib's notation commands.
    let seed = harvest("@[inherit_doc] infixl:65 \" +ᵥ \" => VAdd.vadd\n");
    assert_eq!(seed.len(), 1);
    assert!(matches!(seed.entries()[0].kind, NotationKind::Infixl));
}

/// `Mathlib/Data/Opposite.lean:48` puts a `--` comment on the keyword's own
/// line and the pattern on the next line at **column 0**. An INCOMPLETE command
/// must keep reading whatever the indentation: Lean cannot start a new
/// top-level command while this one is unfinished. Three of Mathlib's 579
/// exportable notation commands have this shape.
#[test]
fn test_harvest_continues_an_incomplete_command_past_a_comment_and_column_zero() {
    let source = concat!(
        "@[inherit_doc]\n",
        "notation:max -- Use a high right binding power so `Presheaf Cᵒᵖ` groups right.\n",
        "-- and a second comment line\n",
        "α \"ᵒᵖ\" => Opposite α\n",
        "\n",
        "namespace Opposite\n",
    );
    let seed = harvest(source);
    assert_eq!(seed.len(), 1, "the wrapped command must be recovered");
    assert_eq!(seed.entries()[0].precedence, Some(1024), "`:max` is 1024");
    assert!(matches!(seed.entries()[0].kind, NotationKind::Notation));
}

#[test]
fn test_harvest_recovers_a_wrapped_command() {
    let source = "notation:max \"⟪\" x \", \" y \"⟫\" =>\n  inner x y\n";
    let seed = harvest(source);
    assert_eq!(seed.len(), 1, "a wrapped command must still be recovered");
    assert!(matches!(seed.entries()[0].kind, NotationKind::Notation));
}

#[test]
fn test_harvest_does_not_swallow_an_indented_line_after_a_complete_command() {
    // A command whose `=>` already has an expansion is COMPLETE, so the
    // indented line below it belongs to something else. Without the
    // completeness check the two lines were joined and the expansion parsed as
    // the application `Top.top Bot.bot`.
    let source = "notation \"⊤\" => Top.top\n  Bot.bot\n";
    let seed = harvest(source);
    assert_eq!(seed.len(), 1);
    assert_unapplied_top_top(&seed.entries()[0].expansion);
}

#[test]
fn test_harvest_does_not_swallow_the_next_top_level_declaration() {
    let source = "notation \"⊤\" => Top.top\ndef after : Nat := 0\n";
    let seed = harvest(source);
    assert_eq!(seed.len(), 1);
    // The expansion must be `Top.top` alone — not `Top.top` applied to
    // whatever followed on the next line.
    assert_unapplied_top_top(&seed.entries()[0].expansion);
}

#[test]
fn test_seeded_parse_accepts_a_symbol_the_file_never_declares() {
    // The whole point: the importing file declares nothing.
    let seed = harvest("notation \"∞\" => Nat\n");
    let user = "def p : Type := ∞\n";
    assert_eq!(
        seeded_rawdecls(&NotationSeed::new(), user),
        1,
        "control: without the seed the symbol is unknown and the decl is recovered"
    );
    assert_eq!(
        seeded_rawdecls(&seed, user),
        0,
        "with the seed the declaration must parse"
    );
}

#[test]
fn test_seeded_infix_parses_at_its_declared_precedence() {
    // Level 25 is the Mathlib hom-arrow band that queue-B rank 4 opened; the
    // symbol is the one that brick probed with, so this test cannot fail for
    // the unrelated reason of a symbol the lexer already owns.
    let seed = harvest("infixr:25 \" ~~> \" => Prod\n");
    let user = "def q (A B : Type) : Type := A ~~> B\n";
    assert_eq!(seeded_rawdecls(&NotationSeed::new(), user), 1, "control");
    assert_eq!(seeded_rawdecls(&seed, user), 0);
}

#[test]
fn test_seeded_scoped_notation_is_inert_until_its_namespace_opens() {
    let seed = harvest("namespace Fin\nscoped notation \"∞\" => Nat\nend Fin\n");
    let closed = "def a : Type := ∞\n";
    let opened = "open Fin\ndef a : Type := ∞\n";
    assert_eq!(
        seeded_rawdecls(&seed, closed),
        1,
        "a scoped notation must stay inert outside its namespace"
    );
    assert_eq!(
        seeded_rawdecls(&seed, opened),
        0,
        "`open Fin` must activate the seeded scoped notation"
    );
}

#[test]
fn test_empty_seed_changes_nothing() {
    let source = "def d : Nat := 1\n";
    assert_eq!(seeded_rawdecls(&NotationSeed::new(), source), 0);
}

#[test]
fn test_scan_imports_skips_the_copyright_block_and_stops_at_the_first_command() {
    let source = concat!(
        "/-\nCopyright (c) 2026. All rights reserved.\nimport NotReally.AComment\n-/\n",
        "import Mathlib.Init\n",
        "import Mathlib.Order.Defs\n",
        "\n",
        "namespace Foo\n",
        "import TooLate.ToCount\n",
    );
    assert_eq!(
        super::scan_imports(source),
        vec!["Mathlib.Init".to_owned(), "Mathlib.Order.Defs".to_owned()],
    );
}

#[test]
fn test_scan_imports_accepts_prelude_and_rejects_junk() {
    assert_eq!(
        super::scan_imports("prelude\nimport Init.Core\ndef d := 1\n"),
        vec!["Init.Core".to_owned()]
    );
    assert!(super::scan_imports("import \n").is_empty());
}

/// The pinned Mathlib checkout is module-system source: 24,640 of its 25,590
/// import commands are `public import`. A scanner that knew only the bare
/// spelling read zero imports from every Mathlib file.
#[test]
fn test_scan_imports_reads_the_module_system_header() {
    let source = concat!(
        "/-\nCopyright (c) 2018. All rights reserved.\n-/\n",
        "module\n",
        "\n",
        "public import Mathlib.Analysis.Normed.Group.Defs\n",
        "public meta import Mathlib.Tactic.Positivity\n",
        "import all Mathlib.Data.NNReal.Basic\n",
        "\n",
        "namespace Norm\n",
    );
    assert_eq!(
        super::scan_imports(source),
        vec![
            "Mathlib.Analysis.Normed.Group.Defs".to_owned(),
            "Mathlib.Tactic.Positivity".to_owned(),
            "Mathlib.Data.NNReal.Basic".to_owned(),
        ],
    );
}

#[test]
fn test_harvest_multiple_commands_in_one_module() {
    let source = concat!(
        "namespace Norm\n",
        "notation:max \"‖\" e \"‖\" => norm e\n",
        "scoped notation:max \"‖\" e \"‖₊\" => nnnorm e\n",
        "local notation \"secret\" => hidden\n",
        "end Norm\n",
    );
    let seed = harvest(source);
    assert_eq!(
        seed.len(),
        2,
        "two exportable commands; the `local` one is dropped"
    );
    assert!(seed.entries()[0].scope_ns.is_none());
    assert_eq!(seed.entries()[1].scope_ns.as_deref(), Some("Norm"));
}
