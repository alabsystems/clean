// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module-system parser brick — end-to-end parse tests.
//!
//! Lean 4's module system (`src/Lean/Parser/Module.lean`, `Command.lean`) lets a
//! file begin with a `module` header, tag its header imports (`public import`
//! / `meta import` / `import all`, the first two and the last only in a
//! `module`), and wrap declarations in `public section` / `@[expose] public
//! section` or prefix them with `public` / `private` / `protected`. These
//! modifiers govern export/module semantics only — they are **transparent to
//! type-checking**, so for `clean check` (parse → elaborate → kernel-verify)
//! each construct Lean takes is accepted and the underlying import / section /
//! declaration is processed exactly as its bare form.
//!
//! Before this brick, Clean's lexer did not know `public` / `module`; it lexed
//! them as identifiers, so `public import X`, a leading `module`, and
//! `public section` all fell into declaration-error recovery (`RawDecl`
//! placeholders). These tests pin that the module system now parses to the
//! right trees, with visibility recorded and otherwise transparent, and that
//! every spelling pinned Lean refuses is refused with Lean's message (plan
//! item `formats-module-spelling-refusals`; the verdict tables are replayed in
//! `module_system_b_e2e_support/verdict_tables.rs`).

use clean_parser::{parse_file, SurfaceDecl, SurfaceExpr, Visibility};

#[path = "module_system_b_e2e_support/verdict_tables.rs"]
mod verdict_tables;

/// Non-recovery decls only (drops `RawDecl` recovery placeholders).
fn real_decls(src: &str) -> Vec<SurfaceDecl> {
    parse_file(src)
        .expect("file parses")
        .into_iter()
        .filter(|d| !matches!(d, SurfaceDecl::RawDecl { .. }))
        .collect()
}

/// Assert the file parses with NO recovery placeholders at the top level.
fn assert_no_raw(src: &str) -> Vec<SurfaceDecl> {
    let decls = parse_file(src).expect("file parses");
    let raw = decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::RawDecl { .. }))
        .count();
    assert_eq!(
        raw, 0,
        "expected no RawDecl recovery placeholders, got {raw} in {decls:#?}"
    );
    decls
}

// --------------------------------------------------------------------------
// Header imports (plan item `formats-module-spelling-refusals`). Pinned Lean
// v4.30.0-rc2 and v4.33.1 refuse a `public`, `meta` or `all` import in a file
// with no `module` header (`Lean.Parser.parseHeader`), and `private import`
// anywhere (`private` is a declaration modifier, so the header ends there).
// Each message is Lean's own line, `lean <file>` minus the file name
// (`tests/fixtures/module_spellings/verdicts.tsv`).
// --------------------------------------------------------------------------

/// The refusal `parse_file` returns, printed as `lean` prints it after the
/// file name.
fn lean_refusal(src: &str) -> String {
    parse_file(src)
        .expect_err("pinned Lean refuses this file")
        .to_string()
}

#[test]
fn test_public_import_without_module_is_refused() {
    assert_eq!(
        lean_refusal("public import Mathlib.Logic.Basic"),
        "1:0: error: cannot use `public import` without `module`"
    );
}

#[test]
fn test_private_import_is_refused_with_and_without_module() {
    let expected = "error: unexpected token 'import'; expected 'abbrev', 'axiom', \
        'builtin_initialize', 'class', 'coinductive', 'def', 'example', 'inductive', \
        'initialize', 'instance', 'opaque', 'structure', 'syntax' or 'theorem'";
    assert_eq!(
        lean_refusal("private import Batteries.Logic"),
        format!("1:7: {expected}")
    );
    assert_eq!(
        lean_refusal("module\n\nprivate import Batteries.Logic"),
        format!("3:7: {expected}")
    );
}

#[test]
fn test_import_all_without_module_is_refused() {
    assert_eq!(
        lean_refusal("import all Mathlib.Tactic.Basic"),
        "1:7: error: cannot use `import all` without `module`"
    );
}

#[test]
fn test_meta_import_without_module_is_refused() {
    assert_eq!(
        lean_refusal("meta import Lean.Elab.Command"),
        "1:0: error: cannot use `meta import` without `module`"
    );
}

#[test]
fn test_public_import_all_in_a_module_is_refused() {
    assert_eq!(
        lean_refusal("module\n\npublic import all Lean.Elab.Command"),
        "3:14: error: cannot use `all` with `public import`; consider using separate \
         `public import Lean.Elab.Command` and `import all Lean.Elab.Command` directives \
         in order to import public data into the public scope and private data into the \
         private scope."
    );
}

// --------------------------------------------------------------------------
// A doc comment ends the header. Pinned Lean's whitespace skips `--` and
// `/- … -/` but not `/-- … -/` (a declaration doc comment, the first slot of
// `declModifiers`) or `/-! … -/` (a module doc, a command of its own), so the
// header ends at either one: an import after it is past the header, and a
// `module` after it is an identifier in command position. Clean's lexer skips
// both as trivia, so it read through them (measured on v4.30.0-rc2 and
// v4.33.1, 2026-10-26; the `…_mod`/`…_nomod` rows of `verdicts.tsv` whose
// spelling names a doc comment).
// --------------------------------------------------------------------------

/// Lean's list after a lone `public` in command position.
const AFTER_PUBLIC: &str = "'abbrev', 'axiom', 'builtin_initialize', 'class', 'coinductive', \
    'def', 'example', 'inductive', 'initialize', 'instance', 'opaque', 'section', 'structure', \
    'syntax' or 'theorem'";

/// Lean's list after a lone declaration doc comment in command position: every
/// command parser that starts with an optional (or, for `add_decl_doc`, a
/// mandatory) doc comment.
const AFTER_DOC: &str = "'#guard_msgs', 'abbrev', 'add_decl_doc', 'axiom', 'binder_predicate', \
    'builtin_cbv_simproc', 'builtin_cbv_simproc_decl', 'builtin_dsimproc', \
    'builtin_dsimproc_decl', 'builtin_grind_propagator', 'builtin_initialize', \
    'builtin_simproc', 'builtin_simproc_decl', 'cbv_simproc', 'cbv_simproc_decl', 'class', \
    'coinductive', 'declare_simp_like_tactic', 'declare_syntax_cat', 'def', 'dsimproc', \
    'dsimproc_decl', 'elab', 'elab_rules', 'example', 'grind_propagator', 'inductive', 'infix', \
    'infixl', 'infixr', 'initialize', 'instance', 'macro', 'macro_rules', 'notation', 'opaque', \
    'postfix', 'prefix', 'recommended_spelling', 'register_error_explanation', \
    'register_tactic_tag', 'register_try?_tactic', 'simproc', 'simproc_decl', 'structure', \
    'syntax', 'tactic_extension', 'theorem' or 'unif_hint'";

#[test]
fn test_a_module_doc_ends_the_header() {
    // An import after the module doc is past the header: `public` is a
    // declaration modifier there, which `import` does not follow.
    assert_eq!(
        lean_refusal("module\n\n/-! doc -/\n\npublic import Init\n\ndef x : Nat := 1\n"),
        format!("5:6: error: unexpected token 'import'; expected {AFTER_PUBLIC}")
    );
    assert_eq!(
        lean_refusal("module\n\npublic import Init\n/-! doc -/\nmeta import Init\n"),
        "5:4: error: unexpected token 'import'; expected 'abbrev', 'axiom', \
         'builtin_initialize', 'class', 'coinductive', 'def', 'example', 'inductive', \
         'initialize', 'instance', 'opaque', 'section', 'structure' or 'theorem'"
    );
    // `module` is the header keyword only as the file's first token.
    assert_eq!(
        lean_refusal("/-! doc -/\nmodule\n\npublic import Init\n"),
        "2:0: error: unexpected identifier; expected command"
    );
}

#[test]
fn test_a_declaration_doc_comment_ends_the_header() {
    // The doc comment opens a command: `public` is its visibility, so
    // `sectionHeader` (which takes no doc comment) is not among the readers.
    assert_eq!(
        lean_refusal("module\n\n/-- d -/\npublic import Init\n"),
        "4:6: error: unexpected token 'import'; expected 'abbrev', 'axiom', \
         'builtin_initialize', 'class', 'coinductive', 'def', 'example', 'inductive', \
         'initialize', 'instance', 'opaque', 'structure', 'syntax' or 'theorem'"
    );
    // Lean reports at the end of the doc comment, the token before the stop.
    assert_eq!(
        lean_refusal("module\n\n/-- d -/\nimport Init\n"),
        format!("3:8: error: unexpected token 'import'; expected {AFTER_DOC}")
    );
    assert_eq!(
        lean_refusal("/-- d -/\nimport Init\n"),
        format!("1:8: error: unexpected token 'import'; expected {AFTER_DOC}")
    );
    assert_eq!(
        lean_refusal("/-- d -/\nmodule\n\npublic import Init\n"),
        format!("1:8: error: unexpected identifier; expected {AFTER_DOC}")
    );
}

/// `sectionHeader` takes no doc comment, and v4.30.0-rc2's `variable` no
/// modifier at all, so a doc comment in front of either is refused
/// (`modifier_matrix.tsv` rows with a `/-- d -/` prefix).
#[test]
fn test_a_doc_comment_before_section_or_variable_is_refused() {
    for (command, body) in [
        ("section", "section\nend"),
        ("variable", "variable (n : Nat)"),
    ] {
        assert_eq!(
            lean_refusal(&format!("def y : Nat := 1\n/-- doc -/ {body}\n")),
            format!("2:10: error: unexpected token '{command}'; expected {AFTER_DOC}")
        );
    }
}

/// Lean's list after `meta` (or `public meta`) in command position: the
/// declarations and `section`, no `syntax`.
const AFTER_META: &str = "'abbrev', 'axiom', 'builtin_initialize', 'class', 'coinductive', \
    'def', 'example', 'inductive', 'initialize', 'instance', 'opaque', 'section', 'structure' \
    or 'theorem'";

/// Lean's list after `private` in command position.
const AFTER_PRIVATE: &str = "'abbrev', 'axiom', 'builtin_initialize', 'class', 'coinductive', \
    'def', 'example', 'inductive', 'initialize', 'instance', 'opaque', 'structure', 'syntax' or \
    'theorem'";

// The tests of a doc comment inside a header import and of `all` as a header
// token (the second review of R154) are in
// `module_system_b_e2e_support/header_tokens.rs`; the two lists above are
// theirs, and `AFTER_PRIVATE` is used below too.
#[path = "module_system_b_e2e_support/header_tokens.rs"]
mod header_tokens;

// --------------------------------------------------------------------------
// A refusal inside a `namespace`/`section` body reaches every entry point
// (second review of R154). The block that meets it latches it and stops, and
// only `parse_file` used to drain the latch: `parse_decl` and its tactic-aware
// forms returned the block, the refused command and the rest dropped. Pinned
// v4.30.0-rc2 refuses both sources with this first message (2026-10-28).
// --------------------------------------------------------------------------

#[test]
fn test_parse_decl_refusal_inside_a_block_is_returned() {
    let expected = format!("2:7: error: unexpected token 'section'; expected {AFTER_PRIVATE}");
    let patterns = clean_parser::TacticPatterns::default();
    for src in [
        "section\nprivate section\nend",
        "namespace Foo\nprivate section\nend Foo",
    ] {
        for (entry, result) in [
            ("parse_decl", clean_parser::parse_decl(src)),
            ("parse_decl_exact", clean_parser::parse_decl_exact(src)),
            (
                "parse_decl_with_tactics",
                clean_parser::parse_decl_with_tactics(src, &patterns),
            ),
            (
                "parse_decl_with_tactics_exact",
                clean_parser::parse_decl_with_tactics_exact(src, &patterns),
            ),
        ] {
            match result {
                Err(err) => assert_eq!(err.to_string(), expected, "{entry} {src:?}"),
                Ok(decl) => panic!("{entry} {src:?}: pinned Lean refuses this, got {decl:#?}"),
            }
        }
    }
}

/// Known divergence, OPEN — ACCEPTED, LEAN REFUSES: a declaration doc comment
/// is a prefix word only in front of `import`, `section`, `variable` and a
/// misplaced `module`. Anywhere else Lean's grammar takes none, Clean still
/// skips it as trivia. Pinned v4.30.0-rc2 and v4.33.1 refuse `/-- d -/ open
/// Nat` with `1:8: error: unexpected token 'open'; expected '#guard_msgs', …`
/// (v4.30.0-rc2 likewise `/-- d -/ #check 1`) and `private /-- d -/ def x :
/// Nat := 1` with `1:7: error: unexpected token '/--'; expected 'abbrev', …`
/// (measured 2026-10-26). This fails the day the parser refuses them: assert
/// Lean's messages then.
#[test]
fn test_doc_comment_where_lean_takes_none_is_skipped_known_divergence() {
    let decls = assert_no_raw("/-- d -/ open Nat\n");
    assert!(
        matches!(decls.as_slice(), [SurfaceDecl::Open { .. }]),
        "{decls:#?}"
    );
    let decls = assert_no_raw("private /-- d -/ def x : Nat := 1\n");
    assert!(
        matches!(decls.as_slice(), [SurfaceDecl::Def { .. }]),
        "{decls:#?}"
    );
}

/// The controls: a module doc after the imports (every Mathlib file's shape),
/// and `--` and `/- … -/` comments anywhere in the header, which are
/// whitespace to Lean.
#[test]
fn test_comments_that_are_whitespace_keep_the_header() {
    for src in [
        "module\n\npublic import Init\n\n/-! doc -/\n\ndef x : Nat := 1\n",
        "/- c -/\nmodule\n/- c -/\npublic import Init\n-- c\nmeta import Init\n\ndef x : Nat := 1\n",
        "module\n\npublic import Init\n\n/-- d -/\npublic def x : Nat := 1\n",
    ] {
        let decls = assert_no_raw(src);
        assert!(
            matches!(decls.last(), Some(SurfaceDecl::Def { .. })),
            "{src}: {decls:#?}"
        );
    }
}

/// A doc comment that the command before it takes as its last argument does
/// not start the next command: Batteries' `library_note <title> docComment`
/// (and the deprecated `library_note2`) and Mathlib's `#adaptation_note
/// (docComment)?`. Pinned Mathlib `43ad0e9d2`, whose `lean-toolchain` is the
/// pin (v4.30.0-rc2), has each in front of a `variable`
/// (`Mathlib/Algebra/Group/Hom/Defs.lean:200`,
/// `Mathlib/RepresentationTheory/Coinduced.lean:291`). Neither command exists
/// in an `Init`-only file, so these are not `verdicts.tsv` rows.
#[test]
fn test_a_doc_comment_the_command_before_takes_is_no_prefix() {
    for src in [
        "library_note «hom simp lemma priority»\n/--\nnote\n-/\n\nvariable (n : Nat)\n",
        "library_note \"old title\" /-- note -/\nsection\nend\n",
        "library_note2 «t» /-- note -/\nvariable (n : Nat)\n",
        "#adaptation_note /-- After lean4#12179 the linter complains. -/\nvariable (n : Nat)\n",
        // A module doc after the argument is a command of its own.
        "library_note «t» /-- a -/ /-! b -/ variable (n : Nat)\n",
    ] {
        let decls = parse_file(src).expect("Mathlib's toolchain takes this file");
        assert_eq!(decls.len(), 2, "{src}: {decls:#?}");
        assert!(
            matches!(
                decls.last(),
                Some(SurfaceDecl::Variable { .. } | SurfaceDecl::Section { .. })
            ),
            "{src}: {decls:#?}"
        );
    }
    // Behind any other command the doc comment opens the next one (matrix
    // row m132, with a line break before `variable`).
    assert_eq!(
        lean_refusal("def y : Nat := 1\n/-- d -/\nvariable (n : Nat)\n"),
        format!("2:8: error: unexpected token 'variable'; expected {AFTER_DOC}")
    );
    // The command before takes ONE: a second doc comment opens the next
    // command. Clean took neither and accepted the file. Measured on pinned
    // v4.30.0-rc2 (2026-10-28) with the command declared two lines above by
    // `import Lean` / `elab "library_note " _t:ident ppSpace _d:docComment :
    // command => pure ()`: `3:34: error: unexpected token 'variable'; expected
    // '#guard_msgs', …`, a longer list for the commands `Lean` adds, and the
    // file with `/-! b -/` for the second exits 0 (the control above).
    assert_eq!(
        lean_refusal("library_note «t» /-- a -/ /-- b -/ variable (n : Nat)\n"),
        format!("1:34: error: unexpected token 'variable'; expected {AFTER_DOC}")
    );
}

#[test]
fn test_module_header_imports_are_accepted() {
    // The negative controls: every header spelling Lean takes in a module.
    for src in [
        "module\npublic import Mathlib.Logic.Basic",
        "module\nimport all Mathlib.Tactic.Basic",
        "module\nmeta import Lean.Elab.Command",
        "module\npublic meta import Lean.Elab.Command",
    ] {
        let decls = assert_no_raw(src);
        match decls.as_slice() {
            [SurfaceDecl::Import { paths, .. }] => assert_eq!(paths.len(), 1, "{src}"),
            other => panic!("{src}: expected one Import, got {other:?}"),
        }
    }
}

// --------------------------------------------------------------------------
// `private section` and `public`/`private variable`. Lean's `sectionHeader`
// is `@[expose]? public? noncomputable? meta? section`, and v4.30.0-rc2's
// `variable` takes no modifier at all (`optional visibility` arrives in
// v4.36.0-rc1, lean4#15518).
// --------------------------------------------------------------------------

#[test]
fn test_private_section_is_refused_with_and_without_module() {
    let expected = "error: unexpected token 'section'; expected 'abbrev', 'axiom', \
        'builtin_initialize', 'class', 'coinductive', 'def', 'example', 'inductive', \
        'initialize', 'instance', 'opaque', 'structure', 'syntax' or 'theorem'";
    let body = "private section\ntheorem t : True := trivial\nend";
    assert_eq!(lean_refusal(body), format!("1:7: {expected}"));
    assert_eq!(
        lean_refusal(&format!("module\n\n{body}")),
        format!("3:7: {expected}")
    );
}

#[test]
fn test_public_and_private_variable_are_refused_with_and_without_module() {
    let public = "error: unexpected token 'variable'; expected 'abbrev', 'axiom', \
        'builtin_initialize', 'class', 'coinductive', 'def', 'example', 'inductive', \
        'initialize', 'instance', 'opaque', 'section', 'structure', 'syntax' or 'theorem'";
    let private = "error: unexpected token 'variable'; expected 'abbrev', 'axiom', \
        'builtin_initialize', 'class', 'coinductive', 'def', 'example', 'inductive', \
        'initialize', 'instance', 'opaque', 'structure', 'syntax' or 'theorem'";
    for (header, line) in [("", 1), ("module\n\n", 3)] {
        assert_eq!(
            lean_refusal(&format!(
                "{header}public variable (n : Nat)\ndef x : Nat := n"
            )),
            format!("{line}:6: {public}")
        );
        assert_eq!(
            lean_refusal(&format!(
                "{header}private variable (n : Nat)\ndef x : Nat := n"
            )),
            format!("{line}:7: {private}")
        );
    }
}

#[test]
fn test_meta_def_without_module_is_accepted() {
    let decls = assert_no_raw("meta def x : Nat := 1");
    assert!(
        matches!(decls.as_slice(), [SurfaceDecl::Def { .. }]),
        "{decls:#?}"
    );
}

// --------------------------------------------------------------------------
// `meta` is a token. Pinned v4.30.0-rc2 and v4.33.1 refuse `def meta : Nat :=
// 1` ("unexpected token 'meta'; expected identifier"), and they end a term
// before a line-start `meta`: `def y : Nat := 1` followed by `meta def z : Nat
// := 2` evaluates `y` to 1 and `z` to 2 (measured 2026-10-25). Clean read the
// application `1 meta`, so `y` failed, and the `meta` rows of
// `modifier_matrix.tsv`, each after a `def y : Nat := 1` line, never reached a
// command.
// --------------------------------------------------------------------------

/// The value of the `Def` named `name` in `decls`.
fn def_value<'a>(decls: &'a [SurfaceDecl], name: &str) -> &'a SurfaceExpr {
    decls
        .iter()
        .find_map(|decl| match decl {
            SurfaceDecl::Def { name: n, val, .. } if n.to_string() == name => Some(val),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no `def {name}` in {decls:#?}"))
}

#[test]
fn test_meta_at_a_line_start_ends_the_term_before_it() {
    let decls = assert_no_raw("def y : Nat := 1\nmeta def z : Nat := 2\n");
    assert_eq!(decls.len(), 2, "{decls:#?}");
    assert!(
        matches!(def_value(&decls, "y"), SurfaceExpr::Lit(..)),
        "`y`'s value took the next line's `meta`: {decls:#?}"
    );
    assert!(
        matches!(def_value(&decls, "z"), SurfaceExpr::Lit(..)),
        "{decls:#?}"
    );
}

/// The last equation of an equation-form declaration ends there too, as at a
/// declaration keyword (`Mathlib/Tactic/NormNum/Result.lean`'s `IsRat.den_nz`
/// is followed by `meta section`), and so it does at a line-start `local`.
#[test]
fn test_meta_or_local_at_a_line_start_ends_the_last_equation() {
    for next in ["meta def z : Nat := 2", "local notation \"τ\" => t"] {
        let src = format!("def t : Nat → Nat\n  | 0 => 0\n  | n + 1 => n\n{next}\n");
        let decls = assert_no_raw(&src);
        assert_eq!(decls.len(), 2, "{src}: {decls:#?}");
        // `fun x => match x with | 0 => 0 | n + 1 => n`: the last arm's body
        // is the variable `n` alone, not an application of it.
        let SurfaceExpr::PatternMatchLambda(_, _, matched) = def_value(&decls, "t") else {
            panic!("{src}: `t` is not an equation-form value: {decls:#?}");
        };
        let SurfaceExpr::Match(_, _, _, arms) = matched.as_ref() else {
            panic!("{src}: `t`'s equations are not a match: {decls:#?}");
        };
        assert_eq!(arms.len(), 2, "{src}: {decls:#?}");
        match arms.last().map(|arm| &arm.body) {
            Some(SurfaceExpr::Ident(_, name)) => assert_eq!(name.to_string(), "n", "{src}"),
            other => panic!("{src}: the last equation took the next line's word: {other:#?}"),
        }
    }
}

#[test]
fn test_meta_at_a_line_start_ends_an_attribute_target_list() {
    // `Mathlib/Tactic/Bound.lean`'s shape: the targets end at the line break.
    let decls = assert_no_raw("attribute [simp] foo\nmeta def z : Nat := 2\n");
    match decls.as_slice() {
        [SurfaceDecl::Attribute { names, .. }, SurfaceDecl::Def { .. }] => {
            let names: Vec<String> = names.iter().map(ToString::to_string).collect();
            assert_eq!(names, ["foo"]);
        }
        other => panic!("expected the attribute and `def z`, got {other:#?}"),
    }
}

/// The control: an escaped `«meta»` is an identifier, and v4.30.0-rc2 takes a
/// line-start one as an argument (`def f (n : Nat) : Nat := n`, `def y : Nat
/// := f` then a `«meta»` line: `#eval y` prints 1, measured 2026-10-25).
#[test]
fn test_escaped_meta_at_a_line_start_is_still_an_argument() {
    let decls = assert_no_raw(
        "def «meta» : Nat := 1\ndef f (n : Nat) : Nat := n\ndef y : Nat := f\n«meta»\n",
    );
    assert_eq!(decls.len(), 3, "{decls:#?}");
    match def_value(&decls, "y") {
        SurfaceExpr::App(_, _, args) => assert_eq!(args.len(), 1, "{decls:#?}"),
        other => panic!("expected `f «meta»`, got {other:#?}"),
    }
}

/// Known divergence, OPEN — ACCEPTED, LEAN REFUSES (plan item
/// `formats-module-spelling-refusals` leaves it open): a bare `import` past
/// the header is still read as an import, and `clean check` imports it for
/// the whole file. Pinned v4.30.0-rc2 and v4.33.1 both refuse this file with
/// `2:0: error: invalid 'import' command, it must be used in the beginning of
/// the file` (measured 2026-10-25; it is also the second message of every
/// `… import` row of `modifier_matrix.tsv`). This fails the day the parser
/// refuses it: assert Lean's message then.
#[test]
fn test_bare_import_past_the_header_is_read_known_divergence() {
    let decls = assert_no_raw("def y : Nat := 1\nimport Init\n");
    assert!(
        matches!(
            decls.as_slice(),
            [SurfaceDecl::Def { .. }, SurfaceDecl::Import { .. }]
        ),
        "{decls:#?}"
    );
}

/// The same divergence after a module doc, which ends the header (above):
/// pinned v4.30.0-rc2 and v4.33.1 refuse `module` / `/-! doc -/` / `import
/// Init` with `3:0: error: invalid 'import' command, it must be used in the
/// beginning of the file` (measured 2026-10-26). The header Clean records has
/// no import; the declaration stream still carries it.
#[test]
fn test_bare_import_after_a_module_doc_is_read_known_divergence() {
    let report = clean_parser::parse_file_with_diagnostics("module\n/-! doc -/\nimport Init\n")
        .expect("Clean still reads the import");
    assert!(report.header.is_module, "{:?}", report.header);
    assert!(report.header.imports.is_empty(), "{:?}", report.header);
    assert!(
        matches!(report.decls.as_slice(), [SurfaceDecl::Import { .. }]),
        "{:#?}",
        report.decls
    );
}

#[test]
fn test_bare_import_still_parses() {
    // Regression guard: the plain form is unaffected.
    let decls = assert_no_raw("import Mathlib.Init");
    assert!(matches!(&decls[0], SurfaceDecl::Import { .. }));
}

#[test]
fn test_public_import_public_module_name_not_swallowed() {
    // A module literally named starting with `all` must not have its head
    // segment eaten: `import allFoo.Bar` is a single module path, since `all`
    // is only the modifier when a *separate* identifier follows it. Here there
    // is no space, so `allFoo` is one identifier.
    let decls = assert_no_raw("import allFoo.Bar");
    match &decls[0] {
        SurfaceDecl::Import { paths, .. } => {
            assert_eq!(
                paths,
                &vec![clean_parser::SurfaceName::generated_path("allFoo.Bar")]
            );
        }
        other => panic!("expected Import, got {other:?}"),
    }
}

// --------------------------------------------------------------------------
// Leading `module` header: recorded in the parse report's `FileHeader`
// (`module_file_header.rs`), never a node of the declaration stream.
// --------------------------------------------------------------------------

#[test]
fn test_leading_module_contributes_no_decl_node() {
    // `module` header followed by an import: only the import survives.
    let decls = assert_no_raw("module\nimport Mathlib.Init");
    assert_eq!(
        decls.len(),
        1,
        "module header should contribute no node: {decls:#?}"
    );
    assert!(matches!(&decls[0], SurfaceDecl::Import { .. }));
}

#[test]
fn test_module_then_public_import() {
    let decls = assert_no_raw("module\npublic import Mathlib.Init");
    assert_eq!(decls.len(), 1);
    assert!(matches!(&decls[0], SurfaceDecl::Import { .. }));
}

// --------------------------------------------------------------------------
// `public section` / `@[expose] public section`: ordinary section wrapper.
// --------------------------------------------------------------------------

#[test]
fn test_public_section_parses_as_section() {
    let decls = assert_no_raw("public section\ntheorem t : True := trivial\nend");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Section { decls, .. } => {
            assert_eq!(decls.len(), 1);
            assert!(matches!(&decls[0], SurfaceDecl::Theorem { .. }));
        }
        other => panic!("expected Section, got {other:?}"),
    }
}

#[test]
fn test_expose_public_section_parses_as_section() {
    let decls = assert_no_raw("@[expose] public section\ntheorem t : True := trivial\nend");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Section { decls, .. } => {
            assert_eq!(decls.len(), 1);
            assert!(matches!(&decls[0], SurfaceDecl::Theorem { .. }));
        }
        other => panic!("expected Section, got {other:?}"),
    }
}

// --------------------------------------------------------------------------
// `public` / `private` / `protected` declaration modifiers: decl parses
// normally, visibility recorded.
// --------------------------------------------------------------------------

#[test]
fn test_public_def_records_public_visibility() {
    let decls = real_decls("public def foo : Nat := 1");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Def {
            name, modifiers, ..
        } => {
            assert_eq!(
                name.name(),
                clean_parser::SurfaceName::generated_path("foo").name()
            );
            assert_eq!(modifiers.visibility, Visibility::Public);
        }
        other => panic!("expected Def, got {other:?}"),
    }
}

#[test]
fn test_private_theorem_records_private_visibility() {
    let decls = real_decls("private theorem bar : True := trivial");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Theorem {
            name, modifiers, ..
        } => {
            assert_eq!(
                name.name(),
                clean_parser::SurfaceName::generated_path("bar").name()
            );
            assert_eq!(modifiers.visibility, Visibility::Private);
        }
        other => panic!("expected Theorem, got {other:?}"),
    }
}

#[test]
fn test_protected_def_records_protected_visibility() {
    let decls = real_decls("protected def baz : Nat := 0");
    match &decls[0] {
        SurfaceDecl::Def { modifiers, .. } => {
            assert_eq!(modifiers.visibility, Visibility::Protected);
        }
        other => panic!("expected Def, got {other:?}"),
    }
}

#[test]
fn test_public_keyword_before_def_composes_with_other_modifiers() {
    // `public noncomputable def` — visibility + computability both recorded.
    let decls = real_decls("public noncomputable def q : Nat := 0");
    match &decls[0] {
        SurfaceDecl::Def { modifiers, .. } => {
            assert_eq!(modifiers.visibility, Visibility::Public);
            assert!(modifiers.is_noncomputable);
        }
        other => panic!("expected Def, got {other:?}"),
    }
}

// --------------------------------------------------------------------------
// Real-Mathlib-header snippet: the exact shape of Mathlib/Logic/Basic.lean's
// preamble parses to its declarations with zero recovery placeholders in the
// module-system header.
// --------------------------------------------------------------------------

#[test]
fn test_real_mathlib_header_snippet_parses() {
    let src = "\
module

public import Mathlib.Tactic.AdaptationNote
public import Batteries.Logic
public import Batteries.Util.LibraryNote

import Mathlib.Tactic.Attr.Register

@[expose] public section

theorem not_not_intro {a : Prop} (ha : a) : ¬¬a := fun h => h ha
";
    let decls = parse_file(src).expect("header snippet parses");

    // Four imports (three public, one bare), then a section wrapping the body.
    let imports = decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::Import { .. }))
        .count();
    assert_eq!(imports, 4, "expected 4 imports, got {decls:#?}");

    let section = decls
        .iter()
        .find_map(|d| match d {
            SurfaceDecl::Section { decls, .. } => Some(decls),
            _ => None,
        })
        .expect("a `public section` wrapping the body");
    assert!(
        section
            .iter()
            .any(|d| matches!(d, SurfaceDecl::Theorem { .. })),
        "section should contain the theorem: {section:#?}"
    );

    // The module-system header must produce NO recovery placeholders.
    let raw = decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::RawDecl { .. }))
        .count();
    assert_eq!(
        raw, 0,
        "module-system header must not error-recover: {decls:#?}"
    );
}

/// Parsing preserves an explicit prelude marker. The elaborator separately
/// requires a bare environment; parser acceptance alone does not supply Init.
#[test]
fn test_prelude_header_has_an_explicit_environment_marker() {
    let decls = parse_file("prelude\nimport Init.Prelude\n\ndef preludeHeaderProbe : Nat := 1\n")
        .expect("file parses");
    assert!(matches!(decls.first(), Some(SurfaceDecl::Prelude { .. })));
    assert!(!decls
        .iter()
        .any(|d| matches!(d, SurfaceDecl::RawDecl { .. })));
}
