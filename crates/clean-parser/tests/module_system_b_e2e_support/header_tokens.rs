// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Part of `module_system_b_e2e.rs`: a doc comment inside a header import, and
//! `all` as a header token (the second review of R154), moved here unchanged so
//! neither file passes 1,000 lines.

use super::*;

// --------------------------------------------------------------------------
// A doc comment INSIDE a header import (second review of R154). The header
// asks whether a doc comment ends before each token it takes, not only before
// an import's first: inside the `atomic(public? meta? "import ")` prefix the
// group fails at the doc comment and the header ends before `public`; after
// `import` or `all`, Lean's identifier parser meets it. Clean read through
// both and recorded the import. Every message below is pinned v4.30.0-rc2's
// first, `lean <file>` minus the file name (measured 2026-10-28).
// --------------------------------------------------------------------------

#[test]
fn test_header_doc_comment_inside_an_import_prefix_is_refused_at_it() {
    for (src, expected) in [
        (
            "module\npublic /-- d -/ import Init\n\ndef x : Nat := 1\n",
            format!("2:6: error: unexpected token '/--'; expected {AFTER_PUBLIC}"),
        ),
        // Without `module` the header ends before `public` too, so Lean's
        // first message is this one, not `1:0`'s "cannot use `public import`".
        (
            "public /-- d -/ import Init\n\ndef x : Nat := 1\n",
            format!("1:6: error: unexpected token '/--'; expected {AFTER_PUBLIC}"),
        ),
        (
            "module\npublic meta /-- d -/ import Init\n",
            format!("2:11: error: unexpected token '/--'; expected {AFTER_META}"),
        ),
        (
            "module\npublic /-- d -/ meta import Init\n",
            format!("2:6: error: unexpected token '/--'; expected {AFTER_PUBLIC}"),
        ),
        (
            "module\nmeta /-- d -/ import Init\n",
            format!("2:4: error: unexpected token '/--'; expected {AFTER_META}"),
        ),
        (
            "module\nmeta /-! d -/ import Init\n",
            format!("2:4: error: unexpected token '/-!'; expected {AFTER_META}"),
        ),
        (
            "module\npublic /-! d -/ import Init\n",
            format!("2:6: error: unexpected token '/-!'; expected {AFTER_PUBLIC}"),
        ),
        // After a header the doc comment ended, as anywhere past the header.
        (
            "module\nimport Init\npublic /-- d -/ import Init\n",
            format!("3:6: error: unexpected token '/--'; expected {AFTER_PUBLIC}"),
        ),
    ] {
        assert_eq!(lean_refusal(src), expected, "{src:?}");
    }
    // The header that did end before the doc comment is checked first:
    // Lean prints only `parseHeader`'s message here.
    assert_eq!(
        lean_refusal("public import Init\npublic /-- d -/ import Init\n"),
        "1:0: error: cannot use `public import` without `module`"
    );
}

#[test]
fn test_header_doc_comment_after_import_or_all_is_refused_at_it() {
    // (source, Lean's position, the doc comment's atom)
    for (src, at, token) in [
        ("module\nimport /-! d -/ Init\n", "2:6", "/-!"),
        ("module\nimport /-- d -/ Init\n", "2:6", "/--"),
        ("module\nimport /-- d -/ all Init\n", "2:6", "/--"),
        ("module\nimport /-! d -/ all Init\n", "2:6", "/-!"),
        ("module\nimport all /-- d -/ Init\n", "2:10", "/--"),
        ("module\nimport all /-! d -/ Init\n", "2:10", "/-!"),
        ("module\npublic import /-- d -/ Init\n", "2:13", "/--"),
        ("import /-- d -/ Init\n", "1:6", "/--"),
        ("import all /-- d -/ Init\n", "1:10", "/--"),
        // Lean logs the header's parse error before `parseHeader`'s messages
        // on the imports before it (`1:0` and `2:14` are its second ones).
        ("public import Init\nimport /-- d -/ Init\n", "2:6", "/--"),
        (
            "module\npublic import all Init\nimport /-! d -/ Init\n",
            "3:6",
            "/-!",
        ),
    ] {
        assert_eq!(
            lean_refusal(src),
            format!("{at}: error: unexpected token '{token}'; expected identifier"),
            "{src:?}"
        );
    }
}

/// Past the header the modifier model stops at a doc comment after its first
/// word the same way, wherever it stands in the prefix.
#[test]
fn test_doc_comment_inside_a_modifier_prefix_is_refused_at_it() {
    assert_eq!(
        lean_refusal("def y : Nat := 1\nprivate /-- d -/ section\nend\n"),
        format!("2:7: error: unexpected token '/--'; expected {AFTER_PRIVATE}")
    );
    assert_eq!(
        lean_refusal("def y : Nat := 1\n@[simp] /-- d -/ variable (n : Nat)\n"),
        "2:7: error: unexpected token '/--'; expected 'abbrev', 'axiom', 'binder_predicate', \
         'builtin_initialize', 'class', 'coinductive', 'def', 'elab', 'elab_rules', 'example', \
         'inductive', 'infix', 'infixl', 'infixr', 'initialize', 'instance', 'macro', \
         'macro_rules', 'notation', 'opaque', 'postfix', 'prefix', 'structure', 'syntax' or \
         'theorem'"
    );
}

/// Two doc comments in a row where no rule takes one: Lean stops at the
/// FIRST, so its atom is the one named, whichever kind comes second (review
/// of the R154 follow-up; pinned v4.30.0-rc2, 2026-10-28). Clean named the
/// closest. Before a command's first token Lean reads them in the same
/// order: `test_a_doc_comment_after_the_one_a_command_carries_is_refused_at_its_end`.
#[test]
fn test_two_doc_comments_in_a_row_are_refused_at_the_first() {
    for (src, expected) in [
        (
            "module\nimport /-- a -/ /-! b -/ Init\n",
            "2:6: error: unexpected token '/--'; expected identifier".to_owned(),
        ),
        (
            "module\nimport /-! a -/ /-- b -/ Init\n",
            "2:6: error: unexpected token '/-!'; expected identifier".to_owned(),
        ),
        (
            "module\nimport all /-! a -/ /-- b -/ Init\n",
            "2:10: error: unexpected token '/-!'; expected identifier".to_owned(),
        ),
        (
            "module\npublic /-- a -/ /-! b -/ import Init\n",
            format!("2:6: error: unexpected token '/--'; expected {AFTER_PUBLIC}"),
        ),
        (
            "module\npublic /-! a -/ /-- b -/ import Init\n",
            format!("2:6: error: unexpected token '/-!'; expected {AFTER_PUBLIC}"),
        ),
        (
            "def y : Nat := 1\nprivate /-- a -/ /-! b -/ section\nend\n",
            format!("2:7: error: unexpected token '/--'; expected {AFTER_PRIVATE}"),
        ),
        (
            "def y : Nat := 1\nprivate /-! a -/ /-- b -/ section\nend\n",
            format!("2:7: error: unexpected token '/-!'; expected {AFTER_PRIVATE}"),
        ),
    ] {
        assert_eq!(lean_refusal(src), expected, "{src:?}");
    }
}

/// The doc comments before a command's first token, read in source order as
/// Lean reads them (second review of the R154 follow-up). A module doc is a
/// command of its own; a declaration doc comment opens a command, and no rule
/// continues one with a doc comment, so when another follows it Lean stops at
/// the end of the first and names the second, after the list a lone doc
/// comment allows. Clean took the closest: the second, or nothing when it was
/// a module doc, so it printed the message Lean logs after this one (`1:18`,
/// `1:17`, `2:25`, `2:24`, `2:17`), as if it were the first, or accepted the
/// file. Every expectation is pinned v4.30.0-rc2's first message (measured
/// 2026-10-28).
#[test]
fn test_a_doc_comment_after_the_one_a_command_carries_is_refused_at_its_end() {
    // (source, the position, the second doc comment's atom)
    for (src, at, token) in [
        ("/-- a -/ /-! b -/ module\n", "1:8", "/-!"),
        ("/-- a -/ /-- b -/ module\n", "1:8", "/--"),
        (
            "def y : Nat := 1\n/-- a -/ /-! b -/ private section\nend\n",
            "2:8",
            "/-!",
        ),
        (
            "module\n/-- a -/ /-! b -/ public import Init\n",
            "2:8",
            "/-!",
        ),
        // Clean accepted these: the module doc was closest, and a bare
        // `section` or `import` has no prefix.
        (
            "def y : Nat := 1\n/-- a -/ /-! b -/ section\nend\n",
            "2:8",
            "/-!",
        ),
        (
            "def y : Nat := 1\n/-- a -/\n/-! b -/\nsection\nend\n",
            "2:8",
            "/-!",
        ),
        ("/-- a -/ /-! b -/ import Init\n", "1:8", "/-!"),
        (
            "def y : Nat := 1\n/-- a -/ /-- b -/ variable (n : Nat)\n",
            "2:8",
            "/--",
        ),
        // The module doc before the first is a command of its own.
        (
            "def y : Nat := 1\n/-! a -/ /-- b -/ /-! c -/ section\nend\n",
            "2:17",
            "/-!",
        ),
    ] {
        assert_eq!(
            lean_refusal(src),
            format!("{at}: error: unexpected token '{token}'; expected {AFTER_DOC}"),
            "{src:?}"
        );
    }
    // The controls: with no declaration doc comment before it, the closest
    // is the command's. After a module doc, the declaration doc comment opens
    // `section`, which takes none; after module docs alone, `module` is an
    // identifier where a command belongs.
    assert_eq!(
        lean_refusal("def y : Nat := 1\n/-! t -/\n/-- doc -/ section\nend\n"),
        format!("3:10: error: unexpected token 'section'; expected {AFTER_DOC}")
    );
    assert_eq!(
        lean_refusal("/-! a -/ /-! b -/ module\n"),
        "1:18: error: unexpected identifier; expected command"
    );
}

/// A doc comment after the
/// one a declaration carries (found by the second review of the R154
/// follow-up; already so on `origin/main`). Lean reads `/-- a -/` as the
/// declaration's doc comment and stops at the next token: pinned v4.30.0-rc2
/// refuses `/-- a -/ /-! b -/ def x : Nat := 1` with `1:8: error: unexpected
/// token '/-!'; expected '#guard_msgs', …` (the list after a lone doc
/// comment, `AFTER_DOC`) and nothing else, and the `/-- b -/` form with the
/// same message naming `'/--'` (measured 2026-10-28 and remeasured 2026-11-10).
/// The leading prefix check must run for ordinary declarations too.
#[test]
fn test_doc_comment_after_a_declarations_doc_comment_is_refused() {
    for (src, token) in [
        ("/-- a -/ /-! b -/ def x : Nat := 1\n", "/-!"),
        ("/-- a -/ /-- b -/ def x : Nat := 1\n", "/--"),
    ] {
        assert_eq!(
            lean_refusal(src),
            format!("1:8: error: unexpected token '{token}'; expected {AFTER_DOC}")
        );
        // Keep the original declaration-shape assertion as an ordinary
        // comment control. Doc-prefix refusal must not reject plain trivia.
        let plain_comments = src.replace("/--", "/- ").replace("/-!", "/- ");
        let decls = assert_no_raw(&plain_comments);
        assert!(
            matches!(decls.as_slice(), [SurfaceDecl::Def { .. }]),
            "{src:?}: {decls:#?}"
        );
    }
}

/// Measured independently with the pinned 4.30.0-rc2 executable. A module doc
/// is a complete command; a declaration doc opens a prefix which another doc
/// cannot continue. Refusal precedes attributes and uses codepoint columns.
#[test]
fn test_leading_stacked_declaration_docs_follow_pinned_first_error() {
    for (src, at, token) in [
        ("/-- a -/ /-- b -/ def x : Nat := 1\n", "1:8", "/--"),
        ("/-- a -/ /-! b -/ def x : Nat := 1\n", "1:8", "/-!"),
        (
            "/-! m -/\n/-- a -/ /-- b -/ def x : Nat := 1\n",
            "2:8",
            "/--",
        ),
        ("/-- αβ -/ /-- b -/ def x : Nat := 1\n", "1:9", "/--"),
        ("/-- a -/ /-- b -/ @[simp\ndef x : Nat := 1\n", "1:8", "/--"),
    ] {
        let expected = format!("{at}: error: unexpected token '{token}'; expected {AFTER_DOC}");
        assert_eq!(lean_refusal(src), expected, "{src:?}");
        assert_eq!(
            clean_parser::parse_decl(src)
                .expect_err("the deliberate prefix API still validates its leading command")
                .to_string(),
            expected,
            "{src:?}"
        );
        assert_eq!(
            clean_parser::parse_decl_exact(src)
                .expect_err("exact declarations share the leading-doc refusal")
                .to_string(),
            expected,
            "{src:?}"
        );
        assert_eq!(
            clean_parser::Parser::parse_file_with_docs(src)
                .expect_err("raw attachment policy must not accept invalid files")
                .to_string(),
            expected,
            "{src:?}"
        );
    }
    for src in [
        "/-- a -/ def x : Nat := 1\n",
        "/-! m -/ /-- a -/ def x : Nat := 1\n",
        "/-! a -/ /-! b -/ def x : Nat := 1\n",
    ] {
        let decls = assert_no_raw(src);
        assert!(
            matches!(decls.as_slice(), [SurfaceDecl::Def { .. }]),
            "{src:?}: {decls:#?}"
        );
    }
}

// --------------------------------------------------------------------------
// `all` is a token in the header (second review of R154): `Module.updateTokens`
// adds the header's `all` to the token table it is read with, so `import all`
// takes `all` whether the module name is on its line or the next. Clean took
// `all` as the modifier only when the name followed on the same line, and
// otherwise as the module name (measured on pinned v4.30.0-rc2, 2026-10-28).
// --------------------------------------------------------------------------

#[test]
fn test_header_import_all_across_a_line_break_is_refused_where_lean_refuses() {
    assert_eq!(
        lean_refusal("import all\n  Init\n\ndef x : Nat := 1\n"),
        "1:7: error: cannot use `import all` without `module`"
    );
    assert_eq!(
        lean_refusal("module\npublic import all\n  Init\n"),
        "2:14: error: cannot use `all` with `public import`; consider using separate \
         `public import Init` and `import all Init` directives in order to import public data \
         into the public scope and private data into the private scope."
    );
}

/// Known divergence, OPEN — REFUSED BY ANOTHER ROUTE: `import all` with no
/// module name after it. Pinned v4.30.0-rc2 refuses `module` / `import all` /
/// `def x : Nat := 1` with `2:10: error: unexpected token 'def'; expected
/// identifier` (and `module` / `import all` at end of file with `3:0: error:
/// unexpected end of input; expected identifier`). Clean takes the `all` and
/// the module name fails to parse, which recovers the import as a `RawDecl`
/// like any header import whose name does not parse; it used to read `all` as
/// the module and accept the file. This fails the day such a name failure is
/// refused in Lean's words: assert Lean's message then.
#[test]
fn test_header_import_all_with_no_module_name_is_recovered_known_divergence() {
    let report =
        clean_parser::parse_file_with_diagnostics("module\nimport all\n\ndef x : Nat := 1\n")
            .expect("Clean recovers the import");
    assert!(report.header.imports.is_empty(), "{:?}", report.header);
    assert!(
        matches!(
            report.decls.as_slice(),
            [SurfaceDecl::RawDecl { .. }, SurfaceDecl::Def { .. }]
        ),
        "{:#?}",
        report.decls
    );
}

/// Known divergence, OPEN — REFUSED BY ANOTHER ROUTE, and nothing after it
/// (review of the R154 follow-up). Lean's header parser stops at its first
/// error, and pinned v4.30.0-rc2 reads no command after a header error: its
/// whole output on each file below is the header's parse error (and, on the
/// last, the `parseHeader` message it logs after it). Clean recovers the
/// import as a `RawDecl`, ends the header there and refuses nothing after it,
/// so its first diagnostic is that recovery, on the line of Lean's first
/// message. It used to read on and return a later refusal as the file's first
/// message (`3:6`, the second import's doc comment, on the first file), or
/// the modifier refusal Lean logs second (`1:0` on the last). This fails the
/// day such a header is refused in Lean's words: assert Lean's first message
/// then.
#[test]
fn test_header_recovered_import_ends_the_header_and_refuses_nothing_after_it() {
    // (source, the header's imports before the recovered one, pinned
    // v4.30.0-rc2's whole output minus the file name; measured 2026-10-28)
    let cases: [(&str, &[&str], &str); 5] = [
        (
            "module\nimport all\nimport /-- d -/ Init\n",
            &[],
            "2:10: error: unexpected token 'import'; expected identifier",
        ),
        (
            "module\nimport all\npublic /-- d -/ import Init\n",
            &[],
            "2:10: error: unexpected token 'public'; expected identifier",
        ),
        (
            "module\nimport all\npublic import all Init\n",
            &[],
            "2:10: error: unexpected token 'public'; expected identifier",
        ),
        (
            "module\nimport all\nprivate section\nend\n",
            &[],
            "2:10: error: unexpected token 'private'; expected identifier",
        ),
        (
            "public import Init\nimport all\n\ndef x : Nat := 1\n",
            &["Init"],
            "2:10: error: unexpected token 'def'; expected identifier\n\
             1:0: error: cannot use `public import` without `module`",
        ),
    ];
    for (src, header, lean) in cases {
        let report = clean_parser::parse_file_with_diagnostics(src)
            .unwrap_or_else(|err| panic!("{src:?}: Lean's first message is {lean:?}, not {err}"));
        let modules: Vec<String> = report
            .header
            .imports
            .iter()
            .map(|import| import.module.to_string())
            .collect();
        assert_eq!(modules, header, "{src:?}");
        let first = report
            .diagnostics
            .first()
            .unwrap_or_else(|| panic!("{src:?}: no recovery diagnostic"));
        let line = src
            .get(..first.recovery_start.byte)
            .map(|before| before.matches('\n').count() + 1);
        let lean_line = lean
            .split(':')
            .next()
            .and_then(|at| at.parse::<usize>().ok());
        assert_eq!(line, lean_line, "{src:?}: {first:?}");
    }
}

/// A universe offset over Lean's maximum refuses the whole file too, with the
/// same exception (review of the R154 follow-up): after a recovered header
/// import `file()` recovers it as a `RawDecl`. Pinned v4.30.0-rc2's whole
/// output on the first source is `2:10: error: unexpected token 'def';
/// expected identifier`: it reads no command after the header error. On the
/// control, whose header parses, it is the offset error at `3:19` ("Universe
/// level offset `9999` exceeds maximum offset `32`") and a note (measured
/// 2026-10-28).
#[test]
fn test_header_recovered_import_recovers_a_universe_offset_error_after_it() {
    let def = "def big (X : Sort (u + 9999)) : Nat := 0\n";
    let decls = parse_file(&format!("module\nimport all\n{def}"))
        .unwrap_or_else(|err| panic!("Lean's first message is the header's, not {err}"));
    assert!(
        matches!(
            decls.as_slice(),
            [SurfaceDecl::RawDecl { .. }, SurfaceDecl::RawDecl { .. }]
        ),
        "{decls:#?}"
    );
    assert!(
        matches!(
            parse_file(&format!("module\nimport Init\n{def}")),
            Err(clean_parser::ParseError::UniverseOffsetTooLarge {
                offset: 9999,
                max: 32
            })
        ),
        "after a header that parses, the offset error refuses the file"
    );
}
