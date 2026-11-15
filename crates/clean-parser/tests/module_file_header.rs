// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The file header `parse_file_with_diagnostics` records (plan item
//! `formats-module-spelling-refusals`): `module`, and each header import with
//! the flags pinned Lean v4.30.0-rc2's `HeaderSyntax.imports`
//! (`Lean/Elab/Import.lean`) gives it — `isExported := publicTk.isSome ||
//! moduleTk.isNone`, `isMeta := metaTk.isSome`, `importAll := allTk.isSome`.
//! Clean used to drop `module` and every import modifier, so a consumer could
//! not tell a module from a plain file, nor a `public import` from a private
//! one.

use clean_parser::{
    parse_file_with_diagnostics, FileHeader, ImportSpec, ParseError, SurfaceDecl, SurfaceName,
};

fn header(src: &str) -> FileHeader {
    parse_file_with_diagnostics(src)
        .expect("pinned Lean reads this header without an error")
        .header
}

/// `(module, is_exported, is_meta, import_all)` of each recorded import.
fn flags(imports: &[ImportSpec]) -> Vec<(String, bool, bool, bool)> {
    imports
        .iter()
        .map(|import| {
            (
                import.module.to_string(),
                import.is_exported,
                import.is_meta,
                import.import_all,
            )
        })
        .collect()
}

#[test]
fn test_header_of_a_module_records_each_import_kind() {
    let header = header(
        "module\n\npublic import A.B\nimport C\nmeta import D\npublic meta import E\n\
         import all F\n\ndef x : Nat := 1\n",
    );
    assert!(header.is_module);
    assert_eq!(
        flags(&header.imports),
        vec![
            ("A.B".to_owned(), true, false, false),
            ("C".to_owned(), false, false, false),
            ("D".to_owned(), false, true, false),
            ("E".to_owned(), true, true, false),
            ("F".to_owned(), false, false, true),
        ]
    );
}

#[test]
fn test_header_of_a_plain_file_exports_every_import() {
    let header = header("import A\nimport B.C\n\ntheorem t : True := trivial\n");
    assert!(!header.is_module);
    assert_eq!(
        flags(&header.imports),
        vec![
            ("A".to_owned(), true, false, false),
            ("B.C".to_owned(), true, false, false),
        ]
    );
}

#[test]
fn test_header_imports_stay_in_the_declaration_stream() {
    let report =
        parse_file_with_diagnostics("module\n\npublic import A\nimport B\n\ndef x : Nat := 1\n")
            .expect("parses");
    let imported: Vec<Vec<SurfaceName>> = report
        .decls
        .iter()
        .filter_map(|decl| match decl {
            SurfaceDecl::Import { paths, .. } => Some(paths.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(
        imported,
        vec![
            vec![SurfaceName::generated_path("A")],
            vec![SurfaceName::generated_path("B")],
        ]
    );
    assert_eq!(
        report.header.imports.len(),
        2,
        "{:?}",
        report.header.imports
    );
    assert!(
        matches!(report.decls.last(), Some(SurfaceDecl::Def { .. })),
        "{:#?}",
        report.decls
    );
}

#[test]
fn test_header_ends_at_the_first_command() {
    let report =
        parse_file_with_diagnostics("module\n\nimport A\n\ndef x : Nat := 1\n").expect("parses");
    assert_eq!(
        flags(&report.header.imports),
        vec![("A".to_owned(), false, false, false)]
    );
    // `module` is a keyword only as the file's first token.
    let later = header("def module : Nat := 1\n");
    assert!(!later.is_module);
    assert!(later.imports.is_empty());
}

/// `--` and `/- … -/` comments are whitespace to Lean and keep the header
/// going; a doc comment (`/-- … -/`, `/-! … -/`) ends it, so an import after
/// one is not a header import (`module_system_b_e2e.rs` has Lean's refusals).
#[test]
fn test_header_reads_through_plain_comments_and_stops_at_a_module_doc() {
    let through = header(
        "/- Copyright -/\nmodule\n/- c -/\npublic import A\n-- c\nmeta import B\n\n\
         /-! doc -/\n\ndef x : Nat := 1\n",
    );
    assert!(through.is_module);
    assert_eq!(
        flags(&through.imports),
        vec![
            ("A".to_owned(), true, false, false),
            ("B".to_owned(), false, true, false),
        ]
    );
    let report = parse_file_with_diagnostics("module\npublic import A\n/-! doc -/\nimport B\n")
        .expect("Clean still reads an import past the header (a known divergence)");
    assert_eq!(
        flags(&report.header.imports),
        vec![("A".to_owned(), true, false, false)]
    );
}

/// `all` is a token of the header's token table (`Module.updateTokens`), so
/// `import all` takes it as the modifier whether the module name is on its
/// line or the next; pinned v4.30.0-rc2 accepts both files (exit 0, measured
/// 2026-10-28). Clean took `all` as the modifier only before a same-line name,
/// so it recorded the module `all` and left `Init` an unknown command. A
/// dotted `all.Foo` stays one module name: Lean's identifier scan reads it
/// whole (pinned v4.30.0-rc2: "unknown module prefix 'all'", no parse error).
#[test]
fn test_header_import_all_across_a_line_break_records_import_all() {
    for src in [
        "module\nimport all\n  Init\n\ndef x : Nat := 1\n",
        "module\nimport\n  all\n  Init\n\ndef x : Nat := 1\n",
    ] {
        let report = parse_file_with_diagnostics(src).expect("pinned Lean accepts this file");
        assert_eq!(
            flags(&report.header.imports),
            vec![("Init".to_owned(), false, false, true)],
            "{src:?}"
        );
        assert!(
            matches!(
                report.decls.as_slice(),
                [SurfaceDecl::Import { .. }, SurfaceDecl::Def { .. }]
            ),
            "{src:?}: {:#?}",
            report.decls
        );
    }
    let dotted = parse_file_with_diagnostics("module\nimport all.Foo\n")
        .expect("Lean parses the header (its error is the missing module)");
    assert_eq!(
        flags(&dotted.header.imports),
        vec![("all.Foo".to_owned(), false, false, false)]
    );
}

/// A doc comment inside a header import is a token to Lean, so the file is
/// refused (`module_system_b_e2e.rs` has Lean's messages) and no header is
/// recorded; Clean used to read through it and record `Init`.
#[test]
fn test_header_with_a_doc_comment_inside_an_import_has_no_report() {
    for src in [
        "module\npublic /-- d -/ import Init\n\ndef x : Nat := 1\n",
        "module\nimport /-! d -/ Init\n",
        "module\nimport all /-- d -/ Init\n",
    ] {
        match parse_file_with_diagnostics(src) {
            Err(ParseError::ModuleSyntaxRefused { .. }) => {}
            other => panic!("{src:?}: pinned Lean refuses this file, got {other:?}"),
        }
    }
}

/// The explicit prelude marker covers only its header token: the `meta`
/// of a following `meta import` stays the import's
/// (`module`/`prelude`/`meta import Lean` is clean-olean's
/// `import_flags/FlagMeta.lean`).
#[test]
fn test_prelude_marker_leaves_the_imports_after_it_in_the_header() {
    let report =
        parse_file_with_diagnostics("module\nprelude\nmeta import Lean\n").expect("parses");
    assert!(report.header.is_module);
    assert!(report.header.is_prelude);
    assert_eq!(
        flags(&report.header.imports),
        vec![("Lean".to_owned(), false, true, false)]
    );
    match report.decls.as_slice() {
        [SurfaceDecl::Prelude { .. }, SurfaceDecl::Import { paths, .. }] => {
            assert_eq!(paths, &vec![SurfaceName::generated_path("Lean")]);
        }
        other => panic!("expected the prelude marker and one import, got {other:#?}"),
    }
}

#[test]
fn module_default_visibility_and_public_sections_restore() {
    use clean_parser::Visibility;
    fn collect(decls: &[SurfaceDecl], out: &mut Vec<(String, Visibility)>) {
        for decl in decls {
            match decl {
                SurfaceDecl::Axiom {
                    name, modifiers, ..
                } => out.push((name.to_string(), modifiers.visibility)),
                SurfaceDecl::Section { decls, .. } => collect(decls, out),
                _ => panic!("unexpected visibility fixture command"),
            }
        }
    }
    let parsed = parse_file_with_diagnostics("module\naxiom a : Nat\npublic section\naxiom b : Nat\nprivate axiom c : Nat\nsection\naxiom d : Nat\nend\nend\naxiom e : Nat\npublic axiom f : Nat").expect("visibility syntax");
    assert!(parsed.diagnostics.is_empty());
    let mut actual = Vec::new();
    collect(&parsed.decls, &mut actual);
    assert_eq!(
        actual,
        vec![
            ("a".into(), Visibility::Private),
            ("b".into(), Visibility::Public),
            ("c".into(), Visibility::Private),
            ("d".into(), Visibility::Public),
            ("e".into(), Visibility::Private),
            ("f".into(), Visibility::Public)
        ]
    );
    let legacy = parse_file_with_diagnostics("axiom a : Nat").expect("legacy syntax");
    let mut actual = Vec::new();
    collect(&legacy.decls, &mut actual);
    assert_eq!(actual, vec![("a".into(), Visibility::Public)]);
}
