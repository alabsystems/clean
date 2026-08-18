// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Editor-path import loading (LSP brick 2 of the 2026-08-10 pillar audit).
//!
//! A real Lean file's `import` header must populate the document's elaboration
//! environment (prelude base + shared `.olean` closure, cached process-wide)
//! instead of elaborating against the near-empty server environment. On load
//! failure the document gets ONE "imports unavailable" diagnostic, not a flood
//! of per-declaration unknown-constant errors.
//!
//! The `.olean`-backed lane is gated on the pinned toolchain being installed
//! (skip-with-eprintln, mirroring
//! `crates/clean-elab/tests/instance_priority_import_probe.rs`); the failure
//! shaping and header-collection lanes run everywhere.

use super::{imports, CleanBackend};
use crate::document::Document;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use tower_lsp::lsp_types::Url;
use tower_lsp::LspService;

/// The pinned toolchain the shared `.olean` loader's default search paths
/// discover via elan. Mirrors `instance_priority_import_probe.rs`.
const PINNED_TOOLCHAIN: &str = "leanprover--lean4---v4.30.0-rc2";

fn v4_30_lib_path() -> Option<PathBuf> {
    let home = std::env::var("HOME").ok()?;
    let lib = PathBuf::from(home)
        .join(".elan/toolchains")
        .join(PINNED_TOOLCHAIN)
        .join("lib/lean");
    lib.join("Init.olean").is_file().then_some(lib)
}

async fn open_and_check(
    backend: &CleanBackend,
    uri: &Url,
    text: &str,
) -> crate::document::ElaboratedDocument {
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(uri).await;
    backend.elaborate_document(uri).await;
    let doc = backend
        .documents
        .get(uri)
        .expect("opened document should remain in the document map");
    doc.elaborated
        .clone()
        .expect("elaborate_document should record an elaborated state")
}

/// `import Init.Core` + a theorem whose proof is an Init.Core-only constant
/// (`not_not_intro` — absent from Clean's hand prelude) must elaborate with
/// ZERO diagnostics: the header resolves through the shared closure cache and
/// the imported constant is in scope. A second document with the same header
/// shares the cached closure and stays clean too.
#[tokio::test]
async fn test_import_init_core_theorem_using_imported_constant_yields_no_diagnostics() {
    let Some(_lib) = v4_30_lib_path() else {
        eprintln!("Skipping: {PINNED_TOOLCHAIN} not installed");
        return;
    };

    let text = "import Init.Core\n\ntheorem uses_imported (p : Prop) (h : p) : \
                Not (Not p) := not_not_intro h\n";

    // Precondition: the closure the editor path resolves for this header must
    // actually carry the imported constant, so the assertion below fails with
    // a precise cause when the loader (rather than the elaborator) regresses.
    let closure = imports::shared_import_closure(
        &[vec!["Init".to_string(), "Core".to_string()]],
        Some(Path::new("/lsp-import-init-core.lean")),
    )
    .expect("Init.Core closure should load from the pinned toolchain");
    assert!(
        closure
            .get_const(&clean_kernel::Name::from_string("not_not_intro"))
            .is_some(),
        "imported closure should contain the Init.Core constant not_not_intro",
    );

    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();

    let uri = Url::parse("file:///lsp-import-init-core.lean").expect("static URI should parse");
    let elaborated = open_and_check(backend, &uri, text).await;
    assert!(
        elaborated.errors.is_empty(),
        "import-backed file should produce zero unknown-constant diagnostics, got {:?}",
        elaborated.errors,
    );
    assert!(
        elaborated
            .declarations
            .iter()
            .any(|decl| decl.name.ends_with("uses_imported")),
        "theorem using the imported constant should elaborate to a declaration, got {:?}",
        elaborated.declarations,
    );

    // Second document, same header: shares the process-wide closure.
    let sibling_uri =
        Url::parse("file:///lsp-import-init-core-sibling.lean").expect("static URI should parse");
    let sibling = open_and_check(backend, &sibling_uri, text).await;
    assert!(
        sibling.errors.is_empty(),
        "sibling document sharing the header should also be diagnostic-free, got {:?}",
        sibling.errors,
    );
}

/// Control for the gated test above: WITHOUT the import line the same theorem
/// must fail (the constant only exists via the import), proving the gated
/// test's zero-diagnostic assertion is meaningful.
#[tokio::test]
async fn test_theorem_using_unimported_constant_reports_diagnostics() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///lsp-no-import-control.lean").expect("static URI should parse");
    let text = "theorem uses_imported (p : Prop) (h : p) : Not (Not p) := not_not_intro h\n";

    let elaborated = open_and_check(backend, &uri, text).await;
    assert!(
        !elaborated.errors.is_empty(),
        "without the import the Init.Core constant must be unknown",
    );
}

/// When the import closure cannot be loaded, the document gets exactly ONE
/// "imports unavailable: <reason>" diagnostic anchored at the import header —
/// and later declarations still elaborate against the base environment rather
/// than drowning in follow-on noise.
#[tokio::test]
async fn test_import_closure_failure_yields_single_imports_unavailable_diagnostic() {
    let uri_path = "/lsp-import-injected-failure.lean";
    let modules = vec![vec![
        "LspImportTest".to_string(),
        "InjectedFailure".to_string(),
    ]];
    imports::inject_outcome_for_test(
        &modules,
        Some(Path::new(uri_path)),
        Err("injected import failure".to_string()),
    );

    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri =
        Url::parse("file:///lsp-import-injected-failure.lean").expect("static URI should parse");
    let text =
        "import LspImportTest.InjectedFailure\ndef lsp_import_probe (a : Prop) : Prop := a\n";

    let elaborated = open_and_check(backend, &uri, text).await;
    assert_eq!(
        elaborated.errors.len(),
        1,
        "a failed import closure should surface exactly one diagnostic, got {:?}",
        elaborated.errors,
    );
    let error = &elaborated.errors[0];
    assert_eq!(
        error.message, "imports unavailable: injected import failure",
        "diagnostic should carry the load-failure reason",
    );
    assert_eq!(
        error.start, 0,
        "diagnostic should anchor at the import header",
    );
    assert!(
        elaborated
            .declarations
            .iter()
            .any(|decl| decl.name.ends_with("lsp_import_probe")),
        "declarations after a failed import should still elaborate, got {:?}",
        elaborated.declarations,
    );
}

/// A successfully cached closure is reused verbatim: injecting a marker
/// environment for a synthetic header makes the document elaborate against
/// exactly that environment (no reload, no default base).
#[tokio::test]
async fn test_cached_import_closure_is_reused_as_the_document_base_env() {
    let uri_path = "/lsp-import-injected-success.lean";
    let modules = vec![vec![
        "LspImportTest".to_string(),
        "InjectedSuccess".to_string(),
    ]];
    let marker_env = clean_kernel::Environment::try_with_prelude()
        .expect("prelude environment should initialize for the marker closure");
    imports::inject_outcome_for_test(
        &modules,
        Some(Path::new(uri_path)),
        Ok(Arc::new(marker_env)),
    );

    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri =
        Url::parse("file:///lsp-import-injected-success.lean").expect("static URI should parse");
    // `Nat.succ` lives in the PRELUDE base the injected closure carries — the
    // bare server environment path would not matter here; what is asserted is
    // that the header resolves without diagnostics through the injected entry
    // (no real `.olean` load can occur for this synthetic module name).
    let text =
        "import LspImportTest.InjectedSuccess\ndef lsp_probe_succ (n : Nat) : Nat := Nat.succ n\n";

    let elaborated = open_and_check(backend, &uri, text).await;
    assert!(
        elaborated.errors.is_empty(),
        "cached closure should serve the header without diagnostics, got {:?}",
        elaborated.errors,
    );
    assert!(
        elaborated
            .declarations
            .iter()
            .any(|decl| decl.name.ends_with("lsp_probe_succ")),
        "declaration should elaborate against the injected closure, got {:?}",
        elaborated.declarations,
    );
}

/// Header collection: every module path of every `import` declaration, in
/// source order, including multi-module import lines.
#[test]
fn test_import_paths_of_decls_collects_all_header_modules() {
    let text = "import Alpha.Beta\nimport Gamma\ndef x (a : Prop) : Prop := a\n";
    let decls =
        clean_parser::parse_file_with_tactics(text, &CleanBackend::builtin_tactic_patterns())
            .expect("header fixture should parse");
    let paths = imports::import_paths_of_decls(&decls);
    assert_eq!(
        paths,
        vec![
            vec!["Alpha".to_string(), "Beta".to_string()],
            vec!["Gamma".to_string()],
        ],
        "both import declarations should contribute their module paths",
    );
}
