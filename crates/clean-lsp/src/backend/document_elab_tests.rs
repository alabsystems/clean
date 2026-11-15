// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The editor elaborates through the module driver `clean check` runs: file
//! state (`open`, `section` / `variable`) reaches later declarations, and a
//! failing member of a block is an error at its own span.

use super::super::CleanBackend;
use crate::document::{Document, ElaboratedDocument};
use tower_lsp::lsp_types::Url;
use tower_lsp::LspService;

async fn elaborate(text: &str) -> ElaboratedDocument {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///document-elab-driver.lean").expect("uri");
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;
    let doc = backend.documents.get(&uri).expect("document stays open");
    doc.elaborated
        .clone()
        .expect("the document elaborates to a result")
}

#[tokio::test]
async fn test_compilation_error_retains_nested_declaration_and_its_following_proof() {
    let text = "namespace T\naxiom n : Nat\ndef bad : Nat := n\ntheorem still_here : bad = n := rfl\nend T\n";
    let elaborated = elaborate(text).await;
    assert_eq!(elaborated.errors.len(), 1, "{:?}", elaborated.errors);
    let error = &elaborated.errors[0];
    assert_eq!(error.start, text.find("def bad").expect("bad offset"));
    assert!(
        error.message.contains("not supported by code generator"),
        "{error:?}"
    );
}

/// A failing member of a `namespace` block used to produce NO diagnostic: the
/// block registered as one result and the editor never looked inside it. It
/// is now an error at the member's own span, as `clean check` reports it.
#[tokio::test]
async fn test_document_elab_failing_namespace_member_is_an_error_at_its_span() {
    let text = "namespace T\ndef a : Nat := 1\ndef b : Nat := nope\nend T\n";
    let elaborated = elaborate(text).await;
    let member = text.find("def b").expect("member offset");
    let error = elaborated
        .errors
        .iter()
        .find(|e| e.message.contains("nope"))
        .unwrap_or_else(|| {
            panic!(
                "the failing member must be an error: {:?}",
                elaborated.errors
            )
        });
    assert_eq!(
        error.start, member,
        "the error sits on the member, not the block"
    );
    assert_eq!(elaborated.errors.len(), 1, "{:?}", elaborated.errors);
}

/// A standalone `open` persists to the next declaration, and a section's
/// `variable` reaches the declaration that uses it: the `FileContext` is
/// threaded exactly as `clean check` threads it.
#[tokio::test]
async fn test_document_elab_file_state_reaches_later_declarations() {
    let text = "namespace Foo\ndef x : Nat := 1\nend Foo\nopen Foo\ndef y : Nat := x\n\
                section\nvariable (n : Nat)\ndef addn (m : Nat) : Nat := n + m\nend\n\
                theorem addn_one_two : addn 1 2 = 3 := rfl\n";
    let elaborated = elaborate(text).await;
    assert!(
        elaborated.errors.is_empty(),
        "file state must reach later declarations: {:?}",
        elaborated.errors
    );
    // `addn` itself is a member of the `section` block, and block members
    // carry no top-level declaration info (`extract_elab_info` reads only a
    // single top-level result); `addn_one_two` elaborating is the evidence
    // that `addn` took the section variable as its first parameter.
    for name in ["y", "addn_one_two"] {
        assert!(
            elaborated.declarations.iter().any(|d| d.name == name),
            "{name} must be elaborated: {:?}",
            elaborated.declarations
        );
    }
}

/// A private declaration of a named document is registered under Lean's
/// module-local name (`_private.<module>.0.pd`, G21), but the editor records,
/// hovers and navigates it by the name the source writes, with user-facing
/// names in its type, as Lean 4.8.0's hover shows it (`pp.privateNames
/// false`: `pt : pd 1 = 2`).
#[tokio::test]
async fn test_document_elab_private_declarations_show_their_user_names() {
    let text = "private def pd (n : Nat) : Nat := n + 1\nprivate theorem pt : pd 1 = 2 := rfl\n";
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///PrivHover.lean").expect("uri");
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;
    let elaborated = backend
        .documents
        .get(&uri)
        .expect("document stays open")
        .elaborated
        .clone()
        .expect("the document elaborates to a result");
    assert!(elaborated.errors.is_empty(), "{:?}", elaborated.errors);
    let names: Vec<String> = elaborated
        .declarations
        .iter()
        .map(|decl| decl.identity.to_string())
        .collect();
    assert_eq!(names, ["pd", "pt"]);
    let pt = &elaborated.declarations[1];
    assert_eq!(pt.name, "pt");
    assert_eq!(pt.type_str, "pd 1 = 2");

    // Hover on the use of `pd` in `pt`'s statement.
    let line = "private theorem pt : pd 1 = 2 := rfl";
    let character = u32::try_from(line.find("pd").expect("use of pd")).expect("column");
    let hover = backend
        .get_hover_at(&uri, tower_lsp::lsp_types::Position { line: 1, character })
        .expect("hover on a private definition");
    let tower_lsp::lsp_types::HoverContents::Markup(markup) = hover.contents else {
        panic!("hover is markdown");
    };
    assert!(markup.value.contains("pd : "), "{}", markup.value);
    assert!(!markup.value.contains("_private"), "{}", markup.value);
}
