// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regressions for the bounded plainTermGoal wire/capture change.
//! These tests distinguish real elaboration from injected observer metadata.

use super::*;
use crate::document::{ElaboratedDecl, ElaboratedDocument, HoleContext, IncrementalState};
use crate::rpc::{PlainTermGoalParams, PlainTermGoalResponse, TextDocumentIdentifier};
use serde_json::json;
use tower_lsp::LspService;

fn params(uri: &Url, position: Position) -> PlainTermGoalParams {
    PlainTermGoalParams {
        text_document: TextDocumentIdentifier { uri: uri.clone() },
        position,
    }
}

/// Injected observer input for deterministic range/version state tests only.
/// This helper does not claim to elaborate or check the supplied goal text.
fn captured(text: &str, expected_type: &str) -> ElaboratedDocument {
    let start = text.rfind('_').expect("fixture has a hole");
    ElaboratedDocument {
        errors: vec![],
        warnings: vec![],
        declarations: vec![],
        term_infos: Vec::new(),
        holes: vec![HoleContext {
            start,
            end: start + 1,
            expected_type: expected_type.to_string(),
            local_bindings: vec![],
        }],
        widget_modules: vec![],
    }
}

#[test]
fn absent_term_goal_is_json_null_and_present_shape_requires_goal_and_range() {
    let absent: Option<PlainTermGoalResponse> = None;
    assert_eq!(serde_json::to_value(absent).unwrap(), json!(null));
    let present = Some(PlainTermGoalResponse {
        goal: "n : Nat\n⊢ Nat".to_string(),
        range: RpcRange {
            start: Position::new(0, 29),
            end: Position::new(0, 30),
        },
    });
    assert_eq!(
        serde_json::to_value(present).unwrap(),
        json!({
            "goal": "n : Nat\n⊢ Nat",
            "range": {
                "start": {"line": 0, "character": 29},
                "end": {"line": 0, "character": 30}
            }
        })
    );
    for invalid in [
        json!({}),
        json!({"goal": "Nat"}),
        json!({"goal": null, "range": {
            "start": {"line": 0, "character": 0},
            "end": {"line": 0, "character": 1}
        }}),
    ] {
        assert!(serde_json::from_value::<Option<PlainTermGoalResponse>>(invalid).is_err());
    }
}

#[test]
fn absent_uri_and_uncaptured_document_return_null_even_with_another_live_hole() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let captured_uri = Url::parse("file:///captured-term.lean").unwrap();
    let text = "def answer : Nat := _\n";
    let mut doc = Document::new(
        captured_uri.clone(),
        1,
        text.to_string(),
        "lean".to_string(),
    );
    doc.elaborated = Some(captured(text, "Nat"));
    backend.documents.insert(captured_uri, doc);
    assert!(backend.has_live_hole_expected_type_state());

    let absent_uri = Url::parse("file:///absent-term.lean").unwrap();
    let absent = backend.plain_term_goal(params(&absent_uri, Position::new(0, 20)));
    assert_eq!(serde_json::to_value(absent).unwrap(), json!(null));
    backend.documents.insert(
        absent_uri.clone(),
        Document::new(absent_uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    assert!(backend
        .plain_term_goal(params(&absent_uri, Position::new(0, 20)))
        .is_none());
}

#[test]
fn term_goal_request_distinguishes_closed_files_from_open_uncaptured_files() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///closed-term.lean").unwrap();
    let position = Position::new(0, 0);
    let assert_closed = || {
        let error = backend
            .plain_term_goal_request(params(&uri, position))
            .expect_err("a closed file is a request error, not an empty goal");
        assert_eq!(serde_json::to_value(error).unwrap()["code"], -32801);
    };
    assert_closed();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, String::new(), "lean".to_string()),
    );
    assert!(backend
        .plain_term_goal_request(params(&uri, position))
        .expect("an open file can receive requests")
        .is_none());
    backend.documents.remove(&uri);
    assert_closed();
}

#[tokio::test]
async fn real_subterm_hole_range_uses_utf16_after_a_non_bmp_identifier() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///non-bmp-term.lean").unwrap();
    let text = "def «😀» (n : Nat) : Nat := (_ : Nat)\n";
    backend
        .env
        .write()
        .await
        .init_nat()
        .expect("Nat initializes");
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;

    let elaborated = backend
        .documents
        .get(&uri)
        .unwrap()
        .elaborated
        .clone()
        .unwrap();
    assert_eq!(elaborated.holes.len(), 1, "a real hole capture is required");
    let hole = &elaborated.holes[0];
    assert_eq!(
        (hole.start, hole.end),
        (33, 34),
        "literal UTF-8 byte offsets"
    );
    assert_eq!(hole.expected_type, "Nat");
    assert_eq!(hole.local_bindings, [("n".to_string(), "Nat".to_string())]);
    let response = backend
        .plain_term_goal(params(&uri, Position::new(0, 29)))
        .expect("the real captured hole supplies a response");
    assert_eq!(response.goal, "n : Nat\n⊢ Nat");
    assert_eq!(response.range.start, Position::new(0, 29));
    assert_eq!(response.range.end, Position::new(0, 30));
    assert_eq!(
        backend
            .plain_term_goal(params(&uri, Position::new(0, 30)))
            .expect("Lean's includeStop also selects the hole at its end")
            .goal,
        response.goal
    );
    let declaration = backend
        .plain_term_goal(params(&uri, Position::new(0, 4)))
        .expect("the elaborated declaration name has its own constant type");
    assert_eq!(declaration.goal, "⊢ Nat → Nat");
    assert_eq!(declaration.range.start, Position::new(0, 4));
    assert_eq!(declaration.range.end, Position::new(0, 8));
    // Real Lean 4.36rc2 selects the enclosing ascription at these points.
    // They are outside the hole, but inside another captured term.
    for position in [Position::new(0, 28), Position::new(0, 31)] {
        let enclosing = backend
            .plain_term_goal(params(&uri, position))
            .expect("the enclosing ascription has its own term context");
        assert_eq!(enclosing.goal, "n : Nat\n⊢ Nat");
        assert_eq!(enclosing.range.start, Position::new(0, 28));
        assert_eq!(enclosing.range.end, Position::new(0, 37));
    }
    assert!(backend
        .plain_term_goal(params(&uri, Position::new(1, 0)))
        .is_none());
    // Keep every original hole-only negative control on the same document
    // and real hole metadata, without ordinary source-term observations.
    backend
        .documents
        .get_mut(&uri)
        .unwrap()
        .elaborated
        .as_mut()
        .unwrap()
        .term_infos
        .clear();
    for outside in [
        Position::new(0, 4),
        Position::new(0, 28),
        Position::new(0, 31),
        Position::new(1, 0),
    ] {
        assert!(backend.plain_term_goal(params(&uri, outside)).is_none());
    }
}

#[test]
fn malformed_recorded_byte_spans_do_not_become_clamped_or_rounded_ranges() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///invalid-hole-span.lean").unwrap();
    let text = "def «😀» : Nat := _\n";
    let emoji = text.find('😀').unwrap();
    for (start, end) in [
        (0, 0),
        (1, 0),
        (0, text.len() + 1),
        (emoji + 1, emoji + 4),
        (emoji, emoji + 1),
    ] {
        let mut doc = Document::new(uri.clone(), 1, text.to_string(), "lean".to_string());
        let mut elaborated = captured(text, "Nat");
        elaborated.holes[0].start = start;
        elaborated.holes[0].end = end;
        doc.elaborated = Some(elaborated);
        backend.documents.insert(uri.clone(), doc);
        for column in 0..=25 {
            assert!(backend
                .plain_term_goal(params(&uri, Position::new(0, column)))
                .is_none());
        }
    }
}

#[tokio::test]
async fn real_dependent_hole_names_follow_the_current_document() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///dependent-term.lean").unwrap();
    for (version, text, expected) in [
        (
            1,
            "def «😀» (A : Type) (x : A) : A := (_ : A)\n",
            "A : Type\nx : A\n⊢ A",
        ),
        (
            2,
            "def «😀» (B : Type) (y : B) : B := (_ : B)\n",
            "B : Type\ny : B\n⊢ B",
        ),
    ] {
        if version == 1 {
            backend.documents.insert(
                uri.clone(),
                Document::new(uri.clone(), version, text.to_string(), "lean".to_string()),
            );
        } else {
            let mut doc = backend.documents.get_mut(&uri).unwrap();
            doc.version = version;
            doc.apply_change(None, text);
        }
        backend.parse_document(&uri).await;
        backend.elaborate_document(&uri).await;
        for column in [36, 37] {
            let response = backend
                .plain_term_goal_request(params(&uri, Position::new(0, column)))
                .unwrap()
                .expect("normal elaboration captures the hole's dependent context");
            assert_eq!(response.goal, expected);
            assert_eq!(response.range.start, Position::new(0, 36));
            assert_eq!(response.range.end, Position::new(0, 37));
        }
    }
}

#[test]
fn full_change_invalidates_holes_and_stale_commit_cannot_restore_them() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///versioned-term.lean").unwrap();
    let old_text = "def f : Nat := _\n";
    let new_text = "-- 😀\ndef f : Bool := _\n";
    let old_elaborated = captured(old_text, "Nat");
    let mut doc = Document::new(uri.clone(), 1, old_text.to_string(), "lean".to_string());
    doc.elaborated = Some(old_elaborated.clone());
    backend.documents.insert(uri.clone(), doc);
    assert!(backend
        .plain_term_goal(params(&uri, Position::new(0, 15)))
        .is_some());
    {
        let mut doc = backend.documents.get_mut(&uri).unwrap();
        doc.version = 2;
        doc.apply_change(None, new_text);
        assert!(doc.elaborated.as_ref().unwrap().holes.is_empty());
    }
    assert!(backend
        .plain_term_goal(params(&uri, Position::new(0, 15)))
        .is_none());
    assert!(backend
        .plain_term_goal(params(&uri, Position::new(1, 16)))
        .is_none());
    assert!(!backend.commit_elaboration(
        &uri,
        1,
        old_text,
        old_elaborated,
        IncrementalState::default(),
        vec![],
        None,
    ));
    assert!(backend
        .documents
        .get(&uri)
        .unwrap()
        .elaborated
        .as_ref()
        .unwrap()
        .holes
        .is_empty());
    assert!(backend.commit_elaboration(
        &uri,
        2,
        new_text,
        captured(new_text, "Bool"),
        IncrementalState::default(),
        vec![],
        None,
    ));
    let response = backend
        .plain_term_goal(params(&uri, Position::new(1, 16)))
        .unwrap();
    assert_eq!(response.goal, "⊢ Bool");
    assert_eq!(response.range.start, Position::new(1, 16));
    assert_eq!(response.range.end, Position::new(1, 17));
}

#[test]
fn incremental_change_invalidates_holes_but_preserves_declaration_metadata() {
    let uri = Url::parse("file:///incremental-term.lean").unwrap();
    let text = "def f : Nat := _\n";
    let mut doc = Document::new(uri, 1, text.to_string(), "lean".to_string());
    let mut elaborated = captured(text, "Nat");
    elaborated.declarations.push(ElaboratedDecl {
        identity: clean_kernel::Name::anon().str("f"),
        name: "f".to_string(),
        type_str: "Nat".to_string(),
        start: 0,
        end: text.len() - 1,
    });
    doc.elaborated = Some(elaborated);
    doc.apply_change(
        Some(Range::new(Position::new(0, 0), Position::new(0, 0))),
        "-- 😀\n",
    );
    let remaining = doc.elaborated.as_ref().unwrap();
    assert!(remaining.holes.is_empty());
    assert_eq!(remaining.declarations.len(), 1);
    assert_eq!(remaining.declarations[0].type_str, "Nat");
    assert_eq!(doc.text(), "-- 😀\ndef f : Nat := _\n");
}

#[tokio::test]
async fn real_ordinary_term_infos_follow_expected_and_inferred_types_across_edits() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///ordinary-term-goal.lean").unwrap();
    for (version, text, expected) in [
        (
            1,
            "def «😀» (A : Type) (x : A) : A := x\n",
            "A : Type\nx : A\n⊢ A",
        ),
        (
            2,
            "def «😀» (A : Type) (x : A) := x\n",
            "A : Type\nx : A\n⊢ A",
        ),
        (
            3,
            "def «😀» (B : Type) (y : B) := y\n",
            "B : Type\ny : B\n⊢ B",
        ),
        (
            4,
            "def «😀» (A : Type) (x : A) : {n : Nat} → A := x\n",
            "A : Type\nx : A\nn✝ : Nat\n⊢ A",
        ),
        (
            5,
            "def «😀» (A : Type) (x : A) : A := let y : A := x; y\n",
            "A : Type\nx : A\ny : A := x\n⊢ A",
        ),
        (
            6,
            "def «😀» (A : Type) (x : A) : A := (x : A)\n",
            "A : Type\nx : A\n⊢ A",
        ),
    ] {
        if version == 1 {
            backend.documents.insert(
                uri.clone(),
                Document::new(uri.clone(), version, text.to_string(), "lean".to_string()),
            );
        } else {
            let mut doc = backend.documents.get_mut(&uri).unwrap();
            doc.version = version;
            doc.apply_change(None, text);
            assert!(doc.elaborated.as_ref().unwrap().term_infos.is_empty());
        }
        backend.parse_document(&uri).await;
        backend.elaborate_document(&uri).await;
        let start = text
            .rfind(if version == 3 || version == 5 {
                'y'
            } else {
                'x'
            })
            .unwrap();
        let doc = backend.documents.get(&uri).unwrap();
        let range = (
            doc.offset_to_position(start),
            doc.offset_to_position(start + 1),
        );
        drop(doc);
        for position in [range.0, range.1] {
            let response = backend
                .plain_term_goal_request(params(&uri, position))
                .unwrap()
                .expect("normal term elaboration supplies the goal");
            assert_eq!(response.goal, expected);
            assert_eq!(response.range.start, range.0);
            assert_eq!(response.range.end, range.1);
        }
        assert!(backend
            .plain_term_goal_request(params(&uri, Position::new(0, 0)))
            .unwrap()
            .is_none());
    }
}

#[tokio::test]
async fn explicit_sorry_without_a_captured_context_does_not_reuse_the_declaration_type() {
    for (index, (text, expected)) in [
        ("def answer : Nat := sorry\n", "⊢ Nat"),
        ("def g : Nat → Nat := sorry\n", "⊢ Nat → Nat"),
        ("def bound (n : Nat) : Nat := sorry\n", "n : Nat\n⊢ Nat"),
    ]
    .into_iter()
    .enumerate()
    {
        let (service, _socket) = LspService::new(CleanBackend::new);
        let backend = service.inner();
        let uri = Url::parse(&format!("file:///uncaptured-sorry-{index}.lean")).unwrap();
        backend
            .env
            .write()
            .await
            .init_nat()
            .expect("Nat initializes");
        backend.documents.insert(
            uri.clone(),
            Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
        );
        backend.parse_document(&uri).await;
        backend.elaborate_document(&uri).await;
        let doc = backend.documents.get(&uri).unwrap();
        let elaborated = doc.elaborated.as_ref().expect("document was checked");
        assert_eq!(
            elaborated.declarations.len(),
            1,
            "keep declaration metadata"
        );
        assert!(
            elaborated.holes.is_empty(),
            "sorry does not manufacture underscore-hole metadata"
        );
        let position = doc.offset_to_position(text.find("sorry").unwrap());
        assert!(elaborated.term_infos.iter().any(|term| {
            term.start == text.find("sorry").unwrap() && term.end == term.start + 5
        }));
        drop(doc);
        assert_eq!(
            backend
                .plain_term_goal(params(&uri, position))
                .expect("the actual sorry term has its own captured context")
                .goal,
            expected
        );
        // Retain the original no-capture negative control on the same real
        // declaration metadata: a declaration type alone cannot supply a goal.
        backend
            .documents
            .get_mut(&uri)
            .unwrap()
            .elaborated
            .as_mut()
            .unwrap()
            .term_infos
            .clear();
        assert!(backend.plain_term_goal(params(&uri, position)).is_none());
    }
}

#[tokio::test]
async fn registered_declaration_names_use_source_tokens_through_comments_and_privacy() {
    let mut comment_checks = 0;
    for text in [
        "namespace N\nprivate def «😀» (n : Nat) : Nat := n\nend N\n",
        "namespace N\n/-- «😀» in docs --/\ndef /- «😀» -/ «😀» (n : Nat) : Nat := n\nend N\n",
    ] {
        let (service, _socket) = LspService::new(CleanBackend::new);
        let backend = service.inner();
        let uri = Url::parse("file:///declaration-name-term.lean").unwrap();
        backend
            .env
            .write()
            .await
            .init_nat()
            .expect("Nat initializes");
        backend.documents.insert(
            uri.clone(),
            Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
        );
        backend.parse_document(&uri).await;
        backend.elaborate_document(&uri).await;
        let doc = backend.documents.get(&uri).unwrap();
        let elaborated = doc.elaborated.as_ref().unwrap();
        assert!(elaborated.errors.is_empty(), "the real definition checks");
        assert_eq!(
            elaborated.declarations.len(),
            0,
            "namespace containers have no top-level navigation declaration"
        );
        let name_start = text.find("«😀» (").unwrap();
        let range = Range::new(
            doc.offset_to_position(name_start),
            doc.offset_to_position(name_start + "«😀»".len()),
        );
        let comment = text
            .find("«😀» in docs")
            .map(|at| doc.offset_to_position(at));
        drop(doc);
        for position in [range.start, range.end] {
            let goal = backend
                .plain_term_goal(params(&uri, position))
                .expect("registered name");
            assert_eq!(goal.goal, "⊢ Nat → Nat");
            assert_eq!(goal.range.start, range.start);
            assert_eq!(goal.range.end, range.end);
        }
        comment_checks += usize::from(comment.is_some());
        assert!(comment
            .is_none_or(|position| backend.plain_term_goal(params(&uri, position)).is_none()));
    }
    assert!(
        comment_checks > 0,
        "the fixtures must exercise a comment position"
    );
}

#[tokio::test]
async fn real_binder_and_tactic_terms_keep_their_own_contexts() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///binder-tactic-term-goal.lean").unwrap();
    let text = "def «😀» (A : Type) : A → A := by\n  intro x\n  exact x\n";
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;
    {
        let doc = backend.documents.get(&uri).unwrap();
        let elaborated = doc.elaborated.as_ref().unwrap();
        assert!(
            elaborated.errors.is_empty(),
            "the real definition must check"
        );
        assert_eq!(elaborated.declarations.len(), 1);
    }
    // Exact native 4.36rc2 observations: binder info hides its own local,
    // whereas a reference to that local includes it in the context.
    for (point, end, expected) in [
        (Position::new(0, 10), Position::new(0, 11), "⊢ Type"),
        (Position::new(0, 14), Position::new(0, 18), "⊢ Sort ?u.1"),
        (Position::new(1, 8), Position::new(1, 9), "A : Type\n⊢ A"),
        (
            Position::new(2, 8),
            Position::new(2, 9),
            "A : Type\nx : A\n⊢ A",
        ),
    ] {
        let response = backend
            .plain_term_goal_request(params(&uri, point))
            .unwrap()
            .expect("actual binder/reference info is present");
        assert_eq!(response.goal, expected);
        assert_eq!(response.range.start, point);
        assert_eq!(response.range.end, end);
    }
    for point in [Position::new(0, 31), Position::new(0, 0)] {
        assert!(backend
            .plain_term_goal_request(params(&uri, point))
            .unwrap()
            .is_none());
    }
}

#[tokio::test]
async fn real_sort_constraints_and_grouped_locals_follow_native_type_positions() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = Url::parse("file:///type-constraint-term-goal.lean").unwrap();
    let text = "def «😀» (A : Type) (B : Type) (a : A) : B → A := fun b => a\n";
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;
    {
        let doc = backend.documents.get(&uri).unwrap();
        assert!(doc.elaborated.as_ref().unwrap().errors.is_empty());
        assert_eq!(doc.elaborated.as_ref().unwrap().declarations.len(), 1);
    }
    for (start, end, expected) in [
        (14, 18, "⊢ Sort ?u.1"),
        (25, 29, "A : Type\n⊢ Sort ?u.2"),
        (36, 37, "A B : Type\n⊢ Type"),
        (41, 42, "A B : Type\na : A\n⊢ Type"),
        (45, 46, "A B : Type\na : A\n⊢ Type"),
        (59, 60, "A B : Type\na : A\nb : B\n⊢ A"),
    ] {
        let response = backend
            .plain_term_goal(params(&uri, Position::new(0, start)))
            .expect("actual type/term observation");
        assert_eq!(response.goal, expected);
        assert_eq!(response.range.start, Position::new(0, start));
        assert_eq!(response.range.end, Position::new(0, end));
    }

    let text = "def one (n : Nat) (A : Type) (a : A) : A := a\ndef two (B : Type) (b : B) : B := b\ndef three : (Type → Type) := fun C => C\n";
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 2, text.to_string(), "lean".to_string()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;
    {
        let doc = backend.documents.get(&uri).unwrap();
        assert!(doc.elaborated.as_ref().unwrap().errors.is_empty());
        assert_eq!(doc.elaborated.as_ref().unwrap().declarations.len(), 3);
    }
    for (line, start, end, expected) in [
        (0, 13, 16, "⊢ Type"),
        (0, 23, 27, "n : Nat\n⊢ Sort ?u.2"),
        (0, 44, 45, "n : Nat\nA : Type\na : A\n⊢ A"),
        (1, 13, 17, "⊢ Sort ?u.1"),
        (2, 13, 17, "⊢ Sort ?u.2"),
        (2, 20, 24, "⊢ Sort ?u.3"),
    ] {
        let response = backend
            .plain_term_goal(params(&uri, Position::new(line, start)))
            .expect("actual declaration-local sort observation");
        assert_eq!(response.goal, expected);
        assert_eq!(response.range.start, Position::new(line, start));
        assert_eq!(response.range.end, Position::new(line, end));
    }
}
