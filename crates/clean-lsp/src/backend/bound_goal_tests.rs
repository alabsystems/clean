// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual document elaboration and cursor selection; no hand-built locals.
use super::CleanBackend;
use crate::document::Document;
use crate::rpc::{PlainGoalParams, TextDocumentIdentifier};
use tower_lsp::lsp_types::{Position, Url};
use tower_lsp::LspService;

fn goals(backend: &CleanBackend, uri: &Url, line: u32, character: u32) -> Option<Vec<String>> {
    backend
        .plain_goal(PlainGoalParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            position: Position::new(line, character),
        })
        .map(|response| response.goals)
}

async fn install(backend: &CleanBackend, name: &str, source: &str) -> Url {
    let uri = Url::parse(&format!("file:///{name}.lean")).unwrap();
    backend.documents.insert(
        uri.clone(),
        Document::new(uri.clone(), 1, source.to_owned(), "lean".to_owned()),
    );
    backend.parse_document(&uri).await;
    backend.elaborate_document(&uri).await;
    uri
}

#[tokio::test]
async fn bound_goal_example_and_theorem_intro_cursor_transition() {
    for head in ["example", "theorem bound_cursor"] {
        let (service, _socket) = LspService::new(CleanBackend::new);
        let backend = service.inner();
        let source =
            format!("{head} (p q : Prop) (hp : p) : q → p := by\n  intro hq\n  exact hp\n");
        let uri = install(backend, "bound-intro", &source).await;
        let before = goals(backend, &uri, 1, 2).expect("actual before intro");
        assert_eq!(before.len(), 1);
        assert!(before[0].ends_with("⊢ q → p"), "{before:?}");
        assert!(!before[0].contains("hq :"));
        let after = goals(backend, &uri, 1, 10).expect("actual after intro");
        assert_eq!(after, vec!["p q : Prop\nhp : p\nhq : q\n⊢ p"]);
        assert_eq!(
            goals(backend, &uri, 1, 3),
            Some(after.clone()),
            "inside a flat tactic uses after"
        );
        assert_eq!(goals(backend, &uri, 2, 2), Some(after));
        assert_eq!(
            goals(backend, &uri, 2, 10),
            Some(vec![]),
            "exact closes actual goal"
        );
        assert!(goals(backend, &uri, 0, 0).is_none());
        let doc = backend.documents.get(&uri).unwrap();
        assert!(
            doc.elaborated.as_ref().unwrap().errors.is_empty(),
            "{:?}",
            doc.elaborated
        );
    }
}

#[tokio::test]
async fn bound_goal_rewrite_uses_actual_changed_target() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let source = "theorem rewritten_view (a b c : Nat) (h : a = b) (hc : b = c) : a = c := by\n  rw [h]\n  exact hc\n";
    let uri = install(backend, "bound-rewrite", source).await;
    let before = goals(backend, &uri, 1, 2).unwrap();
    assert!(before[0].ends_with("⊢ a = c"), "{before:?}");
    assert_eq!(
        goals(backend, &uri, 1, 3),
        Some(before),
        "rewrite nested rule info retains the pre-state at the head"
    );
    let after = goals(backend, &uri, 1, 8).unwrap();
    assert!(after[0].ends_with("⊢ b = c"), "{after:?}");
    assert!(after[0].contains("h : a = b"), "{after:?}");
    assert_eq!(goals(backend, &uri, 2, 10), Some(vec![]));
    assert!(backend
        .documents
        .get(&uri)
        .unwrap()
        .elaborated
        .as_ref()
        .unwrap()
        .errors
        .is_empty());
}

#[tokio::test]
async fn bound_goal_parenthesized_argument_keeps_its_owned_tail() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let source = "theorem parenthesized_cursor (p : Prop) (hp : p) : p := by\n  exact ((hp))\n";
    let uri = install(backend, "bound-owned-delimiters", source).await;
    assert_eq!(
        goals(backend, &uri, 1, 2),
        Some(vec!["p : Prop\nhp : p\n⊢ p".to_owned()])
    );
    let end = source.lines().nth(1).unwrap().len() as u32;
    assert_eq!(goals(backend, &uri, 1, end - 1), Some(vec![]));
    assert_eq!(goals(backend, &uri, 1, end), Some(vec![]));
    assert!(backend
        .documents
        .get(&uri)
        .unwrap()
        .elaborated
        .as_ref()
        .unwrap()
        .errors
        .is_empty());
}

#[tokio::test]
async fn bound_goal_application_argument_keeps_actual_tail() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let source = "theorem application_cursor (p : Prop) (hp : p) (identity : p → p) : p := by\n  exact identity hp\n";
    let uri = install(backend, "bound-application-tail", source).await;
    assert_eq!(
        goals(backend, &uri, 1, 2),
        Some(vec!["p : Prop\nhp : p\nidentity : p → p\n⊢ p".to_owned()])
    );
    assert_eq!(goals(backend, &uri, 1, 18), Some(vec![]));
    assert_eq!(goals(backend, &uri, 1, 19), Some(vec![]));
    assert!(backend
        .documents
        .get(&uri)
        .unwrap()
        .elaborated
        .as_ref()
        .unwrap()
        .errors
        .is_empty());
}

#[tokio::test]
async fn bound_goal_dependent_partial_and_shadow_contexts_are_typed() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = install(
        backend,
        "bound-dependent",
        "theorem dependent_cursor (α : Type) (x : α) (h : x = x) : x = x := by\n  skip\n",
    )
    .await;
    let view = goals(backend, &uri, 1, 3).unwrap();
    assert_eq!(view, vec!["α : Type\nx : α\nh : x = x\n⊢ x = x"]);
    assert!(
        !backend
            .documents
            .get(&uri)
            .unwrap()
            .elaborated
            .as_ref()
            .unwrap()
            .errors
            .is_empty(),
        "partial is not a proof pass"
    );
    let uri = install(
        backend,
        "bound-shadow",
        "theorem shadow_cursor (n : Nat) (h : n = n) (n : Nat) : n = n := by\n  skip\n",
    )
    .await;
    let view = goals(backend, &uri, 1, 3).unwrap();
    assert_eq!(view, vec!["n✝ : Nat\nh : n✝ = n✝\nn : Nat\n⊢ n = n"]);
}

#[tokio::test]
async fn bound_goal_local_instance_and_have_keep_normal_elaboration_context() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let source = "theorem instance_cursor (α : Type) [inst : Inhabited α] (h : True) : True := by\n  have x : α := default\n  exact h\n";
    let uri = install(backend, "bound-instance", source).await;
    let view = goals(backend, &uri, 2, 2).unwrap();
    assert!(view[0].contains("inst : Inhabited α"), "{view:?}");
    assert!(view[0].contains("x : α"), "{view:?}");
    assert!(view[0].ends_with("⊢ True"));
    assert!(!view[0].contains("#F"));
    assert_eq!(goals(backend, &uri, 2, 9), Some(vec![]));
    assert!(backend
        .documents
        .get(&uri)
        .unwrap()
        .elaborated
        .as_ref()
        .unwrap()
        .errors
        .is_empty());
}

#[tokio::test]
async fn bound_goal_sorry_and_failed_exact_never_claim_solved() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = install(
        backend,
        "bound-sorry",
        "example (n : Nat) : n = n := by\n  sorry\n",
    )
    .await;
    let expected = vec!["n : Nat\n⊢ n = n".to_owned()];
    assert_eq!(goals(backend, &uri, 1, 2), Some(expected.clone()));
    assert_eq!(
        goals(backend, &uri, 1, 7),
        Some(expected),
        "trusted after state is unavailable, retain typed before"
    );
    let uri = install(
        backend,
        "bound-invalid-exact",
        "example (n : Nat) : True := by\n  exact n\n",
    )
    .await;
    assert_eq!(
        goals(backend, &uri, 1, 9),
        Some(vec!["n : Nat\n⊢ True".to_owned()])
    );
    assert!(!backend
        .documents
        .get(&uri)
        .unwrap()
        .elaborated
        .as_ref()
        .unwrap()
        .errors
        .is_empty());
}

#[tokio::test]
async fn bound_goal_invalid_header_has_no_typed_view_even_when_tactic_closes() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = install(
        backend,
        "bound-invalid-header",
        "example (n : 0) : True := by\n  trivial\n",
    )
    .await;
    for character in [2, 3, 9] {
        assert!(goals(backend, &uri, 1, character).is_none());
    }
    assert!(!backend
        .documents
        .get(&uri)
        .unwrap()
        .elaborated
        .as_ref()
        .unwrap()
        .errors
        .is_empty());
    let uri = install(
        backend,
        "bound-valid-header",
        "example (n : Nat) : True := by\n  trivial\n",
    )
    .await;
    assert_eq!(
        goals(backend, &uri, 1, 2),
        Some(vec!["n : Nat\n⊢ True".to_owned()])
    );
    assert_eq!(goals(backend, &uri, 1, 9), Some(vec![]));
}

#[tokio::test]
async fn bound_goal_compound_proof_term_uses_actual_nested_by_state() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let source =
        "theorem compound_cursor (p q : Prop) (hp : p) : q → p := (by\n  intro hq\n  exact hp)\n";
    let uri = install(backend, "bound-compound", source).await;
    let view = goals(backend, &uri, 1, 10).unwrap();
    assert_eq!(view, vec!["p q : Prop\nhp : p\nhq : q\n⊢ p"]);
    assert_eq!(goals(backend, &uri, 2, 10), Some(vec![]));
    assert!(backend
        .documents
        .get(&uri)
        .unwrap()
        .elaborated
        .as_ref()
        .unwrap()
        .errors
        .is_empty());
}

#[tokio::test]
async fn bound_goal_nested_and_transitive_sorry_keep_unsolved_view() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let uri = install(
        backend,
        "bound-nested-sorry",
        "theorem nested_sorry_cursor (p : Prop) : p := by\n  exact (by sorry)\n",
    )
    .await;
    let view = goals(backend, &uri, 1, 18).unwrap();
    assert_eq!(
        view,
        vec!["p : Prop\n⊢ p"],
        "admitted term cannot publish no goals"
    );
    let uri = install(backend, "bound-transitive-sorry", "theorem admitted_cursor (p : Prop) : p := by\n  sorry\ntheorem uses_admitted_cursor (p : Prop) : p := by\n  exact admitted_cursor p\n").await;
    let view = goals(backend, &uri, 3, 25).unwrap();
    assert_eq!(
        view,
        vec!["p : Prop\n⊢ p"],
        "an admitted alias cannot publish no goals"
    );
}

#[tokio::test]
async fn bound_goal_by_prefix_keeps_actual_header_context() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let source = "example (p q : Prop) (hp : p) : q → p := by\n  intro hq\n  exact hp\n";
    let uri = install(backend, "bound-by-prefix", source).await;
    let by_character = source[..source.find("by").unwrap()].encode_utf16().count() as u32;
    let expected = goals(backend, &uri, 1, 2).unwrap();
    for character in [by_character, by_character + 1, by_character + 2] {
        assert_eq!(goals(backend, &uri, 0, character), Some(expected.clone()));
    }
    assert!(expected[0].contains("hp : p"));
    assert!(expected[0].ends_with("⊢ q → p"));
}

#[tokio::test]
async fn bound_goal_outer_term_tactic_ignores_nested_by_for_after_selection() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let source =
        "theorem nested_cursor (p : Prop) (hp : p) : p := by\n  exact (by\n    exact hp)\n";
    let uri = install(backend, "bound-nested-cursor", source).await;
    assert_eq!(
        goals(backend, &uri, 1, 2),
        Some(vec!["p : Prop\nhp : p\n⊢ p".to_owned()])
    );
    assert_eq!(goals(backend, &uri, 1, 3), Some(vec![]));
    assert_eq!(
        goals(backend, &uri, 2, 4),
        Some(vec!["p : Prop\nhp : p\n⊢ p".to_owned()])
    );
    assert_eq!(goals(backend, &uri, 2, 5), Some(vec![]));
}

#[tokio::test]
async fn bound_goal_unresolved_constructor_witness_never_claims_solved() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let source = "theorem unresolved_cursor : ∃ n : Nat, True := by\n  exact ⟨_, True.intro⟩\n";
    let uri = install(backend, "bound-unresolved-witness", source).await;
    assert!(goals(backend, &uri, 1, 3).is_none_or(|g| !g.is_empty()));
    assert!(!backend
        .documents
        .get(&uri)
        .unwrap()
        .elaborated
        .as_ref()
        .unwrap()
        .errors
        .is_empty());
}

#[tokio::test]
async fn bound_goal_trailing_whitespace_and_eof_exclude_following_declaration() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let source = "theorem whitespace_cursor (p : Prop) (hp : p) : p := by\n  exact hp\n\ntheorem following_cursor : True := by\n  trivial\n\n";
    let uri = install(backend, "bound-whitespace", source).await;
    for (line, character) in [(1, 3), (1, 10), (2, 0), (4, 9), (5, 0), (6, 0)] {
        assert_eq!(
            goals(backend, &uri, line, character),
            Some(vec![]),
            "actual completed view at {line}:{character}"
        );
    }
    assert!(
        goals(backend, &uri, 3, 0).is_none(),
        "following declaration is outside previous proof"
    );
    assert_eq!(goals(backend, &uri, 3, 35), Some(vec!["⊢ True".to_owned()]));
    assert!(backend
        .documents
        .get(&uri)
        .unwrap()
        .elaborated
        .as_ref()
        .unwrap()
        .errors
        .is_empty());
}

#[tokio::test]
async fn bound_goal_rwa_exposes_closure_only_at_the_rule_list_tail() {
    let (service, _socket) = LspService::new(CleanBackend::new);
    let backend = service.inner();
    let source = "theorem rwa_cursor (a b : Nat) (h : a = b) : a = b := by\n  rwa [h]\n";
    let uri = install(backend, "bound-rwa", source).await;
    // Use the shared display's actual output rather than grouping source binders.
    let actual = goals(backend, &uri, 1, 2).expect("actual before rwa");
    assert_eq!(actual.len(), 1);
    assert!(actual[0].ends_with("⊢ a = b"), "{actual:?}");
    assert!(actual[0].contains("h : a = b"), "{actual:?}");
    for character in [3, 6, 8] {
        assert_eq!(goals(backend, &uri, 1, character), Some(actual.clone()));
    }
    assert_eq!(goals(backend, &uri, 1, 9), Some(vec![]));
    assert!(backend
        .documents
        .get(&uri)
        .unwrap()
        .elaborated
        .as_ref()
        .unwrap()
        .errors
        .is_empty());
}
