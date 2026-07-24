// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the swarm-worker `addDecl` handler (C1 Task C).

use crate::handlers::*;
use crate::session_env::SessionId;
use clean_kernel::{BinderInfo, Declaration, Expr, Name};

/// The proposition `∀ (p : Prop), p → p`, shared by the foundational proof and
/// the domain-axiom fixtures so axiom-citing theorems are well-typed.
fn imp_self_type() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    )
}

/// `fun (p : Prop) (h : p) => h : ∀ (p : Prop), p → p` — a closed,
/// foundational-only proof. Same fixture Task A's recheck tests use.
fn imp_self(name: &str) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: imp_self_type(),
        value: Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        ),
    }
}

/// An ill-typed theorem: claims `∀ (p : Prop), p → p` but the proof is the
/// identity on ONE binder, so the value does not match the type. The kernel
/// must reject it.
fn ill_typed(name: &str) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: imp_self_type(),
        // `fun (p : Prop) => p` : ∀ (p : Prop), Prop — NOT the stated type.
        value: Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
    }
}

#[tokio::test]
async fn test_add_decl_valid_theorem_is_kernel_verified_and_accepted() {
    let state = ServerState::new();
    let session_id = state.create_session().await;

    let params = AddDeclParams {
        session_id: Some(session_id.to_string()),
        decl: imp_self("Swarm.imp_self"),
        require_foundational: true,
        heartbeat_limit: None,
    };

    let response = handle_add_decl(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );
    let result: AddDeclResult =
        serde_json::from_value(response.result.expect("addDecl returns a result"))
            .expect("AddDeclResult deserializes");

    assert!(
        result.accepted,
        "valid foundational theorem must be accepted"
    );
    assert_eq!(result.verdict, AddDeclVerdict::KernelVerified);
    assert!(result.axiom_closure.is_empty());
    assert!(result.reject_reason.is_none());

    // The decl must now be a premise inside the session overlay...
    let sessions = state.sessions.read().await;
    let session = sessions.get(&session_id).expect("session is live");
    assert!(
        session.contains(&Name::from_string("Swarm.imp_self")),
        "accepted decl must land in the session overlay (immediately a premise)"
    );
}

#[tokio::test]
async fn test_add_decl_ill_typed_fails_closed_base_pristine() {
    let state = ServerState::new();

    // Capture the shared base size before the session is even created.
    let base_count_before = state.env.read().await.num_constants();
    let session_id = state.create_session().await;

    let params = AddDeclParams {
        session_id: Some(session_id.to_string()),
        decl: ill_typed("Swarm.ill_typed"),
        require_foundational: true,
        heartbeat_limit: None,
    };

    let response = handle_add_decl(&state, RequestId::Number(2), params).await;
    assert!(
        response.error.is_none(),
        "handler returns a typed result, not a transport error"
    );
    let result: AddDeclResult =
        serde_json::from_value(response.result.expect("addDecl returns a result"))
            .expect("AddDeclResult deserializes");

    assert!(!result.accepted, "ill-typed decl must be rejected");
    assert_eq!(result.verdict, AddDeclVerdict::KernelRejected);
    assert!(
        result
            .reject_reason
            .as_deref()
            .is_some_and(|r| r.starts_with("kernel-rejected:")),
        "reject reason keeps the kernel-rejected prefix: {:?}",
        result.reject_reason
    );

    // Session overlay must not have gained the bad decl...
    {
        let sessions = state.sessions.read().await;
        let session = sessions.get(&session_id).expect("session is live");
        assert!(
            !session.contains(&Name::from_string("Swarm.ill_typed")),
            "ill-typed decl must not enter the overlay"
        );
        assert_eq!(session.session_decl_count(), 0);
    }
    // ...and the SHARED base must be byte-for-byte unchanged.
    assert_eq!(
        state.env.read().await.num_constants(),
        base_count_before,
        "rejected decl must leave the shared base corpus pristine"
    );
}

#[tokio::test]
async fn test_add_decl_missing_session_fails_closed() {
    let state = ServerState::new();
    let params = AddDeclParams {
        session_id: None,
        decl: imp_self("Swarm.no_session"),
        require_foundational: true,
        heartbeat_limit: None,
    };
    let response = handle_add_decl(&state, RequestId::Number(3), params).await;
    assert!(
        response.error.is_some(),
        "a missing session_id must be an error, not a silent corpus write"
    );
}

#[tokio::test]
async fn test_add_decl_unknown_session_fails_closed() {
    let state = ServerState::new();
    // A well-formed but never-created session id.
    let ghost = SessionId::new();
    let params = AddDeclParams {
        session_id: Some(ghost.to_string()),
        decl: imp_self("Swarm.ghost_session"),
        require_foundational: true,
        heartbeat_limit: None,
    };
    let response = handle_add_decl(&state, RequestId::Number(4), params).await;
    assert!(
        response.error.is_some(),
        "an unknown session must fail closed"
    );
}

#[tokio::test]
async fn test_add_decl_accepted_decl_is_premise_for_sibling() {
    let state = ServerState::new();
    let session_id = state.create_session().await;

    // First, add an axiom the sibling will depend on.
    let axiom = Declaration::Axiom {
        name: Name::from_string("Swarm.base_prop"),
        level_params: vec![],
        type_: Expr::prop(),
    };
    let first = handle_add_decl(
        &state,
        RequestId::Number(5),
        AddDeclParams {
            session_id: Some(session_id.to_string()),
            decl: axiom,
            // An axiom's own closure is itself (a domain axiom), so don't
            // require foundational for this setup step.
            require_foundational: false,
            heartbeat_limit: None,
        },
    )
    .await;
    let first_result: AddDeclResult =
        serde_json::from_value(first.result.expect("result")).expect("deserialize");
    assert!(first_result.accepted, "axiom setup add must be accepted");

    // Now a decl whose TYPE references the session-local axiom: it can only
    // type-check if the prior add is visible as a premise.
    let dependent = Declaration::Axiom {
        name: Name::from_string("Swarm.uses_base"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Swarm.base_prop"), vec![]),
    };
    let second = handle_add_decl(
        &state,
        RequestId::Number(6),
        AddDeclParams {
            session_id: Some(session_id.to_string()),
            decl: dependent,
            require_foundational: false,
            heartbeat_limit: None,
        },
    )
    .await;
    let second_result: AddDeclResult =
        serde_json::from_value(second.result.expect("result")).expect("deserialize");
    assert!(
        second_result.accepted,
        "a sibling obligation must see the prior accepted decl as a premise: {:?}",
        second_result.reject_reason
    );
}

#[tokio::test]
async fn test_add_decl_require_foundational_rejects_axiom_dependent_and_rolls_back() {
    let state = ServerState::new();
    let session_id = state.create_session().await;

    // Seed a domain axiom into the session (no foundational requirement).
    let axiom = Declaration::Axiom {
        name: Name::from_string("Swarm.domain_axiom"),
        level_params: vec![],
        type_: imp_self_type(),
    };
    let seed = handle_add_decl(
        &state,
        RequestId::Number(7),
        AddDeclParams {
            session_id: Some(session_id.to_string()),
            decl: axiom,
            require_foundational: false,
            heartbeat_limit: None,
        },
    )
    .await;
    let seed_result: AddDeclResult =
        serde_json::from_value(seed.result.expect("result")).expect("deserialize");
    assert!(seed_result.accepted);

    // A theorem `∀ (p : Prop), p → p` proved BY the domain axiom: it
    // kernel-checks, but its closure cites `Swarm.domain_axiom`, so under the
    // default `require_foundational` it must be rejected AND rolled back.
    let dependent = Declaration::Theorem {
        name: Name::from_string("Swarm.cites_axiom"),
        level_params: vec![],
        type_: imp_self_type(),
        value: Expr::const_(Name::from_string("Swarm.domain_axiom"), vec![]),
    };
    let response = handle_add_decl(
        &state,
        RequestId::Number(8),
        AddDeclParams {
            session_id: Some(session_id.to_string()),
            decl: dependent,
            require_foundational: true,
            heartbeat_limit: None,
        },
    )
    .await;
    let result: AddDeclResult =
        serde_json::from_value(response.result.expect("result")).expect("deserialize");

    assert!(
        !result.accepted,
        "axiom-citing decl must be rejected by policy"
    );
    assert_eq!(result.verdict, AddDeclVerdict::AxiomDependent);
    assert_eq!(
        result.axiom_closure,
        vec!["Swarm.domain_axiom".to_string()],
        "the verdict still reports the domain-axiom closure as facts"
    );
    assert!(result
        .reject_reason
        .as_deref()
        .is_some_and(|r| r.contains("require_foundational")));

    // The policy-rejected decl must NOT linger in the overlay (rolled back),
    // while the earlier accepted axiom is preserved.
    let sessions = state.sessions.read().await;
    let session = sessions.get(&session_id).expect("session is live");
    assert!(
        !session.contains(&Name::from_string("Swarm.cites_axiom")),
        "a policy-rejected decl must be rolled out of the overlay"
    );
    assert!(
        session.contains(&Name::from_string("Swarm.domain_axiom")),
        "rollback discards only this call's decl, not earlier accepted work"
    );
}

#[tokio::test]
async fn test_add_decl_axiom_dependent_accepted_when_not_requiring_foundational() {
    let state = ServerState::new();
    let session_id = state.create_session().await;

    // Seed a domain axiom `Swarm.dep_axiom : ∀ (p : Prop), p → p`.
    let axiom = Declaration::Axiom {
        name: Name::from_string("Swarm.dep_axiom"),
        level_params: vec![],
        type_: imp_self_type(),
    };
    let seed = handle_add_decl(
        &state,
        RequestId::Number(9),
        AddDeclParams {
            session_id: Some(session_id.to_string()),
            decl: axiom,
            require_foundational: false,
            heartbeat_limit: None,
        },
    )
    .await;
    let seed_result: AddDeclResult =
        serde_json::from_value(seed.result.expect("result")).expect("deserialize");
    assert!(seed_result.accepted, "axiom seed must be accepted");

    // A theorem with the SAME type, proved by the axiom const — type and value
    // agree, so it kernel-checks; its closure cites the domain axiom.
    let dependent = Declaration::Theorem {
        name: Name::from_string("Swarm.dep_thm"),
        level_params: vec![],
        type_: imp_self_type(),
        value: Expr::const_(Name::from_string("Swarm.dep_axiom"), vec![]),
    };
    let response = handle_add_decl(
        &state,
        RequestId::Number(10),
        AddDeclParams {
            session_id: Some(session_id.to_string()),
            decl: dependent,
            require_foundational: false,
            heartbeat_limit: None,
        },
    )
    .await;
    let result: AddDeclResult =
        serde_json::from_value(response.result.expect("result")).expect("deserialize");

    assert!(
        result.accepted,
        "axiom-dependent decl is accepted when require_foundational is false: {:?}",
        result.reject_reason
    );
    assert_eq!(result.verdict, AddDeclVerdict::AxiomDependent);
    assert_eq!(result.axiom_closure, vec!["Swarm.dep_axiom".to_string()]);

    let sessions = state.sessions.read().await;
    let session = sessions.get(&session_id).expect("session is live");
    assert!(
        session.contains(&Name::from_string("Swarm.dep_thm")),
        "an accepted axiom-dependent decl lands in the overlay"
    );
}
