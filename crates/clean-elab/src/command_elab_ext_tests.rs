// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended command elaboration (`command_elab_ext`).

use super::command_elab_ext::*;
use crate::error::ElabError;
use clean_kernel::Name;

// =============================================================================
// Attribute parsing tests
// =============================================================================

#[test]
fn test_parse_attribute_simp_no_args() {
    let attr = parse_attribute("simp", &[]);
    assert_eq!(attr, DeclAttribute::Simp(None));
}

#[test]
fn test_parse_attribute_simp_with_priority() {
    let attr = parse_attribute("simp", &["100".to_owned()]);
    assert_eq!(attr, DeclAttribute::Simp(Some(100)));
}

#[test]
fn test_parse_attribute_simp_invalid_priority_is_none() {
    let attr = parse_attribute("simp", &["notanumber".to_owned()]);
    assert_eq!(attr, DeclAttribute::Simp(None));
}

#[test]
fn test_parse_attribute_inline() {
    let attr = parse_attribute("inline", &[]);
    assert_eq!(attr, DeclAttribute::Inline);
}

#[test]
fn test_parse_attribute_reducible() {
    let attr = parse_attribute("reducible", &[]);
    assert_eq!(attr, DeclAttribute::Reducible);
}

#[test]
fn test_parse_attribute_irreducible() {
    let attr = parse_attribute("irreducible", &[]);
    assert_eq!(attr, DeclAttribute::Irreducible);
}

#[test]
fn test_parse_attribute_instance_no_prio() {
    let attr = parse_attribute("instance", &[]);
    assert_eq!(attr, DeclAttribute::Instance(None));
}

#[test]
fn test_parse_attribute_instance_with_prio() {
    let attr = parse_attribute("instance", &["500".to_owned()]);
    assert_eq!(attr, DeclAttribute::Instance(Some(500)));
}

#[test]
fn test_parse_attribute_extern_with_name() {
    let attr = parse_attribute("extern", &["lean_mk_array".to_owned()]);
    assert_eq!(attr, DeclAttribute::Extern("lean_mk_array".to_owned()));
}

#[test]
fn test_parse_attribute_extern_no_name() {
    let attr = parse_attribute("extern", &[]);
    assert_eq!(attr, DeclAttribute::Extern(String::new()));
}

#[test]
fn test_parse_attribute_specialize() {
    assert_eq!(
        parse_attribute("specialize", &[]),
        DeclAttribute::Specialize
    );
}

#[test]
fn test_parse_attribute_nospecialize() {
    assert_eq!(
        parse_attribute("nospecialize", &[]),
        DeclAttribute::Nospecialize
    );
}

#[test]
fn test_parse_attribute_macro_inline() {
    assert_eq!(
        parse_attribute("macro_inline", &[]),
        DeclAttribute::MacroInline
    );
}

#[test]
fn test_parse_attribute_csimp() {
    assert_eq!(parse_attribute("csimp", &[]), DeclAttribute::Csimp);
}

#[test]
fn test_parse_attribute_custom() {
    let attr = parse_attribute("my_custom_attr", &[]);
    assert_eq!(attr, DeclAttribute::Custom("my_custom_attr".to_owned()));
}

// =============================================================================
// Attribute validation tests
// =============================================================================

#[test]
fn test_validate_attributes_no_conflict() {
    let attrs = vec![DeclAttribute::Simp(None), DeclAttribute::Inline];
    validate_attributes(&attrs).expect("no conflict");
}

#[test]
fn test_validate_attributes_reducible_irreducible_conflict() {
    let attrs = vec![DeclAttribute::Reducible, DeclAttribute::Irreducible];
    let err = validate_attributes(&attrs).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("reducible"), "error: {msg}");
    assert!(msg.contains("irreducible"), "error: {msg}");
}

#[test]
fn test_validate_attributes_specialize_nospecialize_conflict() {
    let attrs = vec![DeclAttribute::Specialize, DeclAttribute::Nospecialize];
    let err = validate_attributes(&attrs).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("specialize"), "error: {msg}");
}

#[test]
fn test_validate_attributes_empty() {
    validate_attributes(&[]).expect("empty is valid");
}

// =============================================================================
// Mutual declaration grouping tests
// =============================================================================

#[test]
fn test_group_mutual_decls_empty() {
    let groups = group_mutual_decls(&[]);
    assert!(groups.is_empty());
}

#[test]
fn test_group_mutual_decls_single() {
    let headers = vec![DeclHeader {
        name: "foo".to_owned(),
        kind: MutualDeclKind::Def,
    }];
    let groups = group_mutual_decls(&headers);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0], vec![0]);
}

#[test]
fn test_group_mutual_decls_consecutive_same_kind() {
    let headers = vec![
        DeclHeader {
            name: "a".to_owned(),
            kind: MutualDeclKind::Def,
        },
        DeclHeader {
            name: "b".to_owned(),
            kind: MutualDeclKind::Def,
        },
        DeclHeader {
            name: "c".to_owned(),
            kind: MutualDeclKind::Def,
        },
    ];
    let groups = group_mutual_decls(&headers);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0], vec![0, 1, 2]);
}

#[test]
fn test_group_mutual_decls_alternating_kinds() {
    let headers = vec![
        DeclHeader {
            name: "a".to_owned(),
            kind: MutualDeclKind::Def,
        },
        DeclHeader {
            name: "b".to_owned(),
            kind: MutualDeclKind::Theorem,
        },
        DeclHeader {
            name: "c".to_owned(),
            kind: MutualDeclKind::Inductive,
        },
    ];
    let groups = group_mutual_decls(&headers);
    assert_eq!(groups.len(), 3);
    assert_eq!(groups[0], vec![0]);
    assert_eq!(groups[1], vec![1]);
    assert_eq!(groups[2], vec![2]);
}

#[test]
fn test_group_mutual_decls_mixed() {
    let headers = vec![
        DeclHeader {
            name: "a".to_owned(),
            kind: MutualDeclKind::Def,
        },
        DeclHeader {
            name: "b".to_owned(),
            kind: MutualDeclKind::Def,
        },
        DeclHeader {
            name: "c".to_owned(),
            kind: MutualDeclKind::Theorem,
        },
        DeclHeader {
            name: "d".to_owned(),
            kind: MutualDeclKind::Theorem,
        },
        DeclHeader {
            name: "e".to_owned(),
            kind: MutualDeclKind::Def,
        },
    ];
    let groups = group_mutual_decls(&headers);
    assert_eq!(groups.len(), 3);
    assert_eq!(groups[0], vec![0, 1]);
    assert_eq!(groups[1], vec![2, 3]);
    assert_eq!(groups[2], vec![4]);
}

// =============================================================================
// Namespace / section scoping tests
// =============================================================================

#[test]
fn test_apply_namespace_prefix_anonymous() {
    let ns = Name::from_string("_root_"); // Anon-like
    let decl = Name::from_string("foo");
    // Non-anon namespace, so prefix is applied
    let result = apply_namespace_prefix(&ns, &decl);
    assert_eq!(result.to_string(), "_root_.foo");
}

#[test]
fn test_apply_namespace_prefix_with_ns() {
    let ns = Name::from_string("Nat");
    let decl = Name::from_string("add");
    let result = apply_namespace_prefix(&ns, &decl);
    assert_eq!(result.to_string(), "Nat.add");
}

#[test]
fn test_section_variable_names_passthrough() {
    let vars = vec!["alpha".to_owned(), "n".to_owned()];
    let ns = Name::from_string("MySection");
    let result = section_variable_names(&vars, &ns);
    assert_eq!(result, vars);
}

// =============================================================================
// Deferred elaboration tests
// =============================================================================

#[test]
fn test_deferral_queue_new_is_empty() {
    let q = DeferralQueue::new();
    assert!(q.is_empty());
    assert_eq!(q.len(), 0);
}

#[test]
fn test_deferral_queue_defer_and_drain() {
    let mut q = DeferralQueue::new();
    let id0 = q.defer(
        Name::from_string("foo"),
        DeferralReason::ForwardReference("bar".to_owned()),
    );
    let id1 = q.defer(Name::from_string("baz"), DeferralReason::InstanceResolution);

    assert_eq!(q.len(), 2);
    assert!(!q.is_empty());
    assert_eq!(id0, 0);
    assert_eq!(id1, 1);

    let cmds = q.drain();
    assert_eq!(cmds.len(), 2);
    assert!(q.is_empty());
    assert_eq!(cmds[0].name, Name::from_string("foo"));
    assert_eq!(cmds[1].reason, DeferralReason::InstanceResolution);
}

#[test]
fn test_deferral_queue_is_deferred() {
    let mut q = DeferralQueue::new();
    q.defer(Name::from_string("x"), DeferralReason::Explicit);
    assert!(q.is_deferred(&Name::from_string("x")));
    assert!(!q.is_deferred(&Name::from_string("y")));
}

// =============================================================================
// Error recovery tests
// =============================================================================

#[test]
fn test_recovered_result_all_succeed() {
    let result = elaborate_with_recovery(3, |_| Ok(()));
    assert!(result.all_succeeded());
    assert_eq!(result.total(), 3);
    assert_eq!(result.failure_count(), 0);
    assert_eq!(result.succeeded, vec![0, 1, 2]);
}

#[test]
fn test_recovered_result_some_failures() {
    let result = elaborate_with_recovery(4, |i| {
        if i % 2 == 0 {
            Ok(())
        } else {
            Err(ElabError::NotImplemented(format!("fail at {i}")))
        }
    });
    assert!(!result.all_succeeded());
    assert_eq!(result.total(), 4);
    assert_eq!(result.succeeded, vec![0, 2]);
    assert_eq!(result.failure_count(), 2);
    assert_eq!(result.failures[0].0, 1);
    assert_eq!(result.failures[1].0, 3);
}

#[test]
fn test_recovered_result_all_fail() {
    let result = elaborate_with_recovery(2, |_| Err(ElabError::CannotInfer));
    assert_eq!(result.failure_count(), 2);
    assert!(result.succeeded.is_empty());
}

#[test]
fn test_recovered_result_zero_commands() {
    let result = elaborate_with_recovery(0, |_| Ok(()));
    assert!(result.all_succeeded());
    assert_eq!(result.total(), 0);
}

// =============================================================================
// Doc comment tests
// =============================================================================

#[test]
fn test_doc_comment_registry_empty() {
    let reg = DocCommentRegistry::new();
    assert!(reg.is_empty());
    assert_eq!(reg.len(), 0);
    assert!(reg.get(&Name::from_string("foo")).is_none());
}

#[test]
fn test_doc_comment_attach_and_get() {
    let mut reg = DocCommentRegistry::new();
    reg.attach(
        Name::from_string("Nat.add"),
        "Addition on natural numbers.".to_owned(),
    );
    assert_eq!(reg.len(), 1);
    assert_eq!(
        reg.get(&Name::from_string("Nat.add")),
        Some("Addition on natural numbers.")
    );
}

#[test]
fn test_doc_comment_latest_wins() {
    let mut reg = DocCommentRegistry::new();
    reg.attach(Name::from_string("foo"), "first".to_owned());
    reg.attach(Name::from_string("foo"), "second".to_owned());
    assert_eq!(reg.get(&Name::from_string("foo")), Some("second"));
    assert_eq!(reg.len(), 2); // both stored, latest returned
}

// =============================================================================
// Command trace tests
// =============================================================================

#[test]
fn test_command_trace_empty() {
    let trace = CommandTrace::new();
    assert!(trace.is_empty());
    assert_eq!(trace.len(), 0);
}

#[test]
fn test_command_trace_log_and_entries() {
    let mut trace = CommandTrace::new();
    trace.log(Name::from_string("foo"), "elaborated def");
    trace.log(Name::from_string("bar"), "elaborated theorem");
    assert_eq!(trace.len(), 2);
    assert_eq!(trace.entries()[0].message, "elaborated def");
    assert_eq!(trace.entries()[1].name, Name::from_string("bar"));
}

#[test]
fn test_command_trace_clear() {
    let mut trace = CommandTrace::new();
    trace.log(Name::from_string("x"), "msg");
    assert!(!trace.is_empty());
    trace.clear();
    assert!(trace.is_empty());
}

// =============================================================================
// Visibility tests
// =============================================================================

#[test]
fn test_visibility_default_is_public() {
    let vis = Visibility::default();
    assert_eq!(vis, Visibility::Public);
}

#[test]
fn test_validate_visibility_all_combos() {
    for vis in [
        Visibility::Public,
        Visibility::Protected,
        Visibility::Private,
    ] {
        validate_visibility(vis, "def").expect("should be valid");
        validate_visibility(vis, "theorem").expect("should be valid");
        validate_visibility(vis, "inductive").expect("should be valid");
    }
}

// =============================================================================
// Noncomputable handling tests
// =============================================================================

#[test]
fn test_is_noncomputable_explicit_true() {
    assert!(is_noncomputable_explicit(true));
}

#[test]
fn test_is_noncomputable_explicit_false() {
    assert!(!is_noncomputable_explicit(false));
}

// =============================================================================
// Ordering validation tests
// =============================================================================

#[test]
fn test_validate_ordering_all_present() {
    let decl = Name::from_string("c");
    let deps = vec![Name::from_string("a"), Name::from_string("b")];
    let elaborated = vec![Name::from_string("a"), Name::from_string("b")];
    validate_ordering(&decl, &deps, &elaborated).expect("all deps present");
}

#[test]
fn test_validate_ordering_missing_dep() {
    let decl = Name::from_string("c");
    let deps = vec![Name::from_string("a"), Name::from_string("missing")];
    let elaborated = vec![Name::from_string("a")];
    let err = validate_ordering(&decl, &deps, &elaborated).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("missing"), "error: {msg}");
    assert!(msg.contains("c"), "error should mention decl name: {msg}");
}

#[test]
fn test_validate_ordering_no_deps() {
    let decl = Name::from_string("x");
    validate_ordering(&decl, &[], &[]).expect("no deps always valid");
}

// =============================================================================
// Config tests
// =============================================================================

#[test]
fn test_config_default() {
    let cfg = CommandElabExtConfig::default();
    assert!(cfg.error_recovery);
    assert!(!cfg.tracing);
    assert!(cfg.validate_ordering);
    assert_eq!(cfg.max_deferred, 256);
}

#[test]
fn test_config_custom() {
    let cfg = CommandElabExtConfig {
        error_recovery: false,
        tracing: true,
        validate_ordering: false,
        max_deferred: 64,
    };
    assert!(!cfg.error_recovery);
    assert!(cfg.tracing);
    assert!(!cfg.validate_ordering);
    assert_eq!(cfg.max_deferred, 64);
}
