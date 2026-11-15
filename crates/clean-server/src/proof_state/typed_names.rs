// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source-selector and response-label boundaries, not serialized proof replay.

use super::*;
use clean_kernel::FVarId;

#[test]
fn obligation_local_source_names_preserve_quoted_and_qualified_twins() {
    let nested = parse_obligation_local_name("A.B").unwrap();
    let atomic = parse_obligation_local_name("«A.B»").unwrap();
    assert_eq!(nested.name(), &Name::anon().str("A").str("B"));
    assert_eq!(atomic.name(), &Name::anon().str("A.B"));
    assert_ne!(nested, atomic);
    assert_eq!(local_name_label(&nested), "A.B");
    assert_eq!(local_name_label(&atomic), "«A.B»");
    for name in [nested, atomic, parse_obligation_local_name("«_»").unwrap()] {
        let reparsed = parse_obligation_local_name(&local_name_label(&name)).unwrap();
        assert!(name.same_syntax(&reparsed));
    }
    for invalid in ["", "_", ".h", "_root_.h", "x + y", "<non-source local>"] {
        assert!(parse_obligation_local_name(invalid).is_none(), "{invalid}");
    }
    assert!(parse_obligation_local_name("«_root_».h").is_some());
    assert!(parse_obligation_local_name("«.h»").is_some());
}

#[test]
fn unspellable_local_names_are_not_reified_as_other_source_names() {
    for name in [
        SurfaceName::from_name(Name::anon().num(7)),
        SurfaceName::default(),
        SurfaceName::component("_", false),
        SurfaceName::generated_path("_"),
        SurfaceName::component("a«b", true),
    ] {
        assert!(local_name_source_spelling(&name).is_none());
        assert!(parse_obligation_local_name(&local_name_label(&name)).is_none());
    }
    let literal = SurfaceName::component("7", true);
    assert_eq!(local_name_label(&literal), "«7»");
    assert_eq!(
        parse_obligation_local_name("«7»").unwrap().name(),
        literal.name()
    );
}

#[test]
fn local_response_preserves_exact_expressions_and_quotes_source_name() {
    let env = Environment::new();
    let local = LocalDecl {
        binder_info: Default::default(),
        fvar: FVarId::new(19),
        name: SurfaceName::component("x+y", true),
        ty: Expr::type_(),
        value: Some(Expr::prop()),
    };
    let response = convert_hypothesis(&local, &env);
    assert_eq!(response.name, "«x+y»");
    assert_eq!(response.type_expr, local.ty);
    assert_eq!(response.value, local.value);
    assert_eq!(summarize_local_decl(&local).name, response.name);
    assert_eq!(local.fvar, FVarId::new(19));
    assert!(parse_obligation_local_name(&response.name)
        .unwrap()
        .same_syntax(&local.name));
}

#[test]
fn generated_rewrite_suggestions_quote_local_names_and_refuse_numeric_labels() {
    let env = Environment::new();
    let equality = Expr::const_(Name::anon().str("Eq"), vec![]);
    let local = LocalDecl {
        binder_info: Default::default(),
        fvar: FVarId::new(0),
        name: SurfaceName::component("h.dot", true),
        ty: equality,
        value: None,
    };
    // Routing/printing fixture only; Eq is not asserted to be a well-typed
    // proposition without its arguments in this bare environment.
    let mut state = InternalProofState::with_elab_context(env.clone(), Expr::prop(), vec![local]);
    let suggestions = suggest_tactics_for_goal_and_profile(
        state.current_goal(),
        &env,
        ObligationDomainProfile::General,
    );
    assert!(suggestions.contains(&"rw [«h.dot»]".to_owned()));
    assert!(!suggestions.contains(&"rw [h.dot]".to_owned()));
    state.current_goal_mut().unwrap().local_ctx[0].name =
        SurfaceName::from_name(Name::anon().num(7));
    let suggestions = suggest_tactics_for_goal_and_profile(
        state.current_goal(),
        &env,
        ObligationDomainProfile::General,
    );
    assert!(!suggestions
        .iter()
        .any(|suggestion| suggestion.starts_with("rw [")));
}

#[test]
fn constant_summary_source_keys_preserve_display_twins() {
    let nested = Name::anon().str("A").str("B");
    let atomic = Name::anon().str("A.B");
    let expression = Expr::app(
        Expr::const_(nested.clone(), vec![]),
        Expr::const_(atomic.clone(), vec![]),
    );
    let symbols = expr_symbols(&expression);
    assert_eq!(symbols.len(), 2);
    assert!(symbols.contains(&"A.B".to_owned()));
    assert!(symbols.contains(&"«A.B»".to_owned()));
    assert_eq!(expr_head_symbol(&expression), Some("A.B".to_owned()));
    assert_eq!(kernel_name_source_spelling(&Name::anon().num(7)), None);
    assert_eq!(kernel_name_source_spelling(&Name::anon()), None);
}
