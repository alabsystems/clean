// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::{Declaration, Name};
use clean_parser::{parse_name, SurfaceName};

fn state_with_names(names: &[Name]) -> ProofState {
    let mut env = Environment::new();
    for name in names {
        env.add_decl_structural(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("resolver fixture declaration registers");
    }
    let mut state = ProofState::new(env, Expr::prop());
    let mut namespace = crate::namespace::NamespaceState::new();
    namespace.enter_namespace(Name::anon().str("A"));
    state.set_namespace_state(namespace);
    state
}

#[test]
fn namespace_resolution_keeps_atomic_dots_and_hierarchical_components_distinct() {
    let root = Name::anon().str("h");
    let relative = Name::anon().str("A").str("h");
    let atomic = Name::anon().str("A").str("x.y");
    let hierarchical = Name::anon().str("A").str("x").str("y");
    let state = state_with_names(&[root, relative.clone(), atomic.clone(), hierarchical.clone()]);
    assert_eq!(
        resolve_global_name(&state, &parse_name("h").unwrap()).unwrap(),
        relative
    );
    assert_eq!(
        resolve_global_name(&state, &parse_name("«x.y»").unwrap()).unwrap(),
        atomic
    );
    assert_eq!(
        resolve_global_name(&state, &parse_name("x.y").unwrap()).unwrap(),
        hierarchical
    );
    assert_ne!(atomic, hierarchical);
}

#[test]
fn root_selector_is_lexical_and_relative_selectors_do_not_fall_back_to_globals() {
    let root = Name::anon().str("h");
    let literal_root = Name::anon().str("A").str("_root_").str("h");
    let literal_dot = Name::anon().str("A").str(".h");
    let state = state_with_names(&[root.clone(), literal_root.clone(), literal_dot.clone()]);
    assert_eq!(
        resolve_global_name(&state, &parse_name("_root_.h").unwrap()).unwrap(),
        root
    );
    assert_eq!(
        resolve_global_name(&state, &parse_name("«_root_».h").unwrap()).unwrap(),
        literal_root
    );
    let generated_root = SurfaceName::from_name(Name::anon().str("_root_").str("h"));
    assert_eq!(
        resolve_global_name(&state, &generated_root).unwrap(),
        literal_root
    );
    assert_eq!(
        resolve_global_name(&state, &parse_name("«.h»").unwrap()).unwrap(),
        literal_dot
    );
    assert!(resolve_global_name(
        &state,
        &SurfaceName::component("h", false).with_relative_constructor()
    )
    .is_err());
    assert!(resolve_global_name(&state, &SurfaceName::default()).is_err());
}

#[test]
fn typed_global_resolution_keeps_numeric_and_textual_components_distinct() {
    let numeric = Name::anon().str("A").num(7);
    let textual = Name::anon().str("A").str("7");
    let state = state_with_names(&[numeric.clone(), textual.clone()]);
    assert_eq!(
        resolve_global_name(&state, &SurfaceName::from_name(Name::anon().num(7))).unwrap(),
        numeric
    );
    assert_eq!(
        resolve_global_name(&state, &parse_name("«7»").unwrap()).unwrap(),
        textual
    );
    assert_ne!(numeric, textual);
}
