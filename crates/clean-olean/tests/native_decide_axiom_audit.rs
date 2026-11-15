// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The closure audit over a pinned-Lean `native_decide` theorem names the
//! per-use auxiliary axiom Lean adds (plan item `tactics-decide-lean-faithful`
//! (e)).
//!
//! The fixture `tests/fixtures/lean/v4.30.0-rc2/native_decide/` is compiled at
//! test time by the pinned `lean -o` (its README records the recipe and the
//! pinned `#print axioms`). At v4.30.0-rc2 `native_decide` goes through
//! `Lean.Meta.nativeEqTrue`, which adds `<decl>._native.native_decide.ax_N_M :
//! decide p = true` and closes with `of_decide_eq_true p s <axiom>`; it does
//! not mention `Lean.ofReduceBool` (that is the v4.8.0 shape, and v4.35.0
//! deleted the constant). So a native-evaluation audit keyed on
//! `Lean.ofReduceBool` would pass every v4.30 `native_decide` theorem as free
//! of native evaluation. Clean's own audit (`Environment::axiom_deps`, the
//! domain-axiom closure every checker report discloses) must name the
//! auxiliary axiom, and must name nothing for the `decide` control.

use clean_kernel::env::Environment;
use clean_kernel::name::{Name, NameInner};
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    default_search_paths, load_module_with_deps_shared_with_policy, OleanImportPolicy,
};

const FAMILY: &str = "native_decide";
const MODULE: &str = "NativeDecideAux";

/// The fixture module and its imports, loaded through the trusted `.olean`
/// path into Lean's replay environment (as `replay_forged_lanes.rs` does).
fn load() -> Environment {
    let mut env = Environment::for_lean_replay();
    let mut search = vec![compiled_fixture_dir(FAMILY)];
    search.extend(default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    load_module_with_deps_shared_with_policy(
        &mut env,
        MODULE,
        &search,
        &mut visited,
        OleanImportPolicy::default(),
    )
    .unwrap_or_else(|e| panic!("load {MODULE}: {e}"));
    env
}

/// The components of `name`, outermost first; `None` for a numeric one (no
/// component of Lean's auxiliary-axiom shape is numeric).
fn string_components(name: &Name) -> Option<Vec<String>> {
    let mut components = Vec::new();
    let mut current = name;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, component) => {
                components.push(component.to_string());
                current = parent;
            }
            NameInner::Num(..) => return None,
        }
    }
    components.reverse();
    Some(components)
}

/// Lean's shape for the axiom `nativeEqTrue` adds for a use in `decl`:
/// `decl ++ _native ++ native_decide ++ ax_<N>_<M>`, matched component by
/// component (never by printed form).
fn is_native_decide_aux_axiom(axiom: &Name, decl: &str) -> bool {
    let (Some(components), Some(decl_components)) = (
        string_components(axiom),
        string_components(&Name::from_string(decl)),
    ) else {
        return false;
    };
    let Some(rest) = components.strip_prefix(decl_components.as_slice()) else {
        return false;
    };
    match rest {
        [native, tactic, ax] => {
            native == "_native"
                && tactic == "native_decide"
                && ax.strip_prefix("ax_").is_some_and(|tail| {
                    !tail.is_empty() && tail.split('_').all(|n| n.parse::<u64>().is_ok())
                })
        }
        _ => false,
    }
}

#[test]
fn native_decide_closure_names_the_per_use_auxiliary_axiom() {
    let env = load();
    for decl in ["nd_two_add", "nd_beq"] {
        let deps = env
            .axiom_deps(&Name::from_string(decl))
            .unwrap_or_else(|| panic!("{decl} is declared by the fixture"));
        assert_eq!(
            deps.len(),
            1,
            "{decl}: pinned Lean's `#print axioms` names exactly one axiom, got {deps:?}"
        );
        let axiom = deps.iter().next().expect("one axiom");
        assert!(
            is_native_decide_aux_axiom(axiom, decl),
            "{decl}: the audit must name `{decl}._native.native_decide.ax_N_M`, got `{axiom}`"
        );
        assert_eq!(
            axiom.to_string(),
            format!("{decl}._native.native_decide.ax_1_1")
        );
        assert!(
            !deps.contains(&Name::from_string("Lean.ofReduceBool")),
            "{decl}: v4.30 native_decide does not go through Lean.ofReduceBool"
        );
    }
    let control = env
        .axiom_deps(&Name::from_string("dc_two_add"))
        .expect("dc_two_add is declared by the fixture");
    assert!(
        control.is_empty(),
        "`decide` adds no axiom (pinned Lean: does not depend on any axioms), got {control:?}"
    );
}
