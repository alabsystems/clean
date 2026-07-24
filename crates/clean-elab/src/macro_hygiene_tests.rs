// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Macro hygiene conformance tests.
//!
//! Verifies: (1) basic macro scoping, (2) nested expansion independence,
//! (3) fresh name uniqueness, (4) quote/antiquote hygiene,
//! (5) recursive expansion without collisions, (6) tactic block hygiene.

use crate::macro_integration::MacroCtx;
use clean_macro::expand::{expand_hygienic, HygienicExpander};
use clean_macro::hygiene::{HygieneContext, HygieneState, MacroScope, ScopedName};
use clean_macro::quotation::SyntaxQuote;
use clean_macro::registry::{MacroDef, MacroRegistry};
use clean_macro::syntax::{Syntax, SyntaxKind};
use std::collections::{BTreeSet, HashSet};
// 1. Basic macro scoping

#[test]
fn test_macro_introduced_var_does_not_capture_outer() {
    let mut registry = MacroRegistry::new();
    let kind = SyntaxKind::app("introMacro");
    let def = MacroDef::new(
        "introMacro",
        kind.clone(),
        Syntax::node(kind.clone(), vec![Syntax::mk_antiquot("body")]),
        SyntaxQuote::term(Syntax::mk_let(
            Syntax::ident("_x"),
            None,
            Syntax::mk_num(1),
            Syntax::mk_antiquot("body"),
        )),
    );
    registry.register(def);

    let input = Syntax::node(kind, vec![Syntax::ident("_x")]);
    let mut expander = HygienicExpander::new(&registry);
    let result = expander.expand(input).unwrap();

    let let_node = find_node_by_kind(&result, "let");
    assert!(let_node.is_some(), "should contain a let node");
    let binder_name = let_node.unwrap().child(0).unwrap().as_ident().unwrap();
    // Hygienic expansion mangles underscore-prefixed names.
    assert_ne!(binder_name, "_x", "macro-introduced _x should be mangled");
    assert!(
        binder_name.starts_with("_x"),
        "mangled name should preserve _x prefix"
    );
}

#[test]
fn test_user_binding_unaffected_by_macro_scope() {
    let s1 = MacroScope::fresh();
    let s2 = MacroScope::fresh();

    let user_x = ScopedName::new("x");
    let macro_x = ScopedName::with_scope("x", s1);
    let macro_x2 = ScopedName::with_scope("x", s2);

    assert!(!user_x.binds_same_as(&macro_x), "user vs macro scope");
    assert!(!macro_x.binds_same_as(&macro_x2), "different expansions");
    assert!(
        user_x.binds_same_as(&ScopedName::new("x")),
        "identical unscoped names"
    );
}

#[test]
fn test_non_fresh_names_pass_through_unhygiened() {
    let mut registry = MacroRegistry::new();
    let kind = SyntaxKind::app("passThrough");
    let def = MacroDef::new(
        "passThrough",
        kind.clone(),
        Syntax::node(kind.clone(), vec![]),
        SyntaxQuote::term(Syntax::ident("regularName")),
    );
    registry.register(def);

    let result = expand_hygienic(&registry, Syntax::node(kind, vec![])).unwrap();
    assert_eq!(result.as_ident(), Some("regularName"));
}
// 2. Nested macro expansion

#[test]
fn test_nested_expansions_get_distinct_scopes() {
    let mut registry = MacroRegistry::new();
    let kind = SyntaxKind::app("genFresh");
    let def = MacroDef::new(
        "genFresh",
        kind.clone(),
        Syntax::node(kind.clone(), vec![]),
        SyntaxQuote::term(Syntax::ident("_tmp")),
    );
    registry.register(def);

    let mut expander = HygienicExpander::new(&registry);
    let r1 = expander.expand(Syntax::node(kind.clone(), vec![])).unwrap();
    let r2 = expander.expand(Syntax::node(kind, vec![])).unwrap();

    let n1 = r1.as_ident().unwrap();
    let n2 = r2.as_ident().unwrap();
    assert_ne!(n1, n2, "consecutive expansions must yield distinct names");
    assert!(n1.starts_with("_tmp"));
    assert!(n2.starts_with("_tmp"));
}

#[test]
fn test_nested_macro_in_macro_body() {
    let mut registry = MacroRegistry::new();

    let kind_inner = SyntaxKind::app("inner");
    let def_inner = MacroDef::new(
        "inner",
        kind_inner.clone(),
        Syntax::node(kind_inner.clone(), vec![]),
        SyntaxQuote::term(Syntax::ident("_y")),
    );
    registry.register(def_inner);

    let kind_outer = SyntaxKind::app("outer");
    let def_outer = MacroDef::new(
        "outer",
        kind_outer.clone(),
        Syntax::node(kind_outer.clone(), vec![]),
        SyntaxQuote::term(Syntax::mk_let(
            Syntax::ident("_x"),
            None,
            Syntax::node(kind_inner, vec![]),
            Syntax::ident("_x"),
        )),
    );
    registry.register(def_outer);

    let mut expander = HygienicExpander::new(&registry);
    let result = expander.expand(Syntax::node(kind_outer, vec![])).unwrap();

    assert!(
        expander.stats().expansions >= 2,
        "should expand both macros"
    );
    let names = collect_ident_names(&result);
    assert!(
        !names.contains(&"_x".to_string()),
        "plain _x should be mangled"
    );
    assert!(
        !names.contains(&"_y".to_string()),
        "plain _y should be mangled"
    );
    assert!(names.iter().any(|n| n.starts_with("_x")), "has mangled _x");
    assert!(names.iter().any(|n| n.starts_with("_y")), "has mangled _y");
}

#[test]
fn test_scope_depth_increases_with_nesting() {
    let mut state = HygieneState::new();
    let s1 = state.push_scope();
    let s2 = state.push_scope();
    let s3 = state.push_scope();
    assert_eq!(state.depth(), 3);

    assert_ne!(s1, s2);
    assert_ne!(s2, s3);
    let scopes = state.current_scopes();
    assert!(scopes.contains(&s1) && scopes.contains(&s2) && scopes.contains(&s3));

    state.pop_scope();
    state.pop_scope();
    state.pop_scope();
    assert_eq!(state.depth(), 0);
}

// 3. Fresh name generation

#[test]
fn test_gensym_produces_unique_names() {
    let mut state = HygieneState::new();
    let _ = state.push_scope();

    let mut seen = HashSet::new();
    for _ in 0..100 {
        let name = state.gensym("_v");
        assert!(seen.insert(name.mangled()), "gensym must be unique");
    }
}

#[test]
fn test_fresh_ident_across_scopes() {
    let mut state = HygieneState::new();

    let s1 = state.push_scope();
    let n1 = state.fresh_ident("_temp");
    state.pop_scope();

    let _s2 = state.push_scope();
    let n2 = state.fresh_ident("_temp");
    state.pop_scope();

    assert!(!n1.binds_same_as(&n2));
    assert!(n1.has_scope(s1));
    assert!(!n2.has_scope(s1));
}

#[test]
fn test_hygiene_context_fresh_counter() {
    let mut ctx = HygieneContext::new();
    let generated: Vec<_> = (0..50).map(|_| ctx.fresh("_var")).collect();
    let unique: HashSet<_> = generated.iter().collect();
    assert_eq!(unique.len(), 50, "all 50 generated names should be unique");
}

#[test]
fn test_hygienic_expander_fresh_ident_uniqueness() {
    let registry = MacroRegistry::new();
    let mut expander = HygienicExpander::new(&registry);

    let mut idents = HashSet::new();
    for _ in 0..20 {
        assert!(
            idents.insert(expander.fresh_ident("_f")),
            "fresh_ident must be unique"
        );
    }
}

// 4. Quote/antiquote hygiene

#[test]
fn test_antiquot_spliced_names_preserve_identity() {
    let mut registry = MacroRegistry::new();
    let kind = SyntaxKind::app("wrapMacro");
    let def = MacroDef::new(
        "wrapMacro",
        kind.clone(),
        Syntax::node(kind.clone(), vec![Syntax::mk_antiquot("x")]),
        SyntaxQuote::term(Syntax::mk_paren(Syntax::mk_antiquot("x"))),
    );
    registry.register(def);

    let input = Syntax::node(kind, vec![Syntax::ident("myVar")]);
    let result = expand_hygienic(&registry, input).unwrap();
    assert!(
        result.pretty().contains("myVar"),
        "spliced name should be preserved"
    );
}

#[test]
fn test_quoted_template_fresh_names_are_scoped() {
    let mut registry = MacroRegistry::new();
    let kind = SyntaxKind::app("quoteMacro");
    let def = MacroDef::new(
        "quoteMacro",
        kind.clone(),
        Syntax::node(kind.clone(), vec![Syntax::mk_antiquot("body")]),
        SyntaxQuote::term(Syntax::mk_app(
            Syntax::ident("_fresh"),
            vec![Syntax::mk_antiquot("body")],
        )),
    );
    registry.register(def);

    let input = Syntax::node(kind, vec![Syntax::ident("arg")]);
    let result = expand_hygienic(&registry, input).unwrap();

    let names = collect_ident_names(&result);
    assert!(names.iter().any(|n| n.starts_with("_fresh")));
    assert!(
        !names.contains(&"_fresh".to_string()),
        "_fresh should be mangled"
    );
    assert!(
        names.contains(&"arg".to_string()),
        "arg should be preserved"
    );
}

#[test]
fn test_multiple_antiquots_preserve_all_spliced_names() {
    let mut registry = MacroRegistry::new();
    let kind = SyntaxKind::app("multiSplice");
    let def = MacroDef::new(
        "multiSplice",
        kind.clone(),
        Syntax::node(
            kind.clone(),
            vec![Syntax::mk_antiquot("a"), Syntax::mk_antiquot("b")],
        ),
        SyntaxQuote::term(Syntax::mk_app(
            Syntax::mk_antiquot("a"),
            vec![Syntax::mk_antiquot("b")],
        )),
    );
    registry.register(def);

    let input = Syntax::node(kind, vec![Syntax::ident("foo"), Syntax::ident("bar")]);
    let result = expand_hygienic(&registry, input).unwrap();
    let names = collect_ident_names(&result);
    assert!(names.contains(&"foo".to_string()));
    assert!(names.contains(&"bar".to_string()));
}

// 5. Recursive macro expansion

#[test]
fn test_recursive_expansion_no_collision() {
    let mut registry = MacroRegistry::new();
    let kind_a = SyntaxKind::app("chainA");
    let kind_b = SyntaxKind::app("chainB");

    let def_a = MacroDef::new(
        "chainA",
        kind_a.clone(),
        Syntax::node(kind_a.clone(), vec![Syntax::mk_antiquot("x")]),
        SyntaxQuote::term(Syntax::mk_let(
            Syntax::ident("_step"),
            None,
            Syntax::mk_antiquot("x"),
            Syntax::node(kind_b.clone(), vec![Syntax::ident("_step")]),
        )),
    );
    registry.register(def_a);

    let def_b = MacroDef::new(
        "chainB",
        kind_b.clone(),
        Syntax::node(kind_b, vec![Syntax::mk_antiquot("y")]),
        SyntaxQuote::term(Syntax::mk_let(
            Syntax::ident("_step"),
            None,
            Syntax::mk_antiquot("y"),
            Syntax::ident("_step"),
        )),
    );
    registry.register(def_b);

    let mut expander = HygienicExpander::new(&registry);
    let result = expander
        .expand(Syntax::node(kind_a, vec![Syntax::mk_num(42)]))
        .unwrap();

    let names = collect_ident_names(&result);
    let step_names: HashSet<_> = names.iter().filter(|n| n.starts_with("_step")).collect();
    // chainA and chainB each introduce _step; hygiene must give them distinct manglings.
    assert!(
        step_names.len() >= 2,
        "need >= 2 distinct _step names: {step_names:?}"
    );
}

#[test]
fn test_expansion_depth_tracked() {
    let mut registry = MacroRegistry::new();
    let kind = SyntaxKind::app("depthTest");
    let def = MacroDef::new(
        "depthTest",
        kind.clone(),
        Syntax::node(kind.clone(), vec![]),
        SyntaxQuote::term(Syntax::ident("done")),
    );
    registry.register(def);

    let mut expander = HygienicExpander::new(&registry);
    let _ = expander.expand(Syntax::node(kind, vec![])).unwrap();
    assert!(expander.stats().max_depth >= 1);
    assert_eq!(expander.stats().expansions, 1);
}

// 6. Macros in tactic blocks maintain hygiene

#[test]
fn test_tactic_macro_hygiene() {
    let mut registry = MacroRegistry::new();
    let kind = SyntaxKind::tactic();

    let def = MacroDef::new(
        "tacticIntroFresh",
        kind.clone(),
        Syntax::node(kind.clone(), vec![Syntax::mk_antiquot("goal")]),
        SyntaxQuote::tactic(Syntax::mk_app(
            Syntax::ident("_h"),
            vec![Syntax::mk_antiquot("goal")],
        )),
    );
    registry.register(def);

    let mut expander = HygienicExpander::new(&registry);
    let r1 = expander
        .expand(Syntax::node(kind.clone(), vec![Syntax::ident("target")]))
        .unwrap();
    let r2 = expander
        .expand(Syntax::node(kind, vec![Syntax::ident("target2")]))
        .unwrap();

    let h1: Vec<_> = collect_ident_names(&r1)
        .into_iter()
        .filter(|n| n.starts_with("_h"))
        .collect();
    let h2: Vec<_> = collect_ident_names(&r2)
        .into_iter()
        .filter(|n| n.starts_with("_h"))
        .collect();

    assert!(!h1.is_empty(), "first tactic should have _h-derived name");
    assert!(!h2.is_empty(), "second tactic should have _h-derived name");
    assert_ne!(h1.first(), h2.first(), "tactic _h names should differ");
}

#[test]
fn test_tactic_block_quote_category() {
    let quote = SyntaxQuote::tactic(Syntax::ident("skip"));
    assert_eq!(quote.category, SyntaxKind::tactic());
}

#[test]
fn test_macro_ctx_hygienic_mode_toggle() {
    let mut ctx = MacroCtx::new();
    let kind = SyntaxKind::if_then_else();
    let syntax = Syntax::node(
        kind,
        vec![
            Syntax::ident("cond"),
            Syntax::ident("thenBr"),
            Syntax::ident("elseBr"),
        ],
    );

    let result_hygienic = ctx.expand(syntax.clone()).unwrap();
    ctx.set_hygienic(false);
    let result_non_hygienic = ctx.expand(syntax).unwrap();

    assert!(result_hygienic.is_node());
    assert!(result_non_hygienic.is_node());
}

#[test]
fn test_macro_ctx_expansion_records_stats() {
    let mut ctx = MacroCtx::new();
    let syntax = Syntax::node(
        SyntaxKind::if_then_else(),
        vec![Syntax::ident("c"), Syntax::ident("t"), Syntax::ident("e")],
    );
    let _ = ctx.expand(syntax).unwrap();
    assert!(ctx.last_stats().unwrap().expansions >= 1);
}
#[test]
fn test_scope_guard_auto_pops() {
    let mut ctx = HygieneContext::new();
    let scope;
    {
        let guard = ctx.enter_scope();
        scope = guard.scope();
    }
    assert_eq!(ctx.state().depth(), 0);
    assert!(!scope.is_root());
}

#[test]
fn test_scoped_name_mangling_deterministic() {
    let s = MacroScope::fresh();
    assert_eq!(
        ScopedName::with_scope("_v", s).mangled(),
        ScopedName::with_scope("_v", s).mangled(),
    );
}

#[test]
fn test_scoped_name_multiple_scopes_mangling() {
    let mut scopes = BTreeSet::new();
    scopes.insert(MacroScope::fresh());
    scopes.insert(MacroScope::fresh());
    let mangled = ScopedName::with_scopes("_v", scopes).mangled();
    assert!(mangled.starts_with("_v"));
    assert!(mangled.len() > "_v".len(), "should have scope suffix");
}

#[test]
fn test_introduced_names_tracking() {
    let mut state = HygieneState::new();
    let _ = state.push_scope();
    let _ = state.fresh_ident("_a");
    let _ = state.fresh_ident("_b");
    let _ = state.fresh_ident("_c");
    assert_eq!(state.introduced_names().len(), 3);
    state.clear_introduced();
    assert_eq!(state.introduced_names().len(), 0);
}

fn find_node_by_kind<'a>(syntax: &'a Syntax, kind_name: &str) -> Option<&'a Syntax> {
    if syntax.kind().map(|k| k.name_str()) == Some(kind_name) {
        return Some(syntax);
    }
    syntax
        .children()
        .iter()
        .find_map(|c| find_node_by_kind(c, kind_name))
}

fn collect_ident_names(syntax: &Syntax) -> Vec<String> {
    let mut names = Vec::new();
    collect_ident_names_inner(syntax, &mut names);
    names
}

fn collect_ident_names_inner(syntax: &Syntax, out: &mut Vec<String>) {
    if let Some(name) = syntax.as_ident() {
        out.push(name.to_string());
    }
    for child in syntax.children() {
        collect_ident_names_inner(child, out);
    }
}
