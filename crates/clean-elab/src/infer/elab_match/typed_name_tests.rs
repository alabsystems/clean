// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use crate::FileContext;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{Declaration, Environment};
use clean_parser::{parse_name, Span, SurfaceMatchArm};

fn source_name(text: &str) -> SurfaceName {
    parse_name(text).expect("actual source name parses")
}

fn add_enum(env: &mut Environment, owner: Name, components: &[Name]) {
    let owner_surface = SurfaceName::from_name(owner.clone());
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: owner.clone(),
            type_: Expr::type_(),
            constructors: components
                .iter()
                .map(|component| Constructor {
                    name: owner_surface
                        .append(&SurfaceName::from_name(component.clone()))
                        .into_name(),
                    type_: Expr::const_(owner.clone(), vec![]),
                })
                .collect(),
        }],
    })
    .expect("real kernel registers the typed inductive");
}

fn check(source: &str) -> (Environment, crate::module_batch::ModuleOutcome) {
    let declarations = clean_parser::parse_file(source).expect("actual source parses");
    let mut env = Environment::new();
    let mut file = FileContext::new();
    let outcome = elaborate_module(
        &mut env,
        &mut file,
        &[SourceUnit {
            id: UnitId(0),
            decls: &declarations,
        }],
        BatchOptions::islands(),
    );
    (env, outcome)
}

fn accepted(source: &str) -> Environment {
    let (env, outcome) = check(source);
    assert!(
        outcome.is_clean() && outcome.committed,
        "{}",
        outcome.render_rejections()
    );
    env
}

#[test]
fn constructor_resolution_keeps_quoted_dots_and_numeric_components_distinct() {
    let mut env = Environment::new();
    let owner = Name::anon().str("A.B");
    let nested_owner = Name::anon().str("A").str("B");
    let components = [
        Name::anon().str("c.d"),
        Name::anon().str("7"),
        Name::anon().num(7),
    ];
    add_enum(&mut env, owner.clone(), &components);
    add_enum(&mut env, nested_owner.clone(), &components);
    let ctx = ElabCtx::new(&env);
    let ty = SurfaceName::from_name(owner.clone());
    assert_eq!(
        ctx.resolve_ctor_name(&source_name("«c.d»"), &ty)
            .unwrap()
            .name(),
        &owner.clone().str("c.d")
    );
    assert!(ctx.resolve_ctor_name(&source_name("c.d"), &ty).is_none());
    assert!(ctx
        .resolve_ctor_name(&source_name("A.B.«c.d»"), &ty)
        .is_none());
    assert_eq!(
        ctx.resolve_ctor_name(&source_name("«7»"), &ty)
            .unwrap()
            .name(),
        &owner.clone().str("7")
    );
    assert_eq!(
        ctx.resolve_ctor_name(&SurfaceName::from_name(Name::anon().num(7)), &ty)
            .unwrap()
            .name(),
        &owner.num(7)
    );
}

#[test]
fn constructor_alias_and_root_selector_cannot_rescue_a_different_identity() {
    let mut env = Environment::new();
    let owner = Name::anon().str("M").str("T");
    add_enum(
        &mut env,
        owner.clone(),
        &[Name::anon().str("C"), Name::anon().str("c")],
    );
    add_enum(
        &mut env,
        Name::anon().str("Other"),
        &[Name::anon().str("C")],
    );
    let mut ctx = ElabCtx::new(&env);
    ctx.namespace_state
        .insert_alias_pub(Name::anon().str("alias.dot"), owner.clone().str("C"));
    ctx.namespace_state.insert_alias_pub(
        Name::anon().str("wrong"),
        Name::anon().str("Other").str("C"),
    );
    let ty = SurfaceName::from_name(owner.clone());
    assert_eq!(
        ctx.resolve_ctor_name(&source_name("«alias.dot»"), &ty)
            .unwrap()
            .name(),
        &owner.clone().str("C")
    );
    for wrong in [
        "alias.dot",
        "wrong",
        "Other.C",
        "_root_.T.C",
        "_root_.«alias.dot»",
    ] {
        assert!(
            ctx.resolve_ctor_name(&source_name(wrong), &ty).is_none(),
            "{wrong}"
        );
    }
    for (written, component) in [("T.C", "C"), ("T.c", "c"), ("_root_.M.T.C", "C")] {
        assert_eq!(
            ctx.resolve_ctor_name(&source_name(written), &ty)
                .unwrap()
                .name(),
            &owner.clone().str(component)
        );
    }
}

#[test]
fn relative_constructor_selector_is_not_a_quoted_leading_dot() {
    let mut env = Environment::new();
    let owner = Name::anon().str("T");
    add_enum(
        &mut env,
        owner.clone(),
        &[Name::anon().str("C"), Name::anon().str(".C")],
    );
    let ctx = ElabCtx::new(&env);
    let ty = SurfaceName::from_name(owner.clone());
    let relative = source_name("C").with_relative_constructor();
    assert_eq!(
        ctx.resolve_ctor_name(&relative, &ty).unwrap().name(),
        &owner.clone().str("C")
    );
    assert_eq!(
        ctx.resolve_ctor_name(&source_name("«.C»"), &ty)
            .unwrap()
            .name(),
        &owner.str(".C")
    );
}

#[test]
fn anonymous_generated_name_cannot_select_a_sole_constructor_by_empty_suffix() {
    let mut env = Environment::new();
    let owner = Name::anon().str("T");
    add_enum(&mut env, owner.clone(), &[Name::anon().str("C")]);
    let ctx = ElabCtx::new(&env);
    let ty = SurfaceName::from_name(owner);
    assert!(ctx.resolve_ctor_name(&source_name("C"), &ty).is_some());
    for name in [
        SurfaceName::default(),
        SurfaceName::default().with_relative_constructor(),
    ] {
        assert!(ctx.resolve_ctor_name(&name, &ty).is_none());
    }
}

#[test]
fn generated_induction_hypotheses_keep_source_component_boundaries() {
    assert_eq!(
        generated_prefixed_name("ih_", &source_name("x")).name(),
        &Name::anon().str("ih_x")
    );
    assert_eq!(
        generated_prefixed_name("ih_", &source_name("«x.y»")).name(),
        &Name::anon().str("ih_x.y")
    );
    assert_ne!(
        generated_prefixed_name("ih_", &source_name("«x.y»")),
        generated_prefixed_name("ih_", &source_name("x.y"))
    );
    assert_ne!(
        generated_prefixed_name("ih_", &source_name("«7»")),
        generated_prefixed_name("ih_", &SurfaceName::from_name(Name::anon().num(7)))
    );
}

#[test]
fn nested_mutual_arm_requires_the_exact_container_or_its_own_mirror() {
    let mut env = Environment::new();
    let primary_name = Name::anon().str("Tree");
    let container_name = Name::anon().str("M").str("List");
    let ctor = Name::anon().str("C");
    add_enum(&mut env, primary_name.clone(), std::slice::from_ref(&ctor));
    add_enum(
        &mut env,
        container_name.clone(),
        std::slice::from_ref(&ctor),
    );
    add_enum(
        &mut env,
        Name::anon().str("Other").str("List"),
        std::slice::from_ref(&ctor),
    );
    add_enum(
        &mut env,
        primary_name.clone().str("_List"),
        std::slice::from_ref(&ctor),
    );
    add_enum(&mut env, Name::anon().str("Other").str("_List"), &[ctor]);
    let mut ctx = ElabCtx::new(&env);
    ctx.nested_mutual_aux_arms = Some(NestedMutualAuxArms {
        container_name: SurfaceName::from_name(container_name.clone()),
        arms: vec![SurfaceMatchArm {
            span: Span::dummy(),
            pattern: SurfacePattern::Ctor(source_name("M.List.C"), vec![]),
            body: typed_ident(source_name("Tree.C")),
        }],
        sibling_signatures: vec![],
    });
    let primary = env.get_inductive(&primary_name).unwrap();
    assert!(ctx
        .resolve_nested_mutual_aux_arm(&container_name.str("C"), primary)
        .is_some());
    assert!(ctx
        .resolve_nested_mutual_aux_arm(&primary_name.str("_List").str("C"), primary)
        .is_some());
    for wrong in ["Other.List.C", "Other._List.C", "M.List.c"] {
        assert!(
            ctx.resolve_nested_mutual_aux_arm(source_name(wrong).name(), primary)
                .is_none(),
            "{wrong}"
        );
    }
}

#[test]
fn alias_and_literal_catchall_preserve_escaped_binder_syntax() {
    for spelling in ["«x.y»", "«_»", "«_field_0»"] {
        let name = source_name(spelling);
        let body = typed_ident(name.clone());
        let wrapped = wrap_alias_surface_body(&name, typed_ident(source_name("value")), &body);
        let SurfaceExpr::Let(_, binder, _, _) = wrapped else {
            panic!("alias must bind a let")
        };
        assert!(binder.name.same_syntax(&name));
        let cascade = ElabCtx::build_literal_match_cascade(
            &typed_ident(source_name("value")),
            &[SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Var(name.clone()),
                body,
            }],
        )
        .expect("one exact unqualified binder is a catch-all");
        let SurfaceExpr::Let(_, binder, _, _) = cascade else {
            panic!("catch-all must bind a let")
        };
        assert!(binder.name.same_syntax(&name));
    }
    for name in [
        source_name("x.y"),
        source_name("C").with_relative_constructor(),
    ] {
        assert!(ElabCtx::build_literal_match_cascade(
            &typed_ident(source_name("value")),
            &[SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Var(name),
                body: typed_ident(source_name("value")),
            }]
        )
        .is_none());
    }
}

#[test]
fn anonymous_tuple_marker_cannot_be_authored_as_a_named_constructor() {
    let env = accepted("inductive Data where\n  | make : Data\nstructure Pair where\n  left : Data\n  right : Data\n");
    let ctx = ElabCtx::new(&env);
    let ty = source_name("Pair");
    let expected = Name::anon().str("Pair").str("mk");
    assert_eq!(
        ctx.remap_anonymous_tuple_ctor(&ty, &SurfaceName::generated_path("Prod.mk"), 2)
            .unwrap()
            .name(),
        &expected
    );
    assert!(ctx
        .remap_anonymous_tuple_ctor(&ty, &SurfaceName::generated_path("Prod.mk"), 1)
        .is_none());
    for spelling in ["Prod.mk", "«Prod».mk", "«Prod.mk»"] {
        assert!(
            ctx.remap_anonymous_tuple_ctor(&ty, &source_name(spelling), 2)
                .is_none(),
            "{spelling}"
        );
    }
}

#[test]
fn source_match_uses_exact_constructor_identity_and_registered_order() {
    let env = accepted("inductive Result where\n  | first : Result\n  | second : Result\ninductive «A.B» where\n  | «c.d» : «A.B»\n  | other : «A.B»\ninductive A.B where\n  | «c.d» : A.B\ndef pick (x : «A.B») : Result :=\n  match x with\n  | «A.B».other => Result.second\n  | «A.B».«c.d» => Result.first\n");
    let ctx = ElabCtx::new(&env);
    for (ctor, expected) in [("c.d", "first"), ("other", "second")] {
        let call = Expr::app(
            Expr::const_(Name::anon().str("pick"), vec![]),
            Expr::const_(Name::anon().str("A.B").str(ctor), vec![]),
        );
        assert_eq!(
            ctx.whnf(&call),
            Expr::const_(Name::anon().str("Result").str(expected), vec![])
        );
    }
}

#[test]
fn source_match_rejects_constructor_from_a_different_owner() {
    let (_, outcome) = check("inductive T where\n  | C : T\ninductive Other where\n  | C : Other\ndef bad (x : T) : T :=\n  match x with\n  | Other.C => T.C\n");
    assert!(
        !outcome.is_clean() && !outcome.committed,
        "wrong-owner constructor must not select T.C by suffix"
    );
}

#[test]
fn source_match_checks_owner_with_explicit_and_inferred_result_types() {
    let declarations = "inductive T where\n  | C : T\ninductive Other where\n  | C : Other\ninductive «A.B» where\n  | «c.d» : «A.B»\ninductive A.B where\n  | «c.d» : A.B\n";
    for (owner, valid, wrong) in [
        ("T", "T.C", "Other.C"),
        ("«A.B»", "«A.B».«c.d»", "A.B.«c.d»"),
        ("A.B", "A.B.«c.d»", "«A.B».«c.d»"),
    ] {
        for explicit_type in [false, true] {
            let annotation = if explicit_type {
                format!(": {owner}")
            } else {
                String::new()
            };
            let source = |pattern| {
                format!("{declarations}def pick (x : {owner}) {annotation} :=\n  match x with\n  | {pattern} => {valid}\n")
            };
            let env = accepted(&source(valid));
            let constructor = Expr::const_(source_name(valid).into_name(), vec![]);
            assert_eq!(
                ElabCtx::new(&env).whnf(&Expr::app(
                    Expr::const_(Name::anon().str("pick"), vec![]),
                    constructor.clone(),
                )),
                constructor,
                "{owner}, explicit type {explicit_type}",
            );
            let (_, outcome) = check(&source(wrong));
            assert!(
                !outcome.is_clean() && !outcome.committed,
                "wrong owner {wrong}, explicit type {explicit_type}",
            );
        }
    }
}

#[test]
fn constructor_classification_rejects_wrong_owners_before_coverage_and_nested_binding() {
    let declarations = "inductive T where\n  | C : T\n  | D : T\ninductive Other where\n  | C : Other\n  | box : Other → Other\ninductive Wrap where\n  | mk : T → Wrap\n";
    for body in [
        "def bad (x : T) : T := match x with | Other.C => T.C | T.D => T.D",
        "def bad (x : T) : T := match x with | _root_.Other.C => T.C | _ => T.D",
        "open Other\ndef bad (x : T) : T := match x with | C => T.C | _ => T.D",
        "def bad (x : T) : T := match x with | Other.box _ => T.C | _ => T.D",
        "def bad (x : Wrap) : T := match x with | Wrap.mk Other.C => T.C | Wrap.mk _ => T.D",
        "def bad (x : Wrap) : T := match x with | Wrap.mk (Other.box _) => T.C | Wrap.mk _ => T.D",
        "def bad (x : T) : T := if let Other.C := x then T.C else T.D",
        "def bad (x : T) : T := match x with | Unknown.C => T.C",
    ] {
        let (_, outcome) = check(&format!("{declarations}{body}\n"));
        assert!(!outcome.is_clean() && !outcome.committed, "{body}");
    }
}

#[test]
fn genuine_pattern_binders_preserve_quoted_identity_and_outer_local_shadowing() {
    for binder in ["C", "«Other.C»", "«_root_.Other.C»"] {
        let env = accepted(&format!("inductive T where\n  | C : T\n  | D : T\ninductive Other where\n  | C : Other\ndef copy ({binder} : T) (x : T) : T := match x with | {binder} => {binder}\n"));
        let c = Expr::const_(Name::from_string("T.C"), vec![]);
        let d = Expr::const_(Name::from_string("T.D"), vec![]);
        assert_eq!(
            ElabCtx::new(&env).whnf(&Expr::apps(
                Expr::const_(Name::from_string("copy"), vec![]),
                [c, d.clone()]
            )),
            d,
            "{binder}"
        );
    }
    let env = accepted("inductive T where\n  | C : T\n  | D : T\ninductive Other where\n  | C : Other\ndef copy (x : T) : T := match x with | «Other.C» => «Other.C»\n");
    let d = Expr::const_(Name::from_string("T.D"), vec![]);
    assert_eq!(
        ElabCtx::new(&env).whnf(&Expr::app(
            Expr::const_(Name::from_string("copy"), vec![]),
            d.clone()
        )),
        d
    );
}

#[test]
fn pattern_name_classification_preserves_state_and_refuses_ambiguous_suffixes() {
    let mut env = Environment::new();
    let owner = Name::anon().str("T");
    add_enum(
        &mut env,
        owner.clone(),
        &[
            Name::anon().str("a").str("C"),
            Name::anon().str("b").str("C"),
        ],
    );
    let mut ctx = ElabCtx::new(&env);
    let ty = Expr::const_(owner, vec![]);
    let before = ctx.locals.clone();
    assert!(ctx
        .normalize_match_pattern_names(&SurfacePattern::Var(source_name("C")), &ty)
        .is_err());
    assert_eq!(ctx.locals, before);
    let binder = source_name("«a.C»");
    let fvar = ctx.push_local(binder.clone(), ty.clone());
    let before = ctx.locals.clone();
    let pattern = ctx
        .normalize_match_pattern_names(&SurfacePattern::Var(binder.clone()), &ty)
        .unwrap();
    assert!(matches!(pattern, SurfacePattern::Var(ref name) if name.same_syntax(&binder)));
    assert_eq!(ctx.locals, before);
    assert_eq!(ctx.lookup_local(&binder).unwrap().0, fvar);
}

#[test]
fn pattern_classification_cannot_rescue_inaccessible_constructors_or_rebind_resolved_heads() {
    let mut env = Environment::new();
    let owner = Name::from_string("Ns.T");
    let constructor = owner.clone().str("C");
    add_enum(&mut env, owner.clone(), &[Name::anon().str("C")]);
    env.mark_private(constructor.clone());
    let ty = Expr::const_(owner, vec![]);
    let mut ctx = ElabCtx::new(&env);
    for spelling in ["C", "T.C", "Ns.T.C", "_root_.Ns.T.C"] {
        assert!(
            ctx.normalize_match_pattern_names(&SurfacePattern::Var(source_name(spelling)), &ty)
                .is_err(),
            "{spelling}"
        );
    }
    ctx.namespace_prefix = source_name("Ns.T");
    let normalized = ctx
        .normalize_match_pattern_names(&SurfacePattern::Var(source_name("C")), &ty)
        .unwrap();
    assert!(
        matches!(&normalized, SurfacePattern::Ctor(name, fields) if name.name() == &constructor && fields.is_empty())
    );
    let local_name = SurfaceName::from_name(constructor);
    let local = ctx.push_local(local_name.clone(), ty.clone());
    assert!(ctx.normalize_match_pattern_names(&normalized, &ty).is_err());
    assert_eq!(ctx.lookup_local(&local_name).unwrap().0, local);
}

#[test]
fn native_bool_pattern_aliases_preserve_exact_targets_and_shadowing() {
    let mut env = Environment::with_prelude();
    let bool_type = Expr::const_(Name::anon().str("Bool"), vec![]);
    env.add_decl(Declaration::Definition {
        name: Name::anon().str("Ns").str("true"),
        level_params: vec![],
        type_: bool_type.clone(),
        value: Expr::const_(Name::anon().str("Bool").str("true"), vec![]),
        is_reducible: true,
    })
    .unwrap();
    let mut ctx = ElabCtx::new(&env);
    for component in ["true", "false"] {
        let target = Name::anon().str("Bool").str(component);
        for spelling in [component.to_string(), format!("«{component}»")] {
            let name = source_name(&spelling);
            let normalized = ctx
                .normalize_match_pattern_names(&SurfacePattern::Var(name.clone()), &bool_type)
                .unwrap();
            assert!(matches!(&normalized, SurfacePattern::Ctor(owner, fields)
                if owner.name() == &target && fields.is_empty()));
            assert!(ctx
                .normalize_match_pattern_names(
                    &SurfacePattern::Var(name.clone()),
                    &Expr::const_(Name::anon().str("Nat"), vec![]),
                )
                .is_err());
            let local = ctx.push_local(name.clone(), bool_type.clone());
            let normalized = ctx
                .normalize_match_pattern_names(&SurfacePattern::Var(name.clone()), &bool_type)
                .unwrap();
            assert!(matches!(normalized, SurfacePattern::Var(found) if found.same_syntax(&name)));
            assert_eq!(ctx.lookup_local(&name).unwrap().0, local);
            assert!(ctx
                .normalize_match_pattern_names(&SurfacePattern::Ctor(name, vec![]), &bool_type)
                .is_err());
            ctx.pop_local();
        }
    }
    ctx.namespace_prefix = source_name("Ns");
    let name = source_name("true");
    let normalized = ctx
        .normalize_match_pattern_names(&SurfacePattern::Var(name.clone()), &bool_type)
        .unwrap();
    assert!(matches!(normalized, SurfacePattern::Var(found) if found.same_syntax(&name)));
}

#[test]
fn substituted_native_bool_alias_body_is_not_a_constructor_selector() {
    let mut env = Environment::new();
    add_enum(
        &mut env,
        Name::anon().str("Bool"),
        &[Name::anon().str("false"), Name::anon().str("true")],
    );
    let bool_type = Expr::const_(Name::anon().str("Bool"), vec![]);
    env.add_decl(Declaration::Definition {
        name: Name::anon().str("true"),
        level_params: vec![],
        type_: bool_type.clone(),
        value: Expr::const_(Name::anon().str("Bool").str("false"), vec![]),
        is_reducible: true,
    })
    .unwrap();
    let mut ctx = ElabCtx::new(&env);
    let name = source_name("true");
    let normalized = ctx
        .normalize_match_pattern_names(&SurfacePattern::Var(name.clone()), &bool_type)
        .unwrap();
    assert!(matches!(normalized, SurfacePattern::Var(found) if found.same_syntax(&name)));
    assert!(ctx
        .normalize_match_pattern_names(&SurfacePattern::Ctor(name, vec![]), &bool_type)
        .is_err());
}

#[test]
fn recursive_match_retains_quoted_wildcard_and_generated_looking_binders() {
    for binder in ["«_»", "«x.y»", "«_field_0»"] {
        let env = accepted(&format!("inductive Tree where\n  | leaf : Tree\n  | node : Tree → Tree\ndef copy (t : Tree) : Tree :=\n  match t with\n  | Tree.leaf => Tree.leaf\n  | Tree.node {binder} => Tree.node (copy {binder})\n"));
        let ctx = ElabCtx::new(&env);
        let node = Expr::const_(Name::anon().str("Tree").str("node"), vec![]);
        let leaf = Expr::const_(Name::anon().str("Tree").str("leaf"), vec![]);
        let input = Expr::app(node.clone(), Expr::app(node, leaf));
        let call = Expr::app(
            Expr::const_(Name::anon().str("copy"), vec![]),
            input.clone(),
        );
        assert!(
            ctx.is_def_eq(&call, &input),
            "{binder}: recursive child must not be discarded or captured"
        );
    }
}
