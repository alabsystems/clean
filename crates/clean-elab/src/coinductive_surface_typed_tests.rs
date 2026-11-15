// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn lower_fixture(source: &str) -> Result<Vec<SurfaceDecl>, ElabError> {
    let declarations = clean_parser::parse_file(source).expect("coinductive fixture parses");
    let [SurfaceDecl::Coinductive {
        name,
        universe_params,
        binders,
        ty,
        ctors,
        deriving,
        modifiers,
        ..
    }] = declarations.as_slice()
    else {
        panic!("expected exactly one coinductive declaration");
    };
    lower(
        name,
        name,
        &Environment::new(),
        universe_params,
        binders,
        ty,
        ctors,
        deriving,
        modifiers,
    )
}

fn generated_name(decl: &SurfaceDecl) -> &SurfaceName {
    match decl {
        SurfaceDecl::Def { name, .. } | SurfaceDecl::Theorem { name, .. } => name,
        _ => panic!("unexpected generated declaration kind"),
    }
}

#[test]
fn coinductive_free_names_and_prefixes_preserve_structural_components() {
    let predicate = SurfaceName::component("P", false);
    let quoted = SurfaceName::component("P.field", true);
    let nested = predicate.append(&SurfaceName::component("field", false));
    assert!(!mentions(&generate::typed_ident(&quoted), &predicate));
    assert!(mentions(&generate::typed_ident(&nested), &predicate));
    let expr = generate::lam_typed(
        std::slice::from_ref(&quoted),
        generate::typed_ident(&quoted),
    );
    let mut bound = Vec::new();
    let mut free = Vec::new();
    all_idents(&expr, &mut bound, &mut free).expect("typed lambda");
    assert!(free.is_empty());
    let expr = generate::lam_typed(
        std::slice::from_ref(&quoted),
        generate::typed_ident(&nested),
    );
    let mut bound = Vec::new();
    let mut free = Vec::new();
    all_idents(&expr, &mut bound, &mut free).expect("nonmatching lambda");
    assert_eq!(free, vec![&nested]);
}

#[test]
fn coinductive_alpha_rename_cannot_rewrite_a_display_twin() {
    let quoted = SurfaceName::component("x.y", true);
    let nested = SurfaceName::generated_path("x.y");
    let destination = SurfaceName::component("z", false);
    let map = [(quoted.clone(), destination.clone())];
    let renamed = target::rename_free(&generate::typed_ident(&quoted), &map).expect("exact rename");
    assert!(matches!(renamed, SurfaceExpr::Ident(_, name) if name.same_syntax(&destination)));
    let untouched =
        target::rename_free(&generate::typed_ident(&nested), &map).expect("different identity");
    assert!(matches!(untouched, SurfaceExpr::Ident(_, name) if name == nested));
    let capturing = generate::lam_typed(
        std::slice::from_ref(&destination),
        generate::typed_ident(&quoted),
    );
    assert!(target::rename_free(&capturing, &map).is_err());
    let selector = SurfaceName::component("x", false).with_relative_constructor();
    assert!(target::rename_free(&generate::typed_ident(&selector), &map).is_err());
}

#[test]
fn coinductive_companion_family_is_qualified_without_flattening_its_owner() {
    let quoted = lower_fixture("coinductive «A.B» : Prop → Prop\n| step : «A.B» p → «A.B» p\n")
        .expect("quoted owner");
    let nested = lower_fixture("coinductive A.B : Prop → Prop\n| step : A.B p → A.B p\n")
        .expect("hierarchical owner");
    let quoted_owner = SurfaceName::component("A.B", true);
    let nested_owner = SurfaceName::generated_path("A.B");
    assert_eq!(quoted.len(), 18);
    assert_eq!(nested.len(), 18);
    for (family, owner) in [(&quoted, &quoted_owner), (&nested, &nested_owner)] {
        let names = family.iter().map(generated_name).collect::<Vec<_>>();
        assert!(names.iter().all(|name| name.has_prefix(owner)));
        assert!(names.contains(&owner));
        for suffix in RESERVED_SUFFIXES.into_iter().chain(["step"]) {
            assert!(
                names.contains(&&owner.append(&SurfaceName::component(suffix, false))),
                "missing {suffix}"
            );
        }
    }
    assert!(quoted.iter().all(|a| nested
        .iter()
        .all(|b| generated_name(a) != generated_name(b))));
}

#[test]
fn coinductive_generated_index_binder_preserves_quoted_source_syntax() {
    let declarations = lower_fixture("coinductive P : Prop → Prop\n| step : P «x.y» → P «x.y»\n")
        .expect("quoted target variable");
    let expected = SurfaceName::component("x.y", true);
    let functor = declarations
        .iter()
        .find(|decl| generated_name(decl).name() == SurfaceName::generated_path("P.F").name())
        .expect("one-step functor");
    let SurfaceDecl::Def { binders, .. } = functor else {
        panic!("functor is a definition")
    };
    assert_eq!(binders.len(), 2);
    assert!(binders[1].name.same_syntax(&expected));
}

#[test]
fn coinductive_quoted_names_do_not_bypass_capture_or_companion_refusals() {
    for source in [
        "coinductive P : Prop → Prop\n| «F» : P p → P p\n",
        "coinductive P : Prop → Prop\n| step : P «x_coind» → P «x_coind»\n",
        "coinductive P : Prop → Prop\n| step : .P p → P p\n",
    ] {
        assert!(lower_fixture(source).is_err(), "must refuse: {source}");
    }
}

#[test]
fn coinductive_qualified_heads_and_census_use_exact_components() {
    let owner = clean_parser::parse_name("A.B").unwrap();
    let qualified = clean_parser::parse_expr("A.B").unwrap();
    assert!(matches!(qualified, SurfaceExpr::Proj(..)));
    assert!(is_predicate_head(&qualified, &owner));
    let mut bound = Vec::new();
    let mut free = Vec::new();
    all_predicate_idents(&qualified, &owner, &mut bound, &mut free).unwrap();
    assert_eq!(free, vec![&owner]);
    for spelling in ["«A.B»", "A.C", "Other.A.B", "A.B.extra", "A.1"] {
        let different = clean_parser::parse_expr(spelling).unwrap();
        assert!(!is_predicate_head(&different, &owner), "{spelling}");
    }
    let relative = SurfaceExpr::Ident(Span::dummy(), owner.clone().with_relative_constructor());
    assert!(!is_predicate_head(&relative, &owner));
}

#[test]
fn coinductive_qualified_occurrences_cannot_escape_positivity_checks() {
    let owner = clean_parser::parse_name("A.B").unwrap();
    let recursive = clean_parser::parse_expr("A.B p").unwrap();
    assert!(matches!(
        classify_premise(&recursive, &owner, &[], 1).unwrap(),
        Premise::Rec(args) if args.len() == 1
    ));
    for spelling in ["A.B p → p", "A.B (A.B p)", "A.B.extra p"] {
        let negative = clean_parser::parse_expr(spelling).unwrap();
        assert!(mentions(&negative, &owner), "{spelling}");
        assert!(
            classify_premise(&negative, &owner, &[], 1).is_err(),
            "{spelling}"
        );
    }
    let quoted = clean_parser::parse_expr("«A.B» p").unwrap();
    assert!(!mentions(&quoted, &owner));
    assert!(matches!(
        classify_premise(&quoted, &owner, &[], 1).unwrap(),
        Premise::Plain(_)
    ));
    for source in [
        "coinductive A.B : Prop → Prop\n| step : (A.B p → p) → A.B p\n",
        "coinductive A.B : Prop → Prop\n| step : A.B (A.B p) → A.B p\n",
        "coinductive A.B : Prop → Prop\n| step : A.B p → A.B (A.B p)\n",
        "coinductive A.B : Prop → Prop\n| step (q : A.B p) : A.B p → A.B p\n",
        "coinductive A.B : Prop → Prop\n| step : A.B p → «A.B» p\n",
        "coinductive «A.B» : Prop → Prop\n| step : «A.B» p → A.B p\n",
    ] {
        assert!(lower_fixture(source).is_err(), "must refuse: {source}");
    }
}

#[test]
fn coinductive_qualified_owner_prefix_cannot_be_captured_by_a_local() {
    for source in [
        "coinductive A.B : Prop → Prop\n| step : A.B A → A.B A\n",
        "coinductive A.B : Prop → Prop\n| step («A» : Prop) : A.B p → A.B p\n",
        "coinductive A.B (A : Prop) : Prop → Prop\n| step : A.B A p → A.B A p\n",
        "coinductive A.B : Prop → Prop\n| step : (∀ (A : Prop), A.B p) → A.B p\n",
    ] {
        assert!(lower_fixture(source).is_err(), "must refuse: {source}");
    }
    let owner = clean_parser::parse_name("A.B").unwrap();
    let base = SurfaceName::component("A", false);
    let projected = clean_parser::parse_expr("A.B").unwrap();
    let shadowed = generate::lam_typed(std::slice::from_ref(&base), projected);
    let mut bound = Vec::new();
    let mut free = Vec::new();
    assert!(all_predicate_idents(&shadowed, &owner, &mut bound, &mut free).is_err());
    assert!(mentions(&shadowed, &owner));
    assert_eq!(
        lower_fixture("coinductive A.B : Prop → Prop\n| step : A.B «A.B» → A.B «A.B»\n")
            .expect("quoted dotted local is not the qualified root")
            .len(),
        18
    );
}

#[test]
fn coinductive_owner_census_keeps_unrelated_local_projection_scope() {
    let owner = clean_parser::parse_name("A.B").unwrap();
    let local = SurfaceName::component("x", false);
    let projection = clean_parser::parse_expr("x.field").unwrap();
    let mut bound = Vec::new();
    let mut free = Vec::new();
    all_predicate_idents(&projection, &owner, &mut bound, &mut free).unwrap();
    assert_eq!(free, vec![&local]);
    let scoped = generate::lam_typed(std::slice::from_ref(&local), projection);
    let mut bound = Vec::new();
    let mut free = Vec::new();
    all_predicate_idents(&scoped, &owner, &mut bound, &mut free).unwrap();
    assert!(free.is_empty());
    assert!(!mentions(&scoped, &owner));
}
