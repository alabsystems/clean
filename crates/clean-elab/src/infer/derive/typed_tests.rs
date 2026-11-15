//! Class selection must use actual source resolution and exact global identity.

use super::*;

#[test]
fn typed_class_selection_preserves_escaping_and_rejects_relative_or_local_heads() {
    let env = clean_kernel::Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let plain = clean_parser::parse_name("BEq").expect("builtin name");
    let escaped = clean_parser::parse_name("«BEq»").expect("same exact builtin identity");
    for source in [&plain, &escaped] {
        let resolved = ctx
            .resolve_derive_class(source)
            .expect("actual builtin resolution");
        assert_eq!(resolved.name(), &Name::anon().str("BEq"));
        assert_eq!(builtin_class(resolved.name()), Some("BEq"));
    }
    let relative = plain.clone().with_relative_constructor();
    assert!(ctx.resolve_derive_class(&relative).is_err());
    assert!(ctx
        .resolve_derive_class(&SurfaceName::generated_path("UnknownDeriveClass"))
        .is_err());
    ctx.push_local(plain.clone(), Expr::sort(Level::succ(Level::zero())));
    assert!(
        ctx.resolve_derive_class(&plain).is_err(),
        "a local binding must not select the same-spelled builtin"
    );
}

#[test]
fn typed_builtin_dispatch_has_no_suffix_or_display_fallback() {
    for name in [
        Name::anon().str("Other").str("BEq"),
        Name::anon().str("Other.BEq"),
        Name::anon().num(7),
        Name::anon().str("7"),
    ] {
        assert_eq!(builtin_class(&name), None);
    }
    let env = clean_kernel::Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    assert!(
        ctx.derive_instance(
            &Name::anon().str("Target"),
            &[],
            &[],
            &[],
            &SurfaceName::from_name(Name::anon().str("Other").str("BEq")),
        )
        .is_err(),
        "unknown exact class cannot silently borrow BEq generation"
    );
}

#[test]
fn bare_environment_builtin_dispatch_does_not_create_header_auto_implicits() {
    let env = clean_kernel::Environment::new();
    let mut ctx = ElabCtx::new(&env);
    ctx.in_decl_context = true;
    ctx.in_term_body = false;
    for label in ["BEq", "Inhabited", "DecidableEq", "Repr", "Hashable"] {
        let name = SurfaceName::component(label, false);
        assert!(env.get_const(name.name()).is_none());
        assert_eq!(ctx.resolve_derive_class(&name).unwrap().name(), name.name());
        assert!(ctx.lookup_local(&name).is_none());
        assert!(ctx.has_auto_implicit(&name).is_none());
        assert!(!ctx.in_term_body, "restore the caller's header state");
    }
    let unknown = SurfaceName::component("UnknownClass", false);
    assert!(ctx.resolve_derive_class(&unknown).is_err());
    assert!(ctx.lookup_local(&unknown).is_none());
    assert!(ctx.has_auto_implicit(&unknown).is_none());
    assert!(!ctx.in_term_body, "restore on refusal too");
    ctx.in_term_body = true;
    assert!(ctx.resolve_derive_class(&unknown).is_err());
    assert!(ctx.in_term_body);
}

#[test]
fn derive_global_shadowing_and_typed_custom_paths_precede_builtin_dispatch() {
    let mut env = clean_kernel::Environment::new();
    let namespace_class = Name::anon().str("Ns").str("BEq");
    let literal = Name::anon().str("M.C");
    let hierarchy = Name::anon().str("M").str("C");
    for name in [&namespace_class, &literal, &hierarchy] {
        env.add_decl(clean_kernel::Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("explicit test-only global identity");
    }
    let mut ctx = ElabCtx::new(&env);
    ctx.namespace_prefix = SurfaceName::generated_path("Ns");
    assert_eq!(
        ctx.resolve_derive_class(&SurfaceName::generated_path("BEq"))
            .unwrap()
            .name(),
        &namespace_class
    );
    for (spelling, expected) in [("«M.C»", literal), ("M.C", hierarchy)] {
        assert_eq!(
            ctx.resolve_derive_class(&clean_parser::parse_name(spelling).unwrap())
                .unwrap()
                .name(),
            &expected
        );
    }
    let builtin = SurfaceName::generated_path("BEq");
    ctx.push_local(builtin.clone(), Expr::type_());
    assert!(
        ctx.resolve_derive_class(&builtin).is_err(),
        "local cannot choose a global handler"
    );
    ctx.pop_local();
    ctx.meta_value_bindings
        .insert(builtin.clone(), Expr::const_(namespace_class, vec![]));
    assert!(
        ctx.resolve_derive_class(&builtin).is_err(),
        "a stored term is not global name resolution"
    );
}

#[test]
fn unknown_derive_class_keeps_named_unsupported_diagnostic_without_auto_binding() {
    let env = clean_kernel::Environment::new();
    let mut ctx = ElabCtx::new(&env);
    ctx.in_decl_context = true;
    for spelling in ["UnknownClass", "Other.BEq", "«Other.BEq»"] {
        let name = clean_parser::parse_name(spelling).unwrap();
        let error = ctx.resolve_derive_class(&name).unwrap_err();
        assert!(matches!(error, ElabError::Unsupported { feature }
            if feature.contains(&name.to_string()) && feature.contains("derive handler")));
        assert!(ctx.lookup_local(&name).is_none());
        assert!(ctx.has_auto_implicit(&name).is_none());
        assert!(!ctx.in_term_body);
    }
}

#[test]
fn constructor_field_analysis_alias_is_exact_and_restores_its_owned_local() {
    let mut env = clean_kernel::Environment::with_prelude();
    let twin = Name::anon().str("A.B");
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: twin.clone(),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    let mut ctx = ElabCtx::new(&env);
    let short = SurfaceName::component("B", false);
    let prior = ctx.push_local(short.clone(), Expr::type_());
    let owner = clean_parser::parse_name("A.B").unwrap();
    let constructors = |source| match clean_parser::parse_decl(source).unwrap() {
        clean_parser::SurfaceDecl::Inductive { ctors, .. } => ctors,
        other => panic!("expected actual inductive syntax: {other:?}"),
    };
    let cases = constructors("inductive A.B where | first | second");
    let fields = ctx
        .collect_ctor_fields(owner.name(), &cases)
        .expect("exact default return alias");
    assert_eq!(fields.len(), 2);
    assert!(fields
        .iter()
        .all(|row| row.field_types.is_empty() && !row.has_recursive_field));
    let cases = constructors("inductive A.B where | mk : «A.B» → A.B");
    let fields = ctx
        .collect_ctor_fields(owner.name(), &cases)
        .expect("typed display twin field");
    assert_eq!(fields.len(), 1);
    assert!(!fields[0].has_recursive_field);
    assert!(matches!(fields[0].field_types.as_slice(), [field]
        if matches!(field.kind(), ExprKind::Const(name, _) if name == &twin)));
    let recursive = constructors("inductive A.B where | mk : A.B → A.B");
    let fields = ctx
        .collect_ctor_fields(owner.name(), &recursive)
        .expect("exact recursive field");
    assert!(fields[0].has_recursive_field);
    let refused = constructors("inductive A.B where | mk : MissingField → A.B");
    assert!(ctx.collect_ctor_fields(owner.name(), &refused).is_none());
    assert!(
        ctx.lookup_local(&owner).is_none(),
        "temporary full-name alias must not escape"
    );
    assert_eq!(ctx.lookup_local(&short).map(|(id, _)| id), Some(prior));
    ctx.pop_local();
    assert!(ctx.lookup_local(&short).is_none());
}
