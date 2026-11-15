//! Close controls for exact deriving identity and authority transport.

use super::*;

fn axiom(env: &mut Environment, name: &Name) {
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("actual kernel registration of the test's explicit axiom");
}

#[test]
fn handler_authority_requires_exact_class_and_actual_handler_reference() {
    let class_pairs = [
        (Name::anon().str("A.B"), Name::anon().str("A").str("B")),
        (Name::anon().str("7"), Name::anon().num(7)),
    ];
    for (index, (class, twin)) in class_pairs.into_iter().enumerate() {
        let mut env = Environment::new();
        let handler = Name::anon().str("handler").num(index as u64);
        let other_handler = Name::anon().str("otherHandler").num(index as u64);
        axiom(&mut env, &handler);
        axiom(&mut env, &other_handler);
        env.register_derive_handler(class.clone(), handler.clone());
        let value = Expr::const_(handler.clone(), vec![]);
        let name = source_handler_instance_name(&class, &Name::anon().str("Target"));
        assert_eq!(
            registered_handler_axiom_authority_for_class(&env, &class, &value),
            HashSet::from([handler.clone()])
        );
        assert!(registered_handler_axiom_authority_for_class(&env, &twin, &value).is_empty());
        admit_generated_instance_typed(&env, &class, "Target", &name, &Expr::prop(), &value)
            .expect("exact registered explicit authority remains admitted");
        assert!(admit_generated_instance_typed(
            &env,
            &twin,
            "Target",
            &name,
            &Expr::prop(),
            &value
        )
        .is_err());
        let changed = Expr::const_(other_handler, vec![]);
        assert!(admit_generated_instance_typed(
            &env,
            &class,
            "Target",
            &name,
            &Expr::prop(),
            &changed
        )
        .is_err());

        let decl = Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::prop(),
            value,
            is_reducible: true,
        };
        env.add_decl(decl.clone())
            .expect("same exact generated body kernel checks");
        admit_registered_generated_instance_typed(&env, &class, "Target", &name)
            .expect("post-registration retains exact handler authority");
        assert!(admit_registered_generated_instance_typed(&env, &twin, "Target", &name).is_err());
        let before = env.get_const(&name).expect("registered row").clone();
        assert!(
            env.add_decl(decl).is_err(),
            "duplicate generated identities must reject"
        );
        let after = env.get_const(&name).expect("original row remains");
        assert_eq!(before.type_, after.type_);
        assert_eq!(before.value, after.value);
    }
}

#[test]
fn typed_handler_authority_does_not_admit_reserved_or_unregistered_axioms() {
    let mut env = Environment::new();
    let class = Name::anon().str("Marker");
    let name = source_handler_instance_name(&class, &Name::anon().str("Target"));
    for marker in ["sorryAx", "trustedSecret"] {
        let handler = Name::anon().str(marker);
        axiom(&mut env, &handler);
        env.register_derive_handler(class.clone(), handler.clone());
        assert!(admit_generated_instance_typed(
            &env,
            &class,
            "Target",
            &name,
            &Expr::prop(),
            &Expr::const_(handler, vec![])
        )
        .is_err());
    }
    let missing = Name::anon().str("unregistered");
    axiom(&mut env, &missing);
    assert!(admit_generated_instance_typed(
        &env,
        &class,
        "Target",
        &name,
        &Expr::prop(),
        &Expr::const_(missing, vec![])
    )
    .is_err());
}

fn register_source(env: &mut Environment, source: &str) -> crate::infer::ElabResult {
    let declaration = clean_parser::parse_decl(source).expect("exact source fixture parses");
    crate::elaborate_decl_and_register(env, &declaration)
        .expect("actual source derive and kernel registration must succeed")
}

#[test]
fn source_builtin_derives_keep_quoted_and_hierarchical_targets_separate() {
    let mut env = Environment::with_prelude();
    let targets = [
        (
            "inductive Ordinary where | first | second deriving BEq",
            Name::anon().str("Ordinary"),
        ),
        (
            "inductive «A.B» where | first | second deriving «BEq»",
            Name::anon().str("A.B"),
        ),
        (
            "inductive A.B where | first | second deriving BEq",
            Name::anon().str("A").str("B"),
        ),
    ];
    for (source, target) in targets {
        register_source(&mut env, source);
        let generated = builtin_instance_name(&target, "BEq");
        let info = env
            .get_const(&generated)
            .expect("exact generated Name is installed");
        let mut constants = HashSet::new();
        info.type_.collect_constants_into(&mut constants);
        info.value
            .as_ref()
            .expect("actual generated body")
            .collect_constants_into(&mut constants);
        assert!(constants.contains(&target));
        assert!(constants.contains(&target.clone().str("casesOn")));
        assert_eq!(info.kind, ConstantKind::Definition);
    }
    assert_ne!(
        builtin_instance_name(&Name::anon().str("A.B"), "BEq"),
        builtin_instance_name(&Name::anon().str("A").str("B"), "BEq")
    );
}

#[test]
fn source_repr_materialization_keeps_exact_constructor_identities() {
    let mut env = Environment::with_prelude();
    for (source, target) in [
        (
            "inductive «R.T» where | «a.b» | a deriving Repr",
            Name::anon().str("R.T"),
        ),
        (
            "inductive R.T where | «a.b» | a deriving Repr",
            Name::anon().str("R").str("T"),
        ),
    ] {
        register_source(&mut env, source);
        let info = env
            .get_const(&builtin_instance_name(&target, "Repr"))
            .expect("exact Repr instance is registered");
        let mut constants = HashSet::new();
        info.value
            .as_ref()
            .expect("materialized Repr body")
            .collect_constants_into(&mut constants);
        assert!(
            constants.contains(&target.clone().str("casesOn"))
                || constants.contains(&target.clone().str("rec"))
        );
        assert!(env.get_constructor(&target.clone().str("a.b")).is_some());
        assert!(env
            .get_constructor(&target.clone().str("a").str("b"))
            .is_none());
    }
}

#[test]
fn source_custom_handlers_keep_class_target_and_body_authority_exact() {
    let mut env = Environment::with_prelude();
    for source in [
        "class «M.C» (α : Type) where tag : Prop",
        "class M.C (α : Type) where tag : Prop",
        "@[derive_handler] axiom literalHandler {α : Type} : «M.C» α",
        "@[derive_handler] axiom pathHandler {α : Type} : M.C α",
        "structure «T.X» where value : Nat deriving «M.C», M.C",
    ] {
        register_source(&mut env, source);
    }
    let target = Name::anon().str("T.X");
    for (class, handler, other) in [
        (
            Name::anon().str("M.C"),
            Name::anon().str("literalHandler"),
            Name::anon().str("pathHandler"),
        ),
        (
            Name::anon().str("M").str("C"),
            Name::anon().str("pathHandler"),
            Name::anon().str("literalHandler"),
        ),
    ] {
        let generated = source_handler_instance_name(&class, &target);
        let info = env
            .get_const(&generated)
            .expect("exact custom instance installed");
        let mut constants = HashSet::new();
        info.value
            .as_ref()
            .expect("actual handler body")
            .collect_constants_into(&mut constants);
        assert!(constants.contains(&handler));
        assert!(!constants.contains(&other));
        admit_registered_generated_instance_typed(&env, &class, "T.X", &generated)
            .expect("same registered source authority passes final audit");
    }
}

/// G46 (ledger (116)) mutation control: a generated term carrying an
/// elaborator metavariable (a bit-63-tagged FVar) is named as such. The
/// shape gate asked `has_expr_mvar_quick`, constant false for elaborator
/// metas, so the defect fell through to the generic "free variable" arm.
#[test]
fn test_admit_generated_expr_shape_names_an_elaborator_metavariable() {
    let meta = Expr::fvar(crate::unify::MetaState::to_fvar(crate::unify::MetaId(0)));
    assert!(!meta.has_expr_mvar_quick(), "the kernel flag cannot see it");
    let err = admit_generated_expr_shape("Repr", "T", "instance value", &meta)
        .expect_err("a metavariable in a generated term is refused");
    let text = format!("{err:?}");
    assert!(
        text.contains("unresolved expression metavariable"),
        "the refusal names the metavariable, not a free variable: {text}"
    );
    // An ordinary free variable keeps its own reason.
    let local = Expr::fvar(clean_kernel::FVarId::new(5));
    let err = admit_generated_expr_shape("Repr", "T", "instance value", &local)
        .expect_err("a free variable in a generated term is refused");
    assert!(format!("{err:?}").contains("free variable"), "{err:?}");
}
