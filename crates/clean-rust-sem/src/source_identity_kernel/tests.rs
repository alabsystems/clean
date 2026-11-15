use super::declarations as d;
use super::*;
use clean_kernel::{Declaration, KernelTypeError, Level};

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(d::c(name), args)
}
fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, a, b],
    )
}
fn f(id: u64) -> Expr {
    Expr::fvar(clean_kernel::expr::FVarId::new(id))
}
fn env_ty() -> Expr {
    Expr::arrow(d::c("Nat"), d::c("Nat"))
}
fn reject(env: &Environment, proof: &Expr, goal: &Expr) {
    let mut tc = TypeChecker::new(env);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.check_type(goal, &Expr::sort(Level::zero()))
        .expect("hostile goal itself has type Prop");
    let error = tc
        .check_type(proof, goal)
        .expect_err("wrong universal result/world/context must refuse");
    assert!(
        matches!(error, KernelTypeError::TypeMismatch { .. }),
        "{error:?}"
    );
    assert!(!tc.heartbeat_spent());
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
}

#[test]
fn test_universal_structural_adequacy_is_kernel_checked_without_axioms() {
    let env = source_environment().expect("all source declarations and induction proof must check");
    let name = Name::from_string(d::ADEQUACY);
    let declaration = env.get_const(&name).expect("actual structural theorem");
    let proof = d::c(d::ADEQUACY);
    let mut checker = TypeChecker::new(&env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker
        .check_type(&proof, &declaration.type_)
        .expect("actual forall-source/forall-env/forall-world theorem");
    let audit = env.audit_certification(&declaration.type_, &proof);
    assert!(audit.is_certified(), "{audit:?}");
    for dependency in audit.dependencies {
        assert!(env.axiom_deps(&dependency).unwrap().is_empty());
        assert!(env.foundational_axiom_deps(&dependency).unwrap().is_empty());
        assert!(env.trust_marker_deps(&dependency).unwrap().is_empty());
    }
    assert!(!checker.heartbeat_spent());
}

/// When `var` names a directory, write `data()` there as `file` (pretty JSON).
/// Optional evidence output: it asserts nothing about the subject, `data` is
/// built only when requested, and a requested write that fails still fails
/// the test.
fn export_evidence_if_requested(var: &str, file: &str, data: impl FnOnce() -> serde_json::Value) {
    let Ok(directory) = std::env::var(var) else {
        return;
    };
    let directory = std::path::PathBuf::from(directory);
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(
        directory.join(file),
        serde_json::to_vec_pretty(&data()).unwrap(),
    )
    .unwrap();
}

#[test]
fn test_actual_source_projection_replays_quantified_identity_and_retained_term() {
    for (index, text) in [
        "fn identity(x:u64)->u64 { x }",
        "fn identity(x:u64)->u64 { { x } }",
        "fn identity(x:u64)->u64 { return x }",
        "fn identity(x:u64)->u64 { return { x } }",
    ]
    .into_iter()
    .enumerate()
    {
        let source = project_identity_source(text).unwrap();
        let proof = source.proof_candidate().unwrap();
        let retained = serde_json::to_vec(&proof).unwrap();
        let decoded: Expr = serde_json::from_slice(&retained).unwrap();
        let checked =
            replay_identity_source(text, &decoded).expect("fresh canonical environment replay");
        assert_eq!(checked.source().function(), "identity");
        assert_eq!(checked.source().parameter(), "x");
        assert_eq!(checked.claim(), &source.claim().unwrap());
        export_evidence_if_requested(
            "TRUST_G4_SOURCE_MATH_OUT",
            &format!("source-identity-{index}.json"),
            || {
                serde_json::json!({"model":MODEL,"source":text,"proof":checked.proof(),
                "claim":checked.claim(),"scope":"source-model-only; forall source environment and arbitrary world; no IR/native/source-capture license"})
            },
        );
    }
}

#[test]
fn test_source_shape_refuses_changed_values_effects_binders_and_headers() {
    for text in [
        "fn identity(x:u64)->u64 { 0 }",
        "fn identity(x:u64)->u64 { x+1 }",
        "fn identity(x:u64)->u64 { let z=x; z }",
        "fn identity(x:u64)->u64 { identity(x) }",
        "fn identity(x:i64)->i64 { x }",
        "unsafe fn identity(x:u64)->u64 { x }",
        "fn identity<T:Copy>(x:T)->T { x }",
        "fn identity(x:u64,y:u64)->u64 { y }",
    ] {
        assert!(project_identity_source(text).is_err(), "{text}");
    }
    // The general semantic AST reader is not used to erase these source rows.
    for text in [
        "fn identity(x:u64)->u64 { hidden_effect!(); x }",
        "fn identity(x:u64)->u64 { use erased::item; x }",
        "fn identity(x:u64)->u64 { return x; hidden_effect!(); }",
        "#[unknown_contract] fn identity(x:u64)->u64 { x }",
        "fn identity(x:u64)->u64 { other }",
    ] {
        assert!(project_identity_source(text).is_err(), "{text}");
    }
}

#[test]
fn test_universal_kernel_refuses_wrong_source_result_world_and_trace() {
    let env = source_environment().unwrap();
    let body = SourceBody::Wrapper(Box::new(SourceBody::Block(Box::new(SourceBody::Return(
        Box::new(SourceBody::Variable(0)),
    )))))
    .reflect()
    .unwrap();
    let wrong = SourceBody::Variable(1).reflect().unwrap();
    reject(
        &env,
        &d::identity_proof(wrong),
        &d::identity_claim(body.clone()),
    );
    let rho = f(3);
    let world_ty = f(10);
    let world = f(12);
    let other = f(13);
    let bindings = [
        (3, env_ty()),
        (10, Expr::type_()),
        (12, world_ty.clone()),
        (13, world_ty.clone()),
    ];
    let actual = app(
        d::RUN,
        [world_ty.clone(), body.clone(), rho.clone(), world.clone()],
    );
    let proof = d::close(
        &bindings,
        Expr::apps(
            d::identity_proof(body.clone()),
            [rho.clone(), world_ty.clone(), world.clone()],
        ),
        true,
    );
    let wrong_world = d::close(
        &bindings,
        eq(
            d::exit_ty(world_ty.clone()),
            actual.clone(),
            d::returned(
                world_ty.clone(),
                Expr::app(rho.clone(), Expr::nat_lit(0)),
                other,
            ),
        ),
        false,
    );
    reject(&env, &proof, &wrong_world);
    let wrong_result = d::close(
        &bindings,
        eq(
            d::exit_ty(world_ty.clone()),
            actual.clone(),
            d::returned(world_ty.clone(), Expr::nat_lit(0), world.clone()),
        ),
        false,
    );
    reject(&env, &proof, &wrong_result);
    let nil = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        d::c("Nat"),
    );
    let trace = Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [d::c("Nat"), Expr::nat_lit(1), nil],
    );
    let expected = app(
        d::EXIT_MK,
        [
            world_ty.clone(),
            Expr::app(rho, Expr::nat_lit(0)),
            world,
            trace,
        ],
    );
    let wrong_trace = d::close(&bindings, eq(d::exit_ty(world_ty), actual, expected), false);
    reject(&env, &proof, &wrong_trace);
}

#[test]
fn test_replay_cannot_import_a_forged_context_or_open_proof() {
    let input = "fn identity(x:u64)->u64 { x }";
    assert!(replay_identity_source(input, &d::c("Forged.identity_proof")).is_err());
    assert!(replay_identity_source(input, &f(0)).is_err());
    let mut env = source_environment().unwrap();
    let wrong = Declaration::Definition {
        name: Name::from_string(d::ORIGIN),
        level_params: vec![],
        type_: Expr::arrow(d::c(d::BODY), d::c("Nat")),
        value: Expr::lam(
            clean_kernel::BinderInfo::Default,
            d::c(d::BODY),
            Expr::nat_lit(1),
        ),
        is_reducible: true,
    };
    assert!(
        env.add_decl(wrong).is_err(),
        "source semantics cannot be overwritten or duplicate-skipped"
    );
    // A failed supplied context cannot contaminate the canonical replay environment.
    let projected = project_identity_source(input).unwrap();
    replay_identity_source(input, &projected.proof_candidate().unwrap()).unwrap();
}
