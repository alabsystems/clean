use super::*;
use crate::expr::BinderInfo;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn environment() -> Environment {
    let mut environment = Environment::new();
    environment.init_eq().unwrap();
    environment.init_nat().unwrap();
    environment.init_true_false().unwrap();
    environment
}
fn context(p_value: Expr, h_value: Expr) -> LocalContext {
    let mut context = LocalContext::new();
    context.push_let_with_id(FVarId::new(10), Name::anon(), Expr::prop(), p_value);
    context.push_let_with_id(
        FVarId::new(11),
        Name::anon(),
        Expr::fvar(FVarId::new(10)),
        h_value,
    );
    context
}
fn audit(environment: &Environment, context: &LocalContext, external: &Expr) -> CertificationAudit {
    environment
        .audit_scoped_certification(
            context,
            1,
            external,
            &Expr::fvar(FVarId::new(10)),
            &Expr::fvar(FVarId::new(11)),
            10_000,
        )
        .0
}

#[test]
fn scoped_audit_checks_values_and_the_complete_frozen_claim() {
    let environment = environment();
    assert!(audit(
        &environment,
        &context(c("True"), c("True.intro")),
        &c("True")
    )
    .is_certified());
    assert!(!audit(
        &environment,
        &context(c("False"), c("True.intro")),
        &c("True")
    )
    .is_certified());
    assert!(!audit(&environment, &context(c("True"), c("Nat.zero")), &c("True")).is_certified());
    assert!(!audit(
        &environment,
        &context(c("True"), c("True.intro")),
        &c("False")
    )
    .is_certified());
    assert!(!audit(
        &environment,
        &context(c("True"), c("True.intro")),
        &Expr::prop()
    )
    .is_certified());
    let mut unused = context(c("True"), c("True.intro"));
    unused.push_let_with_id(FVarId::new(12), Name::anon(), c("Nat"), c("True.intro"));
    assert!(
        !audit(&environment, &unused, &c("True")).is_certified(),
        "unused bad values must still be checked"
    );
    let mut assumption = context(c("True"), c("True.intro"));
    assumption.push_with_id(
        FVarId::new(12),
        Name::anon(),
        c("False"),
        BinderInfo::Default,
    );
    assert!(
        !audit(&environment, &assumption, &c("True")).is_certified(),
        "components cannot introduce assumptions"
    );
}

#[test]
fn scoped_audit_preserves_dependent_parameter_definition_parameter_meaning() {
    let environment = environment();
    let alpha = FVarId::new(100);
    let x = FVarId::new(101);
    let alias = FVarId::new(102);
    let h = FVarId::new(103);
    let eq = |a: Expr, l: Expr, r: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [a, l, r],
        )
    };
    let mut context = LocalContext::new();
    context.push_with_id(alpha, Name::anon(), Expr::type_(), BinderInfo::Default);
    context.push_with_id(x, Name::anon(), Expr::fvar(alpha), BinderInfo::Default);
    context.push_let_with_id(alias, Name::anon(), Expr::fvar(alpha), Expr::fvar(x));
    let goal = eq(Expr::fvar(alpha), Expr::fvar(alias), Expr::fvar(x));
    context.push_with_id(h, Name::anon(), goal.clone(), BinderInfo::Default);
    let external = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(
                BinderInfo::Default,
                eq(Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)),
                eq(Expr::bvar(2), Expr::bvar(1), Expr::bvar(1)),
            ),
        ),
    );
    let (result, work) = environment.audit_scoped_certification(
        &context,
        4,
        &external,
        &goal,
        &Expr::fvar(h),
        10_000,
    );
    assert!(result.is_certified(), "{result:?}");
    assert!(work.reference_visits > 0);
    assert!(!environment
        .audit_scoped_certification(&context, 2, &external, &goal, &Expr::fvar(h), 1)
        .0
        .is_certified());
}

#[test]
fn scoped_audit_refuses_forward_references_missing_parameters_and_spent_budget() {
    let environment = environment();
    let mut forward = LocalContext::new();
    forward.push_let_with_id(
        FVarId::new(10),
        Name::anon(),
        Expr::prop(),
        Expr::fvar(FVarId::new(12)),
    );
    forward.push_let_with_id(FVarId::new(12), Name::anon(), Expr::prop(), c("True"));
    assert!(!audit(&environment, &forward, &c("True")).is_certified());
    let mut parameter = LocalContext::new();
    parameter.push_with_id(
        FVarId::new(10),
        Name::anon(),
        c("True"),
        BinderInfo::Default,
    );
    assert!(!environment
        .audit_scoped_certification(&parameter, 1, &c("True"), &c("True"), &c("True.intro"), 100)
        .0
        .is_certified());
    struct Budget;
    impl Drop for Budget {
        fn drop(&mut self) {
            crate::tc::clear_declaration_budget();
        }
    }
    crate::tc::set_declaration_budget(1);
    let _budget = Budget;
    assert!(!audit(
        &environment,
        &context(c("True"), c("True.intro")),
        &c("True")
    )
    .is_certified());
    assert!(crate::tc::declaration_budget_exhausted());
}

#[test]
fn scoped_audit_includes_unused_definition_dependencies() {
    let mut environment = environment();
    let name = Name::from_string("Scoped.UnusedDomainAxiom");
    environment
        .add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("intentional hostile fixture axiom");
    let mut ctx = context(c("True"), c("True.intro"));
    ctx.push_let_with_id(
        FVarId::new(12),
        Name::anon(),
        Expr::prop(),
        Expr::const_(name.clone(), vec![]),
    );
    let result = audit(&environment, &ctx, &c("True"));
    assert!(!result.is_certified());
    assert!(
        result.dependencies.contains(&name),
        "unused definitions retain dependency custody"
    );
}

#[test]
fn scoped_audit_preserves_original_parameter_binder_data() {
    let environment = environment();
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        FVarId::new(10),
        Name::anon(),
        c("True"),
        BinderInfo::Implicit,
    );
    let external = Expr::pi(BinderInfo::Default, c("True"), c("True"));
    let (result, _) = environment.audit_scoped_certification(
        &ctx,
        1,
        &external,
        &c("True"),
        &Expr::fvar(FVarId::new(10)),
        1000,
    );
    assert!(
        !result.is_certified(),
        "the external telescope retains its actual binder data"
    );
}

#[test]
fn scoped_audit_work_is_cumulative_across_declarations_and_root() {
    let environment = environment();
    struct Budget;
    impl Drop for Budget {
        fn drop(&mut self) {
            crate::tc::clear_declaration_budget();
        }
    }
    crate::tc::set_declaration_budget(2_000_000);
    let _budget = Budget;
    let (result, work) = environment.audit_scoped_certification(
        &context(c("True"), c("True.intro")),
        1,
        &c("True"),
        &Expr::fvar(FVarId::new(10)),
        &Expr::fvar(FVarId::new(11)),
        1000,
    );
    assert!(result.is_certified(), "{result:?}");
    assert_eq!(work.ambient_limit, 2_000_000);
    assert!(work
        .declarations
        .iter()
        .all(|row| row.installed && row.after_type >= row.before));
    assert!(work
        .declarations
        .windows(2)
        .all(|pair| pair[1].before >= pair[0].after_value.unwrap_or(pair[0].after_type)));
    assert!(work
        .after_body
        .is_some_and(|after| after > 0 && after <= work.total));
    assert_eq!(work.after_dependencies, Some(work.total));
    assert_eq!(work.total, crate::tc::declaration_budget_used());
}

#[test]
fn scoped_audit_rejects_ill_typed_reducible_external_domain() {
    let environment = environment();
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        FVarId::new(10),
        Name::anon(),
        c("True"),
        BinderInfo::Default,
    );
    // Untyped reduction hides the invalid Nat argument; full external inference must reject it.
    let invalid_domain = Expr::app(
        Expr::lam(BinderInfo::Default, c("Nat"), c("True")),
        c("True.intro"),
    );
    let external = Expr::pi(BinderInfo::Default, invalid_domain, c("True"));
    let (result, _) = environment.audit_scoped_certification(
        &ctx,
        1,
        &external,
        &c("True"),
        &Expr::fvar(FVarId::new(10)),
        10_000,
    );
    assert!(!result.is_certified());
}

fn with_scoped_claim_budget<T>(limit: u64, check: impl FnOnce() -> T) -> T {
    struct Budget;
    impl Drop for Budget {
        fn drop(&mut self) {
            crate::tc::clear_declaration_budget();
        }
    }
    crate::tc::set_declaration_budget(limit);
    let _budget = Budget;
    check()
}

#[test]
fn scoped_audit_reuses_an_exact_outer_claim_with_a_strict_independent_tail() {
    let mut environment = Environment::with_mode(CleanMode::Classical);
    environment.init_eq().unwrap();
    environment.init_nat().unwrap();
    environment.init_true_false().unwrap();
    let binder = BinderInfo::Default;
    let name = Name::from_string("alias");
    let x = FVarId::new(10);
    let alias = FVarId::new(11);
    let universe = vec![Level::succ(Level::zero())];
    let equality = |left, right| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), universe.clone()),
            [c("Nat"), left, right],
        )
    };
    let mut context = LocalContext::new();
    context.push_with_id(x, Name::anon(), c("Nat"), binder);
    context.push_let_with_id(alias, name.clone(), c("Nat"), Expr::fvar(x));
    let goal = equality(Expr::fvar(alias), Expr::fvar(x));
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), universe.clone()),
        [c("Nat"), Expr::fvar(x)],
    );
    let claim = |domain, rhs, tail| {
        Expr::pi(
            binder,
            domain,
            Expr::let_named(name.clone(), c("Nat"), rhs, tail, false),
        )
    };
    let tail = equality(Expr::bvar(0), Expr::bvar(1));
    let exact = claim(c("Nat"), Expr::bvar(0), tail.clone());
    let run = |environment: &Environment, external: &Expr, limit| {
        with_scoped_claim_budget(limit, || {
            environment.audit_scoped_certification(&context, 2, external, &goal, &proof, 10_000)
        })
    };
    let (accepted, exact_work) = run(&environment, &exact, 2_000_000);
    assert!(accepted.is_certified(), "{accepted:?}");
    assert!(exact_work.declarations.iter().all(|row| row.installed));
    assert_eq!(exact_work.matched_claim_bindings, 2);
    assert_eq!(exact_work.after_parameters, exact_work.after_external_type);
    assert!(exact_work.after_external_type.unwrap() > exact_work.after_declarations.unwrap());
    assert!(exact_work.after_dependencies.is_some());

    let exhausted = exact_work.after_external_type.unwrap() - 1;
    let (refused, work) = run(&environment, &exact, exhausted);
    assert!(!refused.is_certified(), "{refused:?}");
    assert_eq!(work.total, exhausted);
    assert_eq!(work.declarations.len(), 2);
    assert!(work.declarations.iter().all(|row| row.installed));
    assert!(work.after_external_type.is_none());

    let equivalent_domain = Expr::app(Expr::lam(binder, c("True"), c("Nat")), c("True.intro"));
    let equivalent = claim(equivalent_domain, Expr::bvar(0), tail.clone());
    let (accepted, ordinary_work) = run(&environment, &equivalent, 2_000_000);
    assert!(accepted.is_certified(), "{accepted:?}");
    assert!(ordinary_work.after_parameters > ordinary_work.after_external_type);

    let goal_change = claim(c("Nat"), c("Nat.zero"), tail.clone());
    let malformed_rhs = claim(c("Nat"), c("True.intro"), tail);
    // Erasing this wrong argument yields the wanted conclusion. The
    // independent tail still has to type-check in the exact context.
    let malformed_tail = Expr::app(
        Expr::lam(binder, c("Nat"), equality(Expr::bvar(1), Expr::bvar(2))),
        c("True.intro"),
    );
    let malformed_tail = claim(c("Nat"), Expr::bvar(0), malformed_tail);
    for changed in [goal_change, malformed_rhs, malformed_tail] {
        let (refused, work) = run(&environment, &changed, 2_000_000);
        assert!(!refused.is_certified(), "{refused:?}");
        assert!(work.after_body.is_none());
    }

    {
        let mut checker = TypeChecker::with_context(&environment, context.clone());
        checker.set_cumulative(true);
        assert!(checked_external_tail(&checker, &context, &exact)
            .unwrap()
            .is_none());
    }
    environment.set_kernel_theory(KernelTheory::LeanReference);
    let (accepted, ordinary_work) = run(&environment, &exact, 2_000_000);
    assert!(accepted.is_certified(), "{accepted:?}");
    assert!(ordinary_work.after_parameters > ordinary_work.after_external_type);
}

#[test]
fn scoped_audit_exact_outer_claim_keeps_unused_definition_dependency() {
    let mut environment = environment();
    let axiom = Name::from_string("Scoped.UnusedExactPrefixAxiom");
    environment
        .add_decl(Declaration::Axiom {
            name: axiom.clone(),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("intentional hostile fixture axiom");
    let rhs = Expr::const_(axiom.clone(), vec![]);
    let name = Name::from_string("unused");
    let binder = BinderInfo::Default;
    let mut context = LocalContext::new();
    context.push_with_id(FVarId::new(10), Name::anon(), c("Nat"), binder);
    context.push_let_with_id(FVarId::new(11), name.clone(), Expr::prop(), rhs.clone());
    let external = Expr::pi(
        binder,
        c("Nat"),
        Expr::let_named(name, Expr::prop(), rhs, c("True"), true),
    );
    let (refused, work) = with_scoped_claim_budget(2_000_000, || {
        environment.audit_scoped_certification(
            &context,
            2,
            &external,
            &c("True"),
            &c("True.intro"),
            10_000,
        )
    });
    assert!(!refused.is_certified(), "{refused:?}");
    assert_eq!(work.matched_claim_bindings, 2);
    assert_eq!(work.after_parameters, work.after_external_type);
    assert!(work.after_body.is_some());
    assert!(work.after_dependencies.is_some());
    assert!(refused.dependencies.contains(&axiom));
}

#[test]
fn scoped_audit_sort_compatibility_cannot_form_an_exact_external_pi() {
    let environment = environment();
    let checker = TypeChecker::new(&environment);
    let binder = BinderInfo::Default;
    let not_a_type = Expr::lam(binder, c("Nat"), Expr::bvar(0));
    assert!(checker.infer_sort(&not_a_type).is_ok());
    assert!(!checker.infer_sort_with_formation(&not_a_type).unwrap().1);

    let mut context = LocalContext::new();
    context.push_with_id(FVarId::new(10), Name::anon(), not_a_type.clone(), binder);
    let external = Expr::pi(binder, not_a_type, c("True"));
    let (refused, work) = environment.audit_scoped_certification(
        &context,
        1,
        &external,
        &c("True"),
        &c("True.intro"),
        10_000,
    );
    assert!(!refused.is_certified(), "{refused:?}");
    assert!(work.declarations[0].installed);
    assert!(work.after_external_type.is_none());
}

#[test]
fn scoped_audit_formats_real_shared_type_mismatch_without_tree_expansion() {
    let environment = environment();
    let mut goal = c("True");
    for _ in 0..64 {
        goal = Expr::pi(BinderInfo::Default, goal.clone(), goal);
    }
    // Exercise the real check_type failure, then the exact audit renderer.
    // Inferring this entire shared goal would test a separate sort-expansion
    // problem before reaching the diagnostic surface this control owns.
    let checker = TypeChecker::new(&environment);
    let failure = checker
        .check_type(&c("Nat.zero"), &goal)
        .expect_err("Nat.zero cannot prove the constructed proposition");
    assert!(matches!(failure, TypeError::TypeMismatch { .. }));
    let issue = rejection_debug(format_args!("complete scoped root body: {failure:?}"));
    let CertificationIssue::TermRejected { error: message } = issue else {
        panic!("the malformed proof must remain a term rejection")
    };
    assert!(message.contains("TypeMismatch"), "{message}");
    assert!(message.contains("diagnostic truncated"), "{message}");
    assert!(message.len() <= 4096);
}

fn paired_definition(binder: BinderInfo, rhs: Expr, body: Expr) -> Expr {
    let h = Expr::lam(BinderInfo::Default, Expr::bvar(0), body);
    let r = Expr::let_named(Name::from_string("R"), Expr::prop(), rhs, h, false);
    Expr::lam(binder, Expr::prop(), r)
}

#[test]
fn scoped_audit_paired_introductions_preserve_dependent_lets_and_refusals() {
    let environment = environment();
    let binder = BinderInfo::Default;
    let body = Expr::pi(binder, Expr::bvar(0), Expr::bvar(1));
    let annotation = |rhs| {
        let body = Expr::let_named(
            Name::from_string("R"),
            Expr::prop(),
            rhs,
            body.clone(),
            false,
        );
        Expr::pi(binder, Expr::prop(), body)
    };
    let replay = |type_: Expr, value: Expr| {
        let mut context = LocalContext::new();
        let id = FVarId::new(10);
        context.push_let_with_id(id, Name::anon(), type_, value);
        environment.audit_scoped_certification(
            &context,
            0,
            &c("True"),
            &c("True"),
            &Expr::apps(Expr::fvar(id), [c("True"), c("True.intro")]),
            10_000,
        )
    };

    let exact = paired_definition(binder, Expr::bvar(0), Expr::bvar(0));
    let (accepted, work) = replay(annotation(Expr::bvar(0)), exact);
    assert!(accepted.is_certified(), "{accepted:?}");
    assert!(work.declarations[0].installed);
    assert!(work.after_body.is_some() && work.after_dependencies.is_some());

    let changed_binder = paired_definition(BinderInfo::Implicit, Expr::bvar(0), Expr::bvar(0));
    let (accepted, _) = replay(annotation(Expr::bvar(0)), changed_binder);
    assert!(
        accepted.is_certified(),
        "ordinary binder conversion: {accepted:?}"
    );

    for changed in [
        paired_definition(binder, Expr::bvar(0), c("True.intro")),
        paired_definition(binder, c("True"), Expr::bvar(0)),
    ] {
        let (refused, work) = replay(annotation(Expr::bvar(0)), changed);
        assert!(!refused.is_certified(), "changed body or RHS accepted");
        assert!(work.declarations[0].after_value.is_some());
        assert!(!work.declarations[0].installed);
        assert!(work.after_body.is_none());
    }

    let bad_rhs = c("True.intro");
    let matching_bad = paired_definition(binder, bad_rhs.clone(), Expr::bvar(0));
    let (refused, work) = replay(annotation(bad_rhs), matching_bad);
    assert!(!refused.is_certified(), "identical ill-typed LETs accepted");
    assert!(work.declarations[0].after_value.is_none());
    assert!(!work.declarations[0].installed);

    // The annotation's inferred type is Nat -> Nat, not a Sort. The
    // standalone infer_sort Pi fallback cannot serve the strict binder rule.
    let non_sort = Expr::lam(binder, c("Nat"), Expr::bvar(0));
    let bad_type = Expr::pi(binder, non_sort.clone(), c("True"));
    let bad_value = Expr::lam(binder, non_sort, c("True.intro"));
    let (refused, work) = replay(bad_type, bad_value);
    assert!(!refused.is_certified(), "non-sort binder domain accepted");
    assert!(work.declarations[0].after_value.is_none());
    assert!(!work.declarations[0].installed);
}

#[test]
fn scoped_audit_paired_residual_sort_preserves_ordinary_pi_rejection() {
    let classical = Environment::try_with_prelude().unwrap();
    assert_eq!(classical.mode(), CleanMode::Classical);
    for environment in [environment(), classical] {
        assert_paired_residual_sort_refusal(&environment);
    }
}

fn assert_paired_residual_sort_refusal(environment: &Environment) {
    let binder = BinderInfo::Default;
    let level_one = Level::succ(Level::zero());
    let level_two = Level::succ(level_one.clone());
    let level_three = Level::succ(level_two.clone());
    let recursor = Expr::const_(Name::from_string("True.rec"), vec![level_three]);
    let motive = Expr::lam(binder, c("True"), Expr::sort(level_two));
    let family_body = Expr::apps(recursor, [motive, Expr::sort(level_one), Expr::bvar(0)]);
    let family_type = Expr::pi(binder, c("True"), family_body);
    let family_value = Expr::lam(binder, c("True"), Expr::prop());
    let family_id = FVarId::new(10);
    let result_id = FVarId::new(11);
    let mut context = LocalContext::new();
    context.push_let_with_id(family_id, Name::anon(), family_type, family_value);
    let result_body = Expr::app(Expr::fvar(family_id), Expr::bvar(0));
    let result_type = Expr::pi(binder, c("True"), result_body);
    let result_value = Expr::lam(binder, c("True"), c("True"));

    let ordinary = TypeChecker::with_context(environment, context.clone());
    assert!(matches!(
        ordinary.infer_sort(&result_type),
        Err(TypeError::ExpectedSort { .. })
    ));
    let local = ordinary.push_binder_local(Name::anon(), c("True"), binder);
    let opened = Expr::app(Expr::fvar(family_id), Expr::fvar(local));
    let inferred = ordinary.infer_type_full(&opened).unwrap();
    assert!(!matches!(inferred.kind(), ExprKind::Sort(_)));
    assert!(matches!(ordinary.whnf(&inferred).kind(), ExprKind::Sort(_)));
    ordinary.pop_binder_local();

    context.push_let_with_id(result_id, Name::anon(), result_type, result_value);
    let (audit, work) = environment.audit_scoped_certification(
        &context,
        0,
        &c("True"),
        &c("True"),
        &c("True.intro"),
        10_000,
    );
    assert!(!audit.is_certified(), "paired replay changed Pi refusal");
    assert_eq!(work.declarations.len(), 2, "{audit:?}");
    assert!(work.declarations[0].installed, "{audit:?}");
    assert!(work.declarations[1].after_value.is_none());
    assert!(!work.declarations[1].installed);
}
