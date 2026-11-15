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
    assert!(matches!(failure, crate::tc::TypeError::TypeMismatch { .. }));
    let issue = rejection_debug(format_args!("complete scoped root body: {failure:?}"));
    let CertificationIssue::TermRejected { error: message } = issue else {
        panic!("the malformed proof must remain a term rejection")
    };
    assert!(message.contains("TypeMismatch"), "{message}");
    assert!(message.contains("diagnostic truncated"), "{message}");
    assert!(message.len() <= 4096);
}
