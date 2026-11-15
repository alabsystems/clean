// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use crate::spec::{ModelUnitSource, Specification};
use clean_elab::ElabCtx;
use clean_kernel::{Expr, Level, Name, TypeChecker, TypeError};
use std::sync::OnceLock;

pub(super) fn positive() -> &'static Specification {
    static SPEC: OnceLock<Specification> = OnceLock::new();
    SPEC.get_or_init(|| {
        crate::eval_ir::build_positive_division_byte_prelude_spec_v1_with_stack()
            .expect("actual public checked positive-division owner")
    })
}

pub(super) fn total() -> &'static Specification {
    static SPEC: OnceLock<Specification> = OnceLock::new();
    SPEC.get_or_init(|| {
        let mut spec = positive().clone();
        spec.install_eval_ir_total_restoring_division_laws_v1()
            .expect("actual public additive total restoring installer");
        spec
    })
}

pub(super) fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

pub(super) fn app(name: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(constant(name), arguments)
}

pub(super) fn equality(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [constant("Nat"), left, right],
    )
}

pub(super) fn reflexivity(answer: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [constant("Nat"), answer],
    )
}

pub(super) fn checker(spec: &Specification) -> TypeChecker<'_> {
    let mut tc = TypeChecker::new(spec.env());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    if let Some(Some(value)) = spec.env().get_option("maxHeartbeats") {
        tc.set_heartbeat_limit(value.parse().expect("maintained heartbeat policy"));
    }
    if let Some(Some(value)) = spec.env().get_option("tcMaxCacheEntries") {
        tc.set_max_cache_entries(value.parse().expect("maintained cache policy"));
    }
    tc
}

pub(super) fn elaborate(spec: &Specification, source: &str) -> Expr {
    let surface = clean_parser::parse_expr(source).expect("independent public endpoint parses");
    let mut context = ElabCtx::new(spec.env());
    let term = context
        .elaborate(&surface)
        .expect("public endpoint elaborates");
    let term = context.metas().instantiate(&term);
    let term = context.metas().instantiate_levels(&term);
    assert!(!term.has_fvar_quick() && !term.has_loose_bvars());
    assert!(!term.has_expr_mvar_quick() && !term.has_level_mvar_quick());
    term
}

pub(super) fn replay(spec: &Specification, claim: &Expr, proof: &Expr, accepted: bool) {
    let tc = checker(spec);
    tc.check_type(claim, &Expr::sort(Level::zero()))
        .expect("actual proposition is independently well typed");
    let result = tc.check_type(proof, claim);
    assert!(
        !tc.heartbeat_spent(),
        "resource exhaustion is not a verdict: {result:?}"
    );
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    if accepted {
        result.expect("independent actual endpoint replay");
        let audit = spec.env().audit_certification(claim, proof);
        assert!(audit.is_certified(), "{audit:#?}");
    } else {
        assert!(
            matches!(result, Err(TypeError::TypeMismatch { .. })),
            "{result:?}"
        );
    }
}

pub(super) fn previous_unchanged(before: &Specification, after: &Specification) {
    for (name, expected) in before.definitions() {
        let actual = after
            .get_definition(name)
            .expect("complete old owner retained");
        assert_eq!(
            (
                &actual.name,
                &actual.type_src,
                &actual.value_src,
                actual.is_axiom,
                actual.category,
                actual.proof_status,
                &actual.description,
                &actual.elaborated_type,
                &actual.elaborated_value,
                &actual.dependencies,
                &actual.axiom_deps
            ),
            (
                &expected.name,
                &expected.type_src,
                &expected.value_src,
                expected.is_axiom,
                expected.category,
                expected.proof_status,
                &expected.description,
                &expected.elaborated_type,
                &expected.elaborated_value,
                &expected.dependencies,
                &expected.axiom_deps
            ),
            "original declaration/bookkeeping {name}"
        );
        let key = Name::from_string(name);
        assert_eq!(before.env().get_const(&key), after.env().get_const(&key));
        assert_eq!(
            before.env().declaration_verification(&key),
            after.env().declaration_verification(&key)
        );
    }
    for option in ["maxHeartbeats", "tcMaxCacheEntries", "relaxedAutoImplicit"] {
        assert_eq!(
            before.env().get_option(option),
            after.env().get_option(option)
        );
    }
    assert_eq!(
        before.red_env_script_override,
        after.red_env_script_override
    );
    assert_eq!(
        before.red_env_interning_override,
        after.red_env_interning_override
    );
    match (&before.model_unit_source, &after.model_unit_source) {
        (ModelUnitSource::CleanFiles, ModelUnitSource::CleanFiles)
        | (ModelUnitSource::RetainedLiterals, ModelUnitSource::RetainedLiterals) => {}
        (ModelUnitSource::Planted(expected), ModelUnitSource::Planted(actual)) => {
            assert_eq!(expected, actual)
        }
        (expected, actual) => panic!("model source changed: {expected:?} -> {actual:?}"),
    }
}

pub(super) fn owner_unchanged(before: &Specification, after: &Specification) {
    let empty = before.env().effect_since(before.env());
    let observed = after.env().effect_since(before.env());
    assert_eq!(empty.disagreement(&observed, after.env()), None);
    assert_eq!(before.env().generation(), after.env().generation());
    assert_eq!(
        before.env().has_constant_source(),
        after.env().has_constant_source()
    );
    assert_eq!(before.definitions().len(), after.definitions().len());
    previous_unchanged(before, after);
}
