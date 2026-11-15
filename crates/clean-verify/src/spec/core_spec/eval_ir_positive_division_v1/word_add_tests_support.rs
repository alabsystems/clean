// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::super::verify_root;
use crate::spec::Specification;
use clean_elab::ElabCtx;
use clean_kernel::{Expr, Level, Name, TypeChecker, TypeError};
use std::sync::OnceLock;

pub(super) const EXPECTED: [&str; 9] = [
    "ir_byte_add_le_of_ltb_false_v1",
    "ir_byte_add_subtract_bound_v1",
    "ir_byte_add_wrap_positive_once_v1",
    "ir_byte_add_wrap_bounded_sum_v1",
    "ir_byte_add_word_bound_v1",
    "ir_byte_add_uint_canonical_v1",
    "ir_byte_add_int_canonical_v1",
    "ir_byte_add_uint_canonical_result_bound_v1",
    "ir_byte_add_int_canonical_result_bound_v1",
];

pub(super) fn byte() -> &'static Specification {
    static SPEC: OnceLock<Specification> = OnceLock::new();
    SPEC.get_or_init(|| {
        crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
            .expect("ordinary public ByteV1, no division/shift package")
    })
}

pub(super) fn added() -> &'static Specification {
    // Test-only immutable fixture, not another production owner/cache profile.
    static SPEC: OnceLock<Specification> = OnceLock::new();
    SPEC.get_or_init(|| {
        let mut spec = byte().clone();
        spec.install_eval_ir_bounded_add_laws_v1()
            .expect("ordinary public additive installer");
        spec
    })
}

pub(super) fn certified(spec: &Specification, name: &str) {
    verify_root(spec, name).unwrap_or_else(|error| panic!("{name}: {error}"));
    let key = Name::from_string(name);
    let info = spec
        .env()
        .get_const(&key)
        .expect("actual stored proposition");
    let proof = Expr::const_(
        key.clone(),
        info.level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>(),
    );
    let audit = spec.env().audit_certification(&info.type_, &proof);
    assert!(audit.is_certified(), "independent root {name}: {audit:#?}");
    assert!(audit.dependencies.contains(&key));
    assert!(spec.env().axiom_deps(&key).expect("root exists").is_empty());
    assert!(spec
        .env()
        .trust_marker_deps(&key)
        .expect("root exists")
        .is_empty());
}

pub(super) fn add_checked(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(source, "independent actual Add/canonicality consumer")
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    certified(spec, name);
}

pub(super) fn previous_definitions_unchanged(before: &Specification, after: &Specification) {
    for (name, expected) in before.definitions() {
        let actual = after
            .get_definition(name)
            .expect("previous definition retained");
        macro_rules! fields {
            ($($field:ident),+ $(,)?) => {
                $(assert_eq!(actual.$field, expected.$field, "{name}: {}", stringify!($field));)+
            };
        }
        fields!(
            name,
            type_src,
            value_src,
            is_axiom,
            category,
            proof_status,
            description,
            elaborated_type,
            elaborated_value,
            dependencies,
            axiom_deps
        );
        let key = Name::from_string(name);
        assert_eq!(before.env().get_const(&key), after.env().get_const(&key));
        assert_eq!(
            before.env().declaration_verification(&key),
            after.env().declaration_verification(&key)
        );
    }
}

pub(super) fn owner_unchanged(before: &Specification, after: &Specification) {
    let empty = before.env().effect_since(before.env());
    let observed = after.env().effect_since(before.env());
    assert_eq!(empty.disagreement(&observed, after.env()), None);
    assert_eq!(before.env().generation(), after.env().generation());
    assert_eq!(before.definitions().len(), after.definitions().len());
    assert_eq!(
        before.red_env_script_override,
        after.red_env_script_override
    );
    assert_eq!(
        before.red_env_interning_override,
        after.red_env_interning_override
    );
    previous_definitions_unchanged(before, after);
}

pub(super) fn value(width: &str, a: &str, b: &str) -> String {
    format!("Bool.rec (fun (_ : Bool) => Nat) (Nat.sub (Nat.add ({a}) ({b})) (ir_nat_pow2 ({width}))) (Nat.add ({a}) ({b})) (ir_nat_ltb (Nat.add ({a}) ({b})) (ir_nat_pow2 ({width})))")
}
pub(super) fn operation(carrier: &str, width: u64, a: u64, b: u64, opcode: &str) -> String {
    format!("ir_binop_eval IRBinOp.{opcode} (IRTy.{carrier} {width}) (IRScalar.int_ {a}) (IRScalar.int_ {b})")
}

pub(super) fn elaborate(spec: &Specification, source: &str) -> Expr {
    let surface = clean_parser::parse_expr(source).expect("independent mathematical expression");
    let mut context = ElabCtx::new(spec.env());
    let expr = context.elaborate(&surface).expect("expression elaborates");
    let expr = context.metas().instantiate(&expr);
    let expr = context.metas().instantiate_levels(&expr);
    assert!(!expr.has_fvar_quick());
    assert!(!expr.has_expr_mvar_quick());
    assert!(!expr.has_level_mvar_quick());
    expr
}

pub(super) fn checker(spec: &Specification) -> TypeChecker<'_> {
    let mut checker = TypeChecker::new(spec.env());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    if let Some(Some(value)) = spec.env().get_option("maxHeartbeats") {
        if let Ok(limit) = value.parse::<u32>() {
            checker.set_heartbeat_limit(limit);
        }
    }
    if let Some(Some(value)) = spec.env().get_option("tcMaxCacheEntries") {
        if let Ok(limit) = value.parse::<usize>() {
            checker.set_max_cache_entries(limit);
        }
    }
    checker
}

pub(super) fn unspent(checker: &TypeChecker<'_>) {
    assert!(
        !checker.heartbeat_spent(),
        "budget exhaustion is not a mathematical verdict"
    );
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
}

pub(super) fn rejects_false(spec: &Specification, proof: &Expr, goal: &Expr) {
    let checker = checker(spec);
    checker
        .check_type(goal, &Expr::sort(Level::zero()))
        .expect("independent goal is Prop");
    let error = checker
        .check_type(proof, goal)
        .expect_err("genuine false/ill-typed claim");
    assert!(matches!(error, TypeError::TypeMismatch { .. }), "{error}");
    unspent(&checker);
}
