// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::super::verify_root;
use crate::spec::{SpecError, Specification};
use clean_elab::ElabCtx;
use clean_kernel::{Expr, Level, Name, TypeChecker, TypeError};
use std::sync::OnceLock;

pub(super) const EXPECTED: [&str; 11] = [
    "ir_positive_division_u64_by_three_bound_v1",
    "ir_positive_division_u64_fill_by_three_bound_v1",
    "ir_positive_division_u64_by_three_v1",
    "ir_positive_division_u64_fill_by_three_v1",
    "ir_positive_division_ashr_value_quotient_congr_v1",
    "ir_positive_division_ashr_i64_value_by_three_v1",
    "ir_byte_lshr_u64_by_three_v1",
    "ir_byte_ashr_i64_by_three_v1",
    "ir_byte_lshr_u64_max_by_three_v1",
    "ir_byte_ashr_i64_negative_one_by_three_v1",
    "ir_byte_ashr_i64_min_by_three_v1",
];

// Each immutable fixture is built through its actual public owned factory once.
// Only mutating consumers clone it; no test serializes the large proof DAG.
pub(super) fn positive() -> &'static Specification {
    static SPEC: OnceLock<Specification> = OnceLock::new();
    SPEC.get_or_init(|| {
        crate::eval_ir::build_positive_division_byte_prelude_spec_v1_with_stack()
            .expect("public owned ByteV1 plus all 49 division laws")
    })
}

pub(super) fn shifted() -> &'static Specification {
    static SPEC: OnceLock<Specification> = OnceLock::new();
    SPEC.get_or_init(|| {
        crate::eval_ir::build_u64_shift_by_three_byte_prelude_spec_v1_with_stack()
            .expect("public owned ByteV1 plus division and actual shift consumers")
    })
}

macro_rules! assert_definition_fields {
    ($before:ident, $after:ident, $($field:ident),+ $(,)?) => {
        $(assert_eq!($before.$field, $after.$field, stringify!($field));)+
    };
}

pub(super) fn previous_definitions_unchanged(before: &Specification, after: &Specification) {
    for (name, expected) in before.definitions() {
        let actual = after
            .get_definition(name)
            .expect("previous definition retained");
        assert_definition_fields!(
            expected,
            actual,
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
            axiom_deps,
        );
        let key = Name::from_string(name);
        assert_eq!(
            before.env().get_const(&key),
            after.env().get_const(&key),
            "stored {name}"
        );
        assert_eq!(
            before.env().declaration_verification(&key),
            after.env().declaration_verification(&key),
            "provenance {name}"
        );
    }
}

pub(super) fn owner_unchanged(before: &Specification, after: &Specification) {
    let empty = before.env().effect_since(before.env());
    let actual = after.env().effect_since(before.env());
    assert_eq!(empty.disagreement(&actual, after.env()), None);
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

pub(super) fn certified(spec: &Specification, root: &str) {
    verify_root(spec, root).unwrap_or_else(|error| panic!("stored root {root}: {error}"));
    let name = Name::from_string(root);
    let info = spec
        .env()
        .get_const(&name)
        .expect("actual stored proposition");
    let term = Expr::const_(
        name.clone(),
        info.level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>(),
    );
    let audit = spec.env().audit_certification(&info.type_, &term);
    assert!(audit.is_certified(), "independent root {root}: {audit:#?}");
    assert!(
        audit.dependencies.contains(&name),
        "actual root remains in closure"
    );
    assert!(spec
        .env()
        .axiom_deps(&name)
        .expect("root exists")
        .is_empty());
    assert!(spec
        .env()
        .trust_marker_deps(&name)
        .expect("root exists")
        .is_empty());
}

#[derive(Clone, Copy)]
pub(super) enum Shift {
    Logical,
    Arithmetic,
}

impl Shift {
    pub(super) fn opcode(self) -> &'static str {
        match self {
            Self::Logical => "lshr",
            Self::Arithmetic => "ashr",
        }
    }
    fn carrier(self) -> &'static str {
        match self {
            Self::Logical => "uint_",
            Self::Arithmetic => "int_",
        }
    }
    fn law(self) -> &'static str {
        match self {
            Self::Logical => "ir_byte_lshr_u64_by_three_v1",
            Self::Arithmetic => "ir_byte_ashr_i64_by_three_v1",
        }
    }
}

pub(super) fn operation(shift: Shift, word: u64, width: u64, amount: u64) -> String {
    format!("ir_binop_eval IRBinOp.{} (IRTy.{} {width}) (IRScalar.int_ {word}) (IRScalar.int_ {amount})", shift.opcode(), shift.carrier())
}

pub(super) fn quotient(word: &str, fuel: u64) -> String {
    format!("ir_dm_quot (ir_dm_go 1 ({word}) {fuel} 8 (IRDivMod.mk ({word}) 0))")
}

pub(super) fn scalar_result(value: &str) -> String {
    format!("IRStepResult.value (IRScalar.int_ ({value}))")
}

pub(super) fn restoring_result(shift: Shift, word: u64) -> String {
    let q = quotient(&word.to_string(), 64);
    match shift {
        Shift::Logical => scalar_result(&q),
        Shift::Arithmetic => {
            let fill = quotient("ir_nat_pow2 64", 64);
            scalar_result(&format!("Bool.rec (fun (_ : Bool) => Nat) ({q}) (Nat.add ({q}) (Nat.sub (ir_nat_pow2 64) ({fill}))) (ir_sign_bit 64 {word})"))
        }
    }
}

pub(super) fn claim(
    name: &str,
    shift: Shift,
    word: u64,
    width: u64,
    amount: u64,
    result: &str,
) -> String {
    let endpoint = operation(shift, word, width, amount);
    let middle = restoring_result(shift, word);
    format!("def {name} : Eq IRStepResult ({endpoint}) ({result}) := Eq.trans IRStepResult ({endpoint}) ({middle}) ({result}) ({} {word} (Eq.refl Bool Bool.true)) (Eq.refl IRStepResult ({result}))", shift.law())
}

pub(super) fn check_consumer(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(
        source,
        "actual generic shift law followed by restoring-side computation",
    )
    .unwrap_or_else(|error| panic!("{name}: {error}"));
    certified(spec, name);
}

fn kernel_result(spec: &Specification, source: &str) -> Expr {
    let surface = clean_parser::parse_expr(source).expect("ground shift result parses");
    let mut context = ElabCtx::new(spec.env());
    let term = context
        .elaborate(&surface)
        .expect("ground shift result elaborates without registering vocabulary");
    let term = context.metas().instantiate(&term);
    let term = context.metas().instantiate_levels(&term);
    assert!(!term.has_fvar_quick());
    assert!(!term.has_expr_mvar_quick());
    assert!(!term.has_level_mvar_quick());
    term
}

fn strict_checker(spec: &Specification) -> TypeChecker<'_> {
    let mut checker = TypeChecker::new(spec.env());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    // Retain the environment's actual limits, or the unchanged kernel defaults.
    if let Some(Some(value)) = spec.env().get_option("maxHeartbeats") {
        if let Ok(limit) = value.parse::<u32>() {
            checker.set_heartbeat_limit(limit);
        }
    }
    if let Some(Some(value)) = spec.env().get_option("tcMaxCacheEntries") {
        if let Ok(max) = value.parse::<usize>() {
            checker.set_max_cache_entries(max);
        }
    }
    checker
}

fn assert_unspent(checker: &TypeChecker<'_>, case: &str) {
    assert!(
        !checker.heartbeat_spent(),
        "{case}: checker must finish within its limit"
    );
    assert!(
        !clean_kernel::tc::declaration_budget_exhausted(),
        "{case}: ambient declaration budget must remain unspent"
    );
}

fn result_eq(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            Expr::const_(Name::from_string("IRStepResult"), vec![]),
            left,
            right,
        ],
    )
}

fn result_refl(result: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::const_(Name::from_string("IRStepResult"), vec![]),
            result,
        ],
    )
}

/// Establish the two distinct literal results before observing a typed refusal.
/// Only bounded restoring terms (or explicitly small actual operations) enter
/// this probe. A string containing "type mismatch" alone is not refutation:
/// the kernel can also leave expensive genuinely equal computations stuck.
pub(super) fn known_false_result_mismatch(
    spec: &Specification,
    case: &str,
    correct: &str,
    wrong: &str,
    actual_literal: u64,
    wrong_literal: u64,
) {
    assert_ne!(
        actual_literal, wrong_literal,
        "{case}: independent expected residues differ"
    );
    let correct = kernel_result(spec, correct);
    let wrong = kernel_result(spec, wrong);
    for (term, literal) in [(&correct, actual_literal), (&wrong, wrong_literal)] {
        let literal = Expr::app(
            Expr::const_(Name::from_string("IRStepResult.value"), vec![]),
            Expr::app(
                Expr::const_(Name::from_string("IRScalar.int_"), vec![]),
                Expr::nat_lit(literal),
            ),
        );
        let goal = result_eq(term.clone(), literal.clone());
        let checker = strict_checker(spec);
        assert!(checker
            .infer_sort(&goal)
            .expect("literal result equality is well-typed")
            .is_zero());
        checker
            .check_type(&result_refl(literal), &goal)
            .unwrap_or_else(|error| panic!("{case}: independently expected normal form: {error}"));
        assert_unspent(&checker, case);
    }
    let goal = result_eq(correct, wrong.clone());
    let checker = strict_checker(spec);
    assert!(checker
        .infer_sort(&goal)
        .expect("known-false result equality is well-typed")
        .is_zero());
    let error = checker
        .check_type(&result_refl(wrong), &goal)
        .expect_err("distinct independently checked result literals cannot be reflexive");
    assert!(
        matches!(error, TypeError::TypeMismatch { .. }),
        "{case}: {error}"
    );
    assert_unspent(&checker, case);
}

pub(super) fn known_false_type_mismatch(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "deliberately false actual shift claim")
        .expect_err("false shift arithmetic must refuse");
    let detail = match error {
        SpecError::ElabError(detail) | SpecError::TypeError(detail) => detail,
        other => panic!("{name}: known-false type mismatch required, got {other}"),
    };
    let lower = detail.to_ascii_lowercase();
    assert!(lower.contains("type mismatch"), "{name}: {detail}");
    for resource in [
        "budget",
        "heartbeat",
        "fuel exhausted",
        "recursion limit",
        "depth limit",
        "unknown identifier",
        "parse error",
    ] {
        assert!(!lower.contains(resource), "{name}: {detail}");
    }
    assert!(spec.get_definition(name).is_none());
    assert!(spec.env().get_const(&Name::from_string(name)).is_none());
}

pub(super) fn collision(error: SpecError, name: &str) {
    match error {
        SpecError::EnvError(detail) => {
            assert!(
                detail.contains("name collision") && detail.contains(name),
                "{detail}"
            );
        }
        other => panic!("exact name collision required for {name}: {other}"),
    }
}
