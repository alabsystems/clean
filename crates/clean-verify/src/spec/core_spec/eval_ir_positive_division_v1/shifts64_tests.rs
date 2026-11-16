// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Independent full-width and amount-zero controls for symbolic shift laws.

use super::{shifts64, verify_root};
use crate::spec::{SpecError, Specification};
use clean_elab::ElabCtx;
use clean_kernel::{Expr, Level, Name, TypeChecker, TypeError};
use std::{collections::BTreeSet, sync::OnceLock};

const ROOTS: [&str; 4] = [
    "ir_byte_lshr_u64_in_range_v1",
    "ir_byte_ashr_i64_in_range_v1",
    "ir_byte_lshr_u64_in_range_result_bound_v1",
    "ir_byte_ashr_i64_in_range_result_bound_v1",
];

const NAMES: [&str; 23] = [
    "ir_nat_pow2_positive_v1",
    "ir_nat_shl_monotone_v1",
    "ir_nat_shl_pow2_add_v1",
    "ir_nat_shl_one_pow2_v1",
    "ir_nat_mul_pow2_add_v1",
    "ir_nat_mul_pow2_sub_v1",
    "ir_nat_pow2_sub_le_v1",
    "ir_positive_divisor_agrees_v1",
    "ir_positive_pow2_divisor_agrees_v1",
    "ir_positive_division_u64_word_fuel_v1",
    "ir_positive_division_u64_fill_fuel_v1",
    "ir_positive_division_u64_word_shift_v1",
    "ir_positive_division_u64_fill_shift_v1",
    "ir_positive_division_u64_word_quotient_lt_v1",
    "ir_positive_division_u64_fill_quotient_v1",
    "ir_lshr_bits_in_range_v1",
    "ir_ashr_bits_in_range_v1",
    "ir_byte_u64_shift_amount_fits_v1",
    "ir_positive_division_u64_ashr_value_v1",
    "ir_byte_lshr_u64_in_range_v1",
    "ir_byte_ashr_i64_in_range_v1",
    "ir_byte_lshr_u64_in_range_result_bound_v1",
    "ir_byte_ashr_i64_in_range_result_bound_v1",
];

fn base() -> &'static Specification {
    static BASE: OnceLock<Specification> = OnceLock::new();
    BASE.get_or_init(|| {
        crate::build_u64_shift_by_three_output_bounds_byte_prelude_spec_v1_with_stack()
            .expect("existing public checked output-bound profile")
    })
}

fn general() -> &'static Specification {
    static SPEC: OnceLock<Specification> = OnceLock::new();
    SPEC.get_or_init(|| {
        let mut spec = base().clone();
        spec.install_eval_ir_u64_in_range_shift_laws_v1()
            .expect("actual additive symbolic shift sources");
        spec
    })
}

fn certified(spec: &Specification, name: &str) {
    verify_root(spec, name).unwrap_or_else(|error| panic!("{name}: {error}"));
    let key = Name::from_string(name);
    let info = spec.env().get_const(&key).expect("stored declaration");
    let term = Expr::const_(
        key.clone(),
        info.level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>(),
    );
    let audit = spec.env().audit_certification(&info.type_, &term);
    assert!(audit.is_certified(), "{name}: {audit:#?}");
    assert!(audit.dependencies.contains(&key));
    assert!(spec.env().axiom_deps(&key).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&key).unwrap().is_empty());
}

fn old_declarations_unchanged(before: &Specification, after: &Specification) {
    for (name, expected) in before.definitions() {
        let actual = after
            .get_definition(name)
            .expect("prior definition retained");
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

fn owner_unchanged(before: &Specification, after: &Specification) {
    let empty = before.env().effect_since(before.env());
    let actual = after.env().effect_since(before.env());
    assert_eq!(empty.disagreement(&actual, after.env()), None);
    assert_eq!(before.env().generation(), after.env().generation());
    assert_eq!(before.definitions().len(), after.definitions().len());
    old_declarations_unchanged(before, after);
}

fn quotient(word: &str, amount: &str, fuel: u64) -> String {
    format!(
        "ir_dm_quot (ir_dm_go 1 ({word}) {fuel} (ir_nat_pow2 ({amount})) (IRDivMod.mk ({word}) 0))"
    )
}

#[derive(Clone, Copy)]
enum Shift {
    Logical,
    Arithmetic,
}

impl Shift {
    fn opcode(self) -> &'static str {
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
    fn root(self) -> &'static str {
        match self {
            Self::Logical => ROOTS[0],
            Self::Arithmetic => ROOTS[1],
        }
    }
    fn bound(self) -> &'static str {
        match self {
            Self::Logical => ROOTS[2],
            Self::Arithmetic => ROOTS[3],
        }
    }
    fn fit(self) -> &'static str {
        match self {
            Self::Logical => "ir_byte_u64_value_fits_v1",
            Self::Arithmetic => "ir_byte_i64_value_fits_v1",
        }
    }
    fn value(self, word: &str, amount: &str) -> String {
        let q = quotient(word, amount, 64);
        match self {
            Self::Logical => q,
            Self::Arithmetic => {
                let fill = quotient("ir_nat_pow2 64", amount, 65);
                format!("@Bool.rec (fun (_ : Bool) => Nat) ({q}) (Nat.add ({q}) (Nat.sub (ir_nat_pow2 64) ({fill}))) (ir_sign_bit 64 ({word}))")
            }
        }
    }
}

fn add(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(
        source,
        "independent actual-operation and restoring result control",
    )
    .unwrap_or_else(|error| panic!("{name}: {error}"));
    certified(spec, name);
}

#[test]
fn general_shift_sources_are_additive_checked_and_separate_from_default_byte() {
    crate::test_utils::run_with_stack(|| {
        assert_eq!(shifts64::ROOTS, ROOTS);
        assert_eq!(
            shifts64::laws().map(|(name, _)| name).collect::<Vec<_>>(),
            NAMES
        );
        let names = shifts64::laws()
            .map(|(name, _)| name)
            .collect::<BTreeSet<_>>();
        assert_eq!(names.len(), NAMES.len(), "no repeated fixed name");
        let spec = general();
        assert_eq!(
            spec.definitions().len(),
            base().definitions().len() + names.len()
        );
        old_declarations_unchanged(base(), spec);
        let delta = spec.env().effect_since(base().env());
        assert_eq!(
            delta
                .changed_constant_names()
                .map(ToString::to_string)
                .collect::<BTreeSet<_>>(),
            names.iter().map(|name| (*name).to_owned()).collect()
        );
        let default = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
        for name in names {
            assert!(base().get_definition(name).is_none());
            assert!(default.get_definition(name).is_none());
            certified(spec, name);
        }
    });
}

#[test]
fn arbitrary_amount_operations_connect_to_actual_nominal_fits_without_result_premises() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = general().clone();
        for shift in [Shift::Logical, Shift::Arithmetic] {
            let op = shift.opcode();
            let carrier = shift.carrier();
            let value = shift.value("word", "amount");
            let root = shift.root();
            let bound = shift.bound();
            let fit = shift.fit();
            let name = format!("general_shift_{op}_universal");
            let actual = format!("ir_binop_eval IRBinOp.{op} (IRTy.{carrier} 64) (IRScalar.int_ word) (IRScalar.int_ amount)");
            let result = format!("IRStepResult.value (IRScalar.int_ ({value}))");
            let output_fit = format!("@Eq Bool (ir_byte_value_matches_v1 ctx (IRTy.{carrier} 64) (IRScalar.int_ ({value}))) Bool.true");
            add(
                &mut spec,
                &name,
                &format!(
                    "def {name} (ctx : IRByteContextV1) (word amount : Nat) \
                 (input : Nat.lt word (ir_nat_pow2 64)) (inRange : Nat.lt amount 64) : \
                 And (@Eq IRStepResult ({actual}) ({result})) ({output_fit}) := \
                 let fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true := \
                   ir_byte_ltb_of_lt_v1 word (ir_nat_pow2 64) input; \
                 @And.intro (@Eq IRStepResult ({actual}) ({result})) ({output_fit}) \
                   ({root} word amount fits inRange) \
                   ({fit} ctx ({value}) ({bound} word amount fits inRange))"
                ),
            );
        }
    });
}

#[test]
fn independent_fullwidth_residues_cover_amount_zero_one_three_thirty_one_and_sixty_three() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = general().clone();
        for (word, amount) in [
            (0_u64, 0_u64),
            (u64::MAX, 0),
            (1_u64 << 63, 0),
            (0, 1),
            (1, 1),
            (u64::MAX, 1),
            (1_u64 << 63, 1),
            (7, 3),
            (8, 3),
            (u64::MAX - 7, 3),
            ((1_u64 << 31) - 1, 31),
            (1_u64 << 31, 31),
            (i64::MAX as u64, 63),
            (1_u64 << 63, 63),
            (u64::MAX, 63),
        ] {
            for shift in [Shift::Logical, Shift::Arithmetic] {
                let value = shift.value(&word.to_string(), &amount.to_string());
                let expected = match shift {
                    Shift::Logical => word >> amount,
                    Shift::Arithmetic => ((word as i64) >> amount) as u64,
                };
                let name = format!(
                    "general_shift_{}_{}_{}_residue",
                    shift.opcode(),
                    word,
                    amount
                );
                add(
                    &mut spec,
                    &name,
                    &format!(
                        "def {name} : @Eq Nat ({value}) {expected} := @Eq.refl Nat {expected}"
                    ),
                );
                let bounded = format!("{name}_bound");
                let law = shift.bound();
                add(
                    &mut spec,
                    &bounded,
                    &format!(
                    "def {bounded} : @Eq Bool (ir_nat_ltb ({value}) (ir_nat_pow2 64)) Bool.true := \
                     {law} {word} {amount} (ir_byte_ltb_of_lt_v1 {word} (ir_nat_pow2 64) \
                       (@Nat.le_add_right (Nat.succ {word}) {})) \
                       (@Nat.le_add_right (Nat.succ {amount}) {})", u64::MAX - word, 63 - amount),
                );
            }
        }
    });
}

fn elaborate(spec: &Specification, source: &str) -> Expr {
    let parsed = clean_parser::parse_expr(source).unwrap();
    let mut ctx = ElabCtx::new(spec.env());
    let term = ctx.elaborate(&parsed).unwrap();
    let term = ctx.metas().instantiate(&term);
    let term = ctx.metas().instantiate_levels(&term);
    assert!(!term.has_fvar_quick() && !term.has_expr_mvar_quick() && !term.has_level_mvar_quick());
    term
}

fn checker(spec: &Specification) -> TypeChecker<'_> {
    let mut checker = TypeChecker::new(spec.env());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    if let Some(Some(value)) = spec.env().get_option("maxHeartbeats") {
        checker.set_heartbeat_limit(
            value
                .parse()
                .expect("maintained declaration heartbeat option"),
        );
    }
    if let Some(Some(value)) = spec.env().get_option("tcMaxCacheEntries") {
        checker.set_max_cache_entries(value.parse().expect("maintained declaration cache option"));
    }
    checker
}

#[test]
fn amount_zero_requires_fill_fuel_sixty_five_and_amount_sixty_four_is_out_of_range() {
    crate::test_utils::run_with_stack(|| {
        let spec = general();
        let checker = checker(spec);
        for (boolean, actual) in [
            (
                "ir_nat_ltb (ir_nat_pow2 64) (ir_nat_shl (ir_nat_pow2 0) 65)".to_owned(),
                "Bool.true",
            ),
            (
                "ir_nat_ltb (ir_nat_pow2 64) (ir_nat_shl (ir_nat_pow2 0) 64)".to_owned(),
                "Bool.false",
            ),
            ("ir_nat_ltb 64 64".to_owned(), "Bool.false"),
        ] {
            checker
                .check_type(
                    &elaborate(spec, &format!("@Eq.refl Bool {actual}")),
                    &elaborate(spec, &format!("@Eq Bool ({boolean}) {actual}")),
                )
                .unwrap();
            let opposite = if actual == "Bool.true" {
                "Bool.false"
            } else {
                "Bool.true"
            };
            let error = checker
                .check_type(
                    &elaborate(spec, &format!("@Eq.refl Bool {opposite}")),
                    &elaborate(spec, &format!("@Eq Bool ({boolean}) {opposite}")),
                )
                .unwrap_err();
            assert!(matches!(error, TypeError::TypeMismatch { .. }), "{error}");
            assert!(!checker.heartbeat_spent());
            assert!(!clean_kernel::tc::declaration_budget_exhausted());
        }
        for (fuel, expected) in [(64, u64::MAX.to_string()), (65, "ir_nat_pow2 64".into())] {
            let q = quotient("ir_nat_pow2 64", "0", fuel);
            checker
                .check_type(
                    &elaborate(spec, &format!("@Eq.refl Nat ({expected})")),
                    &elaborate(spec, &format!("@Eq Nat ({q}) ({expected})")),
                )
                .unwrap();
            assert!(!checker.heartbeat_spent());
        }
    });
}

#[test]
fn every_general_name_collision_and_false_final_law_leave_owner_unchanged() {
    crate::test_utils::run_with_stack(|| {
        for (name, _) in shifts64::laws() {
            let mut spec = base().clone();
            spec.add_recursive_def(
                &format!("def {name} : Nat := 0"),
                "exact fixed-name collision",
            )
            .unwrap();
            let before = spec.clone();
            let error = shifts64::install_transactionally(&mut spec, shifts64::laws()).unwrap_err();
            assert!(
                matches!(error, SpecError::EnvError(ref detail) if detail.contains("name collision") && detail.contains(name)),
                "{error}"
            );
            owner_unchanged(&before, &spec);
        }
        const BAD: &str = "def ir_byte_ashr_i64_in_range_result_bound_v1 : @Eq Bool Bool.true Bool.false := @Eq.refl Bool Bool.false";
        let mut spec = base().clone();
        let before = spec.clone();
        assert_eq!(
            shifts64::laws().last().unwrap().0,
            ROOTS[3],
            "actual final transaction row"
        );
        let rows = shifts64::laws().map(|(name, source)| {
            if name == ROOTS[3] {
                (name, BAD)
            } else {
                (name, source)
            }
        });
        let error = shifts64::install_transactionally(&mut spec, rows).unwrap_err();
        let detail = match error {
            SpecError::ElabError(detail) | SpecError::TypeError(detail) => detail,
            other => panic!("actual final source must reach typed refusal: {other}"),
        };
        assert!(
            detail.contains(ROOTS[3]) && detail.to_ascii_lowercase().contains("type mismatch"),
            "{detail}"
        );
        for resource in [
            "budget",
            "heartbeat",
            "fuel exhausted",
            "recursion limit",
            "unknown constant",
        ] {
            assert!(!detail.to_ascii_lowercase().contains(resource), "{detail}");
        }
        owner_unchanged(&before, &spec);
    });
}
