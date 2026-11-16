// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::{output_bounds, verify_root};
use crate::spec::{SpecError, Specification};
use clean_elab::ElabCtx;
use clean_kernel::{Expr, Level, Name, TypeChecker, TypeError};
use std::collections::BTreeSet;
use std::sync::OnceLock;

const EXPECTED: [&str; 7] = [
    "ir_nat_mul_le_right_v1",
    "ir_nat_quot_lt_of_decomposition_v1",
    "ir_dm_quot_lt_v1",
    "ir_nat_add_sub_lt_of_lt_le_v1",
    "ir_positive_division_u64_fill_quotient_by_three_v1",
    "ir_byte_lshr_u64_by_three_result_bound_v1",
    "ir_byte_ashr_i64_by_three_result_bound_v1",
];

fn shifted() -> &'static Specification {
    static SPEC: OnceLock<Specification> = OnceLock::new();
    SPEC.get_or_init(|| {
        crate::eval_ir::build_u64_shift_by_three_byte_prelude_spec_v1_with_stack()
            .expect("ordinary public owned shift-by-three vocabulary")
    })
}

fn bounded_shifts() -> &'static Specification {
    static SPEC: OnceLock<Specification> = OnceLock::new();
    SPEC.get_or_init(|| {
        let mut spec = shifted().clone();
        spec.install_eval_ir_u64_shift_by_three_output_bound_laws_v1()
            .expect("ordinary additive output-bound installer");
        spec
    })
}

fn certified(spec: &Specification, name: &str) {
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

fn previous_definitions_unchanged(before: &Specification, after: &Specification) {
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
            axiom_deps,
        );
        let key = Name::from_string(name);
        assert_eq!(before.env().get_const(&key), after.env().get_const(&key));
        assert_eq!(
            before.env().declaration_verification(&key),
            after.env().declaration_verification(&key),
        );
    }
}

fn owner_unchanged(before: &Specification, after: &Specification) {
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

fn quotient(word: &str, fuel: u64) -> String {
    format!("ir_dm_quot (ir_dm_go 1 ({word}) {fuel} 8 (IRDivMod.mk ({word}) 0))")
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

    fn bound_law(self) -> &'static str {
        match self {
            Self::Logical => "ir_byte_lshr_u64_by_three_result_bound_v1",
            Self::Arithmetic => "ir_byte_ashr_i64_by_three_result_bound_v1",
        }
    }

    fn operation_law(self) -> &'static str {
        match self {
            Self::Logical => "ir_byte_lshr_u64_by_three_v1",
            Self::Arithmetic => "ir_byte_ashr_i64_by_three_v1",
        }
    }

    fn value_fit_law(self) -> &'static str {
        match self {
            Self::Logical => "ir_byte_u64_value_fits_v1",
            Self::Arithmetic => "ir_byte_i64_value_fits_v1",
        }
    }

    fn value(self, word: &str) -> String {
        let q = quotient(word, 64);
        match self {
            Self::Logical => q,
            Self::Arithmetic => {
                let fill = quotient("ir_nat_pow2 64", 64);
                format!("@Bool.rec (fun (_ : Bool) => Nat) ({q}) (Nat.add ({q}) (Nat.sub (ir_nat_pow2 64) ({fill}))) (ir_sign_bit 64 ({word}))")
            }
        }
    }
}

fn add_checked(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(source, "ordinary actual shift and derived canonical result")
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    certified(spec, name);
}

#[test]
fn output_bound_extension_adds_exact_seven_checked_laws_and_preserves_default_owners() {
    crate::test_utils::run_with_stack(|| {
        assert_eq!(
            output_bounds::LAWS
                .iter()
                .map(|(name, _)| *name)
                .collect::<Vec<_>>(),
            EXPECTED
        );
        let before = shifted();
        let after = bounded_shifts();
        assert_eq!(
            after.definitions().len(),
            before.definitions().len() + EXPECTED.len()
        );
        let delta = after.env().effect_since(before.env());
        assert_eq!(
            delta
                .changed_constant_names()
                .map(ToString::to_string)
                .collect::<BTreeSet<_>>(),
            EXPECTED
                .iter()
                .map(|name| (*name).to_owned())
                .collect::<BTreeSet<_>>(),
        );
        previous_definitions_unchanged(before, after);
        for name in EXPECTED {
            assert!(before.get_definition(name).is_none());
            certified(after, name);
        }
        let default =
            crate::eval_ir::build_byte_prelude_spec_v1_with_stack().expect("default ByteV1");
        for name in EXPECTED {
            assert!(default.get_definition(name).is_none());
        }
        assert!(default
            .get_definition("ir_byte_ashr_i64_by_three_v1")
            .is_none());
        owner_unchanged(before, shifted());
    });
}

#[test]
fn output_bound_owned_factory_replays_the_exact_installed_profile() {
    crate::test_utils::run_with_stack(|| {
        let actual =
            crate::eval_ir::build_u64_shift_by_three_output_bounds_byte_prelude_spec_v1_with_stack(
            )
            .expect("public disposable-owner factory includes derived result bounds");
        let installed = bounded_shifts();
        assert_eq!(actual.definitions().len(), installed.definitions().len());
        previous_definitions_unchanged(installed, &actual);
        for name in EXPECTED {
            certified(&actual, name);
        }
        let default = crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
            .expect("default Byte remains separate");
        for name in EXPECTED {
            assert!(default.get_definition(name).is_none());
        }
    });
}

#[test]
fn output_bounds_connect_arbitrary_full64_actual_operations_to_nominal_result_fits() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = bounded_shifts().clone();
        for shift in [Shift::Logical, Shift::Arithmetic] {
            let name = format!("bounded_shift_universal_{}", shift.opcode());
            let word = shift.value("word");
            let value = format!("IRScalar.int_ ({word})");
            let op = shift.opcode();
            let carrier = shift.carrier();
            let bound = shift.bound_law();
            let operation_law = shift.operation_law();
            let value_fit_law = shift.value_fit_law();
            let source = format!(
                "def {name} (ctx : IRByteContextV1) (word : Nat) \
                 (inputBound : Nat.lt word (ir_nat_pow2 64)) : \
                 And (@Eq IRStepResult \
                   (ir_binop_eval IRBinOp.{op} (IRTy.{carrier} 64) (IRScalar.int_ word) (IRScalar.int_ 3)) \
                   (IRStepResult.value ({value}))) \
                 (@Eq Bool (ir_byte_value_matches_v1 ctx (IRTy.{carrier} 64) ({value})) Bool.true) := \
                 let fits : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true := \
                   ir_byte_ltb_of_lt_v1 word (ir_nat_pow2 64) inputBound; \
                 @And.intro \
                   (@Eq IRStepResult \
                     (ir_binop_eval IRBinOp.{op} (IRTy.{carrier} 64) (IRScalar.int_ word) (IRScalar.int_ 3)) \
                     (IRStepResult.value ({value}))) \
                   (@Eq Bool (ir_byte_value_matches_v1 ctx (IRTy.{carrier} 64) ({value})) Bool.true) \
                   ({operation_law} word fits) \
                   ({value_fit_law} ctx ({word}) ({bound} word fits))"
            );
            add_checked(&mut spec, &name, &source);
            let nat_bound = format!("def {name}_nat_bound (word : Nat) (inputBound : Nat.lt word (ir_nat_pow2 64)) : Nat.lt ({word}) (ir_nat_pow2 64) := ir_byte_separation_lt_of_ltb_v1 ({word}) (ir_nat_pow2 64) ({bound} word (ir_byte_ltb_of_lt_v1 word (ir_nat_pow2 64) inputBound))");
            add_checked(&mut spec, &format!("{name}_nat_bound"), &nat_bound);
        }
    });
}

#[test]
fn output_bounds_cover_zero_transition_and_full64_positive_and_negative_encodings() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = bounded_shifts().clone();
        for word in [
            0_u64,
            7,
            8,
            i64::MAX as u64,
            1_u64 << 63,
            u64::MAX - 7,
            u64::MAX,
        ] {
            for shift in [Shift::Logical, Shift::Arithmetic] {
                let name = format!("derived_bound_{}_{}", shift.opcode(), word);
                let result = shift.value(&word.to_string());
                let law = shift.bound_law();
                add_checked(&mut spec, &name, &format!("def {name} : @Eq Bool (ir_nat_ltb ({result}) (ir_nat_pow2 64)) Bool.true := {law} {word} (@Eq.refl Bool Bool.true)"));
                let expected = match shift {
                    Shift::Logical => word >> 3,
                    Shift::Arithmetic => ((word as i64) >> 3) as u64,
                };
                let literal_name = format!("{name}_independent_residue");
                add_checked(&mut spec, &literal_name, &format!("def {literal_name} : @Eq Nat ({result}) {expected} := @Eq.refl Nat {expected}"));
            }
        }
    });
}

fn elaborate(spec: &Specification, source: &str) -> Expr {
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

fn strict_checker(spec: &Specification) -> TypeChecker<'_> {
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

#[test]
fn output_bounds_refuse_known_false_quotient_fill_and_fuel_changes_without_resource_exhaustion() {
    crate::test_utils::run_with_stack(|| {
        let spec = bounded_shifts();
        for (case, false_boolean) in [
            (
                "quotient_upper_one",
                format!("ir_nat_ltb ({}) 1", quotient("8", 64)),
            ),
            (
                "quotient_not_strictly_below_fill",
                "ir_nat_ltb (Nat.add 1 (Nat.sub 8 1)) 8".into(),
            ),
            (
                "fill_above_limit",
                "ir_nat_ltb (Nat.add 8 (Nat.sub 8 9)) 8".into(),
            ),
        ] {
            let false_goal = elaborate(spec, &format!("@Eq Bool ({false_boolean}) Bool.false"));
            let false_proof = elaborate(spec, "@Eq.refl Bool Bool.false");
            let checker = strict_checker(spec);
            checker
                .check_type(&false_proof, &false_goal)
                .expect("independent false normal form");
            let bad_goal = elaborate(spec, &format!("@Eq Bool ({false_boolean}) Bool.true"));
            let bad_proof = elaborate(spec, "@Eq.refl Bool Bool.true");
            let error = checker
                .check_type(&bad_proof, &bad_goal)
                .expect_err("mathematically false bound");
            assert!(
                matches!(error, TypeError::TypeMismatch { .. }),
                "{case}: {error}"
            );
            assert!(
                !checker.heartbeat_spent(),
                "{case}: unchanged limit remains unspent"
            );
            assert!(!clean_kernel::tc::declaration_budget_exhausted());
        }
        let zero_fill = quotient("ir_nat_pow2 64", 0);
        let checker = strict_checker(spec);
        checker
            .check_type(
                &elaborate(spec, "@Eq.refl Nat 0"),
                &elaborate(spec, &format!("@Eq Nat ({zero_fill}) 0")),
            )
            .expect("zero restoring fuel yields quotient zero, not 2^61");
        let error = checker
            .check_type(
                &elaborate(spec, "ir_positive_division_u64_fill_quotient_by_three_v1"),
                &elaborate(spec, &format!("@Eq Nat ({zero_fill}) (ir_nat_pow2 61)")),
            )
            .expect_err("actual fuel64 equality cannot certify fuel0");
        assert!(matches!(error, TypeError::TypeMismatch { .. }), "{error}");
        assert!(!checker.heartbeat_spent());
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
    });
}

#[test]
fn output_bound_installer_refuses_every_collision_and_rolls_back_a_late_false_law() {
    crate::test_utils::run_with_stack(|| {
        for name in EXPECTED {
            let mut spec = shifted().clone();
            spec.add_recursive_def(&format!("def {name} : Nat := 0"), "collision control")
                .expect("ordinary conflicting declaration");
            let before = spec.clone();
            let error = spec
                .install_eval_ir_u64_shift_by_three_output_bound_laws_v1()
                .expect_err("every occupied fixed name refuses");
            assert!(
                matches!(error, SpecError::EnvError(ref detail) if detail.contains("name collision") && detail.contains(name)),
                "{error}"
            );
            owner_unchanged(&before, &spec);
        }
        let mut spec = shifted().clone();
        let before = spec.clone();
        const FALSE_LAST: &str = "def ir_byte_ashr_i64_by_three_result_bound_v1 : @Eq Bool Bool.true Bool.false := @Eq.refl Bool Bool.false";
        let rows = output_bounds::LAWS.iter().copied().map(|(name, source)| {
            if name == "ir_byte_ashr_i64_by_three_result_bound_v1" {
                (name, FALSE_LAST)
            } else {
                (name, source)
            }
        });
        let error = output_bounds::install_transactionally(&mut spec, rows)
            .expect_err("false final source law must refuse the whole transaction");
        let detail = match error {
            SpecError::ElabError(detail) | SpecError::TypeError(detail) => detail,
            other => panic!("known false declaration expected a typed refusal, got {other}"),
        };
        assert!(
            detail.contains("ir_byte_ashr_i64_by_three_result_bound_v1"),
            "rollback must reach the actual final law, not fail in an earlier helper: {detail}"
        );
        assert!(
            detail.to_ascii_lowercase().contains("type mismatch"),
            "{detail}"
        );
        for resource in [
            "budget",
            "heartbeat",
            "fuel exhausted",
            "depth limit",
            "parse error",
            "unknown identifier",
        ] {
            assert!(!detail.to_ascii_lowercase().contains(resource), "{detail}");
        }
        owner_unchanged(&before, &spec);
        for name in EXPECTED {
            assert!(spec.get_definition(name).is_none());
            assert!(spec.env().get_const(&Name::from_string(name)).is_none());
        }
    });
}
