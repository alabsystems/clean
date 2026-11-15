// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Re-registration must compare payloads, not only existing name membership.
//! These public admission regressions are not a proof of Rust execution.

use std::collections::BTreeMap;

use clean_kernel::env::EnvError;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveError, InductiveType};
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};
use serde::Serialize;
use serde_json::Value;

fn json(value: &impl Serialize) -> Value {
    serde_json::to_value(value).expect("declaration records must serialize")
}

#[derive(Debug, PartialEq)]
struct DeclarationTables {
    generation: u64,
    counts: [usize; 4],
    tables: Vec<BTreeMap<Name, Value>>,
    safety_marks: BTreeMap<Name, (bool, bool)>,
}

// Canonicalize outer HashMap order, retaining ordered fields in each record.
// This compares all four declaration tables and public provenance, not private
// cache bytes or every other internal Environment field.
fn tables(env: &Environment) -> DeclarationTables {
    DeclarationTables {
        generation: env.generation(),
        counts: [
            env.num_constants(),
            env.num_inductives(),
            env.num_constructors(),
            env.num_recursors(),
        ],
        tables: vec![
            env.constants().map(|v| (v.name.clone(), json(v))).collect(),
            env.inductives()
                .map(|v| (v.name.clone(), json(v)))
                .collect(),
            env.constructors()
                .map(|v| (v.name.clone(), json(v)))
                .collect(),
            env.recursors().map(|v| (v.name.clone(), json(v))).collect(),
            env.constants()
                .map(|v| (v.name.clone(), json(&env.declaration_verification(&v.name))))
                .collect(),
            env.constants()
                .map(|v| (v.name.clone(), json(&env.get_constant_origin(&v.name))))
                .collect(),
        ],
        safety_marks: env
            .constants()
            .map(|value| {
                let name = &value.name;
                (name.clone(), (env.is_unsafe(name), env.is_partial(name)))
            })
            .collect(),
    }
}

fn family(name: &str) -> InductiveDecl {
    let name = Name::from_string(name);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: name.clone().str("mk"),
                type_: Expr::const_(name, vec![]),
            }],
        }],
    }
}

fn add(env: &mut Environment, decl: InductiveDecl, core_only: bool) -> Result<(), EnvError> {
    if core_only {
        env.add_inductive_core(decl)
    } else {
        env.add_inductive(decl)
    }
}

fn assert_changed_refused(original: InductiveDecl, changed: InductiveDecl) {
    let collision = changed.types[0].name.clone();
    for core_only in [false, true] {
        let mut env = Environment::new();
        add(&mut env, original.clone(), core_only)
            .expect("the initial source must be genuinely admitted");
        let before = tables(&env);
        let result = add(&mut env, changed.clone(), core_only);
        assert_eq!(
            tables(&env),
            before,
            "refusal must preserve declaration state"
        );
        let error = result.expect_err("same names do not imply the same declaration");
        assert!(
            matches!(error, EnvError::DuplicateName(ref name) if name == &collision),
            "core_only={core_only}: expected the changed family's collision, got {error:?}"
        );
    }
}

#[test]
fn reregistration_changed_former_is_not_a_noop() {
    let original = family("ReregisterFormer");
    let mut changed = original.clone();
    changed.types[0].type_ = Expr::bvar(0);
    assert_changed_refused(original, changed);
}

#[test]
fn reregistration_unknown_constructor_field_is_not_a_noop() {
    let original = family("ReregisterField");
    let mut changed = original.clone();
    let old_return = changed.types[0].constructors[0].type_.clone();
    changed.types[0].constructors[0].type_ = Expr::arrow(
        Expr::const_(Name::from_string("ReregisterMissingFieldType"), vec![]),
        old_return,
    );
    assert_changed_refused(original, changed);
}

#[test]
fn reregistration_removed_constructor_is_not_a_noop() {
    let mut original = family("ReregisterConstructors");
    let mut second = original.types[0].constructors[0].clone();
    second.name = original.types[0].name.clone().str("other");
    original.types[0].constructors.push(second);
    let mut changed = original.clone();
    changed.types[0]
        .constructors
        .pop()
        .expect("two original constructors");
    assert_changed_refused(original, changed);
}

fn two_constructor_family(name: &str) -> InductiveDecl {
    let mut decl = family(name);
    let mut other = decl.types[0].constructors[0].clone();
    other.name = decl.types[0].name.clone().str("other");
    decl.types[0].constructors.push(other);
    decl
}

fn mutual_family() -> InductiveDecl {
    let mut decl = family("ReregisterMutualLeft");
    decl.types.extend(family("ReregisterMutualRight").types);
    decl
}

fn assert_noop(env: &mut Environment, original: &InductiveDecl, core_only: bool) {
    let before = tables(env);
    add(env, original.clone(), core_only).expect("the identical source remains an allowed no-op");
    assert_eq!(
        tables(env),
        before,
        "a no-op must not alter tables or provenance"
    );
}

#[test]
fn reregistration_reordered_constructors_is_not_a_noop() {
    let original = two_constructor_family("ReregisterCtorOrder");
    let mut changed = original.clone();
    changed.types[0].constructors.reverse();
    assert_changed_refused(original, changed);
}

#[test]
fn reregistration_erased_constructor_list_is_not_a_noop() {
    let original = family("ReregisterErasedCtors");
    let mut changed = original.clone();
    changed.types[0].constructors.clear();
    assert_changed_refused(original, changed);
}

#[test]
fn reregistration_reduced_mutual_block_is_not_a_noop() {
    let original = mutual_family();
    for retained_member in 0..2 {
        let mut changed = original.clone();
        changed.types = vec![changed.types[retained_member].clone()];
        assert_changed_refused(original.clone(), changed);
    }
}

#[test]
fn reregistration_reordered_mutual_block_is_not_a_noop() {
    let original = mutual_family();
    let mut changed = original.clone();
    changed.types.reverse();
    assert_changed_refused(original, changed);
}

#[test]
fn reregistration_added_universe_parameter_is_not_a_noop() {
    let original = family("ReregisterAddedUniverse");
    let mut changed = original.clone();
    changed.level_params.push(Name::from_string("u"));
    assert_changed_refused(original, changed);
}

#[test]
fn reregistration_reordered_universe_parameters_is_not_a_noop() {
    let mut original = family("ReregisterUniverseOrder");
    original.level_params = vec![Name::from_string("u"), Name::from_string("v")];
    original.types[0].constructors[0].type_ = Expr::const_(
        original.types[0].name.clone(),
        original
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>(),
    );
    let mut changed = original.clone();
    changed.level_params.reverse();
    // Do not rewrite the constructor's ordered level arguments along with the
    // declaration. These are genuinely different source payloads.
    assert_changed_refused(original, changed);
}

fn assert_initial_refusal(
    changed: impl Fn(&mut InductiveDecl),
    owns: impl Fn(&EnvError, &Name, &Name) -> bool,
) {
    for core_only in [false, true] {
        let original = family("ReregisterEarlyValidation");
        let family_name = original.types[0].name.clone();
        let ctor_name = original.types[0].constructors[0].name.clone();
        let mut env = Environment::new();
        add(&mut env, original.clone(), core_only).expect("first admission must succeed");
        let before = tables(&env);
        let mut input = original;
        changed(&mut input);
        let result = add(&mut env, input, core_only);
        assert_eq!(tables(&env), before);
        let error = result.expect_err("initial validation must still refuse malformed input");
        assert!(
            owns(&error, &family_name, &ctor_name),
            "core_only={core_only}: unexpected initial validation error: {error:?}"
        );
    }
}

#[test]
fn reregistration_unreasonable_params_retains_initial_error() {
    assert_initial_refusal(
        |decl| decl.num_params = 2, // Two parameters for a zero-binder former.
        |error, family_name, ctor_name| {
            matches!(
                error,
                EnvError::Inductive(InductiveError::ConstructorParamMismatch {
                    ctor_name: actual_ctor,
                    ind_name: actual_family,
                    param_idx: 0,
                }) if actual_ctor == ctor_name && actual_family == family_name
            )
        },
    );
}

#[test]
fn reregistration_wrong_return_retains_initial_error() {
    assert_initial_refusal(
        |decl| decl.types[0].constructors[0].type_ = Expr::type_(),
        |error, family_name, ctor_name| {
            matches!(
                error,
                EnvError::Inductive(InductiveError::ConstructorReturnType(
                    actual_ctor, actual_family
                )) if actual_ctor == ctor_name && actual_family == family_name
            )
        },
    );
}

#[test]
fn reregistration_duplicate_ctor_retains_initial_error() {
    assert_initial_refusal(
        |decl| {
            let repeated = decl.types[0].constructors[0].clone();
            decl.types[0].constructors.push(repeated);
        },
        |error, _, ctor_name| matches!(error, EnvError::DuplicateName(actual) if actual == ctor_name),
    );
}

#[test]
fn reregistration_identical_plain_source_is_a_noop() {
    for core_only in [false, true] {
        let mut env = Environment::new();
        let original = two_constructor_family("ReregisterPlainNoop");
        add(&mut env, original.clone(), core_only).expect("plain source must actually be admitted");
        for repeated_core_only in [false, true] {
            assert_noop(&mut env, &original, repeated_core_only);
        }
    }
}

#[test]
fn reregistration_identical_empty_family_is_a_noop() {
    for core_only in [false, true] {
        let mut original = family("ReregisterEmptyNoop");
        original.types[0].constructors.clear();
        let mut env = Environment::new();
        add(&mut env, original.clone(), core_only).expect("empty families remain admissible");
        assert_noop(&mut env, &original, core_only);
    }
}

#[test]
fn reregistration_identical_mutual_source_is_a_noop() {
    for core_only in [false, true] {
        let mut env = Environment::new();
        let original = mutual_family();
        add(&mut env, original.clone(), core_only)
            .expect("mutual source must actually be admitted");
        let names: Vec<_> = original
            .types
            .iter()
            .map(|member| member.name.clone())
            .collect();
        for member in &original.types {
            let stored = env
                .get_inductive(&member.name)
                .expect("each mutual member exists");
            assert_eq!(stored.all_names, names);
        }
        for repeated_core_only in [false, true] {
            assert_noop(&mut env, &original, repeated_core_only);
        }
    }
}

fn fixed_index_family() -> InductiveDecl {
    let mut decl = family("ReregisterFixedIndex");
    decl.types[0].type_ = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    decl.types[0].constructors[0].type_ = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::app(
            Expr::const_(decl.types[0].name.clone(), vec![]),
            Expr::bvar(0),
        ),
    );
    decl
}

#[test]
fn reregistration_original_fixed_index_source_is_a_noop_after_promotion() {
    for core_only in [false, true] {
        let original = fixed_index_family();
        assert_eq!(original.num_params, 0);
        let mut env = Environment::new();
        add(&mut env, original.clone(), core_only).expect("the indexed source must be admitted");
        let stored = env
            .get_inductive(&original.types[0].name)
            .expect("family metadata");
        assert_eq!((stored.num_params, stored.num_indices), (1, 0));
        let ctor = env
            .get_constructor(&original.types[0].constructors[0].name)
            .expect("constructor metadata");
        assert_eq!((ctor.num_params, ctor.num_fields), (1, 0));
        // The original pre-promotion p=0 input is essential to this regression.
        // Reconstructing a stored p=1 declaration would not test it.
        for repeated_core_only in [false, true] {
            assert_noop(&mut env, &original, repeated_core_only);
        }
    }
}

fn nested_family() -> InductiveDecl {
    // Same counter/List telescope as the existing inductive_nested_prefix
    // public admission fixture, retaining the original (pre-elimination) data.
    let name = Name::from_string("ReregisterNested");
    let constant = Expr::const_(name.clone(), vec![]);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: name.clone().str("zero"),
                    type_: constant.clone(),
                },
                Constructor {
                    name: name.clone().str("next"),
                    type_: Expr::arrow(constant.clone(), constant.clone()),
                },
                Constructor {
                    name: name.str("children"),
                    type_: Expr::arrow(
                        Expr::app(
                            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
                            constant.clone(),
                        ),
                        constant,
                    ),
                },
            ],
        }],
    }
}

#[test]
fn reregistration_original_nested_source_is_a_noop_after_restoration() {
    // No extra feature or public kernel API: with_prelude and real nested
    // registration run on a standard library thread with a bounded larger stack.
    std::thread::Builder::new()
        .name("reregistration-nested".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let prelude = Environment::with_prelude();
            for core_only in [false, true] {
                let mut env = prelude.clone();
                let original = nested_family();
                let member = &original.types[0];
                add(&mut env, original.clone(), core_only)
                    .expect("the original nested source must actually be admitted");
                let stored = env
                    .get_inductive(&member.name)
                    .expect("restored nested metadata");
                assert!(stored.is_nested);
                assert_eq!(stored.all_names, vec![member.name.clone()]);
                assert_eq!(stored.num_params, original.num_params);
                assert_eq!(
                    stored.constructor_names,
                    member
                        .constructors
                        .iter()
                        .map(|ctor| ctor.name.clone())
                        .collect::<Vec<_>>()
                );
                for ctor in &member.constructors {
                    assert_eq!(
                        env.get_constructor(&ctor.name)
                            .expect("restored constructor")
                            .type_,
                        ctor.type_
                    );
                    assert_eq!(
                        env.get_const(&ctor.name)
                            .expect("restored constructor constant")
                            .type_,
                        ctor.type_
                    );
                }
                assert!(env
                    .get_recursor(&member.name.clone().str("rec_1"))
                    .is_some());
                for repeated_core_only in [false, true] {
                    assert_noop(&mut env, &original, repeated_core_only);
                }
            }
        })
        .expect("spawn the large-stack nested regression")
        .join()
        .expect("nested regression must not panic");
}

#[test]
fn reregistration_empty_ctor_params_change_is_not_a_noop() {
    let mut original = family("ReregisterEmptyParams");
    original.types[0].constructors.clear();
    let mut changed = original.clone();
    changed.num_params = 1;
    // No constructors means initial return-slot validation is vacuous; this
    // checks parameter compatibility at the re-registration boundary itself.
    assert_changed_refused(original, changed);
}

#[test]
fn reregistration_unsafe_or_partial_payload_is_not_a_noop() {
    for core_only in [false, true] {
        for mark_ctor in [false, true] {
            for mark_unsafe in [false, true] {
                let original = family("ReregisterSafetyMarks");
                let member = &original.types[0];
                let marked_name = if mark_ctor {
                    member.constructors[0].name.clone()
                } else {
                    member.name.clone()
                };
                let mut env = Environment::new();
                add(&mut env, original.clone(), core_only)
                    .expect("first admit a real declaration before adding a safety mark");
                assert!(!env.is_unsafe(&marked_name));
                assert!(!env.is_partial(&marked_name));
                if mark_unsafe {
                    env.mark_unsafe(marked_name.clone());
                } else {
                    env.mark_partial(marked_name.clone());
                }
                assert_eq!(env.is_unsafe(&marked_name), mark_unsafe);
                assert_eq!(env.is_partial(&marked_name), !mark_unsafe);
                let before = tables(&env);
                let result = add(&mut env, original.clone(), core_only);
                assert_eq!(
                    tables(&env),
                    before,
                    "refusal must retain both safety marks"
                );
                let error = result.expect_err("canonical spelling does not erase safety marks");
                // The error identifies the first occupied input namespace
                // name, not the first differing payload field or marked name.
                assert!(
                    matches!(error, EnvError::DuplicateName(ref name) if name == &member.name),
                    "core_only={core_only}, mark_ctor={mark_ctor}, mark_unsafe={mark_unsafe}: {error:?}"
                );
                assert_eq!(env.is_unsafe(&marked_name), mark_unsafe);
                assert_eq!(env.is_partial(&marked_name), !mark_unsafe);
            }
        }
    }
}
