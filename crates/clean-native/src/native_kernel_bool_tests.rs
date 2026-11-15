// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_compiler::{
    constant_to_decl_with_meaning,
    lcnf::{Alt, Code, DeclValue, LetValue},
};
use clean_kernel::Declaration;

fn world() -> Environment {
    let mut env = Environment::for_lean_replay();
    env.admit_builtin_source_for_testing(
        include_bytes!("../tests/fixtures/string_bytearray/fixture-lean-4.35.0.json"),
        &["bridgeDynamic"],
    )
    .expect("genuine source Bool definitions in their actual dependency closure");
    env
}

fn add(env: &mut Environment, name: Name, ty: Expr, value: Expr) -> ConstantInfo {
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: false,
    })
    .expect("checked caller");
    env.get_const(&name).expect("published caller").clone()
}

fn bool_value(value: bool) -> Expr {
    Expr::const_str(if value { "Bool.true" } else { "Bool.false" })
}

#[test]
fn exact_logical_bool_values_reduce_without_exporting_noncomputable_roots() {
    let mut env = world();
    for text in ["Bool.and", "Bool.or"] {
        let name = Name::from_string(text);
        let original = env
            .get_const(&name)
            .expect("actual logical definition")
            .clone();
        assert!(env.is_noncomputable(&name));
        for meaning in [CodeMeaning::LeanCompiled, CodeMeaning::KernelValue] {
            assert!(constant_to_decl_with_meaning(&env, &original, meaning)
                .expect("ordinary policy")
                .is_none());
        }
        for a in [false, true] {
            for b in [false, true] {
                let value = Expr::apps(
                    Expr::const_(name.clone(), vec![]),
                    [bool_value(a), bool_value(b)],
                );
                let info = add(
                    &mut env,
                    Name::from_string(&format!("bool_{text}_{a}_{b}")),
                    Expr::const_str("Bool"),
                    value,
                );
                assert!(rewrite(&env, &info, CodeMeaning::LeanCompiled)
                    .expect("mode refusal")
                    .is_none());
                let normalized = rewrite(&env, &info, CodeMeaning::KernelValue)
                    .expect("exact delta normalization")
                    .expect("changed caller");
                let expected = if text == "Bool.and" { a && b } else { a || b };
                assert!(TypeChecker::new(&env).is_def_eq(&normalized, &bool_value(expected)));
            }
        }
        assert!(
            env.is_noncomputable(&name),
            "normalization never changes source tags"
        );
    }
}

#[test]
fn logical_bool_normalization_declines_partial_unsafe_and_component_twins() {
    let mut env = world();
    let bool_ = Expr::const_str("Bool");
    let ty = Expr::arrow(bool_.clone(), bool_.clone());
    let partial = add(
        &mut env,
        Name::from_string("partialBool"),
        ty,
        Expr::app(Expr::const_str("Bool.and"), bool_value(false)),
    );
    assert!(rewrite(&env, &partial, CodeMeaning::KernelValue)
        .expect("partial declined")
        .is_none());
    let twin = Name::anon().str("Bool.and");
    add(
        &mut env,
        twin.clone(),
        Expr::arrow(bool_.clone(), Expr::arrow(bool_.clone(), bool_.clone())),
        expected_body(true),
    );
    env.mark_noncomputable(twin.clone());
    let info = add(
        &mut env,
        Name::from_string("twinBool"),
        bool_.clone(),
        Expr::apps(
            Expr::const_(twin, vec![]),
            [bool_value(true), bool_value(false)],
        ),
    );
    assert!(rewrite(&env, &info, CodeMeaning::KernelValue)
        .expect("typed identity")
        .is_none());
    let info = add(
        &mut env,
        Name::from_string("unsafeBool"),
        bool_,
        Expr::apps(
            Expr::const_str("Bool.and"),
            [bool_value(true), bool_value(false)],
        ),
    );
    for unsafe_flag in [false, true] {
        let mut candidate = env.clone();
        if unsafe_flag {
            candidate.mark_unsafe(Name::from_string("Bool.and"));
        } else {
            candidate.mark_partial(Name::from_string("Bool.and"));
        }
        assert!(rewrite(&candidate, &info, CodeMeaning::KernelValue)
            .expect("unsafe or partial declined")
            .is_none());
    }
}

#[test]
fn a_checked_same_typed_boolean_definition_is_not_permission_to_substitute_it() {
    let mut env = Environment::new();
    let bool_ = Expr::const_str("Bool");
    env.add_inductive_core(clean_kernel::InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![clean_kernel::InductiveType {
            name: Name::from_string("Bool"),
            type_: Expr::type_(),
            constructors: vec![
                clean_kernel::Constructor {
                    name: Name::from_string("Bool.false"),
                    type_: bool_.clone(),
                },
                clean_kernel::Constructor {
                    name: Name::from_string("Bool.true"),
                    type_: bool_.clone(),
                },
            ],
        }],
    })
    .expect("checked enum");
    add(
        &mut env,
        Name::from_string("Bool.and"),
        Expr::arrow(bool_.clone(), Expr::arrow(bool_.clone(), bool_.clone())),
        Expr::lam(
            BinderInfo::Default,
            bool_.clone(),
            Expr::lam(BinderInfo::Default, bool_.clone(), bool_value(false)),
        ),
    );
    env.mark_noncomputable(Name::from_string("Bool.and"));
    let info = add(
        &mut env,
        Name::from_string("counterfeitCaller"),
        bool_,
        Expr::apps(
            Expr::const_str("Bool.and"),
            [bool_value(true), bool_value(true)],
        ),
    );
    assert!(canonical_bool(&env));
    assert!(rewrite(&env, &info, CodeMeaning::KernelValue)
        .expect("different checked body declined")
        .is_none());
}

fn rhs_calls(code: &Code, branch: Option<bool>, expected: bool) -> (usize, usize) {
    let plus = |a: (usize, usize), b: (usize, usize)| (a.0 + b.0, a.1 + b.1);
    match code {
        Code::Let(decl, body) => {
            let mut result = rhs_calls(body, branch, expected);
            if matches!(&decl.value, LetValue::Const { name, .. } if *name == Name::from_string("rightProbe"))
            {
                result.0 += 1;
                result.1 += usize::from(branch != Some(expected));
            }
            result
        }
        Code::Fun(fun, body) => plus(
            rhs_calls(&fun.body, None, expected),
            rhs_calls(body, branch, expected),
        ),
        Code::JoinPoint(fun, body) => plus(
            rhs_calls(&fun.body, None, expected),
            rhs_calls(body, branch, expected),
        ),
        Code::Cases(cases) => cases.alts.iter().fold((0, 0), |sum, alt| {
            let (next, body) = match alt {
                Alt::Ctor {
                    ctor_name, body, ..
                } => {
                    let branch = if *ctor_name == Name::from_string("Bool.false") {
                        Some(false)
                    } else if *ctor_name == Name::from_string("Bool.true") {
                        Some(true)
                    } else {
                        branch
                    };
                    (branch, body)
                }
                Alt::Default(body) => (branch, body),
            };
            plus(sum, rhs_calls(body, next, expected))
        }),
        _ => (0, 0),
    }
}

#[test]
fn right_operand_stays_in_its_selected_branch_even_in_value_position() {
    let mut env = world();
    let bool_ = Expr::const_str("Bool");
    add(
        &mut env,
        Name::from_string("rightProbe"),
        Expr::arrow(bool_.clone(), bool_.clone()),
        Expr::lam(BinderInfo::Default, bool_.clone(), Expr::bvar(0)),
    );
    add(
        &mut env,
        Name::from_string("boolIdentity"),
        Expr::arrow(bool_.clone(), bool_.clone()),
        Expr::lam(BinderInfo::Default, bool_.clone(), Expr::bvar(0)),
    );
    for (text, expected_branch) in [("Bool.and", true), ("Bool.or", false)] {
        let operation = Expr::apps(
            Expr::const_str(text),
            [
                Expr::bvar(1),
                Expr::app(Expr::const_str("rightProbe"), Expr::bvar(0)),
            ],
        );
        let value = Expr::lam(
            BinderInfo::Default,
            bool_.clone(),
            Expr::lam(
                BinderInfo::Default,
                bool_.clone(),
                Expr::app(Expr::const_str("boolIdentity"), operation),
            ),
        );
        let info = add(
            &mut env,
            Name::from_string(&format!("guard_{text}")),
            Expr::arrow(bool_.clone(), Expr::arrow(bool_.clone(), bool_.clone())),
            value,
        );
        let original = constant_to_decl_with_meaning(&env, &info, CodeMeaning::KernelValue)
            .expect("original LCNF")
            .expect("caller");
        let DeclValue::Code(original) = original.body else {
            panic!("original code");
        };
        assert_eq!(
            rhs_calls(&original, None, expected_branch),
            (1, 1),
            "control: generic call evaluates its argument eagerly"
        );
        let normalized = rewrite(&env, &info, CodeMeaning::KernelValue)
            .expect("normalize")
            .expect("changed");
        let mut prepared = info.clone();
        prepared.value = Some(normalized);
        let decl = constant_to_decl_with_meaning(&env, &prepared, CodeMeaning::KernelValue)
            .expect("normalized LCNF")
            .expect("caller");
        let DeclValue::Code(code) = decl.body else {
            panic!("normalized code");
        };
        assert_eq!(
            rhs_calls(&code, None, expected_branch),
            (1, 0),
            "the right operand is evaluated only in the selected alternative"
        );
    }
}
