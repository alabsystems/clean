// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source fixtures for the kernel-checked SMT input preparation boundary.

use super::prepare_integer_ops::prepare_smt_integer_expr;
use crate::tactic::smt_translate::{SmtLibTranslator, SmtSort, TranslateError};
use crate::tactic::{LocalDecl, ProofState};
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Name, TypeChecker};
use clean_parser::SurfaceName;

pub(super) fn source_state(source: &str) -> ProofState {
    let mut env = Environment::with_prelude();
    let decls = clean_parser::parse_file(source).expect("parse source fixture");
    assert!(!decls.is_empty());
    for decl in &decls {
        crate::elaborate_decl_and_register(&mut env, decl)
            .expect("register checked source fixture");
    }
    let name = Name::from_string("smtInput");
    let info = env.get_const(&name).expect("registered source definition");
    let mut body = info.value.as_ref().expect("definition value").clone();
    {
        let tc = TypeChecker::new(&env);
        let inferred = tc
            .infer_type_full(&body)
            .expect("strict source value inference");
        assert!(tc.is_def_eq(&inferred, &info.type_));
    }
    assert!(env
        .axiom_deps(&name)
        .expect("source axiom closure")
        .is_empty());
    let mut context = Vec::new();
    while let ExprKind::Lam(_, domain, value) = body.kind() {
        let fvar = FVarId::new(context.len() as u64);
        let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
        assert_eq!(
            domain.as_ref(),
            &int_ty,
            "fixture binders are Int variables"
        );
        context.push(LocalDecl {
            binder_info: Default::default(),
            fvar,
            name: SurfaceName::component(format!("x{}", context.len()), false),
            ty: domain.as_ref().clone(),
            value: None,
        });
        body = value.instantiate(&Expr::fvar(fvar));
    }
    let state = ProofState::with_context(env, body, context);
    let inferred = state
        .infer_type_strict(
            state.current_goal().expect("fixture goal"),
            &state.current_goal().expect("fixture goal").target,
        )
        .expect("strict opened source inference");
    assert!(
        inferred.is_prop()
            || matches!(inferred.kind(), ExprKind::Const(name, _) if name.to_string() == "Int")
    );
    state
}

fn prepared_translation(source: &str) -> Result<String, TranslateError> {
    let state = source_state(source);
    let goal = state.current_goal().expect("source goal");
    let prepared = prepare_smt_integer_expr(&state, goal, &goal.target)?;
    assert!(state.is_def_eq(goal, &goal.target, &prepared));
    let mut translator = SmtLibTranslator::new();
    for decl in &goal.local_ctx {
        translator.register_fvar(decl.fvar, SmtSort::Int, Expr::fvar(decl.fvar));
    }
    translator.translate_expr(&prepared)
}

#[test]
fn test_source_int_division_numeral_constructors_and_instances() {
    for source in [
        "def smtInput : Int := Int.ediv (Int.ofNat 7) (Int.ofNat 3)",
        "def smtInput : Int := (Int.ofNat 7) / (Int.ofNat 3)",
        "def smtInput : Int := (7 : Int) / (3 : Int)",
    ] {
        assert_eq!(
            prepared_translation(source).expect("checked source division translates"),
            "(ite (= 3 0) 0 (div 7 3))",
            "{source}"
        );
    }
}

#[test]
fn test_source_int_division_variables_and_modulus_use_actual_builtin_fields() {
    for (body, expected) in [
        ("a / b", "(ite (= fvar_1 0) 0 (div fvar_0 fvar_1))"),
        ("a % b", "(ite (= fvar_1 0) fvar_0 (mod fvar_0 fvar_1))"),
    ] {
        assert_eq!(
            prepared_translation(&format!("def smtInput (a b : Int) : Int := {body}"))
                .expect("checked builtin instance field translates"),
            expected
        );
    }
}

#[test]
fn test_source_int_negative_constructor_zero_and_large_numerals() {
    for (body, expected) in [
        (
            "Int.ediv (Int.negSucc 6) (Int.ofNat 2)",
            "(ite (= 2 0) 0 (div (- (+ 6 1)) 2))",
        ),
        (
            "Int.ediv (Int.negSucc 0) (Int.ofNat 0)",
            "(ite (= 0 0) 0 (div (- (+ 0 1)) 0))",
        ),
        (
            "(18446744073709551616 : Int) / (2 : Int)",
            "(ite (= 2 0) 0 (div 18446744073709551616 2))",
        ),
    ] {
        assert_eq!(
            prepared_translation(&format!("def smtInput : Int := {body}"))
                .expect("exact constructor numeral translates"),
            expected
        );
    }
}

#[test]
fn test_source_custom_numeral_dictionary_uses_its_actual_value() {
    assert_eq!(
        prepared_translation(
            "def smtInput : Int := @OfNat.ofNat Int 7 (@OfNat.mk Int 7 (Int.ofNat 42))"
        )
        .expect("checked concrete dictionary value translates"),
        "42"
    );
}

#[test]
fn test_source_custom_int_division_and_symbolic_numeral_dictionaries_stay_refused() {
    for source in [
        "def smtInput (a b : Int) : Int := \
         @HDiv.hDiv Int Int Int (@HDiv.mk Int Int Int (fun x y => x)) a b",
        "def smtInput (a b : Int) : Int := @OfNat.ofNat Int 7 (@OfNat.mk Int 7 a)",
        "def smtInput (a b : Int) : Int := @HDiv.hDiv Int Int Int (@HDiv.mk Int Int Int Int.div) a b",
    ] {
        assert!(matches!(
            prepared_translation(source),
            Err(TranslateError::UnsupportedExpr(_))
        ));
    }
}

#[test]
fn test_smt_natural_literals_and_integer_constructors_use_exact_decimal_encoding() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let natural = Expr::nat_lit_u128(1u128 << 64);
    assert_eq!(
        tc.infer_type_full(&natural)
            .expect("kernel checks big natural literal"),
        Expr::const_(Name::from_string("Nat"), vec![])
    );
    assert_eq!(
        SmtLibTranslator::new()
            .translate_expr(&natural)
            .expect("decimal natural literal"),
        "18446744073709551616"
    );
    let negative = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        natural,
    );
    assert_eq!(
        tc.infer_type_full(&negative)
            .expect("kernel checks big negative constructor"),
        Expr::const_(Name::from_string("Int"), vec![])
    );
    assert_eq!(
        SmtLibTranslator::new()
            .translate_expr(&negative)
            .expect("decimal negative constructor"),
        "(- (+ 18446744073709551616 1))"
    );
}

#[test]
fn test_source_quoted_integer_head_lookalikes_stay_refused() {
    for source in [
        "def «Int.ofNat» (n : Nat) : Int := Int.ofNat 0\n\
         def smtInput : Int := «Int.ofNat» 7",
        "def «Int.negSucc» (n : Nat) : Int := Int.ofNat 0\n\
         def smtInput : Int := «Int.negSucc» 7",
        "def «Int.ediv» (a b : Int) : Int := a\n\
         def smtInput (a b : Int) : Int := @HDiv.hDiv Int Int Int (@HDiv.mk Int Int Int «Int.ediv») a b",
    ] {
        assert!(matches!(prepared_translation(source), Err(TranslateError::UnsupportedExpr(_))), "{source}");
    }
}

#[test]
fn test_integer_input_preparation_rejects_ill_typed_conversion() {
    let state = source_state("def smtInput (a b : Int) : Int := a / b");
    let goal = state.current_goal().expect("goal");
    // This dictionary reduces to Int.ediv, but the supplied Nat operands do
    // not inhabit its Int domain. Successful projection reduction is not a
    // substitute for strict inference of the original term.
    let mut args: Vec<_> = goal.target.get_app_args().into_iter().cloned().collect();
    assert_eq!(args.len(), 6);
    args[4] = Expr::nat_lit(7);
    args[5] = Expr::nat_lit(3);
    let malformed = Expr::apps(goal.target.get_app_fn().clone(), args);
    assert!(matches!(
        prepare_smt_integer_expr(&state, goal, &malformed),
        Err(TranslateError::UnsupportedExpr(_))
    ));
}
