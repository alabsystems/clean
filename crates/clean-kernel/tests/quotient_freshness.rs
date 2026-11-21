// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quotient installation must not overwrite genuinely checked declarations.

use clean_kernel::{
    env::KernelTheory, BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl,
    InductiveType, Level, Name, ReferenceKernel, ReferenceRefusal, TypeChecker,
};

const QUOTIENT_NAMES: [&str; 5] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound"];

fn name(text: &str) -> Name {
    Name::from_string(text)
}

fn constant(text: &str) -> Expr {
    Expr::const_(name(text), vec![])
}

fn empty_environment() -> Environment {
    let mut env = Environment::default();
    env.set_kernel_theory(KernelTheory::LeanReference);
    assert!(
        !env.quot_installed(),
        "the fixture must exercise fresh installation"
    );
    for text in QUOTIENT_NAMES {
        assert!(
            env.get_const(&name(text)).is_none(),
            "fixture already holds {text}"
        );
    }
    env
}

fn eq_family() -> InductiveDecl {
    let sort_u = Expr::sort(Level::param(name("u")));
    let pi = |domain, body| Expr::pi(BinderInfo::Default, domain, body);
    InductiveDecl {
        level_params: vec![name("u")],
        num_params: 2,
        types: vec![InductiveType {
            name: name("Eq"),
            type_: Expr::pi(
                BinderInfo::Implicit,
                sort_u.clone(),
                pi(Expr::bvar(0), pi(Expr::bvar(1), Expr::prop())),
            ),
            constructors: vec![Constructor {
                name: name("Eq.refl"),
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    sort_u,
                    pi(
                        Expr::bvar(0),
                        Expr::apps(
                            Expr::const_(name("Eq"), vec![Level::param(name("u"))]),
                            [Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)],
                        ),
                    ),
                ),
            }],
        }],
    }
}

fn definition(text: &str, value: Expr) -> Declaration {
    Declaration::Definition {
        name: name(text),
        level_params: vec![],
        type_: Expr::type_(),
        value,
        is_reducible: false,
    }
}

fn state(env: &Environment) -> serde_json::Value {
    let mut constants: Vec<_> = env
        .constants()
        .map(|info| {
            (
                info.name.to_string(),
                serde_json::to_value(info).expect("serialize actual constant"),
                env.declaration_verification(&info.name),
            )
        })
        .collect();
    constants.sort_by(|a, b| a.0.cmp(&b.0));
    let mut quotients: Vec<_> = env.quotients().cloned().collect();
    quotients.sort_by_key(|quotient| quotient.name.to_string());
    serde_json::json!({
        "generation": env.generation(),
        "constants": constants,
        "quotients": quotients,
        "installed": env.quot_installed(),
        "inductives": env.num_inductives(),
        "constructors": env.num_constructors(),
        "recursors": env.num_recursors(),
    })
}

fn occupied_name_is_refused(occupied: &str) {
    let mut env = empty_environment();
    env.add_inductive_core(eq_family())
        .expect("admit actual Eq");
    env.add_decl(definition(occupied, Expr::prop()))
        .expect("admit the original ordinary definition");
    env.add_decl(definition("retainedQuotientUser", constant(occupied)))
        .expect("admit a declaration depending on the original binding");
    TypeChecker::new(&env)
        .check_type(&constant(occupied), &Expr::type_())
        .expect("the original dependent value must actually type-check");
    let before = state(&env);
    let error = env
        .add_quot()
        .expect_err("installing quotient primitives must not overwrite an occupied name");
    assert!(error.contains(occupied), "wrong collision: {error}");
    assert_eq!(state(&env), before, "refusal must not install a prefix");
    TypeChecker::new(&env)
        .check_type(&constant(occupied), &Expr::type_())
        .expect("the old dependent value remains well typed after refusal");
    env.add_decl(definition("freshAfterQuotientRefusal", Expr::prop()))
        .expect("an unrelated checked extension still works");
}

macro_rules! collision {
    ($test:ident, $occupied:literal) => {
        #[test]
        fn $test() {
            occupied_name_is_refused($occupied);
        }
    };
}

collision!(occupied_quot_is_refused_without_mutation, "Quot");
collision!(occupied_quot_mk_is_refused_without_mutation, "Quot.mk");
collision!(occupied_quot_lift_is_refused_without_mutation, "Quot.lift");
collision!(occupied_quot_ind_is_refused_without_mutation, "Quot.ind");
collision!(
    occupied_quot_sound_is_refused_without_mutation,
    "Quot.sound"
);

#[test]
fn fresh_quotient_installation_remains_idempotent() {
    let mut env = empty_environment();
    env.add_inductive_core(eq_family())
        .expect("admit actual Eq");
    env.add_quot().expect("all five primitive names are fresh");
    assert!(env.quot_installed());
    for text in QUOTIENT_NAMES {
        assert!(env.get_const(&name(text)).is_some(), "missing {text}");
        assert!(env.get_quot(&name(text)).is_some(), "missing {text}");
    }
    let installed = state(&env);
    env.add_quot()
        .expect("the installed quotient stays idempotent");
    assert_eq!(state(&env), installed);
}

#[test]
fn reference_entry_preserves_its_admitted_names_on_quotient_collision() {
    for occupied in QUOTIENT_NAMES {
        let mut entry = ReferenceKernel::new(empty_environment())
            .expect("start from an actually quotient-free checked base");
        entry
            .add_inductive_checked(eq_family())
            .expect("Eq must be admitted through this entry");
        entry
            .add_checked(definition(occupied, Expr::prop()))
            .expect("admit the ordinary definition through the same entry");
        entry
            .add_checked(definition("retainedQuotientUser", constant(occupied)))
            .expect("admit its actual dependent declaration");
        let before = state(entry.environment());
        let before_digest = entry.env_digest();
        let error = entry
            .add_quot_checked()
            .expect_err("the fenced caller must inherit quotient name freshness");
        assert!(
            matches!(error, ReferenceRefusal::Admission(ref reason) if reason.contains(occupied)),
            "expected the occupied primitive name, got {error:?}"
        );
        assert_eq!(state(entry.environment()), before);
        assert_eq!(
            entry.env_digest(),
            before_digest,
            "refusal must not extend the entry chain"
        );
        entry
            .check_closed_term(&Expr::type_(), &constant(occupied))
            .expect("the entry still checks the original admitted binding");
        entry
            .add_checked(definition("freshAfterQuotientRefusal", Expr::prop()))
            .expect("the entry still admits an unrelated valid definition");
    }
}
