// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The environment's native-fold verdict cache is keyed by `(generation,
//! num_constants)` (`env/native_fold_authority.rs`). Each test warms the cache
//! for `Nat.add`, performs one environment write that changes what `Nat.add`
//! means while keeping the constant count, and requires the warm environment
//! to answer exactly what a cold clone (whose cache starts empty) answers.
//! A stale `Fold` verdict would let the kernel compute `Nat.add 2 3 = 5`
//! natively for a constant that no longer justifies it.
//!
//! The `forget_decl` tests cover a write that LOWERS the count: a later
//! provisional insert (`check_inductive_well_typed`, step 1) brings it back,
//! so the key returns to its warm value unless the removal moved the
//! generation.

use std::collections::HashMap;
use std::sync::Arc;

use clean_kernel::env::{
    ConstantInfo, ConstantKind, ConstantSource, EnvError, Environment, TrustedEnvExt,
};
use clean_kernel::{
    BinderInfo, Constructor, Expr, InductiveDecl, InductiveType, Level, Name, TypeChecker,
};

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn nat() -> Expr {
    Expr::const_(n("Nat"), vec![])
}

fn nat2() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(BinderInfo::Default, nat(), nat()),
    )
}

fn sum_2_3() -> Expr {
    Expr::apps(
        Expr::const_(n("Nat.add"), vec![]),
        [Expr::nat_lit(2), Expr::nat_lit(3)],
    )
}

fn warm_add(env: &Environment) {
    let add = n("Nat.add");
    assert!(
        env.native_fold_verdict(&add).is_ok(),
        "positive control: the canonical Nat.add folds"
    );
    assert!(
        TypeChecker::new(env).is_def_eq(&sum_2_3(), &Expr::nat_lit(5)),
        "positive control: Nat.add 2 3 = 5 by the canonical fold"
    );
}

fn assert_warm_matches_cold(env: &Environment) {
    let add = n("Nat.add");
    let cold = env.clone();
    let expected = cold.native_fold_verdict(&add);
    assert!(
        expected.is_err(),
        "cold verdict must refuse Nat.add: {expected:?}"
    );
    assert_eq!(
        env.native_fold_verdict(&add),
        expected,
        "warm verdict must follow the cold verdict after the write"
    );
    assert!(
        !TypeChecker::new(&cold).is_def_eq(&sum_2_3(), &Expr::nat_lit(5)),
        "cold control refuses Nat.add 2 3 = 5"
    );
    assert!(
        !TypeChecker::new(env).is_def_eq(&sum_2_3(), &Expr::nat_lit(5)),
        "ATTACK ACCEPTED: a stale fold verdict computed Nat.add 2 3 = 5"
    );
}

#[derive(Debug)]
struct MapSource(HashMap<Name, ConstantInfo>);

impl ConstantSource for MapSource {
    fn get(&self, name: &Name) -> Option<&ConstantInfo> {
        self.0.get(name)
    }

    fn contains(&self, name: &Name) -> bool {
        self.0.contains_key(name)
    }
}

/// `Nat.add := fun a _ => a`: δ computes `Nat.add 2 3 = 2`.
fn forged_add() -> ConstantInfo {
    ConstantInfo::new(
        n("Nat.add"),
        vec![],
        nat2(),
        Some(Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::lam(BinderInfo::Default, nat(), Expr::bvar(1)),
        )),
        false,
    )
}

/// `add_skolem_axiom` over an existing name replaces the constant in place:
/// the count is unchanged, and the write must still invalidate the verdict.
#[test]
fn skolem_axiom_over_a_folded_name_recomputes_the_verdict() {
    let mut env = Environment::with_prelude();
    warm_add(&env);
    let count = env.num_constants();
    TrustedEnvExt::add_skolem_axiom(&mut env, n("Nat.add"), nat2());
    assert_eq!(env.num_constants(), count, "replacement keeps the count");
    assert_eq!(
        env.get_const(&n("Nat.add")).map(|ci| ci.kind),
        Some(ConstantKind::Axiom)
    );
    assert_warm_matches_cold(&env);
}

/// Replacing the lazy constant source changes what a lazily served name
/// resolves to without touching the eager table or its count.
#[test]
fn replacing_the_lazy_source_recomputes_the_verdict() {
    let mut env = Environment::with_prelude();
    let add = n("Nat.add");
    let canonical = env.get_const(&add).cloned().expect("prelude Nat.add");
    assert!(env.forget_decl(&add));
    env.set_constant_source(Arc::new(MapSource(HashMap::from([(
        add.clone(),
        canonical,
    )]))));
    warm_add(&env);
    let count = env.num_constants();
    env.set_constant_source(Arc::new(MapSource(HashMap::from([(
        add.clone(),
        forged_add(),
    )]))));
    assert_eq!(env.num_constants(), count, "a source swap keeps the count");
    assert_warm_matches_cold(&env);
    // The δ answer of the forged definition, which the fold would contradict.
    assert!(TypeChecker::new(&env).is_def_eq(&sum_2_3(), &Expr::nat_lit(2)));
}

/// `add_skolem_axiom` over `Nat.add`, then straight to definitional equality
/// with no verdict query first: the consequence of a stale verdict, which the
/// test above reaches only after its verdict assertion.
#[test]
fn skolem_axiom_over_a_folded_name_refuses_the_fold_without_a_verdict_query() {
    let mut env = Environment::with_prelude();
    warm_add(&env);
    TrustedEnvExt::add_skolem_axiom(&mut env, n("Nat.add"), nat2());
    assert_eq!(
        env.get_const(&n("Nat.add")).map(|ci| ci.kind),
        Some(ConstantKind::Axiom)
    );
    let cold = env.clone();
    assert!(
        !TypeChecker::new(&cold).is_def_eq(&sum_2_3(), &Expr::nat_lit(5)),
        "cold control refuses Nat.add 2 3 = 5 for an axiom Nat.add"
    );
    assert!(
        !TypeChecker::new(&env).is_def_eq(&sum_2_3(), &Expr::nat_lit(5)),
        "FALSE ACCEPTANCE: the warm environment decided Nat.add 2 3 = 5 for an axiom Nat.add"
    );
}

fn one() -> Level {
    Level::succ(Level::zero())
}

fn eq_nat(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(n("Eq"), vec![one()]), [nat(), a, b])
}

/// `(fun (_ : 5 = 5) => body) (Eq.refl (Nat.add 2 3))`: well typed iff
/// `Nat.add 2 3 ≡ 5`, and β-reduces to `body` without that check.
fn guarded_by_sum(body: Expr) -> Expr {
    Expr::app(
        Expr::lam(
            BinderInfo::Default,
            eq_nat(Expr::nat_lit(5), Expr::nat_lit(5)),
            body,
        ),
        Expr::apps(Expr::const_(n("Eq.refl"), vec![one()]), [nat(), sum_2_3()]),
    )
}

/// `inductive T | mk : guarded_by_sum Nat → T`: the constructor's type is
/// well typed iff `Nat.add 2 3 ≡ 5`.
fn family_with_a_guarded_field(name: &str) -> InductiveDecl {
    let family = n(name);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: family.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: family.clone().str("mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    guarded_by_sum(nat()),
                    Expr::const_(family, vec![]),
                ),
            }],
        }],
    }
}

/// `inductive T : guarded_by_sum Type` with no constructors: the family's
/// type is well typed iff `Nat.add 2 3 ≡ 5`, and nothing built from the
/// family (its recursor and auxiliaries) contains the guard.
fn family_with_a_guarded_type(name: &str) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n(name),
            type_: guarded_by_sum(Expr::type_()),
            constructors: vec![],
        }],
    }
}

/// Where an admission was refused: the declaration whose type check failed,
/// or the refusal itself. Sites, not messages, so the comparison does not
/// depend on how a type error prints its terms.
fn refusal_site(error: &EnvError) -> String {
    match error {
        EnvError::TypeCheckFailed { name, .. } => format!("type check of {name}"),
        other => other.to_string(),
    }
}

/// The canonical `Nat.add` held eagerly, shadowing a lazily served forgery,
/// with the cache warmed by the canonical fold. `forget_decl(Nat.add)` then
/// exposes the forgery.
fn shadowed_forgery() -> Environment {
    let mut env = Environment::with_prelude();
    env.set_constant_source(Arc::new(MapSource(HashMap::from([(
        n("Nat.add"),
        forged_add(),
    )]))));
    warm_add(&env);
    env
}

/// `forget_decl` is a mutation, so it moves the generation; the verdict and
/// the definitional equality after it follow a cold clone's.
#[test]
fn forget_decl_moves_the_generation() {
    let mut env = shadowed_forgery();
    let generation = env.generation();
    assert!(env.forget_decl(&n("Nat.add")));
    assert!(
        env.generation() > generation,
        "forget_decl must move the generation: an insert that restores the count must not \
         meet a verdict cached before the removal"
    );
    assert_warm_matches_cold(&env);
}

/// The adversarial check's probe: forget `Nat.add` and one unrelated
/// constant, so the admission's provisional family and constructor bring the
/// count back to the warm count. The warm admission must refuse where the
/// cold clone does, at the constructor's type check; a refusal at a later
/// site means the provisional check passed on a stale verdict.
#[test]
fn forget_decl_then_a_provisional_constructor_refuses_where_a_cold_clone_does() {
    Environment::with_prelude()
        .add_inductive(family_with_a_guarded_field("AuditT"))
        .expect("positive control: the canonical Nat.add 2 3 = 5 admits the constructor");
    let mut env = shadowed_forgery();
    let count = env.num_constants();
    assert!(env.forget_decl(&n("Nat.add")));
    assert!(env.forget_decl(&n("Nat.mul")), "prelude Nat.mul");
    assert_eq!(env.num_constants(), count - 2);
    let cold = env
        .clone()
        .add_inductive(family_with_a_guarded_field("AuditT"))
        .expect_err("control: a cold clone refuses the constructor (forged Nat.add 2 3 = 2)");
    let warm = env
        .add_inductive(family_with_a_guarded_field("AuditT"))
        .expect_err("ATTACK ACCEPTED: the warm environment admitted the constructor");
    assert_eq!(
        refusal_site(&warm),
        refusal_site(&cold),
        "the warm admission must refuse where the cold one does"
    );
    assert_eq!(refusal_site(&cold), "type check of AuditT.mk");
    // The rolled-back admission leaves the verdict following a cold clone's.
    assert_warm_matches_cold(&env);
}

/// The same window with the guard in the family's own type, which only the
/// provisional check reads: a stale verdict there admits the family end to
/// end. Forgetting `Nat.add` alone suffices, as the provisional insert is
/// the family itself.
#[test]
fn forget_decl_then_a_provisional_family_refuses_where_a_cold_clone_does() {
    Environment::with_prelude()
        .add_inductive(family_with_a_guarded_type("AuditU"))
        .expect("positive control: the canonical Nat.add 2 3 = 5 admits the family");
    let mut env = shadowed_forgery();
    let count = env.num_constants();
    assert!(env.forget_decl(&n("Nat.add")));
    assert_eq!(env.num_constants(), count - 1);
    let cold = env
        .clone()
        .add_inductive(family_with_a_guarded_type("AuditU"))
        .expect_err("control: a cold clone refuses the family (forged Nat.add 2 3 = 2)");
    let warm = env
        .add_inductive(family_with_a_guarded_type("AuditU"))
        .expect_err("ATTACK ACCEPTED: the warm environment admitted an ill-typed family");
    assert_eq!(
        refusal_site(&warm),
        refusal_site(&cold),
        "the warm admission must refuse where the cold one does"
    );
    assert_eq!(refusal_site(&cold), "type check of AuditU");
    assert_warm_matches_cold(&env);
}
