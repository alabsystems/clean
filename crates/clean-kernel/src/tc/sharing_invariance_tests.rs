// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual type-checking controls for the universal owner. Uniform modes are
//! deliberately tested only as counterexamples to that insufficient strategy.
use super::*;
use crate::{env::Declaration, expr::BinderInfo};
use std::{cell::Cell, sync::Arc};

fn n(s: &str) -> Name {
    Name::from_string(s)
}
fn params() -> Vec<Name> {
    vec![n("u"), n("v")]
}
fn levels() -> Vec<Level> {
    params().into_iter().map(Level::param).collect()
}
fn raw() -> Level {
    Level::lean_imax_core(Level::param(n("v")), Level::succ(Level::param(n("u"))))
}
fn fixture() -> Environment {
    let mut env = Environment::for_lean_replay();
    for (name, type_) in [
        ("cS", Expr::sort(raw())),
        (
            "F",
            Expr::arrow(Expr::sort(raw()), Expr::sort(Level::zero())),
        ),
    ] {
        env.add_decl(Declaration::Axiom {
            name: n(name),
            level_params: params(),
            type_,
        })
        .expect("honest Lean declaration");
    }
    env
}
fn identity() -> (Expr, Expr) {
    let ty = Expr::const_(n("cS"), levels());
    (
        Expr::lam(BinderInfo::Default, ty.clone(), Expr::bvar(0)),
        Expr::arrow(ty.clone(), ty),
    )
}
fn original<'a>(env: &'a Environment, value: &Expr, expected: &Expr) -> TypeChecker<'a> {
    let mut tc = TypeChecker::new(env);
    tc.set_kernel_theory(KernelTheory::Lean);
    assert!(tc.check_type(value, expected).is_err());
    assert!(
        tc.level_sharing_error().is_some(),
        "control must encounter original refusal"
    );
    tc
}

#[test]
fn invariant_value_passes_every_dynamic_path_and_original_stays_refused() {
    let env = fixture();
    let (value, expected) = identity();
    let tc = original(&env, &value, &expected);
    let summary = tc
        .recheck_type_sharing_invariant(&value, &expected)
        .expect("every possible identity body checks");
    assert!(summary.completed_paths > 1);
    assert!(
        tc.level_sharing_error().is_some(),
        "success cannot rehabilitate original sticky state"
    );
    assert!(tc.check_type(&value, &expected).is_err());
}

fn uniform(env: &Environment, value: &Expr, expected: &Expr, rebuild: bool) {
    let mut prefix = Vec::new();
    for _ in 0..32 {
        let tc = TypeChecker::for_sharing_prefix(env, KernelTheory::Lean, prefix.clone(), 100_000);
        let outcome = tc.check_type(value, expected);
        let state = tc.sharing_replay.as_ref().unwrap().borrow();
        if let Some(encounter) = state.pending.clone() {
            prefix.push(Decision { encounter, rebuild });
            continue;
        }
        assert!(state.complete());
        outcome.expect("uniform interpretation is favorable");
        return;
    }
    panic!("uniform control did not complete");
}
#[test]
fn two_uniform_successes_do_not_hide_mixed_execution_failure() {
    let env = fixture();
    let value = Expr::app(
        Expr::const_(n("F"), levels()),
        Expr::const_(n("cS"), levels()),
    );
    let expected = Expr::sort(Level::zero());
    uniform(&env, &value, &expected, false);
    uniform(&env, &value, &expected, true);
    let tc = original(&env, &value, &expected);
    assert!(matches!(
        tc.recheck_type_sharing_invariant(&value, &expected),
        Err(SharingInvariantFailure::NotEstablished(_))
    ));
}
#[test]
fn budgets_refuse_before_any_universal_success() {
    let env = fixture();
    let (value, expected) = identity();
    let mut tc = original(&env, &value, &expected);
    assert!(matches!(
        tc.recheck_type_sharing_with_limits(&value, &expected, 0, 32),
        Err(SharingInvariantFailure::Exhausted("state"))
    ));
    assert!(matches!(
        tc.recheck_type_sharing_with_limits(&value, &expected, 256, 0),
        Err(SharingInvariantFailure::Exhausted("decision/trace"))
    ));
    tc.set_heartbeat_limit(1);
    assert!(matches!(
        tc.recheck_type_sharing_invariant(&value, &expected),
        Err(SharingInvariantFailure::Exhausted(_))
    ));
}
#[test]
fn extended_or_nonhazard_context_never_gets_implicit_replay_admission() {
    let env = fixture();
    let (value, expected) = identity();
    let tc = TypeChecker::new(&env);
    assert!(matches!(
        tc.recheck_type_sharing_invariant(&value, &expected),
        Err(SharingInvariantFailure::UnsupportedContext)
    ));
    let mut tc = original(&env, &value, &expected);
    tc.set_kernel_theory(KernelTheory::Extended);
    assert!(matches!(
        tc.recheck_type_sharing_invariant(&value, &expected),
        Err(SharingInvariantFailure::UnsupportedContext)
    ));
}

struct CountingChoices {
    calls: Cell<usize>,
}
impl SharingChoices for CountingChoices {
    fn choose_rebuild(&self, _: &Level) -> Option<bool> {
        let i = self.calls.get();
        self.calls.set(i + 1);
        Some(i != 0)
    }
}
#[test]
fn shared_expression_fold_visits_both_encounters_independently() {
    let shared = Arc::new(Expr::sort(raw()));
    let expression = Expr::app_arc(shared.clone(), shared);
    let choices = CountingChoices {
        calls: Cell::new(0),
    };
    let ps = params();
    let ls = levels();
    let out = expression.lean_instantiate_level_params_with_choices(
        &crate::level::SliceLookup {
            params: &ps,
            levels: &ls,
        },
        Some(&choices),
    );
    assert!(!out.sharing_dependent);
    assert_eq!(
        choices.calls.get(),
        2,
        "FoldMemo must not collapse independent unknown source encounters"
    );
    assert_ne!(
        out.expr, expression,
        "second encounter selected rebuilt level, first kept raw"
    );
}
#[test]
fn transcript_refuses_same_level_at_another_constant() {
    let name = n("first");
    let expression = Expr::sort(raw());
    let ps = params();
    let ls = levels();
    let state = RefCell::new(SharingReplay::new(Vec::new()));
    let owner = SharingInstantiation {
        replay: &state,
        constant: &name,
        expression: &expression,
        parameters: &ps,
        replacements: &ls,
    };
    assert_eq!(owner.choose_rebuild(&raw()), None);
    assert!(!state.borrow().complete());
    let encounter = state.borrow().pending.clone().unwrap();
    let state = RefCell::new(SharingReplay::new(vec![Decision {
        encounter,
        rebuild: false,
    }]));
    let other = n("second");
    let owner = SharingInstantiation {
        replay: &state,
        constant: &other,
        expression: &expression,
        parameters: &ps,
        replacements: &ls,
    };
    assert_eq!(owner.choose_rebuild(&raw()), None);
    assert!(state.borrow().diverged);
    assert!(!state.borrow().complete());
}

fn arc_inference_revisits(certificates: bool) {
    let env = fixture();
    let expression = Expr::sort(raw());
    let ps = params();
    let ls = levels();
    let encounter = Encounter {
        constant: n("cS"),
        expression,
        parameters: ps.into(),
        replacements: ls.into(),
        original: raw(),
    };
    let prefix = [false, true]
        .into_iter()
        .map(|rebuild| Decision {
            encounter: encounter.clone(),
            rebuild,
        })
        .collect();
    let mut tc = TypeChecker::for_sharing_prefix(&env, KernelTheory::Lean, prefix, 100_000);
    // An active App-child frame and nonzero memo capacity exercise the actual
    // shortcut. Universal mode must bypass it independently of capacity zero.
    tc.infer_memo_depth.set(1);
    tc.max_cache_entries = 64;
    let shared = Arc::new(Expr::const_(n("cS"), levels()));
    let infer = || {
        if certificates {
            tc.infer_type_with_cert_arc(&shared).map(|(ty, _)| ty)
        } else {
            #[cfg(not(debug_assertions))]
            {
                tc.infer_type_fast_arc(&shared)
            }
            #[cfg(debug_assertions)]
            {
                panic!("fast-Arc control requires its actual non-debug build path")
            }
        }
    };
    let first = infer().expect("raw path");
    let second = infer().expect("rebuilt path");
    assert_ne!(
        first, second,
        "shared Arc cannot answer a later independent encounter"
    );
    assert!(tc.sharing_replay.as_ref().unwrap().borrow().complete());
}
#[test]
#[cfg(not(debug_assertions))]
fn fast_arc_inference_does_not_reuse_an_earlier_choice() {
    arc_inference_revisits(false);
}
#[test]
fn certificate_arc_inference_does_not_reuse_an_earlier_choice() {
    arc_inference_revisits(true);
}

#[test]
fn source_level_profiles_match_actual_native_version_difference() {
    use crate::level::LeanLevelProfile;
    let u = Level::param(n("u"));
    let raw_one = Level::lean_imax_core(Level::succ(Level::zero()), u.clone());
    for (profile, expected) in [
        (LeanLevelProfile::Lean48, false),
        (LeanLevelProfile::Lean430, true),
    ] {
        let mut env = fixture();
        env.set_lean_level_profile(profile);
        let mut tc = TypeChecker::new(&env);
        tc.set_kernel_theory(KernelTheory::Lean);
        assert_eq!(
            tc.is_def_eq(&Expr::sort(raw_one.clone()), &Expr::sort(u.clone())),
            expected
        );
        let built = tc.level_imax(Level::succ(Level::zero()), u.clone());
        assert_eq!(built, if expected { u.clone() } else { raw_one.clone() });
    }
}

#[test]
fn version_profile_survives_json_binary_and_changes_content_identity() {
    use crate::level::LeanLevelProfile;
    let mut env = fixture();
    let modern = env.content_digest();
    env.set_lean_level_profile(LeanLevelProfile::Lean48);
    assert_ne!(
        modern,
        env.content_digest(),
        "a receipt cannot be rebound to another profile"
    );
    let json = env.to_json().unwrap();
    let restored = Environment::from_json(&json).unwrap();
    assert_eq!(restored.lean_level_profile(), LeanLevelProfile::Lean48);
    let bytes = env.to_bincode().unwrap();
    let restored = Environment::from_bincode(&bytes).unwrap();
    assert_eq!(restored.lean_level_profile(), LeanLevelProfile::Lean48);
}

#[test]
fn memoized_modern_level_answer_cannot_cross_into_legacy_checker() {
    use crate::level::LeanLevelProfile;
    let mut modern = fixture();
    modern.set_lean_level_profile(LeanLevelProfile::Lean430);
    let mut legacy = modern.clone();
    legacy.set_lean_level_profile(LeanLevelProfile::Lean48);
    let left = Expr::sort(Level::lean_imax_core(
        Level::succ(Level::zero()),
        Level::param(n("u")),
    ));
    let right = Expr::sort(Level::param(n("u")));
    let mut tc = TypeChecker::new(&modern);
    tc.set_kernel_theory(KernelTheory::Lean);
    assert!(tc.is_def_eq(&left, &right));
    let caches = tc.take_caches();
    let mut tc =
        TypeChecker::with_context_and_caches(&legacy, super::super::LocalContext::new(), caches);
    tc.set_kernel_theory(KernelTheory::Lean);
    assert!(
        !tc.is_def_eq(&left, &right),
        "the native4.8 negative answer cannot inherit4.30 cache success"
    );
}

#[test]
fn legacy_profile_keeps_genuine_sharing_ambiguity_refused() {
    let mut env = fixture();
    env.set_lean_level_profile(crate::level::LeanLevelProfile::Lean48);
    let value = Expr::app(
        Expr::const_(n("F"), levels()),
        Expr::const_(n("cS"), levels()),
    );
    let expected = Expr::sort(Level::zero());
    let tc = original(&env, &value, &expected);
    assert!(matches!(
        tc.recheck_type_sharing_invariant(&value, &expected),
        Err(SharingInvariantFailure::NotEstablished(_))
    ));
}

#[test]
fn legacy_profile_cannot_be_relabelled_as_reference_v1() {
    let mut env = fixture();
    env.set_lean_level_profile(crate::level::LeanLevelProfile::Lean48);
    assert!(matches!(
        crate::reference::ReferenceKernel::new(env),
        Err(crate::reference::ReferenceRefusal::NonLeanSetting {
            setting: "lean_level_profile"
        })
    ));
}

#[cfg(debug_assertions)]
#[test]
fn discarded_debug_private_sharing_replay_keeps_real_certificates() {
    // Use the universal owner's genuine private factory. The regression must
    // not widen that factory or fabricate a favorable replay/cache state.
    let env = Environment::new();
    let checker = TypeChecker::for_sharing_prefix(&env, KernelTheory::Lean, Vec::new(), 100_000);
    let shared = Arc::new(Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)));
    let expected = Expr::arrow(Expr::type_(), Expr::type_());
    let (ty, cert) = checker
        .infer_type_with_cert_arc(&shared)
        .expect("actual private sharing replay");
    assert_eq!(ty, expected);
    assert!(!checker.cert_retained.get());
    assert_eq!(checker.infer_memo_depth.get(), 0);
    assert_eq!(checker.ctx_len(), 0);
    assert!(checker.infer_arc_memo.borrow().is_empty());
    assert_eq!(
        crate::cert::CertVerifier::new(&env)
            .verify(&cert, &shared)
            .expect("private sharing replay must retain the real certificate"),
        expected
    );
}
