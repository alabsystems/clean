// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::{sources, ROOTS};
use crate::eval_ir::{
    build_nat_bool_reflection_prelude_spec_v1_with_stack, build_prelude_spec_with_stack,
    NAT_BOOL_REFLECTION_PRELUDE_PROFILE_V1,
};
use crate::spec::Specification;
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};
use std::sync::OnceLock;

const EXPECTED: [&str; 7] = [
    "ir_bool_false_ne_true",
    "ir_nat_eqb_walk_refl",
    "ir_nat_eqb_refl",
    "ir_nat_eqb_sound_walk",
    "ir_nat_eqb_sound",
    "ir_bm_and_fst",
    "ir_bm_and_snd",
];

fn with_package(test: impl FnOnce(&Specification) + Send + 'static) {
    static PACKAGE: OnceLock<Specification> = OnceLock::new();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let spec = PACKAGE.get_or_init(|| {
                build_nat_bool_reflection_prelude_spec_v1_with_stack()
                    .expect("fixed public production-Prelude Nat/Bool package")
            });
            test(spec);
        })
        .unwrap()
        .join()
        .unwrap();
}

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}

fn eq(ty: &str, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_str(ty), left, right],
    )
}

fn refl(ty: &str, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str(ty), value],
    )
}

fn pi(ty: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, ty, body)
}

fn truth() -> Expr {
    Expr::const_str("Bool.true")
}

fn independent_goal(root: &str) -> Expr {
    match root {
        "ir_nat_eqb_sound" => pi(
            Expr::const_str("Nat"),
            pi(
                Expr::const_str("Nat"),
                pi(
                    eq(
                        "Bool",
                        app("ir_nat_eqb", [Expr::bvar(1), Expr::bvar(0)]),
                        truth(),
                    ),
                    eq("Nat", Expr::bvar(2), Expr::bvar(1)),
                ),
            ),
        ),
        "ir_nat_eqb_refl" => pi(
            Expr::const_str("Nat"),
            eq(
                "Bool",
                app("ir_nat_eqb", [Expr::bvar(0), Expr::bvar(0)]),
                truth(),
            ),
        ),
        "ir_bm_and_fst" | "ir_bm_and_snd" => pi(
            Expr::const_str("Bool"),
            pi(
                Expr::const_str("Bool"),
                pi(
                    eq(
                        "Bool",
                        app("Bool.and", [Expr::bvar(1), Expr::bvar(0)]),
                        truth(),
                    ),
                    eq(
                        "Bool",
                        Expr::bvar(if root == "ir_bm_and_fst" { 2 } else { 1 }),
                        truth(),
                    ),
                ),
            ),
        ),
        "ir_bool_false_ne_true" => pi(
            Expr::sort(Level::zero()),
            pi(
                eq("Bool", Expr::const_str("Bool.false"), truth()),
                Expr::bvar(1),
            ),
        ),
        other => panic!("unexpected independent endpoint {other}"),
    }
}

fn accepted(env: &Environment, label: &str, goal: &Expr, proof: &Expr) {
    let audit = env.audit_certification(goal, proof);
    assert!(audit.is_certified(), "{label}: {audit:#?}");
    println!("NAT_BOOL_REFLECTION_ACCEPT label={label} profile={NAT_BOOL_REFLECTION_PRELUDE_PROFILE_V1} dependencies={}", audit.dependencies.len());
}

fn rejected(env: &Environment, label: &str, goal: &Expr, proof: &Expr) {
    let audit = env.audit_certification(goal, proof);
    assert!(!audit.is_certified(), "{label}: false endpoint certified");
    let issues = format!("{:?}", audit.issues);
    assert!(
        issues.contains("TypeMismatch"),
        "{label}: semantic refusal required: {issues}"
    );
    assert!(
        !issues.contains("Heartbeat") && !issues.contains("BudgetExhausted"),
        "{label}: resource unknown is not semantic refusal: {issues}"
    );
    println!("NAT_BOOL_REFLECTION_REFUSAL label={label} issues={issues}");
}

#[test]
fn production_factory_has_exact_shared_sources_and_preserves_default_prelude() {
    with_package(|spec| {
        assert_eq!(
            sources().map(|(name, _)| name).collect::<Vec<_>>(),
            EXPECTED
        );
        let base = build_prelude_spec_with_stack().expect("unchanged public production Prelude");
        assert_eq!(
            spec.definitions().len(),
            base.definitions().len() + EXPECTED.len()
        );
        for name in base.definitions().keys() {
            let key = Name::from_string(name);
            assert_eq!(
                base.env().get_const(&key),
                spec.env().get_const(&key),
                "inherited {name}"
            );
            assert_eq!(
                base.env().closure_digest(&key).unwrap(),
                spec.env().closure_digest(&key).unwrap(),
                "inherited closure {name}"
            );
        }
        for name in EXPECTED {
            assert!(
                base.get_definition(name).is_none(),
                "default Prelude remains opt-in: {name}"
            );
            assert!(base.env().get_const(&Name::from_string(name)).is_none());
            let info = spec.env().get_const(&Name::from_string(name)).unwrap();
            assert!(info.value.is_some());
            println!(
                "NAT_BOOL_REFLECTION_IDENTITY root={name} digest={:?}",
                spec.env().closure_digest(&info.name).unwrap()
            );
        }
        assert!(spec
            .env()
            .get_const(&Name::from_string("ir_lzm_module"))
            .is_none());
        assert_eq!(
            spec.env().get_option("maxHeartbeats").unwrap().as_deref(),
            Some("2000000")
        );
        assert_eq!(
            spec.env()
                .get_option("tcMaxCacheEntries")
                .unwrap()
                .as_deref(),
            Some("100000")
        );
    });
}

#[test]
fn independent_universal_nat_and_bool_goals_have_empty_axiom_and_trust_closures() {
    with_package(|spec| {
        for root in ROOTS {
            let key = Name::from_string(root);
            let info = spec.env().get_const(&key).unwrap();
            let goal = independent_goal(root);
            assert_eq!(
                info.type_, goal,
                "independently constructed endpoint {root}"
            );
            accepted(spec.env(), root, &goal, &Expr::const_str(root));
            assert!(spec.env().axiom_deps(&key).unwrap().is_empty());
            assert!(spec.env().foundational_axiom_deps(&key).unwrap().is_empty());
            assert!(spec.env().trust_marker_deps(&key).unwrap().is_empty());
        }
        // The actual reflection root cannot prove all naturals equal without its premise.
        let false_goal = pi(
            Expr::const_str("Nat"),
            pi(
                Expr::const_str("Nat"),
                eq("Nat", Expr::bvar(1), Expr::bvar(0)),
            ),
        );
        rejected(
            spec.env(),
            "soundness-premise-removed",
            &false_goal,
            &Expr::const_str("ir_nat_eqb_sound"),
        );
        // Even self-comparison at an arbitrary neutral Nat is not Eq.refl computation.
        let symbolic = pi(
            Expr::const_str("Nat"),
            eq(
                "Bool",
                app("ir_nat_eqb", [Expr::bvar(0), Expr::bvar(0)]),
                truth(),
            ),
        );
        let false_proof = Expr::lam(
            BinderInfo::Default,
            Expr::const_str("Nat"),
            refl("Bool", truth()),
        );
        rejected(
            spec.env(),
            "symbolic-reflexivity-needs-theorem",
            &symbolic,
            &false_proof,
        );
    });
}

#[test]
fn actual_nat_comparison_handles_unbounded_values_and_refuses_false_premises() {
    with_package(|spec| {
        let large = app("Nat.succ", [Expr::nat_lit(u64::MAX)]);
        for n in [
            Expr::nat_lit(0),
            Expr::nat_lit(17),
            Expr::nat_lit(u64::MAX),
            large.clone(),
        ] {
            let self_goal = eq("Bool", app("ir_nat_eqb", [n.clone(), n.clone()]), truth());
            accepted(
                spec.env(),
                "actual-self-comparison",
                &self_goal,
                &refl("Bool", truth()),
            );
            let proof = app(
                "ir_nat_eqb_sound",
                [n.clone(), n.clone(), app("ir_nat_eqb_refl", [n.clone()])],
            );
            accepted(
                spec.env(),
                "soundness-on-actual-self",
                &eq("Nat", n.clone(), n),
                &proof,
            );
        }
        for (a, b) in [
            (Expr::nat_lit(0), Expr::nat_lit(1)),
            (Expr::nat_lit(17), Expr::nat_lit(18)),
            (Expr::nat_lit(u64::MAX), large),
        ] {
            let premise = eq("Bool", app("ir_nat_eqb", [a.clone(), b.clone()]), truth());
            rejected(
                spec.env(),
                "forged-true-comparison",
                &premise,
                &refl("Bool", truth()),
            );
            let proof = app(
                "ir_nat_eqb_sound",
                [a.clone(), b.clone(), refl("Bool", truth())],
            );
            rejected(
                spec.env(),
                "soundness-requires-actual-true-premise",
                &eq("Nat", a, b),
                &proof,
            );
        }
    });
}

#[test]
fn actual_boolean_eliminators_refuse_each_false_conjunction_and_absurdity_forgery() {
    with_package(|spec| {
        for x in ["Bool.false", "Bool.true"] {
            for y in ["Bool.false", "Bool.true"] {
                for (root, endpoint) in [("ir_bm_and_fst", x), ("ir_bm_and_snd", y)] {
                    let proof = app(
                        root,
                        [
                            Expr::const_str(x),
                            Expr::const_str(y),
                            refl("Bool", truth()),
                        ],
                    );
                    let goal = eq("Bool", Expr::const_str(endpoint), truth());
                    if x == "Bool.true" && y == "Bool.true" {
                        accepted(spec.env(), root, &goal, &proof);
                    } else {
                        rejected(spec.env(), "false-conjunction-premise", &goal, &proof);
                    }
                }
            }
        }
        let false_goal = eq("Nat", Expr::nat_lit(0), Expr::nat_lit(1));
        let forged = app(
            "ir_bool_false_ne_true",
            [false_goal.clone(), refl("Bool", truth())],
        );
        rejected(
            spec.env(),
            "absurdity-requires-contradiction",
            &false_goal,
            &forged,
        );
    });
}

#[test]
fn package_collision_and_replay_budget_exhaustion_fail_closed() {
    with_package(|spec| {
        let error = spec
            .clone()
            .into_nat_bool_reflection_prelude_v1()
            .expect_err("fixed names cannot be installed twice");
        assert!(
            matches!(error, crate::spec::SpecError::EnvError(ref message) if message.contains("name collision") && message.contains("ir_bool_false_ne_true")),
            "{error}"
        );
        let mut bounded = spec.env().clone();
        bounded.set_option("maxHeartbeats".into(), Some("1".into()));
        let root = "ir_nat_eqb_sound";
        let audit = bounded.audit_certification(&independent_goal(root), &Expr::const_str(root));
        assert!(!audit.is_certified());
        let issues = format!("{:?}", audit.issues);
        assert!(
            issues.contains("Heartbeat") || issues.contains("BudgetExhausted"),
            "bounded replay stays resource unknown: {issues}"
        );
        println!("NAT_BOOL_REFLECTION_RESOURCE_UNKNOWN issues={issues}");
        accepted(
            spec.env(),
            "original-owner-retained",
            &independent_goal(root),
            &Expr::const_str(root),
        );
    });
}
