//! Local assumed-environment accounting, not dependency-closed import replay.
use clean_kernel::env::{
    ConstantInfo, ConstantKind, Environment, ProofValueElision, Reducibility, TrustedEnvExt,
};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_olean::verify_batch_full::{
    typecheck_constants_full, typecheck_constants_full_streaming,
};
use clean_olean::verify_parallel::typecheck_constants_full_parallel;
use std::collections::{BTreeMap, BTreeSet};

type Counts = (usize, usize, BTreeMap<String, String>);
fn modes(env: &Environment, names: &[&str]) -> Vec<(&'static str, Counts)> {
    let targets = names
        .iter()
        .map(|s| (*s).to_owned())
        .collect::<BTreeSet<_>>();
    let eager = typecheck_constants_full(env, &targets, 2_000_000);
    let mut cloned = env.clone();
    let (p, f, e, _) = typecheck_constants_full_streaming(
        &mut cloned,
        &targets,
        2_000_000,
        ProofValueElision::OpaqueOnly,
        Some(1),
    );
    let parallel = typecheck_constants_full_parallel(env, &targets, 2, 2_000_000);
    let rows = vec![
        ("eager", eager),
        ("streaming", (p, f, e)),
        ("parallel", parallel),
    ];
    eprintln!("LOCAL_COUNTS {rows:?}");
    rows
}
fn family() -> Environment {
    let mut env = Environment::default();
    let name = Name::anon().str("CountFlag");
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::sort(Level::succ(Level::zero())),
            constructors: vec![Constructor {
                name: name.clone().str("mk"),
                type_: Expr::const_(name, vec![]),
            }],
        }],
    })
    .unwrap();
    assert_eq!(env.constants().count(), 3);
    assert_eq!(
        env.inductives().count() + env.constructors().count() + env.recursors().count(),
        3
    );
    env
}
fn insert(env: &mut Environment, name: Name, levels: Vec<Name>, ty: Expr, value: Option<Expr>) {
    // SOUNDNESS: adversarial local-registry fixtures only. Structural insertion
    // is intentionally not admission; the environment never escapes this test.
    assert!(env
        .extend_constants_structural(std::iter::once(ConstantInfo::new_with_reducibility(
            name,
            levels,
            ty,
            value,
            Reducibility::Opaque,
            ConstantKind::Definition
        )))
        .is_empty());
}
const FAMILY: &[&str] = &["CountFlag", "CountFlag.mk", "CountFlag.rec"];

#[test]
fn local_accounting_one_verdict_for_each_checked_family_identity() {
    for (mode, (p, f, e)) in modes(&family(), FAMILY) {
        assert_eq!((p, f), (3, 0), "{mode}: {e:?}");
        assert!(e.is_empty());
    }
}
#[test]
fn local_accounting_duplicate_family_cannot_hide_bad_value() {
    let mut env = family();
    let ty = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::bvar(0),
    );
    let value = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    insert(&mut env, Name::anon().str("Bad"), vec![], ty, Some(value));
    for (mode, (p, f, e)) in modes(&env, &["CountFlag", "CountFlag.mk", "CountFlag.rec", "Bad"]) {
        assert_eq!((p, f), (3, 1), "{mode}: {e:?}");
        assert!(e.contains_key("Bad"));
    }
}
#[test]
fn local_accounting_conflicting_well_sorted_mirror_is_not_skipped() {
    let mut env = family();
    insert(
        &mut env,
        Name::anon().str("CountFlag"),
        vec![],
        Expr::sort(Level::zero()),
        None,
    );
    for (mode, (p, f, e)) in modes(&env, FAMILY) {
        assert_eq!((p, f), (2, 1), "{mode}: {e:?}");
        assert!(e["CountFlag"].contains("registry"));
    }
}
#[test]
fn local_accounting_every_projection_still_gets_its_type_check() {
    let mut env = family();
    insert(
        &mut env,
        Name::anon().str("CountFlag"),
        vec![],
        Expr::app(Expr::sort(Level::zero()), Expr::sort(Level::zero())),
        None,
    );
    for (mode, (_p, f, e)) in modes(&env, FAMILY) {
        assert!(f >= 1, "{mode}");
        assert!(e["CountFlag"].contains("registry"));
        assert!(e["CountFlag"].contains("infer_sort"));
    }
}
#[test]
fn local_accounting_mirror_level_telescope_must_agree() {
    let mut env = family();
    insert(
        &mut env,
        Name::anon().str("CountFlag"),
        vec![Name::anon().str("u")],
        Expr::sort(Level::succ(Level::zero())),
        None,
    );
    for (mode, (_p, f, e)) in modes(&env, FAMILY) {
        assert!(f >= 1, "{mode}");
        assert!(e["CountFlag"].contains("registry"));
    }
}
#[test]
fn local_accounting_family_mirror_cannot_add_a_value() {
    let mut env = family();
    insert(
        &mut env,
        Name::anon().str("CountFlag"),
        vec![],
        Expr::sort(Level::succ(Level::zero())),
        Some(Expr::sort(Level::zero())),
    );
    for (mode, (_p, f, e)) in modes(&env, FAMILY) {
        assert!(f >= 1, "{mode}");
        assert!(e["CountFlag"].contains("registry"));
    }
}
fn collision(names: [Name; 2], target: &str) {
    let mut env = Environment::default();
    for name in names {
        insert(&mut env, name, vec![], Expr::sort(Level::zero()), None);
    }
    assert_eq!(env.constants().count(), 2);
    for (mode, (p, f, e)) in modes(&env, &[target]) {
        assert_eq!((p, f), (0, 2), "{mode}: {e:?}");
        assert!(e[target].contains("ambiguous"));
    }
}
#[test]
fn local_accounting_quoted_display_alias_is_explicitly_ambiguous() {
    collision(
        [Name::anon().str("A.B"), Name::anon().str("A").str("B")],
        "A.B",
    );
}
#[test]
fn local_accounting_numeric_and_string_segments_are_distinct() {
    collision(
        [Name::anon().str("A").num(1), Name::anon().str("A").str("1")],
        "A.1",
    );
}
#[test]
fn local_accounting_missing_target_survives_beside_present_target() {
    let mut env = Environment::default();
    insert(
        &mut env,
        Name::anon().str("Present"),
        vec![],
        Expr::sort(Level::succ(Level::zero())),
        Some(Expr::sort(Level::zero())),
    );
    for (mode, (p, f, e)) in modes(&env, &["Present", "Missing"]) {
        assert_eq!((p, f), (1, 1), "{mode}: {e:?}");
        assert!(e["Missing"].contains("missing"));
        assert!(!e.contains_key("Present"));
    }
}

#[test]
fn local_accounting_missing_body_is_not_a_success_beside_missing_target() {
    let mut env = Environment::default();
    insert(
        &mut env,
        Name::anon().str("Present"),
        vec![],
        Expr::sort(Level::zero()),
        None,
    );
    for (mode, (p, f, e)) in modes(&env, &["Present", "Missing"]) {
        assert_eq!((p, f), (0, 2), "{mode}: {e:?}");
        assert!(e["Present"].contains("no stored value"), "{mode}: {e:?}");
        assert!(e["Missing"].contains("missing"), "{mode}: {e:?}");
    }
}
#[test]
fn local_accounting_empty_request_has_no_successes_or_failures() {
    for (mode, (p, f, e)) in modes(&family(), &[]) {
        assert_eq!((p, f), (0, 0), "{mode}: {e:?}");
        assert!(e.is_empty());
    }
}

#[test]
fn local_accounting_ambiguous_targets_keep_both_bad_value_checks() {
    let mut env = Environment::default();
    let ty = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::bvar(0),
    );
    let value = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    for name in [Name::anon().str("A.B"), Name::anon().str("A").str("B")] {
        insert(&mut env, name, vec![], ty.clone(), Some(value.clone()));
    }
    for (mode, (pass, fail, errors)) in modes(&env, &["A.B"]) {
        assert_eq!((pass, fail), (0, 2), "{mode}: {errors:?}");
        assert_eq!(
            errors["A.B"].matches("check_type:").count(),
            2,
            "{mode}: {errors:?}"
        );
        assert!(errors["A.B"].contains("Str(\"A.B\")"));
        assert!(errors["A.B"].contains("Str(\"A\")/Str(\"B\")"));
    }
}

fn generated_auxiliaries() -> Environment {
    let mut env = Environment::default();
    let name = Name::anon().str("AuxFlag");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::sort(Level::succ(Level::zero())),
            constructors: vec![Constructor {
                name: name.clone().str("mk"),
                type_: Expr::const_(name, vec![]),
            }],
        }],
    })
    .unwrap();
    for suffix in ["casesOn", "recOn"] {
        let name = Name::anon().str("AuxFlag").str(suffix);
        let constant = env
            .get_const(&name)
            .expect("actual generated auxiliary constant");
        assert!(
            constant.value.is_some(),
            "real definitional wrapper required"
        );
        assert!(
            env.get_recursor(&name).is_some(),
            "actual mirrored rule-table entry required"
        );
    }
    env
}

#[test]
fn local_accounting_generated_value_bearing_recursors_are_counted_once() {
    let env = generated_auxiliaries();
    let names: BTreeSet<_> = env
        .constants()
        .map(|c| c.name.clone())
        .chain(env.inductives().map(|c| c.name.clone()))
        .chain(env.constructors().map(|c| c.name.clone()))
        .chain(env.recursors().map(|c| c.name.clone()))
        .collect();
    let labels: Vec<_> = names.iter().map(ToString::to_string).collect();
    let refs: Vec<_> = labels.iter().map(String::as_str).collect();
    assert!(names.len() >= 5);
    for (mode, (pass, fail, errors)) in modes(&env, &refs) {
        assert_eq!((pass, fail), (names.len(), 0), "{mode}: {errors:?}");
        assert!(errors.is_empty());
    }
}

#[test]
fn local_accounting_generated_recursors_still_check_the_actual_value() {
    let mut env = generated_auxiliaries();
    let name = Name::anon().str("AuxFlag").str("casesOn");
    let constant = env.get_const(&name).unwrap().clone();
    insert(
        &mut env,
        name,
        constant.level_params,
        constant.type_,
        Some(Expr::sort(Level::zero())),
    );
    for (mode, (pass, fail, errors)) in modes(&env, &["AuxFlag.casesOn"]) {
        assert_eq!((pass, fail), (0, 1), "{mode}: {errors:?}");
        assert!(errors["AuxFlag.casesOn"].contains("check_type:"));
    }
}
