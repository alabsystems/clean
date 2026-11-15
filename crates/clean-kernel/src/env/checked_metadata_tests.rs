use super::*;
use crate::{Declaration, DeclarationVerification};

fn fixture() -> (Environment, Name) {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let name = Name::from_string("Metadata.f");
    let nat = Expr::const_str("Nat");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            nat.clone(),
            Expr::arrow(nat.clone(), nat.clone()),
        ),
        value: Expr::lam(
            BinderInfo::Implicit,
            nat.clone(),
            Expr::lam(BinderInfo::Default, nat, Expr::bvar(0)),
        ),
        is_reducible: false,
    })
    .unwrap();
    (env, name)
}

fn infos() -> Vec<(Name, BinderInfo)> {
    vec![
        (Name::anon().str("a.b"), BinderInfo::Implicit),
        (Name::from_string("a.b"), BinderInfo::Default),
    ]
}

#[test]
fn checked_metadata_preserves_exact_names_type_value_and_provenance() {
    let (mut env, name) = fixture();
    let before = env.get_const(&name).unwrap().clone();
    let verification = env.declaration_verification(&name);
    env.add_checked_param_infos(&name, infos(), true).unwrap();
    let names = env.get_typed_param_names(&name).unwrap();
    assert_eq!(
        names,
        infos().iter().map(|(n, _)| n.clone()).collect::<Vec<_>>()
    );
    assert_ne!(names[0], names[1]);
    assert_eq!(names[0].to_string(), names[1].to_string());
    assert_eq!(env.get_const(&name), Some(&before));
    assert_eq!(env.declaration_verification(&name), verification);
}

#[test]
fn checked_metadata_refuses_absent_and_display_twin_owners() {
    let (mut env, name) = fixture();
    let twin = Name::anon().str("Metadata.f");
    assert_eq!(twin.to_string(), name.to_string());
    assert_ne!(twin, name);
    for key in [twin, Name::from_string("absent")] {
        assert!(env.add_checked_param_infos(&key, infos(), true).is_err());
        assert!(env.get_typed_param_names(&key).is_none());
    }
    assert!(env.get_typed_param_names(&name).is_none());
}

#[test]
fn checked_metadata_refuses_wrong_kind_and_arity_without_overwriting() {
    let (mut env, name) = fixture();
    env.add_checked_param_infos(&name, infos(), true).unwrap();
    let mut wrong_kind = infos();
    wrong_kind[0].1 = BinderInfo::Default;
    let mut too_many = infos();
    too_many.push((Name::from_string("extra"), BinderInfo::Default));
    for values in [wrong_kind, too_many, infos()[..1].to_vec()] {
        assert!(env.add_checked_param_infos(&name, values, true).is_err());
        assert_eq!(env.get_typed_param_names(&name).unwrap()[0], infos()[0].0);
        assert_eq!(
            env.get_param_binder_infos(&name).unwrap(),
            [BinderInfo::Implicit, BinderInfo::Default]
        );
    }
}

#[test]
fn checked_metadata_accepts_only_a_matching_declared_prefix() {
    let (mut env, name) = fixture();
    env.add_checked_param_infos(&name, infos()[..1].to_vec(), false)
        .unwrap();
    assert_eq!(env.get_typed_param_names(&name).unwrap().len(), 1);
    assert!(env
        .add_checked_param_infos(
            &name,
            vec![(Name::from_string("x"), BinderInfo::Default)],
            false
        )
        .is_err());
    assert_eq!(env.get_typed_param_names(&name).unwrap().len(), 1);
}

#[test]
fn checked_metadata_checks_signature_but_never_launders_a_value() {
    let (mut env, _) = fixture();
    let bad = Name::from_string("Metadata.badType");
    env.add_decl_unchecked(Declaration::Definition {
        name: bad.clone(),
        level_params: vec![],
        type_: Expr::nat_lit(0),
        value: Expr::nat_lit(0),
        is_reducible: false,
    });
    assert!(env.add_checked_param_infos(&bad, vec![], true).is_err());
    assert!(env.get_typed_param_names(&bad).is_none());
    let unchecked = Name::from_string("Metadata.uncheckedValue");
    env.add_decl_unchecked(Declaration::Definition {
        name: unchecked.clone(),
        level_params: vec![],
        type_: Expr::const_str("Nat"),
        value: Expr::const_str("Nat"),
        is_reducible: false,
    });
    let before = env.declaration_verification(&unchecked);
    assert_ne!(before, Some(DeclarationVerification::FullKernelCheck));
    env.add_checked_param_infos(&unchecked, vec![], true)
        .unwrap();
    assert_eq!(env.declaration_verification(&unchecked), before);
    assert_eq!(
        env.get_const(&unchecked).unwrap().value,
        Some(Expr::const_str("Nat"))
    );
}

#[test]
fn checked_irreducibility_preserves_value_kind_and_verification() {
    let (mut env, name) = fixture();
    let before = env.get_const(&name).unwrap().clone();
    let verification = env.declaration_verification(&name);
    env.restrict_checked_unfolding(&name).unwrap();
    assert_eq!(env.get_reducibility(&name), Some(Reducibility::Irreducible));
    let after = env.get_const(&name).unwrap();
    assert_eq!(after.type_, before.type_);
    assert_eq!(after.value, before.value);
    assert_eq!(after.kind, before.kind);
    assert_eq!(env.declaration_verification(&name), verification);
    let generation = env.generation();
    env.restrict_checked_unfolding(&name).unwrap();
    assert_eq!(env.generation(), generation);
}

#[test]
fn checked_irreducibility_refuses_missing_and_value_free_declarations() {
    let (mut env, _) = fixture();
    let missing = Name::from_string("Metadata.missing");
    assert!(env.restrict_checked_unfolding(&missing).is_err());
    let axiom = Name::from_string("Metadata.assumption");
    env.add_decl(Declaration::Axiom {
        name: axiom.clone(),
        level_params: vec![],
        type_: Expr::const_str("Nat"),
    })
    .unwrap();
    let before = env.get_const(&axiom).unwrap().clone();
    assert!(env.restrict_checked_unfolding(&axiom).is_err());
    assert_eq!(env.get_const(&axiom), Some(&before));
}
