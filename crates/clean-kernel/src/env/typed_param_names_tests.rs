use super::*;

#[test]
fn exact_parameter_names_keep_dotted_and_numeric_twins() {
    let mut env = Environment::default();
    let owner = Name::anon().str("f");
    let names = vec![
        Name::anon().str("a.b"),
        Name::anon().str("a").str("b"),
        Name::anon().str("7"),
        Name::anon().num(7),
    ];
    env.set_typed_param_infos(
        owner.clone(),
        names
            .iter()
            .cloned()
            .map(|n| (n, BinderInfo::Implicit))
            .collect(),
    );
    assert_eq!(env.get_typed_param_names(&owner), Some(names.as_slice()));
    assert_ne!(names[0], names[1]);
    assert_ne!(names[2], names[3]);
    let display = env.get_param_names(&owner).unwrap();
    assert_eq!(display[0], display[1]);
    assert_eq!(display[2], display[3]);
    assert_eq!(
        env.get_param_binder_infos(&owner),
        Some([BinderInfo::Implicit; 4].as_slice())
    );
}

#[test]
fn legacy_parameter_mutations_invalidate_exact_sidecar() {
    let mut env = Environment::default();
    let owner = Name::anon().str("f");
    env.set_typed_param_names(owner.clone(), vec![Name::anon().str("a.b")]);
    env.set_param_names(owner.clone(), vec!["a.b".into()]);
    assert!(env.get_typed_param_names(&owner).is_none());
    env.set_typed_param_infos(
        owner.clone(),
        vec![(Name::anon().str("7"), BinderInfo::Implicit)],
    );
    env.set_param_infos(owner.clone(), vec![("7".into(), BinderInfo::Default)]);
    assert!(env.get_typed_param_names(&owner).is_none());
    assert_eq!(
        env.get_param_binder_infos(&owner),
        Some([BinderInfo::Default].as_slice())
    );
}

#[test]
fn shadowing_overlay_removes_only_exact_parameter_owner() {
    let mut env = Environment::default();
    let quoted = Name::anon().str("a.b");
    let nested = Name::anon().str("a").str("b");
    env.set_typed_param_names(quoted.clone(), vec![Name::anon().str("quoted")]);
    env.set_typed_param_names(nested.clone(), vec![Name::anon().str("nested")]);
    let overlay = env.clone_pruned_shadowing_overlay(&[quoted.clone()].into_iter().collect());
    assert!(overlay.get_typed_param_names(&quoted).is_none());
    assert_eq!(
        overlay.get_typed_param_names(&nested),
        env.get_typed_param_names(&nested)
    );
    assert!(env.get_typed_param_names(&quoted).is_some());
}
