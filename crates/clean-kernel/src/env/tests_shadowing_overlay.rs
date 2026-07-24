// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::mode::CleanMode;
use std::collections::HashSet;

fn single_ctor_decl(name: &Name, ctor_name: &Name) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: ctor_name.clone(),
                type_: Expr::const_(name.clone(), vec![]),
            }],
        }],
    }
}

fn insert_generated_inductive_names(shadowed_names: &mut HashSet<Name>, type_name: &Name) {
    let type_name = type_name.to_string();
    for suffix in ["rec", "casesOn", "recOn", "noConfusionType", "noConfusion"] {
        shadowed_names.insert(Name::from_string(&format!("{type_name}.{suffix}")));
    }
}

struct ShadowingOverlayFixture {
    env: Environment,
    shadow_name: Name,
    shadow_ctor: Name,
    stale_shadow_instance: Name,
    keep_class: Name,
    keep_instance: Name,
    ext_name: Name,
    payload_name: Name,
    original_generation: u64,
}

fn add_shadow_structure_fixture(env: &mut Environment) -> (Name, Name, Name) {
    let shadow_name = Name::from_string("Shadow.Struct");
    let shadow_ctor = Name::from_string("Shadow.Struct.mk");
    env.add_inductive(single_ctor_decl(&shadow_name, &shadow_ctor))
        .expect("shadow structure should register");
    env.register_structure_fields(shadow_name.clone(), vec![])
        .expect("shadow structure fields should register");
    env.register_class(KernelClassInfo {
        name: shadow_name.clone(),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });

    let stale_shadow_instance = Name::from_string("Shadow.oldInst");
    env.add_decl_unchecked(Declaration::Axiom {
        name: stale_shadow_instance.clone(),
        level_params: vec![],
        type_: Expr::const_(shadow_name.clone(), vec![]),
    });
    env.register_instance(KernelInstanceInfo {
        name: stale_shadow_instance.clone(),
        class_name: shadow_name.clone(),
        priority: DEFAULT_INSTANCE_PRIORITY,
        type_: Some(Expr::const_(shadow_name.clone(), vec![])),
        value: None,
    });
    env.set_param_names(stale_shadow_instance.clone(), vec!["inst".to_string()]);

    (shadow_name, shadow_ctor, stale_shadow_instance)
}

fn add_keep_class_fixture(env: &mut Environment) -> (Name, Name) {
    let keep_class = Name::from_string("Keep.Class");
    env.add_decl_unchecked(Declaration::Axiom {
        name: keep_class.clone(),
        level_params: vec![],
        type_: Expr::type_(),
    });
    env.register_class(KernelClassInfo {
        name: keep_class.clone(),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });

    let keep_instance = Name::from_string("Keep.inst");
    env.add_decl_unchecked(Declaration::Axiom {
        name: keep_instance.clone(),
        level_params: vec![],
        type_: Expr::const_(keep_class.clone(), vec![]),
    });
    env.register_instance(KernelInstanceInfo {
        name: keep_instance.clone(),
        class_name: keep_class.clone(),
        priority: DEFAULT_INSTANCE_PRIORITY,
        type_: Some(Expr::const_(keep_class.clone(), vec![])),
        value: None,
    });
    env.set_param_names(keep_instance.clone(), vec!["keep".to_string()]);

    (keep_class, keep_instance)
}

fn add_extension_fixture(env: &mut Environment) -> (Name, Name) {
    let ext_name = Name::from_string("overlay.ext");
    let payload_name = Name::from_string("overlay.entry");
    assert!(
        env.register_persistent_extension(ext_name.clone()),
        "persistent extension should register once"
    );
    env.add_persistent_extension_entries(
        &ext_name,
        0,
        vec![EnvExtensionEntry {
            name: payload_name.clone(),
            data: EnvExtensionEntryData::Scalar(7),
        }],
    );

    (ext_name, payload_name)
}

fn build_shadowing_overlay_fixture() -> ShadowingOverlayFixture {
    let mut env = Environment::with_mode(CleanMode::Classical);
    env.init_quot();

    let (shadow_name, shadow_ctor, stale_shadow_instance) = add_shadow_structure_fixture(&mut env);
    let (keep_class, keep_instance) = add_keep_class_fixture(&mut env);
    let (ext_name, payload_name) = add_extension_fixture(&mut env);

    ShadowingOverlayFixture {
        original_generation: env.generation(),
        env,
        shadow_name,
        shadow_ctor,
        stale_shadow_instance,
        keep_class,
        keep_instance,
        ext_name,
        payload_name,
    }
}

fn assert_shadowed_entries_pruned(fixture: &ShadowingOverlayFixture, overlay: &Environment) {
    assert_eq!(
        overlay.mode(),
        CleanMode::Classical,
        "overlay must preserve the source environment mode"
    );
    assert_eq!(
        overlay.num_quotients(),
        fixture.env.num_quotients(),
        "overlay must preserve quotient state"
    );
    assert!(
        overlay.get_const(&fixture.shadow_name).is_none(),
        "shadowed structure constant must be pruned"
    );
    assert!(
        overlay.get_constructor(&fixture.shadow_ctor).is_none(),
        "shadowed constructor must be pruned"
    );
    assert!(
        overlay
            .get_recursor(&Name::from_string("Shadow.Struct.rec"))
            .is_none(),
        "generated recursor names must be pruned when requested"
    );
    assert!(
        overlay
            .get_structure_field_names(&fixture.shadow_name)
            .is_none(),
        "shadowed structure fields must be pruned with the structure name"
    );
    assert!(
        !overlay.is_class(&fixture.shadow_name),
        "shadowed class metadata must be pruned with the structure name"
    );
    assert!(
        overlay.get_class_instances(&fixture.shadow_name).is_empty(),
        "instances of a shadowed class must be dropped even when their names are not shadowed"
    );
    assert!(
        overlay.get_const(&fixture.stale_shadow_instance).is_some(),
        "non-shadowed stale instance constants stay available as plain constants in the overlay"
    );
    assert!(
        overlay
            .get_param_names(&fixture.stale_shadow_instance)
            .is_some(),
        "param names for unrelated constants must be preserved"
    );
    assert!(
        overlay.generation() > fixture.original_generation,
        "overlay pruning must bump generation for cache invalidation"
    );
}

fn assert_preserved_entries(fixture: &ShadowingOverlayFixture, overlay: &Environment) {
    assert!(
        overlay.is_class(&fixture.keep_class),
        "unrelated class metadata must survive cloning"
    );
    assert!(
        overlay.is_instance(&fixture.keep_instance),
        "unrelated instance metadata must survive cloning"
    );
    let keep_param_names = overlay
        .get_param_names(&fixture.keep_instance)
        .expect("unrelated parameter names must survive cloning");
    assert_eq!(
        keep_param_names.len(),
        1,
        "keep instance should have one param name"
    );
    assert_eq!(
        keep_param_names[0], "keep",
        "param name should be preserved"
    );
    assert!(
        overlay
            .get_persistent_extension_state(&fixture.ext_name)
            .is_some(),
        "persistent extensions must survive cloning"
    );
    let entries = overlay
        .get_persistent_extension_module_entries(&fixture.ext_name, 0)
        .expect("overlay extension entries should remain");
    assert_eq!(
        entries.len(),
        1,
        "persistent extension should keep one entry"
    );
    assert_eq!(
        entries[0].name, fixture.payload_name,
        "entry name should be preserved"
    );
    match &entries[0].data {
        EnvExtensionEntryData::Scalar(value) => {
            assert_eq!(*value, 7, "entry payload should be preserved");
        }
        other => panic!("expected scalar payload, got {other:?}"),
    }
}

fn assert_original_env_unchanged(fixture: &ShadowingOverlayFixture) {
    assert!(
        fixture.env.get_const(&fixture.shadow_name).is_some(),
        "helper must not mutate the original environment"
    );
    assert!(
        fixture.env.is_class(&fixture.shadow_name),
        "original class metadata must remain intact"
    );
    assert!(
        !fixture
            .env
            .get_class_instances(&fixture.shadow_name)
            .is_empty(),
        "original instance registry must remain intact"
    );
}

#[test]
fn test_clone_pruned_shadowing_overlay_preserves_env_payload() {
    let fixture = build_shadowing_overlay_fixture();
    let mut shadowed_names =
        HashSet::from([fixture.shadow_name.clone(), fixture.shadow_ctor.clone()]);
    insert_generated_inductive_names(&mut shadowed_names, &fixture.shadow_name);

    let overlay = fixture.env.clone_pruned_shadowing_overlay(&shadowed_names);

    assert_shadowed_entries_pruned(&fixture, &overlay);
    assert_preserved_entries(&fixture, &overlay);
    assert_original_env_unchanged(&fixture);
}
