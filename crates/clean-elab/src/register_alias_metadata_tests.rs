// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::register_param_names;
use crate::ElabResult;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, KernelEnvError, Name};
use clean_parser::{parse_file, DeclModifiers};

fn alias_source() -> clean_parser::SurfaceDecl {
    parse_file("alias metadataAlias := Nat.succ")
        .expect("alias syntax")
        .remove(0)
}

fn alias_result(ty: Expr) -> ElabResult {
    ElabResult::Definition {
        name: Name::from_string("metadataAlias"),
        universe_params: vec![],
        ty,
        val: Expr::const_(Name::from_string("Nat.succ"), vec![]),
        modifiers: DeclModifiers::default(),
    }
}

#[test]
fn alias_metadata_validates_the_resident_telescope_before_writing() {
    let mut env = Environment::with_prelude();
    let target = Name::from_string("Nat.succ");
    let alias = Name::from_string("metadataAlias");
    env.add_checked_param_infos(
        &target,
        vec![(Name::from_string("n"), BinderInfo::Default)],
        true,
    )
    .expect("checked target binder metadata");
    let ty = env.get_const(&target).expect("target").type_.clone();
    env.add_decl(Declaration::Definition {
        name: alias.clone(),
        level_params: vec![],
        type_: ty.clone(),
        value: Expr::const_(target, vec![]),
        is_reducible: false,
    })
    .expect("checked alias declaration");
    register_param_names(&mut env, &alias_source(), &alias_result(ty));
    assert_eq!(
        env.get_typed_param_names(&alias),
        Some([Name::from_string("n")].as_slice())
    );
    assert_eq!(
        env.get_param_binder_infos(&alias),
        Some([BinderInfo::Default].as_slice())
    );
}

#[test]
fn alias_metadata_refuses_a_resident_telescope_mismatch_without_writing() {
    let mut env = Environment::with_prelude();
    let target = Name::from_string("Nat.succ");
    let alias = Name::from_string("metadataAlias");
    env.add_checked_param_infos(
        &target,
        vec![(Name::from_string("n"), BinderInfo::Default)],
        true,
    )
    .expect("checked target binder metadata");
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Definition {
        name: alias.clone(),
        level_params: vec![],
        type_: ty.clone(),
        value: Expr::const_(Name::from_string("Nat.zero"), vec![]),
        is_reducible: false,
    })
    .expect("checked resident zero");
    let before = env.get_const(&alias).expect("resident alias").clone();
    let before_verification = env.declaration_verification(&alias);
    let before_generation = env.generation();
    let error = env
        .add_checked_param_infos(
            &alias,
            vec![(Name::from_string("n"), BinderInfo::Default)],
            false,
        )
        .expect_err("target metadata cannot overrun the resident alias type");
    assert!(matches!(
        error,
        KernelEnvError::InvalidDeclarationShape {
            init: "checked declaration metadata",
            ref decl,
            detail: "parameter metadata exceeds the declaration telescope",
        } if decl == &alias
    ));
    register_param_names(&mut env, &alias_source(), &alias_result(ty));
    assert!(env.get_param_binder_infos(&alias).is_none());
    assert!(env.get_typed_param_names(&alias).is_none());
    let after = env.get_const(&alias).expect("alias remains resident");
    assert_eq!(before.type_, after.type_);
    assert_eq!(before.value, after.value);
    assert_eq!(before.name, after.name);
    assert_eq!(before.level_params, after.level_params);
    assert_eq!(before.kind, after.kind);
    assert_eq!(env.declaration_verification(&alias), before_verification);
    assert_eq!(env.generation(), before_generation);
}
