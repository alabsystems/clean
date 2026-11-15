// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel/import-style field metadata at the actual structure-literal boundary.
//! The literal is a typed AST; this does not claim source syntax accepts the
//! space-bearing field identity used to collide with a diagnostic fallback.

use super::*;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};

fn metadata_env(target_has_metadata: bool) -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("Nat initialization");
    for owner in ["MetadataSource", "MetadataTarget"] {
        let owner = SurfaceName::generated_path(owner).into_name();
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: owner.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: owner.clone().str("mk"),
                    type_: Expr::arrow(
                        Expr::const_(Name::from_string("Nat"), vec![]),
                        Expr::const_(owner, vec![]),
                    ),
                }],
            }],
        })
        .expect("checked one-field inductive");
    }
    let field = Name::anon().str("field 0");
    env.register_structure_fields(Name::from_string("MetadataSource"), vec![field.clone()])
        .expect("source's actual exact field metadata");
    if target_has_metadata {
        env.register_structure_fields(Name::from_string("MetadataTarget"), vec![field])
            .expect("target's actual exact field metadata");
    }
    env
}

fn elaborate_update(env: &Environment, source_owner: Name) -> (Result<Expr, ElabError>, Expr) {
    let mut ctx = ElabCtx::new(env);
    let local = SurfaceName::generated_path("source");
    let fvar = ctx.push_local(local.clone(), Expr::const_(source_owner, vec![]));
    let target = SurfaceName::generated_path("MetadataTarget");
    let result = ctx.elab_struct_lit(
        &Some(Box::new(SurfaceExpr::Ident(Span::dummy(), target.clone()))),
        &Some(Box::new(SurfaceExpr::Ident(Span::dummy(), local))),
        &[],
    );
    if let Ok(value) = &result {
        let actual_type = ctx.infer_type(value).expect("check elaborated update type");
        assert!(ctx.is_def_eq(&actual_type, &Expr::const_(target.into_name(), vec![])));
    }
    (result, Expr::fvar(fvar))
}

#[test]
fn missing_target_metadata_does_not_select_diagnostic_field_name() {
    let env = metadata_env(false);
    let target = Name::from_string("MetadataTarget");
    assert!(env.get_structure_field_names(&target).is_none());
    assert_eq!(
        env.get_structure_field_names(&Name::from_string("MetadataSource")),
        Some([Name::anon().str("field 0")].as_slice())
    );
    let (result, _) = elaborate_update(&env, Name::from_string("MetadataSource"));
    match result.expect_err("diagnostic field 0 must not become a selector") {
        ElabError::MissingStructureFields {
            struct_name,
            fields,
        } => {
            assert_eq!(struct_name, target);
            assert_eq!(fields, vec!["field 0".to_owned()]);
        }
        other => panic!("expected the missing-field refusal, got {other:?}"),
    }
}

#[test]
fn real_target_metadata_selects_the_exact_diagnostic_spelling_twin() {
    let env = metadata_env(true);
    assert_eq!(
        env.get_structure_field_names(&Name::from_string("MetadataTarget")),
        Some([Name::anon().str("field 0")].as_slice())
    );
    let source_owner = Name::from_string("MetadataSource");
    let (result, source) = elaborate_update(&env, source_owner.clone());
    assert_eq!(
        result.expect("real field metadata must select the source field"),
        Expr::app(
            Expr::const_(Name::from_string("MetadataTarget.mk"), vec![]),
            Expr::proj(source_owner, 0, source),
        )
    );
}

#[test]
fn missing_metadata_preserves_same_structure_positional_update() {
    let env = metadata_env(false);
    let target = Name::from_string("MetadataTarget");
    assert!(env.get_structure_field_names(&target).is_none());
    let (result, source) = elaborate_update(&env, target.clone());
    assert_eq!(
        result.expect("same-structure update must not need a field-name table"),
        Expr::app(
            Expr::const_(target.clone().str("mk"), vec![]),
            Expr::proj(target, 0, source),
        )
    );
}
