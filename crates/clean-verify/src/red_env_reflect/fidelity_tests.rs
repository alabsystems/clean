// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Final stored block capture controls. No test treats `all_names` as a
//! certificate of the pre-restoration strict context or re-admits a mutated
//! record. Only the positive fixture goes through actual kernel admission.

use super::*;
use clean_kernel::{BinderInfo, Constructor, InductiveDecl, InductiveType};

fn mutual_source() -> (Environment, Vec<Name>) {
    let names = vec![
        Name::from_string("StoredBlock.ZFirst"),
        Name::from_string("StoredBlock.ASecond"),
    ];
    let mut env = Environment::new();
    let type_ = Expr::sort(Level::succ(Level::Zero));
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![
            InductiveType {
                name: names[0].clone(),
                type_: type_.clone(),
                constructors: vec![Constructor {
                    name: Name::from_string("StoredBlock.ZFirst.mk"),
                    type_: Expr::const_(names[0].clone(), vec![]),
                }],
            },
            InductiveType {
                name: names[1].clone(),
                type_: Expr::pi(BinderInfo::Default, Expr::prop(), type_),
                constructors: vec![Constructor {
                    name: Name::from_string("StoredBlock.ASecond.mk"),
                    type_: Expr::pi(
                        BinderInfo::Default,
                        Expr::prop(),
                        Expr::app(Expr::const_(names[1].clone(), vec![]), Expr::bvar(0)),
                    ),
                }],
            },
        ],
    })
    .expect("actual kernel admission of an ordered two-member source block");
    (env, names)
}

fn image(env: &Environment, name: &Name) -> ReflectedInductive {
    let source = env.get_inductive(name).expect("actual source member");
    validate_source_inductive_block(env, source).expect("actual sibling metadata agrees");
    reflect_inductive_metadata(name, source, env.get_const(name))
        .expect("capture actual same-name signature and stored block")
}

fn block_image(env: &Environment, names: &[Name]) -> Reflection {
    Reflection {
        recs: vec![],
        defs: vec![],
        nat_signatures: vec![],
        inductives: names.iter().map(|name| image(env, name)).collect(),
        constructors: vec![],
        projection_witness: None,
        interning: vec![],
        skips: vec![],
    }
}

#[test]
fn test_final_block_capture_preserves_actual_mutual_source_order() {
    crate::test_utils::run_with_stack(|| {
        let (env, names) = mutual_source();
        assert!(names[0].to_string() > names[1].to_string());
        let captured = block_image(&env, &names);
        captured
            .validate_inductive_blocks()
            .expect("source-backed block images agree");
        for (index, record) in captured.inductives.iter().enumerate() {
            let source = env.get_inductive(&names[index]).expect("source member");
            assert_eq!(record.signature.name, source.name);
            assert_eq!(record.all_names, names);
            assert_eq!(record.all_names, source.all_names);
            assert_eq!(record.constructor_names, source.constructor_names);
            assert_eq!(record.num_params, 0);
            assert_eq!(record.num_indices, index as u32);
        }
        // Different member types/index counts are valid; the ordered block
        // validator must not accidentally demand equal former telescopes.
        assert_ne!(
            captured.inductives[0].signature.type_,
            captured.inductives[1].signature.type_
        );
        assert!(
            captured.def_script().is_err(),
            "not the allowlisted full image"
        );
    });
}

#[test]
fn test_final_block_structure_refuses_loss_duplicates_and_display_collisions() {
    let family = Name::from_string("Block.Part");
    let sibling = Name::from_string("Block.Other");
    let ctor = Name::from_string("Block.Part.mk");
    let good = vec![family.clone(), sibling.clone()];
    validate_inductive_block_names(&family, &good, std::slice::from_ref(&ctor))
        .expect("distinct ordered structural identities");
    for bad in [
        vec![],
        vec![sibling],
        vec![family.clone(), family.clone()],
        vec![family.clone(), ctor.clone()],
    ] {
        assert!(
            validate_inductive_block_names(&family, &bad, std::slice::from_ref(&ctor)).is_err()
        );
    }
    let display_alias = Name::anon().str("Block.Part");
    assert_ne!(family, display_alias);
    assert_eq!(family.to_string(), display_alias.to_string());
    let error = validate_inductive_block_names(&family, &[family.clone(), display_alias], &[])
        .expect_err("structural collision must not collapse into one TSV tag");
    assert!(error.contains("display key"), "{error}");
}

#[test]
fn test_final_block_source_refuses_missing_wrong_kind_and_sibling_drift() {
    crate::test_utils::run_with_stack(|| {
        let (env, names) = mutual_source();
        let source = env.get_inductive(&names[0]).expect("actual first member");
        validate_source_inductive_block(&env, source).expect("positive source control");
        for replacement in [
            Name::from_string("StoredBlock.Missing"),
            Name::from_string("StoredBlock.ASecond.mk"),
        ] {
            let mut bad = source.clone();
            bad.all_names[1] = replacement;
            let error = validate_source_inductive_block(&env, &bad)
                .expect_err("missing or constructor-kind sibling is not an inductive");
            assert!(error.contains("absent or wrong-kind"), "{error}");
        }
        let mut changed = Vec::new();
        let mut bad = source.clone();
        bad.all_names.reverse();
        changed.push(bad);
        bad = source.clone();
        bad.all_names.truncate(1);
        changed.push(bad);
        bad = source.clone();
        bad.num_params += 1;
        changed.push(bad);
        bad = source.clone();
        bad.level_params
            .push(Name::from_string("unexpectedUniverse"));
        changed.push(bad);
        for bad in changed {
            let error = validate_source_inductive_block(&env, &bad)
                .expect_err("actual stored siblings expose list/parameter drift");
            assert!(error.contains("identity/order/parameters"), "{error}");
        }
    });
}

#[test]
fn test_final_block_image_checks_shared_order_but_does_not_authenticate_omissions() {
    crate::test_utils::run_with_stack(|| {
        let (env, names) = mutual_source();
        let good = block_image(&env, &names);
        good.validate_inductive_blocks()
            .expect("positive image control");
        for change in 0..3 {
            let mut bad = good.clone();
            match change {
                0 => bad.inductives[1].all_names.reverse(),
                1 => bad.inductives[1].num_params += 1,
                _ => bad.inductives[1]
                    .signature
                    .level_params
                    .push(Name::from_string("unexpectedUniverse")),
            }
            assert!(bad.validate_inductive_blocks().is_err());
        }
        // Internal consistency cannot authenticate a coherently truncated
        // image. Actual Environment capture and independent readback do that.
        let mut truncated = good;
        for record in &mut truncated.inductives {
            record.all_names = vec![record.signature.name.clone()];
        }
        truncated
            .validate_inductive_blocks()
            .expect("do not overstate the internal image guard");
        let mut source = env.get_inductive(&names[0]).expect("source").clone();
        source.all_names.truncate(1);
        assert!(validate_source_inductive_block(&env, &source).is_err());
    });
}

#[test]
fn test_final_block_only_names_append_without_reordering_source_or_old_tags() {
    crate::test_utils::run_with_stack(|| {
        let (env, names) = mutual_source();
        let mut selected = image(&env, &names[0]);
        let mut tags = vec![("Existing".to_string(), 0)];
        append_signature_names(&mut tags, std::slice::from_ref(&selected.signature));
        let before = tags.clone();
        assert!(!tags.iter().any(|(name, _)| name == &names[1].to_string()));
        append_inductive_block_names(&mut tags, std::slice::from_ref(&selected));
        assert_eq!(&tags[..before.len()], before);
        assert!(tags.iter().any(|(name, _)| name == &names[1].to_string()));
        assert_eq!(selected.all_names, names);
        let once = tags.clone();
        append_inductive_block_names(&mut tags, std::slice::from_ref(&selected));
        assert_eq!(tags, once);
        selected.all_names.reverse();
        append_inductive_block_names(&mut tags, &[selected]);
        assert_eq!(tags, once, "interning does not encode list order");
    });
}

#[test]
fn test_final_block_eq_aliases_and_emission_use_promoted_source_metadata() {
    crate::test_utils::run_with_stack(|| {
        let seed = crate::spec::Specification::new_red_env_reflection_seed().expect("seed");
        let env = seed.env();
        let source = env
            .get_inductive(&Name::from_string("Eq"))
            .expect("actual Eq");
        assert_eq!((source.num_params, source.num_indices), (2, 1));
        assert_eq!(source.all_names, vec![source.name.clone()]);
        let reflected = reflect_foundation_core(env).expect("actual source capture");
        let eq = reflected
            .inductives
            .iter()
            .find(|record| record.signature.name == source.name)
            .expect("captured Eq");
        assert_eq!(eq.all_names, source.all_names);
        let refl = env
            .get_constructor(&Name::from_string("Eq.refl"))
            .expect("actual Eq.refl");
        assert_eq!((refl.num_params, refl.num_fields), (2, 0));
        let script = reflected
            .def_script()
            .expect("complete source metadata emits");
        for (atom, ty, expected) in [
            (
                "kcre_eq_type_name",
                "Name",
                reflected
                    .render_name(&source.name.to_string())
                    .expect("source name"),
            ),
            (
                "kcre_eq_refl_name",
                "Name",
                reflected
                    .render_name(&refl.name.to_string())
                    .expect("source name"),
            ),
            (
                "kcre_eq_type_signature",
                "KConstSig",
                reflected
                    .metadata_atom(&source.name, "ind", "signature")
                    .expect("source atom"),
            ),
            (
                "kcre_eq_refl_signature",
                "KConstSig",
                reflected
                    .metadata_atom(&refl.name, "ctor", "signature")
                    .expect("source atom"),
            ),
            (
                "kcre_eq_ind_meta",
                "KIndMeta",
                reflected
                    .metadata_atom(&source.name, "ind", "meta")
                    .expect("source atom"),
            ),
            (
                "kcre_eq_refl_meta",
                "KCtorMeta",
                reflected
                    .metadata_atom(&refl.name, "ctor", "meta")
                    .expect("source atom"),
            ),
        ] {
            let line = format!("def {atom} : {ty} := {expected}");
            assert_eq!(
                script
                    .lines()
                    .filter(|candidate| *candidate == line)
                    .count(),
                1
            );
        }
        let meta = reflected
            .metadata_atom(&source.name, "ind", "meta")
            .expect("metadata atom");
        let line = script
            .lines()
            .find(|line| line.starts_with(&format!("def {meta} :")))
            .expect("emitted Eq metadata");
        let block = source
            .all_names
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        assert!(line.ends_with(&format!(
            " {}",
            reflected.render_params(&block).expect("stored block")
        )));
        let mut missing = reflected.clone();
        missing
            .interning
            .retain(|(name, _)| name != &source.name.to_string());
        assert!(
            missing.def_script().is_err(),
            "missing source tag cannot publish"
        );
    });
}
