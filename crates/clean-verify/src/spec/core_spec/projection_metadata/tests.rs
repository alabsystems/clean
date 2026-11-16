// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::test_utils::{build_spec_with_stack, run_with_stack};
use clean_kernel::{ConstantKind, ExprKind, Name};

const NEGATIVE_CONTROLS: &[&str] = &[
    r"def projection_metadata_forged_bound_success : @Eq (OptionType ProjectionMetadataResult)
 (projection_resolve projection_metadata_control_env (Nat.succ Nat.zero) Name.anonymous (Nat.succ Nat.zero) projection_metadata_control_type)
 (@OptionType.some ProjectionMetadataResult projection_metadata_control_result) := @Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.some ProjectionMetadataResult projection_metadata_control_result)",
    r"def projection_metadata_forged_universe_success : @Eq (OptionType ProjectionMetadataResult)
 (projection_resolve projection_metadata_control_env (Nat.succ Nat.zero) Name.anonymous Nat.zero (KExpr.const Name.anonymous (@ListType.cons Level Level.zero (@ListType.nil Level))))
 (@OptionType.some ProjectionMetadataResult projection_metadata_control_result) := @Eq.refl (OptionType ProjectionMetadataResult) (@OptionType.some ProjectionMetadataResult projection_metadata_control_result)",
    r"def projection_metadata_forged_parent_agreement : ProjectionMetadataAgreement projection_metadata_control_tenv Name.anonymous projection_metadata_wrong_parent_result :=
 @ProjectionMetadataAgreement.mk projection_metadata_control_tenv Name.anonymous projection_metadata_wrong_parent_result
 (@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig (kind_sig projection_metadata_control_ind)))
 (@Eq.refl (OptionType KConstSig) (@OptionType.some KConstSig projection_metadata_control_sig))
 (@Eq.refl (ListType Name) (@ListType.nil Name)) (@Eq.refl Name Name.anonymous) (@Eq.refl Nat Nat.zero) (@Eq.refl Nat Nat.zero)",
    r"def projection_metadata_forged_order_agreement : ProjectionUniverseCoherence
 (@ListType.cons Name Name.anonymous (@ListType.cons Name projection_metadata_control_cn (@ListType.nil Name)))
 (KConstSig.mk (@ListType.cons Name projection_metadata_control_cn (@ListType.cons Name Name.anonymous (@ListType.nil Name))) (KExpr.sort Level.zero)) :=
 @Eq.refl (ListType Name) (@ListType.cons Name Name.anonymous (@ListType.cons Name projection_metadata_control_cn (@ListType.nil Name)))",
];

#[test]
fn projection_metadata_static_records_parse() {
    let actual: Vec<_> = PROOFS
        .iter()
        .chain(CONTROLS)
        .chain(GENERATED_PROOFS)
        .map(|(name, _, _)| *name)
        .collect();
    assert_eq!(
        actual, PROOF_ROOTS,
        "audit roots cover every actual proof record"
    );
    for source in DATA.iter().chain(CONTROL_DATA).chain(GENERATED_DATA) {
        clean_parser::parse_decl(source).expect("metadata declaration parses");
    }
    for &(name, ty, body) in PROOFS.iter().chain(CONTROLS).chain(GENERATED_PROOFS) {
        clean_parser::parse_decl(&format!("def {name} : {ty} := {body}"))
            .expect("explicit checked proof record parses");
    }
    for source in NEGATIVE_CONTROLS {
        clean_parser::parse_decl(source).expect("negative controls must parse");
    }
}

#[test]
fn projection_metadata_actual_registered_proofs_have_empty_closures() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        for &(name, ty_source, value_source) in
            PROOFS.iter().chain(CONTROLS).chain(GENERATED_PROOFS)
        {
            let definition = spec.definitions().get(name).expect("registered proof");
            let kernel_name = Name::from_string(name);
            let constant = spec.env().get_const(&kernel_name).expect("actual root");
            let ty = definition.elaborated_type.as_ref().expect("checked type");
            let value = definition.elaborated_value.as_ref().expect("checked body");
            assert!(!definition.is_axiom, "{name}");
            assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
            assert_eq!(definition.category, AxiomCategory::DerivedLemma, "{name}");
            assert_eq!(
                definition.proof_status,
                ProofStatus::DerivedProved,
                "{name}"
            );
            assert_eq!(definition.type_src, ty_source, "{name}");
            assert_eq!(
                definition.value_src.as_deref(),
                Some(value_source),
                "{name}"
            );
            assert_eq!(&constant.type_, ty, "{name}");
            assert_eq!(constant.value.as_ref(), Some(value), "{name}");
            assert!(
                !matches!(value.kind(), ExprKind::Const(n, _) if n == &kernel_name),
                "{name}"
            );
            spec.verify_definition(name).expect("actual proof rechecks");
            assert!(
                spec.env()
                    .axiom_deps(&kernel_name)
                    .expect("domain closure")
                    .is_empty(),
                "{name}"
            );
            assert!(
                spec.env()
                    .foundational_axiom_deps(&kernel_name)
                    .expect("foundation closure")
                    .is_empty(),
                "{name}"
            );
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    });
}

#[test]
fn projection_metadata_refuses_forged_success_and_agreement() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        for source in NEGATIVE_CONTROLS {
            let clean_parser::SurfaceDecl::Def { name, .. } =
                clean_parser::parse_decl(source).expect("negative control must parse")
            else {
                panic!("expected definition");
            };
            let error = spec
                .add_recursive_def(
                    source,
                    "Reject a false runtime success or false admitted-record equality.",
                )
                .expect_err("forged evidence must fail type checking");
            assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
            // Legacy record-key projection only; exact kernel identity is checked separately.
            assert!(
                !spec.definitions().contains_key(
                    &name
                        .qualify_under(&Default::default())
                        .into_name()
                        .to_string()
                ),
                "{name}"
            );
            assert!(
                spec.env()
                    .get_const(&name.qualify_under(&Default::default()).into_name())
                    .is_none(),
                "{name}"
            );
        }
    });
}
