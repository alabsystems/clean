// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Actual checked type-prefix metadata, not completed byte/public/Full admission.

use crate::spec::Specification;
use clean_kernel::{
    ConstantKind, DeclarationVerification, Expr, ExprKind, Level, Name, TypeChecker,
};
use std::collections::BTreeSet;

#[test]
fn checked_byte_type_prefix_has_exact_live_family_telescopes() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = Specification::new_eval_ir_prelude_spec().expect("ordinary checked prelude");
        let before: BTreeSet<_> = spec.env().inductives().map(|v| v.name.clone()).collect();
        spec.add_eval_ir_byte_types()
            .expect("the actual checked production type registration");
        let fresh: BTreeSet<_> = spec
            .env()
            .inductives()
            .filter(|v| !before.contains(&v.name))
            .map(|v| v.name.clone())
            .collect();
        let expected: BTreeSet<_> = [
            "IRByteEnumVariantV1",
            "IRByteEnumV1",
            "IRByteLayoutV1",
            "IRByteSignatureV1",
            "IRByteFunctionV1",
            "IRByteOperandV1",
            "IRByteSiteV1",
            "IRByteContextV1",
            "IRByteAllocationV1",
            "IRByteMemoryV1",
            "IRByteMemoryResultV1",
            "IRByteWorldV1",
            "IRByteConfigV1",
            "IRByteImportResultV1",
            "IRByteValueMatchV1",
        ]
        .into_iter()
        .map(Name::from_string)
        .collect();
        assert_eq!(expected.len(), 15);
        assert_eq!(
            fresh, expected,
            "exact source-family enrollment, never empty"
        );
        let mut records = Vec::new();
        for family in fresh {
            let inductive = spec.env().get_inductive(&family).expect("live family");
            let rec_name = Name::append(&family, "rec");
            let recursor = spec.env().get_recursor(&rec_name).expect("live recursor");
            assert_eq!(recursor.inductive_name, family);
            assert_eq!(recursor.num_params, inductive.num_params);
            assert_eq!(recursor.num_indices, inductive.num_indices);
            assert_eq!(
                recursor.num_minors as usize,
                inductive.constructor_names.len()
            );
            let mut constants = Vec::new();
            for lookup in std::iter::once(family.clone())
                .chain(inductive.constructor_names.iter().cloned())
                .chain(std::iter::once(rec_name.clone()))
            {
                let info = spec.env().get_const(&lookup).expect("actual live constant");
                assert_eq!(info.name, lookup, "typed name identity");
                assert_ne!(info.kind, ConstantKind::Axiom);
                assert_eq!(
                    spec.env().declaration_verification(&lookup),
                    Some(DeclarationVerification::FullKernelCheck)
                );
                if lookup == family {
                    assert_eq!(info.type_, inductive.type_);
                } else if lookup == rec_name {
                    assert_eq!(info.type_, recursor.type_);
                } else {
                    let constructor = spec
                        .env()
                        .get_constructor(&lookup)
                        .expect("live constructor");
                    assert_eq!(constructor.inductive_name, family);
                    assert_eq!(info.type_, constructor.type_);
                }
                assert!(!info.type_.has_fvar_quick());
                assert!(!info.type_.has_loose_bvars());
                assert!(!info.type_.has_expr_mvar_quick());
                assert!(!info.type_.has_level_mvar_quick());
                let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
                let sort = checker
                    .infer_type_full(&info.type_)
                    .expect("full declared type check");
                assert!(matches!(checker.whnf(&sort).kind(), ExprKind::Sort(_)));
                let term = Expr::const_(
                    lookup.clone(),
                    info.level_params
                        .iter()
                        .cloned()
                        .map(Level::param)
                        .collect::<Vec<_>>(),
                );
                checker
                    .check_type(&term, &info.type_)
                    .expect("public full constant check");
                assert!(!checker.heartbeat_spent());
                constants.push(serde_json::json!({
                    "lookup_name": lookup,
                    "constant": info,
                    "verification": spec.env().declaration_verification(&info.name),
                }));
            }
            records.push(serde_json::json!({
                "family": inductive,
                "recursor": recursor,
                "constants": constants,
            }));
        }
        assert_eq!(records.len(), 15);
        println!(
            "BYTE_TYPE_PREFIX_TELESCOPES {}",
            serde_json::to_string(&serde_json::json!({
                "records": records,
                "scope": "Normal checked prelude plus actual byte_types only; no later byte/public/Full/strict46 admission or body/world claim",
            }))
            .expect("metadata serialization")
        );
    });
}
