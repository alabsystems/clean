// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Checked ordinary-prelude metadata only; no completed division or late46 admission.

use crate::spec::Specification;
use clean_kernel::{
    ConstantKind, DeclarationVerification, Expr, ExprKind, Level, Name, TypeChecker,
};

#[test]
fn checked_prelude_divmod_family_has_live_checked_telescope() {
    crate::test_utils::run_with_stack(|| {
        let spec =
            Specification::new_eval_ir_prelude_spec().expect("ordinary checked EvalIR prelude");
        let family = Name::from_string("IRDivMod");
        let rec_name = Name::from_string("IRDivMod.rec");
        let ctor_name = Name::from_string("IRDivMod.mk");
        let inductive = spec
            .env()
            .get_inductive(&family)
            .expect("actual data family");
        let recursor = spec.env().get_recursor(&rec_name).expect("actual recursor");
        assert_eq!(inductive.num_params, 0);
        assert_eq!(inductive.num_indices, 0);
        assert_eq!(inductive.constructor_names, vec![ctor_name.clone()]);
        assert_eq!(recursor.inductive_name, family);
        assert_eq!(recursor.num_params, 0);
        assert_eq!(recursor.num_indices, 0);
        assert_eq!(recursor.num_minors, 1);
        let mut constants = Vec::new();
        for lookup in [family.clone(), ctor_name, rec_name.clone()] {
            let info = spec.env().get_const(&lookup).expect("live constant");
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
                assert_eq!(constructor.type_, info.type_);
            }
            assert!(!info.type_.has_fvar_quick());
            assert!(!info.type_.has_loose_bvars());
            assert!(!info.type_.has_expr_mvar_quick());
            assert!(!info.type_.has_level_mvar_quick());
            let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
            let type_type = checker
                .infer_type_full(&info.type_)
                .expect("full declared-type check");
            assert!(matches!(checker.whnf(&type_type).kind(), ExprKind::Sort(_)));
            let term = Expr::const_(
                lookup,
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
                "constant": info,
                "verification": spec.env().declaration_verification(&info.name),
            }));
        }
        assert_eq!(constants.len(), 3);
        println!(
            "DIVMOD_TYPE_PREFIX_TELESCOPE {}",
            serde_json::to_string(&serde_json::json!({
                "family": inductive,
                "recursor": recursor,
                "constants": constants,
                "scope": "Normal checked ordinary EvalIR prelude only; no division law, completed byte model, Full, late46 body or AX-closure claim",
            })).expect("metadata serialization")
        );
    });
}
