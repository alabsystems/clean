// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Isolated checked data headers; this does not build or qualify the Bmem bodies.

use crate::spec::Specification;
use clean_kernel::{
    ConstantKind, DeclarationVerification, Expr, ExprKind, Level, Name, TypeChecker,
};
use std::collections::BTreeSet;

fn actual_headers(owner: &'static str) -> Vec<&'static str> {
    owner
        .split("r#\"")
        .skip(1)
        .map(|tail| {
            tail.split_once("\"#")
                .expect("complete production raw literal")
                .0
        })
        .filter(|source| source.starts_with("inductive "))
        .collect()
}

#[test]
fn actual_production_bmem_headers_have_checked_isolated_telescopes() {
    crate::test_utils::run_with_stack(|| {
        let trie = actual_headers(include_str!("eval_ir_bmem_trie.rs"));
        let core = actual_headers(include_str!("eval_ir_bmem_core.rs"));
        assert_eq!(trie.len(), 2, "exact production trie data headers");
        assert_eq!(core.len(), 12, "exact production core data headers");
        let headers: Vec<_> = trie.into_iter().chain(core).collect();
        let expected = [
            "IRBmKV",
            "IRBmTrie",
            "IRBmAlloc",
            "IRRfTy",
            "IRBmField",
            "IRBmRow",
            "IRBmHit",
            "IRBmAt",
            "IRBmLay",
            "IRBmMem",
            "IRBmCfg",
            "IRBmSize",
            "IRBmGlobal",
            "IRBmCtx",
        ];
        assert_eq!(headers.len(), expected.len());
        let mut spec =
            Specification::new_eval_ir_prelude_spec().expect("real ordinary EvalIR prelude");
        let before: BTreeSet<_> = spec
            .env()
            .inductives()
            .map(|info| info.name.clone())
            .collect();
        for (source, name) in headers.iter().zip(expected) {
            assert!(source.starts_with(&format!("inductive {name} ")));
            assert!(spec.env().get_const(&Name::from_string(name)).is_none());
            spec.add_inductive(
                source,
                "Isolated exact production data header; no Bmem body admission",
            )
            .expect("normal parser, elaborator and checked inductive registration");
        }
        let fresh: BTreeSet<_> = spec
            .env()
            .inductives()
            .filter(|info| !before.contains(&info.name))
            .map(|info| info.name.clone())
            .collect();
        let expected: BTreeSet<_> = expected.into_iter().map(Name::from_string).collect();
        assert_eq!(expected.len(), 14);
        assert_eq!(fresh, expected, "no missing, duplicate or extra family");
        let mut records = Vec::new();
        for family in fresh {
            let inductive = spec
                .env()
                .get_inductive(&family)
                .expect("actual checked family");
            let rec_name = Name::append(&family, "rec");
            let recursor = spec
                .env()
                .get_recursor(&rec_name)
                .expect("actual generated recursor");
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
                        .expect("actual constructor");
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
                    .expect("full declared-type check");
                assert!(matches!(checker.whnf(&sort).kind(), ExprKind::Sort(_)));
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
            records.push(
                serde_json::json!({"family": inductive, "recursor": recursor,
                "constants": constants}),
            );
        }
        assert_eq!(records.len(), 14);
        println!("BMEM_ISOLATED_TYPE_TELESCOPES {}",
            serde_json::to_string(&serde_json::json!({"records": records, "sources": headers,
                "scope": "Exact included production data headers through normal checked add_inductive in ordinary EvalIR prelude; isolated TYPE metadata only, not Bmem definitions, actual complete bundle, Full, runtime, strict46 or axiom-closure qualification"}))
                .expect("metadata serialization"));
    });
}
