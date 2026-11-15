// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `clean-compiler-unvalidated` re-stamp and the link views, on modules
//! the real emitter produced.

use super::*;
use crate::emit_trust_ir::{emit_trust_ir_with_config, RuntimeLowering, TrustIrConfig};
use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;

/// `fn forty_two() -> u64 { ret 42 }` and `fn main() -> u64 { ret forty_two() }`.
fn two_bodies() -> Vec<IRDecl> {
    let forty_two = IRDecl {
        name: Name::from_string("forty_two"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let main = IRDecl {
        name: Name::from_string("main"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: FnId(Name::from_string("forty_two")),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    vec![forty_two, main]
}

fn extern_calls_module() -> Module {
    let config = TrustIrConfig {
        module_name: "lane".to_owned(),
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    emit_trust_ir_with_config(&two_bodies(), &config).expect("the fixture lowers")
}

#[test]
fn scalar_c_signature_checks_actual_definition_and_refuses_abi_mutations() {
    let module = extern_calls_module();
    check_scalar_c_signature(&module, "forty_two", &[], ScalarWord::U64).unwrap();
    assert!(
        check_scalar_c_signature(&module, "forty_two", &[ScalarWord::U32], ScalarWord::U64)
            .is_err()
    );
    assert!(check_scalar_c_signature(&module, "forty_two", &[], ScalarWord::U32).is_err());
    assert!(check_scalar_c_signature(&module, "absent", &[], ScalarWord::U64).is_err());
    for mutation in 0..6 {
        let mut bad = module.clone();
        let function = bad
            .functions
            .iter_mut()
            .find(|f| f.name == "forty_two")
            .unwrap();
        match mutation {
            0 => function.calling_conv = trust_ir::CallingConv::Fast,
            1 => function.attrs.naked = true,
            2 => function.blocks.clear(),
            3 => bad.func_types[function.ty.as_usize()].is_vararg = true,
            4 => function.linkage = trust_ir::Linkage::Weak,
            _ => function.visibility = trust_ir::Visibility::Hidden,
        }
        assert!(
            check_scalar_c_signature(&bad, "forty_two", &[], ScalarWord::U64).is_err(),
            "mutation {mutation}"
        );
    }
}

fn gates(module: &Module) -> Vec<(String, Option<BodyGate>)> {
    module
        .functions
        .iter()
        .map(|f| (f.name.clone(), f.body_gate.clone()))
        .collect()
}

#[test]
fn test_restamp_ungated_bodies_become_unvalidated_and_bodyless_stay_none() {
    let mut module = extern_calls_module();
    let bodies = module
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty())
        .count();
    assert_eq!(bodies, 2, "the fixture has two bodies");
    assert!(
        module
            .functions
            .iter()
            .filter(|f| !f.blocks.is_empty())
            .all(|f| f.body_gate == Some(BodyGate::Ungated)),
        "the emitter stamps every body Ungated: {:?}",
        gates(&module)
    );
    let census = restamp_ungated_as_unvalidated(&mut module).expect("no claim-less body");
    assert_eq!(census.unvalidated, 2);
    assert!(census.kept.is_empty());
    for function in &module.functions {
        if function.blocks.is_empty() {
            assert_eq!(
                function.body_gate, None,
                "bodyless `{}` is not a codegen subject",
                function.name
            );
        } else {
            assert_eq!(
                function.body_gate,
                Some(BodyGate::Gated {
                    authority: CLEAN_COMPILER_UNVALIDATED_AUTHORITY.to_owned(),
                    evidence: None,
                }),
                "body `{}`",
                function.name
            );
        }
    }
    assert!(
        trust_ir_build::validate_module(&module).is_empty(),
        "the re-stamped module is still structurally valid"
    );
}

#[test]
fn test_restamp_keeps_an_existing_gated_claim() {
    let mut module = extern_calls_module();
    let tv = BodyGate::Gated {
        authority: "clean-kernel-tv".to_owned(),
        evidence: None,
    };
    let forty_two = module
        .functions
        .iter_mut()
        .find(|f| f.name == "forty_two")
        .expect("forty_two is emitted");
    forty_two.body_gate = Some(tv.clone());
    let census = restamp_ungated_as_unvalidated(&mut module).expect("no claim-less body");
    assert_eq!(census.unvalidated, 1, "only `main` was Ungated");
    assert_eq!(census.kept.get("clean-kernel-tv"), Some(&1));
    let kept = module
        .functions
        .iter()
        .find(|f| f.name == "forty_two")
        .expect("forty_two is emitted");
    assert_eq!(
        kept.body_gate,
        Some(tv),
        "a Gated claim is never overwritten"
    );
}

/// NEGATIVE CONTROL: a claim-less body is refused by name and the module is
/// left untouched — the lane never licenses the permissive `None` state.
#[test]
fn test_restamp_refuses_a_claim_less_body_and_changes_nothing() {
    let mut module = extern_calls_module();
    let main = module
        .functions
        .iter_mut()
        .find(|f| f.name == "main")
        .expect("main is emitted");
    main.body_gate = None;
    let before = gates(&module);
    let err = restamp_ungated_as_unvalidated(&mut module).expect_err("None must be refused");
    assert_eq!(err, LaneLicenseError::ClaimLessBody("main".to_owned()));
    assert_eq!(gates(&module), before, "all or nothing");
}

#[test]
fn test_link_views_read_the_emitted_signatures() {
    let module = extern_calls_module();
    let main = defined_signature(&module, "main").expect("main is defined");
    assert!(main.params.is_empty());
    assert_eq!(main.returns, vec![AbiSlot::Other("U64".to_owned())]);
    assert!(defined_signature(&module, "absent").is_none());
    let defined = defined_symbols(&module);
    assert!(defined.contains(&"main".to_owned()) && defined.contains(&"forty_two".to_owned()));
    // ExternCalls declares the runtime ABI it routes through, bodyless.
    let bodyless = bodyless_declarations(&module);
    assert!(
        bodyless.iter().all(|d| !defined.contains(&d.symbol)),
        "a symbol is either defined or left to the link, never both"
    );
    assert!(
        bodyless.iter().any(|d| d.symbol.starts_with("clean_")),
        "ExternCalls declares its runtime imports: {bodyless:?}"
    );
}
