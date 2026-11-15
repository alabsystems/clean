//! Typed identity controls for the real emitter and existing TV entrypoint.
//! RuntimeProbe identities come from the retained upstream fixture; these IR
//! bodies are diagnostic controls, not a claim to lower its partial body.

use super::*;
use clean_kernel::{BinderInfo, Expr, Level, Name};
use trust_ir::inst::Inst;

fn identity(name: Name, ty: IRType) -> IRDecl {
    IRDecl {
        name,
        params: vec![(VarId(0), ty.clone())],
        return_type: ty,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    }
}

fn caller(name: &str, callee: Name, ty: IRType) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params: vec![(VarId(0), ty.clone())],
        return_type: ty.clone(),
        body: IRBody::VDecl {
            var: VarId(1),
            ty,
            value: IRExpr::Apply {
                fn_id: FnId(callee),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    }
}

fn targets(module: &Module, index: usize) -> Vec<FuncId> {
    module.functions[index]
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter_map(|n| {
            if let Inst::Call { callee, .. } = &n.inst {
                Some(*callee)
            } else {
                None
            }
        })
        .collect()
}

#[test]
fn runtime_fixture_twins_keep_distinct_functions_and_cross_calls() {
    let hierarchical = Name::from_string("RuntimeProbe.count._unsafe_rec");
    let quoted = Name::anon().str("RuntimeProbe").str("count._unsafe_rec");
    assert_ne!(hierarchical, quoted);
    assert_eq!(hierarchical.to_string(), quoted.to_string());
    let module = emit_trust_ir(&[
        identity(hierarchical.clone(), IRType::UInt32),
        identity(quoted.clone(), IRType::UInt64),
        caller("hierarchicalCaller", hierarchical, IRType::UInt32),
        caller("quotedCaller", quoted, IRType::UInt64),
    ])
    .expect("both exact identities must be representable");
    assert_eq!(module.functions.len(), 4);
    assert_ne!(module.functions[0].name, module.functions[1].name);
    assert_eq!(module.functions[0].name, "RuntimeProbe.count._unsafe_rec");
    assert_eq!(targets(&module, 2), vec![module.functions[0].id]);
    assert_eq!(targets(&module, 3), vec![module.functions[1].id]);
    assert!(validate_module(&module).is_empty());
}

#[test]
fn numeric_string_and_quoted_unicode_twins_are_not_deduplicated() {
    let root = Name::anon().str("Probe");
    let names = [
        root.clone().num(7),
        root.clone().str("7"),
        root.str("07"),
        Name::from_string("α.β"),
        Name::anon().str("α.β"),
    ];
    let decls: Vec<_> = names
        .into_iter()
        .map(|n| identity(n, IRType::UInt32))
        .collect();
    let module = emit_trust_ir(&decls).expect("all typed names representable");
    let labels: HashSet<_> = module.functions.iter().map(|f| &f.name).collect();
    assert_eq!(labels.len(), 5);
}

#[test]
fn quoted_uint_native_lookalike_keeps_its_own_body_and_call() {
    let quoted = Name::anon().str("UInt32.add");
    let module = emit_trust_ir(&[
        identity(quoted.clone(), IRType::UInt32),
        caller("quotedArithmeticCaller", quoted, IRType::UInt32),
    ])
    .expect("quoted lookalike is an ordinary function, not a primitive");
    assert_eq!(module.functions.len(), 2);
    assert_eq!(targets(&module, 1), vec![module.functions[0].id]);
    assert!(!module.functions[1]
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .any(|n| matches!(n.inst, Inst::BinOp { .. })));
}

#[test]
fn quoted_nat_add_and_canonical_nat_add_keep_separate_call_targets() {
    let ordinary = Name::from_string("Nat.add");
    let quoted = Name::anon().str("Nat.add");
    let module = emit_trust_ir(&[
        identity(ordinary.clone(), IRType::UInt32),
        identity(quoted.clone(), IRType::UInt32),
        caller("ordinaryNatCaller", ordinary, IRType::UInt32),
        caller("quotedNatCaller", quoted, IRType::UInt32),
    ])
    .expect("Nat identities do not alias");
    assert_eq!(targets(&module, 2), vec![module.functions[0].id]);
    assert_eq!(targets(&module, 3), vec![module.functions[1].id]);
}

#[test]
fn ordinary_caller_cannot_certify_quoted_native_source_by_display_name() {
    // Same old display string, different actual source constant. The current
    // generic TV vocabulary cannot interpret this source identity faithfully.
    for levels in [vec![], vec![Level::param(Name::anon().str("quoted.level"))]] {
        let mut decl = caller(
            "ordinaryTvCaller",
            Name::from_string("UInt32.add"),
            IRType::UInt32,
        );
        if let IRBody::VDecl {
            value: IRExpr::Apply { args, .. },
            ..
        } = &mut decl.body
        {
            args.push(IRArg::Var(VarId(0)));
        }
        let mut module = emit_trust_ir(&[decl]).expect("canonical native emission");
        let source = Expr::lam(
            BinderInfo::Default,
            Expr::const_str("UInt32"),
            Expr::apps(
                Expr::const_(Name::anon().str("UInt32.add"), levels),
                [Expr::bvar(0), Expr::bvar(0)],
            ),
        );
        let report = crate::emit_trust_ir_tv::certify_backend_translation(
            &mut module,
            &[("ordinaryTvCaller".to_owned(), source)],
        );
        assert!(
            report.certified.is_empty(),
            "quoted source must not borrow canonical semantics"
        );
        assert_eq!(report.skipped.len() + report.refused.len(), 1);
    }
}

#[test]
fn ordinary_labels_and_calls_remain_unchanged() {
    let module = emit_trust_ir(&[
        identity(Name::from_string("ordinaryLeaf"), IRType::UInt32),
        caller(
            "ordinaryCaller",
            Name::from_string("ordinaryLeaf"),
            IRType::UInt32,
        ),
    ])
    .unwrap();
    assert_eq!(
        module
            .functions
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>(),
        ["ordinaryLeaf", "ordinaryCaller"]
    );
    assert_eq!(targets(&module, 1), vec![module.functions[0].id]);
}

#[test]
fn wire_encoding_roundtrips_and_reserves_its_entire_namespace() {
    use super::names::{decode_wire_name, wire_name, PREFIX};
    let root = Name::anon().str("Probe");
    let mut names = vec![
        Name::anon(),
        Name::anon().str(""),
        root.clone().num(0),
        root.clone().num(u64::MAX),
        root.clone().str("0"),
        root.clone().str("00"),
        Name::anon().str("α.β"),
        Name::from_string("α.β"),
        Name::anon().str(PREFIX),
        Name::anon().str(format!("{PREFIX}a")),
        Name::anon().str("a\0b"),
    ];
    for text in ["a", "b.c", "7", "", "_", "雪", PREFIX] {
        names.push(root.clone().str(text));
    }
    let labels: HashSet<_> = names.iter().map(wire_name).collect();
    assert_eq!(labels.len(), names.len());
    for name in names {
        let label = wire_name(&name);
        assert_eq!(decode_wire_name(&label), Some(name));
    }
    for malformed in [
        "",
        "as0z",
        "an00z",
        "an10000000000000000z",
        "asffz",
        "aXz",
        "as00",
    ] {
        assert!(decode_wire_name(&format!("{PREFIX}{malformed}")).is_none());
    }
}

#[test]
fn body_swap_changes_only_the_exact_function_and_wrong_signature_refuses() {
    let a = Name::from_string("Twin.leaf");
    let b = Name::anon().str("Twin.leaf");
    let base = vec![
        identity(a.clone(), IRType::UInt32),
        identity(b.clone(), IRType::UInt32),
        caller("toA", a, IRType::UInt32),
        caller("toB", b.clone(), IRType::UInt32),
    ];
    let original = emit_trust_ir(&base).unwrap();
    let mut changed = base.clone();
    changed[1].body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::UInt32,
        value: IRExpr::Lit(IRLiteral::UInt32(19)),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let changed = emit_trust_ir(&changed).unwrap();
    assert_eq!(original.functions[0], changed.functions[0]);
    assert_ne!(original.functions[1], changed.functions[1]);
    assert_eq!(targets(&original, 2), targets(&changed, 2));
    assert_eq!(targets(&original, 3), targets(&changed, 3));
    let bytes =
        trust_ir::binary::serialize_module(&changed).expect("serialize_module: test fixture");
    let decoded = trust_ir::binary::deserialize_module(&bytes).unwrap();
    assert_eq!(decoded.functions, changed.functions);
    let malformed = [
        identity(b.clone(), IRType::UInt64),
        caller("wrongCarrier", b, IRType::UInt32),
    ];
    assert!(emit_trust_ir(&malformed).is_err());
    assert!(emit_trust_ir(&[base[0].clone(), base[0].clone()]).is_err());
}

#[test]
fn dropped_extern_twins_keep_distinct_mangled_targets_and_ordinary_order() {
    let a = Name::from_string("Extern.leaf");
    let b = Name::anon().str("Extern.leaf");
    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..Default::default()
    };
    let module = emit_trust_ir_with_config(
        &[
            caller("first", a.clone(), IRType::Object),
            caller("second", b.clone(), IRType::Object),
        ],
        &config,
    )
    .unwrap();
    let aid = module
        .functions
        .iter()
        .find(|f| f.name == crate::mangle::mangle_name(&a))
        .unwrap()
        .id;
    let bid = module
        .functions
        .iter()
        .find(|f| f.name == crate::mangle::mangle_name(&b))
        .unwrap()
        .id;
    assert_ne!(aid, bid);
    for (label, target) in [("first", aid), ("second", bid)] {
        let index = module
            .functions
            .iter()
            .position(|f| f.name == label)
            .unwrap();
        assert_eq!(targets(&module, index), vec![target]);
    }
    let ordinary = emit_trust_ir_with_config(
        &[
            caller("zCaller", Name::from_string("zLeaf"), IRType::Object),
            caller("aCaller", Name::from_string("aLeaf"), IRType::Object),
        ],
        &config,
    )
    .unwrap();
    let a = ordinary
        .functions
        .iter()
        .position(|f| f.name == "l_aLeaf")
        .unwrap();
    let z = ordinary
        .functions
        .iter()
        .position(|f| f.name == "l_zLeaf")
        .unwrap();
    assert!(a < z, "historical lexical extern order is preserved");
}

#[test]
fn quoted_decision_name_does_not_override_its_body() {
    let declaration = |name| IRDecl {
        name,
        params: vec![(VarId(0), IRType::UInt64), (VarId(1), IRType::UInt64)],
        return_type: IRType::Bool,
        body: IRBody::VDecl {
            var: VarId(2),
            ty: IRType::Bool,
            value: IRExpr::Lit(IRLiteral::Bool(false)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        },
    };
    let module = emit_trust_ir(&[
        declaration(Name::from_string("UInt64.decEq")),
        declaration(Name::anon().str("UInt64.decEq")),
    ])
    .unwrap();
    let has_cmp = |index: usize| {
        module.functions[index]
            .instructions()
            .any(|n| matches!(n.inst, Inst::ICmp { .. }))
    };
    assert!(has_cmp(0));
    assert!(!has_cmp(1));
}

#[test]
fn legacy_tv_guard_covers_levels_types_and_projection_owners() {
    use super::names::legacy_source_identity_supported as supported;
    let hidden = Name::anon().str("Hidden.name");
    assert!(!supported(&Expr::const_(
        Name::from_string("ordinary"),
        vec![Level::param(hidden.clone())]
    )));
    assert!(!supported(&Expr::lam(
        BinderInfo::Default,
        Expr::const_(hidden.clone(), vec![]),
        Expr::bvar(0)
    )));
    assert!(!supported(&Expr::proj(hidden, 0, Expr::bvar(0))));
    assert!(supported(&Expr::const_(
        Name::from_string("ordinary"),
        vec![Level::param(Name::from_string("u"))]
    )));
}

#[test]
fn checked_source_pipeline_pairs_escaped_leaf_with_its_original_expr() {
    use crate::pass_manager::{compile_lcnf_to_trust_ir_with_report, PipelineConfig};
    use clean_kernel::env::{Declaration, Environment};
    let mut env = Environment::try_with_prelude().unwrap();
    let name = Name::anon().str("actual.identity");
    let ty = Expr::const_str("UInt32");
    let value = Expr::lam(BinderInfo::Default, ty.clone(), Expr::bvar(0));
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::arrow(ty.clone(), ty),
        value,
        is_reducible: true,
    })
    .unwrap();
    let decl = crate::to_lcnf::constant_to_decl(&env, env.get_const(&name).unwrap())
        .unwrap()
        .unwrap();
    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..Default::default()
    };
    let (module, report) =
        compile_lcnf_to_trust_ir_with_report(&[decl], &env, &PipelineConfig::default(), &config)
            .unwrap();
    let label = wire_name(&name);
    assert!(module.functions.iter().any(|f| f.name == label));
    assert!(
        report.certified.contains(&label),
        "exact original/leaf pairing: {report:?}"
    );
    assert!(!report.certified.contains(&name.to_string()));
}

/// v41 `display_path`: an escaped typed name's link symbol is the
/// `__clean_typed_v1_…` wire encoding, so its readable spelling rides in
/// `display_path`; an ordinary name's symbol IS its readable spelling, so it
/// carries none. Display twins may share a display path — the symbol is what
/// keeps their bodies and call targets apart.
#[test]
fn escaped_wire_symbols_carry_the_readable_name_in_display_path() {
    let hierarchical = Name::from_string("RuntimeProbe.count._unsafe_rec");
    let quoted = Name::anon().str("RuntimeProbe").str("count._unsafe_rec");
    let module = emit_trust_ir(&[
        identity(hierarchical.clone(), IRType::UInt32),
        identity(quoted.clone(), IRType::UInt64),
    ])
    .unwrap();
    let [ordinary, escaped] = module.functions.as_slice() else {
        panic!("two functions expected, got {}", module.functions.len());
    };
    assert_eq!(ordinary.name, hierarchical.to_string());
    assert_eq!(ordinary.display_path, None);
    assert!(escaped.name.starts_with(names::PREFIX));
    assert_eq!(
        escaped.display_path.as_deref(),
        Some("RuntimeProbe.count._unsafe_rec")
    );
    assert_eq!(
        escaped.display_path.as_deref(),
        Some(ordinary.name.as_str())
    );
    assert!(validate_module(&module).is_empty());
}

/// Codegen license through the REAL pipeline (`compile_lcnf_to_trust_ir_with_report`,
/// ExternCalls, TV on by default): the one kernel-certified body is
/// `Gated { "clean-kernel-tv" }`, its escaped symbol carries the readable
/// name in `display_path`, every runtime import (bodyless) makes no claim,
/// and any other emitted body stays `Ungated`.
#[test]
fn checked_source_pipeline_licenses_exactly_the_certified_body() {
    use crate::pass_manager::{compile_lcnf_to_trust_ir_with_report, PipelineConfig};
    use clean_kernel::env::{Declaration, Environment};
    use trust_ir::BodyGate;
    let mut env = Environment::try_with_prelude().unwrap();
    let name = Name::anon().str("actual.identity");
    let ty = Expr::const_str("UInt32");
    let value = Expr::lam(BinderInfo::Default, ty.clone(), Expr::bvar(0));
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::arrow(ty.clone(), ty),
        value,
        is_reducible: true,
    })
    .unwrap();
    let decl = crate::to_lcnf::constant_to_decl(&env, env.get_const(&name).unwrap())
        .unwrap()
        .unwrap();
    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..Default::default()
    };
    let (module, report) =
        compile_lcnf_to_trust_ir_with_report(&[decl], &env, &PipelineConfig::default(), &config)
            .unwrap();
    let label = wire_name(&name);
    assert_eq!(report.certified, vec![label.clone()], "{report:?}");
    let mut gated = 0;
    for f in &module.functions {
        if f.name == label {
            gated += 1;
            assert!(f.body_gate.is_some());
            assert_eq!(
                f.body_gate,
                crate::emit_trust_ir_tv::kernel_tv_gate(&module, f.id),
                "the minted license, with evidence"
            );
            assert_eq!(f.display_path.as_deref(), Some("actual.identity"));
        } else if f.is_declaration() {
            assert_eq!(f.body_gate, None, "`{}` is a bodyless import", f.name);
        } else {
            assert_eq!(f.body_gate, Some(BodyGate::Ungated), "`{}`", f.name);
        }
    }
    assert_eq!(gated, 1);
    // `certified` and `Gated` are the same set, by construction.
    let licensed: Vec<&str> = module
        .functions
        .iter()
        .filter(|f| matches!(f.body_gate, Some(BodyGate::Gated { .. })))
        .map(|f| f.name.as_str())
        .collect();
    assert_eq!(licensed, [label.as_str()]);
}

#[test]
fn resolved_escaped_callee_cannot_borrow_an_ordinary_source_certificate() {
    use crate::emit_trust_ir_tv::certify_backend_translation;
    let escaped = Name::anon().str("Escaped.leaf");
    let mut module = emit_trust_ir(&[
        identity(escaped.clone(), IRType::UInt32),
        caller("ordinaryCaller", escaped.clone(), IRType::UInt32),
    ])
    .unwrap();
    let leaf = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("UInt32"),
        Expr::bvar(0),
    );
    // Deliberately supply an ordinary-spelled source twin. The emitted callee
    // row itself must prevent legacy composition even if source spelling lies.
    let source = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("UInt32"),
        Expr::app(Expr::const_str("Escaped.leaf"), Expr::bvar(0)),
    );
    let label = wire_name(&escaped);
    let report = certify_backend_translation(
        &mut module,
        &[(label.clone(), leaf), ("ordinaryCaller".into(), source)],
    );
    assert!(report.certified.contains(&label));
    assert!(!report.certified.contains(&"ordinaryCaller".to_owned()));
    assert!(report.skipped.iter().any(|(n, _)| n == "ordinaryCaller"));
}

#[test]
fn partial_application_uses_exact_twins_with_independent_arities() {
    use trust_ir::constant::Constant;
    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    for pair in [
        [Name::from_string("Pap.leaf"), Name::anon().str("Pap.leaf")],
        [
            Name::anon().str("Pap").num(7),
            Name::anon().str("Pap").str("7"),
        ],
    ] {
        for in_slice in [true, false] {
            let mut decls = Vec::new();
            if in_slice {
                for (i, name) in pair.iter().enumerate() {
                    decls.push(IRDecl {
                        name: name.clone(),
                        params: (0..i + 2)
                            .map(|n| (VarId(n as u32), IRType::Object))
                            .collect(),
                        return_type: IRType::Object,
                        body: IRBody::Ret(IRArg::Var(VarId(0))),
                    });
                }
            }
            for (i, name) in pair.iter().enumerate() {
                decls.push(IRDecl {
                    name: Name::from_string(&format!("make{i}")),
                    params: vec![(VarId(0), IRType::Object)],
                    return_type: IRType::Object,
                    body: IRBody::VDecl {
                        var: VarId(1),
                        ty: IRType::Object,
                        value: IRExpr::PartialApply {
                            fn_id: FnId(name.clone()),
                            arity: (i + 2) as u16,
                            args: vec![IRArg::Var(VarId(0))],
                        },
                        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
                    },
                });
            }
            let module = emit_trust_ir_with_config(&decls, &config).unwrap();
            let mut targets = Vec::new();
            for (i, name) in pair.iter().enumerate() {
                let label = if in_slice {
                    wire_name(name)
                } else {
                    crate::mangle::mangle_name(name)
                };
                let target = module.functions.iter().find(|f| f.name == label).unwrap();
                let maker = module
                    .functions
                    .iter()
                    .find(|f| f.name == format!("make{i}"))
                    .unwrap();
                let addresses: Vec<_> = maker
                    .blocks
                    .iter()
                    .flat_map(|b| &b.body)
                    .filter_map(|n| {
                        if let Inst::Const {
                            value: Constant::FnDef(id),
                            ..
                        } = &n.inst
                        {
                            Some(*id)
                        } else {
                            None
                        }
                    })
                    .collect();
                assert_eq!(addresses, [target.id]);
                targets.push(target.id);
            }
            assert_ne!(targets[0], targets[1]);
            assert!(validate_module(&module).is_empty());
        }
    }
}
