//! Focused producer/RC DATA controls, not runtime or ownership proofs.
use super::*;

#[test]
fn boxed_arithmetic_repeated_owned_object_and_reuse_keep_rc_gate() {
    let name = Name::from_string("boxedAliasData");
    let source = IRDecl {
        name: name.clone(),
        params: vec![(VarId(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    // A post-boxing producer proposal coalesces one actual UInt64 box and
    // reuses it in BOTH argument slots, then reads it again after the call.
    let input = IRDecl {
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::UInt64,
                arg: IRArg::Var(VarId(0)),
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::UInt64,
                value: IRExpr::Apply {
                    fn_id: FnId(Name::from_string("UInt64.add")),
                    args: vec![IRArg::Var(VarId(1)), IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::VDecl {
                    var: VarId(3),
                    ty: IRType::UInt64,
                    value: IRExpr::Unbox {
                        ty: IRType::UInt64,
                        arg: IRArg::Var(VarId(1)),
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
                }),
            }),
        },
        ..source.clone()
    };
    let root = std::env::var_os("CLEAN_BOXED_RC_TEST_OUTPUT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir().join(format!("clean-boxed-rc-{}", std::process::id()))
        });
    std::fs::create_dir(&root).unwrap();
    for (name, value) in [
        ("pre-boxing.json", serde_json::to_value(&source).unwrap()),
        ("input-boxed.json", serde_json::to_value(&input).unwrap()),
    ] {
        std::fs::write(root.join(name), serde_json::to_vec_pretty(&value).unwrap()).unwrap();
    }
    assert!(crate::rc_repair::verify_rc_linearity(std::slice::from_ref(&input)).is_err());
    let repaired = crate::rc_repair::rc_repair_boxed(
        std::slice::from_ref(&source),
        vec![input.clone()],
        &Default::default(),
    );
    std::fs::write(
        root.join("actual-repaired-boxed.json"),
        serde_json::to_vec_pretty(&repaired).unwrap(),
    )
    .unwrap();
    crate::rc_repair::verify_rc_linearity(&repaired).unwrap();
    crate::ir_checker::check_decls(&repaired).unwrap();
    let mut pending = vec![&repaired[0].body];
    let mut retains = 0;
    let mut releases = 0;
    while let Some(body) = pending.pop() {
        match body {
            IRBody::Inc { var, n, rest } => {
                if *var == VarId(1) {
                    retains += *n;
                }
                pending.push(rest);
            }
            IRBody::Dec { var, rest } => {
                if *var == VarId(1) {
                    releases += 1;
                }
                pending.push(rest);
            }
            IRBody::VDecl { rest, .. } => pending.push(rest),
            IRBody::Ret(_) => {}
            other => panic!("unexpected alias fixture node: {other:?}"),
        }
    }
    std::fs::write(
        root.join("actual-credits.json"),
        serde_json::to_vec_pretty(&serde_json::json!({"retains":retains,"releases":releases}))
            .unwrap(),
    )
    .unwrap();
    assert!(
        retains >= 2,
        "two owned argument slots plus the later alias need distinct credits"
    );
    assert_eq!(
        releases, 1,
        "the caller's later alias credit is retired once"
    );
    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let data = emit_trust_ir_with_supply_data(&repaired, &config).unwrap();
    for (name, value) in [
        (
            "actual-module.json",
            serde_json::to_value(&data.module).unwrap(),
        ),
        (
            "actual-supplies.json",
            serde_json::to_value(&data.native_arithmetic_supplies).unwrap(),
        ),
        (
            "actual-uses.json",
            serde_json::to_value(&data.native_arithmetic_uses).unwrap(),
        ),
    ] {
        std::fs::write(root.join(name), serde_json::to_vec_pretty(&value).unwrap()).unwrap();
    }
    assert_eq!(data.native_arithmetic_supplies.len(), 1);
    assert_eq!(data.native_arithmetic_uses.len(), 1);
    let use_ = &data.native_arithmetic_uses[0];
    assert!(matches!(
        use_.kind,
        NativeArithmeticUseKind::BoxedApply { .. }
    ));
    assert_eq!(
        use_.call_args[0], use_.call_args[1],
        "actual emitted call retains the alias"
    );
}
