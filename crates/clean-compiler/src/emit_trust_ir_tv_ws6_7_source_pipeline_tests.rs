// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real checked source through the canonical bound pipeline, rather than the
//! manual minter or the Rust ABI's separate self-check path.

use super::*;
use crate::pass_manager::{compile_lcnf_to_trust_ir_with_report, PipelineConfig};
use crate::rc_repair::e2e_support::elaborated_env_with;
use clean_kernel::{KernelInstanceInfo, Level, DEFAULT_INSTANCE_PRIORITY};

/// Optional DATA handoff to the separately built IR consumer. These files carry
/// no authority: that consumer supplies the original source name/environment,
/// reconstructs its own goal from the complete module, and rechecks the proof.
fn export_actual_source_equation_fixture(
    label: &str,
    module: &Module,
    env: &Environment,
    equation: &clean_reflect::source_equation::CheckedSourceEquation,
    definitions: &[&str],
) {
    let Some(root) = std::env::var_os("CLEAN_SOURCE_EQUATION_EXPORT_DIR") else {
        return;
    };
    let root = std::path::PathBuf::from(root);
    assert!(
        root.is_absolute(),
        "fixture export needs an explicit absolute directory"
    );
    std::fs::create_dir_all(&root).expect("create export root");
    let dir = root.join(label);
    std::fs::create_dir(&dir).expect("each fixture output must be fresh");
    let bytes = trust_ir::binary::serialize_module(module).expect("encode actual complete module");
    assert_eq!(
        trust_ir::binary::deserialize_module(&bytes).expect("round-trip complete module"),
        *module
    );
    std::fs::write(dir.join("module.bin"), bytes).expect("write complete module data");
    let write_expr = |filename: &str, expr: &Expr| {
        let bytes = trust_ir::proof::encode_clean_expr_v1(expr).expect("canonical Expr codec");
        assert_eq!(
            trust_ir::proof::decode_clean_expr_v1(&bytes).expect("round-trip Expr data"),
            *expr
        );
        std::fs::write(dir.join(filename), bytes).expect("write exact Expr data");
    };
    let mut metadata = String::from(
        "DATA ONLY: external consumer rederives the goal and audits every declaration.\n",
    );
    for (i, name) in definitions.iter().enumerate() {
        let info = env
            .get_const(&KName::from_string(name))
            .expect("actual checked source definition");
        assert_eq!(info.kind, clean_kernel::ConstantKind::Definition);
        assert!(info.level_params.is_empty());
        write_expr(
            &format!("definition-{i}.name.bin"),
            &Expr::const_(info.name.clone(), vec![]),
        );
        write_expr(&format!("definition-{i}.type.bin"), &info.type_);
        write_expr(
            &format!("definition-{i}.value.bin"),
            info.value.as_ref().expect("definition value"),
        );
        metadata.push_str(&format!(
            "definition-{i}: name={name} is_reducible={} reducibility={:?}\n",
            info.is_reducible, info.reducibility
        ));
    }
    let Declaration::Theorem {
        name,
        level_params,
        type_,
        value,
    } = equation.declaration()
    else {
        panic!("only exact checked Theorem data can be exported");
    };
    assert!(level_params.is_empty());
    write_expr("theorem.name.bin", &Expr::const_(name.clone(), vec![]));
    write_expr("theorem.type.bin", type_);
    write_expr("theorem.value.bin", value);
    std::fs::write(
        dir.join("source-closure-digest.bin"),
        equation.source_closure_digest(),
    )
    .expect("source closure digest");
    std::fs::write(
        dir.join("equation-closure-digest.bin"),
        equation.equation_closure_digest(),
    )
    .expect("theorem closure digest");
    metadata.push_str(&format!("source={}\n", equation.source()));
    std::fs::write(dir.join("DATA.txt"), metadata).expect("write diagnostic declaration metadata");
}

#[test]
fn ws6_7_actual_fnv128_source_carrier_pipeline() {
    use trust_ir::interpret::{InterpretValue, Interpreter};
    let definitions = ["trust_cg_fnv128_step_lo", "trust_cg_fnv128_step_hi"];
    let env = elaborated_env_with(include_str!("testdata/fnv128_step.lean"));
    let sources: Vec<_> = definitions.iter().map(|s| KName::from_string(s)).collect();
    let target = trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".to_string(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    };
    let output = crate::rust_abi::compile_rust_abi(
        &env,
        &sources,
        &[],
        &PipelineConfig::default(),
        "actual_fnv128",
        &target,
    )
    .unwrap_or_else(|error| {
        let decls: Vec<_> = sources
            .iter()
            .map(|source| {
                crate::to_lcnf::constant_to_decl(&env, env.get_const(source).unwrap())
                    .unwrap()
                    .unwrap()
            })
            .collect();
        let artifacts = crate::pass_manager::compile_lcnf_decls_at_rust_abi(
            &decls,
            &env,
            &PipelineConfig::default(),
            true,
        )
        .expect("diagnostic shared compiler artifacts");
        panic!(
            "complete actual FNV source refused: {error:?}; shared IR: {:#?}",
            artifacts.boxed_ir_decls
        );
    });
    let mut module = output.module;
    assert_eq!(
        module.functions.len(),
        2,
        "both complete source functions, no hidden adapters"
    );
    let originals: Vec<_> = definitions
        .iter()
        .zip(&sources)
        .map(|(s, name)| {
            (
                s.to_string(),
                env.get_const(name).unwrap().value.clone().unwrap(),
            )
        })
        .collect();
    let report = certify_backend_translation_in_environment(&mut module, &originals, &env);
    assert_eq!(
        report.certified.len(),
        2,
        "certified={:?}; skipped={:?}; refused={:?}",
        report.certified,
        report.skipped,
        report.refused
    );
    assert!(
        report.skipped.is_empty() && report.refused.is_empty(),
        "{report:?}"
    );
    assert_eq!(
        report.source_equations.len(),
        2,
        "both original source equations required"
    );
    assert!(
        validate_module_for_codegen(&module).is_empty(),
        "independent complete module reader"
    );
    for (label, source) in definitions.iter().zip(&sources) {
        let function = module.functions.iter().find(|f| f.name == *label).unwrap();
        let denotation = denote_function(&module, function).expect("actual complete FNV dataflow");
        let equation = clean_reflect::source_equation::check_uint_source_equation(
            &env,
            source,
            &denotation,
            source.clone().str("checked"),
        )
        .expect("complete original FNV source equals actual emitted model");
        export_actual_source_equation_fixture(label, &module, &env, &equation, &definitions);
        let mut wrong = module.clone();
        let body = wrong
            .functions
            .iter_mut()
            .find(|f| f.id == function.id)
            .unwrap();
        let node = body
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.body)
            .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Xor, .. }))
            .unwrap();
        let Inst::BinOp { op, .. } = &mut node.inst else {
            unreachable!()
        };
        *op = BinOp::Or;
        let changed = wrong
            .functions
            .iter()
            .find(|f| f.id == function.id)
            .unwrap();
        let wrong_denotation = denote_function(&wrong, changed).expect("in-fragment FNV mutation");
        clean_reflect::source_equation::check_uint_source_equation(
            &env,
            source,
            &wrong_denotation,
            source.clone().str("wrong"),
        )
        .expect_err("original source independently refuses the changed FNV implementation");
        assert!(
            !validate_module_for_codegen(&wrong).is_empty(),
            "changed FNV body loses its license"
        );
    }
    let lo_func = module
        .functions
        .iter()
        .find(|f| f.name == definitions[0])
        .unwrap();
    let hi_func = module
        .functions
        .iter()
        .find(|f| f.name == definitions[1])
        .unwrap();
    let arg = |x: u64| InterpretValue::int(Ty::U64, i128::from(x)).unwrap();
    // Independent finite oracle, not a universal proof of combined FNV math.
    for hi in [0, 1, u64::MAX, 0x0123_4567_89ab_cdef] {
        for lo in [
            0,
            1,
            u64::MAX,
            0xffff_ffff,
            0x1_0000_0000,
            0x8000_0000_0000_0000,
        ] {
            for byte in [0, 1, 127, 128, 255, u64::MAX] {
                let low = Interpreter::with_module(&module)
                    .execute_func(lo_func.id, vec![arg(lo), arg(byte)])
                    .expect("actual low source executes")
                    .returns[0]
                    .as_int()
                    .unwrap()
                    .as_unsigned();
                let high = Interpreter::with_module(&module)
                    .execute_func(hi_func.id, vec![arg(hi), arg(lo), arg(byte)])
                    .expect("actual high source executes")
                    .returns[0]
                    .as_int()
                    .unwrap()
                    .as_unsigned();
                let expected = (((u128::from(hi) << 64) | u128::from(lo)) ^ u128::from(byte))
                    .wrapping_mul((1u128 << 88) + 315);
                assert_eq!((high << 64) | low, expected);
            }
        }
    }
}

#[test]
fn ws6_7_actual_shift_source_carrier_all_uint_widths() {
    use trust_ir::interpret::{InterpretValue, Interpreter};
    for width in [8u32, 16, 32, 64] {
        for (direction, spelling, operation) in
            [("Left", "<<<", BinOp::Shl), ("Right", ">>>", BinOp::LShr)]
        {
            let label = format!("boundActualShift{direction}{width}");
            let env = elaborated_env_with(&format!(
                "def {label} (a amount : UInt{width}) : UInt{width} := a {spelling} amount\n"
            ));
            let source = KName::from_string(&label);
            let target = trust_ir::TargetInfo {
                triple: "aarch64-apple-darwin".to_string(),
                pointer_size: 8,
                endianness: trust_ir::Endianness::Little,
                abi: None,
                struct_passing: trust_ir::StructPassingPolicy::Unclassified,
            };
            let output = crate::rust_abi::compile_rust_abi(
                &env,
                std::slice::from_ref(&source),
                &[],
                &PipelineConfig::default(),
                &label,
                &target,
            )
            .expect("actual source through shared carrier compiler");
            let mut module = output.module;
            assert_eq!(
                module.functions.len(),
                1,
                "complete module has no hidden adapter"
            );
            let originals = vec![(
                label.clone(),
                env.get_const(&source).unwrap().value.clone().unwrap(),
            )];
            let report = certify_backend_translation_in_environment(&mut module, &originals, &env);
            assert_eq!(report.certified, vec![label.clone()], "{report:?}");
            assert!(
                report.skipped.is_empty() && report.refused.is_empty(),
                "{report:?}"
            );
            assert_eq!(
                report.source_equations.len(),
                1,
                "original source binding required"
            );
            assert!(
                validate_module_for_codegen(&module).is_empty(),
                "independent complete-module reader"
            );
            let function = &module.functions[0];
            let denotation = denote_function(&module, function).expect("bounded shift dataflow");
            let equation = clean_reflect::source_equation::check_uint_source_equation(
                &env,
                &source,
                &denotation,
                source.clone().str("checked"),
            )
            .expect("original checked UInt shift equals actual emitted denotation");
            export_actual_source_equation_fixture(&label, &module, &env, &equation, &[&label]);
            let ty = module.func_types[function.ty.as_usize()].params[0].clone();
            let mask = (1u128 << width) - 1;
            for a in [0, 1, mask - 1, mask] {
                for amount in [
                    0,
                    1,
                    u128::from(width - 1),
                    u128::from(width),
                    u128::from(width + 1),
                    mask,
                ] {
                    let arg = |x: u128| {
                        InterpretValue::int(ty.clone(), i128::try_from(x).unwrap()).unwrap()
                    };
                    let result = Interpreter::with_module(&module)
                        .execute_func(function.id, vec![arg(a), arg(amount)])
                        .expect("actual module executes even over-width Lean amounts");
                    let k = u32::try_from(amount % u128::from(width)).unwrap();
                    let expected = if operation == BinOp::Shl {
                        (a << k) & mask
                    } else {
                        a >> k
                    };
                    assert_eq!(result.returns[0].as_int().unwrap().as_unsigned(), expected);
                }
            }
            // A bounded shift in the wrong direction is still defined IR,
            // but its original-source equation must fail independently.
            let mut wrong = module.clone();
            let node = wrong.functions[0]
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.body)
                .find(|n| matches!(n.inst, Inst::BinOp { op, .. } if op == operation))
                .unwrap();
            let Inst::BinOp { op, .. } = &mut node.inst else {
                unreachable!()
            };
            *op = if operation == BinOp::Shl {
                BinOp::LShr
            } else {
                BinOp::Shl
            };
            let wrong_denotation = denote_function(&wrong, &wrong.functions[0])
                .expect("wrong direction still has a defined bounded denotation");
            clean_reflect::source_equation::check_uint_source_equation(
                &env,
                &source,
                &wrong_denotation,
                source.clone().str("wrongDirection"),
            )
            .expect_err("original source independently rejects a changed shift direction");
            assert!(
                !validate_module_for_codegen(&wrong).is_empty(),
                "changed body cannot keep its license"
            );

            let mut raw = module.clone();
            let body = &mut raw.functions[0];
            let original_amount = body
                .blocks
                .iter()
                .flat_map(|b| &b.body)
                .find_map(|n| {
                    if let Inst::BinOp {
                        op: BinOp::URem,
                        lhs,
                        ..
                    } = n.inst
                    {
                        Some(lhs)
                    } else {
                        None
                    }
                })
                .expect("modulo amount instruction");
            let shift = body
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.body)
                .find(|n| matches!(n.inst, Inst::BinOp { op, .. } if op == operation))
                .expect("actual shift instruction");
            let Inst::BinOp { rhs, .. } = &mut shift.inst else {
                unreachable!()
            };
            *rhs = original_amount;
            assert!(
                !validate_module_for_codegen(&raw).is_empty(),
                "unbounded shift must lose admission"
            );
            assert!(
                denote_function(&raw, &raw.functions[0]).is_err(),
                "producer also refuses raw unbounded shift"
            );
        }
    }
}

#[test]
fn ws6_7_actual_xor_source_pipeline_all_uint_widths() {
    use trust_ir::interpret::{InterpretValue, Interpreter};
    for width in [8u32, 16, 32, 64] {
        let label = format!("boundActualXor{width}");
        let factor = if width == 64 { 315u128 } else { 3 };
        let source_text = format!(
            "def {label} (lo byte : UInt{width}) : UInt{width} := (lo ^^^ byte) * {factor}\n"
        );
        let env = elaborated_env_with(&source_text);
        let source = KName::from_string(&label);
        let decl = crate::to_lcnf::constant_to_decl(&env, env.get_const(&source).unwrap())
            .expect("checked Lean source lowers")
            .expect("computational source");
        let cfg = crate::emit_trust_ir::TrustIrConfig {
            runtime_lowering: crate::emit_trust_ir::RuntimeLowering::ExternCalls,
            certify_translation: true,
            ..Default::default()
        };
        let (module, report) =
            compile_lcnf_to_trust_ir_with_report(&[decl], &env, &PipelineConfig::default(), &cfg)
                .expect("shared actual-source XOR pipeline");
        assert_eq!(report.certified, vec![label.clone()], "{report:?}");
        assert!(
            report.skipped.is_empty() && report.refused.is_empty(),
            "{report:?}"
        );
        assert_eq!(
            report.source_equations.len(),
            1,
            "original source equation is required"
        );
        let errors = validate_module_for_codegen(&module);
        let boxed_name = format!("l_{label}___boxed");
        assert!(
            matches!(errors.as_slice(),
            [ValidationError::UngatedBodyForCodegen { name, .. }] if name == &boxed_name),
            "the general Lean ABI's unproved boxed adapter must remain refused: {errors:?}"
        );
        // Rust callers use the actual shared carrier-ABI profile. Its output
        // is deliberately claim-free; the existing minter must bind the
        // original checked source before the independent reader admits it.
        let target = trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".to_string(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        };
        let output = crate::rust_abi::compile_rust_abi(
            &env,
            std::slice::from_ref(&source),
            &[],
            &PipelineConfig::default(),
            &label,
            &target,
        )
        .expect("actual Rust carrier ABI source compiler");
        let mut module = output.module;
        assert_eq!(
            module.functions.len(),
            1,
            "no hidden or removed adapter body"
        );
        let originals = vec![(
            label.clone(),
            env.get_const(&source).unwrap().value.clone().unwrap(),
        )];
        let report = certify_backend_translation_in_environment(&mut module, &originals, &env);
        assert_eq!(report.certified, vec![label.clone()], "{report:?}");
        assert!(
            report.skipped.is_empty() && report.refused.is_empty(),
            "{report:?}"
        );
        assert_eq!(
            report.source_equations.len(),
            1,
            "the carrier output also needs its source equation"
        );
        let errors = validate_module_for_codegen(&module);
        assert!(
            errors.is_empty(),
            "independent reader of complete carrier module: {errors:?}"
        );
        let function = module.functions.iter().find(|f| f.name == label).unwrap();
        assert!(function
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Xor, .. })));
        let denotation = denote_function(&module, function).expect("actual emitted XOR dataflow");
        let equation = clean_reflect::source_equation::check_uint_source_equation(
            &env,
            &source,
            &denotation,
            source.clone().str("checked"),
        )
        .expect("original UInt source equals actual emitted denotation");
        export_actual_source_equation_fixture(&label, &module, &env, &equation, &[&label]);
        let ty = module.func_types[function.ty.as_usize()].params[0].clone();
        let mask = (1u128 << width) - 1;
        for (a, b) in [
            (0, 0),
            (mask, 0),
            (mask, mask),
            (mask - 1, 1),
            (0xaa & mask, 0x55 & mask),
            (1, 2),
        ] {
            let arg =
                |v: u128| InterpretValue::int(ty.clone(), i128::try_from(v).unwrap()).unwrap();
            let result = Interpreter::with_module(&module)
                .execute_func(function.id, vec![arg(a), arg(b)])
                .expect("actual module executes");
            assert_eq!(
                result.returns[0].as_int().unwrap().as_unsigned(),
                ((a ^ b) * factor) & mask
            );
        }
        let mut wrong = module.clone();
        let body = wrong
            .functions
            .iter_mut()
            .find(|f| f.id == function.id)
            .unwrap();
        let node = body
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.body)
            .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Xor, .. }))
            .unwrap();
        let Inst::BinOp { op, .. } = &mut node.inst else {
            unreachable!()
        };
        *op = BinOp::Or;
        assert!(
            !validate_module_for_codegen(&wrong).is_empty(),
            "changed emitter cannot keep its license"
        );
        let changed = wrong
            .functions
            .iter()
            .find(|f| f.id == function.id)
            .unwrap();
        let wrong_denotation =
            denote_function(&wrong, changed).expect("wrong but in-fragment dataflow");
        clean_reflect::source_equation::check_uint_source_equation(
            &env,
            &source,
            &wrong_denotation,
            source.clone().str("wrong"),
        )
        .expect_err("original-source equation independently rejects the changed emitted operation");
    }
}

fn add_checked_sub_dictionary_source(env: &mut Environment) {
    let u = Expr::const_str("UInt32");
    let levels = vec![Level::zero(); 3];
    let dictionary = KName::from_string("boundSubDictionary");
    env.add_decl(Declaration::Definition {
        name: dictionary.clone(),
        level_params: vec![],
        type_: Expr::apps(
            Expr::const_(KName::from_string("HAdd"), levels.clone()),
            [u.clone(), u.clone(), u.clone()],
        ),
        value: Expr::apps(
            Expr::const_(KName::from_string("HAdd.mk"), levels.clone()),
            [
                u.clone(),
                u.clone(),
                u.clone(),
                Expr::const_str("UInt32.sub"),
            ],
        ),
        is_reducible: true,
    })
    .expect("a subtraction field is a valid kernel-checked HAdd dictionary");
    env.register_instance(KernelInstanceInfo {
        name: dictionary,
        class_name: KName::from_string("HAdd"),
        priority: DEFAULT_INSTANCE_PRIORITY,
        type_: None,
        value: None,
    });
    env.add_decl(Declaration::Definition {
        name: KName::from_string("boundField"),
        level_params: vec![],
        type_: Expr::arrow(u.clone(), Expr::arrow(u.clone(), u.clone())),
        value: Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::lam(
                BinderInfo::Default,
                u.clone(),
                Expr::apps(
                    Expr::const_(KName::from_string("HAdd.hAdd"), levels),
                    [
                        u.clone(),
                        u.clone(),
                        u,
                        Expr::const_str("boundSubDictionary"),
                        Expr::bvar(1),
                        Expr::bvar(0),
                    ],
                ),
            ),
        ),
        is_reducible: true,
    })
    .expect("the custom-dictionary source itself kernel-checks");
}

#[test]
fn ws6_7_pipeline_mints_bound_mask_and_actual_dictionary_field_from_checked_source() {
    let mut env = elaborated_env_with(
        "def boundMask (a b : UInt32) : UInt32 := UInt32.lor (UInt32.land a b) 1\n",
    );
    add_checked_sub_dictionary_source(&mut env);
    let pipeline = PipelineConfig::default();
    let cfg = crate::emit_trust_ir::TrustIrConfig {
        module_name: "ws6_7_source_environment".to_string(),
        runtime_lowering: crate::emit_trust_ir::RuntimeLowering::ExternCalls,
        certify_translation: true,
        ..crate::emit_trust_ir::TrustIrConfig::default()
    };
    assert!(cfg.bind_certificates, "exercise the normal bound pipeline");
    for (name, expected_ops) in [
        ("boundMask", &[BinOp::And, BinOp::Or][..]),
        ("boundField", &[BinOp::Sub][..]),
    ] {
        let source_name = KName::from_string(name);
        let decl = crate::to_lcnf::constant_to_decl(
            &env,
            env.get_const(&source_name)
                .expect("checked source declaration"),
        )
        .expect("checked source lowers through the canonical LCNF frontend")
        .expect("the source is computational");
        let (module, report) = compile_lcnf_to_trust_ir_with_report(
            std::slice::from_ref(&decl),
            &env,
            &pipeline,
            &cfg,
        )
        .unwrap_or_else(|error| panic!("{name}: actual bound pipeline: {error}"));
        assert_eq!(
            report.certified,
            vec![name.to_string()],
            "{name}: {report:?}"
        );
        assert!(report.skipped.is_empty(), "{name}: no skip: {report:?}");
        assert!(report.refused.is_empty(), "{name}: {report:?}");
        let function = module.functions.iter().find(|f| f.name == name).unwrap();
        let ops: Vec<_> = function
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter_map(|node| match &node.inst {
                Inst::BinOp { op, .. } => Some(*op),
                _ => None,
            })
            .collect();
        for op in expected_ops {
            assert!(ops.contains(op), "{name}: must emit {op:?}, got {ops:?}");
        }
        if name == "boundField" {
            assert!(
                !ops.contains(&BinOp::Add),
                "HAdd's name cannot replace its Sub field"
            );
        }
        let obligation = tv_obligation(&module, name);
        let binding = module
            .proof_certificates
            .iter()
            .filter(|c| c.obligation == obligation.id)
            .find_map(|c| c.evidence.clean_cic_kernel_recheck())
            .and_then(|r| r.binding.as_deref())
            .expect("the actual pipeline minted a bound kernel certificate");
        let identity = binding.source.as_ref().expect("checked source identity");
        assert_eq!(identity.decl, name);
        assert_eq!(
            identity.closure_digest.bytes,
            env.closure_digest(&source_name).unwrap()
        );
        let expected_gate = kernel_tv_gate(&module, function.id)
            .expect("the actual certificate has one evidenced body gate");
        assert_eq!(function.body_gate, Some(expected_gate));
        assert_eq!(
            validate_module(&module),
            Vec::new(),
            "{name}: independent recheck"
        );
        assert_eq!(
            validate_module_with_config(
                &module,
                &ValidationConfig::pinned()
                    .with_bound_certificates(true)
                    .with_gate_evidence(true),
            )
            .into_errors(),
            Vec::new(),
            "{name}: independently checked source certificate, binding and gate evidence",
        );
        // A source body's TV does not prove the generated boxed entry's
        // marshaling. Keep that body in the denominator and require strict
        // whole-module codegen to refuse it, as the existing real-source
        // pipeline control does. Never inherit a callee license onto it.
        let bodies: Vec<_> = module
            .functions
            .iter()
            .filter(|f| !f.is_declaration())
            .collect();
        assert_eq!(
            bodies.len(),
            2,
            "the source and its actual generated boxed entry"
        );
        let helper = bodies.into_iter().find(|f| f.id != function.id).unwrap();
        assert_eq!(helper.name, format!("l_{name}___boxed"));
        let before_entry_check = module.clone();
        let entry =
            clean_reflect::boxed_entry::check_uint32_boxed_entry(&module, helper.id, function.id)
                .expect("the actual emitted helper follows the checked U32 choreography");
        assert_eq!(entry.arity(), 2);
        assert_eq!(
            module, before_entry_check,
            "checking the wrapper grants no license"
        );
        assert_eq!(
            validate_module_with_config(&module, &strict()).into_errors(),
            vec![ValidationError::UngatedBodyForCodegen {
                function: helper.id.index(),
                name: helper.name.clone(),
            }],
            "{name}: exactly the unminted boxed helper must remain refused",
        );
    }
}

#[test]
fn ws6_7_actual_source_equation_checks_the_original_definition_and_emitted_body() {
    let env = elaborated_env_with(
        "def boundActualEquation (a b : UInt32) : UInt32 := UInt32.mul (UInt32.add a 7) b\n",
    );
    let source = KName::from_string("boundActualEquation");
    let decl = crate::to_lcnf::constant_to_decl(&env, env.get_const(&source).unwrap())
        .expect("actual checked source lowers")
        .expect("computational source");
    let cfg = crate::emit_trust_ir::TrustIrConfig {
        runtime_lowering: crate::emit_trust_ir::RuntimeLowering::ExternCalls,
        certify_translation: true,
        ..Default::default()
    };
    let (module, report) =
        compile_lcnf_to_trust_ir_with_report(&[decl], &env, &PipelineConfig::default(), &cfg)
            .expect("the canonical bound source pipeline");
    assert_eq!(report.certified, vec!["boundActualEquation"]);
    assert!(
        report.skipped.is_empty() && report.refused.is_empty(),
        "{report:?}"
    );
    let function = module
        .functions
        .iter()
        .find(|f| f.name == "boundActualEquation")
        .unwrap();
    let denotation = denote_function(&module, function).expect("actual IR denotation");
    let before = module.clone();
    let equation = clean_reflect::source_equation::check_uint_source_equation(
        &env, &source, &denotation, KName::from_string("ActualSourceEquation.checked"),
    ).expect("the kernel proves the original UInt source's Nat image equals the actual emitted denotation");
    export_actual_source_equation_fixture(
        "boundActualEquation",
        &module,
        &env,
        &equation,
        &["boundActualEquation"],
    );
    let mut replay = env.clone();
    replay
        .add_decl(equation.declaration().clone())
        .expect("replay exact source equation and proof");
    assert_eq!(
        module, before,
        "a source equation alone cannot mint a body license or change obligations"
    );
    let mut wrong = module.clone();
    let body = wrong
        .functions
        .iter_mut()
        .find(|f| f.id == function.id)
        .unwrap();
    let node = body
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.body)
        .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Add, .. }))
        .unwrap();
    let Inst::BinOp { op, .. } = &mut node.inst else {
        unreachable!()
    };
    *op = BinOp::Mul;
    let wrong_body = wrong
        .functions
        .iter()
        .find(|f| f.id == function.id)
        .unwrap();
    let denotation = denote_function(&wrong, wrong_body).expect("wrong but in-fragment emission");
    let error = clean_reflect::source_equation::check_uint_source_equation(
        &env,
        &source,
        &denotation,
        KName::from_string("ActualSourceEquation.wrong"),
    )
    .expect_err("the actual source equation must reject a changed emitted operation");
    assert!(error.to_string().contains("TypeMismatch"), "{error:?}");
}

#[test]
fn ws6_7_actual_source_equation_proves_the_real_hadd_sub_dictionary_pipeline() {
    let mut env = elaborated_env_with("def sourceSubSeed (a : UInt32) : UInt32 := a\n");
    add_checked_sub_dictionary_source(&mut env);
    let source = KName::from_string("boundField");
    let decl = crate::to_lcnf::constant_to_decl(&env, env.get_const(&source).unwrap())
        .expect("real source lowers")
        .expect("computational source");
    let cfg = crate::emit_trust_ir::TrustIrConfig {
        runtime_lowering: crate::emit_trust_ir::RuntimeLowering::ExternCalls,
        certify_translation: true,
        ..Default::default()
    };
    let (module, report) =
        compile_lcnf_to_trust_ir_with_report(&[decl], &env, &PipelineConfig::default(), &cfg)
            .expect("unchanged canonical source pipeline");
    assert_eq!(report.certified, vec!["boundField"]);
    let function = module
        .functions
        .iter()
        .find(|f| f.name == "boundField")
        .unwrap();
    let denotation = denote_function(&module, function).expect("actual emitted Sub");
    let before = module.clone();
    let equation = clean_reflect::source_equation::check_uint_source_equation(
        &env,
        &source,
        &denotation,
        KName::from_string("SourceSub.actualDictionary"),
    )
    .expect("real CIC arithmetic proves the actual HAdd dictionary's Sub field");
    export_actual_source_equation_fixture(
        "boundField",
        &module,
        &env,
        &equation,
        &["boundSubDictionary", "boundField"],
    );
    let mut replay = env.clone();
    replay
        .add_decl(equation.declaration().clone())
        .expect("replay the exact proof");
    assert_eq!(
        module, before,
        "no source proof alone licenses emitted wrappers or native code"
    );
    let mut wrong = module.clone();
    let body = wrong
        .functions
        .iter_mut()
        .find(|f| f.id == function.id)
        .unwrap();
    let node = body
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.body)
        .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Sub, .. }))
        .unwrap();
    let Inst::BinOp { op, .. } = &mut node.inst else {
        unreachable!()
    };
    *op = BinOp::Add;
    let wrong_function = wrong
        .functions
        .iter()
        .find(|f| f.id == function.id)
        .unwrap();
    let wrong_denotation = denote_function(&wrong, wrong_function).unwrap();
    clean_reflect::source_equation::check_uint_source_equation(
        &env,
        &source,
        &wrong_denotation,
        KName::from_string("SourceSub.wrongEmission"),
    )
    .expect_err("Sub cannot prove an emitted Add");
    let digest = env.closure_digest(&source).unwrap();
    assert!(env.forget_decl(&KName::from_string("boundSubDictionary")));
    let u = Expr::const_str("UInt32");
    env.add_decl(Declaration::Definition {
        name: KName::from_string("boundSubDictionary"),
        level_params: vec![],
        type_: Expr::apps(
            Expr::const_(KName::from_string("HAdd"), vec![Level::zero(); 3]),
            [u.clone(), u.clone(), u.clone()],
        ),
        value: Expr::apps(
            Expr::const_(KName::from_string("HAdd.mk"), vec![Level::zero(); 3]),
            [u.clone(), u.clone(), u, Expr::const_str("UInt32.add")],
        ),
        is_reducible: true,
    })
    .expect("replacement dictionary field is itself kernel checked");
    assert_ne!(env.closure_digest(&source).unwrap(), digest);
    clean_reflect::source_equation::check_uint_source_equation(
        &env,
        &source,
        &denotation,
        KName::from_string("SourceSub.changedDictionary"),
    )
    .expect_err("the old Sub equation cannot prove a changed actual dictionary field");
}

#[test]
fn ws6_7_actual_source_equation_proves_the_original_nested_bound_mask() {
    use trust_ir::Constant;

    let mut env = elaborated_env_with(
        "def boundMask (a b : UInt32) : UInt32 := UInt32.lor (UInt32.land a b) 1\n",
    );
    let source = KName::from_string("boundMask");
    let decl = crate::to_lcnf::constant_to_decl(&env, env.get_const(&source).unwrap())
        .expect("the original boundMask source lowers")
        .expect("computational source");
    let cfg = crate::emit_trust_ir::TrustIrConfig {
        runtime_lowering: crate::emit_trust_ir::RuntimeLowering::ExternCalls,
        certify_translation: true,
        ..Default::default()
    };
    let (module, report) =
        compile_lcnf_to_trust_ir_with_report(&[decl], &env, &PipelineConfig::default(), &cfg)
            .expect("unchanged canonical boundMask pipeline");
    assert_eq!(report.certified, vec!["boundMask"]);
    assert!(
        module
            .functions
            .iter()
            .any(|f| f.name == "l_boundMask___boxed"),
        "the generated helper remains in the module"
    );
    let function = module
        .functions
        .iter()
        .find(|f| f.name == "boundMask")
        .unwrap();
    let denotation =
        denote_function(&module, function).expect("actual emitted nested bitwise body");
    let before = module.clone();
    let equation = clean_reflect::source_equation::check_uint_source_equation(
        &env,
        &source,
        &denotation,
        KName::from_string("SourceBitwise.actualBoundMask"),
    )
    .expect("actual CIC bounds and congruence prove the original nested source");
    export_actual_source_equation_fixture("boundMask", &module, &env, &equation, &["boundMask"]);
    let mut replay = env.clone();
    replay
        .add_decl(equation.declaration().clone())
        .expect("replay the actual original-source proof");
    assert_eq!(
        module, before,
        "no source theorem alone licenses wrappers, ABI or bytes"
    );

    for label in ["operator", "literal", "operand"] {
        let mut wrong = module.clone();
        let body = wrong
            .functions
            .iter_mut()
            .find(|f| f.id == function.id)
            .unwrap();
        match label {
            "operator" => {
                let node = body
                    .blocks
                    .iter_mut()
                    .flat_map(|b| &mut b.body)
                    .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::Or, .. }))
                    .unwrap();
                let Inst::BinOp { op, .. } = &mut node.inst else {
                    unreachable!()
                };
                *op = BinOp::And;
            }
            "literal" => {
                let node = body
                    .blocks
                    .iter_mut()
                    .flat_map(|b| &mut b.body)
                    .find(|n| {
                        matches!(
                            n.inst,
                            Inst::Const {
                                value: Constant::Int(1),
                                ..
                            }
                        )
                    })
                    .unwrap();
                let Inst::Const { value, .. } = &mut node.inst else {
                    unreachable!()
                };
                *value = Constant::Int(2);
            }
            "operand" => {
                let node = body
                    .blocks
                    .iter_mut()
                    .flat_map(|b| &mut b.body)
                    .find(|n| matches!(n.inst, Inst::BinOp { op: BinOp::And, .. }))
                    .unwrap();
                let Inst::BinOp { lhs, rhs, .. } = &mut node.inst else {
                    unreachable!()
                };
                *rhs = *lhs;
            }
            _ => unreachable!(),
        }
        let wrong_function = wrong
            .functions
            .iter()
            .find(|f| f.id == function.id)
            .unwrap();
        let wrong_denotation = denote_function(&wrong, wrong_function).unwrap();
        clean_reflect::source_equation::check_uint_source_equation(
            &env,
            &source,
            &wrong_denotation,
            KName::from_string("SourceBitwise.wrongEmission").str(label),
        )
        .expect_err("an actual changed emitted result must refuse");
    }

    // This elaborated boundMask has no dependency on instOfNatUInt32: its
    // literal was resolved already. Exercise an ACTUAL retained dictionary
    // field using a separate checked definition with the same bitwise result.
    let u = Expr::const_str("UInt32");
    let levels = vec![Level::zero(); 3];
    let dictionary = KName::from_string("boundBitwiseDictionary");
    let dictionary_type = Expr::apps(
        Expr::const_(KName::from_string("HAdd"), levels.clone()),
        [u.clone(), u.clone(), u.clone()],
    );
    let dictionary_value = |operation: &str| {
        Expr::apps(
            Expr::const_(KName::from_string("HAdd.mk"), levels.clone()),
            [u.clone(), u.clone(), u.clone(), Expr::const_str(operation)],
        )
    };
    env.add_decl(Declaration::Definition {
        name: dictionary.clone(),
        level_params: vec![],
        type_: dictionary_type.clone(),
        value: dictionary_value("UInt32.land"),
        is_reducible: true,
    })
    .expect("a genuine checked HAdd dictionary may carry the land field");
    let dictionary_source = KName::from_string("boundMaskDictionary");
    env.add_decl(Declaration::Definition {
        name: dictionary_source.clone(),
        level_params: vec![],
        type_: Expr::arrow(u.clone(), Expr::arrow(u.clone(), u.clone())),
        value: Expr::lam(
            BinderInfo::Default,
            u.clone(),
            Expr::lam(
                BinderInfo::Default,
                u.clone(),
                Expr::apps(
                    Expr::const_str("UInt32.lor"),
                    [
                        Expr::apps(
                            Expr::const_(KName::from_string("HAdd.hAdd"), levels.clone()),
                            [
                                u.clone(),
                                u.clone(),
                                u.clone(),
                                Expr::const_(dictionary.clone(), vec![]),
                                Expr::bvar(1),
                                Expr::bvar(0),
                            ],
                        ),
                        Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(1u64)),
                    ],
                ),
            ),
        ),
        is_reducible: true,
    })
    .expect("the dictionary-dependent bitwise source itself kernel-checks");
    clean_reflect::source_equation::check_uint_source_equation(
        &env,
        &dictionary_source,
        &denotation,
        KName::from_string("SourceBitwise.actualDictionary"),
    )
    .expect("the actual retained land dictionary has the same source result");
    let digest = env.closure_digest(&dictionary_source).unwrap();
    assert!(env.forget_decl(&dictionary));
    env.add_decl(Declaration::Definition {
        name: dictionary,
        level_params: vec![],
        type_: dictionary_type,
        value: dictionary_value("UInt32.lor"),
        is_reducible: true,
    })
    .expect("the replacement bitwise dictionary field is itself fully checked");
    assert_ne!(
        env.closure_digest(&dictionary_source).unwrap(),
        digest,
        "the actual source closure must bind its retained dictionary"
    );
    clean_reflect::source_equation::check_uint_source_equation(
        &env,
        &dictionary_source,
        &denotation,
        KName::from_string("SourceBitwise.changedDictionary"),
    )
    .expect_err("the old equation cannot prove a changed actual dictionary field");
}

#[test]
fn ws6_7_actual_source_equation_proves_checked_conditional_all_uint_widths() {
    for width in [8, 16, 32, 64] {
        let label = format!("boundConditional{width}");
        let source = format!(
            "def {label} (a b : UInt{width}) : UInt{width} := if a < b then a + 1 else b\n"
        );
        assert_actual_conditional_source_pipeline(width, label, &source);
    }
}

#[test]
fn ws6_7_actual_source_equation_proves_computed_comparison_all_uint_widths() {
    for width in [8, 16, 32, 64] {
        let label = format!("boundComputedConditional{width}");
        let source = format!(
            "def {label} (a b c : UInt{width}) : UInt{width} := if (a - b) < c then a + 1 else b\n"
        );
        assert_actual_conditional_source_pipeline(width, label, &source);
    }
}

fn assert_actual_conditional_source_pipeline(width: u32, label: String, source_text: &str) {
    let env = elaborated_env_with(source_text);
    let source = KName::from_string(&label);
    let decl = crate::to_lcnf::constant_to_decl(&env, env.get_const(&source).unwrap())
        .expect("the actual checked conditional lowers")
        .expect("computational source");
    let cfg = crate::emit_trust_ir::TrustIrConfig {
        runtime_lowering: crate::emit_trust_ir::RuntimeLowering::ExternCalls,
        certify_translation: true,
        ..Default::default()
    };
    let (module, report) =
        compile_lcnf_to_trust_ir_with_report(&[decl], &env, &PipelineConfig::default(), &cfg)
            .expect("the unchanged canonical conditional pipeline");
    let function = module.functions.iter().find(|f| f.name == label).unwrap();
    let denotation = denote_function(&module, function);
    if let Some(root) = std::env::var_os("CLEAN_SOURCE_EQUATION_EXPORT_DIR") {
        let root = std::path::PathBuf::from(root).join("conditional-diagnostics");
        assert!(root.is_absolute());
        std::fs::create_dir_all(&root).expect("conditional diagnostic directory");
        std::fs::write(
            root.join(format!("{label}.module.bin")),
            trust_ir::binary::serialize_module(&module)
                .expect("actual conditional module encoding"),
        )
        .expect("actual conditional module data");
        std::fs::write(
            root.join(format!("{label}.module.txt")),
            format!("{module:#?}"),
        )
        .expect("actual conditional module diagnostic");
        let info = env.get_const(&source).unwrap();
        let mut expressions = vec![
            ("name", Expr::const_(info.name.clone(), vec![])),
            ("type", info.type_.clone()),
            ("value", info.value.as_ref().unwrap().clone()),
        ];
        if let Ok(denotation) = &denotation {
            expressions.push(("denotation", denotation.body.clone()));
        } else if let Err(error) = &denotation {
            std::fs::write(
                root.join(format!("{label}.denotation-error.txt")),
                error.to_string(),
            )
            .unwrap();
        }
        for (suffix, expression) in expressions {
            let bytes = trust_ir::proof::encode_clean_expr_v1(&expression)
                .expect("canonical actual conditional Expr data");
            assert_eq!(
                trust_ir::proof::decode_clean_expr_v1(&bytes).unwrap(),
                expression
            );
            std::fs::write(root.join(format!("{label}.{suffix}.bin")), bytes).unwrap();
            std::fs::write(
                root.join(format!("{label}.{suffix}.txt")),
                expression.to_string(),
            )
            .unwrap();
        }
        std::fs::write(root.join(format!("{label}.DATA.txt")), format!(
                "DATA ONLY: actual original checked Definition and actual emitted module/Nat model.\nwidth={width} arity={} is_reducible={} reducibility={:?}\n",
                module.func_types[function.ty.as_usize()].params.len(), info.is_reducible, info.reducibility,
            )).unwrap();
    }
    let denotation = denotation.expect("the actual emitted conditional");
    assert_eq!(report.certified, vec![label.clone()], "{width}: {report:?}");
    assert_eq!(report.source_equations.len(), 1);
    assert_eq!(report.final_module_digest, Some(Ok(module.stable_digest())));
    let retained = &report.source_equations[0];
    assert_eq!(retained.source, source);
    assert_eq!(retained.function, function.id);
    let expected = clean_reflect::source_equation::check_uint_source_equation(
        &env,
        &source,
        &denotation,
        KName::from_string(&format!("CleanSourceTV.{label}.denotes")),
    )
    .expect("same original full equation checked by production");
    let Declaration::Theorem {
        name,
        level_params,
        type_,
        value,
    } = expected.declaration()
    else {
        panic!("actual source equation must be a theorem");
    };
    assert_eq!(&retained.theorem_name, name);
    assert_eq!(&retained.level_params, level_params);
    assert_eq!(&retained.type_, type_);
    assert_eq!(&retained.value, value);
    assert_eq!(
        &retained.source_closure_digest,
        expected.source_closure_digest()
    );
    assert_eq!(
        &retained.equation_closure_digest,
        expected.equation_closure_digest()
    );
    let mut retained_replay = env.clone();
    retained_replay
        .add_decl(Declaration::Theorem {
            name: retained.theorem_name.clone(),
            level_params: retained.level_params.clone(),
            type_: retained.type_.clone(),
            value: retained.value.clone(),
        })
        .expect("replay the retained original judgment/value");
    let before = module.clone();
    let checked = clean_reflect::source_equation::check_uint_source_equation(
        &env,
        &source,
        &denotation,
        KName::from_string(&format!("SourceConditional.checked{width}")),
    )
    .expect("actual CIC proof connects the original conditional to the emitted body");
    export_actual_source_equation_fixture(&label, &module, &env, &checked, &[&label]);
    let mut replay = env.clone();
    replay
        .add_decl(checked.declaration().clone())
        .expect("replay original-source conditional proof");
    assert_eq!(
        module, before,
        "value equations never mint wrapper/ABI/body licenses"
    );

    for label in ["comparison", "arms"] {
        let mut wrong = module.clone();
        let body = wrong
            .functions
            .iter_mut()
            .find(|f| f.id == function.id)
            .unwrap();
        if label == "comparison" {
            let node = body
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.body)
                .find(|n| matches!(n.inst, Inst::ICmp { .. }))
                .unwrap();
            let Inst::ICmp { op, .. } = &mut node.inst else {
                unreachable!()
            };
            *op = ICmpOp::Uge;
        } else {
            let node = body
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.body)
                .find(|n| matches!(n.inst, Inst::CondBr { .. }))
                .unwrap();
            let Inst::CondBr {
                then_target,
                else_target,
                ..
            } = &mut node.inst
            else {
                unreachable!()
            };
            std::mem::swap(then_target, else_target);
        }
        let wrong_body = wrong
            .functions
            .iter()
            .find(|f| f.id == function.id)
            .unwrap();
        let wrong_denotation =
            denote_function(&wrong, wrong_body).expect("the mutated conditional is still modeled");
        assert!(
            clean_reflect::source_equation::check_uint_source_equation(
                &env,
                &source,
                &wrong_denotation,
                KName::from_string(&format!("SourceConditional.wrong{width}.{label}")),
            )
            .is_err(),
            "{width}: actual original source rejects changed {label}"
        );
        assert!(
            source_comparand_bytes(
                &wrong,
                wrong_body,
                env.get_const(&source).unwrap().value.as_ref().unwrap(),
                Some(&env),
            )
            .is_err(),
            "the importer's actual source comparison rejects changed {label}"
        );

        // Exercise the real minter too. Remove the deliberately stale
        // fixture evidence; a failed remint must add no evidence/license.
        wrong.proof_obligations.clear();
        wrong.proof_certificates.clear();
        for body in &mut wrong.functions {
            body.body_gate = Some(BodyGate::Ungated);
        }
        assert_ne!(report.final_module_digest, Some(Ok(wrong.stable_digest())));
        let before_refusal = wrong.clone();
        let report = certify_backend_translation_in_environment(
            &mut wrong,
            &[(
                source.to_string(),
                env.get_const(&source)
                    .unwrap()
                    .value
                    .as_ref()
                    .unwrap()
                    .clone(),
            )],
            &env,
        );
        assert!(
            report.certified.is_empty() && report.refused.len() == 1,
            "actual conditional remint must refuse changed {label}: {report:?}"
        );
        assert!(report.source_equations.is_empty());
        assert_eq!(report.final_module_digest, None);
        assert_eq!(
            wrong, before_refusal,
            "refusal never writes proof evidence or a body license"
        );
    }
}

#[test]
fn ws6_7_source_report_binds_all_four_widths_to_one_final_module() {
    let labels: Vec<_> = [8, 16, 32, 64]
        .map(|w| format!("reportConditional{w}"))
        .to_vec();
    let text = [8, 16, 32, 64]
        .iter()
        .zip(&labels)
        .map(|(w, name)| {
            format!("def {name} (a b : UInt{w}) : UInt{w} := if a < b then a + 1 else b\n")
        })
        .collect::<String>();
    let env = elaborated_env_with(&text);
    let decls: Vec<_> = labels
        .iter()
        .map(|label| {
            crate::to_lcnf::constant_to_decl(
                &env,
                env.get_const(&KName::from_string(label)).unwrap(),
            )
            .expect("actual conditional lowers")
            .expect("computational source")
        })
        .collect();
    let cfg = crate::emit_trust_ir::TrustIrConfig {
        runtime_lowering: crate::emit_trust_ir::RuntimeLowering::ExternCalls,
        certify_translation: true,
        ..Default::default()
    };
    let (module, report) =
        compile_lcnf_to_trust_ir_with_report(&decls, &env, &PipelineConfig::default(), &cfg)
            .expect("four actual source conditionals in one production module");
    assert!(report.refused.is_empty());
    assert_eq!(report.source_equations.len(), 4);
    assert_eq!(report.final_module_digest, Some(Ok(module.stable_digest())));
    for label in &labels {
        let source = KName::from_string(label);
        let function = module.functions.iter().find(|f| &f.name == label).unwrap();
        let record = report
            .source_equations
            .iter()
            .find(|r| r.source == source)
            .unwrap();
        assert_eq!(record.function, function.id);
        let expected = clean_reflect::source_equation::check_uint_source_equation(
            &env,
            &source,
            &denote_function(&module, function).unwrap(),
            KName::from_string(&format!("CleanSourceTV.{label}.denotes")),
        )
        .expect("original complete equation");
        let Declaration::Theorem {
            name,
            level_params,
            type_,
            value,
        } = expected.declaration()
        else {
            panic!("expected theorem");
        };
        assert_eq!(
            (
                &record.theorem_name,
                &record.level_params,
                &record.type_,
                &record.value
            ),
            (name, level_params, type_, value)
        );
        assert_eq!(
            &record.source_closure_digest,
            expected.source_closure_digest()
        );
        assert_eq!(
            &record.equation_closure_digest,
            expected.equation_closure_digest()
        );
    }
    let originals: Vec<_> = labels
        .iter()
        .map(|label| {
            (
                label.clone(),
                env.get_const(&KName::from_string(label))
                    .unwrap()
                    .value
                    .as_ref()
                    .unwrap()
                    .clone(),
            )
        })
        .collect();
    let mut legacy = module.clone();
    legacy.proof_obligations.clear();
    legacy.proof_certificates.clear();
    for function in &mut legacy.functions {
        function.body_gate = Some(BodyGate::Ungated);
    }
    let before = legacy.clone();
    let absent = certify_backend_translation(&mut legacy, &originals);
    assert!(absent.certified.is_empty());
    assert!(absent.source_equations.is_empty());
    assert_eq!(absent.final_module_digest, None);
    assert_eq!(absent.skipped.len(), 4);
    assert_eq!(legacy, before);
}
