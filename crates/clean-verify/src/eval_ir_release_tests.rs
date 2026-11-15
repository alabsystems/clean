// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Checks the real public canonical owner and closed unmodelled transitions.
//! These fixtures are not a Rust Release implementation or native adequacy claim.

use super::{checked_syntax_identity, EvalIrSyntaxEpoch, EVAL_IR_SYNTAX_EPOCH};
use crate::spec::Specification;
use clean_kernel::{Declaration, Environment, Expr, Level, Name, TypeChecker};

fn owner() -> Specification {
    crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
        .expect("actual checked canonical arithmetic/Byte owner")
}

fn strict_roundtrip(spec: &Specification, name: &str) {
    let name = Name::from_string(name);
    let info = spec
        .env()
        .get_const(&name)
        .unwrap_or_else(|| panic!("missing actual checked root {name}"));
    let proof = info.value.as_ref().expect("closed proof body");
    let claim: Expr = serde_json::from_slice(&serde_json::to_vec(&info.type_).unwrap()).unwrap();
    let decoded: Expr = serde_json::from_slice(&serde_json::to_vec(proof).unwrap()).unwrap();
    assert_eq!(claim, info.type_);
    assert_eq!(decoded, *proof);
    assert!(!decoded.has_fvar_quick() && !decoded.has_loose_bvars());
    assert!(!claim.has_fvar_quick() && !claim.has_loose_bvars());
    for body in [proof, &decoded] {
        let mut tc = TypeChecker::new(spec.env());
        tc.set_allow_unsafe(false);
        tc.set_allow_partial(false);
        tc.check_type(body, &claim)
            .expect("strict complete closed proof");
        assert!(!tc.heartbeat_spent());
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        assert!(spec.env().audit_certification(&claim, body).is_certified());
    }
    spec.env()
        .check_decl_readonly_strict(&Declaration::Definition {
            name: name.clone(),
            level_params: info.level_params.clone(),
            type_: claim,
            value: decoded,
            is_reducible: info.is_reducible,
        })
        .expect("strict actual stored declaration replay");
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec
        .env()
        .foundational_axiom_deps(&name)
        .unwrap()
        .is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn register(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Release syntax closed-model regression only")
        .expect("actual owner elaborates and checks fixture");
}

#[test]
fn release_epoch_uses_actual_public_canonical_owner_and_exact_metadata() {
    crate::test_utils::run_with_stack(|| {
        let spec = owner();
        let identity = checked_syntax_identity(spec.env(), EVAL_IR_SYNTAX_EPOCH).unwrap();
        assert_eq!(identity.epoch, EvalIrSyntaxEpoch::RetainedRelease);
        assert_eq!(
            identity.irinst_closure_digest,
            spec.env()
                .closure_digest(&Name::from_string("IRInst"))
                .unwrap()
        );
        assert!(
            checked_syntax_identity(spec.env(), EvalIrSyntaxEpoch::BeforeRelease)
                .unwrap_err()
                .contains("epoch mismatch")
        );
        let family = spec
            .env()
            .get_inductive(&Name::from_string("IRInst"))
            .unwrap();
        assert_eq!(family.constructor_names.len(), 33);
        assert_eq!(
            family.constructor_names[31],
            Name::from_string("IRInst.atomic_fetch_add_relaxed_usize_seq")
        );
        assert_eq!(
            family.constructor_names[32],
            Name::from_string("IRInst.release")
        );
        let release = spec
            .env()
            .get_constructor(&family.constructor_names[32])
            .unwrap();
        assert_eq!((release.constructor_idx, release.num_fields), (32, 1));
        assert_eq!(
            release.type_,
            super::syntax_epoch::constructor_type(&["Nat"])
        );
        for suffix in ["rec", "casesOn", "recOn"] {
            let rec = spec
                .env()
                .get_recursor(&Name::from_string(&format!("IRInst.{suffix}")))
                .unwrap();
            assert_eq!(rec.num_minors, 33);
            assert_eq!(rec.rules.len(), 33);
            assert_eq!(rec.rules[32].constructor_name, release.name);
            assert!(!rec.rules[32].recursive_fields.iter().any(|x| *x));
            rec.validate_metadata().unwrap();
        }
        // The cache cell's model key is the syntax epoch, not merely ByteV1's execution label.
        assert_eq!(super::BYTE_V1.syntax_epoch, EVAL_IR_SYNTAX_EPOCH);
        let clone = owner();
        assert_eq!(
            identity,
            checked_syntax_identity(clone.env(), EVAL_IR_SYNTAX_EPOCH).unwrap()
        );
        for name in [
            "ir_exec_release_unmodelled",
            "ir_exec_release_pointer_irrelevant",
            "ir_byte_release_unmodelled_v1",
        ] {
            strict_roundtrip(&spec, name);
        }
    });
}

#[test]
fn release_wrong_old_family_and_mutated_constructor_headers_refuse() {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
    crate::test_utils::run_with_stack(|| {
        let spec = owner();
        // NEGATIVE fixture only: re-admit exact checked prerequisites and the genuine
        // previous32 telescopes. Positive qualification always uses the public owner.
        let mut prerequisites = Environment::with_prelude();
        for family_name in [
            "IRList",
            "IROption",
            "IRTy",
            "IRConst",
            "IRBinOp",
            "IRUnOp",
            "IROverflowOp",
            "IRICmpOp",
            "IRFCmpOp",
            "IRCastOp",
            "IRSwitchCase",
        ] {
            let family = spec
                .env()
                .get_inductive(&Name::from_string(family_name))
                .unwrap();
            prerequisites
                .add_inductive(InductiveDecl {
                    level_params: family.level_params.clone(),
                    num_params: family.num_params,
                    types: vec![InductiveType {
                        name: family.name.clone(),
                        type_: family.type_.clone(),
                        constructors: family
                            .constructor_names
                            .iter()
                            .map(|name| {
                                let ctor = spec.env().get_constructor(name).unwrap();
                                Constructor {
                                    name: name.clone(),
                                    type_: ctor.type_.clone(),
                                }
                            })
                            .collect(),
                    }],
                })
                .expect("exact prerequisite re-admission");
        }
        let old_constructors: Vec<_> = super::syntax_epoch::INSTRUCTION_HEADERS[..32]
            .iter()
            .map(|(name, fields)| Constructor {
                name: Name::from_string(&format!("IRInst.{name}")),
                type_: super::syntax_epoch::constructor_type(fields),
            })
            .collect();
        let mut old = prerequisites.clone();
        old.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("IRInst"),
                type_: Expr::sort(Level::succ(Level::zero())),
                constructors: old_constructors.clone(),
            }],
        })
        .expect("actual previous32 constructor telescopes re-admit");
        assert_eq!(
            old.get_inductive(&Name::from_string("IRInst"))
                .unwrap()
                .constructor_names
                .len(),
            32
        );
        assert!(checked_syntax_identity(&old, EVAL_IR_SYNTAX_EPOCH)
            .unwrap_err()
            .contains("Release33"));
        let mut wrong_constructors = old_constructors;
        wrong_constructors.push(Constructor {
            name: Name::from_string("IRInst.release"),
            type_: super::syntax_epoch::constructor_type(&["Bool"]),
        });
        prerequisites
            .add_inductive(InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![InductiveType {
                    name: Name::from_string("IRInst"),
                    type_: Expr::sort(Level::succ(Level::zero())),
                    constructors: wrong_constructors,
                }],
            })
            .expect("wrong but well-typed33-header is a genuine admitted negative");
        assert!(
            checked_syntax_identity(&prerequisites, EVAL_IR_SYNTAX_EPOCH)
                .unwrap_err()
                .contains("constructor header mismatch: IRInst.release")
        );
        let mut env = spec.env().clone();
        let conflict = env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("IRInst"),
                type_: Expr::sort(Level::succ(Level::zero())),
                constructors: vec![],
            }],
        });
        assert!(
            conflict.is_err(),
            "same-name registration cannot replace current metadata"
        );
        assert_eq!(
            checked_syntax_identity(&env, EVAL_IR_SYNTAX_EPOCH).unwrap(),
            checked_syntax_identity(spec.env(), EVAL_IR_SYNTAX_EPOCH).unwrap()
        );
    });
}

#[test]
fn release_fetched_site_arity_and_world_preflights_keep_their_order() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = owner();
        for source in [
            "def release_frame : IRFrame := IRFrame.mk 71 0 2 (IRList.nil IRBinding) (IRList.nil Nat)",
            "def release_machine : IRMachine := IRMachine.mk (IRList.cons IRFrame release_frame (IRList.nil IRFrame)) (IRList.nil IRMemSlot) 1",
            "def release_world : IRByteWorldV1 Nat := IRByteWorldV1.mk Nat (ir_byte_memory_empty_v1 64) 91 (IRList.cons Nat 1 (IRList.nil Nat)) 2",
            "def release_invalid_world : IRByteWorldV1 Nat := IRByteWorldV1.mk Nat (ir_byte_memory_empty_v1 64) 91 (IRList.nil Nat) 0",
            "def release_provider : IRByteProvidersV1 Nat := fun (_ : Nat) (_ : IRList IRScalar) (mem : IRByteMemoryV1) (host : Nat) => IRByteImportResultV1.mk Nat (IROutcome.ret (IRList.nil IRScalar)) mem host",
            "def release_site : IRByteSiteV1 := IRByteSiteV1.mk 71 0 2 0 1 (IRList.nil IRTy)",
            "def release_context : IRByteContextV1 := IRByteContextV1.mk (IRModule.mk (IRList.nil IRFunc) (IRList.nil IRGlobal)) (IRList.nil IRByteLayoutV1) (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1) (IRList.cons IRByteSiteV1 release_site (IRList.nil IRByteSiteV1))",
            "def release_full_module : IRModule := IRModule.mk (IRList.cons IRFunc (IRFunc.mk 71 (IRList.nil Nat) 0 (IRList.cons IRBlock (IRBlock.mk 0 (IRList.nil Nat) (IRList.cons IRNode (IRNode.mk (IRInst.release 0) (IRList.nil Nat)) (IRList.cons IRNode (IRNode.mk (IRInst.release 1) (IRList.nil Nat)) (IRList.nil IRNode)))) (IRList.nil IRBlock))) (IRList.nil IRFunc)) (IRList.nil IRGlobal)",
            "def release_full_context : IRByteContextV1 := IRByteContextV1.mk release_full_module (IRList.nil IRByteLayoutV1) (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1) (IRList.cons IRByteSiteV1 (IRByteSiteV1.mk 71 0 0 0 1 (IRList.nil IRTy)) (IRList.cons IRByteSiteV1 (IRByteSiteV1.mk 71 0 1 0 1 (IRList.nil IRTy)) (IRList.nil IRByteSiteV1)))",
            "def release_full_machine : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk 71 0 0 (IRList.nil IRBinding) (IRList.nil Nat)) (IRList.nil IRFrame)) (IRList.nil IRMemSlot) 1",
            "def release_missing_context : IRByteContextV1 := IRByteContextV1.mk (IRModule.mk (IRList.nil IRFunc) (IRList.nil IRGlobal)) (IRList.nil IRByteLayoutV1) (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1) (IRList.nil IRByteSiteV1)",
        ] { register(&mut spec, source); }
        for (name, actual, expected) in [
            ("release_full_fetch_unmodelled", "ir_byte_step_v1 Nat release_full_context release_provider (IRByteConfigV1.running Nat release_full_machine release_world)", "IRByteConfigV1.halted Nat (IROutcome.unmodelled IRFault.width_bounded) release_world"),
            ("release_fetched_unmodelled", "ir_byte_step_node_v1 Nat release_context release_provider release_machine release_world release_frame (IRNode.mk (IRInst.release 0) (IRList.nil Nat))", "IRByteConfigV1.halted Nat (IROutcome.unmodelled IRFault.width_bounded) release_world"),
            ("release_pointer_one_also_unmodelled", "ir_byte_step_node_v1 Nat release_context release_provider release_machine release_world release_frame (IRNode.mk (IRInst.release 1) (IRList.nil Nat))", "IRByteConfigV1.halted Nat (IROutcome.unmodelled IRFault.width_bounded) release_world"),
            ("release_missing_site_first", "ir_byte_step_node_v1 Nat release_missing_context release_provider release_machine release_world release_frame (IRNode.mk (IRInst.release 0) (IRList.cons Nat 7 (IRList.nil Nat)))", "IRByteConfigV1.halted Nat (IROutcome.stuck IRFault.fetch_past_end) release_world"),
            ("release_bad_result_arity_first", "ir_byte_step_node_v1 Nat release_context release_provider release_machine release_world release_frame (IRNode.mk (IRInst.release 0) (IRList.cons Nat 7 (IRList.nil Nat)))", "IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) release_world"),
            ("release_invalid_world_first", "ir_byte_step_v1 Nat release_context release_provider (IRByteConfigV1.running Nat release_machine release_invalid_world)", "IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_addr) release_invalid_world"),
        ] {
            register(&mut spec, &format!("def {name} : Eq (IRByteConfigV1 Nat) ({actual}) ({expected}) := Eq.refl (IRByteConfigV1 Nat) ({expected})"));
            strict_roundtrip(&spec, name);
        }
        for (name, right) in [
            ("release_not_pointer_fault", "IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.not_ptr) release_world"),
            ("release_not_running", "IRByteConfigV1.running Nat release_machine release_world"),
            ("release_not_changed_world", "IRByteConfigV1.halted Nat (IROutcome.unmodelled IRFault.width_bounded) release_invalid_world"),
        ] {
            let result = spec.add_recursive_def(&format!("def {name} : Eq (IRByteConfigV1 Nat) (ir_byte_exec_v1 Nat release_context release_provider release_machine release_world release_site (IRInst.release 0) (IRList.nil Nat)) ({right}) := Eq.refl (IRByteConfigV1 Nat) ({right})"), "Deliberately false Release result");
            let error = result.expect_err("wrong endpoint must refuse");
            assert!(matches!(&error, crate::spec::SpecError::ElabError(message) if message.contains("Type mismatch:")), "must be a genuine elaborator type mismatch: {error:?}");
            assert!(!clean_kernel::tc::declaration_budget_exhausted());
        }
        assert_ne!(
            Expr::app(Expr::const_str("IRInst.release"), Expr::nat_lit(0)),
            Expr::app(Expr::const_str("IRInst.release"), Expr::nat_lit(1))
        );
    });
}

#[test]
fn release_eliminator_missing_minor_is_a_real_type_mismatch() {
    use clean_kernel::BinderInfo;
    crate::test_utils::run_with_stack(|| {
        let spec = owner();
        let rec = spec
            .env()
            .get_const(&Name::from_string("IRInst.rec"))
            .unwrap();
        let mut args = vec![Expr::lam(
            BinderInfo::Default,
            Expr::const_str("IRInst"),
            Expr::const_str("Bool"),
        )];
        for (_, fields) in super::syntax_epoch::INSTRUCTION_HEADERS {
            let mut ty = super::syntax_epoch::constructor_type(fields);
            let mut binders = vec![];
            for _ in 0..fields.len() {
                let clean_kernel::ExprKind::Pi(_, field, rest) = ty.kind() else {
                    panic!("fixed telescope")
                };
                binders.push((**field).clone());
                ty = (**rest).clone();
            }
            args.push(
                binders
                    .into_iter()
                    .rev()
                    .fold(Expr::const_str("Bool.false"), |rest, field| {
                        Expr::lam(BinderInfo::Default, field, rest)
                    }),
            );
        }
        let major = Expr::app(Expr::const_str("IRInst.release"), Expr::nat_lit(0));
        let levels = rec
            .level_params
            .iter()
            .map(|_| Level::succ(Level::zero()))
            .collect::<Vec<_>>();
        let mut complete = args.clone();
        complete.push(major.clone());
        let term = Expr::apps(
            Expr::const_(Name::from_string("IRInst.rec"), levels.clone()),
            complete,
        );
        let mut tc = TypeChecker::new(spec.env());
        tc.set_allow_unsafe(false);
        tc.set_allow_partial(false);
        tc.check_type(&term, &Expr::const_str("Bool"))
            .expect("all33 actual minors typecheck");
        args.pop(); // Deliberately reuse an old32-minor application against the new owner.
        args.push(major);
        let old = Expr::apps(Expr::const_(Name::from_string("IRInst.rec"), levels), args);
        let error = tc
            .check_type(&old, &Expr::const_str("Bool"))
            .expect_err("missing33rd minor must refuse");
        assert!(format!("{error:?}").contains("TypeMismatch"), "{error:?}");
        assert!(!tc.heartbeat_spent());
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
    });
}

#[test]
fn release_stack_and_bm_laws_use_the_real_dependency_scoped_installer() {
    crate::test_utils::run_with_stack(|| {
        let spec = crate::eval_ir::build_spec_with_stack()
            .expect("actual dependency-scoped checked stack/Bm installer");
        checked_syntax_identity(spec.env(), EVAL_IR_SYNTAX_EPOCH).unwrap();
        for name in [
            "ir_bm_release_unmodelled",
            "ir_stk_arm_release",
            "ir_mext_arm_release",
            "ir_stkn_arm_release",
            "ir_mextv_arm_release",
            "ir_bdst_arm_release",
            "ir_mexto_arm_release",
            "ir_mextvo_arm_release",
        ] {
            strict_roundtrip(&spec, name);
        }
    });
}

#[test]
fn release_auxiliary_body_authentication_rejects_same_header_wrong_values() {
    crate::test_utils::run_with_stack(|| {
        let spec = owner();
        for suffix in ["casesOn", "recOn"] {
            let name = Name::from_string(&format!("IRInst.{suffix}"));
            let mut forged = spec.env().get_const(&name).unwrap().clone();
            assert!(
                forged.value.is_some(),
                "canonical auxiliaries carry actual wrappers"
            );
            forged.value = Some(Expr::const_str("Bool.false"));
            let mut untrusted = spec.env().clone();
            // Existing kernel test-fixtures door, never a production admission.
            untrusted.add_constant_unchecked_for_test(forged);
            let error = checked_syntax_identity(&untrusted, EVAL_IR_SYNTAX_EPOCH).expect_err(
                "same name/type/present-value is not canonical auxiliary authentication",
            );
            assert!(
                error.contains("does not inhabit") || error.contains("strict auxiliary check"),
                "{error}"
            );
            assert!(!clean_kernel::tc::declaration_budget_exhausted());
        }
    });
}
