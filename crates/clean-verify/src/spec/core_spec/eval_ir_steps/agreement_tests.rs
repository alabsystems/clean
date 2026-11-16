// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Kernel-checked specialization, not a Rust/compiler refinement claim.

use super::{IR_STEPS_SHARED_DRIVER_PROOF, IR_STEPS_SHARED_DRIVER_TYPE};
use crate::spec::core_spec::acceptance_in::theorem;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::{SpecError, Specification};
use crate::test_utils::run_with_stack;
use clean_kernel::{ConstantKind, ExprKind, Level, Name, TypeChecker};

const ROOT: &str = "ir_steps_shared_driver_agreement";
const EXPECTED_TYPE: &str = "forall (m : IRModule) (fuel : Nat) (c : IRConfig), @Eq IRConfig (ir_steps fuel m c) (ir_drive_v1 IRConfig (fun (c0 : IRConfig) => @IRConfig.rec (fun (_ : IRConfig) => Bool) (fun (_ : IRMachine) => Bool.false) (fun (_ : IROutcome) => Bool.true) c0) (fun (c0 : IRConfig) => @IRConfig.rec (fun (_ : IRConfig) => IRConfig) (fun (s : IRMachine) => ir_step m s) (fun (o : IROutcome) => IRConfig.halted o) c0) fuel c)";

// Pin the unchanged generic driver independently of the new specialization.
const SHARED_DRIVER: &str = "def ir_drive_v1 (C : Type) (halted : C -> Bool) (step : C -> C) (fuel : Nat) (c : C) : C := @Nat.rec (fun (_ : Nat) => C -> C) (fun (c0 : C) => c0) (fun (_ : Nat) (ih : C -> C) => fun (c0 : C) => @Bool.rec (fun (_ : Bool) => C) (ih (step c0)) c0 (halted c0)) fuel c";

const NEGATIVES: &[(&str, &str, &str)] = &[
    (
        "ir_steps_false_driver_endpoint",
        "forall (m : IRModule) (s : IRMachine) (o : IROutcome), Eq IRConfig (ir_steps Nat.zero m (IRConfig.running s)) (IRConfig.halted o)",
        "fun (m : IRModule) (s : IRMachine) (o : IROutcome) => ir_steps_shared_driver_agreement m Nat.zero (IRConfig.running s)",
    ),
    (
        "ir_steps_false_no_step",
        "forall (m : IRModule) (s : IRMachine), Eq IRConfig (ir_steps (Nat.succ Nat.zero) m (IRConfig.running s)) (IRConfig.running s)",
        "fun (m : IRModule) (s : IRMachine) => @Eq.refl IRConfig (IRConfig.running s)",
    ),
];

#[test]
fn specialization_agreement_is_a_checked_universal_prop() {
    run_with_stack(|| {
        let spec = Specification::new_eval_ir_spec().expect("real EvalIR bundle");
        assert_eq!(IR_STEPS_SHARED_DRIVER_TYPE, EXPECTED_TYPE);
        let record = spec.definitions().get(ROOT).expect("agreement record");
        assert_eq!(record.type_src, IR_STEPS_SHARED_DRIVER_TYPE);
        assert_eq!(
            record.value_src.as_deref(),
            Some(IR_STEPS_SHARED_DRIVER_PROOF)
        );
        assert!(!record.is_axiom);
        assert_eq!(record.category, AxiomCategory::DerivedLemma);
        assert_eq!(record.proof_status, ProofStatus::DerivedProved);
        let ty = record.elaborated_type.as_ref().expect("checked statement");
        let body = record.elaborated_value.as_ref().expect("checked proof");
        let root = Name::from_string(ROOT);
        assert!(!matches!(body.kind(), ExprKind::Const(name, _) if name == &root));
        let constant = spec.env().get_const(&root).expect("actual theorem");
        assert_eq!(constant.kind, ConstantKind::Theorem);
        assert_eq!(&constant.type_, ty);
        assert_eq!(constant.value.as_ref(), Some(body));
        let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
        let sort = checker.infer_type_full(ty).expect("statement checks");
        let ExprKind::Sort(level) = sort.kind() else {
            panic!("agreement must inhabit Prop")
        };
        assert!(Level::is_def_eq(level, &Level::zero()));
        let actual = checker.infer_type_full(body).expect("stored proof checks");
        assert!(checker.is_def_eq(&actual, ty));
        spec.verify_definition(ROOT).expect("proof record rechecks");
        assert!(spec.env().axiom_deps(&root).expect("root").is_empty());
        assert!(spec
            .env()
            .foundational_axiom_deps(&root)
            .expect("root")
            .is_empty());
        assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, ROOT).is_empty());

        let driver = spec
            .definitions()
            .get("ir_drive_v1")
            .expect("generic driver retained");
        assert_eq!(driver.type_src, SHARED_DRIVER);
        assert_eq!(driver.value_src.as_deref(), Some(SHARED_DRIVER));
        let driver_constant = spec
            .env()
            .get_const(&Name::from_string("ir_drive_v1"))
            .expect("generic driver constant");
        assert_eq!(driver_constant.kind, ConstantKind::Definition);
        assert!(!driver.is_axiom);

        // The universal theorem specializes to all three defining cases. The
        // running case calls the real ir_step, not an assumed step contract.
        for (source, expected) in [
            (
                "fun (m : IRModule) (c : IRConfig) => ir_steps_shared_driver_agreement m Nat.zero c",
                "forall (m : IRModule) (c : IRConfig), Eq IRConfig (ir_steps Nat.zero m c) c",
            ),
            (
                "fun (m : IRModule) (s : IRMachine) => ir_steps_shared_driver_agreement m (Nat.succ Nat.zero) (IRConfig.running s)",
                "forall (m : IRModule) (s : IRMachine), Eq IRConfig (ir_steps (Nat.succ Nat.zero) m (IRConfig.running s)) (ir_step m s)",
            ),
            (
                "fun (m : IRModule) (o : IROutcome) => ir_steps_shared_driver_agreement m (Nat.succ Nat.zero) (IRConfig.halted o)",
                "forall (m : IRModule) (o : IROutcome), Eq IRConfig (ir_steps (Nat.succ Nat.zero) m (IRConfig.halted o)) (IRConfig.halted o)",
            ),
        ] {
            let value = spec.elaborate_source(source, "agreement caller").expect("caller");
            let expected = spec.elaborate_source(expected, "agreement target").expect("target");
            let actual = checker.infer_type_full(&value).expect("caller fully checks");
            let _ = checker.infer_type_full(&expected).expect("target fully checks");
            assert!(checker.is_def_eq(&actual, &expected));
        }
    });
}

#[test]
fn specialization_rejects_wrong_endpoints_without_insertion() {
    run_with_stack(|| {
        let mut spec = Specification::new_eval_ir_spec().expect("real EvalIR bundle");
        let before = spec.definitions().len();
        for &(name, ty_source, proof_source) in NEGATIVES {
            let root = Name::from_string(name);
            assert!(!spec.definitions().contains_key(name));
            assert!(spec.env().get_const(&root).is_none());
            let ty = spec
                .elaborate_source(ty_source, "false statement")
                .expect("valid type");
            let proof = spec
                .elaborate_source(proof_source, "false proof")
                .expect("valid body");
            {
                let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
                let sort = checker.infer_type_full(&ty).expect("statement checks");
                assert!(
                    matches!(sort.kind(), ExprKind::Sort(level) if Level::is_def_eq(level, &Level::zero()))
                );
                let actual = checker.infer_type_full(&proof).expect("body itself checks");
                assert!(!checker.is_def_eq(&actual, &ty), "{name}: genuine mismatch");
            }
            let error = theorem(
                &mut spec,
                name,
                ty_source,
                proof_source,
                "False specialized/shared-driver endpoint control",
            )
            .expect_err("false body must be refused");
            let SpecError::TypeError(message) = error else {
                panic!("{name}: expected body TypeMismatch, got {error:?}")
            };
            assert!(
                message.starts_with(&format!("add_decl {name}:")),
                "{message}"
            );
            assert!(
                message.to_ascii_lowercase().contains("type mismatch"),
                "{message}"
            );
            assert!(!spec.definitions().contains_key(name));
            assert!(spec.env().get_const(&root).is_none());
            assert_eq!(spec.definitions().len(), before);
        }
    });
}
