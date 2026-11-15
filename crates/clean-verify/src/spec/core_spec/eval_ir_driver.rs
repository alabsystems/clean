// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Configuration-preserving, instruction-independent execution driver.
//!
//! A profile supplies its whole configuration, its terminal-state predicate,
//! and its single-step semantics. Zero fuel and terminal states return that
//! configuration unchanged: neither an outcome projection nor a call to the
//! step function can discard the final world. A running state consumes one
//! unit of fuel per application of the supplied step.
//!
//! The legacy `ir_steps` specializes this driver to `IRConfig` and `ir_step`.
//! Its existing faithfulness and composition proofs still check against the
//! unchanged `ir_run`. New profiles can retain bytes, provider state, and
//! resource ownership in their configurations without copying the iterator.
//!
//! This definition does not validate a supplied step function or establish
//! that any profile implements Core or native code. Those are separate
//! semantic obligations. The equations here are checked terms, not an
//! authority granted by a profile name or a proof-status label.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_DRIVE: &str = "def ir_drive_v1 (C : Type) (halted : C -> Bool) (step : C -> C) (fuel : Nat) (c : C) : C := @Nat.rec (fun (_ : Nat) => C -> C) (fun (c0 : C) => c0) (fun (_ : Nat) (ih : C -> C) => fun (c0 : C) => @Bool.rec (fun (_ : Bool) => C) (ih (step c0)) c0 (halted c0)) fuel c";

const SRC_ZERO: &str = "def ir_drive_zero_v1 (C : Type) (halted : C -> Bool) (step : C -> C) (c : C) : @Eq C (ir_drive_v1 C halted step Nat.zero c) c := @Eq.refl C c";

const SRC_SUCC: &str = "def ir_drive_succ_v1 (C : Type) (halted : C -> Bool) (step : C -> C) (fuel : Nat) (c : C) : @Eq C (ir_drive_v1 C halted step (Nat.succ fuel) c) (@Bool.rec (fun (_ : Bool) => C) (ir_drive_v1 C halted step fuel (step c)) c (halted c)) := @Eq.refl C (@Bool.rec (fun (_ : Bool) => C) (ir_drive_v1 C halted step fuel (step c)) c (halted c))";

const SRC_HALTED: &str = "def ir_drive_halted_v1 (C : Type) (halted : C -> Bool) (step : C -> C) (c : C) (h : @Eq Bool (halted c) Bool.true) (fuel : Nat) : @Eq C (ir_drive_v1 C halted step fuel c) c := @Nat.rec (fun (k : Nat) => @Eq C (ir_drive_v1 C halted step k c) c) (@Eq.refl C c) (fun (k : Nat) (_ih : @Eq C (ir_drive_v1 C halted step k c) c) => @Eq.subst Bool (fun (b : Bool) => @Eq C (@Bool.rec (fun (_ : Bool) => C) (ir_drive_v1 C halted step k (step c)) c b) c) Bool.true (halted c) (@Eq.symm Bool (halted c) Bool.true h) (@Eq.refl C c)) fuel";

// The Bool convoy keeps the terminal equality available in the true branch.
// A terminal step need not be idempotent: the driver must never call it.
const SRC_ADD: &str = r#"def ir_drive_add_v1 (C : Type) (halted : C -> Bool) (step : C -> C) (b : Nat) (a : Nat) : forall (c : C), @Eq C (ir_drive_v1 C halted step (Nat.add b a) c) (ir_drive_v1 C halted step b (ir_drive_v1 C halted step a c)) :=
@Nat.rec
  (fun (k : Nat) => forall (c : C), @Eq C (ir_drive_v1 C halted step (Nat.add b k) c) (ir_drive_v1 C halted step b (ir_drive_v1 C halted step k c)))
  (fun (c : C) => @Eq.refl C (ir_drive_v1 C halted step b c))
  (fun (k : Nat) (ih : forall (c : C), @Eq C (ir_drive_v1 C halted step (Nat.add b k) c) (ir_drive_v1 C halted step b (ir_drive_v1 C halted step k c))) =>
    fun (c : C) =>
    @Bool.rec
      (fun (flag : Bool) => @Eq Bool (halted c) flag -> @Eq C
        (@Bool.rec (fun (_ : Bool) => C) (ir_drive_v1 C halted step (Nat.add b k) (step c)) c flag)
        (ir_drive_v1 C halted step b (@Bool.rec (fun (_ : Bool) => C) (ir_drive_v1 C halted step k (step c)) c flag)))
      (fun (_h : @Eq Bool (halted c) Bool.false) => ih (step c))
      (fun (h : @Eq Bool (halted c) Bool.true) => @Eq.symm C (ir_drive_v1 C halted step b c) c (ir_drive_halted_v1 C halted step c h b))
      (halted c) (@Eq.refl Bool (halted c)))
  a"#;

impl Specification {
    /// Install the shared iterator and its zero, successor, terminal and
    /// fuel-composition laws.
    ///
    /// All declarations are elaborated and rechecked against the kernel. The
    /// caller must already have installed `Nat`, `Bool`, and equality. This
    /// adds no axioms and does not modify any existing semantics declaration.
    pub(super) fn add_eval_ir_driver(&mut self) -> Result<(), SpecError> {
        for (name, source, description) in [
            (
                "ir_drive_v1",
                SRC_DRIVE,
                "Configuration-preserving fuel iterator over a supplied profile step; no instruction or provider semantics are assumed.",
            ),
            (
                "ir_drive_zero_v1",
                SRC_ZERO,
                "Zero fuel preserves every field of the supplied configuration.",
            ),
            (
                "ir_drive_succ_v1",
                SRC_SUCC,
                "One unit of fuel tests for termination before applying the supplied step.",
            ),
            (
                "ir_drive_halted_v1",
                SRC_HALTED,
                "A terminal configuration is preserved for arbitrary fuel, without assuming its step is a fixed point.",
            ),
            (
                "ir_drive_add_v1",
                SRC_ADD,
                "Splitting fuel preserves the entire configuration for any instruction/provider profile, including failures and already terminal states.",
            ),
        ] {
            self.add_recursive_def(source, description)?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    fn driver_spec() -> Specification {
        let mut spec = Specification::new_empty();
        spec.add_foundation_types().expect("foundation types");
        spec.add_eval_ir_driver().expect("checked shared driver");
        spec
    }

    fn assert_checked(spec: &Specification, name: &str) {
        let def = spec.get_definition(name).expect("registered definition");
        assert!(!def.is_axiom, "{name} must have a definition");
        assert!(def.elaborated_value.is_some(), "{name} needs a term");
        spec.verify_definition(name).expect("kernel replay");
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .expect("root must exist");
        assert!(deps.is_empty(), "{name} has domain axioms: {deps:?}");
        let markers = spec
            .env()
            .trust_marker_deps(&Name::from_string(name))
            .expect("root must exist");
        assert!(markers.is_empty(), "{name} has trust markers: {markers:?}");
    }

    fn add_checked(spec: &mut Specification, name: &str, source: &str) {
        spec.add_recursive_def(source, "shared driver checked witness")
            .expect("witness must elaborate and check");
        assert_checked(spec, name);
    }

    fn world_spec() -> Specification {
        let mut spec = driver_spec();
        spec.add_inductive(
            "inductive IRDriveTestConfig : Type\n| running : Nat -> Nat -> IRDriveTestConfig\n| halted : Nat -> Nat -> IRDriveTestConfig",
            "Test configuration with program position or status and observable world",
        )
        .expect("test configuration");
        add_checked(
            &mut spec,
            "ir_drive_test_halted",
            "def ir_drive_test_halted (c : IRDriveTestConfig) : Bool := @IRDriveTestConfig.rec (fun (_ : IRDriveTestConfig) => Bool) (fun (_pc : Nat) (_world : Nat) => Bool.false) (fun (_status : Nat) (_world : Nat) => Bool.true) c",
        );
        // The first step mutates the world, and the second mutates it again
        // before failing. Calling step on an already terminal configuration
        // deliberately destroys its status and world, so an extra step is
        // observable rather than hidden by an idempotent step definition.
        add_checked(
            &mut spec,
            "ir_drive_test_step",
            "def ir_drive_test_step (c : IRDriveTestConfig) : IRDriveTestConfig := @IRDriveTestConfig.rec (fun (_ : IRDriveTestConfig) => IRDriveTestConfig) (fun (pc : Nat) (world : Nat) => @Nat.rec (fun (_ : Nat) => IRDriveTestConfig) (IRDriveTestConfig.running (Nat.succ Nat.zero) (Nat.succ world)) (fun (_ : Nat) (_ih : IRDriveTestConfig) => IRDriveTestConfig.halted (Nat.succ Nat.zero) (Nat.succ world)) pc) (fun (_status : Nat) (_world : Nat) => IRDriveTestConfig.running Nat.zero Nat.zero) c",
        );
        spec
    }

    #[test]
    fn generic_equations_are_kernel_checked_without_domain_axioms() {
        crate::test_utils::run_with_stack(|| {
            let spec = driver_spec();
            for name in [
                "ir_drive_v1",
                "ir_drive_zero_v1",
                "ir_drive_succ_v1",
                "ir_drive_halted_v1",
                "ir_drive_add_v1",
            ] {
                assert_checked(&spec, name);
            }
        });
    }

    #[test]
    fn driver_and_legacy_specialization_check_in_the_production_prelude() {
        crate::test_utils::run_with_stack(|| {
            let mut spec =
                Specification::new_eval_ir_prelude_spec().expect("production prelude EvalIR");
            spec.add_eval_ir_steps()
                .expect("driver and unchanged legacy laws in the production prelude");
            for name in [
                "ir_drive_halted_v1",
                "ir_run_of_steps",
                "ir_steps_add",
                "ir_run_steps_split",
            ] {
                assert_checked(&spec, name);
            }
        });
    }

    #[test]
    fn zero_and_exhausted_fuel_preserve_the_whole_running_world() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = world_spec();
            add_checked(
                &mut spec,
                "ir_drive_test_zero",
                "def ir_drive_test_zero (pc : Nat) (world : Nat) : @Eq IRDriveTestConfig (ir_drive_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step Nat.zero (IRDriveTestConfig.running pc world)) (IRDriveTestConfig.running pc world) := @Eq.refl IRDriveTestConfig (IRDriveTestConfig.running pc world)",
            );
            add_checked(
                &mut spec,
                "ir_drive_test_partial",
                "def ir_drive_test_partial (world : Nat) : @Eq IRDriveTestConfig (ir_drive_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step (Nat.succ Nat.zero) (IRDriveTestConfig.running Nat.zero world)) (IRDriveTestConfig.running (Nat.succ Nat.zero) (Nat.succ world)) := @Eq.refl IRDriveTestConfig (IRDriveTestConfig.running (Nat.succ Nat.zero) (Nat.succ world))",
            );
            assert!(spec.add_recursive_def(
                "def ir_drive_test_lost_partial (world : Nat) : @Eq IRDriveTestConfig (ir_drive_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step (Nat.succ Nat.zero) (IRDriveTestConfig.running Nat.zero world)) (IRDriveTestConfig.running (Nat.succ Nat.zero) world) := @Eq.refl IRDriveTestConfig (IRDriveTestConfig.running (Nat.succ Nat.zero) world)",
                "must reject loss of the running world's mutation",
            ).is_err());
        });
    }

    #[test]
    fn arbitrary_terminal_status_and_world_survive_poison_step_and_fuel() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = world_spec();
            add_checked(
                &mut spec,
                "ir_drive_test_terminal",
                "def ir_drive_test_terminal (status : Nat) (world : Nat) (fuel : Nat) : @Eq IRDriveTestConfig (ir_drive_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step fuel (IRDriveTestConfig.halted status world)) (IRDriveTestConfig.halted status world) := ir_drive_halted_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step (IRDriveTestConfig.halted status world) (@Eq.refl Bool Bool.true) fuel",
            );
            assert!(spec.add_recursive_def(
                "def ir_drive_test_stepped_terminal : @Eq IRDriveTestConfig (ir_drive_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step (Nat.succ Nat.zero) (IRDriveTestConfig.halted Nat.zero Nat.zero)) (IRDriveTestConfig.running Nat.zero Nat.zero) := @Eq.refl IRDriveTestConfig (IRDriveTestConfig.running Nat.zero Nat.zero)",
                "must reject stepping an already terminal configuration",
            ).is_err());
        });
    }

    #[test]
    fn failure_retains_prior_and_failing_step_effects_with_surplus_fuel() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = world_spec();
            add_checked(
                &mut spec,
                "ir_drive_test_failure",
                "def ir_drive_test_failure (world : Nat) (fuel : Nat) : @Eq IRDriveTestConfig (ir_drive_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step (Nat.succ (Nat.succ fuel)) (IRDriveTestConfig.running Nat.zero world)) (IRDriveTestConfig.halted (Nat.succ Nat.zero) (Nat.succ (Nat.succ world))) := ir_drive_halted_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step (IRDriveTestConfig.halted (Nat.succ Nat.zero) (Nat.succ (Nat.succ world))) (@Eq.refl Bool Bool.true) fuel",
            );
            assert!(spec.add_recursive_def(
                "def ir_drive_test_lost_failure (world : Nat) : @Eq IRDriveTestConfig (ir_drive_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step (Nat.succ (Nat.succ Nat.zero)) (IRDriveTestConfig.running Nat.zero world)) (IRDriveTestConfig.halted (Nat.succ Nat.zero) (Nat.succ world)) := @Eq.refl IRDriveTestConfig (IRDriveTestConfig.halted (Nat.succ Nat.zero) (Nat.succ world))",
                "must reject rollback of the failing step's effect",
            ).is_err());
        });
    }

    #[test]
    fn shared_composition_preserves_world_and_failure_across_resumption() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = world_spec();
            add_checked(
                &mut spec,
                "ir_drive_test_resume",
                "def ir_drive_test_resume (first : Nat) (remaining : Nat) (c : IRDriveTestConfig) : @Eq IRDriveTestConfig (ir_drive_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step (Nat.add remaining first) c) (ir_drive_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step remaining (ir_drive_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step first c)) := ir_drive_add_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step remaining first c",
            );
            add_checked(
                &mut spec,
                "ir_drive_test_resume_failure",
                "def ir_drive_test_resume_failure (world : Nat) : @Eq IRDriveTestConfig (ir_drive_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step (Nat.succ Nat.zero) (ir_drive_v1 IRDriveTestConfig ir_drive_test_halted ir_drive_test_step (Nat.succ Nat.zero) (IRDriveTestConfig.running Nat.zero world))) (IRDriveTestConfig.halted (Nat.succ Nat.zero) (Nat.succ (Nat.succ world))) := @Eq.refl IRDriveTestConfig (IRDriveTestConfig.halted (Nat.succ Nat.zero) (Nat.succ (Nat.succ world)))",
            );
        });
    }

    #[test]
    fn legacy_iterator_faithfulness_composition_and_activation_replay() {
        crate::test_utils::run_with_stack(|| {
            let spec = Specification::new_eval_ir_spec().expect("real legacy EvalIR bundle");
            for name in [
                "ir_steps",
                "ir_run_halted",
                "ir_steps_halted",
                "ir_run_of_steps",
                "ir_steps_add",
                "ir_run_steps_split",
                "ir_lzm_activation_zero",
                "ir_lzm_activation_succ",
                "ir_lzm_activation_param",
            ] {
                assert_checked(&spec, name);
            }
        });
    }
}
