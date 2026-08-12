// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Fuel monotonicity for the IR machine** — crystal A4's first prerequisite.
//!
//! A4 is `forall l, EncodesLiveLevelRef mem r l -> ir_eval … = ret …`, and it
//! cannot be stated at a fixed fuel: steps grow with `|l|`, and `ir_run` reports
//! exhaustion as `IROutcome.fuel_out`, *"its OWN outcome, distinct from every
//! real result, so no theorem can mistake it for success"*. So A4 carries a
//! `Le (ir_lz_fuel l) fuel` premise, and that premise is useless without the
//! monotonicity proved here.
//!
//! ## The statement has to be about successful returns
//!
//! The unconditional form — `ir_run f m c = ir_run (succ f) m c` — is **false**:
//! a run that exhausts at `f` may halt at `succ f`. Restricting to `ret v` is
//! not a convenience, it is what makes the lemma true.
//!
//! The proof is `Nat.rec` on the fuel, generalised over the configuration, with
//! an `IRConfig.rec` convoy per arm. Every `halted` case is the identity, since
//! `ir_run` returns a halted outcome unchanged at any fuel. The one case with
//! content is zero/`running`, where `ir_run` computes to `fuel_out` and the
//! hypothesis claims it equals `ret v` — refuted by the discriminators, which
//! come in Prop and Type twins because the kernel is non-cumulative and the
//! induction's goal is an `Eq`.
//!
//! Also here: `ir_lz_init_mem_is_mem0`, discharging the globals-shadowing
//! hazard. `ir_init` concatenates globals in front of the caller heap and
//! lookup is first-match, so a global at a live address would shadow a caller
//! cell and void A2's premise. It is `Eq.refl` today and is registered so that
//! it **stops reducing** the moment an emitted body declares globals.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_FUELOUT_NE_RET_T: &str = "def ir_outcome_fuelout_ne_ret (v : IRList IRScalar) (C : Type) (h : Eq IROutcome IROutcome.fuel_out (IROutcome.ret v)) : C := Eq.substType IROutcome (fun (o : IROutcome) => IROutcome.rec (fun (_ : IROutcome) => Type) (fun (_ : IRList IRScalar) => C) (fun (_ : IRFault) => ConstFreeUnit) (fun (_ : IRFault) => ConstFreeUnit) (fun (_ : IRFault) => ConstFreeUnit) (fun (_ : IRFault) => ConstFreeUnit) ConstFreeUnit o) IROutcome.fuel_out (IROutcome.ret v) h ConstFreeUnit.triv";

const SRC_FUELOUT_NE_RET_P: &str = "def ir_outcome_fuelout_ne_ret_prop (v : IRList IRScalar) (C : Prop) (h : Eq IROutcome IROutcome.fuel_out (IROutcome.ret v)) : C := Eq.subst IROutcome (fun (o : IROutcome) => IROutcome.rec (fun (_ : IROutcome) => Prop) (fun (_ : IRList IRScalar) => C) (fun (_ : IRFault) => (Eq Nat Nat.zero Nat.zero)) (fun (_ : IRFault) => (Eq Nat Nat.zero Nat.zero)) (fun (_ : IRFault) => (Eq Nat Nat.zero Nat.zero)) (fun (_ : IRFault) => (Eq Nat Nat.zero Nat.zero)) (Eq Nat Nat.zero Nat.zero) o) IROutcome.fuel_out (IROutcome.ret v) h (Eq.refl Nat Nat.zero)";

const SRC_RUN_SUCC_RET: &str = "def ir_run_succ_ret (m : IRModule) (f : Nat) : forall (c : IRConfig) (v : IRList IRScalar), Eq IROutcome (ir_run f m c) (IROutcome.ret v) -> Eq IROutcome (ir_run (Nat.succ f) m c) (IROutcome.ret v) := Nat.rec (fun (k : Nat) => forall (c : IRConfig) (v : IRList IRScalar), Eq IROutcome (ir_run k m c) (IROutcome.ret v) -> Eq IROutcome (ir_run (Nat.succ k) m c) (IROutcome.ret v)) (fun (c : IRConfig) (v : IRList IRScalar) => IRConfig.rec (fun (c0 : IRConfig) => Eq IROutcome (ir_run Nat.zero m c0) (IROutcome.ret v) -> Eq IROutcome (ir_run (Nat.succ Nat.zero) m c0) (IROutcome.ret v)) (fun (s : IRMachine) (h : Eq IROutcome (ir_run Nat.zero m (IRConfig.running s)) (IROutcome.ret v)) => ir_outcome_fuelout_ne_ret_prop v (Eq IROutcome (ir_run (Nat.succ Nat.zero) m (IRConfig.running s)) (IROutcome.ret v)) h) (fun (o : IROutcome) (h : Eq IROutcome (ir_run Nat.zero m (IRConfig.halted o)) (IROutcome.ret v)) => h) c) (fun (k : Nat) (ih : forall (c : IRConfig) (v : IRList IRScalar), Eq IROutcome (ir_run k m c) (IROutcome.ret v) -> Eq IROutcome (ir_run (Nat.succ k) m c) (IROutcome.ret v)) (c : IRConfig) (v : IRList IRScalar) => IRConfig.rec (fun (c0 : IRConfig) => Eq IROutcome (ir_run (Nat.succ k) m c0) (IROutcome.ret v) -> Eq IROutcome (ir_run (Nat.succ (Nat.succ k)) m c0) (IROutcome.ret v)) (fun (s : IRMachine) => ih (ir_step m s) v) (fun (o : IROutcome) (h : Eq IROutcome (ir_run (Nat.succ k) m (IRConfig.halted o)) (IROutcome.ret v)) => h) c) f";

const SRC_RUN_LE_RET: &str = "def ir_run_le_ret (m : IRModule) (f : Nat) (g : Nat) (hle : Le f g) : forall (c : IRConfig) (v : IRList IRScalar), Eq IROutcome (ir_run f m c) (IROutcome.ret v) -> Eq IROutcome (ir_run g m c) (IROutcome.ret v) := Le.rec f (fun (g : Nat) (_hg : Le f g) => forall (c : IRConfig) (v : IRList IRScalar), Eq IROutcome (ir_run f m c) (IROutcome.ret v) -> Eq IROutcome (ir_run g m c) (IROutcome.ret v)) (fun (c : IRConfig) (v : IRList IRScalar) (h : Eq IROutcome (ir_run f m c) (IROutcome.ret v)) => h) (fun (g2 : Nat) (_h2 : Le f g2) (ih : forall (c : IRConfig) (v : IRList IRScalar), Eq IROutcome (ir_run f m c) (IROutcome.ret v) -> Eq IROutcome (ir_run g2 m c) (IROutcome.ret v)) (c : IRConfig) (v : IRList IRScalar) (h : Eq IROutcome (ir_run f m c) (IROutcome.ret v)) => ir_run_succ_ret m g2 c v (ih c v h)) g hle";

const SRC_INIT_MEM_IS_MEM0: &str = "def ir_lz_init_mem_is_mem0 : forall (mem : IRList IRMemSlot), Eq (IRList IRMemSlot) (ir_mem_concat (ir_globals_mem (ir_mod_globals ir_lz_module)) mem) mem := fun (mem : IRList IRMemSlot) => Eq.refl (IRList IRMemSlot) mem";

impl Specification {
    /// Fuel monotonicity, its discriminators, and the globals discharge.
    pub(super) fn add_eval_ir_fuel(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_FUELOUT_NE_RET_T, "ir_outcome_fuelout_ne_ret: fuel exhaustion is not a successful return, Type-motive variant. ir_run reports exhaustion as IROutcome.fuel_out, which its own description calls out as \"its OWN outcome, distinct from every real result, so no theorem can mistake it for success\". This is the declaration that makes that structural fact usable in a proof. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_FUELOUT_NE_RET_P, "ir_outcome_fuelout_ne_ret_prop: the same at a Prop motive. The kernel is non-cumulative, so the two motive universes need separate declarations -- and this is the one the fuel induction actually needs, because its goal is an Eq, which is Prop. Reaching for the Type variant there is a universe conflict, not a coercion. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_RUN_SUCC_RET, "ir_run_succ_ret: FUEL MONOTONICITY for the IR machine. If ir_run returns ret v at fuel f, it returns ret v at fuel succ f. \
\
Stated for SUCCESSFUL RETURNS on purpose: the unconditional form Eq (ir_run f m c) (ir_run (succ f) m c) is FALSE, because a run that exhausts at f may halt at succ f, and exhaustion is its own outcome. \
\
Nat.rec on the fuel generalised over the configuration, with an IRConfig.rec convoy in each arm. The zero/running case is where the discriminator earns its place -- there ir_run computes to fuel_out, and the hypothesis says that equals ret v. Every halted case is the identity because ir_run returns a halted outcome unchanged at any fuel. \
\
Without this, crystal A4's Le (ir_lz_fuel l) fuel premise is unusable: a forall-l theorem at fixed fuel is false, since steps grow with the size of l. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_RUN_LE_RET, "ir_run_le_ret: fuel monotonicity at a bound rather than a successor -- if the run succeeds at f and Le f g, it succeeds at g with the same result. Le.rec over the ordering, iterating ir_run_succ_ret. This is the exact shape A4's fuel premise supplies. \
\
Note Le's first argument is a PARAMETER, so Le.rec takes it before the motive and the motive ranges over the second argument plus the proof. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_INIT_MEM_IS_MEM0, "ir_lz_init_mem_is_mem0: the globals-shadowing hazard, DISCHARGED -- and left as an alarm. \
\
ir_init builds the machine's memory as ir_mem_concat (ir_globals_mem ...) mem0, and ir_mem_lookup is head-first first-match, so a global cell at the same address would SHADOW a caller cell and silently invalidate A2's representation premise. Today ir_lz_module declares no globals, so the concatenation is the identity and this is Eq.refl. \
\
That is exactly why it is worth registering rather than assuming: when A0 emits a body that does declare globals, this lemma STOPS REDUCING and the build fails, instead of the theorem quietly ceasing to be true. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Monotonicity must be stated for SUCCESSFUL returns. The unconditional
    /// form is false — a run that exhausts at f may halt at succ f — so if
    /// `IROutcome.ret` ever leaves this statement, the lemma has become wrong.
    #[test]
    fn test_monotonicity_is_restricted_to_returns() {
        assert!(SRC_RUN_SUCC_RET.contains("(IROutcome.ret v)"));
        assert!(SRC_RUN_LE_RET.contains("(IROutcome.ret v)"));
    }

    /// The zero/running case is the only one with content, and it must go
    /// through the discriminator — that is where fuel_out is refuted.
    #[test]
    fn test_exhaustion_is_refuted_not_assumed() {
        assert!(
            SRC_RUN_SUCC_RET.contains("ir_outcome_fuelout_ne_ret_prop"),
            "the Prop twin is required: the induction's goal is an Eq"
        );
    }

    /// Le's first argument is a parameter, so Le.rec takes it before the motive.
    #[test]
    fn test_le_rec_parameter_convention() {
        assert!(
            SRC_RUN_LE_RET.contains("Le.rec f "),
            "parameter comes first"
        );
    }

    /// The globals discharge must be Eq.refl — its value is that it STOPS
    /// reducing when an emitted body declares globals.
    #[test]
    fn test_globals_discharge_is_by_computation() {
        assert!(SRC_INIT_MEM_IS_MEM0.contains("Eq.refl"));
        assert!(SRC_INIT_MEM_IS_MEM0.contains("ir_globals_mem (ir_mod_globals ir_lz_module)"));
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [
            SRC_FUELOUT_NE_RET_T,
            SRC_FUELOUT_NE_RET_P,
            SRC_RUN_SUCC_RET,
            SRC_RUN_LE_RET,
            SRC_INIT_MEM_IS_MEM0,
        ] {
            let mut d: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => d += 1,
                    ')' => d -= 1,
                    _ => {}
                }
                assert!(d >= 0);
            }
            assert_eq!(d, 0, "unbalanced parens");
            assert!(src.is_ascii());
        }
    }
}
