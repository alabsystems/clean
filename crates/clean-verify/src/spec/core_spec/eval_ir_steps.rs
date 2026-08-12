// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The configuration-level iterator** — crystal A4's second prerequisite.
//!
//! `ir_run` collapses a machine straight to an `IROutcome` and ERASES every
//! intermediate configuration. That is fine for a whole-program claim, but A4's
//! proof is an induction over `Level` whose recursive cases sit at `Call` nodes
//! inside `Level::is_zero` (blocks b3, b4, b5 each self-call function 0). To use
//! the induction hypothesis there, one has to say
//!
//! > after *k* steps the machine is back in the CALLER's frame with the call's
//! > result id bound to the callee's answer
//!
//! and that sentence mentions a configuration, not an outcome. It is not
//! expressible against `ir_run` at all. `ir_steps` is the same recursion with
//! the outcome projection removed, so the statement becomes available:
//!
//! ```text
//! ir_steps 0        m c = c
//! ir_steps (succ k) m (running s)  = ir_steps k m (ir_step m s)
//! ir_steps (succ k) m (halted o)   = halted o
//! ```
//!
//! ## Faithfulness is the whole point, so it is proved, not asserted
//!
//! A second iterator is only useful if it is the SAME machine. `ir_run_of_steps`
//! pins that: `ir_run f m c = ir_config_outcome (ir_steps f m c)`, where
//! `ir_config_outcome` maps a still-running configuration to `fuel_out` and a
//! halted one to its outcome — precisely `ir_run`'s zero case. So `ir_steps`
//! cannot drift from `ir_run` without this equation failing to typecheck.
//!
//! `ir_run_steps_split` is the form the activation lemma will consume:
//! `ir_run (Nat.add g f) m c = ir_run g m (ir_steps f m c)`. Note the argument
//! order — `Nat.add` recurses on its SECOND argument, so the step count has to
//! sit there or the base case stops reducing.
//!
//! ## An over-approximated step count will NOT do at this level
//!
//! For `ir_run`, surplus fuel is harmless: once halted, extra fuel is absorbed
//! (`ir_run_halted`), which is what makes the `Le` premise of A4 work. At the
//! CONFIGURATION level that absorption does not exist — a callee that returns
//! after *k* steps leaves a caller frame underneath, and running past *k* keeps
//! executing THE CALLER. So the activation lemma needs an exact cost, and since
//! `Max` short-circuits, the cost function must itself branch on
//! `level_is_zero l1`. `ir_steps_halted` is the one absorption that does survive
//! here, and only because a halted configuration has no frames left to resume.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_CONFIG_OUTCOME: &str = "def ir_config_outcome (c : IRConfig) : IROutcome := IRConfig.rec (fun (_ : IRConfig) => IROutcome) (fun (_ : IRMachine) => IROutcome.fuel_out) (fun (o : IROutcome) => o) c";

const SRC_STEPS: &str = "def ir_steps (fuel : Nat) (m : IRModule) (c : IRConfig) : IRConfig := Nat.rec (fun (_ : Nat) => IRConfig -> IRConfig) (fun (c0 : IRConfig) => c0) (fun (_ : Nat) (ih : IRConfig -> IRConfig) => fun (c0 : IRConfig) => IRConfig.rec (fun (_ : IRConfig) => IRConfig) (fun (s : IRMachine) => ih (ir_step m s)) (fun (o : IROutcome) => IRConfig.halted o) c0) fuel c";

const SRC_RUN_HALTED: &str = "def ir_run_halted (m : IRModule) (o : IROutcome) (g : Nat) : Eq IROutcome (ir_run g m (IRConfig.halted o)) o := Nat.rec (fun (k : Nat) => Eq IROutcome (ir_run k m (IRConfig.halted o)) o) (Eq.refl IROutcome o) (fun (k : Nat) (_ih : Eq IROutcome (ir_run k m (IRConfig.halted o)) o) => Eq.refl IROutcome o) g";

const SRC_STEPS_HALTED: &str = "def ir_steps_halted (m : IRModule) (o : IROutcome) (f : Nat) : Eq IRConfig (ir_steps f m (IRConfig.halted o)) (IRConfig.halted o) := Nat.rec (fun (k : Nat) => Eq IRConfig (ir_steps k m (IRConfig.halted o)) (IRConfig.halted o)) (Eq.refl IRConfig (IRConfig.halted o)) (fun (k : Nat) (_ih : Eq IRConfig (ir_steps k m (IRConfig.halted o)) (IRConfig.halted o)) => Eq.refl IRConfig (IRConfig.halted o)) f";

const SRC_RUN_OF_STEPS: &str = "def ir_run_of_steps (m : IRModule) (f : Nat) : forall (c : IRConfig), Eq IROutcome (ir_run f m c) (ir_config_outcome (ir_steps f m c)) := Nat.rec (fun (k : Nat) => forall (c : IRConfig), Eq IROutcome (ir_run k m c) (ir_config_outcome (ir_steps k m c))) (fun (c : IRConfig) => Eq.refl IROutcome (ir_run Nat.zero m c)) (fun (k : Nat) (ih : forall (c : IRConfig), Eq IROutcome (ir_run k m c) (ir_config_outcome (ir_steps k m c))) => fun (c : IRConfig) => IRConfig.rec (fun (c0 : IRConfig) => Eq IROutcome (ir_run (Nat.succ k) m c0) (ir_config_outcome (ir_steps (Nat.succ k) m c0))) (fun (s : IRMachine) => ih (ir_step m s)) (fun (o : IROutcome) => Eq.refl IROutcome o) c) f";

const SRC_RUN_STEPS_SPLIT: &str = "def ir_run_steps_split (m : IRModule) (g : Nat) (f : Nat) : forall (c : IRConfig), Eq IROutcome (ir_run (Nat.add g f) m c) (ir_run g m (ir_steps f m c)) := Nat.rec (fun (k : Nat) => forall (c : IRConfig), Eq IROutcome (ir_run (Nat.add g k) m c) (ir_run g m (ir_steps k m c))) (fun (c : IRConfig) => Eq.refl IROutcome (ir_run g m c)) (fun (k : Nat) (ih : forall (c : IRConfig), Eq IROutcome (ir_run (Nat.add g k) m c) (ir_run g m (ir_steps k m c))) => fun (c : IRConfig) => IRConfig.rec (fun (c0 : IRConfig) => Eq IROutcome (ir_run (Nat.add g (Nat.succ k)) m c0) (ir_run g m (ir_steps (Nat.succ k) m c0))) (fun (s : IRMachine) => ih (ir_step m s)) (fun (o : IROutcome) => Eq.symm IROutcome (ir_run g m (IRConfig.halted o)) o (ir_run_halted m o g)) c) f";

const SRC_STEPS_ADD: &str = "def ir_steps_add (m : IRModule) (b : Nat) (a : Nat) : forall (c : IRConfig), Eq IRConfig (ir_steps (Nat.add b a) m c) (ir_steps b m (ir_steps a m c)) := Nat.rec (fun (k : Nat) => forall (c : IRConfig), Eq IRConfig (ir_steps (Nat.add b k) m c) (ir_steps b m (ir_steps k m c))) (fun (c : IRConfig) => Eq.refl IRConfig (ir_steps b m c)) (fun (k : Nat) (ih : forall (c : IRConfig), Eq IRConfig (ir_steps (Nat.add b k) m c) (ir_steps b m (ir_steps k m c))) => fun (c : IRConfig) => IRConfig.rec (fun (c0 : IRConfig) => Eq IRConfig (ir_steps (Nat.add b (Nat.succ k)) m c0) (ir_steps b m (ir_steps (Nat.succ k) m c0))) (fun (s : IRMachine) => ih (ir_step m s)) (fun (o : IROutcome) => Eq.symm IRConfig (ir_steps b m (IRConfig.halted o)) (IRConfig.halted o) (ir_steps_halted m o b)) c) a";

impl Specification {
    /// The configuration-level iterator and its faithfulness to `ir_run`.
    pub(super) fn add_eval_ir_steps(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_CONFIG_OUTCOME, "ir_config_outcome: read an outcome off a configuration -- fuel_out if it is still running, its own outcome if it has halted. This is exactly ir_run's ZERO case, factored out, which is what lets ir_run_of_steps state that the iterator and the runner are the same machine. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_STEPS, "ir_steps: iterate ir_step at the CONFIGURATION level, keeping the machine instead of projecting an outcome. \
\
ir_run erases every intermediate configuration, so a compositional claim -- after k steps the machine is back in the caller's frame with the call's result id bound -- is not merely hard to prove against it, it is not STATABLE against it. A4's induction over Level has its recursive cases at the Call nodes in blocks b3/b4/b5 of Level::is_zero, so it needs exactly that sentence. \
\
Same recursion as ir_run with the projection removed: zero is the identity, succ steps a running machine and leaves a halted one alone. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_RUN_HALTED, "ir_run_halted: a halted configuration returns its outcome at ANY fuel. Nat.rec on the fuel; both arms are Eq.refl and neither needs the induction hypothesis, because ir_run's zero and succ cases agree on halted. This is the absorption that makes surplus fuel harmless at the OUTCOME level -- and the reason A4 can take a Le premise rather than an exact count. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_STEPS_HALTED, "ir_steps_halted: a halted configuration is a fixed point of the iterator. \
\
Note how much weaker this is than ir_run_halted's absorption: it holds only because a HALTED configuration has no frames left to resume into. A still-running callee that has just returned does have a caller underneath, and stepping past its return keeps executing THE CALLER. That is why the activation lemma cannot use an over-approximated step count the way A4's fuel premise can. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_RUN_OF_STEPS, "ir_run_of_steps: THE FAITHFULNESS EQUATION. ir_run f m c = ir_config_outcome (ir_steps f m c). \
\
A second iterator is worth nothing unless it is the same machine, and this is what pins it: ir_steps cannot drift from ir_run without this equation failing to typecheck. Nat.rec on the fuel with an IRConfig.rec convoy; the zero arm is Eq.refl because ir_run's zero case IS ir_config_outcome, and the succ/halted arm is Eq.refl because both sides compute to the outcome. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_STEPS_ADD, "ir_steps_add: composition for the configuration iterator. ir_steps (Nat.add b a) m c = ir_steps b m (ir_steps a m c). \
\
This is what lets the activation lemma be assembled from segments -- run to the Call, apply the induction hypothesis for the callee, run the one node after it returns -- instead of being one monolithic computation. \
\
Induct on a, not on b: ir_steps peels from the FRONT of its fuel, so only the leading segment can be stripped a step at a time. Nat.add recurses on its second argument, which is why a sits there. The succ/halted arm needs Eq.symm over ir_steps_halted. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_RUN_STEPS_SPLIT, "ir_run_steps_split: run the first f steps as a configuration transformer, then finish. ir_run (Nat.add g f) m c = ir_run g m (ir_steps f m c). \
\
This is the shape the activation lemma consumes: it converts a fact about where the machine IS after a known number of steps into a fact about what it RETURNS. \
\
Argument order is forced, not stylistic. Nat.add recurses on its SECOND argument, so the step count f must sit there; with the arguments swapped, Nat.add g Nat.zero stops reducing to g and the base case dies. The succ/halted arm needs Eq.symm over ir_run_halted, because the induction leaves the equation pointing the other way. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The iterator must keep configurations. If it ever projects to an
    /// `IROutcome`, it has become `ir_run` again and A4's induction loses the
    /// only statement it can use at a `Call` node.
    #[test]
    fn test_iterator_returns_a_configuration() {
        assert!(SRC_STEPS.contains("(c : IRConfig) : IRConfig"));
        assert!(
            SRC_STEPS.contains("(fun (o : IROutcome) => IRConfig.halted o)"),
            "the halted case must re-wrap, not project"
        );
    }

    /// Faithfulness is the reason a second iterator is allowed to exist.
    #[test]
    fn test_faithfulness_equation_relates_both_machines() {
        assert!(SRC_RUN_OF_STEPS.contains("ir_run k m c"));
        assert!(SRC_RUN_OF_STEPS.contains("ir_config_outcome (ir_steps k m c)"));
    }

    /// `Nat.add` recurses on its second argument, so the step count has to be
    /// there. Swapping the arguments breaks the base case silently — it stops
    /// reducing rather than becoming false — so pin the order.
    #[test]
    fn test_split_puts_the_step_count_second() {
        assert!(
            SRC_RUN_STEPS_SPLIT.contains("ir_run (Nat.add g f) m c"),
            "step count must be Nat.add's second argument"
        );
        assert!(
            SRC_RUN_STEPS_SPLIT.contains("Eq.symm IROutcome"),
            "the succ/halted arm needs the equation reversed"
        );
    }

    /// `ir_run_halted` absorbs surplus fuel; `ir_steps_halted` does NOT absorb
    /// surplus steps in general — it holds only at a halted configuration.
    /// Keep both, and keep them distinct.
    #[test]
    fn test_absorption_is_stated_at_both_levels() {
        assert!(SRC_RUN_HALTED.contains("Eq IROutcome (ir_run g m (IRConfig.halted o)) o"));
        assert!(SRC_STEPS_HALTED
            .contains("Eq IRConfig (ir_steps f m (IRConfig.halted o)) (IRConfig.halted o)"));
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [
            SRC_CONFIG_OUTCOME,
            SRC_STEPS,
            SRC_RUN_HALTED,
            SRC_STEPS_HALTED,
            SRC_RUN_OF_STEPS,
            SRC_RUN_STEPS_SPLIT,
            SRC_STEPS_ADD,
        ] {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            let opens = src.matches('(').count();
            let closes = src.matches(')').count();
            assert_eq!(opens, closes, "unbalanced parens in: {}", &src[..60]);
        }
    }
}
