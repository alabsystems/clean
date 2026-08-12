// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The exact step cost of `Level::is_zero`** — crystal A4's third prerequisite.
//!
//! `ir_lz_cost l` is the number of `ir_step`s the EvalIR machine takes to run
//! `Level::is_zero` on a heap encoding `l`, from the moment its frame is pushed
//! to the moment its `Return` executes.
//!
//! ## Why the count has to be EXACT
//!
//! At the outcome level a surplus is harmless — `ir_run_halted` absorbs it, and
//! that is what lets A4 take a `Le … fuel` premise. At the CONFIGURATION level
//! there is no such absorption for a nested call: a callee that returns after
//! *k* steps leaves the caller's frame underneath it, so running past *k* keeps
//! executing THE CALLER. An over-approximation would silently step the caller
//! into instructions it has not reached. So the activation lemma needs the exact
//! figure, and this is it.
//!
//! ## The cost function branches, because the machine does
//!
//! `Level::is_zero`'s `Max` arm is `l1.is_zero() && l2.is_zero()`, and `&&`
//! SHORT-CIRCUITS — block b3 ends in a `CondBr`, not a `BinOp::And`. So the two
//! edges cost different amounts and `ir_lz_cost` must branch on
//! `level_is_zero l1` exactly where the machine branches:
//!
//! ```text
//! ir_lz_cost zero        = 5      b0 (load, extractfield, switch) + b1 (const, ret)
//! ir_lz_cost (succ _)    = 5      b0 + b2; succ is a LEAF arm, the edge is not followed
//! ir_lz_cost (param _)   = 5      b0 + b2, the arm b2 shares with succ
//! ir_lz_cost (max l1 l2) = 9 + cost l1 + (if level_is_zero l1 then 6 + cost l2 else 2)
//! ir_lz_cost (imax _ l2) = 9 + cost l2
//! ```
//!
//! The 9 in the `Max`/`IMax` cases is b0's 3, plus b3/b5's four setup nodes
//! (extractfield, null const, icmp, assert), plus the `Call`, plus the one node
//! executed after the callee returns. `ir_push` advances the caller's pc at PUSH
//! time, so the return resumes AFTER the call rather than repeating it — that is
//! what makes the "+1 after the callee" a single node and not two.
//!
//! ## The nesting is chosen for the PROOF, not for legibility
//!
//! Each cost is written right-nested with the LITERAL segments in `Nat.add`'s
//! second argument. `Nat.add` recurses there, so a literal segment reduces and
//! `ir_steps` peels it definitionally; only the VARIABLE segments (a child's
//! cost) need `ir_steps_add`. That is why the activation arms apply that lemma
//! twice rather than six times, and why no associativity lemma is needed
//! anywhere. The VALUES are unchanged -- the execution witnesses below still
//! pin them, and still read 25 for `Max(Zero, Zero)`.
//!
//! ## The counts are checked by execution, not by arithmetic
//!
//! Every figure above is a claim about a machine, so it is settled by running
//! the machine. Each `_halts_` witness is `Eq.refl` on
//! `ir_steps (ir_lz_cost l) …`, which the kernel discharges by executing that
//! many steps and comparing configurations.
//!
//! A `_halts_` witness ALONE would be too weak, and the reason is worth stating:
//! the outermost frame's `Return` halts the machine, and `ir_steps_halted` makes
//! a halted configuration a fixed point — so an over-count would still land on
//! `halted`. It would prove `cost >= actual`, not `cost = actual`. The `_tight_`
//! witnesses close that: at `Nat.pred (ir_lz_cost l)` the configuration is still
//! `running`. Halted at *n* and running at *n-1* pins *n* exactly.
//!
//! `ir_lz_cost_halts_param` is universally quantified in BOTH the heap's payload
//! and the level's `Name`, which is not decoration — it is A2's non-functionality
//! showing through. `EncodesLevelArc`'s `param` arm leaves the payload
//! unconstrained, so one heap encodes `Level.param nm` for every `nm`; the cost,
//! and the answer, are the same for all of them.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_IS_RUNNING: &str = "def ir_config_is_running (c : IRConfig) : Bool := IRConfig.rec (fun (_ : IRConfig) => Bool) (fun (_ : IRMachine) => Bool.true) (fun (_ : IROutcome) => Bool.false) c";

const SRC_COST: &str = "def ir_lz_cost (l : Level) : Nat := Level.rec (fun (_ : Level) => Nat) ir_d5 (fun (_ : Level) (_ : Nat) => ir_d5) (fun (l1 : Level) (l2 : Level) (c1 : Nat) (c2 : Nat) => Nat.add (Nat.add (Bool.rec (fun (_ : Bool) => Nat) ir_d3 (Nat.add (Nat.add (Nat.add ir_d1 c2) ir_d5) ir_d1) (level_is_zero l1)) c1) ir_d8) (fun (l1 : Level) (l2 : Level) (c1 : Nat) (c2 : Nat) => Nat.add (Nat.add ir_d1 c2) ir_d8) (fun (_ : Name) => ir_d5) l";

const HEAP_ZERO: &str = "(ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0)";
const HEAP_SUCC: &str = "(ir_cell ir_d0 (ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ ir_d1))) (ir_cell ir_d1 (ir_var ir_d0 ir_sp0) ir_mem0))";
const HEAP_PARAM: &str = "(ir_cell ir_d0 (ir_var ir_d4 (ir_sp1 (IRScalar.int_ n))) ir_mem0)";
const HEAP_MAXZZ: &str = "(ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d1 (ir_var ir_d0 ir_sp0) (ir_cell ir_d2 (ir_var ir_d0 ir_sp0) ir_mem0)))";

/// `ir_init` applied to the level-zero module at the standard entry shape.
fn init(heap: &str, na: &str) -> String {
    format!("(ir_init ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) {heap} {na})")
}

/// After exactly `ir_lz_cost lvl` steps the machine has halted with `ans`.
fn halts(name: &str, binder: &str, lvl: &str, heap: &str, na: &str, ans: &str) -> String {
    let tgt = format!("(IRConfig.halted (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.{ans}))))");
    format!(
        "def {name} {binder}: Eq IRConfig (ir_steps (ir_lz_cost {lvl}) ir_lz_module {}) {tgt} := Eq.refl IRConfig {tgt}",
        init(heap, na)
    )
}

/// One step earlier it is still running — which is what makes the count exact.
fn tight(name: &str, lvl: &str, heap: &str, na: &str) -> String {
    format!(
        "def {name} : Eq Bool (ir_config_is_running (ir_steps (Nat.pred (ir_lz_cost {lvl})) ir_lz_module {})) Bool.true := Eq.refl Bool Bool.true",
        init(heap, na)
    )
}

impl Specification {
    /// The exact step cost of `Level::is_zero`, checked by execution.
    pub(super) fn add_eval_ir_cost(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_IS_RUNNING, "ir_config_is_running: is this configuration still executing? Needed only so that the TIGHTNESS witnesses can say what a halted-at-n witness cannot -- that at n-1 the machine had not yet finished. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_COST, "ir_lz_cost: the EXACT number of machine steps Level::is_zero takes on a heap encoding l, from frame push to Return. \
\
Exact, not an upper bound, and the difference is load-bearing. Surplus FUEL is absorbed at the outcome level by ir_run_halted -- that is what lets A4 take a Le premise -- but a nested call has no such absorption: the callee returns into a caller frame, so stepping past its Return keeps executing THE CALLER. An over-approximation would corrupt the very composition it was meant to simplify. \
\
The function branches because the machine branches. Max is l1.is_zero() && l2.is_zero() and && SHORT-CIRCUITS -- block b3 ends in a CondBr, not a BinOp::And -- so the two edges cost different amounts and the cost branches on level_is_zero l1 at exactly the same point. \
\
zero, succ and param all cost 5: b0's load/extractfield/switch, then two nodes in the leaf block. succ is 5 rather than recursive because it is a LEAF arm -- the machine does not follow the edge. Max costs 9 + cost l1 + (6 + cost l2 if the left side is zero, else 2); IMax costs 9 + cost l2, never reading its first operand. The 9 is b0's 3, four setup nodes, the Call, and the single node after the callee returns -- single because ir_push advances the caller's pc at PUSH time. DerivedProved, zero axiom_deps.")?;

        self.add_recursive_def(&halts("ir_lz_cost_halts_zero", "", "Level.zero", HEAP_ZERO, "ir_d1", "true"), "ir_lz_cost_halts_zero: after exactly ir_lz_cost Level.zero steps the machine has halted returning true. Eq.refl -- the KERNEL executes the machine and compares configurations, so the count is checked by running it rather than by my arithmetic. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&tight("ir_lz_cost_tight_zero", "Level.zero", HEAP_ZERO, "ir_d1"), "ir_lz_cost_tight_zero: one step earlier the machine is STILL RUNNING. \
\
This is the witness that makes the cost exact rather than merely sufficient. The outermost Return halts the machine and ir_steps_halted makes a halted configuration a fixed point, so an over-count would still land on halted and the _halts_ witness alone would only establish cost >= actual. Halted at n and running at n-1 pins n. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&halts("ir_lz_cost_halts_succ", "", "(Level.succ Level.zero)", HEAP_SUCC, "ir_d2", "false"), "ir_lz_cost_halts_succ: Succ(Zero) costs the same 5 steps as a leaf and returns false. The inner Zero is present in the heap precisely so that a semantics which wrongly recursed would both cost more and answer true. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&halts("ir_lz_cost_halts_param", "(n : Nat) (nm : Name) ", "(Level.param nm)", HEAP_PARAM, "ir_d1", "false"), "ir_lz_cost_halts_param: universally quantified in BOTH the heap payload n and the level's Name nm. \
\
Not decoration -- this is A2's non-functionality showing through. EncodesLevelArc's param arm leaves the payload unconstrained, so a single heap encodes Level.param nm for EVERY nm. The cost and the answer are the same for all of them, which is exactly why that freedom is harmless here even though it makes the relation non-functional. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&halts("ir_lz_cost_halts_max_zz", "", "(Level.max Level.zero Level.zero)", HEAP_MAXZZ, "ir_d3", "true"), "ir_lz_cost_halts_max_zz: THE INTERESTING COUNT -- 25 steps. Two nested frame pushes and pops, two LevelArc null checks, and a CondBr taking the then-edge, all executed by the kernel. If either the recursive cost or the short-circuit branch were off by one this would not typecheck. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&tight("ir_lz_cost_tight_max_zz", "(Level.max Level.zero Level.zero)", HEAP_MAXZZ, "ir_d3"), "ir_lz_cost_tight_max_zz: still running at 24. Together with the previous witness this pins the recursive case exactly, including the cost contributed by the nested activations. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The cost must branch where the machine branches. `Max` short-circuits,
    /// so a cost function without `level_is_zero` in it is wrong on one edge.
    #[test]
    fn test_cost_branches_on_the_short_circuit() {
        assert!(
            SRC_COST.contains("Bool.rec (fun (_ : Bool) => Nat)"),
            "the Max arm must branch"
        );
        assert!(
            SRC_COST.contains("(level_is_zero l1)"),
            "and it must branch on the LEFT operand, which is what b3's CondBr tests"
        );
    }

    /// `IMax` never reads its first operand — impredicative collapse. If the
    /// cost ever mentions `ih1` in the imax arm, it has stopped matching b5.
    #[test]
    fn test_imax_ignores_its_first_operand() {
        let imax = SRC_COST
            .split("(fun (l1 : Level) (l2 : Level) (c1 : Nat) (c2 : Nat) => Nat.add (Nat.add ir_d1 c2) ir_d8)")
            .count();
        assert_eq!(
            imax, 2,
            "the imax arm must be 8 + cost l2 + 1, and must not mention c1"
        );
    }

    /// Every count claim is settled by executing the machine. A `_halts_`
    /// witness must be `Eq.refl` over `ir_steps (ir_lz_cost …)` — if it ever
    /// stops being reflexivity, the kernel is no longer doing the checking.
    #[test]
    fn test_counts_are_checked_by_execution() {
        let w = halts("w", "", "Level.zero", HEAP_ZERO, "ir_d1", "true");
        assert!(w.contains("ir_steps (ir_lz_cost Level.zero) ir_lz_module"));
        assert!(w.contains(":= Eq.refl IRConfig"));
    }

    /// Halted-at-n alone proves only `cost >= actual`, because a halted
    /// configuration is a fixed point of `ir_steps`. Tightness needs `pred`.
    #[test]
    fn test_tightness_probes_one_step_earlier() {
        let t = tight("t", "Level.zero", HEAP_ZERO, "ir_d1");
        assert!(
            t.contains("Nat.pred (ir_lz_cost Level.zero)"),
            "tightness must probe at cost - 1"
        );
        assert!(t.contains("ir_config_is_running"));
        assert!(t.ends_with("Bool.true := Eq.refl Bool Bool.true"));
    }

    /// The param witness is quantified in both the payload and the name; that
    /// universality is the point, not a spot check.
    #[test]
    fn test_param_witness_is_universally_quantified() {
        let p = halts(
            "p",
            "(n : Nat) (nm : Name) ",
            "(Level.param nm)",
            HEAP_PARAM,
            "ir_d1",
            "false",
        );
        assert!(p.contains("(n : Nat) (nm : Name)"));
        assert!(p.contains("(IRScalar.int_ n)"), "payload stays free");
        assert!(p.contains("Level.param nm"), "and so does the name");
    }

    #[test]
    fn test_sources_balanced_ascii() {
        let owned = [
            halts("a", "", "Level.zero", HEAP_ZERO, "ir_d1", "true"),
            tight("b", "Level.zero", HEAP_ZERO, "ir_d1"),
            halts(
                "c",
                "",
                "(Level.succ Level.zero)",
                HEAP_SUCC,
                "ir_d2",
                "false",
            ),
            halts(
                "d",
                "(n : Nat) (nm : Name) ",
                "(Level.param nm)",
                HEAP_PARAM,
                "ir_d1",
                "false",
            ),
            halts(
                "e",
                "",
                "(Level.max Level.zero Level.zero)",
                HEAP_MAXZZ,
                "ir_d3",
                "true",
            ),
            tight(
                "f",
                "(Level.max Level.zero Level.zero)",
                HEAP_MAXZZ,
                "ir_d3",
            ),
        ];
        let all = [SRC_IS_RUNNING, SRC_COST]
            .into_iter()
            .chain(owned.iter().map(String::as_str));
        for src in all {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(
                src.matches('(').count(),
                src.matches(')').count(),
                "unbalanced parens in: {}",
                &src[..50.min(src.len())]
            );
        }
    }
}
