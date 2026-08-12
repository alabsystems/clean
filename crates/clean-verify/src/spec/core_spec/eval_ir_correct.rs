// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A4 — the equality theorem.**
//!
//! ```text
//! ir_lz_correct : forall mem fuel na r l,
//!     EncodesLiveLevelRef mem r l ->
//!     Le (ir_lz_cost l) fuel ->
//!     ir_eval fuel ir_lz_module 0 [r] mem na
//!       = IROutcome.ret [IRScalar.bool_ (level_is_zero l)]
//! ```
//!
//! For EVERY reflected `Level`, every heap that represents it, every next-address
//! counter, and every fuel at or above the cost, running `M_level_is_zero` on the
//! EvalIR machine returns exactly what the reflected `level_is_zero` says. Not a
//! sample of levels: the theorem is quantified over `Level` and proved by
//! induction on the representation derivation.
//!
//! ## The two quantifiers that make it worth having
//!
//! **Over the heap.** `mem` is arbitrary and constrained only through
//! `ir_mem_lookup` equations. The machine may be handed a heap with unrelated
//! cells, shared sub-levels (the relation is a DAG, not a tree), and dead cells
//! elsewhere. A2's decision to phrase representation as a lookup EQUATION rather
//! than list membership is what makes this sound — membership would be satisfied
//! by a shadowed duplicate while the machine reads a different cell.
//!
//! **Over the fuel.** The `Le` premise is not cosmetic: a fixed-fuel statement
//! would be false, since steps grow with `|l|`. It is discharged by
//! `ir_run_le_ret`, and that lemma is only true because exhaustion is its own
//! outcome and can be refuted rather than merely distinguished.
//!
//! ## How the pieces meet
//!
//! `ir_lz_activation` is the induction, over `EncodesLevelArc`. Each arm hands
//! off to a machine-level lemma proved in `eval_ir_activation`: the three leaves
//! directly, and `max`/`imax` through the segment lemmas. The `max` arm needs a
//! CONVOY — `Bool.rec` with a motive carrying `level_is_zero l1 = v` — because
//! both the cost and the answer depend on the left operand's value, and that is
//! exactly the short-circuit the machine performs.
//!
//! A4 itself is then short. `ir_init` on this module is DEFINITIONALLY the
//! activation's starting machine with no caller: `ir_lz_module` declares no
//! globals, so `ir_mem_concat` is the identity on the caller heap, and the
//! outermost frame has empty return destinations, so its `Return` halts. That
//! makes `ir_ret_to` collapse to `halted (ret v)`, `ir_run_of_steps` converts the
//! configuration statement into an outcome statement, and `ir_run_le_ret`
//! weakens the exact cost to the `Le` premise.
//!
//! ## What this does and does not license
//!
//! `ir_lz_module` is HAND-AUTHORED, not emitted — see `eval_ir_crystal`. So this
//! is a theorem about a module that MIRRORS `Level::is_zero`, and the remaining
//! obligation is job A0/A1: that the compiler emits this module, pinned by an
//! artifact digest. A4 is the half that says *if the emitted IR is this, the
//! semantics agree with the kernel function*. It is not by itself a statement
//! about the shipped binary.
//!
//! ## A5 — from agreement to mathematics
//!
//! `ir_lz_machine_sound` composes A4 with `level_is_zero_sound`: if the MACHINE
//! answers true, then `forall rho, level_eval rho l = 0`. A4 alone says two
//! programs agree; A5 says the running machine's answer entails a denotational
//! fact about universe levels.
//!
//! It is ONE-DIRECTIONAL and must stay so. A `Param` may be zero under some
//! assignment while `level_is_zero` answers false — `Level::is_zero` means
//! DEFINITELY zero — and the machine inherits that asymmetry exactly.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_MACH0_S: &str = "def ir_lz_mach0_s (mem : IRList IRMemSlot) (p : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 p) (IRList.nil IRBinding)) dests) rest) mem na";

const SRC_ACTIVATION: &str = "def ir_lz_activation (mem : IRList IRMemSlot) (s : IRScalar) (l : Level) (d : EncodesLevelArc mem s l) : forall (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame), Eq IRConfig (ir_steps (ir_lz_cost l) ir_lz_module (IRConfig.running (ir_lz_mach0_s mem s na dests rest))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ (level_is_zero l)))) := EncodesLevelArc.rec mem (fun (s0 : IRScalar) (l0 : Level) (_ : EncodesLevelArc mem s0 l0) => forall (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame), Eq IRConfig (ir_steps (ir_lz_cost l0) ir_lz_module (IRConfig.running (ir_lz_mach0_s mem s0 na dests rest))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ (level_is_zero l0))))) (fun (a : Nat) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 ir_sp0) Bool.true))) => fun (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) => ir_lz_activation_zero mem a na dests rest h) (fun (a : Nat) (b : Nat) (l0 : Level) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ b))) Bool.true))) (_arc : EncodesLevelArc mem (IRScalar.ptr_ b) l0) (_ihb : forall (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame), Eq IRConfig (ir_steps (ir_lz_cost l0) ir_lz_module (IRConfig.running (ir_lz_mach0_s mem (IRScalar.ptr_ b) na dests rest))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ (level_is_zero l0))))) => fun (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) => ir_lz_activation_succ mem a na dests rest b h) (fun (a : Nat) (b1 : Nat) (b2 : Nat) (l1 : Level) (l2 : Level) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))) (_arc1 : EncodesLevelArc mem (IRScalar.ptr_ b1) l1) (_arc2 : EncodesLevelArc mem (IRScalar.ptr_ b2) l2) (ih1 : forall (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame), Eq IRConfig (ir_steps (ir_lz_cost l1) ir_lz_module (IRConfig.running (ir_lz_mach0_s mem (IRScalar.ptr_ b1) na dests rest))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ (level_is_zero l1))))) (ih2 : forall (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame), Eq IRConfig (ir_steps (ir_lz_cost l2) ir_lz_module (IRConfig.running (ir_lz_mach0_s mem (IRScalar.ptr_ b2) na dests rest))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ (level_is_zero l2))))) => fun (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) => Bool.rec (fun (v : Bool) => Eq Bool (level_is_zero l1) v -> Eq IRConfig (ir_steps (Nat.add (Nat.add (Bool.rec (fun (_ : Bool) => Nat) ir_d3 (Nat.add (Nat.add (Nat.add ir_d1 (ir_lz_cost l2)) ir_d5) ir_d1) v) (ir_lz_cost l1)) ir_d8) ir_lz_module (IRConfig.running (ir_lz_mach0_s mem (IRScalar.ptr_ a) na dests rest))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ (Bool.and v (level_is_zero l2)))))) (fun (hf : Eq Bool (level_is_zero l1) Bool.false) => ir_lz_max_false_seg mem a b1 b2 (ir_lz_cost l1) na dests rest h (fun (na2 : Nat) (d2 : IRList Nat) (r2 : IRList IRFrame) => Eq.subst Bool (fun (bv : Bool) => Eq IRConfig (ir_steps (ir_lz_cost l1) ir_lz_module (IRConfig.running (ir_lz_mach0_s mem (IRScalar.ptr_ b1) na2 d2 r2))) (ir_ret_to d2 r2 mem na2 (ir_vl1 (IRScalar.bool_ bv)))) (level_is_zero l1) Bool.false hf (ih1 na2 d2 r2))) (fun (ht : Eq Bool (level_is_zero l1) Bool.true) => ir_lz_max_true_seg mem a b1 b2 (ir_lz_cost l1) (ir_lz_cost l2) (level_is_zero l2) na dests rest h (fun (na2 : Nat) (d2 : IRList Nat) (r2 : IRList IRFrame) => Eq.subst Bool (fun (bv : Bool) => Eq IRConfig (ir_steps (ir_lz_cost l1) ir_lz_module (IRConfig.running (ir_lz_mach0_s mem (IRScalar.ptr_ b1) na2 d2 r2))) (ir_ret_to d2 r2 mem na2 (ir_vl1 (IRScalar.bool_ bv)))) (level_is_zero l1) Bool.true ht (ih1 na2 d2 r2)) ih2) (level_is_zero l1) (Eq.refl Bool (level_is_zero l1))) (fun (a : Nat) (b1 : Nat) (b2 : Nat) (l1 : Level) (l2 : Level) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))) (_arc1 : EncodesLevelArc mem (IRScalar.ptr_ b1) l1) (_arc2 : EncodesLevelArc mem (IRScalar.ptr_ b2) l2) (_ih1 : forall (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame), Eq IRConfig (ir_steps (ir_lz_cost l1) ir_lz_module (IRConfig.running (ir_lz_mach0_s mem (IRScalar.ptr_ b1) na dests rest))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ (level_is_zero l1))))) (ih2 : forall (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame), Eq IRConfig (ir_steps (ir_lz_cost l2) ir_lz_module (IRConfig.running (ir_lz_mach0_s mem (IRScalar.ptr_ b2) na dests rest))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ (level_is_zero l2))))) => fun (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) => ir_lz_imax_seg mem a b1 b2 (ir_lz_cost l2) (level_is_zero l2) na dests rest h ih2) (fun (a : Nat) (w : IRScalar) (nm : Name) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 (ir_sp1 w)) Bool.true))) => fun (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) => ir_lz_activation_param mem a na dests rest w h) s l d";

const SRC_CORRECT: &str = "def ir_lz_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) (href : EncodesLiveLevelRef mem r l) : Le (ir_lz_cost l) fuel -> Eq IROutcome (ir_eval fuel ir_lz_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l)))) := EncodesLiveLevelRef.rec mem (fun (s0 : IRScalar) (l1 : Level) (_ : EncodesLiveLevelRef mem s0 l1) => Le (ir_lz_cost l1) fuel -> Eq IROutcome (ir_eval fuel ir_lz_module ir_d0 (ir_vl1 s0) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l1))))) (fun (a : Nat) (l0 : Level) (arc : EncodesLevelArc mem (IRScalar.ptr_ a) l0) (hle : Le (ir_lz_cost l0) fuel) => ir_run_le_ret ir_lz_module (ir_lz_cost l0) fuel hle (ir_init ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ a)) mem na) (ir_vl1 (IRScalar.bool_ (level_is_zero l0))) (Eq.trans IROutcome (ir_run (ir_lz_cost l0) ir_lz_module (ir_init ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ a)) mem na)) (ir_config_outcome (ir_steps (ir_lz_cost l0) ir_lz_module (ir_init ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ a)) mem na))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l0)))) (ir_run_of_steps ir_lz_module (ir_lz_cost l0) (ir_init ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ a)) mem na)) (Eq.subst IRConfig (fun (k : IRConfig) => Eq IROutcome (ir_config_outcome k) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l0))))) (ir_ret_to (IRList.nil Nat) (IRList.nil IRFrame) mem na (ir_vl1 (IRScalar.bool_ (level_is_zero l0)))) (ir_steps (ir_lz_cost l0) ir_lz_module (ir_init ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ a)) mem na)) (Eq.symm IRConfig (ir_steps (ir_lz_cost l0) ir_lz_module (ir_init ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ a)) mem na)) (ir_ret_to (IRList.nil Nat) (IRList.nil IRFrame) mem na (ir_vl1 (IRScalar.bool_ (level_is_zero l0)))) (ir_lz_activation mem (IRScalar.ptr_ a) l0 arc na (IRList.nil Nat) (IRList.nil IRFrame))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l0)))))))) r l href";

const SRC_SCALAR_BOOL: &str = "def ir_scalar_bool (s : IRScalar) : Bool := IRScalar.rec (fun (_ : IRScalar) => Bool) Bool.false (fun (b : Bool) => b) (fun (_ : Nat) => Bool.false) (fun (_ : Nat) => Bool.false) Bool.false (fun (_ : Nat) => Bool.false) Bool.false (fun (_ : Nat) (_ : Nat) => Bool.false) (fun (_ : Nat) => Bool.false) (fun (_ : IRScalar) (_ : Bool) => Bool.false) Bool.false (fun (_ : IRScalar) (_ : IRScalar) (_ : Bool) (_ : Bool) => Bool.false) s";

const SRC_VALS_HEAD_BOOL: &str = "def ir_vals_head_bool (v : IRList IRScalar) : Bool := IRList.rec IRScalar (fun (_ : IRList IRScalar) => Bool) Bool.false (fun (x : IRScalar) (_ : IRList IRScalar) (_ : Bool) => ir_scalar_bool x) v";

const SRC_OUTCOME_BOOL: &str = "def ir_outcome_bool (o : IROutcome) : Bool := IROutcome.rec (fun (_ : IROutcome) => Bool) (fun (v : IRList IRScalar) => ir_vals_head_bool v) (fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.false) Bool.false o";

const SRC_MACHINE_SOUND: &str = "def ir_lz_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) (href : EncodesLiveLevelRef mem r l) (hle : Le (ir_lz_cost l) fuel) (hret : Eq IROutcome (ir_eval fuel ir_lz_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))) : forall (rho : Name -> Nat), Eq Nat (level_eval rho l) Nat.zero := level_is_zero_sound l (Eq.cong IROutcome Bool ir_outcome_bool (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l)))) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l)))) (ir_eval fuel ir_lz_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) (Eq.symm IROutcome (ir_eval fuel ir_lz_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l)))) (ir_lz_correct mem fuel na r l href hle)) hret))";

const SRC_MACHINE_SOUND_WITNESS: &str = "def ir_lz_machine_sound_witness : forall (rho : Name -> Nat), Eq Nat (level_eval rho Level.zero) Nat.zero := ir_lz_machine_sound (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) (ir_lz_cost Level.zero) ir_d1 (IRScalar.ptr_ ir_d0) Level.zero encodes_live_ref_zero_witness (Le.refl (ir_lz_cost Level.zero)) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))))";

const SRC_OUTCOME_IS_RET: &str = "def ir_outcome_is_ret (o : IROutcome) : Bool := IROutcome.rec (fun (_ : IROutcome) => Bool) (fun (_ : IRList IRScalar) => Bool.true) (fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.false) Bool.false o";

const SRC_NEVER_FAULTS: &str = "def ir_lz_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) (href : EncodesLiveLevelRef mem r l) (hle : Le (ir_lz_cost l) fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_lz_module ir_d0 (ir_vl1 r) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_lz_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l)))) (ir_lz_correct mem fuel na r l href hle)";

impl Specification {
    /// A4: the equality theorem, and the induction it rests on.
    pub(super) fn add_eval_ir_correct(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_MACH0_S, "ir_lz_mach0_s: the activation machine indexed by an IRScalar rather than an address. EncodesLevelArc is indexed by IRScalar, so the induction motive must be too; at IRScalar.ptr_ a this is definitionally ir_lz_mach0 mem a, which is why the machine-level arms apply unchanged. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ACTIVATION, "ir_lz_activation: THE INDUCTION. For every heap-encoded Level, an activation of Level::is_zero runs exactly ir_lz_cost l steps and lands on the caller's resumption carrying level_is_zero l. \
\
By EncodesLevelArc.rec, one arm per Level constructor. The leaves discharge directly; max and imax go through the segment lemmas. \
\
The max arm is the one with structure. Both the COST and the ANSWER depend on level_is_zero l1 -- the cost because b3 ends in a CondBr and the two edges are different lengths, the answer because Bool.and l1 l2 collapses differently on each side -- so the case analysis needs a CONVOY: Bool.rec at a motive fun v => Eq Bool (level_is_zero l1) v -> .... Splitting on the value alone would lose the connection between the two occurrences. Each branch then transports its child's induction hypothesis along that equation to the answer the segment lemma expects. \
\
Note the recursor binds ALL constructor fields, including the sub-derivations, BEFORE the induction hypotheses -- max and imax take ten binders, not eight. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_CORRECT, "ir_lz_correct: *** CRYSTAL A4. THE EQUALITY THEOREM. *** \
\
For every Level l, every heap representing it, every next-address counter and every fuel at or above ir_lz_cost l, ir_eval on ir_lz_module returns exactly IROutcome.ret [bool (level_is_zero l)]. Quantified over Level and proved by induction, not sampled. \
\
The heap is arbitrary and touched only through lookup equations, so unrelated cells, DAG sharing and dead cells elsewhere are all permitted. The Le premise is load-bearing rather than decorative: at fixed fuel the statement is FALSE, since steps grow with the size of l. \
\
The assembly is short because the definitions line up. ir_init on this module is DEFINITIONALLY the activation's starting machine with no caller -- ir_lz_module declares no globals so ir_mem_concat is the identity, and the outermost frame has empty return destinations so its Return halts -- which collapses ir_ret_to to halted (ret v). ir_run_of_steps then converts the configuration statement into an outcome statement and ir_run_le_ret weakens the exact cost to the premise. \
\
SCOPE, which must travel with any statement of this result: ir_lz_module is HAND-AUTHORED, not emitted. This says that IF the compiler emits this module THEN its semantics agree with the kernel's Level::is_zero. Pinning the emitted artifact to it is job A0/A1 and is NOT done here, so this is not yet a statement about the shipped binary. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_SCALAR_BOOL, "ir_scalar_bool: read a Bool off a runtime value, false on the eleven non-Bool constructors. Part of getting the machine's ANSWER back out of its outcome so it can be fed to a theorem about Levels. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_VALS_HEAD_BOOL, "ir_vals_head_bool: the Bool in the first returned value. Level::is_zero returns exactly one value, so this is total where it matters and false elsewhere. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_OUTCOME_BOOL, "ir_outcome_bool: the Bool a successful outcome carries; false for every fault and for exhaustion. \
\
This is what makes A5's composition an equality argument rather than an inversion argument. Rather than inverting IROutcome.ret / ir_vl1 / IRScalar.bool_ through three injectivity lemmas, apply this projection to BOTH sides with Eq.cong and let the kernel compute -- ir_outcome_bool (ret [bool b]) reduces to b. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_MACHINE_SOUND, "ir_lz_machine_sound: *** CRYSTAL A5. *** If the MACHINE answers true, the level is genuinely zero -- denotationally, under EVERY assignment of parameters to naturals. \
\
This is where the crystal stops being about agreement between two programs and starts being about mathematics. A4 says the machine computes level_is_zero l; level_is_zero_sound says a definitely-zero level evaluates to 0 under every r : Name -> Nat. Composed: forall rho, level_eval rho l = 0, concluded from an observation about a running machine. \
\
ONE-DIRECTIONAL, and necessarily so. The converse is FALSE: a Param may be zero under some assignment while level_is_zero answers false, which is why Level::is_zero means DEFINITELY zero rather than zero. The machine inherits that asymmetry exactly. \
\
Both of A4's premises are carried through unchanged -- the representation of the heap and the fuel bound -- because neither can be dropped: without the first the machine reads an unrelated heap, and without the second it may return fuel_out, which is not a return at all. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_MACHINE_SOUND_WITNESS, "ir_lz_machine_sound_witness: A5 is not vacuous, and the witness RUNS THE MACHINE. \
\
Instantiated at the one-cell heap encoding Level.zero, with A2's encodes_live_ref_zero_witness supplying the representation premise, Le.refl supplying the fuel bound at exactly ir_lz_cost Level.zero, and Eq.refl supplying the observation -- which the kernel discharges by executing five steps. So every hypothesis of A5 is simultaneously satisfiable by a concrete configuration, and the conclusion it yields is a real statement about level_eval. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_OUTCOME_IS_RET, "ir_outcome_is_ret: did the machine finish with a value? False for every fault and for exhaustion, so it separates success from ALL five failure modes at once. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_NEVER_FAULTS, "ir_lz_never_faults: *** NO UB, NO PANIC, NO EXHAUSTION -- on any represented input. *** \
\
A corollary of A4, and it discharges the Phase-A obligation the design records as the panic arm STATED UNREACHED. IROutcome separates success from ub, type_error, unmodelled, stuck and fuel_out, so proving the outcome is a ret rules out every one of them simultaneously. \
\
Three concrete things it says about the emitted body. (1) Block b6 -- the Switch default, an IRInst.unreachable, which the semantics treats as UB rather than as a licence -- is NEVER executed; the five arms really are the enum's full tag set. (2) The null-check asserts in b3/b4/b5, standing for LevelArc::Deref's expect, NEVER fire. (3) No load faults bad_addr or null_deref, so every pointer the body follows is live and non-null. \
\
All three are earned by A2's premise rather than assumed: EncodesLevelArc pins each cell's liveness to Bool.true and each child to IRScalar.ptr_, which is exactly what the guards observe. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A4 must stay quantified over `Level`. If it ever names a constructor in
    /// its statement, it has become a sample.
    #[test]
    fn test_a4_is_universally_quantified_over_level() {
        assert!(SRC_CORRECT.contains("(l : Level)"));
        for c in ["Level.zero", "Level.succ", "Level.max", "Level.imax"] {
            assert!(
                !SRC_CORRECT.split(":=").next().unwrap_or("").contains(c),
                "A4's STATEMENT must not mention {c}"
            );
        }
    }

    /// The fuel premise is load-bearing: at fixed fuel the theorem is false.
    #[test]
    fn test_a4_carries_the_fuel_premise() {
        assert!(SRC_CORRECT.contains("Le (ir_lz_cost l) fuel ->"));
        assert!(SRC_CORRECT.contains("ir_run_le_ret"));
    }

    /// The heap is arbitrary — constrained only through lookup equations.
    #[test]
    fn test_a4_heap_is_arbitrary() {
        assert!(SRC_CORRECT.contains("(mem : IRList IRMemSlot)"));
        assert!(
            !SRC_CORRECT.contains("ir_cell"),
            "a concrete heap would make this a witness, not a theorem"
        );
    }

    /// The `max` arm needs a convoy, because cost and answer both depend on the
    /// left operand. Splitting on the value alone loses the connection.
    #[test]
    fn test_max_arm_uses_a_convoy() {
        assert!(SRC_ACTIVATION.contains("fun (v : Bool) => Eq Bool (level_is_zero l1) v ->"));
        assert!(SRC_ACTIVATION.contains("(Eq.refl Bool (level_is_zero l1))"));
    }

    /// Recursors bind every constructor field, sub-derivations included, before
    /// the induction hypotheses.
    #[test]
    fn test_arms_bind_the_sub_derivations() {
        assert!(SRC_ACTIVATION.contains("(_arc1 : EncodesLevelArc mem (IRScalar.ptr_ b1) l1)"));
        assert!(SRC_ACTIVATION.contains("(_arc2 : EncodesLevelArc mem (IRScalar.ptr_ b2) l2)"));
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [SRC_MACH0_S, SRC_ACTIVATION, SRC_CORRECT] {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count());
        }
    }
}
