// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`ir_itd` — the designated target RUNNING TO COMPLETION, and returning what
//! its inference callee gave it, for EVERY payload it could have given.**
//!
//! `ir_it` halts at the first call. `ir_itc` goes one frame into the real
//! heartbeat. `ir_itb` runs the whole dispatch and halts at `call 2`, step 8.
//! This chain supplies the second model and the target **returns**, at step 14.
//!
//! ```text
//!   ir_itd_module sp = IRModule.mk [ ir_it_func ; ir_itb_hb ; ir_itd_fast sp ] []
//! ```
//!
//! # What is actually proved
//!
//! ```text
//!   forall sp p q,
//!     ir_eval 14 (ir_itd_module sp) 0 [ptr p, ptr q] mem0 7
//!       = IROutcome.ret [ ir_const_value (ir_itd_cval sp) ]
//! ```
//!
//! `sp : IRConst` is the payload spine `infer_type_fast` hands back, and it is
//! UNIVERSALLY QUANTIFIED. So this is not one execution witness with a value
//! that happens to come out right: the target's ok path neither inspects nor
//! alters its callee's payload, whatever that payload was. That is the
//! TRANSPORT property, and transport is what the body actually does —
//!
//! ```text
//!   b5:  %29 = call 2 (%0, %1)        <- the inference
//!        store Result %2, %29         <- into the alloca'd slot
//!        br b3
//!   b3:  %5  = load Result %2         <- back out of it
//!        ret %5
//! ```
//!
//! — a memory round-trip and a return. The 2026-09-16 link-5 census recorded
//! exactly this shape as the reason `infer_type` needs no model of `Expr`'s
//! internals: a body that TRANSPORTS its return carries no payload obligation.
//! This chain is that observation executed by the kernel rather than asserted.
//!
//! **What is NOT quantified, and why it cannot be.** Slot 0 of the result is
//! the discriminant, and it is the selector `ir_it_b1`'s `extractfield` +
//! `switch` read to choose the ok branch in the first place. Quantifying it
//! would make the branch undecidable, so `ir_itd_cval` pins it to `0` and
//! quantifies everything after it. The claim is therefore "every payload of the
//! ok result", not "every possible return value".
//!
//! Why an abstract spine reduces at all: `ir_const_value` is `IRConst.rec`
//! (`eval_ir_ops.rs`), so `ir_const_value sp` is stuck at the neutral `sp` —
//! but it is stuck IDENTICALLY on both sides, because the machine's own
//! `ir_const_eval` aggregate arm produces `IRScalar.aggv (ir_const_value sp)`
//! from the same spine. Nothing between that `const_` and the final `ret` ever
//! forces it: `ir_store_exec` matches on the POINTER, `ir_mem_update` carries
//! the value opaquely, and `ir_load_view` is the identity when the module's
//! encodings table is empty (`ir_mod_encs (IRModule.mk fs gs) = nil`, and the
//! `IROption.rec` branches on the TABLE before the result).
//!
//! # The two residuals, and they are both AUTHORED
//!
//! `ir_itb_hb` is the heartbeat model this chain REUSES rather than restates,
//! so the body executed here is the same one `ir_itb` ran. `ir_itd_fast` is new
//! and is the second: two nodes standing in for `infer_type_fast`, which is
//! where the actual inference happens. Neither is derived and this chain proves
//! nothing about what either real body returns.
//!
//! What it does establish is the caller's half, which is the half the target
//! owns: GIVEN the heartbeat says ok and GIVEN the inference returns a payload,
//! `infer_type` returns that payload. Retiring the models needs the closures
//! behind them — 313 functions for the heartbeat (`eval_ir_itc.rs`), 113 for
//! the inference side — or a compositional call rule the machine does not have.
//!
//! # Why the heap is concrete here when `ir_itb`'s is abstract
//!
//! `ir_itb` halts before any store or load, so its only heap effect is the
//! entry `alloca`'s head-cons, which commutes with any `mem`. This chain
//! RESOLVES an address, and at an abstract allocation counter `ir_mem_lookup`'s
//! `ir_nat_eqb` is stuck at a neutral operand — which is why
//! `eval_ir_slot_lemmas.rs` states its store and load steps with the lookup
//! SUSPENDED and discharges it by `Eq.subst`, while its end-to-end
//! `ir_slot_concrete` runs at `ir_mem0` and a concrete counter. The same split
//! applies here, and the quantifier was spent where the content is: on the
//! payload being transported, not on the heap it is parked in.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The ok-`Result` constant the inference model returns: discriminant `0` at
/// slot 0 — PINNED, because it is the switch selector — and the whole rest of
/// the spine QUANTIFIED.
const SRC_ITD_CVAL: &str = "def ir_itd_cval (sp : IRConst) : IRConst := IRConst.aggv (IRConst.vcons (IRConst.int_ ir_d0) sp)";

/// The authored inference model's only block: that constant, and a return.
const SRC_ITD_FAST_B0: &str = "def ir_itd_fast_b0 (sp : IRConst) : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_it_tresult (ir_itd_cval sp)) ir_d2) (ir_nd (IRInst.ret (ir_nl1 ir_d2))))";

/// The authored model itself — id 2, arity 2, the index `infer_type`'s `call 2`
/// names with both of its own parameters.
const SRC_ITD_FAST: &str = "def ir_itd_fast (sp : IRConst) : IRFunc := IRFunc.mk ir_d2 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk (ir_itd_fast_b0 sp) ir_blk0)";

/// The module: the MINTED target, and BOTH authored models beside it.
const SRC_ITD_MODULE: &str = "def ir_itd_module (sp : IRConst) : IRModule := IRModule.mk (IRList.cons IRFunc ir_it_func (IRList.cons IRFunc ir_itb_hb (IRList.cons IRFunc (ir_itd_fast sp) (IRList.nil IRFunc)))) (IRList.nil IRGlobal)";

/// The value the model returns, derived THROUGH `ir_const_value` from the very
/// constant the block emits — one spelling, not two transcriptions.
const SRC_ITD_ANSWER: &str =
    "def ir_itd_answer (sp : IRConst) : IRScalar := ir_const_value (ir_itd_cval sp)";

/// Lower half of the cost pin.
const SRC_ITD_THIRTEEN: &str = "def ir_itd_is_still_running_at_thirteen (sp : IRConst) (p : Nat) (q : Nat) : Eq IROutcome (ir_eval ir_d13 (ir_itd_module sp) ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) ir_mem0 ir_d7) IROutcome.fuel_out := Eq.refl IROutcome IROutcome.fuel_out";

/// **The transport theorem, at the exact cost.**
const SRC_ITD_FOURTEEN: &str = "def ir_itd_transports_the_inference_result (sp : IRConst) (p : Nat) (q : Nat) : Eq IROutcome (ir_eval ir_d14 (ir_itd_module sp) ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) ir_mem0 ir_d7) (IROutcome.ret (ir_vl1 (ir_itd_answer sp))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_itd_answer sp)))";

/// Halting is stable under more fuel.
const SRC_ITD_MORE_FUEL: &str = "def ir_itd_more_fuel_does_not_change_it (sp : IRConst) (p : Nat) (q : Nat) : Eq IROutcome (ir_eval ir_d40 (ir_itd_module sp) ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) ir_mem0 ir_d7) (IROutcome.ret (ir_vl1 (ir_itd_answer sp))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_itd_answer sp)))";

impl Specification {
    /// `ir_itd` — the target running to completion over two authored models.
    pub(super) fn add_eval_ir_itd(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_ITD_CVAL, "ir_itd_cval: the ok-Result constant the inference model returns. Slot 0 is the discriminant and is PINNED to zero because it is the selector ir_it_b1's extractfield and switch read to choose the ok branch -- quantifying it would make the branch undecidable. Everything AFTER it is the parameter `sp`, so the payload is universally quantified and the claim below is about every payload of the ok result rather than about one witness. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITD_FAST_B0, "ir_itd_fast_b0: the authored inference model's only block -- the quantified constant, and a return. An aggregate CONSTANT for the same reason ir_itb_hb_b0 uses one: ir_undef_then_insertfield_faults pins that the producer's undef-then-insertfield construction idiom cannot execute, so a model must be written in the fragment the machine has rather than the one the producer uses. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITD_FAST, "ir_itd_fast: the AUTHORED stand-in for <impl tc::TypeChecker<'env>>::infer_type_fast, at id 2 and arity 2 -- the index and the parameter count infer_type's `call 2 (%0, %1)` names. This is the SECOND residual of this chain and the larger one: infer_type_fast is where the actual inference happens. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITD_MODULE, "ir_itd_module: the designated target and BOTH models. It NAMES ir_it_func and ir_itb_hb rather than transcribing either -- so the target body executed here is byte-identical to the one ir_it, ir_itc and ir_itb carry, and the heartbeat model is the same term ir_itb ran, not a copy that could drift from it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITD_ANSWER, "ir_itd_answer: the value ir_itd_fast returns, derived THROUGH ir_const_value from ir_itd_cval -- the very constant the block emits. Defining it this way rather than transcribing an IRScalar spine beside the IRConst one means the theorem's two sides genuinely cite ONE spelling and cannot drift apart. It also explains why an abstract spine reduces: ir_const_value is IRConst.rec, so `ir_const_value sp` is stuck at the neutral sp -- but identically on both sides, because the machine's ir_const_eval aggregate arm produces IRScalar.aggv (ir_const_value sp) from the same spine. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITD_THIRTEEN, "ir_itd_is_still_running_at_thirteen: at THIRTEEN steps the machine has executed the load and is sitting on the final ret, not yet taken. Registered as the lower half of a COST PIN: together with ir_itd_transports_the_inference_result at fourteen it fixes the run's cost at exactly 14 steps rather than bracketing it between a tight side and a comfortable over-approximation. The sibling chains state only over-approximations, and an earlier draft of THIS file asserted `fuel_out` at sixteen on a step count that was guessed rather than traced -- the spec build refused it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITD_FOURTEEN, "*** THE DESIGNATED TARGET RUNS TO COMPLETION AND RETURNS WHAT ITS INFERENCE CALLEE GAVE IT -- FOR EVERY PAYLOAD IT COULD HAVE GIVEN. *** In exactly fourteen steps, for every payload spine sp and both pointer arguments, the machine allocas the Result slot, calls the heartbeat model, reads the tag, takes the switch onto the ok branch, calls the inference model, STORES its aggregate result into the slot, branches, LOADS it back and RETURNS it -- and what comes out is ir_itd_answer sp, the very value that went in. \\n\\nsp is UNIVERSALLY QUANTIFIED, so this is the TRANSPORT property and not an execution witness: infer_type's ok path neither inspects nor alters its callee's payload. That is why the link-5 census could record that this target needs no model of Expr's internals, and this is that observation kernel-checked rather than argued. The discriminant slot is necessarily NOT quantified -- it is the switch selector -- so the claim is about every payload of the ok result. \\n\\nIt also exercises the memory round-trip at an AGGREGATE, and at one whose spine is ABSTRACT: nothing between the callee's const_ and the caller's ret forces it, because ir_store_exec matches on the pointer, ir_mem_update carries the value opaquely, and ir_load_view is the identity on an empty encodings table. \\n\\nWhat it does NOT establish: BOTH callees are authored. This is the caller's half of a compositional argument whose other halves are a 313-function closure and a 113-function one. A4 is not claimed for infer_type. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITD_MORE_FUEL, "ir_itd_more_fuel_does_not_change_it: the same outcome at forty steps as at fourteen. Registered separately because a halted machine staying halted is a property of ir_run worth pinning beside the cost, and because ir_it_more_fuel_does_not_help pins the analogous fact on the stuck side. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
