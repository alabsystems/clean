// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`ir_itc` — the designated target WITH its size-one cut defined, and the cut
//! EXERCISED rather than described.**
//!
//! `ir_it` defines `TypeChecker::infer_type` alone: its `call 1` names a function
//! the module does not contain, so the machine halts `stuck no_func` at the
//! target's second instruction. This module defines `tick_heartbeat` beside it —
//! twenty blocks, `ir_th_b0..ir_th_b19` — so that call RESOLVES, the machine
//! ENTERS the heartbeat, and halts at *its* first call instead.
//!
//! That is the `ir_lz` → `ir_lzc` step applied to the crystal's own target, and
//! `tick_heartbeat` is not an arbitrary next callee: it is the cut the
//! 2026-09-16 closure measurement named. Removing it takes `infer_type`'s
//! transitive closure from **396 functions with 12 recursion back edges** to
//! **113 with none** — every one of those cycles is `heartbeat_profiler` sort
//! code reached through this body, and none is `infer_type`'s own typechecking
//! recursion. Until now that was a fact about a call graph. Here it is the
//! machine running.
//!
//! ```text
//!   infer_type   %2 = alloca struct.2 ; %3 = call 1     <- RESOLVES now
//!   tick_heartbeat  %1 = alloca ; %2 = undef ; %3 = undef ; %4 = call 3
//!                                                       <- halts HERE
//! ```
//!
//! # What is proved, and what is deliberately not
//!
//! Two facts, and the pair is the point. `ir_itc_enters_the_heartbeat` shows the
//! machine still RUNNING at a fuel where `ir_it` is already halted — that is the
//! call resolving, by computation. `ir_itc_halts_inside_the_heartbeat` shows
//! where it then stops: `stuck no_func` at canonical 3,
//! `LocalKey::<DeclBudget>::with`, a thread-local access.
//!
//! **A4 is NOT claimed**, exactly as in `ir_it`. The module still calls four
//! functions it does not define, and the census asserts the absence of an
//! A4-shaped name rather than leaving it to prose.
//!
//! # What this cost, recorded because it was not what I predicted
//!
//! The mint refused at `numeral 64 is outside the registered ir_d0..ir_d63 atom
//! pool` — `tick_heartbeat` has SSA ids to 130 where the designated target alone
//! reaches 39. I recorded that as blocked on byte-identity of landed artifacts,
//! citing the minter's own warning. That warning is about the **data** pool
//! (`nat_data`, cutoff 16); `nat`'s STRUCTURAL pool is a separate bound, and
//! `ir_mt`'s committed defs spell `IRConst.int_ 63` and `IRConst.int_ 64` as RAW
//! literals — which is exactly what the separation buys. A structural index at or
//! above 64 could not have been minted under the old bound, so none existed to
//! respell, and 106 mint-gate tests across four chains confirm it.
//!
//! The real obstacle was smaller twice over: `ir_d64` is already taken by
//! `eval_ir_valid_char.rs` (as `Nat.add ir_d32 ir_d32`, the machine WIDTH), and
//! that stage runs LATER, so chaining through it fails with `Unknown identifier`.
//! `ir_d65` is therefore built from `ir_d63`. Three framings, each narrower than
//! the last, and only the third survived.
//!
//! # Why the next step is NOT more of this, measured
//!
//! The obvious continuation is the `ir_lzc` → `ir_lzd` one: add the callee this
//! module halts at (`LocalKey::<DeclBudget>::with` — 12 instructions, max SSA 7)
//! and go a frame deeper again. That does not terminate in any useful number of
//! steps, and the number is the reason:
//!
//! ```text
//!   tick_heartbeat's OWN transitive closure:
//!     313 functions, 55,122 instructions, max SSA id 8,285
//! ```
//!
//! The bulk is `HeartbeatProfiler::tick` (593 instructions) pulling in
//! hashbrown's `Entry`/`HashMap` machinery. Defining the heartbeat path to
//! completion would be ~313 more chains, each with its own tag-table body and a
//! full-spec verify, and the atom pool would have to reach 8,285 rather than 130.
//!
//! So this module is where the frame-by-frame method ends usefully. Going
//! further needs one of two things, and both are named rather than implied:
//!
//! * a COMPOSITIONAL call rule — assume-guarantee, so a callee's contract stands
//!   in for its body and the closure never has to be defined. The machine has no
//!   such rule today; `ir_call_exec` resolves or goes stuck.
//! * an AUTHORED MODEL of `tick_heartbeat`'s effect — the `ir_lzb_deref` pattern,
//!   which is exactly what the crystal did for the one callee rustc could not
//!   give a body for. Here the body exists and its CLOSURE is what cannot be
//!   carried, which is a different reason for the same remedy.
//!
//! The second is harder than `ir_lzb_deref` was, and the earlier note saying so
//! now has its comparison: `tick_heartbeat` MUTATES a counter, so its model is a
//! state obligation rather than a read — and the alternative that model is
//! weighed against costs 313 functions.
//!
//! # THE SECOND ROUTE WAS TAKEN THE SAME DAY — read `eval_ir_itb.rs`
//!
//! Everything above stands as the reason the FRAME-BY-FRAME method stops here.
//! It is no longer the reason progress stops: `ir_itb` (2026-09-16) supplies the
//! authored model and the target runs its whole dispatch, and `ir_itd` supplies
//! a second one for `infer_type_fast` and the target RETURNS, in 14 steps, with
//! the transported payload universally quantified.
//!
//! One correction to the bullet above, because it is the sentence a reader will
//! act on: the model that worked does NOT model `tick_heartbeat`'s EFFECT. It
//! models its ANSWER — an aggregate constant on the ok branch — which is exactly
//! how it sidesteps the state obligation this module called the hard part. The
//! state obligation is still open and still hard; it is simply not what the
//! caller's half needed. What the answer-model costs instead is stated plainly
//! in `eval_ir_itb.rs`: the chain proves nothing about whether the real body
//! returns that answer under any condition.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The minted definition script, replayed line for line.
const MINTED_IR_ITC: &str = include_str!("generated/ir_itc.defs.txt");

/// The minted script's lines, in registration order.
static MINTED_IR_ITC_LINES: std::sync::LazyLock<Vec<&'static str>> =
    std::sync::LazyLock::new(|| {
        MINTED_IR_ITC
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect()
    });

/// The minted two-body module definitions, in registration order.
#[must_use]
pub(crate) fn ir_itc_module_defs() -> &'static [&'static str] {
    &MINTED_IR_ITC_LINES
}

const SRC_ITC_MACH0: &str = "def ir_itc_mach0 (mem : IRList IRMemSlot) (p : Nat) (q : Nat) (na : Nat) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl2 ir_d0 ir_d1) (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) (@IRList.nil IRBinding)) (@IRList.nil Nat)) (@IRList.nil IRFrame)) mem na";

const SRC_ITC_INIT: &str = "def ir_itc_init_is_mach0 (mem : IRList IRMemSlot) (p : Nat) (q : Nat) (na : Nat) : @Eq IRConfig (ir_init ir_itc_module ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) mem na) (IRConfig.running (ir_itc_mach0 mem p q na)) := @Eq.refl IRConfig (IRConfig.running (ir_itc_mach0 mem p q na))";

const SRC_ITC_ENTERS: &str = "def ir_itc_enters_the_heartbeat (mem : IRList IRMemSlot) (p : Nat) (q : Nat) (na : Nat) : @Eq IROutcome (ir_eval ir_d3 ir_itc_module ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) mem na) IROutcome.fuel_out := @Eq.refl IROutcome IROutcome.fuel_out";

const SRC_ITC_STUCK: &str = "def ir_itc_halts_inside_the_heartbeat (mem : IRList IRMemSlot) (p : Nat) (q : Nat) (na : Nat) : @Eq IROutcome (ir_eval ir_d16 ir_itc_module ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) mem na) (IROutcome.stuck IRFault.no_func) := @Eq.refl IROutcome (IROutcome.stuck IRFault.no_func)";

impl Specification {
    /// `ir_itc` — the target with its cut defined.
    pub(super) fn add_eval_ir_itc(&mut self) -> Result<(), SpecError> {
        for line in ir_itc_module_defs() {
            self.add_recursive_def(line, "ir_itc: the designated target TOGETHER WITH tick_heartbeat, minted from the infer_type callee bundle. Function 0 is `TypeChecker::infer_type` (six blocks); function 1 is `tc::heartbeat::tick_heartbeat` (twenty blocks), the callee whose absence makes infer_type's transitive closure cyclic -- 396 functions and 12 recursion back edges become 113 and none once it is cut. Defining it here is what makes `call 1` RESOLVE where ir_it_module goes stuck at it. DerivedProved, zero axiom_deps.")?;
        }
        self.add_recursive_def(SRC_ITC_MACH0, "ir_itc_mach0: the machine ir_init produces -- the same two pointer parameters ir_it binds, over a module that now carries two function bodies. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITC_INIT, "ir_itc_init_is_mach0: the hand-written initial machine IS the one ir_init builds, for every heap, both arguments and every counter, by computation. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITC_ENTERS, "*** THE SIZE-ONE CUT, EXERCISED. *** At three steps the machine is still RUNNING -- fuel_out, not stuck -- where ir_it_module has already halted at exactly this point. That difference IS the call resolving: ir_it goes `stuck no_func` at infer_type's second instruction because tick_heartbeat is absent, and this module, which defines it, walks into it instead. Registered as its own theorem rather than left to the later halt, because `it got further` and `it halted somewhere else` are different claims and only the first says the cut works. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITC_STUCK, "ir_itc_halts_inside_the_heartbeat: and where it then stops -- `stuck no_func` at canonical 3, `LocalKey::<DeclBudget>::with`, tick_heartbeat's own first call and a thread-local access. Fail-closed, never a misroute: ir_func_find matches a candidate on its OWN id, so an absent callee halts rather than resolving to a body that is present. A4 is NOT claimed over this module, exactly as for ir_it and ir_lz -- four functions it calls are still declarations. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
