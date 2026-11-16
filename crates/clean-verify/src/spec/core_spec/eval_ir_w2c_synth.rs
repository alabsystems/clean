// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **W2c — the synthetic micro-module lane's call+module tranche:
//! `callindirect`, `globaladdr`.** The FINAL synthetic tranche: after it,
//! every `IRInst` constructor except `overflow` (plan W3) and `fcmp` (plan W4)
//! has battery rows.
//!
//! Plan: `docs/analysis/evalir-completion-plan-2026-08-24.md` §5 W2c. Both
//! constructors have REAL dispatch arms (`ir_exec`,
//! `eval_ir_machine.rs:931,937`) but no committed emitted body exercises
//! them. Same lane discipline as W2a/W2b (`eval_ir_w2a_synth.rs` /
//! `eval_ir_w2b_synth.rs`, read those module docs first): one authored
//! micro-module per constructor, kernel-executed `ir_w2c_*` witnesses
//! including the fault edges, synthetic `.trust-ir.txt` twins under
//! `tests/fixtures/synth/`, and `Synthetic`-labeled battery rows
//! (`tests/crystal_a3_semdiff/w2c_chains.rs`) that re-read this stage's module
//! lines through the `ir_w2c_*_module_defs` re-exports.
//!
//! ## What makes each module the SMALLEST honest observation
//!
//! * **`callindirect` dispatches through a VALUE, and that is the property
//!   under measure.** The callee arrives as a function-pointer ARGUMENT, and
//!   the module carries TWO companion callees — one argument-independent
//!   (`const 11`), one the identity — so the same caller body computes
//!   different answers purely because the function-pointer value differs.
//!   A single callee could not distinguish "the machine resolved the value"
//!   from "the machine returned the argument"; two can.
//! * **`globaladdr` is observable through the module's global store.** The
//!   module's one global (`IRGlobal.mk ir_d0 (IRConst.int_ ir_d7)`) is read
//!   through its address (the initializer row) and written through ONE
//!   `globaladdr` result then read back through a SECOND `globaladdr` of the
//!   same global (the store row) — the second read observing the first write
//!   is exactly the "repeated address-of aliases" property
//!   `ir_globaladdr_eval`'s doc names. `store`/`load`/`condbr` ride along;
//!   all three carry W1 agreement rows, so each chain's new information is
//!   its constructor's.
//!
//! ## Design constraints and measured facts that shaped the modules
//!
//! * **A global's id IS its address** (`ir_globals_mem`), and `ir_init`
//!   starts the allocator at the caller-supplied `na`. A module that carried
//!   both globals and `alloca` at `na = 0` would collide cell addresses, so
//!   the `globaladdr` module allocates nothing — the design rule is: globals
//!   or a low `na`, never both. (The reference interpreter has no such
//!   coupling — it lazily allocates a global's backing store on FIRST
//!   `global_addr` and caches the pointer, `interpret.rs::global_pointer` at
//!   trust-ir `a4e81b6` — and no row here observes allocation order, so the
//!   materialize-at-init / materialize-on-first-use split is unobservable in
//!   this module and recorded here rather than smoothed.)
//! * **The null-callee edge diverges by CODE, not merely site.** Clean's
//!   `ir_callind_exec` pins `ub null_deref`; the reference interpreter
//!   reports its own `invalid_function_pointer` code — NOT
//!   `undefined_behavior` (`interpret.rs:1415-1421`, measured at `a4e81b6`) —
//!   so the battery carries the row as a DECLARED delta, never class
//!   agreement (`w2c_chains.rs`).
//! * **The inert operands stay inert.** `IRInst.callindirect`'s `sig` and
//!   `calling_conv` fields are carried but never dispatched on — proved, not
//!   assumed: `ir_exec_callind_sig_irrelevant` /
//!   `ir_exec_callind_conv_irrelevant` (`eval_ir_machine.rs:989-1016`). The
//!   Clean twin spells the sig tag `ir_d9` where the E2 twin spells
//!   `functy.920`; the theorems are why that mismatch cannot matter.
//!
//! Everything here is `DerivedProved`, zero axiom_deps: every witness is an
//! `Eq.refl` the kernel discharges by running the machine (whole-program
//! `ir_eval` witnesses) or by iota-reducing one evaluator match
//! (`ir_w2c_ga_no_global` over `ir_globaladdr_eval`). Witness fuels are
//! SUFFICIENT, not least — the battery pins each row's least fuel from below.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// ── callindirect: value-driven dispatch to one of two companion callees ───
//
//   caller (id 0): bb0(%0: fnptr, %1: u32): %2 = call_indirect %0(%1); ret %2
//   callee A (id 1, const11): bb0(%0: u32): %1 = const u32 11; ret %1
//   callee B (id 2, ident):   bb0(%0: u32): ret %0

const SRC_IR_W2C_CI_B0: &str = "def ir_w2c_ci_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.callindirect ir_d0 ir_d9 (ir_nl1 ir_d1) ir_d0) ir_d2) (ir_nd (IRInst.ret (ir_nl1 ir_d2))))";

const SRC_IR_W2C_CI_FUNC: &str = "def ir_w2c_ci_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_w2c_ci_b0 ir_blk0)";

const SRC_IR_W2C_CI_CA_B0: &str = "def ir_w2c_ci_ca_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ (IRTy.uint_ 32) (IRConst.int_ ir_d11)) ir_d1) (ir_nd (IRInst.ret (ir_nl1 ir_d1))))";

const SRC_IR_W2C_CI_CA_FUNC: &str = "def ir_w2c_ci_ca_func : IRFunc := IRFunc.mk ir_d1 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_w2c_ci_ca_b0 ir_blk0)";

const SRC_IR_W2C_CI_CB_B0: &str = "def ir_w2c_ci_cb_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd1 (ir_nd (IRInst.ret (ir_nl1 ir_d0))))";

const SRC_IR_W2C_CI_CB_FUNC: &str = "def ir_w2c_ci_cb_func : IRFunc := IRFunc.mk ir_d2 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_w2c_ci_cb_b0 ir_blk0)";

const SRC_IR_W2C_CI_MODULE: &str = "def ir_w2c_ci_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_w2c_ci_func (@IRList.cons IRFunc ir_w2c_ci_ca_func (@IRList.cons IRFunc ir_w2c_ci_cb_func (@IRList.nil IRFunc)))) (@IRList.nil IRGlobal)";

/// The `callindirect` micro-module's definitions, in registration order — the
/// lines the battery registers, re-exported rather than re-typed.
#[must_use]
pub fn ir_w2c_ci_module_defs() -> &'static [&'static str] {
    &[
        SRC_IR_W2C_CI_B0,
        SRC_IR_W2C_CI_FUNC,
        SRC_IR_W2C_CI_CA_B0,
        SRC_IR_W2C_CI_CA_FUNC,
        SRC_IR_W2C_CI_CB_B0,
        SRC_IR_W2C_CI_CB_FUNC,
        SRC_IR_W2C_CI_MODULE,
    ]
}

const SRC_IR_W2C_CI_ON_CONST: &str = "def ir_w2c_ci_on_const (x : Nat) : @Eq IROutcome (ir_eval ir_d8 ir_w2c_ci_module ir_d0 (@IRList.cons IRScalar (IRScalar.fnptr_ ir_d1) (@IRList.cons IRScalar (IRScalar.int_ x) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d11))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d11)))";

const SRC_IR_W2C_CI_ON_IDENT: &str = "def ir_w2c_ci_on_ident (x : Nat) : @Eq IROutcome (ir_eval ir_d8 ir_w2c_ci_module ir_d0 (@IRList.cons IRScalar (IRScalar.fnptr_ ir_d2) (@IRList.cons IRScalar (IRScalar.int_ x) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ x))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ x)))";

const SRC_IR_W2C_CI_ON_NULL: &str = "def ir_w2c_ci_on_null (x : Nat) : @Eq IROutcome (ir_eval ir_d8 ir_w2c_ci_module ir_d0 (@IRList.cons IRScalar IRScalar.nullptr_ (@IRList.cons IRScalar (IRScalar.int_ x) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.ub IRFault.null_deref) := @Eq.refl IROutcome (IROutcome.ub IRFault.null_deref)";

const SRC_IR_W2C_CI_NOT_FNPTR: &str = "def ir_w2c_ci_not_fnptr (n : Nat) (x : Nat) : @Eq IROutcome (ir_eval ir_d8 ir_w2c_ci_module ir_d0 (@IRList.cons IRScalar (IRScalar.int_ n) (@IRList.cons IRScalar (IRScalar.int_ x) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_fnptr) := @Eq.refl IROutcome (IROutcome.type_error IRFault.not_fnptr)";

const SRC_IR_W2C_CI_NO_FUNC: &str = "def ir_w2c_ci_no_func (x : Nat) : @Eq IROutcome (ir_eval ir_d8 ir_w2c_ci_module ir_d0 (@IRList.cons IRScalar (IRScalar.fnptr_ ir_d5) (@IRList.cons IRScalar (IRScalar.int_ x) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.stuck IRFault.no_func) := @Eq.refl IROutcome (IROutcome.stuck IRFault.no_func)";

// ── globaladdr: initializer read, and store/load through two addresses ────
//
//   global 0: u32 = 7
//   bb0(%0: u32, %1: bool): %2 = global_addr @global.0; condbr %1, bb1, bb2
//   bb1: %3 = global_addr @global.0; store u32 %0 -> %2;
//        %4 = load u32, %3; ret %4
//   bb2: %5 = load u32, %2; ret %5

const SRC_IR_W2C_GA_B0: &str = "def ir_w2c_ga_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.globaladdr ir_d0) ir_d2) (ir_nd (IRInst.condbr ir_d1 ir_d1 ir_nl0 ir_d2 ir_nl0)))";

const SRC_IR_W2C_GA_B1: &str = "def ir_w2c_ga_b1 : IRBlock := IRBlock.mk ir_d1 ir_nl0 (@IRList.cons IRNode (ir_nd1 (IRInst.globaladdr ir_d0) ir_d3) (ir_bd3 (ir_nd (IRInst.store (IRTy.uint_ 32) ir_d2 ir_d0 Bool.false)) (ir_nd1 (IRInst.load (IRTy.uint_ 32) ir_d3 Bool.false) ir_d4) (ir_nd (IRInst.ret (ir_nl1 ir_d4)))))";

const SRC_IR_W2C_GA_B2: &str = "def ir_w2c_ga_b2 : IRBlock := IRBlock.mk ir_d2 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.load (IRTy.uint_ 32) ir_d2 Bool.false) ir_d5) (ir_nd (IRInst.ret (ir_nl1 ir_d5))))";

const SRC_IR_W2C_GA_FUNC: &str = "def ir_w2c_ga_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_w2c_ga_b0 (ir_blk ir_w2c_ga_b1 (ir_blk ir_w2c_ga_b2 ir_blk0)))";

const SRC_IR_W2C_GA_MODULE: &str = "def ir_w2c_ga_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_w2c_ga_func (@IRList.nil IRFunc)) (@IRList.cons IRGlobal (IRGlobal.mk ir_d0 (IRConst.int_ ir_d7)) (@IRList.nil IRGlobal))";

/// The `globaladdr` micro-module's definitions, in registration order.
#[must_use]
pub fn ir_w2c_ga_module_defs() -> &'static [&'static str] {
    &[
        SRC_IR_W2C_GA_B0,
        SRC_IR_W2C_GA_B1,
        SRC_IR_W2C_GA_B2,
        SRC_IR_W2C_GA_FUNC,
        SRC_IR_W2C_GA_MODULE,
    ]
}

const SRC_IR_W2C_GA_ON_INIT: &str = "def ir_w2c_ga_on_init (x : Nat) : @Eq IROutcome (ir_eval ir_d8 ir_w2c_ga_module ir_d0 (@IRList.cons IRScalar (IRScalar.int_ x) (@IRList.cons IRScalar (IRScalar.bool_ Bool.false) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d7))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d7)))";

const SRC_IR_W2C_GA_ON_STORE: &str = "def ir_w2c_ga_on_store (x : Nat) : @Eq IROutcome (ir_eval ir_d8 ir_w2c_ga_module ir_d0 (@IRList.cons IRScalar (IRScalar.int_ x) (@IRList.cons IRScalar (IRScalar.bool_ Bool.true) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ x))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ x)))";

const SRC_IR_W2C_GA_NONBOOL: &str = "def ir_w2c_ga_nonbool (x : Nat) (n : Nat) : @Eq IROutcome (ir_eval ir_d8 ir_w2c_ga_module ir_d0 (@IRList.cons IRScalar (IRScalar.int_ x) (@IRList.cons IRScalar (IRScalar.int_ n) (@IRList.nil IRScalar))) ir_mem0 ir_d0) (IROutcome.type_error IRFault.not_bool) := @Eq.refl IROutcome (IROutcome.type_error IRFault.not_bool)";

const SRC_IR_W2C_GA_NO_GLOBAL: &str = "def ir_w2c_ga_no_global : @Eq IRStepResult (ir_globaladdr_eval ir_w2c_ga_module ir_d5) (IRStepResult.fault (IROutcome.type_error IRFault.no_global)) := @Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.no_global))";

impl Specification {
    /// The W2c synthetic micro-modules (call+module tranche) and their
    /// kernel-executed witnesses.
    ///
    /// Reuses (all from `add_eval_ir`): the `IRInst`/`IRBlock`/`IRFunc`/
    /// `IRGlobal`/`IRModule` syntax, `IRConst`, the `ir_d0..ir_d16` numerals,
    /// the `ir_nd`/`ir_nd1`/`ir_bd1..3`/`ir_blk`/`ir_blk0`/`ir_nl0..2`/
    /// `ir_vl1` builders, `ir_mem0`, `ir_globaladdr_eval`, and the machine
    /// (`ir_eval`, `IROutcome`, `IRFault`, `IRStepResult`). Deliberately
    /// nothing from any chain stage, so the battery can register the module
    /// lines standalone into the minimal `EvalIr` bundle spec.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check — for the witnesses, that means the kernel RAN the machine
    /// and got a different outcome, which is a red to report, never to tune.
    pub(super) fn add_eval_ir_w2c_synth(&mut self) -> Result<(), SpecError> {
        for (line, doc) in [
            (SRC_IR_W2C_CI_B0, "ir_w2c_ci_b0: SYNTHETIC micro-module entry (W2c callindirect): call through the function-pointer ARGUMENT %0, passing %1; return what the callee returned. The sig tag (ir_d9) and calling-conv tag (ir_d0) are carried but never dispatched on — proved inert by ir_exec_callind_sig_irrelevant / ir_exec_callind_conv_irrelevant, which is why the Clean tag and the E2 twin's functy.920 need not agree. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_CI_FUNC, "ir_w2c_ci_func: the caller — two parameters (callee fnptr, payload at SSA ids 0,1), entry block 0, one block, function id 0. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_CI_CA_B0, "ir_w2c_ci_ca_b0: companion callee A — argument-INDEPENDENT (const u32 11), so reaching it is observable no matter what payload rode along. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_CI_CA_FUNC, "ir_w2c_ci_ca_func: callee A at function id 1 (the id IRScalar.fnptr_ ir_d1 resolves to). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_CI_CB_B0, "ir_w2c_ci_cb_b0: companion callee B — the IDENTITY, so the payload's round-trip through the indirect call frame is observable. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_CI_CB_FUNC, "ir_w2c_ci_cb_func: callee B at function id 2. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_CI_MODULE, "ir_w2c_ci_module: the SYNTHETIC callindirect module — authored for the W2c differential (E2 twins tests/fixtures/synth/synth_callindirect{,_c11,_id}.trust-ir.txt); no producer emitted it and no lineage gate applies. Two callees, ONE caller body: the same instructions compute different answers purely through the function-pointer value, which is the constructor's semantics. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_CI_ON_CONST, "ir_w2c_ci_on_const: dispatching to callee A returns 11 for EVERY payload — the payload is transported to a callee that ignores it, so the witness quantifies over it and pins that the answer came from the callee, not the argument. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_CI_ON_IDENT, "ir_w2c_ci_on_ident: dispatching to callee B returns the payload, for EVERY payload — with ir_w2c_ci_on_const this is the two-point separation that pins value-driven dispatch: same body, same payload class, different fnptr, different answer. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_CI_ON_NULL, "ir_w2c_ci_on_null: FAULT EDGE — calling through the null function pointer is `ub null_deref` at every payload (ir_callind_exec's nullptr_ arm). MEASURED CODE SPLIT, recorded where the verdict lives: the reference interpreter reports its own `invalid_function_pointer` code, NOT undefined_behavior (interpret.rs:1415-1421, trust-ir a4e81b6), so the battery row is a DECLARED delta, never class agreement. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_CI_NOT_FNPTR, "ir_w2c_ci_not_fnptr: FAULT EDGE — an integer in the callee slot is `type_error not_fnptr` at every pair of values (ir_callind_exec fails closed arm-per-shape on every non-fnptr scalar; the int arm is the representative witness). Kernel-only: the E2 twin rejects the same input at the ENTRY signature check, a different site with no shared row vocabulary. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_CI_NO_FUNC, "ir_w2c_ci_no_func: FAULT EDGE — a function pointer to an id the module does not define is STUCK (no_func), not UB: ir_call_exec declines a dangling callee rather than inventing a result. Kernel-only: E2 reports its own invalid_function_pointer code for the same input (function_pointer_target, a4e81b6), the same class split as the null edge. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_GA_B0, "ir_w2c_ga_b0: SYNTHETIC micro-module entry (W2c globaladdr): take the global's address, then condbr on %1 between the store/load aliasing observation (bb1) and the initializer read (bb2). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_GA_B1, "ir_w2c_ga_b1: the aliasing arm — a SECOND globaladdr of the same global, store %0 through the FIRST address, load back through the SECOND, return it: the load observing the store is exactly the repeated-address-of-aliases property ir_globaladdr_eval's doc names, measured rather than asserted. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_GA_B2, "ir_w2c_ga_b2: the initializer arm — load the never-written global and return it: pins that ir_init materialized the global's cell with ir_const_value of its initializer. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_GA_FUNC, "ir_w2c_ga_func: two parameters (value, selector at SSA ids 0,1), entry block 0, three blocks. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_GA_MODULE, "ir_w2c_ga_module: the SYNTHETIC globaladdr module — one function, ONE global (id 0, initializer int 7; E2 twin tests/fixtures/synth/synth_globaladdr.trust-ir.txt, whose global lives in the chain's composed module header). A global's id IS its address, so this module allocates nothing: alloca at na=0 would collide with the global's cell (module doc — the globals-or-low-na design rule). DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_GA_ON_INIT, "ir_w2c_ga_on_init: the never-written global reads as its initializer 7, for EVERY (never-consulted) value argument. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_GA_ON_STORE, "ir_w2c_ga_on_store: store x through one globaladdr result, load through the other, get x back — for EVERY x (transport, no arithmetic). This is the aliasing witness: two globaladdr executions of the same global denote one cell. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_GA_NONBOOL, "ir_w2c_ga_nonbool: FAULT EDGE — an integer in the selector slot is `type_error not_bool` at every pair of values (ir_condbr_exec), pinned so a routing fault cannot be confused with a global-store fault. DerivedProved, zero axiom_deps."),
            (SRC_IR_W2C_GA_NO_GLOBAL, "ir_w2c_ga_no_global: FAULT EDGE, value-level — globaladdr of an id the module's global list does not carry is `type_error no_global` (ir_globaladdr_eval's none arm). Kernel-only: E2 reports the same shape as its own missing_value code (global_pointer's out-of-range arm, a4e81b6), outside the shared class map. DerivedProved, zero axiom_deps."),
        ] {
            self.add_recursive_def(line, doc)?;
        }
        Ok(())
    }
}
