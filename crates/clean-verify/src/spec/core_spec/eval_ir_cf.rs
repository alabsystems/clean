// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`ir_cf` — the caller the `IRConst.phantomdata` extension exists for.**
//!
//! `<ControlFlow<()> as Try>::from_output`, function index 331 of the
//! `infer_type` callee bundle. Two nodes:
//!
//! ```text
//!   bb0(%0: ()):
//!     %1 = const enum.56 { 0, phantomdata }
//!     ret %1
//! ```
//!
//! # Why this body and not a bigger one
//!
//! Because of the landing rule. `IRConst.phantomdata` was added to the reflected
//! constant grammar on 2026-09-16 to unblock `tc::heartbeat::tick_heartbeat` —
//! the one callee whose absence makes `infer_type`'s call closure cyclic — and
//! that unblocking did NOT succeed: reader A cleared PhantomData and refused one
//! step later on `no Clean IRTy image for trust_ir::Ty::Tuple([U32, Bool])`, the
//! checked-arithmetic pair. `IRTy` already HAS `tuple_`, but the machine faults
//! it `not_agg` and gives it no size, so imaging it would produce a core the
//! machine operationally declines. That is a design question, not a table row.
//!
//! So the extension would have landed with no chained body using it — a
//! capability without its caller, which this repo's landing rule forbids. This
//! body IS the caller: reader A refuses it outright without the constructor
//! (measured), it is a body of `infer_type`'s derived closure, and its minted
//! script carries `IRConst.phantomdata` inside the aggregate spine:
//!
//! ```text
//!   IRConst.aggv (IRConst.vcons (IRConst.int_ ir_d0)
//!                 (IRConst.vcons IRConst.phantomdata IRConst.vnil))
//! ```
//!
//! # What is proved
//!
//! That the machine RETURNS rather than faulting, for every heap, argument and
//! counter, by computation. That is deliberately weaker than A4: it does not say
//! WHAT comes back. The return is an aggregate, and the A5-shaped injection this
//! programme has (`ir_ret_int_inj`) is the INTEGER one — an aggregate injection
//! does not exist, so an A4/A5 pair here would need machinery no chain has yet.
//! Stating the weaker fact is what keeps this file honest about the difference.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The minted definition script, replayed line for line.
const MINTED_IR_CF: &str = include_str!("generated/ir_cf.defs.txt");

/// Registration rationales, one per minted line, in script order.
const MINTED_IR_CF_DOCS: &[&str] = &[
    "ir_cf_tcflow: `ControlFlow<()>` as an IR enum, crate id 56 -- THE RETURN TYPE, and the type the body's aggregate constant is built at. DerivedProved, zero axiom_deps.",
    "ir_cf_b0: THE WHOLE BODY -- two nodes, an aggregate constant and a ret. The constant is `{ 0, phantomdata }`: tag 0 (Continue) and a ZERO-SIZED payload. It is the first constant in any chain whose spine carries IRConst.phantomdata, and reader A cannot project this body at all without that constructor. DerivedProved, zero axiom_deps.",
    "ir_cf_func: the `Try::from_output` impl as EvalIR -- ONE parameter of unit type, taken and ignored, entry block 0, one block. DerivedProved, zero axiom_deps.",
    "ir_cf_module: the module for <ControlFlow<()> as Try>::from_output, MINTED from the emitted trust-ir. It calls nothing, so unlike ir_it_module it does not go stuck; it returns. DerivedProved, zero axiom_deps.",
];

/// The minted script's lines, in registration order.
static MINTED_IR_CF_LINES: std::sync::LazyLock<Vec<&'static str>> =
    std::sync::LazyLock::new(|| {
        MINTED_IR_CF
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect()
    });

/// The minted `from_output` module definitions, in registration order.
#[must_use]
pub(crate) fn ir_cf_module_defs() -> &'static [&'static str] {
    &MINTED_IR_CF_LINES
}

const SRC_CF_MACH0: &str = "def ir_cf_mach0 (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 IRScalar.unit_) (@IRList.nil IRBinding)) (@IRList.nil Nat)) (@IRList.nil IRFrame)) mem na";

const SRC_CF_INIT: &str = "def ir_cf_init_is_mach0 (mem : IRList IRMemSlot) (na : Nat) : @Eq IRConfig (ir_init ir_cf_module ir_d0 (ir_vl1 IRScalar.unit_) mem na) (IRConfig.running (ir_cf_mach0 mem na)) := @Eq.refl IRConfig (IRConfig.running (ir_cf_mach0 mem na))";

const SRC_CF_RETURNS: &str = "def ir_cf_returns (mem : IRList IRMemSlot) (na : Nat) : @Eq Bool (ir_outcome_is_ret (ir_eval ir_d4 ir_cf_module ir_d0 (ir_vl1 IRScalar.unit_) mem na)) Bool.true := @Eq.refl Bool Bool.true";

impl Specification {
    /// `ir_cf` — the phantomdata caller.
    pub(super) fn add_eval_ir_cf(&mut self) -> Result<(), SpecError> {
        let minted = ir_cf_module_defs();
        if minted.len() != MINTED_IR_CF_DOCS.len() {
            return Err(SpecError::EnvError(format!(
                "the minted ir_cf script has {} definitions but {} rationales are declared; \
                 regenerate the docs table with the script rather than reusing it",
                minted.len(),
                MINTED_IR_CF_DOCS.len()
            )));
        }
        for (line, doc) in minted.iter().zip(MINTED_IR_CF_DOCS) {
            self.add_recursive_def(line, doc)?;
        }
        self.add_recursive_def(SRC_CF_MACH0, "ir_cf_mach0: the machine ir_init produces -- one unit-typed parameter bound on entry. The module declares no globals, so ir_mem_concat is the identity on the caller heap. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_CF_INIT, "ir_cf_init_is_mach0: the hand-written initial machine IS the one ir_init builds, for every heap and counter, by computation. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_CF_RETURNS, "ir_cf_returns: *** THE KERNEL MATERIALIZES A PhantomData-BEARING AGGREGATE CONSTANT AND RETURNS IT. *** For every heap and counter the outcome is a RET -- not ub, not stuck, not a type error, not fuel_out. This is the fact that makes IRConst.phantomdata a capability WITH a caller: the constant cannot be built without it, and the machine evaluates it here. Deliberately weaker than A4: it does not say what comes back. The return is an aggregate and the only ret-injection this programme has is the INTEGER one (ir_ret_int_inj), so an A4/A5 pair over this body needs machinery no chain has yet. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
