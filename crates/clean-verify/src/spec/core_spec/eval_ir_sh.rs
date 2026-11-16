// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`ir_sh` — the first chain carrying a TUPLE type, and the aggregate gap made
//! concrete on a real body.**
//!
//! `<expr::types::AppArgsIter<'_> as Iterator>::size_hint`, function index 468 of
//! the `infer_type` callee bundle. Six instructions:
//!
//! ```text
//!   bb0(%0: ptr):
//!     %1 = const usize 0
//!     %2 = undef enum.33                      ; the None upper bound
//!     %3 = undef (usize, enum.33)             ; the pair
//!     %4 = insertfield (usize, enum.33) %3, 0, %1
//!     %5 = insertfield (usize, enum.33) %4, 1, %2
//!     ret %5
//! ```
//!
//! # Two things it is for
//!
//! **It is the CALLER for the tuple image.** `IRTy.tuple_` existed in the object
//! language, but `a2project` had no image for `trust_ir::Ty::Tuple`, so no chain
//! could carry one. This body cannot be projected without it, which is what keeps
//! the image from being a capability with no caller.
//!
//! **And it makes the aggregate-construction gap concrete.**
//! `ir_undef_then_insertfield_faults` states the gap abstractly, for every index
//! and value. This body is the gap happening: the machine binds the constant,
//! binds two `undef_`s, and then FAULTS at the first `insertfield`, because
//! `IRInst.undef` ignores its type and `ir_insert_field` needs an `aggv`.
//! `ir_sh_halts_at_the_pack` is that, by computation, on six instructions from
//! `infer_type`'s own closure.
//!
//! # What the tuple image erases, said out loud
//!
//! `IRTy.tuple_` takes a Nat and the reflected module has no tuple table to
//! index, so the image is ARITY-ONLY: `(tuple 2)`, element types gone. A body
//! differing only by `(ptr, enum.33)` projects to the SAME core. The tag table's
//! `tuple_sites` count is what makes that visible — the ir_ni posture, where a
//! `u64`-for-`usize` swap is caught by a count and not by the resolved core.
//!
//! Arity-only is enough for the machine: `insertfield` and `extractfield` ignore
//! the declared type and work structurally over the value's spine, and a tuple
//! LOAD has no recorded size, so it fails closed exactly where the element types
//! would have mattered.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The minted definition script, replayed line for line.
const MINTED_IR_SH: &str = include_str!("generated/ir_sh.defs.txt");

/// Registration rationales, one per minted line, in script order.
const MINTED_IR_SH_DOCS: &[&str] = &[
    "ir_sh_topt: `Option<usize>` as an IR enum, crate id 33 -- the UPPER BOUND of the size hint, built by `undef` and never filled, which is exactly what `None` is. DerivedProved, zero axiom_deps.",
    "ir_sh_b0: THE WHOLE BODY -- six nodes. The THIRD is the first `IRTy.tuple_` any chain has carried, and the FOURTH is where the machine stops: an insertfield into a bare `undef_`. DerivedProved, zero axiom_deps.",
    "ir_sh_func: `Iterator::size_hint` as EvalIR -- one pointer parameter, taken and never dereferenced, entry block 0, one block. It answers (0, None) unconditionally, which is why it reads no memory. DerivedProved, zero axiom_deps.",
    "ir_sh_module: the module for AppArgsIter::size_hint, MINTED from the emitted trust-ir. It calls nothing, so unlike ir_it_module it does not go stuck at a missing callee -- it FAULTS, inside itself, on the aggregate-construction gap. DerivedProved, zero axiom_deps.",
];

/// The minted script's lines, in registration order.
static MINTED_IR_SH_LINES: std::sync::LazyLock<Vec<&'static str>> =
    std::sync::LazyLock::new(|| {
        MINTED_IR_SH
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect()
    });

/// The minted `size_hint` module definitions, in registration order.
#[must_use]
pub(crate) fn ir_sh_module_defs() -> &'static [&'static str] {
    &MINTED_IR_SH_LINES
}

const SRC_SH_MACH0: &str = "def ir_sh_mach0 (mem : IRList IRMemSlot) (p : Nat) (na : Nat) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) (@IRList.nil Nat)) (@IRList.nil IRFrame)) mem na";

const SRC_SH_INIT: &str = "def ir_sh_init_is_mach0 (mem : IRList IRMemSlot) (p : Nat) (na : Nat) : @Eq IRConfig (ir_init ir_sh_module ir_d0 (ir_vl1 (IRScalar.ptr_ p)) mem na) (IRConfig.running (ir_sh_mach0 mem p na)) := @Eq.refl IRConfig (IRConfig.running (ir_sh_mach0 mem p na))";

const SRC_SH_FAULTS: &str = "def ir_sh_halts_at_the_pack (mem : IRList IRMemSlot) (p : Nat) (na : Nat) : @Eq IROutcome (ir_eval ir_d8 ir_sh_module ir_d0 (ir_vl1 (IRScalar.ptr_ p)) mem na) (IROutcome.type_error IRFault.not_agg) := @Eq.refl IROutcome (IROutcome.type_error IRFault.not_agg)";

impl Specification {
    /// `ir_sh` — the tuple caller, and the aggregate gap on a real body.
    pub(super) fn add_eval_ir_sh(&mut self) -> Result<(), SpecError> {
        let minted = ir_sh_module_defs();
        if minted.len() != MINTED_IR_SH_DOCS.len() {
            return Err(SpecError::EnvError(format!(
                "the minted ir_sh script has {} definitions but {} rationales are declared; \
                 regenerate the docs table with the script rather than reusing it",
                minted.len(),
                MINTED_IR_SH_DOCS.len()
            )));
        }
        for (line, doc) in minted.iter().zip(MINTED_IR_SH_DOCS) {
            self.add_recursive_def(line, doc)?;
        }
        self.add_recursive_def(SRC_SH_MACH0, "ir_sh_mach0: the machine ir_init produces -- one pointer parameter bound on entry, no globals, so ir_mem_concat is the identity on the caller heap. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_SH_INIT, "ir_sh_init_is_mach0: the hand-written initial machine IS the one ir_init builds, for every heap, argument and counter, by computation. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_SH_FAULTS, "ir_sh_halts_at_the_pack: *** THE AGGREGATE-CONSTRUCTION GAP, HAPPENING. *** For every heap, argument and counter the machine binds the constant, binds two undefs, and then FAULTS at the first insertfield with type_error not_agg -- because `IRInst.undef` ignores its declared type and `ir_insert_field` requires an IRScalar.aggv. `ir_undef_then_insertfield_faults` states that abstractly; this is it on six instructions from infer_type's own derived closure, by computation. \\n\\nIt is a FAULT and not a `stuck`, and the difference is the point: ir_it_module halts because a callee is missing from the module, which more module would fix; this body is COMPLETE and halts anyway, because the machine cannot execute the idiom the producer builds every aggregate with. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
