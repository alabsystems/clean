// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`ir_its` — the FIRST chain minted from a body of `TypeChecker::infer_type`'s
//! derived closure, and A4/A5 over it.**
//!
//! Every chain before this one is minted from the CRATE module: a body the THIR
//! lowerer produced for `clean-kernel` itself. This one is minted from the
//! callee SIDECAR's partial bundle for `<impl tc::TypeChecker<'env>>::infer_type`
//! — `dump-infertype-O3-part/callees/clean_kernel.callees.trust-ir.bin`, 2,388
//! functions — and its body is function index 102 of that artifact.
//!
//! The body is `<[level::Level; 2] as smallvec::Array>::size`, the associated
//! size accessor of the `SmallVec` backing array `Level::max_args` uses. Three
//! nodes:
//!
//! ```text
//!     %0 = const usize 2
//!     %1 = copy usize %0
//!     ret %1
//! ```
//!
//! ## Why THIS body, stated so the modesty is not mistaken for a claim
//!
//! It is the smallest body in that closure the proven-output gate already
//! proves, and it is deliberately the easiest thing in the artifact. What is new
//! is not the difficulty, it is the PROVENANCE: no chain before it names the
//! infer_type sidecar bundle as its dump, so nothing in the spec had ever
//! executed a body that reached the module through `infer_type`'s own call
//! closure. A4 and A5 hold here for a body of that closure; they hold for ONE
//! body of 2,388, which is width one of a width the backlog measures in
//! thousands.
//!
//! ## The `usize` pin is a target fact and it is recorded, not assumed
//!
//! **CORRECTED.** This paragraph first said "the first chained body whose core
//! module resolves `usize`", and that is FALSE: `ir_ni` carries a `usize` lane
//! with `sites: 1` and `ir_lzd` one with `isize_sites: 2`. The A2 gate is how it
//! was found -- reader B REFUSED this fixture outright until the lane existed, so
//! the claim was made about a body reader B had never read.
//! `a2project` REFUSES to project it without an explicit `--usize-bits`, because
//! `usize` is target-dependent and resolving it silently would bake an unstated
//! word size into a committed core module. Reader A records `usize_bits: 64` and
//! `usize_sites_resolved: 2` in `generated/ir_its.core.prov.json`, and the tag
//! table carries the same fact with its justification. The 64 is the
//! aarch64-apple-darwin fact the whole crystal lane is measured on.
//!
//! ## Two ways this chain differs from every earlier one, both measured
//!
//! * its emitted header prints `fn @…` with **no** calling-convention keyword
//!   where every crate-module chain prints `rustcc`. Reader A records
//!   `artifact_calling_conv: ccc`. That is the sidecar lane showing through:
//!   these bodies are derived from monomorphized upstream MIR, not lowered from
//!   this crate's THIR.
//! * its `#producer` clause says `trust-ir`, where the crate-module chains say
//!   `trust` — the sidecar bundle's own producer stamp.
//!
//! ## What is NOT established here, and it is the larger half
//!
//! **The A2 MINT GATE for this chain is not written.** Every earlier chain has a
//! `tests/crystal_a2_mint_*.rs` running three independent readers — A over the
//! artifact binary, B over the emitted text, C over the elaborated term — and
//! requiring them to agree. This chain has reader A's projection
//! (`generated/ir_its.core.*`) and the minted script, and the emitted text was
//! read BY HAND and agrees, character for character, with what reader A
//! projected. A hand comparison is not a gate. Until `crystal_a2_mint_its.rs`
//! exists, the core module's fidelity to the artifact rests on ONE reader, and
//! that is the residual this file carries.
//!
//! A4/A5 below are about the module as registered, which is exactly the posture
//! `eval_ir_level_minted.rs` describes for `ir_lz`: what is proved is what the
//! kernel computes over the registered term.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The minted definition script, replayed line for line.
const MINTED_IR_ITS: &str = include_str!("generated/ir_its.defs.txt");

/// Registration rationales, one per minted line, in script order.
const MINTED_IR_ITS_DOCS: &[&str] = &[
    "ir_its_b0: THE WHOLE BODY, MINTED FROM THE EMITTED ARTIFACT (generated/ir_its.core.txt, projected by a2project from the infer_type callee bundle at dump_sha256 9b02ce7cdfd4a000...). THREE nodes in one block: a usize constant, a copy of it, and a ret. The copy is not redundant decoration -- it is what the producer emits, and a transcription that dropped it would agree with the artifact on the answer and differ on the step count, which is exactly what ir_its_exact pins. DerivedProved, zero axiom_deps.",
    "ir_its_func: the associated size accessor as EvalIR -- ZERO parameters, entry block 0, one block. Like ir_mt_func and unlike every argument-taking chain, so A4 quantifies over nothing but the heap and the fuel. DerivedProved, zero axiom_deps.",
    "ir_its_module: the module for <[level::Level; 2] as smallvec::Array>::size, MINTED from the emitted trust-ir rather than transcribed from it, and the FIRST module in the spec minted from a body of TypeChecker::infer_type's derived closure rather than from the crate module. The unwitnessed ledger is EMPTY -- no switch -- so the emitted text fully determines the core module. Reader A (a2project over the artifact binary), reader B (the committed emitted text) and reader C (this registered term, decoded back) agree under the three-reader A2 gate in tests/crystal_a2_mint_its.rs; the hand reading this line used to cite in its place is what that gate replaced, and writing it found two false claims the hand reading had passed. DerivedProved, zero axiom_deps.",
];

/// The minted script's lines, in registration order.
static MINTED_IR_ITS_LINES: std::sync::LazyLock<Vec<&'static str>> =
    std::sync::LazyLock::new(|| {
        MINTED_IR_ITS
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect()
    });

/// The minted `Array::size` module definitions, in registration order.
#[must_use]
pub(crate) fn ir_its_module_defs() -> &'static [&'static str] {
    &MINTED_IR_ITS_LINES
}

const SRC_ITS_SIZE: &str = "def smallvec_level2_array_size : Nat := ir_d2";

const SRC_ITS_MACH0: &str = "def ir_its_mach0 (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params ir_nl0 ir_vl0 (@IRList.nil IRBinding)) (@IRList.nil Nat)) (@IRList.nil IRFrame)) mem na";

const SRC_ITS_INIT: &str = "def ir_its_init_is_mach0 (mem : IRList IRMemSlot) (na : Nat) : @Eq IRConfig (ir_init ir_its_module ir_d0 ir_vl0 mem na) (IRConfig.running (ir_its_mach0 mem na)) := @Eq.refl IRConfig (IRConfig.running (ir_its_mach0 mem na))";

const SRC_ITS_EXACT: &str = "def ir_its_exact (mem : IRList IRMemSlot) (na : Nat) : @Eq IROutcome (ir_run ir_d3 ir_its_module (IRConfig.running (ir_its_mach0 mem na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ smallvec_level2_array_size))) := @Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ smallvec_level2_array_size)))";

const SRC_ITS_CORRECT: &str = "def ir_its_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (hle : Le ir_d3 fuel) : @Eq IROutcome (ir_eval fuel ir_its_module ir_d0 ir_vl0 mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ smallvec_level2_array_size))) := ir_run_le_ret ir_its_module ir_d3 fuel hle (IRConfig.running (ir_its_mach0 mem na)) (ir_vl1 (IRScalar.int_ smallvec_level2_array_size)) (ir_its_exact mem na)";

const SRC_ITS_NEVER_FAULTS: &str = "def ir_its_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (hle : Le ir_d3 fuel) : @Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_its_module ir_d0 ir_vl0 mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_its_module ir_d0 ir_vl0 mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ smallvec_level2_array_size))) (ir_its_correct mem fuel na hle)";

const SRC_ITS_MACHINE_SOUND: &str = "def ir_its_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (k : Nat) (hle : Le ir_d3 fuel) (hret : @Eq IROutcome (ir_eval fuel ir_its_module ir_d0 ir_vl0 mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ k)))) : @Eq Nat smallvec_level2_array_size k := ir_ret_int_inj smallvec_level2_array_size k (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ smallvec_level2_array_size))) (ir_eval fuel ir_its_module ir_d0 ir_vl0 mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ k))) (Eq.symm IROutcome (ir_eval fuel ir_its_module ir_d0 ir_vl0 mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ smallvec_level2_array_size))) (ir_its_correct mem fuel na hle)) hret)";

impl Specification {
    /// `ir_its` — the minted `Array::size` chain from infer_type's closure.
    pub(super) fn add_eval_ir_its(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_ITS_SIZE, "smallvec_level2_array_size: the reflected answer -- the LENGTH of the backing array `[Level; 2]`, which is what smallvec's `Array::size` for `[T; 2]` returns. Named rather than written as the literal 2 in A4 so the theorem reads as 'the emitted body computes the array length' rather than 'the emitted body returns 2', and so a chain minted for `[Level; 4]` would need a different constant here instead of silently reusing this one. DerivedProved, zero axiom_deps.")?;
        // The module is REPLAYED from the minted script, line for line — the
        // eval_ir_meta_tag.rs / eval_ir_level_minted.rs posture.
        let minted = ir_its_module_defs();
        if minted.len() != MINTED_IR_ITS_DOCS.len() {
            return Err(SpecError::EnvError(format!(
                "the minted ir_its script has {} definitions but {} rationales are declared; \
                 regenerate the docs table with the script rather than reusing it",
                minted.len(),
                MINTED_IR_ITS_DOCS.len()
            )));
        }
        for (line, doc) in minted.iter().zip(MINTED_IR_ITS_DOCS) {
            self.add_recursive_def(line, doc)?;
        }
        self.add_recursive_def(SRC_ITS_MACH0, "ir_its_mach0: the machine ir_init produces for this module. No parameters, so ir_bind_params over the empty lists is the empty locals list; the module declares no globals, so ir_mem_concat is the identity on the caller heap. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITS_INIT, "ir_its_init_is_mach0: the hand-written initial machine IS the one ir_init builds, for every heap and next-address counter, by computation. Registered rather than assumed so that a change to ir_init stops this reducing instead of silently making A4 a theorem about a different starting state. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITS_EXACT, "ir_its_exact: *** THE KERNEL RUNS THE EMITTED BODY. *** Three steps -- const, copy, ret -- and the outcome is ret [int 2], for EVERY heap and counter, by Eq.refl. The step count is part of the statement: a transcription that dropped the copy would still answer 2 and would not reduce here. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITS_CORRECT, "ir_its_correct: *** A4 FOR A BODY OF TypeChecker::infer_type'S DERIVED CLOSURE. *** For every heap, fuel at or above three, and counter, the minted module evaluates to ret [the array length]. The module is function index 102 of the infer_type callee bundle, minted by reader A from the artifact binary -- nothing in it is a model of anything. It is ONE body of 2,388 and the easiest one in the bundle; what is new is the provenance, not the difficulty. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITS_NEVER_FAULTS, "ir_its_never_faults: the outcome is a RETURN -- not ub, not stuck, not a type error, not fuel_out -- at every fuel at or above three. A corollary of A4 by congruence, registered separately because 'it returns something' and 'it returns the right thing' are different claims and the first is the one a no-panic reading needs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITS_MACHINE_SOUND, "ir_its_machine_sound: *** A5 FOR A BODY OF infer_type'S DERIVED CLOSURE. *** The flip: if the machine returns ANY integer k at sufficient fuel, then k IS the array length. A4 says the body computes the right answer; this says nothing else can come out of it, which is the direction a miscompile would break. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
