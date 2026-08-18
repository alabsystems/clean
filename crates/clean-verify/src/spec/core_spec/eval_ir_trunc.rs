// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The NINTH complete width-one chain — and the first over a CAST:
//! `env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}`.**
//!
//! ```text
//! fn get_char_val(e: &Expr) -> Option<u32> {
//!     super::native_reducers_char::char_code_point(e).map(|n| n as u32)
//! }                                                       // ^^^^^^^^^ THIS closure
//! ```
//!
//! ```text
//! rustcc fn @env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}(functy.540) {
//!     ; #producer: trust
//!     ; #names: %1="n"
//! bb0(%0: (), %1: u64):
//!     %2 = trunc u64 %1 to u32  ; #loc: 347 120 60
//!     ret %2  ; #loc: 347 120 68
//! }
//! ```
//!
//! ## Why THIS body, out of the three casts in the crate
//!
//! The 2026-08-15 lane-8 census recorded a cast as unclaimed ground and named
//! three bodies. All three were **re-derived from this lane's own whole-crate
//! dump** rather than inherited, and the operator census over all 177 codegen
//! flips reproduces the float lane's exactly — `const` 116, `extractfield` 37,
//! `insertfield` 22, `load` 15, `icmp` 11, **`zext` 2, `trunc` 1**, `and` 1,
//! `or` 1, `fadd`/`fsub`/`fmul`/`fdiv` 1 each.
//!
//! | body | cast | instrs | canonical lines | markers | interpreter | flip |
//! |---|---|---|---|---|---|---|
//! | `cert::builder::state::NodeId::index` | `zext u32 -> usize` | 3 | 4 | 2 REAL | **not-run** | #61 |
//! | `env::persistent_ext::ExtensionIdx::index` | `zext u32 -> usize` | 3 | 4 | 2 REAL | **not-run** | #49 |
//! | `…::get_char_val::{closure#0}` | **`trunc u64 -> u32`** | 2 | 5 | 2 REAL | **agreed, 5 samples** | #195 |
//!
//! Chosen on CONTENT, and the axis is the one that makes a cast interesting:
//!
//! 1. **Information is LOST.** A zero extension is an injective embedding; its
//!    refinement theorem says the value is unchanged, which is the least a cast
//!    can say. `trunc u64 -> u32` is `n mod 2^32`, so distinct inputs collapse —
//!    and the theorem has to be exact about *which* information survives.
//!    `ir_gc_high_word_is_discarded` states it for every pair of inputs and
//!    `ir_gc_two_inputs_one_answer` executes it on the shipped body.
//! 2. **The two `zext` bodies are the same body twice.** Instruction for
//!    instruction — `extractfield u32 %0, 0` / `zext u32 %1 to usize` / `ret %2`
//!    — with identical instr counts, identical `4 canonical line(s) identical`,
//!    identical `2 marker line(s) identical` and identical zero call counts.
//!    They differ in their struct id (`struct.317` vs `struct.848`) and nothing
//!    else. Chaining one would be chaining one of a duplicated pair; the `trunc`
//!    is the only one of its kind in the crate.
//! 3. **The producer's own interpreter differential RAN on it** — `agreed` on 5
//!    sampled inputs. Both `zext` bodies are `interpreter: not-run`
//!    ("non-scalar parameter type is non-interpretable"), because their argument
//!    is a by-value newtype struct. So the chosen body carries strictly more
//!    producer-side evidence than either alternative.
//!
//! The two `zext` bodies are not left unmodelled by this lane even though they
//! are not chained: `ir_gc_zext_is_an_embedding` registers what the semantics
//! computes for exactly their opcode and width direction, so a later lane that
//! wants one has the evaluator and only owes the transcription. What it will
//! ALSO owe is a decision about `usize`: the CFG type lane deliberately leaves
//! it unresolved (`?usize`) rather than assuming a width, and fails loudly.
//!
//! ## Was a build item needed? NO — and that is a measurement, not a hope
//!
//! The float lane needed one: every float operation in the semantics was the
//! single verdict `ir_float_fault`. The cast lane needed none. `IRInst.cast`
//! has been a constructor of `IRInst` since the syntax was written
//! (`eval_ir_syntax.rs`), `IRCastOp` carries 17/17 of `trust_ir::CastOp`,
//! `ir_cast_eval` dispatches all seventeen arms, `ir_trunc_eval` / `ir_zext_eval`
//! / `ir_sext_eval` are exact typed evaluators, and the machine has had a case
//! for the instruction all along (`eval_ir_machine.rs`, `IRInst.cast op sr ds a
//! => ir_bind_result s rs (ir_cast_eval op sr ds (ir_getd s a))`).
//!
//! **The build item was in the GATE, not in the semantics** — and it is the
//! same class of hole the float lane found. Before this chain, a cast was in no
//! CFG lane at all: a body whose entire content is `trunc` + `ret` parsed to an
//! EMPTY `Cfg` on both sides, and two empty CFGs compare equal. The `casts` and
//! `cast_tys` lanes close it.
//!
//! ## Both widths are semantic input, and the float lane's hole is checked for
//!
//! `fdiv f32` and `fdiv f64` differed in NO lane until `binop_tys`. A cast has
//! **two** types and both were checked here before the lane was trusted:
//!
//! * DESTINATION — `ir_trunc_int` returns `ir_wrap dw x`, so `trunc u64 -> u32`
//!   and `trunc u64 -> u8` are different functions of the same operand.
//!   `ir_gc_dest_width_is_semantic` is that, for every `n`.
//! * SOURCE — the guard is `ir_nat_leb dw sw`, so `trunc u8 -> u32` is
//!   `ir_width_fault` where `trunc u64 -> u32` is a value. The source width
//!   decides FAULT versus VALUE and is not implied by the operand.
//!   `ir_gc_source_width_is_semantic` is that, for every scalar.
//! * The OPCODE — `zext u64 -> u32` at this chain's own widths is
//!   `ir_width_fault`, because zero extension requires `sw <= dw`.
//!   `ir_gc_opcode_is_semantic` is that, for every scalar. So swapping
//!   `trunc` for `zext` in the transcription turns a value into a fault, and it
//!   is a kernel-executed fact rather than a comment.
//!
//! ## What this does NOT establish — read before quoting it
//!
//! `env_get_char_val_closure` is `ir_wrap ir_d32`, i.e. `n mod 2^32`. That IS
//! what Rust's `as u32` does to a `u64`, and this module does not prove it — it
//! is the same shape of gap [`super::eval_ir_valid_char`] states for
//! `env_is_valid_char` and [`super::eval_ir_float_div`] states for
//! `ir_f64_div`, and it is the smallest of the three, because a residue has less
//! structure than an interval test or a float format.
//!
//! The GENERAL periodicity law — `ir_wrap 32 (n + 2^32) = ir_wrap 32 n` for
//! every `n` — is **not** proved here. It needs `ir_nat_rem` periodicity, which
//! nobody in this program has earned, and buying it with the kernel-native
//! `Nat.div`/`Nat.mod` would add ACCELERATED CONSTANTS whose declared bodies the
//! kernel never consults: speed bought with trust, which is exactly what the
//! float lane refused for `finite + finite`. What IS proved generally is the
//! conditional form — equal low words give equal outcomes — and the collapse
//! itself is executed at concrete inputs instead of assumed.
//!
//! The link between the proved module and the emitted one is STRUCTURAL —
//! `tests/crystal_a1_lineage/get_char_val_trunc.rs`. Everything past the flip
//! seam is downstream and covered by nothing here. And this is width one.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// NOTHING is re-declared here. `ir_d8` / `ir_d32` / `ir_d64`, `ir_br_tu32`
// (fifth chain), `ir_vc_tu64` and `EncodesU64Val` (sixth chain), `ir_tU8`,
// `ir_outcome_nat` (second chain) and `ir_run_le_ret` all already exist and this
// stage runs after every one of them. The eighth chain's ONE real error was
// re-declaring `ir_nl3`/`ir_vl3`, which elaborated cleanly in every fast gate
// and failed only in the full `Specification::new()` at 27 minutes an attempt.
// A name that already exists is a name to REUSE.

// ── the reflected closure and its representation premise ──────────────
const SRC_ENV_GET_CHAR_VAL_CLOSURE: &str =
    "def env_get_char_val_closure (n : Nat) : Nat := ir_wrap ir_d32 n";

// ── the emitted module, transcribed ───────────────────────────────────
const SRC_IR_GC_B0: &str = "def ir_gc_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1) ir_d2) (ir_nd (IRInst.ret (ir_nl1 ir_d2))))";
const SRC_IR_GC_FUNC: &str = "def ir_gc_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk ir_gc_b0 ir_blk0)";
const SRC_IR_GC_MODULE: &str = "def ir_gc_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_gc_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)";

// ── the machine ───────────────────────────────────────────────────────
const SRC_IR_GC_MACH0: &str = "def ir_gc_mach0 (p : IRScalar) (n : Nat) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl2 ir_d0 ir_d1) (ir_vl2 p (IRScalar.int_ n)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";
const SRC_IR_GC_EXACT: &str = "def ir_gc_exact (p : IRScalar) (n : Nat) (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d2 ir_gc_module (IRConfig.running (ir_gc_mach0 p n mem na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure n)))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure n))))";

// ── A4, A5, and the corollaries ───────────────────────────────────────
const SRC_IR_GC_CORRECT: &str = "def ir_gc_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (p : IRScalar) (r : IRScalar) (n : Nat) (h : EncodesU64Val r n) : Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure n)))) := EncodesU64Val.rec (fun (r0 : IRScalar) (n0 : Nat) (_ : EncodesU64Val r0 n0) => Le ir_d2 fuel -> Eq IROutcome (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p r0) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure n0))))) (fun (m : Nat) (hle : Le ir_d2 fuel) => ir_run_le_ret ir_gc_module ir_d2 fuel hle (IRConfig.running (ir_gc_mach0 p m mem na)) (ir_vl1 (IRScalar.int_ (env_get_char_val_closure m))) (ir_gc_exact p m mem na)) r n h";
const SRC_IR_GC_MACHINE_SOUND: &str = "def ir_gc_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (p : IRScalar) (r : IRScalar) (n : Nat) (k : Nat) (h : EncodesU64Val r n) (hle : Le ir_d2 fuel) (hret : Eq IROutcome (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ k)))) : Eq Nat (env_get_char_val_closure n) k := Eq.cong IROutcome Nat ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure n)))) (IROutcome.ret (ir_vl1 (IRScalar.int_ k))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure n)))) (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ k))) (Eq.symm IROutcome (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure n)))) (ir_gc_correct mem fuel na p r n h hle)) hret)";
const SRC_IR_GC_NEVER_FAULTS: &str = "def ir_gc_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (p : IRScalar) (r : IRScalar) (n : Nat) (h : EncodesU64Val r n) (hle : Le ir_d2 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p r) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure n)))) (ir_gc_correct mem fuel na p r n h hle)";

// A5 REACHING PAST THE ANSWER, ONTO THE ARGUMENTS: the discarded high word.
const SRC_IR_GC_HIGH_WORD_IS_DISCARDED: &str = "def ir_gc_high_word_is_discarded (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (p : IRScalar) (n : Nat) (m : Nat) (hle : Le ir_d2 fuel) (heq : Eq Nat (env_get_char_val_closure n) (env_get_char_val_closure m)) : Eq IROutcome (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p (IRScalar.int_ n)) mem na) (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p (IRScalar.int_ m)) mem na) := Eq.trans IROutcome (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p (IRScalar.int_ n)) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure m)))) (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p (IRScalar.int_ m)) mem na) (Eq.trans IROutcome (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p (IRScalar.int_ n)) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure n)))) (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure m)))) (ir_gc_correct mem fuel na p (IRScalar.int_ n) n (EncodesU64Val.mk n) hle) (Eq.cong Nat IROutcome (fun (k : Nat) => IROutcome.ret (ir_vl1 (IRScalar.int_ k))) (env_get_char_val_closure n) (env_get_char_val_closure m) heq)) (Eq.symm IROutcome (ir_eval fuel ir_gc_module ir_d0 (ir_vl2 p (IRScalar.int_ m)) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure m)))) (ir_gc_correct mem fuel na p (IRScalar.int_ m) m (EncodesU64Val.mk m) hle))";

// ── CAST SEMANTICS, stated as theorems rather than as prose ───────────
const SRC_IR_GC_TRUNC_LOW_WORD: &str = "def ir_gc_trunc_is_the_low_word (n : Nat) : Eq IRStepResult (ir_cast_eval IRCastOp.trunc ir_vc_tu64 ir_br_tu32 (IRScalar.int_ n)) (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d32 n))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d32 n)))";
const SRC_IR_GC_DEST_WIDTH: &str = "def ir_gc_dest_width_is_semantic (n : Nat) : Eq IRStepResult (ir_cast_eval IRCastOp.trunc ir_vc_tu64 ir_tU8 (IRScalar.int_ n)) (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d8 n))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d8 n)))";
const SRC_IR_GC_SOURCE_WIDTH: &str = "def ir_gc_source_width_is_semantic (a : IRScalar) : Eq IRStepResult (ir_cast_eval IRCastOp.trunc ir_tU8 ir_br_tu32 a) ir_width_fault := Eq.refl IRStepResult ir_width_fault";
const SRC_IR_GC_OPCODE: &str = "def ir_gc_opcode_is_semantic (a : IRScalar) : Eq IRStepResult (ir_cast_eval IRCastOp.zext ir_vc_tu64 ir_br_tu32 a) ir_width_fault := Eq.refl IRStepResult ir_width_fault";
const SRC_IR_GC_ZEXT_EMBEDS: &str = "def ir_gc_zext_is_an_embedding (n : Nat) : Eq IRStepResult (ir_cast_eval IRCastOp.zext ir_br_tu32 ir_vc_tu64 (IRScalar.int_ n)) (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d64 (ir_wrap ir_d32 n)))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (ir_wrap ir_d64 (ir_wrap ir_d32 n))))";
const SRC_IR_GC_NOT_INT: &str = "def ir_gc_non_integer_operand_is_a_type_error (b : Bool) : Eq IRStepResult (ir_cast_eval IRCastOp.trunc ir_vc_tu64 ir_br_tu32 (IRScalar.bool_ b)) (IRStepResult.fault (IROutcome.type_error IRFault.not_int)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_int))";

// ── kernel-EXECUTED witnesses ─────────────────────────────────────────
//   7            fits in 32 bits, quotient 0
//   4294967295 = 2^32 - 1, the largest value the cast preserves
//   4294967296 = 2^32,     the smallest value it sends to zero
//   4294967303 = 2^32 + 7, the collapse partner of 7
const SRC_W_FITS: &str = "def ir_gc_w_fits : Eq IROutcome (ir_eval ir_d2 ir_gc_module ir_d0 (ir_vl2 IRScalar.unit_ (IRScalar.int_ 7)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 7))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 7)))";
const SRC_W_U32MAX: &str = "def ir_gc_w_u32max_survives : Eq IROutcome (ir_eval ir_d2 ir_gc_module ir_d0 (ir_vl2 IRScalar.unit_ (IRScalar.int_ 4294967295)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 4294967295))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 4294967295)))";
const SRC_W_2P32: &str = "def ir_gc_w_2p32_becomes_zero : Eq IROutcome (ir_eval ir_d2 ir_gc_module ir_d0 (ir_vl2 IRScalar.unit_ (IRScalar.int_ 4294967296)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 0)))";
const SRC_W_LOSES: &str = "def ir_gc_w_loses_the_high_word : Eq IROutcome (ir_eval ir_d2 ir_gc_module ir_d0 (ir_vl2 IRScalar.unit_ (IRScalar.int_ 4294967303)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ 7))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 7)))";
const SRC_W_COLLAPSE: &str = "def ir_gc_two_inputs_one_answer : Eq IROutcome (ir_eval ir_d2 ir_gc_module ir_d0 (ir_vl2 IRScalar.unit_ (IRScalar.int_ 7)) ir_mem0 ir_d0) (ir_eval ir_d2 ir_gc_module ir_d0 (ir_vl2 IRScalar.unit_ (IRScalar.int_ 4294967303)) ir_mem0 ir_d0) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 7)))";
const SRC_W_ZEXT_KEEPS: &str = "def ir_gc_zext_keeps_what_trunc_drops : Eq IRStepResult (ir_cast_eval IRCastOp.zext ir_br_tu32 ir_vc_tu64 (IRScalar.int_ 4294967295)) (IRStepResult.value (IRScalar.int_ 4294967295)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 4294967295))";
const SRC_W_ROUNDTRIP: &str = "def ir_gc_roundtrip_does_not_restore : Eq IRStepResult (ir_cast_eval IRCastOp.zext ir_br_tu32 ir_vc_tu64 (IRScalar.int_ (ir_wrap ir_d32 4294967303))) (IRStepResult.value (IRScalar.int_ 7)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 7))";
const SRC_W_ENV_UNREAD: &str = "def ir_gc_env_is_unread : Eq IROutcome (ir_eval ir_d2 ir_gc_module ir_d0 (ir_vl2 IRScalar.unit_ (IRScalar.int_ 7)) ir_mem0 ir_d0) (ir_eval ir_d2 ir_gc_module ir_d0 (ir_vl2 (IRScalar.ptr_ ir_d3) (IRScalar.int_ 7)) ir_mem0 ir_d0) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ 7)))";
const SRC_W_CORRECT: &str = "def ir_gc_correct_witness (n : Nat) : Eq IROutcome (ir_eval ir_d2 ir_gc_module ir_d0 (ir_vl2 IRScalar.unit_ (IRScalar.int_ n)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (IRScalar.int_ (env_get_char_val_closure n)))) := ir_gc_correct ir_mem0 ir_d2 ir_d0 IRScalar.unit_ (IRScalar.int_ n) n (EncodesU64Val.mk n) (Le.refl ir_d2)";
const SRC_W_SOUND: &str = "def ir_gc_machine_sound_witness : Eq Nat (env_get_char_val_closure 4294967303) 7 := ir_gc_machine_sound ir_mem0 ir_d2 ir_d0 IRScalar.unit_ (IRScalar.int_ 4294967303) 4294967303 7 (EncodesU64Val.mk 4294967303) (Le.refl ir_d2) ir_gc_w_loses_the_high_word";
const SRC_W_DISCARD: &str = "def ir_gc_high_word_is_discarded_witness : Eq IROutcome (ir_eval ir_d2 ir_gc_module ir_d0 (ir_vl2 IRScalar.unit_ (IRScalar.int_ 7)) ir_mem0 ir_d0) (ir_eval ir_d2 ir_gc_module ir_d0 (ir_vl2 IRScalar.unit_ (IRScalar.int_ 4294967303)) ir_mem0 ir_d0) := ir_gc_high_word_is_discarded ir_mem0 ir_d2 ir_d0 IRScalar.unit_ 7 4294967303 (Le.refl ir_d2) (Eq.refl Nat 7)";

impl Specification {
    /// Register the NINTH complete width-one chain, and the first over a CAST:
    /// `env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_trunc(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_ENV_GET_CHAR_VAL_CLOSURE, "env_get_char_val_closure: the reflected env::native_reducers_beq_shortcircuit::get_char_val::{closure#0} (native_reducers_beq_shortcircuit.rs:120), which is `|n| n as u32` on a u64. It is ir_wrap ir_d32 -- the canonical low 32 bits -- and NOT a proof that Rust's `as u32` is that residue; that gap is the same shape as env_is_valid_char's and ir_f64_div's and is the smallest of the three. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_B0, "ir_gc_b0: THE WHOLE BODY, TRANSCRIBED FROM THE EMITTED IR (tests/fixtures/get_char_val_trunc.trust-ir.txt). One cast -- opcode trunc, SOURCE u64, DESTINATION u32, operand %1 -- into %2, then `ret %2`. Every one of those four is semantic input and every one of them is a CFG lane: the opcode (zext at these widths is ir_width_fault), the source width (the ir_nat_leb dw sw guard decides fault versus value), the destination width (it is the modulus), and the operand. Before this chain a cast was in NO lane, so this body parsed to an EMPTY Cfg on both sides and two empty CFGs compare equal. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_FUNC, "ir_gc_func: the closure as EvalIR -- TWO parameters (%0 the closure environment, whose emitted type is the UNIT type `()` because this closure captures nothing, and %1 the u64 operand), entry block 0, one block. %0 is bound and never read, and that is not an assumption: the producer's own interpreter differential records `1 proven-never-read opaque param(s) as placeholders` for this body, and A4 quantifies over it with no premise at all. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_MODULE, "ir_gc_module: the module for env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}, TRANSCRIBED FROM MEASURED OUTPUT -- the verbatim trust-ir trustc emitted for the shipped kernel, recorded at tests/fixtures/get_char_val_trunc.trust-ir.txt and checked graph-for-graph and instruction-for-instruction, including the two new cast lanes, by tests/crystal_a1_lineage/get_char_val_trunc.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_MACH0, "ir_gc_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Binds TWO parameters positionally. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_EXACT, "ir_gc_exact: the machine agrees with the reflected closure at EXACTLY 2 steps, for every u64 bit pattern, every heap and every next-address counter. One Eq.refl, and it is affordable for a reason worth stating: the cast's result is IRStepResult.value immediately -- nothing in this body is stuck on a symbolic scrutinee, unlike the fifth, sixth and eighth chains, which all needed the answer abstracted to a parameter before the machine would move. The residue ir_wrap ir_d32 n stays an UNREDUCED application on both sides, so the kernel never computes it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_CORRECT, "ir_gc_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE, FOR A CAST. *** For every u64 bit pattern n, every value representing it, every closure environment value, every heap, every next-address counter and every fuel at or above 2, ir_eval on ir_gc_module returns exactly IROutcome.ret [int_ (ir_wrap ir_d32 n)]. \n\nA0 is measured on the SHIPPED kernel: lowered, spliced, unsupported [], derived_mir.verdict agreed (5 canonical lines identical), markers_exact TRUE over TWO REAL MARKER LINES, the producer's own interpreter differential agreed on 5 sampled inputs, zero calls so the reachable closure is bodyful, and a codegen flip event whose A-LIN lineage equals the coverage row's. A1 is gated by tests/crystal_a1_lineage/get_char_val_trunc.rs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_MACHINE_SOUND, "ir_gc_machine_sound: *** A5, THE INVERSION. *** If the MACHINE running the emitted body answers k, then the reflected closure's value at n IS k -- for every k, not for a chosen one. Goes through A4 rather than restating it, reading the answer back with ir_outcome_nat (registered by the SECOND chain, reused rather than re-declared). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_NEVER_FAULTS, "ir_gc_never_faults: *** NO UB, NO TYPE ERROR, NO STUCK STATE, NO EXHAUSTION -- on ANY u64 bit pattern. *** A corollary of A4. Concretely: the cast never faults not_int, never faults width_bounded, the ret never runs off the end of the block, the operand is always found in the frame, and 2 steps always suffice. Unlike the eighth chain there is no refusal arm to except: a truncation to a narrower integer is TOTAL, which is exactly the difference between a residue and a rounding. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_HIGH_WORD_IS_DISCARDED, "ir_gc_high_word_is_discarded: *** A5 REACHING PAST THE MACHINE'S ANSWER, ONTO THE ARGUMENTS -- and the statement that a TRUNCATION is not a ZERO EXTENSION. *** If two u64 bit patterns have the same low word, then the SHIPPED body's outcome on them is identical: everything above bit 31 is discarded and the emitted code cannot depend on it. \n\nThis is the honest general form of `information is lost`. The unconditional periodicity law -- ir_wrap 32 (n + 2^32) = ir_wrap 32 n for every n -- is deliberately NOT proved: it needs ir_nat_rem periodicity, and buying that with the kernel-native Nat.div/Nat.mod would add accelerated constants whose declared bodies the kernel never consults, i.e. speed bought with trust, which is what the eighth chain refused for finite-plus-finite. The premise is discharged CONCRETELY at (7, 2^32+7) by Eq.refl, which is the kernel deciding the collapse by running it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_TRUNC_LOW_WORD, "ir_gc_trunc_is_the_low_word: the cast instruction's semantics at THIS chain's exact opcode and widths, for every operand -- the value is the canonical low-32 residue and nothing else. Registered separately from A4 so a later lane can cite the instruction without the machine. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_DEST_WIDTH, "ir_gc_dest_width_is_semantic: *** THE DESTINATION WIDTH IS THE MODULUS. *** The same opcode and the same source type at destination u8 computes ir_wrap ir_d8 n where the chain's own instruction computes ir_wrap ir_d32 n. Different functions of the same operand, for every operand -- which is why the cast_tys lane carries the destination and why a transcription that got it wrong is a different program. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_SOURCE_WIDTH, "ir_gc_source_width_is_semantic: *** THE SOURCE WIDTH DECIDES FAULT VERSUS VALUE, so it is not `the operand's type, already implied`. *** ir_trunc_int's guard is ir_nat_leb dw sw, so truncating a u8 to a u32 is ir_width_fault for EVERY scalar -- including well-typed integers. This is the half of the cast type lane that has no analogue in the eighth chain's binop_tys, because a binop has one type and a cast has two. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_OPCODE, "ir_gc_opcode_is_semantic: *** SWAPPING trunc FOR zext AT THESE WIDTHS TURNS A VALUE INTO A FAULT. *** Zero extension requires sw <= dw, so zext u64 -> u32 is ir_width_fault for every scalar, where the shipped body's trunc u64 -> u32 answers. The two opcodes are the same shape and opposite operations, and this is the kernel-executed form of that claim rather than a sentence about it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_ZEXT_EMBEDS, "ir_gc_zext_is_an_embedding: what the semantics computes for the OTHER two cast bodies in the crate -- cert::builder::state::NodeId::index and env::persistent_ext::ExtensionIdx::index, which are `zext u32 -> usize` and are the same body twice. Zero extension canonicalizes at the SOURCE width and embeds in the no-narrower destination, so it loses nothing a canonical operand had. Registered although neither body is chained here, so a later lane owes only the transcription and a decision about `usize` -- which the CFG type lane deliberately leaves unresolved rather than assuming a width for. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_GC_NOT_INT, "ir_gc_non_integer_operand_is_a_type_error: FAIL-CLOSED. A Bool at an integer cast is IROutcome.type_error IRFault.not_int -- not a silent 0/1, not a refusal. ir_as_int declines IRScalar.bool_, which is why EncodesU64Val cannot be weakened to `the argument arrived somehow`. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_FITS, "CONCRETE EXECUTION WITNESS -- 7 survives. The kernel runs the emitted module for two steps on a value that fits in the destination width and returns it unchanged. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_U32MAX, "CONCRETE EXECUTION WITNESS -- 2^32 - 1, the LARGEST value the cast preserves, survives exactly. Affordable because the residue's cost is linear in the QUOTIENT (here zero) and independent of the dividend; on the pre-2026-08-15 substrate this single declaration was the ~9.6-day extrapolation the fifth chain's sentinel drew. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_2P32, "CONCRETE EXECUTION WITNESS -- 2^32, the SMALLEST value the cast sends to zero. Paired with the witness above it pins the boundary from both sides: one below is preserved in full, exactly at it everything is gone. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_LOSES, "*** CONCRETE EXECUTION WITNESS -- 2^32 + 7 becomes 7. INFORMATION IS LOST, and the kernel decided it by running the shipped body. *** This is the witness the whole chain is for: a zero extension could not produce it, and a cast lane that compared only the opcode and the operand would have accepted a transcription that did not. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_COLLAPSE, "*** CONCRETE EXECUTION WITNESS -- TWO DIFFERENT INPUTS, ONE OUTCOME. *** The emitted body run on 7 and on 2^32 + 7 produces the SAME IROutcome, by Eq.refl -- i.e. the kernel evaluated both runs and found them equal. The general conditional form is ir_gc_high_word_is_discarded; this is the instance that shows the condition is inhabited by a genuinely non-injective pair. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ZEXT_KEEPS, "CONTRAST WITNESS -- zext keeps what trunc drops. 2^32 - 1 zero-extended from u32 to u64 is itself; the same magnitude one step higher is annihilated by the trunc above. Registered so `a truncation loses information and a zero extension does not` is a kernel-executed pair rather than a claim. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ROUNDTRIP, "CONTRAST WITNESS -- THE ROUND TRIP DOES NOT RESTORE. Zero-extending the truncation of 2^32 + 7 back to u64 gives 7, not 2^32 + 7. The composite is not the identity, and the kernel computes both halves. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_ENV_UNREAD, "CONCRETE WITNESS -- THE CLOSURE ENVIRONMENT IS GENUINELY UNREAD. The emitted body run with IRScalar.unit_ in %0 (its emitted type is `()`) and with a junk pointer in %0 produces the same outcome, by Eq.refl. That is the executable form of the producer's `1 proven-never-read opaque param(s)` record, and it is why A4 quantifies over %0 with no premise instead of assuming one. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_CORRECT, "ir_gc_correct_witness: A4's premises are all SATISFIABLE, discharged concretely -- the empty heap, the unit closure environment, the exact fuel bound by Le.refl, and one EncodesU64Val.mk. The bit pattern stays universally quantified. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_SOUND, "ir_gc_machine_sound_witness: A5 is not vacuous, and its observation premise is an EXECUTION rather than an assumption -- ir_gc_w_loses_the_high_word, the run that returns 7 from 2^32 + 7. The conclusion is the residue equation, decided by the kernel. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_W_DISCARD, "ir_gc_high_word_is_discarded_witness: the discard theorem's premises are SATISFIABLE at a pair that genuinely differs -- 7 and 2^32 + 7 -- with the low-word equality discharged by Eq.refl, i.e. by the kernel computing both residues. Nothing here is supposed. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The whole body: one `trunc` from u64 to u32 over `%1` into `%2`, then
    /// `ret %2`. Every token in that sentence is a lane the CFG gate compares.
    #[test]
    fn test_the_body_is_one_typed_cast_and_a_ret_of_its_result() {
        assert!(
            SRC_IR_GC_B0.contains("IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1) ir_d2")
        );
        assert!(SRC_IR_GC_B0.contains("IRInst.ret (ir_nl1 ir_d2)"));
        // …and it returns the TRUNCATED value, not the argument.
        assert!(!SRC_IR_GC_B0.contains("IRInst.ret (ir_nl1 ir_d1)"));
        assert!(
            !SRC_IR_GC_B0.contains("condbr")
                && !SRC_IR_GC_B0.contains("switch")
                && !SRC_IR_GC_B0.contains("IRInst.br "),
            "one block, no control flow at all"
        );
    }

    /// The two types are the ones the artifact carries, and they are REUSED
    /// aliases rather than re-declarations.
    #[test]
    fn test_the_widths_are_u64_to_u32_and_the_aliases_are_reused() {
        assert!(SRC_IR_GC_B0.contains("ir_vc_tu64 ir_br_tu32"));
        assert!(
            !SRC_IR_GC_B0.contains("ir_br_tu32 ir_vc_tu64"),
            "source then destination — the reverse is a widening, which faults"
        );
        for src in [
            SRC_ENV_GET_CHAR_VAL_CLOSURE,
            SRC_IR_GC_B0,
            SRC_IR_GC_FUNC,
            SRC_IR_GC_MODULE,
            SRC_IR_GC_MACH0,
        ] {
            assert!(
                !src.contains("def ir_vc_tu64")
                    && !src.contains("def ir_br_tu32")
                    && !src.contains("def ir_d32")
                    && !src.contains("def ir_d64"),
                "a name that already exists is a name to REUSE: {src}"
            );
        }
    }

    /// Two parameters, and the first is the (empty) closure environment.
    #[test]
    fn test_two_parameters_and_the_environment_is_unconstrained() {
        assert!(SRC_IR_GC_FUNC.contains("IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0"));
        assert!(SRC_IR_GC_MACH0.contains("ir_bind_params (ir_nl2 ir_d0 ir_d1)"));
        let statement = SRC_IR_GC_CORRECT.split(":=").next().unwrap_or("");
        assert!(statement.contains("(p : IRScalar)"));
        assert!(
            !statement.contains("EncodesU64Val p"),
            "the environment is never read; constraining it would weaken the theorem"
        );
    }

    /// A4 is universally quantified and its fuel bound is exactly 2.
    #[test]
    fn test_a4_quantifies_over_every_bit_pattern_and_heap() {
        let statement = SRC_IR_GC_CORRECT.split(":=").next().unwrap_or("");
        assert!(statement.contains("(n : Nat)"));
        assert!(statement.contains("(mem : IRList IRMemSlot)"));
        assert!(statement.contains("Le ir_d2 fuel ->"));
        assert!(statement.contains("(env_get_char_val_closure n)"));
        assert!(
            !statement.contains("ir_mem0"),
            "a concrete heap would make this a witness, not a theorem"
        );
        assert_eq!(
            SRC_IR_GC_CORRECT.matches("EncodesU64Val.rec").count(),
            1,
            "one recursor for the one integer parameter"
        );
        // The ret-only fuel monotonicity is enough here: unlike the eighth
        // chain, this A4's conclusion IS an IROutcome.ret.
        assert!(SRC_IR_GC_CORRECT.contains("ir_run_le_ret"));
    }

    /// **The cast semantics is the point, so it is registered as theorems.**
    /// Opcode, source width and destination width must each be shown to change
    /// the function, or the `cast_tys` lane is decoration.
    #[test]
    fn test_both_widths_and_the_opcode_are_shown_to_be_semantic() {
        // destination: a different modulus
        assert!(SRC_IR_GC_DEST_WIDTH.contains("ir_vc_tu64 ir_tU8"));
        assert!(SRC_IR_GC_DEST_WIDTH.contains("ir_wrap ir_d8 n"));
        // source: fault, not value
        assert!(SRC_IR_GC_SOURCE_WIDTH.contains("ir_tU8 ir_br_tu32"));
        assert!(SRC_IR_GC_SOURCE_WIDTH.contains("ir_width_fault"));
        assert!(
            SRC_IR_GC_SOURCE_WIDTH.contains("(a : IRScalar)"),
            "for EVERY scalar, including well-typed integers"
        );
        // opcode: zext at the chain's own widths is a fault
        assert!(SRC_IR_GC_OPCODE.contains("IRCastOp.zext ir_vc_tu64 ir_br_tu32"));
        assert!(SRC_IR_GC_OPCODE.contains("ir_width_fault"));
        // …and the chain's own instruction is a VALUE, so the three above are
        // genuinely different outcomes rather than three spellings of one.
        assert!(SRC_IR_GC_TRUNC_LOW_WORD.contains("IRStepResult.value"));
        assert!(SRC_IR_GC_TRUNC_LOW_WORD.contains("ir_wrap ir_d32 n"));
    }

    /// The information loss is proved conditionally and executed concretely,
    /// and the unconditional law is NOT claimed.
    #[test]
    fn test_information_loss_is_conditional_general_plus_concrete_witnesses() {
        let statement = SRC_IR_GC_HIGH_WORD_IS_DISCARDED
            .split(":=")
            .next()
            .unwrap_or("");
        assert!(statement.contains("(n : Nat) (m : Nat)"));
        assert!(
            statement.contains(
                "(heq : Eq Nat (env_get_char_val_closure n) (env_get_char_val_closure m))"
            ),
            "the low-word equality is a PREMISE; without it the statement would be false"
        );
        assert!(SRC_IR_GC_HIGH_WORD_IS_DISCARDED
            .contains("ir_gc_correct mem fuel na p (IRScalar.int_ n) n"));
        assert!(SRC_IR_GC_HIGH_WORD_IS_DISCARDED
            .contains("ir_gc_correct mem fuel na p (IRScalar.int_ m) m"));
        // the collapse itself, executed
        assert!(SRC_W_LOSES.contains("IRScalar.int_ 4294967303"));
        assert!(SRC_W_LOSES.contains("IROutcome.ret (ir_vl1 (IRScalar.int_ 7))"));
        assert!(SRC_W_COLLAPSE.contains("IRScalar.int_ 7"));
        assert!(SRC_W_COLLAPSE.contains("IRScalar.int_ 4294967303"));
        // and the zext contrast
        assert!(SRC_W_ZEXT_KEEPS.contains("IRCastOp.zext ir_br_tu32 ir_vc_tu64"));
        assert!(SRC_W_ROUNDTRIP.contains("ir_wrap ir_d32 4294967303"));
        assert!(SRC_W_ROUNDTRIP.contains("IRScalar.int_ 7"));
    }

    /// The boundary of the preserved range is pinned from both sides.
    #[test]
    fn test_the_destination_boundary_is_pinned_from_both_sides() {
        assert!(SRC_W_U32MAX.contains("IRScalar.int_ 4294967295"));
        assert!(SRC_W_U32MAX.contains("IROutcome.ret (ir_vl1 (IRScalar.int_ 4294967295))"));
        assert!(SRC_W_2P32.contains("IRScalar.int_ 4294967296"));
        assert!(SRC_W_2P32.contains("IROutcome.ret (ir_vl1 (IRScalar.int_ 0))"));
    }

    /// Every witness runs the machine (or the instruction), and the fail-closed
    /// ones are tagged faults rather than values.
    #[test]
    fn test_witnesses_execute_and_the_negative_ones_fault() {
        for src in [SRC_W_FITS, SRC_W_U32MAX, SRC_W_2P32, SRC_W_LOSES] {
            assert!(src.contains("ir_eval ir_d2 ir_gc_module"));
            assert!(src.contains(":= Eq.refl IROutcome"));
        }
        assert!(SRC_IR_GC_NOT_INT.contains("IROutcome.type_error IRFault.not_int"));
        assert!(SRC_IR_GC_NOT_INT.contains("(b : Bool)"));
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [
            SRC_ENV_GET_CHAR_VAL_CLOSURE,
            SRC_IR_GC_B0,
            SRC_IR_GC_FUNC,
            SRC_IR_GC_MODULE,
            SRC_IR_GC_MACH0,
            SRC_IR_GC_EXACT,
            SRC_IR_GC_CORRECT,
            SRC_IR_GC_MACHINE_SOUND,
            SRC_IR_GC_NEVER_FAULTS,
            SRC_IR_GC_HIGH_WORD_IS_DISCARDED,
            SRC_IR_GC_TRUNC_LOW_WORD,
            SRC_IR_GC_DEST_WIDTH,
            SRC_IR_GC_SOURCE_WIDTH,
            SRC_IR_GC_OPCODE,
            SRC_IR_GC_ZEXT_EMBEDS,
            SRC_IR_GC_NOT_INT,
            SRC_W_FITS,
            SRC_W_U32MAX,
            SRC_W_2P32,
            SRC_W_LOSES,
            SRC_W_COLLAPSE,
            SRC_W_ZEXT_KEEPS,
            SRC_W_ROUNDTRIP,
            SRC_W_ENV_UNREAD,
            SRC_W_CORRECT,
            SRC_W_SOUND,
            SRC_W_DISCARD,
        ] {
            let mut d: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => d += 1,
                    ')' => d -= 1,
                    _ => {}
                }
                assert!(d >= 0, "unbalanced parens in {src}");
            }
            assert_eq!(d, 0, "unbalanced parens in {src}");
            assert!(src.is_ascii(), "spec sources must be ASCII");
        }
    }
}
