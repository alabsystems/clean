// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The ELEVENTH complete width-one chain, and the FIRST over a body that
//! computes an address and dereferences it: `env::types::SimpPriority::value`.**
//!
//! Every earlier chain in this tree reads memory at most through the receiver
//! pointer it was handed. This one does not: its `Custom` arm materialises a
//! byte offset, `gep`s the receiver by it, and loads through the RESULT. The
//! address the machine dereferences is one it computed.
//!
//! ## Why this body, measured rather than chosen
//!
//! `data/crystal_frontier_census_2026-08-20.json`, re-derived at HEAD by
//! `scripts/crystal_frontier_census.py` from one sealed-driver whole-crate
//! dump of the shipped `clean-kernel` (trust seal `50879dc8…`, guard PASS
//! before every run, `clean-kernel` tree `a3ae6c21f`):
//!
//! ```text
//! construct      carry  agreed  mk_exact  bodyful  ag+bf  flipO3  flipO0
//! gep             1304       4         4       18      2       4       4
//! call            4823     450         2       52     11       2     414
//! ```
//!
//! The 2026-08-16 census recorded `gep` and `call` at **flip_O3 = 0 and
//! flip_O0 = 0**, and `docs/analysis/frontier-2026-08-16.md` §0.4 concluded
//! "`call` has 0 and recursion has 0 at the deployed profile". Five producer
//! waves later (GS, CP, DR, W3, W3b) `gep` flips **4** times at `-O3` and
//! `call` **2**; at `-O0` `call` flips **414**. That table was stale and this
//! module is the first thing built on the re-measured one.
//!
//! Of the four `gep`-carrying `-O3` flips, two are `level::Level::is_zero` and
//! `level::Level::is_nonzero`, whose reachable closure is NOT bodyful —
//! `<LevelArc as Deref>::deref` calls two DECLARATIONS, so links 3/4 cannot
//! hold for them and `docs/CRYSTAL_STATUS.md` records why. The other two are
//! `env::types::Reducibility::height` and this body. Between those two:
//!
//! | axis | `Reducibility::height` | `SimpPriority::value` |
//! |---|---|---|
//! | `gep` sits on | the explicit switch case | **the DEFAULT edge** |
//! | non-`gep` arm materialises | `0u32` | **`1000u32`, a real width-32 residue** |
//! | `switch-map` perturbation | `applications=0` — **never reaches the body** | `applications=1`, `agreed -> mismatch` |
//!
//! The perturbation is why this body and not the other. A fail-closed control
//! that cannot reach the body it is controlling is not a control, and the
//! measured `applications=0` on `height` is recorded in
//! `tests/fixtures/simp_priority_value.lineage.json` rather than worked around.
//!
//! ## What is proved
//!
//! For EVERY `SimpPriority`, every heap representing it, and every fuel at or
//! above 8, `ir_eval` on the MINTED `ir_pv_module` returns exactly
//! `simp_priority_value p` (`ir_pv_correct`); if the machine answers `n` then
//! `simp_priority_value p = n` (`ir_pv_machine_sound`); and on any represented
//! priority it never faults, never traps and never exhausts fuel
//! (`ir_pv_never_faults`). Both emitted arms are executed by the kernel as
//! witnesses.
//!
//! ## The three facts that make this a MEMORY chain rather than a claim of one
//!
//! * `ir_pv_off_is_four` — the offset the machine computes from the emitted
//!   `const i64 4` is 4. The relation is stated at `ir_wrap ir_d64 ir_d4`, the
//!   term the machine actually produces, and this theorem is what says it is
//!   the byte offset the producer meant. (The `bvar_in_range` chain's lesson:
//!   name the term the machine materialises, not a spelling of it.)
//! * `ir_pv_on_custom_seven` / `ir_pv_on_custom_eleven` — two heaps differing
//!   ONLY in the cell at `a + 4`, two different answers. The load through the
//!   `gep` result is load-bearing; the theorem is not constant.
//! * `ir_pv_custom_without_payload_is_ub` — a `Custom` heap carrying the tag
//!   cell and NOTHING at `a + 4` evaluates to `IROutcome.ub IRFault.bad_addr`.
//!   The machine really does dereference the computed address, and
//!   `EncodesSimpPriority.custom`'s second premise is doing work rather than
//!   decorating the statement. `ir_pv_on_default` is its mirror: the DEFAULT
//!   arm returns 1000 on a one-cell heap, so that path provably never touches
//!   `a + 4`.
//!
//! ## What this does NOT establish
//!
//! * **The layout is a PREMISE, not a theorem.** `EncodesSimpPriority.custom`
//!   asserts a cell at `a + ir_pv_off` holding the payload. Nothing here proves
//!   that Rust puts `Custom`'s `u32` at byte 4 of a `SimpPriority`, and nothing
//!   here proves that a byte offset is a cell offset — EvalIR's heap is
//!   cell-addressed and inherits the producer's `+4` as `+4`. That is the same
//!   class as `EncodesCleanMode`'s tag premise, one slot further out, and it is
//!   where this chain's representation assumption lives.
//! * The link between the proved module and the emitted one is the A2 MINT
//!   (`tests/crystal_a2_mint_pv.rs`) plus the A1 comparator, not a semantic
//!   proof that Clean's `IRInst` encoding means what trust-ir's does.
//! * The lineage digest is RECORDED, not recomputed from the artifact by the
//!   Clean side.
//! * The payload is a `Nat` and the emitted load is a `u32`. The model's `load`
//!   is the identity on a non-`undef` cell (`ir_load_value`), so the theorem
//!   quantifies over payloads a `u32` cannot hold. That is a COARSENESS of the
//!   model, stated: it is why `ir_pv_correct` is true for every `Nat` and why
//!   that is weaker than it looks.
//! * Width one. By itself it retires no kernel-wide trust assumption.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The MINTED module script, generated from the emitted artifact by
/// `ir_mint::mint` and gated byte for byte by `tests/crystal_a2_mint_pv.rs`.
/// It is not hand transcribed and must not be hand edited.
const MINTED_IR_PV: &str = include_str!("generated/ir_pv.defs.txt");

/// The per-definition rationale for the minted script, in registration order.
/// One row per `def` line; the count is asserted below, so a regenerated script
/// with a different shape fails rather than silently reusing the wrong doc.
const MINTED_IR_PV_DOCS: &[&str] = &[
    "ir_pv_tprio: the SimpPriority enum type, crate interning id 127 -- the id the emitted body names in `%2 = load enum.127, ptr %0`. MINTED from generated/ir_pv.tags.json. The alias reads `IRTy.enum_ 127` and not `IRTy.enum_ ir_d127`: 127 is outside the registered ir_d0..ir_d16 atom pool, and before 2026-08-20 `Tags::alias_defs` would have emitted a constant the specification does not declare. DerivedProved, zero axiom_deps.",
    "ir_pv_b0: entry block, MINTED FROM THE EMITTED ARTIFACT. Load the SimpPriority, read its discriminant at width 32, and dispatch: ONE explicit case (tag 0 -> b1) and a default edge (-> b2) that carries the Custom arm. The exhaustive-enum flag is the MEASURED false. DerivedProved, zero axiom_deps.",
    "ir_pv_b1: Default => the materialised constant 1000 at width 32, then br to the join. This arm reads NO memory, which ir_pv_on_default pins by evaluating it on a heap that has no cell at a+4. DerivedProved, zero axiom_deps.",
    "ir_pv_b2: *** THE MEMORY ARM. *** The default edge, carrying Custom: materialise the byte offset 4 at width 64, `gep inbounds i8` the receiver by it, and LOAD THROUGH THE RESULT at width 32. Four nodes, so the minter emits the generic IRList.cons spine rather than an ir_bdN builder -- there is no ir_bd4. DerivedProved, zero axiom_deps.",
    "ir_pv_b3: the JOIN block, taking a u32 block PARAMETER. Both arms funnel through br into bb3(%1: u32) and return that parameter. DerivedProved, zero axiom_deps.",
    "ir_pv_func: SimpPriority::value as EvalIR: id 0, one parameter (the &SimpPriority receiver, SSA id 0), entry block 0, four blocks -- matching the emitted body's control-flow graph exactly. DerivedProved, zero axiom_deps.",
    "ir_pv_module: the module for SimpPriority::value, MINTED from the emitted trust-ir rather than transcribed from it. Reader A (the artifact binary), reader B (the emitted text) and reader C (this elaborated term) agree on it; see crate::ir_mint for what that establishes and what it does not. DerivedProved, zero axiom_deps.",
];

/// The minted script's lines, in registration order.
///
/// ONE source of truth, shared by [`Specification::add_eval_ir_priority`] and
/// anything that must run the machine on *the registered module* rather than on
/// a second transcription of it.
static MINTED_IR_PV_LINES: std::sync::LazyLock<Vec<&'static str>> =
    std::sync::LazyLock::new(|| {
        MINTED_IR_PV
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect()
    });

/// The minted `SimpPriority::value` module definitions, in registration order.
#[must_use]
pub fn ir_pv_module_defs() -> &'static [&'static str] {
    &MINTED_IR_PV_LINES
}

const SRC_SIMPPRIORITYR: &str =
    "inductive SimpPriorityR : Type\n| default_ : SimpPriorityR\n| custom : Nat -> SimpPriorityR";

const SRC_IR_PV_DFLT: &str = "def ir_pv_dflt : Nat := ir_wrap ir_d32 1000";

const SRC_IR_PV_DFLT_IS_1000: &str =
    "def ir_pv_dflt_is_1000 : Eq Nat ir_pv_dflt 1000 := Eq.refl Nat 1000";

const SRC_IR_PV_OFF: &str = "def ir_pv_off : Nat := ir_wrap ir_d64 ir_d4";

const SRC_IR_PV_OFF_IS_FOUR: &str =
    "def ir_pv_off_is_four : Eq Nat ir_pv_off ir_d4 := Eq.refl Nat ir_d4";

const SRC_SIMP_PRIORITY_TAG: &str = "def simp_priority_tag (p : SimpPriorityR) : Nat := SimpPriorityR.rec (fun (_ : SimpPriorityR) => Nat) ir_d0 (fun (_ : Nat) => ir_d1) p";

const SRC_SIMP_PRIORITY_VALUE: &str = "def simp_priority_value (p : SimpPriorityR) : Nat := SimpPriorityR.rec (fun (_ : SimpPriorityR) => Nat) ir_pv_dflt (fun (v : Nat) => v) p";

const SRC_ENCODESSIMPPRIORITY: &str = "inductive EncodesSimpPriority (mem : IRList IRMemSlot) : IRScalar -> SimpPriorityR -> Type\n| default_ : forall (a : Nat) (fs : IRScalar), Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 fs) Bool.true)) -> EncodesSimpPriority mem (IRScalar.ptr_ a) SimpPriorityR.default_\n| custom : forall (a : Nat) (fs : IRScalar) (v : Nat), Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true)) -> Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_pv_off)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_pv_off) (IRScalar.int_ v) Bool.true)) -> EncodesSimpPriority mem (IRScalar.ptr_ a) (SimpPriorityR.custom v)";

const SRC_IR_PV_ON_DEFAULT: &str = "def ir_pv_on_default : Eq IROutcome (ir_eval ir_d8 ir_pv_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_pv_dflt))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_pv_dflt)))";

const SRC_IR_PV_ON_CUSTOM_SEVEN: &str = "def ir_pv_on_custom_seven : Eq IROutcome (ir_eval ir_d8 ir_pv_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d1 ir_sp0) (ir_cell ir_d4 (IRScalar.int_ ir_d7) ir_mem0)) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d7))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d7)))";

const SRC_IR_PV_ON_CUSTOM_ELEVEN: &str = "def ir_pv_on_custom_eleven : Eq IROutcome (ir_eval ir_d8 ir_pv_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d1 ir_sp0) (ir_cell ir_d4 (IRScalar.int_ ir_d11) ir_mem0)) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d11))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d11)))";

const SRC_IR_PV_CUSTOM_WITHOUT_PAYLOAD_IS_UB: &str = "def ir_pv_custom_without_payload_is_ub : Eq IROutcome (ir_eval ir_d8 ir_pv_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d1 ir_sp0) ir_mem0) ir_d1) (IROutcome.ub IRFault.bad_addr) := Eq.refl IROutcome (IROutcome.ub IRFault.bad_addr)";

const SRC_IR_PV_MACH0: &str = "def ir_pv_mach0 (mem : IRList IRMemSlot) (a : Nat) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 (IRScalar.ptr_ a)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";

const SRC_IR_PV_AFTER_LOAD: &str = "def ir_pv_after_load (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (o : (IROption IRMemSlot)) : IRConfig := ir_bind_result (ir_pv_mach0 mem a na) (ir_nl1 ir_d2) (ir_load_slot o)";

const SRC_IR_PV_CFG1: &str = "def ir_pv_cfg1 (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (fs : IRScalar) : IRConfig := ir_steps ir_d4 ir_pv_module (ir_pv_after_load mem a na (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true)))";

const SRC_IR_PV_AFTER_GEP_LOAD: &str = "def ir_pv_after_gep_load (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (fs : IRScalar) (o : (IROption IRMemSlot)) : IRConfig := ir_bind_result (ir_cfg_mach (ir_pv_cfg1 mem a na fs) (ir_pv_mach0 mem a na)) (ir_nl1 ir_d7) (ir_load_slot o)";

const SRC_IR_PV_DEFAULT_ARM: &str = "def ir_pv_default_arm (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (fs : IRScalar) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 fs) Bool.true))) : Eq IROutcome (ir_run ir_d8 ir_pv_module (IRConfig.running (ir_pv_mach0 mem a na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_pv_dflt))) := Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d7 ir_pv_module (ir_pv_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_pv_dflt)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 fs) Bool.true)) h) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_pv_dflt))))";

const SRC_IR_PV_CFG1_IS_FOUR_STEPS: &str = "def ir_pv_cfg1_is_four_steps (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (fs : IRScalar) : Eq IRConfig (ir_steps ir_d4 ir_pv_module (ir_pv_after_load mem a na (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true)))) (ir_pv_cfg1 mem a na fs) := Eq.refl IRConfig (ir_pv_cfg1 mem a na fs)";

const SRC_IR_PV_REACHES_THE_SECOND_LOAD: &str = "def ir_pv_reaches_the_second_load (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (fs : IRScalar) : Eq IRConfig (ir_steps ir_d5 ir_pv_module (ir_pv_after_load mem a na (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true)))) (ir_pv_after_gep_load mem a na fs (ir_mem_lookup mem (Nat.add a ir_pv_off))) := Eq.refl IRConfig (ir_pv_after_gep_load mem a na fs (ir_mem_lookup mem (Nat.add a ir_pv_off)))";

const SRC_IR_PV_SPLIT: &str = "def ir_pv_split (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (fs : IRScalar) : Eq IROutcome (ir_run ir_d7 ir_pv_module (ir_pv_after_load mem a na (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true)))) (ir_run ir_d2 ir_pv_module (ir_pv_after_gep_load mem a na fs (ir_mem_lookup mem (Nat.add a ir_pv_off)))) := Eq.refl IROutcome (ir_run ir_d2 ir_pv_module (ir_pv_after_gep_load mem a na fs (ir_mem_lookup mem (Nat.add a ir_pv_off))))";

const SRC_IR_PV_CUSTOM_ARM: &str = "def ir_pv_custom_arm (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (fs : IRScalar) (v : Nat) (h1 : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true))) (h2 : Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_pv_off)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_pv_off) (IRScalar.int_ v) Bool.true))) : Eq IROutcome (ir_run ir_d8 ir_pv_module (IRConfig.running (ir_pv_mach0 mem a na))) (IROutcome.ret (ir_vl1 (IRScalar.int_ v))) := Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d7 ir_pv_module (ir_pv_after_load mem a na o)) (IROutcome.ret (ir_vl1 (IRScalar.int_ v)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true)) h1) (Eq.trans IROutcome (ir_run ir_d7 ir_pv_module (ir_pv_after_load mem a na (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true)))) (ir_run ir_d2 ir_pv_module (ir_pv_after_gep_load mem a na fs (ir_mem_lookup mem (Nat.add a ir_pv_off)))) (IROutcome.ret (ir_vl1 (IRScalar.int_ v))) (ir_pv_split mem a na fs) (Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IROutcome (ir_run ir_d2 ir_pv_module (ir_pv_after_gep_load mem a na fs o)) (IROutcome.ret (ir_vl1 (IRScalar.int_ v)))) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_pv_off) (IRScalar.int_ v) Bool.true)) (ir_mem_lookup mem (Nat.add a ir_pv_off)) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_pv_off)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_pv_off) (IRScalar.int_ v) Bool.true)) h2) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ v))))))";

const SRC_IR_PV_CORRECT: &str = "def ir_pv_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (p : SimpPriorityR) (henc : EncodesSimpPriority mem r p) : Le ir_d8 fuel -> Eq IROutcome (ir_eval fuel ir_pv_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (simp_priority_value p)))) := EncodesSimpPriority.rec mem (fun (s0 : IRScalar) (p0 : SimpPriorityR) (_ : EncodesSimpPriority mem s0 p0) => Le ir_d8 fuel -> Eq IROutcome (ir_eval fuel ir_pv_module ir_d0 (ir_vl1 s0) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (simp_priority_value p0))))) (fun (a : Nat) (fs : IRScalar) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 fs) Bool.true))) (hle : Le ir_d8 fuel) => ir_run_le_ret ir_pv_module ir_d8 fuel hle (IRConfig.running (ir_pv_mach0 mem a na)) (ir_vl1 (IRScalar.int_ ir_pv_dflt)) (ir_pv_default_arm mem a na fs h)) (fun (a : Nat) (fs : IRScalar) (v : Nat) (h1 : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 fs) Bool.true))) (h2 : Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_pv_off)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_pv_off) (IRScalar.int_ v) Bool.true))) (hle : Le ir_d8 fuel) => ir_run_le_ret ir_pv_module ir_d8 fuel hle (IRConfig.running (ir_pv_mach0 mem a na)) (ir_vl1 (IRScalar.int_ v)) (ir_pv_custom_arm mem a na fs v h1 h2)) r p henc";

const SRC_IR_PV_CORRECT_WITNESS: &str = "def ir_pv_correct_witness : Eq IROutcome (ir_eval ir_d8 ir_pv_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d1 ir_sp0) (ir_cell ir_d4 (IRScalar.int_ ir_d7) ir_mem0)) ir_d1) (IROutcome.ret (ir_vl1 (IRScalar.int_ (simp_priority_value (SimpPriorityR.custom ir_d7))))) := ir_pv_correct (ir_cell ir_d0 (ir_var ir_d1 ir_sp0) (ir_cell ir_d4 (IRScalar.int_ ir_d7) ir_mem0)) ir_d8 ir_d1 (IRScalar.ptr_ ir_d0) (SimpPriorityR.custom ir_d7) (EncodesSimpPriority.custom (ir_cell ir_d0 (ir_var ir_d1 ir_sp0) (ir_cell ir_d4 (IRScalar.int_ ir_d7) ir_mem0)) ir_d0 ir_sp0 ir_d7 (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d1 ir_sp0) Bool.true))) (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d4 (IRScalar.int_ ir_d7) Bool.true)))) (Le.refl ir_d8)";

const SRC_IR_PV_MACHINE_SOUND: &str = "def ir_pv_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (p : SimpPriorityR) (n : Nat) (henc : EncodesSimpPriority mem r p) (hle : Le ir_d8 fuel) (hret : Eq IROutcome (ir_eval fuel ir_pv_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ n)))) : Eq Nat (simp_priority_value p) n := Eq.cong IROutcome Nat ir_outcome_nat (IROutcome.ret (ir_vl1 (IRScalar.int_ (simp_priority_value p)))) (IROutcome.ret (ir_vl1 (IRScalar.int_ n))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ (simp_priority_value p)))) (ir_eval fuel ir_pv_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ n))) (Eq.symm IROutcome (ir_eval fuel ir_pv_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (simp_priority_value p)))) (ir_pv_correct mem fuel na r p henc hle)) hret)";

const SRC_IR_PV_MACHINE_SOUND_WITNESS: &str = "def ir_pv_machine_sound_witness : Eq Nat (simp_priority_value (SimpPriorityR.custom ir_d7)) ir_d7 := ir_pv_machine_sound (ir_cell ir_d0 (ir_var ir_d1 ir_sp0) (ir_cell ir_d4 (IRScalar.int_ ir_d7) ir_mem0)) ir_d8 ir_d1 (IRScalar.ptr_ ir_d0) (SimpPriorityR.custom ir_d7) ir_d7 (EncodesSimpPriority.custom (ir_cell ir_d0 (ir_var ir_d1 ir_sp0) (ir_cell ir_d4 (IRScalar.int_ ir_d7) ir_mem0)) ir_d0 ir_sp0 ir_d7 (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d1 ir_sp0) Bool.true))) (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d4 (IRScalar.int_ ir_d7) Bool.true)))) (Le.refl ir_d8) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d7))))";

const SRC_IR_PV_MACHINE_SOUND_DEFAULT_WITNESS: &str = "def ir_pv_machine_sound_default_witness : Eq Nat (simp_priority_value SimpPriorityR.default_) ir_pv_dflt := ir_pv_machine_sound (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) ir_d8 ir_d1 (IRScalar.ptr_ ir_d0) SimpPriorityR.default_ ir_pv_dflt (EncodesSimpPriority.default_ (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) ir_d0 ir_sp0 (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d0 ir_sp0) Bool.true)))) (Le.refl ir_d8) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_pv_dflt))))";

const SRC_IR_PV_NEVER_FAULTS: &str = "def ir_pv_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (p : SimpPriorityR) (henc : EncodesSimpPriority mem r p) (hle : Le ir_d8 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_pv_module ir_d0 (ir_vl1 r) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_pv_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.int_ (simp_priority_value p)))) (ir_pv_correct mem fuel na r p henc hle)";

impl Specification {
    /// The width-one chain over the MINTED shape of `SimpPriority::value`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or kernel-check.
    pub(super) fn add_eval_ir_priority(&mut self) -> Result<(), SpecError> {
        self.add_inductive(SRC_SIMPPRIORITYR, "SimpPriorityR: the reflected SimpPriority (env/types.rs:218). TWO variants, and unlike every fieldless reflected type chained before it one of them CARRIES A PAYLOAD -- which is the whole reason this body geps. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_DFLT, "ir_pv_dflt: the value the Default arm materialises, named as the term the MACHINE produces (`ir_wrap ir_d32 1000`) rather than as a spelling of it. This is the bvar_in_range lesson applied on purpose: naming the residue on one side and the literal on the other made a 6-step chain take five days of kernel reduction. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_DFLT_IS_1000, "ir_pv_dflt_is_1000: and that residue IS 1000 -- the same constant `LEAN_DEFAULT_INSTANCE_PRIORITY` names at env/types.rs:210. Kernel-checked by reduction, so the previous definition is pinned to a number a reader recognises instead of being taken on faith. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_OFF, "ir_pv_off: the byte offset the machine computes from the emitted `%5 = const i64 4`, again named as the term the machine produces (`ir_wrap ir_d64 ir_d4`). This is the address arithmetic the whole chain exists to exercise. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_OFF_IS_FOUR, "ir_pv_off_is_four: *** THE OFFSET IS 4. *** The width-64 residue of the emitted constant is the byte offset the producer meant, kernel-checked by reduction rather than asserted in a comment. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_SIMP_PRIORITY_TAG, "simp_priority_tag: each variant's discriminant, 0 and 1 in declaration order. The ONE place the reflected type meets the emitted layout's tag. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_SIMP_PRIORITY_VALUE, "simp_priority_value: the reflected `SimpPriority::value` (env/types.rs:228) -- 1000 on Default, the payload on Custom. DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODESSIMPPRIORITY, "EncodesSimpPriority mem p x: the heap at p represents priority x. *** TWO CELLS ON THE CUSTOM ARM, AND THAT IS THE NEW THING. *** Default needs one live cell whose field 0 is the tag, with the payload spine UNIVERSALLY QUANTIFIED (`fs`) because the emitted body never reads it through extractfield. Custom needs that cell AND a second live cell at `Nat.add a ir_pv_off` holding the payload -- the address this body computes with a gep and then dereferences. Stated as EQUATIONS on ir_mem_lookup: membership would be satisfiable by a shadowed duplicate while the machine reads a different cell. THE LAYOUT IS A PREMISE: nothing here proves Rust puts the u32 at byte 4, nor that a byte offset is a cell offset. DerivedProved, zero axiom_deps.")?;
        // The module is REPLAYED from the minted script, line for line. A
        // generated artifact registered by the same code a gate regenerates is
        // the `kernel_core_red_env` posture: Clean's parser and elaborator still
        // turn the text into the term the theorems are about.
        let minted = ir_pv_module_defs();
        if minted.len() != MINTED_IR_PV_DOCS.len() {
            return Err(SpecError::EnvError(format!(
                "the minted ir_pv script has {} definitions but {} rationales are declared; \
                 regenerate the docs table with the script rather than reusing it",
                minted.len(),
                MINTED_IR_PV_DOCS.len()
            )));
        }
        for (line, doc) in minted.iter().zip(MINTED_IR_PV_DOCS) {
            self.add_recursive_def(line, doc)?;
        }
        self.add_recursive_def(SRC_IR_PV_ON_DEFAULT, "GATE WITNESS: Default. The kernel runs the machine, 6 steps, on a ONE-CELL heap -- there is no cell at a+4 at all, so this also pins that the Default arm never touches the payload address. Had it, the answer would be `ub bad_addr`, which is exactly what the next-but-two witness shows. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_ON_CUSTOM_SEVEN, "GATE WITNESS: Custom(7), through the DEFAULT EDGE and the gep. The kernel runs the machine 8 steps: load, extractfield, switch, const, gep, load, br, ret -- and the sixth step dereferences an address the fifth computed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_ON_CUSTOM_ELEVEN, "GATE WITNESS: Custom(11). Identical to the previous heap in every cell EXCEPT the one at a+4, and the answer moves with it. This is the non-vacuity of the load: a theorem that ignored the second cell would prove both, and it cannot. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_CUSTOM_WITHOUT_PAYLOAD_IS_UB, "*** THE MACHINE REALLY DEREFERENCES THE COMPUTED ADDRESS. *** A Custom heap with the tag cell and NOTHING at a+4 evaluates to `ub bad_addr`, kernel-checked by reduction. So EncodesSimpPriority.custom's second premise is load-bearing and not decoration, and the gep is not an address the machine merely computes and discards. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_MACH0, "ir_pv_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_AFTER_LOAD, "ir_pv_after_load: the entry step with the heap lookup made SYNTACTIC, so Eq.subst has something to rewrite. Binds %2, matching the emitted SSA numbering. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_CFG1, "ir_pv_cfg1: the configuration four steps past the entry load, on the Custom tag -- extractfield, switch, const, gep. It is a CLOSED definition because those four steps reduce with `a`, `na`, `mem` and the payload spine all symbolic: nothing in them reads memory. The next step is the one that does. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_AFTER_GEP_LOAD, "ir_pv_after_gep_load: the SECOND load, with ITS heap lookup made syntactic -- the same device as ir_pv_after_load, one dereference further in, at the address the gep produced. This is the definition every earlier chain had no need of, because no earlier chain read memory twice. Binds %7. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_DEFAULT_ARM, "ir_pv_default_arm: the machine agrees with the reflected value on Default at EXACTLY 8 steps of budget (it halts in 6). One Eq.subst on the entry lookup, then Eq.refl -- the kernel executes the arm. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_CFG1_IS_FOUR_STEPS, "ir_pv_cfg1_is_four_steps: the entry load plus FOUR steps -- extractfield, switch, const, gep -- is exactly `ir_pv_cfg1`, kernel-checked by reduction rather than counted in a comment. A step count is the one thing in a chain like this that a reader cannot check by eye, and getting it wrong is how a two-lookup proof fails with a message about constructor discriminants. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_REACHES_THE_SECOND_LOAD, "ir_pv_reaches_the_second_load: *** FIVE steps past the entry load IS the second load, at the address the gep computed. *** The right-hand side is the config with that heap lookup made SYNTACTIC; the equation says the machine really arrives there and really reads `ir_mem_lookup mem (Nat.add a ir_pv_off)`. This is the fact the whole memory claim rests on, and it is a theorem rather than a step count in prose. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_SPLIT, "ir_pv_split: the same identity carried into `ir_run`, so the custom arm can be proved by rewriting at the second lookup. Seven steps from the entry load split as FIVE (up to and INCLUDING the gep'd load) plus TWO (the br and the ret). The five/two split is not a guess: `ir_pv_reaches_the_second_load` above pins the first half by reduction, and this lemma is where the arithmetic became a theorem instead of a comment -- the first attempt wrote three and failed, because `ir_pv_after_gep_load` is the config AFTER that load, not before it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_CUSTOM_ARM, "ir_pv_custom_arm: *** THE TWO-LOOKUP PROOF. *** Custom in exactly 8 steps, through TWO nested Eq.substs: the outer one fixes the entry load's lookup at `a`, the inner one fixes the gep'd load's lookup at `Nat.add a ir_pv_off`, and the kernel discharges the rest by executing the body. The two are chained rather than combined because they are not simultaneous: the second address does not exist until the machine has computed it, which is what ir_pv_cfg1 names. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_CORRECT, "ir_pv_correct: *** THE EQUALITY THEOREM, OVER THE MINTED SHAPE. *** For every SimpPriority, every heap representing it, and every fuel at or above 8, ir_eval on ir_pv_module returns exactly simp_priority_value p. The module is GENERATED from the emitted artifact (generated/ir_pv.defs.txt), not transcribed, and tests/crystal_a2_mint_pv.rs fails closed if the registered script is not what minting the committed core module produces. A0 is measured at HEAD: derived_mir.verdict = agreed, markers_exact = true and NON-VACUOUS (2 marker lines, not 0), with no widening of the codegen-flip gate. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_CORRECT_WITNESS, "ir_pv_correct_witness: not vacuous, and the witness RUNS THE MACHINE at Custom -- the arm that geps. Every premise is discharged concretely: the representation by EncodesSimpPriority.custom with both cell equations by Eq.refl, and the fuel bound by Le.refl at exactly 8. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_MACHINE_SOUND, "ir_pv_machine_sound: *** A5 FOR THIS CHAIN. *** If the MACHINE answers n on a heap representing p, then simp_priority_value p really is n. An INVERSION, from an observation about the running machine back to the reflected function. The composition is an equality argument, not an injectivity lemma: apply ir_outcome_nat to both sides with Eq.cong and let the kernel compute. That is why this stage must run AFTER add_eval_ir_kind_ord, which registers it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_MACHINE_SOUND_WITNESS, "ir_pv_machine_sound_witness: A5 is not vacuous, and the witness RUNS THE MACHINE through the gep -- the `hret` premise is discharged by Eq.refl, which the kernel checks by executing the body over the two-cell heap. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_MACHINE_SOUND_DEFAULT_WITNESS, "ir_pv_machine_sound_default_witness: the same inversion on the other arm, over the one-cell heap. Both arms of the emitted switch are exercised by an A5 instance, not just by an A4 one. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_PV_NEVER_FAULTS, "ir_pv_never_faults: *** NO UB, NO PANIC, NO EXHAUSTION -- on any REPRESENTED priority. *** A corollary of ir_pv_correct. IROutcome separates success from ub, type_error, unmodelled, stuck and fuel_out, so proving the outcome is a ret rules out all five at once. Read it against ir_pv_custom_without_payload_is_ub, which is the same body on an UNREPRESENTED heap and IS ub: the no-fault result is earned by EncodesSimpPriority's two-cell premise, not assumed. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
