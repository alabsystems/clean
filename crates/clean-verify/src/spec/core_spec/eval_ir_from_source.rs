// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The THIRD complete width-one chain: `mode::CleanMode::from_source_system`.**
//!
//! One shipped kernel function carried the whole way from its real source to a
//! Clean-kernel-checked theorem, with every link a real mechanism: the emitted
//! trust-ir recorded verbatim, the proved module gated against that emission,
//! the codegen flip and its A-LIN lineage digest pinned, the semantics, the
//! refinement theorem, and the kernel check.
//!
//! ## Why this body, and what had to be BUILT to reach it
//!
//! The 2026-08-12 candidate measurement
//! (`data/crystal_width_candidates_2026-08-12.json`) ranked this body **2** —
//! the widest fully-flippable body in `clean-kernel` after `Level::kind_ord` —
//! and recorded it as **not chainable**, for one specific reason:
//!
//! > LINK 3. Every arm materializes `const enum.17 { k }` — a
//! > `trust_ir::Constant::Aggregate`. Clean's `IRConst` has SEVEN constructors
//! > (int_, bool_, unit_, null_, undef_, float_, func_) and no aggregate form,
//! > so `ir_const_eval` has no case for the construct this body emits. Closing
//! > it means extending `IRConst` + `ir_const_eval` (a build item), not
//! > asserting the link.
//!
//! That build item is now done, per the standing rule that a lowering gap is a
//! build item and never a reason to retarget the proof. `IRConst` gained the
//! inline element spine `aggv`/`vnil`/`vcons` — the `IRScalar` precedent, for
//! the same measured reason (a structural `IRList IRConst` field is a NESTED
//! inductive and the elaborator does not register one) — `ir_const_value`
//! became an explicit `IRConst.rec` so the spine is materialized recursively,
//! and `ir_const_eval` gained a real typed evaluator (`ir_const_agg_eval`) plus
//! fail-closed verdicts for the spine's junk inhabitants. See
//! `eval_ir_syntax.rs` and `eval_ir_ops.rs`.
//!
//! ### The aggregate shapes, MEASURED rather than guessed
//!
//! Whole-crate release differential of `clean-kernel` at this HEAD, stage1
//! trustc `5cd23255…`, `scripts/trust_ir_build.sh`'s profile. Both refused
//! candidates emit the SAME constant shape:
//!
//! ```text
//! mode::CleanMode::from_source_system     %3 = const enum.17  { 0 }
//! <tc::ExprPathStep as Clone>::clone      %4 = const enum.181 { 0 }
//! ```
//!
//! i.e. `Constant::Aggregate([Constant::Int(k)])` — **arity one, element kind
//! `Int`, nesting depth one**, no nested aggregate anywhere in either body.
//! The producer's convention (`trust-ir/src/interpret.rs:1712-1766`) is that an
//! enum-typed aggregate constant carries its discriminant at element 0 and the
//! selected variant's fields at `1..`, which is the same tag-at-slot-0
//! convention `ir_var` already builds for values — so `ir_const_value (ir_cvar
//! k)` is definitionally `ir_var k ir_sp0`, and a materialized enum constant is
//! the *same value* as a loaded enum.
//!
//! ## What this chain adds over the two that already exist
//!
//! | axis | `has_cubical_layer` | `kind_ord` | `from_source_system` |
//! |---|---|---|---|
//! | blocks | 5 | 7 | **14** |
//! | explicit switch cases | 2 | 4 | **11** |
//! | case list | contiguous | contiguous | **non-contiguous (0..9, then 11; tag 10 via the default)** |
//! | distinct answers | 2 (Bool) | 5 (u8) | **5 modes out of 12 tags — a many-to-one map** |
//! | argument | `&self`, loaded from the heap | `&self`, loaded from the heap | **BY VALUE — no load, no heap at all** |
//! | answer | `IRConst.bool_` | `IRConst.int_` | **`IRConst.aggv` — an aggregate constant** |
//! | join parameter | `bool` | `u8` | **`enum.17`, an aggregate** |
//!
//! The by-value argument is the structurally new thing and it changes the
//! representation premise: [`EncodesSourceSystemVal`] relates an `IRScalar` to a
//! `SourceSystemR` with **no memory argument** — the first A2 in this program
//! that mentions no heap, because the emitted body performs no load. It is also
//! payload-agnostic (the element spine is universally quantified), which is the
//! honest premise for a body that reads field 0 and nothing else.
//!
//! ## What this chain still does NOT add
//!
//! No recursion, no arithmetic, no comparison, no call, no panic arm. That is
//! not a choice made here: measured at this HEAD, none of the 153
//! codegen-flipped bodies in `clean-kernel` contains an `icmp`, arithmetic, a
//! cast, a `condbr`, a `gep` or a call, so the hard shape is unreachable
//! through the release flip set for *every* body. What that set's boundary is
//! CAUSED by is a separate question the `-C opt-level=0` measurement in
//! `docs/CRYSTAL_STATUS.md` speaks to; nothing in this module rests on either
//! answer.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_SOURCESYSTEMR: &str = "inductive SourceSystemR : Type\n| lean4 : SourceSystemR\n| coq : SourceSystemR\n| agda : SourceSystemR\n| cubicalagda : SourceSystemR\n| isabellehol : SourceSystemR\n| hollight : SourceSystemR\n| hol4 : SourceSystemR\n| mizar : SourceSystemR\n| metamathzfc : SourceSystemR\n| metamathset : SourceSystemR\n| pvs : SourceSystemR\n| acl2 : SourceSystemR";

const SRC_SOURCE_SYSTEM_TAG: &str = "def source_system_tag (s : SourceSystemR) : Nat := SourceSystemR.rec (fun (_ : SourceSystemR) => Nat) ir_d0 ir_d1 ir_d2 ir_d3 ir_d4 ir_d5 ir_d6 ir_d7 ir_d8 ir_d9 ir_d10 ir_d11 s";

const SRC_CLEAN_MODE_FROM_SOURCE: &str = "def clean_mode_from_source (s : SourceSystemR) : CleanModeR := SourceSystemR.rec (fun (_ : SourceSystemR) => CleanModeR) CleanModeR.constructive CleanModeR.impredicative CleanModeR.constructive CleanModeR.cubical CleanModeR.classical CleanModeR.classical CleanModeR.classical CleanModeR.settheoretic CleanModeR.settheoretic CleanModeR.classical CleanModeR.classical CleanModeR.classical s";

const SRC_CLEAN_MODE_OF_TAG: &str = "def clean_mode_of_tag (n : Nat) : CleanModeR := Bool.rec (fun (_ : Bool) => CleanModeR) (Bool.rec (fun (_ : Bool) => CleanModeR) (Bool.rec (fun (_ : Bool) => CleanModeR) (Bool.rec (fun (_ : Bool) => CleanModeR) (Bool.rec (fun (_ : Bool) => CleanModeR) CleanModeR.settheoretic CleanModeR.classical (ir_nat_eqb n ir_d4)) CleanModeR.directed (ir_nat_eqb n ir_d3)) CleanModeR.cubical (ir_nat_eqb n ir_d2)) CleanModeR.impredicative (ir_nat_eqb n ir_d1)) CleanModeR.constructive (ir_nat_eqb n ir_d0)";

const SRC_CLEAN_MODE_OF_TAG_TAG: &str = "def clean_mode_of_tag_tag (m : CleanModeR) : Eq CleanModeR (clean_mode_of_tag (clean_mode_tag m)) m := CleanModeR.rec (fun (m0 : CleanModeR) => Eq CleanModeR (clean_mode_of_tag (clean_mode_tag m0)) m0) (Eq.refl CleanModeR CleanModeR.constructive) (Eq.refl CleanModeR CleanModeR.impredicative) (Eq.refl CleanModeR CleanModeR.cubical) (Eq.refl CleanModeR CleanModeR.directed) (Eq.refl CleanModeR CleanModeR.classical) (Eq.refl CleanModeR CleanModeR.settheoretic) m";

const SRC_ENCODESSOURCESYSTEMVAL: &str = "inductive EncodesSourceSystemVal : IRScalar -> SourceSystemR -> Type\n| mk : forall (s : SourceSystemR) (fs : IRScalar), EncodesSourceSystemVal (ir_var (source_system_tag s) fs) s";

// ── the emitted module, MINTED ────────────────────────────────────────
/// The MINTED module script, generated from the emitted artifact by
/// `ir_mint_gen` over `generated/ir_fs.core.txt` + `generated/ir_fs.tags.json`
/// (crystal A2). `tests/crystal_a2_mint_fs.rs` fails closed if this committed
/// script is not what minting the committed core module produces.
///
/// The 2026-08-21 migration off the hand transcription found NO semantic
/// divergence — THIRTEEN divergent lines in TWO notation classes, printed
/// before adoption, both definitionally equal: `ir_fs_b0`'s extractfield type
/// inlines `(IRTy.uint_ ir_d8)` where the hand line named `ir_tU8`, and the
/// twelve arm constants spell the raw
/// `(IRConst.aggv (IRConst.vcons (IRConst.int_ ir_dN) IRConst.vnil))` spine
/// where the hand lines named `ir_cvar ir_dN` (`ir_cvar tag := IRConst.aggv
/// (ir_cs1 (IRConst.int_ tag))`). The other four lines (`ir_fs_tmode`,
/// `ir_fs_b13`, `ir_fs_func`, `ir_fs_module`) minted byte-identical, and ONE
/// line is minted-only: the `ir_fs_tsrc` interface alias (see its rationale).
const MINTED_IR_FS: &str = include_str!("generated/ir_fs.defs.txt");

/// Registration rationales, one per minted line, in script order.
const MINTED_IR_FS_DOCS: &[&str] = &[
    "ir_fs_tmode: enum.17, the CleanMode enum id the emitted body names in `const enum.17 { k }`. Unlike every earlier chain's type shorthand this one is SEMANTIC INPUT, not decoration: ir_const_agg_eval consults ir_ty_is_agg on it, so an aggregate constant at a scalar type is type_error not_agg. The particular id 13 is still not consulted. DerivedProved, zero axiom_deps.",
    "ir_fs_tsrc: enum.211 (fixture era), the SourceSystem enum the body takes BY VALUE -- INTERFACE-ONLY, named by NOTHING in the module: the argument's discriminant is read straight off the SSA value, so the type occurs only in the header the core module cannot hold. Registered so the tag table's canonical-1 pin (the one that makes the parameter-type row producer-invariant, `enum#1`) is an elaborated term and not only a JSON row. It has already moved once (laneREG 2026-08-21 dump: 176), which is why the pin is canonical rather than verbatim. DerivedProved, zero axiom_deps.",
    "ir_fs_b0: entry block, MINTED FROM THE EMITTED ARTIFACT (generated/ir_fs.core.txt; reader B's copy of the same body is tests/fixtures/from_source_system.trust-ir.txt). NO LOAD -- the argument arrives by value as %0, so the body reads its discriminant directly with extractfield u8 %0, 0. ELEVEN explicit switch cases and a NON-CONTIGUOUS case list: 0..9 map to bb1..bb10, then 11 maps to bb11, and tag 10 (PVS) is the value the DEFAULT edge carries. exhaustive_enum_unreachable is Bool.false and that is the MEASURED value read off the artifact binary by reader A, the flag's one witness: the default is reached on every PVS. DerivedProved, zero axiom_deps.",
    "ir_fs_b1: Lean4 => Constructive, materialized as the AGGREGATE CONSTANT `const enum.17 { 0 }` -- the construct that made this body unchainable until IRConst gained an aggregate form. DerivedProved, zero axiom_deps.",
    "ir_fs_b2: Coq => Impredicative. DerivedProved, zero axiom_deps.",
    "ir_fs_b3: Agda => Constructive. A SEPARATE block from Lean4's even though the answer is the same constant, as emitted -- the compiler does not share arms, and a module that did would be a different CFG. DerivedProved, zero axiom_deps.",
    "ir_fs_b4: CubicalAgda => Cubical. The one arm whose mode carries the cubical layer, and the arm the A5 witnesses instantiate. DerivedProved, zero axiom_deps.",
    "ir_fs_b5: IsabelleHOL => Classical. DerivedProved, zero axiom_deps.",
    "ir_fs_b6: HOLLight => Classical, in its OWN block. DerivedProved, zero axiom_deps.",
    "ir_fs_b7: HOL4 => Classical, in its OWN block. Three source-level or-patterns, three emitted blocks. DerivedProved, zero axiom_deps.",
    "ir_fs_b8: Mizar => SetTheoretic. DerivedProved, zero axiom_deps.",
    "ir_fs_b9: MetamathZFC => SetTheoretic. DerivedProved, zero axiom_deps.",
    "ir_fs_b10: MetamathSet => Classical. DerivedProved, zero axiom_deps.",
    "ir_fs_b11: ACL2 => Classical. Reached by the ONLY non-contiguous explicit case, selector 11 -- the arm a case table transcribed as 0..10 would silently misroute. DerivedProved, zero axiom_deps.",
    "ir_fs_b12: the DEFAULT edge => Classical, i.e. PVS (tag 10). The emitted body routes the TENTH tag through the default rather than the last one, so the default is neither a trap nor the tail of the enum -- it is one specific reachable variant in the middle of the range. DerivedProved, zero axiom_deps.",
    "ir_fs_b13: the JOIN block, taking an AGGREGATE block parameter (bb13(%1: enum.17)) and returning it. Not a Bool and not a u8: this is the first chain in the spec whose join carries a structured value, so the answer travels through the machine as an IRScalar.aggv rather than as a scalar. DerivedProved, zero axiom_deps.",
    "ir_fs_func: CleanMode::from_source_system as EvalIR -- one parameter (the SourceSystem, by value, SSA id 0), entry block 0, FOURTEEN blocks, matching the emitted body's control-flow graph exactly. DerivedProved, zero axiom_deps.",
    "ir_fs_module: the module for from_source_system, MINTED from the emitted trust-ir rather than transcribed from it. Reader A (the artifact binary), reader B (the emitted text, tests/fixtures/from_source_system.trust-ir.txt) and reader C (this elaborated term) agree on it -- modulo the one-entry unwitnessed ledger, the switch's unprinted exhaustive flag; see crate::ir_mint. DerivedProved, zero axiom_deps.",
];

/// The minted script's lines, in registration order — ONE source of truth for
/// [`Specification::add_eval_ir_from_source`] and anything that must run the
/// machine on *the registered module* rather than on a second transcription
/// (the GAP-2 encoding differential reads these same lines).
static MINTED_IR_FS_LINES: std::sync::LazyLock<Vec<&'static str>> =
    std::sync::LazyLock::new(|| {
        MINTED_IR_FS
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect()
    });

/// The minted `from_source_system` module definitions, in registration order.
///
/// Same contract as `ir_h2_module_defs`: shared by
/// [`Specification::add_eval_ir_from_source`] and the GAP-2 encoding
/// differential (`crate::ir_semdiff`). A FUNCTION over the minted script
/// rather than an array of hand-written constants as of 2026-08-21.
#[must_use]
pub fn ir_fs_module_defs() -> &'static [&'static str] {
    &MINTED_IR_FS_LINES
}

const SRC_IR_FS_ON_LEAN4: &str = "def ir_fs_on_lean4 : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d0 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d0 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d0 ir_sp0)))";
const SRC_IR_FS_ON_COQ: &str = "def ir_fs_on_coq : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d1 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d1 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d1 ir_sp0)))";
const SRC_IR_FS_ON_AGDA: &str = "def ir_fs_on_agda : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d2 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d0 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d0 ir_sp0)))";
const SRC_IR_FS_ON_CUBICALAGDA: &str = "def ir_fs_on_cubicalagda : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d3 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d2 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d2 ir_sp0)))";
const SRC_IR_FS_ON_ISABELLEHOL: &str = "def ir_fs_on_isabellehol : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d4 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))";
const SRC_IR_FS_ON_HOLLIGHT: &str = "def ir_fs_on_hollight : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d5 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))";
const SRC_IR_FS_ON_HOL4: &str = "def ir_fs_on_hol4 : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d6 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))";
const SRC_IR_FS_ON_MIZAR: &str = "def ir_fs_on_mizar : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d7 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d5 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d5 ir_sp0)))";
const SRC_IR_FS_ON_METAMATHZFC: &str = "def ir_fs_on_metamathzfc : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d8 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d5 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d5 ir_sp0)))";
const SRC_IR_FS_ON_METAMATHSET: &str = "def ir_fs_on_metamathset : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d9 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))";
const SRC_IR_FS_ON_ACL2: &str = "def ir_fs_on_acl2 : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d11 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))";
const SRC_IR_FS_ON_PVS_DEFAULT: &str = "def ir_fs_on_pvs_default : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d10 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))";
const SRC_IR_FS_ON_PAYLOAD_JUNK: &str = "def ir_fs_on_payload_junk : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d10 (ir_sp2 IRScalar.undef_ IRScalar.vnil))) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))";

// ── the refinement theorem and its A5 ──────────────────────────────────────
const SRC_IR_FS_MACH0: &str = "def ir_fs_mach0 (v : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 v) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";

const SRC_IR_FS_EXACT: &str = "def ir_fs_exact (mem : IRList IRMemSlot) (na : Nat) (fs : IRScalar) (s : SourceSystemR) : Eq IROutcome (ir_run ir_d5 ir_fs_module (IRConfig.running (ir_fs_mach0 (ir_var (source_system_tag s) fs) mem na))) (IROutcome.ret (ir_vl1 (ir_var (clean_mode_tag (clean_mode_from_source s)) ir_sp0))) := SourceSystemR.rec (fun (s0 : SourceSystemR) => Eq IROutcome (ir_run ir_d5 ir_fs_module (IRConfig.running (ir_fs_mach0 (ir_var (source_system_tag s0) fs) mem na))) (IROutcome.ret (ir_vl1 (ir_var (clean_mode_tag (clean_mode_from_source s0)) ir_sp0)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d0 ir_sp0)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d1 ir_sp0)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d0 ir_sp0)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d2 ir_sp0)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d5 ir_sp0)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d5 ir_sp0)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0)))) s";

const SRC_IR_FS_CORRECT: &str = "def ir_fs_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (s : SourceSystemR) (henc : EncodesSourceSystemVal r s) : Le ir_d5 fuel -> Eq IROutcome (ir_eval fuel ir_fs_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var (clean_mode_tag (clean_mode_from_source s)) ir_sp0))) := EncodesSourceSystemVal.rec (fun (r0 : IRScalar) (s0 : SourceSystemR) (_ : EncodesSourceSystemVal r0 s0) => Le ir_d5 fuel -> Eq IROutcome (ir_eval fuel ir_fs_module ir_d0 (ir_vl1 r0) mem na) (IROutcome.ret (ir_vl1 (ir_var (clean_mode_tag (clean_mode_from_source s0)) ir_sp0)))) (fun (s0 : SourceSystemR) (fs : IRScalar) (hle : Le ir_d5 fuel) => ir_run_le_ret ir_fs_module ir_d5 fuel hle (IRConfig.running (ir_fs_mach0 (ir_var (source_system_tag s0) fs) mem na)) (ir_vl1 (ir_var (clean_mode_tag (clean_mode_from_source s0)) ir_sp0)) (ir_fs_exact mem na fs s0)) r s henc";

const SRC_IR_SPINE_HEAD_NAT: &str = "def ir_spine_head_nat (sp : IRScalar) : Nat := IRScalar.rec (fun (_ : IRScalar) => Nat) Nat.zero (fun (_ : Bool) => Nat.zero) (fun (_ : Nat) => Nat.zero) (fun (_ : Nat) => Nat.zero) Nat.zero (fun (_ : Nat) => Nat.zero) Nat.zero (fun (_ : Nat) (_ : Nat) => Nat.zero) (fun (_ : Nat) => Nat.zero) (fun (_ : IRScalar) (_ : Nat) => Nat.zero) Nat.zero (fun (x : IRScalar) (_ : IRScalar) (_ : Nat) (_ : Nat) => ir_scalar_nat x) sp";

const SRC_IR_AGG_DISC: &str = "def ir_agg_disc (v : IRScalar) : Nat := IRScalar.rec (fun (_ : IRScalar) => Nat) Nat.zero (fun (_ : Bool) => Nat.zero) (fun (_ : Nat) => Nat.zero) (fun (_ : Nat) => Nat.zero) Nat.zero (fun (_ : Nat) => Nat.zero) Nat.zero (fun (_ : Nat) (_ : Nat) => Nat.zero) (fun (_ : Nat) => Nat.zero) (fun (sp : IRScalar) (_ : Nat) => ir_spine_head_nat sp) Nat.zero (fun (_ : IRScalar) (_ : IRScalar) (_ : Nat) (_ : Nat) => Nat.zero) v";

const SRC_IR_VALS_HEAD_DISC: &str = "def ir_vals_head_disc (v : IRList IRScalar) : Nat := IRList.rec IRScalar (fun (_ : IRList IRScalar) => Nat) Nat.zero (fun (x : IRScalar) (_ : IRList IRScalar) (_ : Nat) => ir_agg_disc x) v";

const SRC_IR_OUTCOME_DISC: &str = "def ir_outcome_disc (o : IROutcome) : Nat := IROutcome.rec (fun (_ : IROutcome) => Nat) (fun (v : IRList IRScalar) => ir_vals_head_disc v) (fun (_ : IRFault) => Nat.zero) (fun (_ : IRFault) => Nat.zero) (fun (_ : IRFault) => Nat.zero) (fun (_ : IRFault) => Nat.zero) Nat.zero o";

const SRC_IR_FS_MACHINE_SOUND: &str = "def ir_fs_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (s : SourceSystemR) (t : Nat) (henc : EncodesSourceSystemVal r s) (hle : Le ir_d5 fuel) (hret : Eq IROutcome (ir_eval fuel ir_fs_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var t ir_sp0)))) : Eq Nat (clean_mode_tag (clean_mode_from_source s)) t := Eq.cong IROutcome Nat ir_outcome_disc (IROutcome.ret (ir_vl1 (ir_var (clean_mode_tag (clean_mode_from_source s)) ir_sp0))) (IROutcome.ret (ir_vl1 (ir_var t ir_sp0))) (Eq.trans IROutcome (IROutcome.ret (ir_vl1 (ir_var (clean_mode_tag (clean_mode_from_source s)) ir_sp0))) (ir_eval fuel ir_fs_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var t ir_sp0))) (Eq.symm IROutcome (ir_eval fuel ir_fs_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var (clean_mode_tag (clean_mode_from_source s)) ir_sp0))) (ir_fs_correct mem fuel na r s henc hle)) hret)";

const SRC_IR_FS_MACHINE_SOUND_MODE: &str = "def ir_fs_machine_sound_mode (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (s : SourceSystemR) (t : Nat) (henc : EncodesSourceSystemVal r s) (hle : Le ir_d5 fuel) (hret : Eq IROutcome (ir_eval fuel ir_fs_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var t ir_sp0)))) : Eq CleanModeR (clean_mode_of_tag t) (clean_mode_from_source s) := Eq.trans CleanModeR (clean_mode_of_tag t) (clean_mode_of_tag (clean_mode_tag (clean_mode_from_source s))) (clean_mode_from_source s) (Eq.symm CleanModeR (clean_mode_of_tag (clean_mode_tag (clean_mode_from_source s))) (clean_mode_of_tag t) (Eq.cong Nat CleanModeR clean_mode_of_tag (clean_mode_tag (clean_mode_from_source s)) t (ir_fs_machine_sound mem fuel na r s t henc hle hret))) (clean_mode_of_tag_tag (clean_mode_from_source s))";

const SRC_IR_FS_MACHINE_SOUND_CUBICAL: &str = "def ir_fs_machine_sound_cubical (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (s : SourceSystemR) (t : Nat) (henc : EncodesSourceSystemVal r s) (hle : Le ir_d5 fuel) (hret : Eq IROutcome (ir_eval fuel ir_fs_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var t ir_sp0)))) : Eq Bool (clean_mode_has_cubical (clean_mode_of_tag t)) (clean_mode_has_cubical (clean_mode_from_source s)) := Eq.cong CleanModeR Bool clean_mode_has_cubical (clean_mode_of_tag t) (clean_mode_from_source s) (ir_fs_machine_sound_mode mem fuel na r s t henc hle hret)";

const SRC_IR_FS_NEVER_FAULTS: &str = "def ir_fs_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (s : SourceSystemR) (henc : EncodesSourceSystemVal r s) (hle : Le ir_d5 fuel) : Eq Bool (ir_outcome_is_ret (ir_eval fuel ir_fs_module ir_d0 (ir_vl1 r) mem na)) Bool.true := Eq.cong IROutcome Bool ir_outcome_is_ret (ir_eval fuel ir_fs_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (ir_var (clean_mode_tag (clean_mode_from_source s)) ir_sp0))) (ir_fs_correct mem fuel na r s henc hle)";

const SRC_IR_FS_CORRECT_WITNESS: &str = "def ir_fs_correct_witness : Eq IROutcome (ir_eval ir_d5 ir_fs_module ir_d0 (ir_vl1 (ir_var ir_d3 ir_sp0)) ir_mem0 ir_d0) (IROutcome.ret (ir_vl1 (ir_var (clean_mode_tag (clean_mode_from_source SourceSystemR.cubicalagda)) ir_sp0))) := ir_fs_correct ir_mem0 ir_d5 ir_d0 (ir_var ir_d3 ir_sp0) SourceSystemR.cubicalagda (EncodesSourceSystemVal.mk SourceSystemR.cubicalagda ir_sp0) (Le.refl ir_d5)";

const SRC_IR_FS_MACHINE_SOUND_WITNESS: &str = "def ir_fs_machine_sound_witness : Eq Nat (clean_mode_tag (clean_mode_from_source SourceSystemR.cubicalagda)) ir_d2 := ir_fs_machine_sound ir_mem0 ir_d5 ir_d0 (ir_var ir_d3 ir_sp0) SourceSystemR.cubicalagda ir_d2 (EncodesSourceSystemVal.mk SourceSystemR.cubicalagda ir_sp0) (Le.refl ir_d5) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d2 ir_sp0))))";

const SRC_IR_FS_MACHINE_SOUND_MODE_WITNESS: &str = "def ir_fs_machine_sound_mode_witness : Eq CleanModeR (clean_mode_of_tag ir_d2) (clean_mode_from_source SourceSystemR.cubicalagda) := ir_fs_machine_sound_mode ir_mem0 ir_d5 ir_d0 (ir_var ir_d3 ir_sp0) SourceSystemR.cubicalagda ir_d2 (EncodesSourceSystemVal.mk SourceSystemR.cubicalagda ir_sp0) (Le.refl ir_d5) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d2 ir_sp0))))";

const SRC_IR_FS_MACHINE_SOUND_CUBICAL_WITNESS: &str = "def ir_fs_machine_sound_cubical_witness : Eq Bool (clean_mode_has_cubical (clean_mode_of_tag ir_d2)) (clean_mode_has_cubical (clean_mode_from_source SourceSystemR.cubicalagda)) := ir_fs_machine_sound_cubical ir_mem0 ir_d5 ir_d0 (ir_var ir_d3 ir_sp0) SourceSystemR.cubicalagda ir_d2 (EncodesSourceSystemVal.mk SourceSystemR.cubicalagda ir_sp0) (Le.refl ir_d5) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d2 ir_sp0))))";

const SRC_IR_FS_MACHINE_SOUND_JUNK_WITNESS: &str = "def ir_fs_machine_sound_junk_witness : Eq Nat (clean_mode_tag (clean_mode_from_source SourceSystemR.pvs)) ir_d4 := ir_fs_machine_sound ir_mem0 ir_d5 ir_d0 (ir_var ir_d10 (ir_sp2 IRScalar.undef_ IRScalar.vnil)) SourceSystemR.pvs ir_d4 (EncodesSourceSystemVal.mk SourceSystemR.pvs (ir_sp2 IRScalar.undef_ IRScalar.vnil)) (Le.refl ir_d5) (Eq.refl IROutcome (IROutcome.ret (ir_vl1 (ir_var ir_d4 ir_sp0))))";

impl Specification {
    /// Register the THIRD complete width-one chain:
    /// `mode::CleanMode::from_source_system`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_from_source(&mut self) -> Result<(), SpecError> {
        self.add_inductive(SRC_SOURCESYSTEMR, "SourceSystemR: the reflected SourceSystem (mode.rs:336-361). TWELVE fieldless variants in declaration order, so a value IS its discriminant -- which is why the compiler emits a plain discriminant switch for from_source_system and why this body is in the class the flip gate accepts. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_SOURCE_SYSTEM_TAG, "source_system_tag: each variant's discriminant, 0..11 in declaration order. The ONE place the reflected argument type meets the emitted layout, and the reason the emitted switch's explicit case list is 0..9 plus 11: tag 10 (PVS) is the value routed through the default edge. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_CLEAN_MODE_FROM_SOURCE, "clean_mode_from_source: the reflected CleanMode::from_source_system (mode.rs:184-196). NOT a predicate and not an injection: twelve source systems map onto FIVE of the six modes, many-to-one -- Lean4/Agda share Constructive, the three HOL systems plus MetamathSet, PVS and ACL2 share Classical, Mizar and MetamathZFC share SetTheoretic. The equality theorem below therefore cannot be discharged by any case split smaller than the full twelve. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_CLEAN_MODE_OF_TAG, "clean_mode_of_tag: a total left inverse of clean_mode_tag on 0..5, by a chain of decidable Nat equalities. Total means it must answer somewhere off the tag range: every n >= 5 answers settheoretic, which is correct AT 5 and arbitrary above it. That arbitrariness is harmless and is stated rather than hidden -- clean_mode_of_tag_tag only ever applies it to a real tag, and the A5 that uses it obtains its argument from clean_mode_tag. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_CLEAN_MODE_OF_TAG_TAG, "clean_mode_of_tag_tag: clean_mode_of_tag inverts clean_mode_tag on every CleanModeR, by CleanModeR.rec with six Eq.refl arms -- the kernel computes each tag and re-selects the mode. This is what upgrades the A5 below from a statement about a NUMBER to a statement about a MODE. DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODESSOURCESYSTEMVAL, "EncodesSourceSystemVal v s: the IRScalar v is the BY-VALUE representation of source system s. \n\nNo memory argument, and that is the structurally new thing about this chain: the emitted body takes its argument by value (`bb0(%0: enum.211)`) and performs NO load, so there is no heap for a representation premise to constrain. The two earlier chains both had to pin a live cell with an ir_mem_lookup equation because their argument was a reference; this one has nothing to pin, and saying so is the honest premise rather than a weaker one. \n\nPayload-agnostic on purpose: the element spine fs is universally quantified, because the body reads field 0 and nothing else -- measured, in the emitted body: one extractfield at index 0, then a switch. SourceSystem is fieldless so a real value's spine is ir_sp0, but quantifying makes the theorem hold for every spine and makes the 'reads only the tag' claim checked rather than asserted. \n\nSAME OPEN LAYOUT OBLIGATION as eval_ir_repr's, carried forward rather than laundered: these are trust-ir DECLARATION-INDEX tags, which is what the emitted body switches on; the Rust enum is niche-encoded downstream of trust-ir. DerivedProved, zero axiom_deps.")?;
        // The module is REPLAYED from the minted script, line for line — the
        // eval_ir_mode.rs / eval_ir_priority.rs posture: Clean's parser and
        // elaborator still turn the text into the term the theorems are about.
        let minted = ir_fs_module_defs();
        if minted.len() != MINTED_IR_FS_DOCS.len() {
            return Err(SpecError::EnvError(format!(
                "the minted ir_fs script has {} definitions but {} rationales are declared; \
                 regenerate the docs table with the script rather than reusing it",
                minted.len(),
                MINTED_IR_FS_DOCS.len()
            )));
        }
        for (line, doc) in minted.iter().zip(MINTED_IR_FS_DOCS) {
            self.add_recursive_def(line, doc)?;
        }
        self.add_recursive_def(SRC_IR_FS_ON_LEAN4, "GATE WITNESS: Lean4, explicit switch case 0. Eq.refl -- the kernel runs the machine for 5 steps (2 in the entry block, 2 in an arm, 1 in the join) and compares. The answer is an AGGREGATE value, so this is also the first executed proof that ir_const_agg_eval materializes one and that the join block carries it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_IR_FS_ON_COQ,
            "GATE WITNESS: Coq, explicit case 1 => Impredicative. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_IR_FS_ON_AGDA, "GATE WITNESS: Agda, explicit case 2 => Constructive. Same ANSWER as Lean4 through a DIFFERENT block, which is what makes the many-to-one map real in the artifact. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_ON_CUBICALAGDA, "GATE WITNESS: CubicalAgda, explicit case 3 => Cubical. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_ON_ISABELLEHOL, "GATE WITNESS: IsabelleHOL, explicit case 4 => Classical. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(
            SRC_IR_FS_ON_HOLLIGHT,
            "GATE WITNESS: HOLLight, explicit case 5 => Classical. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_IR_FS_ON_HOL4,
            "GATE WITNESS: HOL4, explicit case 6 => Classical. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_IR_FS_ON_MIZAR,
            "GATE WITNESS: Mizar, explicit case 7 => SetTheoretic. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(SRC_IR_FS_ON_METAMATHZFC, "GATE WITNESS: MetamathZFC, explicit case 8 => SetTheoretic. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_ON_METAMATHSET, "GATE WITNESS: MetamathSet, explicit case 9 => Classical. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_ON_ACL2, "GATE WITNESS: ACL2, the NON-CONTIGUOUS explicit case 11 => Classical. A transcription that renumbered the case list would route this tag to the default and still answer Classical by accident; it is here because the ARM matters, and the CFG gate checks the case map separately. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_ON_PVS_DEFAULT, "GATE WITNESS: PVS, tag 10, reached through the DEFAULT EDGE => Classical. All TWELVE emitted arms are executed by these witnesses -- eleven explicit cases and the default. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_ON_PAYLOAD_JUNK, "GATE WITNESS: the body never reads past field 0. Same tag 10 as the previous witness, but the argument carries a two-element payload spine whose first element is IRScalar.undef_ -- a value the semantics treats as unreadable. The machine still answers Classical, which is the executable proof behind EncodesSourceSystemVal's universally quantified spine. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_MACH0, "ir_fs_mach0: the machine ir_init produces for this module -- definitionally equal to it, since the module declares no globals so ir_mem_concat is the identity on the caller heap. Takes the argument VALUE rather than an address, because this body's parameter is passed by value. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_EXACT, "ir_fs_exact: the machine agrees with the reflected from_source_system at EXACTLY 5 steps, for every SourceSystem constructor, every payload spine and every heap. SourceSystemR.rec with twelve Eq.refl arms -- and no Eq.subst anywhere, which is the by-value argument paying off: the two earlier chains had to rewrite a heap lookup into the goal before the machine could compute, and this one has no lookup to rewrite. mem, na and the spine fs stay free variables throughout. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_CORRECT, "ir_fs_correct: *** THE EQUALITY THEOREM, OVER THE EMITTED SHAPE. *** For every SourceSystem, every IRScalar representing it, every heap and every fuel at or above 5, ir_eval on ir_fs_module returns exactly the aggregate value whose tag is clean_mode_tag (clean_mode_from_source s). The conclusion is a STRUCTURED value, not a scalar: this is the first chain whose theorem's right-hand side is an IRScalar.aggv. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_SPINE_HEAD_NAT, "ir_spine_head_nat: element 0 of an inline payload spine, as a Nat. Every non-spine value is zero -- a total projection, used only to OBSERVE an equality that is already proved, never to decide anything. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_AGG_DISC, "ir_agg_disc: the discriminant of an aggregate value, i.e. ir_spine_head_nat of its spine. The aggregate-valued counterpart of ir_scalar_nat, needed because this chain's answer is an enum value rather than an integer. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_VALS_HEAD_DISC, "ir_vals_head_disc: the tag of the first returned value. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_OUTCOME_DISC, "ir_outcome_disc: the tag carried by a ret outcome; every fault and fuel_out is zero. The projection Eq.cong applies to invert the equality theorem. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_MACHINE_SOUND, "ir_fs_machine_sound: *** A5 FOR THIS CHAIN, THE INVERSION. *** If the MACHINE returns an aggregate whose tag is t, then t really is the tag of the mode the reflected function assigns that source system. Quantified over every heap, every representing value, every fuel at or above 5. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_MACHINE_SOUND_MODE, "ir_fs_machine_sound_mode: *** A5, LIFTED OFF THE TAG. *** The same hypothesis, but the conclusion is an equation between MODES -- clean_mode_of_tag t IS clean_mode_from_source s -- obtained by composing the tag inversion with clean_mode_of_tag_tag. This matters because a tag is a layout fact and a mode is a semantic object; without this step the A5 would only ever conclude something about a number the compiler chose. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_MACHINE_SOUND_CUBICAL, "ir_fs_machine_sound_cubical: *** A5 REACHING A SEMANTIC PREDICATE. *** From the machine's raw aggregate answer alone, the cubical-layer question about the imported system's default mode is decided: clean_mode_has_cubical (clean_mode_of_tag t) equals clean_mode_has_cubical (clean_mode_from_source s). The predicate is the FIRST chain's reflected function (add_eval_ir_mode), so this is a composition ACROSS two chains about two different shipped kernel functions -- the analogue of ir_ko_machine_sound_denot reaching level_eval. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_NEVER_FAULTS, "ir_fs_never_faults: *** NO UB, NO PANIC, NO EXHAUSTION -- on any represented source system. *** IROutcome separates success from ub, type_error, unmodelled, stuck and fuel_out, so proving the outcome is a ret rules out all five at once. Here it also rules out the two NEW fail-closed verdicts the aggregate extension introduced: an aggregate constant at a scalar type, and a bare element-spine node, both type_error not_agg. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_CORRECT_WITNESS, "ir_fs_correct_witness: A4 is not vacuous, and the witness RUNS THE MACHINE at CubicalAgda -- every premise discharged concretely, the representation by EncodesSourceSystemVal.mk with the fieldless spine. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_MACHINE_SOUND_WITNESS, "ir_fs_machine_sound_witness: A5 is not vacuous. The observation is Eq.refl, which the kernel discharges by executing the body and finding the aggregate answer with tag 2. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_MACHINE_SOUND_MODE_WITNESS, "ir_fs_machine_sound_mode_witness: the mode-level A5 is not vacuous -- CubicalAgda's machine answer really does invert to CleanModeR.cubical. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_MACHINE_SOUND_CUBICAL_WITNESS, "ir_fs_machine_sound_cubical_witness: the cross-chain composition is not vacuous. Both sides reduce to Bool.true, so the machine's aggregate answer for CubicalAgda decides the cubical-layer question affirmatively. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IR_FS_MACHINE_SOUND_JUNK_WITNESS, "ir_fs_machine_sound_junk_witness: A5 instantiated on the DEFAULT edge (PVS, tag 10) with a junk payload spine -- the two hardest instances at once. DerivedProved, zero axiom_deps.")?;

        Ok(())
    }
}

/// Millisecond unit tests on the generated sources.
///
/// The full spec build costs tens of minutes, and the two commonest ways a
/// declaration in this file can be wrong — a parse error and a transcription
/// that drifts off the emitted CFG — are both decidable without it. The CFG
/// gate in `tests/crystal_a1_lineage/from_source_system.rs` is the authority on
/// the second; these are the fast pre-flight.
// The acceptance tests moved to `eval_ir_from_source_tests.rs` on 2026-08-21
// (the `eval_ir_float_div_tests.rs` precedent): the A2 mint migration put this
// file at the 500-line convention that `data/paragon_ratchet.json`'s
// `files_over_500` enforces shrink-only.
#[cfg(test)]
#[path = "eval_ir_from_source_tests.rs"]
mod tests;
