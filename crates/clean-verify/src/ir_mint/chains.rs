// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The committed A2 chain artifacts, one constant block per chain.
//!
//! Read `super` (src/ir_mint/mod.rs) first: it owns the three-reader design
//! and the normalization story these constants exist for. Each chain carries
//! four artifacts — the reader-A core module, the minted definition script the
//! spec REPLAYS, the mint record (provenance + digests + the unwitnessed
//! ledger), and the tag table (the crate-level build facts and the interface
//! pin, kept OUT of the module's identity).

/// The committed core module of the width-one chain, produced by reader A.
pub const IR_H2_CORE: &str = include_str!("../spec/core_spec/generated/ir_h2.core.txt");
/// The committed minted definition script of the width-one chain.
pub const IR_H2_DEFS: &str = include_str!("../spec/core_spec/generated/ir_h2.defs.txt");
/// The committed mint record: provenance, digests and the unwitnessed ledger.
pub const IR_H2_RECORD: &str = include_str!("../spec/core_spec/generated/ir_h2.mint.json");
/// The committed tag table of the width-one chain: canonical first-use index →
/// the crate-level interning id the artifact names.
pub const IR_H2_TAGS: &str = include_str!("../spec/core_spec/generated/ir_h2.tags.json");
/// The committed core module of the EIGHTEENTH chain and the FIRST COMPLETE
/// ONE (A0 6-of-6, A6 4-of-4): `expr::meta::ExprMeta::has_loose_bvars`
/// CALLING `expr::meta::ExprMeta::loose_bvar_range`.
///
/// **The only committed core module with TWO functions.** Reader A projected
/// both bodies in one pass (`a2project … --with …`) under ONE interning
/// namespace, so `(call 1 …)` in the caller and `(func 1 …)` for the callee are
/// the same numeral by construction. It is what separates this chain from
/// [`IR_LZ_CORE`], whose `funcs` lane also has two rows: there the second
/// function is CALLED and not DEFINED, so `ir_call_exec` goes `stuck no_func`;
/// here it is defined and the call resolves.
pub const IR_HLB_CORE: &str = include_str!("../spec/core_spec/generated/ir_hlb.core.txt");
/// The committed minted definition script of the call chain — six lines
/// defining two functions, replayed verbatim by `eval_ir_has_loose_bvars.rs`.
pub const IR_HLB_DEFS: &str = include_str!("../spec/core_spec/generated/ir_hlb.defs.txt");
/// The committed mint record of the call chain — TWO reader-A dumps, and the
/// record says two rather than the eleven original rows' three, because this
/// chain postdates the producer A/B record: laneREG `wc-REG/dump_O3`
/// (2026-08-21, the projection it was minted from) and laneF8 `wc-ctl/dump_O3`
/// (2026-08-23, an independent reproduction that projects the SAME core module
/// byte for byte with all four crate-level indices moved). Plus the 2026-08-23
/// migration verdict: four of six lines byte-identical, two differing in three
/// definitionally-equal notation classes, NO semantic divergence.
pub const IR_HLB_RECORD: &str = include_str!("../spec/core_spec/generated/ir_hlb.mint.json");
/// The committed tag table of the call chain. Two firsts: the `extra_bodies`
/// lane, which names the SECOND body of the module, its Clean name prefix and
/// its own interface; and a `funcs` lane whose two rows are both DEFINED
/// functions rather than one body and one foreign callee.
pub const IR_HLB_TAGS: &str = include_str!("../spec/core_spec/generated/ir_hlb.tags.json");
/// The committed core module of the ELEVENTH chain,
/// `env::types::SimpPriority::value` — the first chained body that computes an
/// address with a `gep` and loads through the result.
pub const IR_PV_CORE: &str = include_str!("../spec/core_spec/generated/ir_pv.core.txt");
/// The committed minted definition script of the `gep` chain.
pub const IR_PV_DEFS: &str = include_str!("../spec/core_spec/generated/ir_pv.defs.txt");
/// The committed mint record of the `gep` chain.
pub const IR_PV_RECORD: &str = include_str!("../spec/core_spec/generated/ir_pv.mint.json");
/// The committed tag table of the `gep` chain. Its one enum is interned at
/// **127**, outside the `ir_d0..ir_d16` atom pool, which is why
/// `mint::interning_id` exists.
pub const IR_PV_TAGS: &str = include_str!("../spec/core_spec/generated/ir_pv.tags.json");
/// The committed core module of the `FlatFlags::contains` chain — projected
/// 2026-08-21 by reader A from the laneREG dump; its digest equals all three
/// producer A/B columns. The ninth chain in the mint, and the first whose
/// interface pins a BY-VALUE STRUCT (twice — both parameters are the same
/// canonical struct, and that sameness is the row's semantic payload).
pub const IR_FC_CORE: &str = include_str!("../spec/core_spec/generated/ir_fc.core.txt");
/// The committed minted definition script of the `contains` chain.
pub const IR_FC_DEFS: &str = include_str!("../spec/core_spec/generated/ir_fc.defs.txt");
/// The committed mint record of the `contains` chain.
pub const IR_FC_RECORD: &str = include_str!("../spec/core_spec/generated/ir_fc.mint.json");
/// The committed tag table of the `contains` chain. One INTERFACE-ONLY struct
/// row (FlatFlags, crate id 1017): the module's instructions name no aggregate
/// at all, so the struct occurs only in the header the core module cannot
/// hold — the struct sibling of `ir_fs_tsrc`.
pub const IR_FC_TAGS: &str = include_str!("../spec/core_spec/generated/ir_fc.tags.json");
/// The committed core module of the `FlatFlags::with` chain — projected
/// 2026-08-21 by reader A from the laneREG dump. The tenth chain in the mint,
/// the first whose STRUCT the module itself names (its const and insertfield),
/// and the first minted chain that is NOT in the producer A/B record — its
/// mint record states one dump, not three.
pub const IR_FW_CORE: &str = include_str!("../spec/core_spec/generated/ir_fw.core.txt");
/// The committed minted definition script of the `with` chain.
pub const IR_FW_DEFS: &str = include_str!("../spec/core_spec/generated/ir_fw.defs.txt");
/// The committed mint record of the `with` chain.
pub const IR_FW_RECORD: &str = include_str!("../spec/core_spec/generated/ir_fw.mint.json");
/// The committed tag table of the `with` chain: one REAL struct row
/// (FlatFlags, crate id 1017 at canonical 0 — the same crate entry its
/// sibling `contains` pins interface-only).
pub const IR_FW_TAGS: &str = include_str!("../spec/core_spec/generated/ir_fw.tags.json");
/// The committed core module of the THIRD complete chain,
/// `mode::CleanMode::from_source_system` — projected 2026-08-21 by reader A
/// from the laneREG dump; its digest equals all three producer A/B columns.
/// The eighth chain in the mint, the first whose argument is a BY-VALUE enum
/// and the first whose arms are AGGREGATE constants.
pub const IR_FS_CORE: &str = include_str!("../spec/core_spec/generated/ir_fs.core.txt");
/// The committed minted definition script of the `from_source_system` chain.
pub const IR_FS_DEFS: &str = include_str!("../spec/core_spec/generated/ir_fs.defs.txt");
/// The committed mint record of the `from_source_system` chain.
pub const IR_FS_RECORD: &str = include_str!("../spec/core_spec/generated/ir_fs.mint.json");
/// The committed tag table of the `from_source_system` chain. Two enums: the
/// RESULT (`CleanMode`, crate id 13, canonical 0 — the only aggregate the core
/// module names) and, NEW IN KIND, the INTERFACE-ONLY SourceSystem row
/// (fixture-era 178 at canonical 1), which exists so the by-value argument's
/// type pin is the producer-invariant `enum#1` rather than `enum#?`.
pub const IR_FS_TAGS: &str = include_str!("../spec/core_spec/generated/ir_fs.tags.json");
/// The committed core module of the SECOND complete chain,
/// `level::Level::kind_ord` — committed by the gate's first landing (its
/// producer A/B row is one of the original eleven) and MINTED on 2026-08-21.
/// The seventh chain in the mint, and the second whose unwitnessed ledger is
/// non-empty: the body dispatches, so the switch's unprinted exhaustive flag
/// occurs exactly once.
pub const IR_KO_CORE: &str = include_str!("../spec/core_spec/generated/ir_ko.core.txt");
/// The committed minted definition script of the `kind_ord` chain.
pub const IR_KO_DEFS: &str = include_str!("../spec/core_spec/generated/ir_ko.defs.txt");
/// The committed mint record of the `kind_ord` chain.
pub const IR_KO_RECORD: &str = include_str!("../spec/core_spec/generated/ir_ko.mint.json");
/// The committed tag table of the `kind_ord` chain. Its one enum — `Level`,
/// crate id 2 on all four recorded dumps — sits INSIDE the `ir_d0..ir_d16`
/// atom pool, so the minted alias spells it `ir_d2` where `ir_pv_tprio`
/// spells its 127 as a literal: `mint::interning_id`'s other arm.
pub const IR_KO_TAGS: &str = include_str!("../spec/core_spec/generated/ir_ko.tags.json");
/// The committed core module of the TWELFTH chain,
/// `env::native_reducers_float::reduce_float_add::{closure#0}` — the first
/// minted chain whose unwitnessed ledger is EMPTY: the body carries no
/// `switch`, so the emitted text fully determines the core module.
pub const IR_FA_CORE: &str = include_str!("../spec/core_spec/generated/ir_fa.core.txt");
/// The committed minted definition script of the `fadd` chain.
pub const IR_FA_DEFS: &str = include_str!("../spec/core_spec/generated/ir_fa.defs.txt");
/// The committed mint record of the `fadd` chain.
pub const IR_FA_RECORD: &str = include_str!("../spec/core_spec/generated/ir_fa.mint.json");
/// The committed tag table of the `fadd` chain. Every aggregate lane is
/// measured EMPTY — `f64` is a machine type, not a crate table entry — so the
/// table's load-bearing half is the interface: the `f64` parameter rows are
/// what separate this body from an `f32` twin the core module cannot see.
pub const IR_FA_TAGS: &str = include_str!("../spec/core_spec/generated/ir_fa.tags.json");
/// The committed core module of the THIRTEENTH chain,
/// `env::native_reducers_float::reduce_float_sub::{closure#0}` — `ir_fa`'s
/// shape with the one non-commutative operator of the tranche.
pub const IR_FS2_CORE: &str = include_str!("../spec/core_spec/generated/ir_fs2.core.txt");
/// The committed minted definition script of the `fsub` chain.
pub const IR_FS2_DEFS: &str = include_str!("../spec/core_spec/generated/ir_fs2.defs.txt");
/// The committed mint record of the `fsub` chain.
pub const IR_FS2_RECORD: &str = include_str!("../spec/core_spec/generated/ir_fs2.mint.json");
/// The committed tag table of the `fsub` chain — empty aggregate lanes, the
/// interface as the load-bearing half, exactly as `ir_fa`'s.
pub const IR_FS2_TAGS: &str = include_str!("../spec/core_spec/generated/ir_fs2.tags.json");
/// The committed core module of the FOURTEENTH chain,
/// `env::native_reducers_float::reduce_float_mul::{closure#0}` — the last of
/// the float tranche, closing the migration of chains 12–14 to the mint.
pub const IR_FM_CORE: &str = include_str!("../spec/core_spec/generated/ir_fm.core.txt");
/// The committed minted definition script of the `fmul` chain.
pub const IR_FM_DEFS: &str = include_str!("../spec/core_spec/generated/ir_fm.defs.txt");
/// The committed mint record of the `fmul` chain.
pub const IR_FM_RECORD: &str = include_str!("../spec/core_spec/generated/ir_fm.mint.json");
/// The committed tag table of the `fmul` chain — empty aggregate lanes, the
/// interface as the load-bearing half, exactly as its two siblings'.
pub const IR_FM_TAGS: &str = include_str!("../spec/core_spec/generated/ir_fm.tags.json");
/// The committed core module of the EIGHTH chain,
/// `env::native_reducers_float::reduce_float_div::{closure#0}` — minted with
/// the 2026-08-21 float migration alongside its three tranche siblings.
pub const IR_FD_CORE: &str = include_str!("../spec/core_spec/generated/ir_fd.core.txt");
/// The committed minted definition script of the `fdiv` chain.
pub const IR_FD_DEFS: &str = include_str!("../spec/core_spec/generated/ir_fd.defs.txt");
/// The committed mint record of the `fdiv` chain.
pub const IR_FD_RECORD: &str = include_str!("../spec/core_spec/generated/ir_fd.mint.json");
/// The committed tag table of the `fdiv` chain — empty aggregate lanes, the
/// interface as the load-bearing half, exactly as its three siblings'.
pub const IR_FD_TAGS: &str = include_str!("../spec/core_spec/generated/ir_fd.tags.json");
/// The committed core module of the `bvar_in_range` chain — the first
/// CONDBR-carrying body minted (2026-08-21, laneREG dump; digest equals all
/// three producer A/B columns).
pub const IR_BR_CORE: &str = include_str!("../spec/core_spec/generated/ir_br.core.txt");
/// The committed minted definition script of the `bvar_in_range` chain.
pub const IR_BR_DEFS: &str = include_str!("../spec/core_spec/generated/ir_br.defs.txt");
/// The committed mint record of the `bvar_in_range` chain.
pub const IR_BR_RECORD: &str = include_str!("../spec/core_spec/generated/ir_br.mint.json");
/// The committed tag table of the `bvar_in_range` chain — empty aggregate
/// lanes; the load-bearing half is the interface: three u32 parameter widths
/// and the two Bool joins.
pub const IR_BR_TAGS: &str = include_str!("../spec/core_spec/generated/ir_br.tags.json");
/// The committed core module of the `is_valid_char` chain — `ir_br`'s condbr
/// sibling at width 64 (minted 2026-08-21; digest equals all three producer
/// A/B columns).
pub const IR_VC_CORE: &str = include_str!("../spec/core_spec/generated/ir_vc.core.txt");
/// The committed minted definition script of the `is_valid_char` chain.
pub const IR_VC_DEFS: &str = include_str!("../spec/core_spec/generated/ir_vc.defs.txt");
/// The committed mint record of the `is_valid_char` chain.
pub const IR_VC_RECORD: &str = include_str!("../spec/core_spec/generated/ir_vc.mint.json");
/// The committed tag table of the `is_valid_char` chain — empty aggregate
/// lanes; the pins are the u64 argument width and the two Bool joins.
pub const IR_VC_TAGS: &str = include_str!("../spec/core_spec/generated/ir_vc.tags.json");
/// The committed core module of the `get_char_val_trunc` chain — the first
/// CAST-carrying body minted and the first with a UNIT parameter (2026-08-21;
/// digest equals all three producer A/B columns).
pub const IR_GC_CORE: &str = include_str!("../spec/core_spec/generated/ir_gc.core.txt");
/// The committed minted definition script of the `get_char_val_trunc` chain.
pub const IR_GC_DEFS: &str = include_str!("../spec/core_spec/generated/ir_gc.defs.txt");
/// The committed mint record of the `get_char_val_trunc` chain.
pub const IR_GC_RECORD: &str = include_str!("../spec/core_spec/generated/ir_gc.mint.json");
/// The committed tag table of the `get_char_val_trunc` chain. The sharp pin
/// is the UNIT closure environment: only this row witnesses it is empty.
pub const IR_GC_TAGS: &str = include_str!("../spec/core_spec/generated/ir_gc.tags.json");
/// The committed core module of the `meta_tag_shl` chain — the first
/// ASSERT-carrying body minted and the first CTFE seam (2026-08-21; digest
/// equals all three producer A/B columns).
pub const IR_MT_CORE: &str = include_str!("../spec/core_spec/generated/ir_mt.core.txt");
/// The committed minted definition script of the `meta_tag_shl` chain.
pub const IR_MT_DEFS: &str = include_str!("../spec/core_spec/generated/ir_mt.defs.txt");
/// The committed mint record of the `meta_tag_shl` chain.
pub const IR_MT_RECORD: &str = include_str!("../spec/core_spec/generated/ir_mt.mint.json");
/// The committed tag table of the `meta_tag_shl` chain — every lane EMPTY
/// and the emptiness is the pin; the only clause set with `proof`, sans
/// `names`.
pub const IR_MT_TAGS: &str = include_str!("../spec/core_spec/generated/ir_mt.tags.json");
/// The committed core module of the `expr_path_step_clone` chain — the
/// original specimen of the whole-crate enum drift class (181/181/176/182
/// observed, fixture-era 184 pinned; digest equals all three A/B columns).
pub const IR_EP_CORE: &str = include_str!("../spec/core_spec/generated/ir_ep.core.txt");
/// The committed minted definition script of the `expr_path_step_clone`
/// chain.
pub const IR_EP_DEFS: &str = include_str!("../spec/core_spec/generated/ir_ep.defs.txt");
/// The committed mint record of the `expr_path_step_clone` chain.
pub const IR_EP_RECORD: &str = include_str!("../spec/core_spec/generated/ir_ep.mint.json");
/// The committed tag table of the `expr_path_step_clone` chain: enum 184
/// (outside the atom pool, minted as the literal), and the first join to bind
/// an AGGREGATE — pinned as `enum#0` under `Tags::canon_ty`.
pub const IR_EP_TAGS: &str = include_str!("../spec/core_spec/generated/ir_ep.tags.json");
/// The committed core module of the `NodeId::index` chain — the chain that
/// FORCED the `usize` image (2026-08-22): reader A refused `trust_ir::Ty::Usize`
/// until the width was stated, and the resolution (64, one site) is a pinned
/// TARGET fact in the tag table, never a silent constant in a reader.
pub const IR_NI_CORE: &str = include_str!("../spec/core_spec/generated/ir_ni.core.txt");
/// The committed minted definition script of the `NodeId::index` chain.
pub const IR_NI_DEFS: &str = include_str!("../spec/core_spec/generated/ir_ni.defs.txt");
/// The committed mint record of the `NodeId::index` chain — ONE reader-A dump:
/// the chain postdates the producer A/B record, and the record says so.
pub const IR_NI_RECORD: &str = include_str!("../spec/core_spec/generated/ir_ni.mint.json");
/// The committed tag table of the `NodeId::index` chain: an INTERFACE-ONLY
/// struct row (the by-value receiver), and the first `usize` lane —
/// bits 64, one site, both compared by `project`.
pub const IR_NI_TAGS: &str = include_str!("../spec/core_spec/generated/ir_ni.tags.json");
/// The committed core module of the `set_lean4_core_strict_monads` chain —
/// the chain whose insertfield FIELD INDEX (81) was a named mint refusal until
/// the 2026-08-22 reclassification of field indices as machine data
/// (`shape.rs`), and the first minted body with a `store`.
pub const IR_SM_CORE: &str = include_str!("../spec/core_spec/generated/ir_sm.core.txt");
/// The committed minted definition script of the strict-monads-setter chain.
pub const IR_SM_DEFS: &str = include_str!("../spec/core_spec/generated/ir_sm.defs.txt");
/// The committed mint record of the strict-monads-setter chain — ONE reader-A
/// dump: the chain postdates the producer A/B record, and the record says so.
pub const IR_SM_RECORD: &str = include_str!("../spec/core_spec/generated/ir_sm.mint.json");
/// The committed tag table of the strict-monads-setter chain: one REAL struct
/// row (Environment, crate id 441), named by all three memory instructions.
pub const IR_SM_TAGS: &str = include_str!("../spec/core_spec/generated/ir_sm.tags.json");
/// The committed core module of the designated target `level::Level::is_zero`,
/// produced by reader A. MINTABLE since the 2026-08-22 pool widening and, since
/// the same day's decision memo
/// (`designs/2026-08-22-is-zero-model-vs-minted-decision.md`), REGISTERED as
/// `ir_lz_module` from [`IR_LZ_DEFS`] like every other chain. The hand
/// semantic model that used to carry that name is `ir_lzm_module`
/// (`eval_ir_crystal.rs`), and the A4/A5 theorems are about IT — see
/// `crystal_a2_mint_lz.rs` for the wall between the two, printed verbatim.
/// Read by the callee identity lane, which is the only chain in the set that
/// CALLS anything.
pub const IR_LZ_CORE: &str = include_str!("../spec/core_spec/generated/ir_lz.core.txt");
/// The minted definition script for the designated target: `ir_lz_tlevel`,
/// `ir_lz_b0`..`ir_lz_b9`, `ir_lz_func`, `ir_lz_module` — thirteen lines,
/// replayed verbatim by `eval_ir_level_minted.rs`. It defines ONE function and
/// CALLS a second (`<LevelArc as Deref>::deref`, canonical index 1) that is
/// not in the module, so `ir_call_exec` goes `stuck no_func` on the `Max` and
/// `IMax` arms: the A4 statement over this module is REFUTED, kernel-checked
/// (`ir_lz_minted_refutes_a4_on_max`), not proved. What IS proved about it is
/// representation equality with the artifact (M1–M10) and the three
/// constant-arm executions.
pub const IR_LZ_DEFS: &str = include_str!("../spec/core_spec/generated/ir_lz.defs.txt");
/// The mint record: both digests, the reader-A provenance it was cut from,
/// and the one-dump caveat (this chain postdates the producer A/B record).
pub const IR_LZ_RECORD: &str = include_str!("../spec/core_spec/generated/ir_lz.mint.json");
/// Reader A's append-only provenance for the exact Clean-0.4 source-bound
/// binary that produced [`IR_LZ_CORE`].  The callee-identity gate cross-links
/// its binary hash to the fixture-rebaseline evidence rather than trusting a
/// transient dump pathname.  The a152 predecessor remains committed beside
/// this file as the account of its own binary.
pub const IR_LZ_B039_PROVENANCE: &str =
    include_str!("../spec/core_spec/generated/ir_lz.b039.prov.json");
/// The committed tag table of the designated target. Its `funcs` lane is the
/// only one in the tree that is non-empty, because `level_is_zero` is the only
/// chained body that calls anything.
pub const IR_LZ_TAGS: &str = include_str!("../spec/core_spec/generated/ir_lz.tags.json");
