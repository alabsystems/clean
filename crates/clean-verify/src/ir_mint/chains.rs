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
/// Reader A's OWN provenance for the width-one chain over the exact binary the
/// 2026-10-07 source-bound rebaseline (clean 047ebd051) cut the fixture from,
/// emitted by `scripts/crystal_a2_project` beside a byte-identical
/// `ir_h2.core.txt`. M7 compares the tag table's crate ids against THIS record:
/// the producer A/B table is historical (field-81 era, `enum.13` on all three
/// producers), and its ids stop describing the artifact the moment a kernel type
/// is interned ahead of `CleanMode` -- which 047ebd051's two new `Environment`
/// fields did (`enum.13` -> `enum.17`).
pub const IR_H2_PROVENANCE: &str = include_str!("../spec/core_spec/generated/ir_h2.core.prov.json");
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
/// `ir_cf` and `ir_sh` — the two chains whose committed core AND committed
/// emitted text were both on disk with NEITHER exposed, so nothing read either
/// and nothing could notice the two drifting apart. Measured 2026-09-20:
/// `IR_CF_CORE`/`IR_SH_CORE` were undefined and the strings `ir_cf` / `ir_sh`
/// appeared nowhere under `ir_mint/`, while `generated/ir_{cf,sh}.emitted.txt`
/// had been committed all along. Exposed here so the corpus test can compare
/// reader A against reader B, which is the check every other chain's core gets.
pub const IR_CF_CORE: &str = include_str!("../spec/core_spec/generated/ir_cf.core.txt");
/// The committed EMITTED trust-ir of the `ir_cf` chain — reader B's input.
pub const IR_CF_EMITTED: &str = include_str!("../spec/core_spec/generated/ir_cf.emitted.txt");
/// The committed tag table of the `ir_cf` chain.
pub const IR_CF_TAGS: &str = include_str!("../spec/core_spec/generated/ir_cf.tags.json");
/// The committed core module of the `ir_sh` chain, reader A's side.
pub const IR_SH_CORE: &str = include_str!("../spec/core_spec/generated/ir_sh.core.txt");
/// The committed EMITTED trust-ir of the `ir_sh` chain — reader B's input.
pub const IR_SH_EMITTED: &str = include_str!("../spec/core_spec/generated/ir_sh.emitted.txt");
/// The committed tag table of the `ir_sh` chain.
pub const IR_SH_TAGS: &str = include_str!("../spec/core_spec/generated/ir_sh.tags.json");

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

/// The committed core module of the `ir_its` chain — the FIRST projected from a
/// body of `TypeChecker::infer_type`'s DERIVED CLOSURE rather than from the
/// crate module. Function index 102 of the callee sidecar's partial bundle,
/// `<[level::Level; 2] as smallvec::Array>::size`, produced by reader A with an
/// explicit `--usize-bits 64`: this is the first chained body whose core module
/// resolves `usize` at all, and `a2project` refuses to resolve it silently.
pub const IR_ITS_CORE: &str = include_str!("../spec/core_spec/generated/ir_its.core.txt");
/// The minted definition script for that body: `ir_its_b0`, `ir_its_func`,
/// `ir_its_module` — three lines, replayed verbatim by `eval_ir_its.rs`, over
/// which A4 (`ir_its_correct`) and A5 (`ir_its_machine_sound`) are proved.
pub const IR_ITS_DEFS: &str = include_str!("../spec/core_spec/generated/ir_its.defs.txt");
/// The mint record: both digests and the definition count.
pub const IR_ITS_RECORD: &str = include_str!("../spec/core_spec/generated/ir_its.mint.json");
/// Reader A's provenance for the projection — the dump it was cut from, its
/// sha256, the artifact indices, and the `usize_bits` target fact with the
/// number of sites it resolved.
pub const IR_ITS_PROVENANCE: &str =
    include_str!("../spec/core_spec/generated/ir_its.core.prov.json");
/// The committed tag table. Every aggregate lane is EMPTY and that is a
/// measurement; the interface lanes carry the two ways this chain differs from
/// every crate-module one (no calling-convention keyword, `trust-ir` producer).
pub const IR_ITS_TAGS: &str = include_str!("../spec/core_spec/generated/ir_its.tags.json");
/// Reader B's input for this chain: the emitted trust-ir text for the body,
/// excerpted verbatim from the dump `ir_its.core.prov.json` names and sha256s.
///
/// It lives HERE and not in `tests/fixtures/` on purpose: `crystal-fixture-pins`
/// requires every fixture there to carry a row in the single current rebaseline
/// record, whose premise is that every retained fixture is byte-identical to ONE
/// dump — and this body comes from a second one (the `infer_type` callee
/// sidecar bundle) that contains none of the others. See the note at the top of
/// `tests/crystal_a2_mint_its.rs` and docs/JUSTIFIED_EXCEPTIONS.md.
pub const IR_ITS_EMITTED: &str = include_str!("../spec/core_spec/generated/ir_its.emitted.txt");

// ── ir_it — THE DESIGNATED TARGET ──────────────────────────────────────────
//
// `TypeChecker::infer_type` itself, function index 0 of the same callee sidecar
// bundle `ir_its` is cut from. Every other chain in this file is a body chosen
// because it was tractable; this is the body the crystal is FOR.
//
// It is not a bigger `ir_its`. Six blocks where `ir_its` has one, a `switch`, a
// call to `tick_heartbeat` and a call to `infer_type_fast`, and five `undef`
// aggregates. Two consequences travel with those and are pinned by the gate in
// `tests/crystal_a2_mint_it.rs`: the unwitnessed ledger is NOT empty here (one
// slot, because trust-ir's Display never prints `Switch.exhaustive_enum_
// unreachable`), and reader B must be given this body's OWN func id, because a
// body that calls anything needs `self_crate_id` interned first.

/// The committed core module of the `ir_it` chain — **the crystal's designated
/// target**, `TypeChecker::infer_type`, projected by reader A from function
/// index 0 of the `infer_type` callee sidecar bundle.
pub const IR_IT_CORE: &str = include_str!("../spec/core_spec/generated/ir_it.core.txt");
/// The minted definition script for that body — THIRTEEN definitions, against
/// `ir_its`'s three, replayed verbatim by `eval_ir_it.rs`.
pub const IR_IT_DEFS: &str = include_str!("../spec/core_spec/generated/ir_it.defs.txt");
/// The mint record: both digests, the definition count, and the ONE
/// `text_unwitnessed` slot this chain has and `ir_its` does not.
pub const IR_IT_RECORD: &str = include_str!("../spec/core_spec/generated/ir_it.mint.json");
/// Reader A's provenance: the callee-sidecar dump and its sha256, the artifact
/// indices, and the target-width fact — which for this body resolved ZERO
/// `usize` sites and FOUR `isize` ones, the reverse of `ir_its`.
pub const IR_IT_PROVENANCE: &str = include_str!("../spec/core_spec/generated/ir_it.core.prov.json");
/// The committed tag table — the largest in the tree: five `structs` rows and
/// three `funcs` rows, where most chains have none of either.
pub const IR_IT_TAGS: &str = include_str!("../spec/core_spec/generated/ir_it.tags.json");
/// Reader B's input for this chain. It lives in `generated/` beside reader A's
/// projection for the same structural reason `IR_ITS_EMITTED` does — it is cut
/// from the callee sidecar dump, not the crate module's, and the fixture-pin
/// gate's rebaseline premise cannot span two dumps.
pub const IR_IT_EMITTED: &str = include_str!("../spec/core_spec/generated/ir_it.emitted.txt");
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
/// the chain whose insertfield FIELD INDEX (81 then, 83 since the 2026-10-07
/// re-derivation) was a named mint refusal until
/// the 2026-08-22 reclassification of field indices as machine data
/// (`shape.rs`), and the first minted body with a `store`.
pub const IR_SM_CORE: &str = include_str!("../spec/core_spec/generated/ir_sm.core.txt");
/// The committed minted definition script of the strict-monads-setter chain.
pub const IR_SM_DEFS: &str = include_str!("../spec/core_spec/generated/ir_sm.defs.txt");
/// The committed mint record of the strict-monads-setter chain — ONE reader-A
/// dump: the chain postdates the producer A/B record, and the record says so.
pub const IR_SM_RECORD: &str = include_str!("../spec/core_spec/generated/ir_sm.mint.json");
/// The committed tag table of the strict-monads-setter chain: one REAL struct
/// row (Environment, crate id 586), named by all three memory instructions.
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
/// Reader A's append-only provenance for the binary the 2026-10-07 source-bound
/// rebaseline (clean 047ebd051, trustc 321aaeda7) cut `level_is_zero`'s fixture
/// from: the CURRENT record the callee-identity gate binds, superseding
/// [`IR_LZ_B039_PROVENANCE`], which stays committed beside it as the account of
/// its own binary (as `ir_lz.a152.prov.json` did before it). Same core digest
/// and names; only the crate ids moved (3905/3894 -> 1961/1947).
pub const IR_LZ_047E_PROVENANCE: &str =
    include_str!("../spec/core_spec/generated/ir_lz.047e.prov.json");
/// The committed tag table of the designated target. Its `funcs` lane is the
/// only one in the tree that is non-empty, because `level_is_zero` is the only
/// chained body that calls anything.
pub const IR_LZ_TAGS: &str = include_str!("../spec/core_spec/generated/ir_lz.tags.json");
/// The committed core module of the `ir_lzc` chain — the SECOND core module
/// with two functions, and the FIRST with a non-empty `(globals …)` list.
///
/// `level::Level::is_zero` TOGETHER WITH the body of
/// `<level::LevelArc as std::ops::Deref>::deref`, projected beside it from the
/// SAME dump under ONE interning namespace (`a2project … --with …`). Function 0
/// is the designated target RE-MINTED — byte-identical to the `(func 0 …)`
/// block of [`IR_LZ_CORE`], which is what `crystal_a2_mint_lzc.rs::m1` checks
/// today; S9 ties the minted `ir_lzc_func` to the frozen `ir_lz_func` by a
/// kernel-checked `Eq.refl` rather than replacing it. Canonicals 2 and 3 are
/// DECLARATIONS the crate artifact carries with no body, so the call resolves
/// at index 1 and `ir_call_exec` goes `stuck no_func` ONE CALL DEEPER than
/// `ir_lz` does. This is Phase A of retiring the authored `ir_lzb_deref`
/// model: A4 is NOT claimed over this module.
pub const IR_LZC_CORE: &str = include_str!("../spec/core_spec/generated/ir_lzc.core.txt");
/// The committed minted definition script of the `ir_lzc` chain — SIXTEEN
/// lines: the alias, the FIRST non-empty `IRGlobal` line the mint has ever
/// produced, the root's ten blocks and its func, the deref's one block and its
/// func under the tag table's `ir_lad` prefix, and the two-function /
/// one-global module line.
pub const IR_LZC_DEFS: &str = include_str!("../spec/core_spec/generated/ir_lzc.defs.txt");
/// The committed mint record of the `ir_lzc` chain — ONE reader-A dump, stated
/// as one and not inherited from `ir_lz`'s two, plus the declarations note that
/// names canonicals 2/3 and the Phase-B join key (crate id AND functy, because
/// the artifact holds a second declaration under the same name).
pub const IR_LZC_RECORD: &str = include_str!("../spec/core_spec/generated/ir_lzc.mint.json");
/// Reader A's OWN provenance for the `ir_lzc` projection, emitted BY
/// `scripts/crystal_a2_project` beside `ir_lzc.core.txt` in the same run — the
/// [`IR_LZ_B039_PROVENANCE`] shape, one chain later. M7 compares the tag
/// table's pins against THIS file rather than against the mint record's
/// hand-maintained `reader_a` block, and then compares the two, so the record
/// cannot drift away from the artifact in silence: the reader's ids, names,
/// resolved element type and core digest are the evidence, and the record is a
/// transcription that has to keep matching it.
pub const IR_LZC_PROVENANCE: &str =
    include_str!("../spec/core_spec/generated/ir_lzc.core.prov.json");
/// The committed tag table of the `ir_lzc` chain — `level::Level::is_zero`
/// TOGETHER WITH the body of `<level::LevelArc as std::ops::Deref>::deref`
/// that reader A projects beside it from the same dump. Three firsts in one
/// table: a `funcs` lane with FOUR rows, two of them DECLARATIONS (`defined:
/// false` — `Option::as_deref` and `Option::expect` have no body in the crate
/// artifact, so `ir_call_exec` goes `stuck no_func` one call deeper than
/// `ir_lz` does); an `extra_bodies` row whose body CALLS declarations; and the
/// first `globals` lane, pinning the one module-table global the deref names
/// (`__trust_promoted_4557`, the `expect` message bytes) by name, resolved
/// type and linkage. The other three constants of the quartet are
/// [`IR_LZC_CORE`], [`IR_LZC_DEFS`] and [`IR_LZC_RECORD`], above.
pub const IR_LZC_TAGS: &str = include_str!("../spec/core_spec/generated/ir_lzc.tags.json");

/// The FIVE-BODY module: the designated target plus the real bodies of every
/// function it reaches, from TWO artifacts joined by the callee sidecar's
/// manifest. No authored function.
pub const IR_LZD_CORE: &str = include_str!("../spec/core_spec/generated/ir_lzd.core.txt");
/// Reader A's record for [`IR_LZD_CORE`], including both input digests and
/// both declaration-to-body retargets.
pub const IR_LZD_PROVENANCE: &str =
    include_str!("../spec/core_spec/generated/ir_lzd.core.prov.json");
/// The five-body chain's tag table.
pub const IR_LZD_TAGS: &str = include_str!("../spec/core_spec/generated/ir_lzd.tags.json");
/// The minted script for [`IR_LZD_CORE`] — 38 declarations ending in
/// `ir_lzd_module`, an `IRModule.mkv` over FIVE functions, one global and a
/// FOUR-row encodings table (two niche rows, two pointer-wrapper rows).
pub const IR_LZD_DEFS: &str = include_str!("../spec/core_spec/generated/ir_lzd.defs.txt");

/// The committed core module of `env::native_reducers_float::reduce_float_beq::{closure#0}`
/// — `ir_fa`'s shape with the one COMPARISON of the float tranche, and the first
/// chained body whose emitted instruction is an `fcmp`. Every aggregate lane is
/// measured EMPTY, as on `ir_fa`; what this adds over the W4 synthetic lane is
/// that `oeq` at binary64 is now witnessed by an EMITTED body rather than by an
/// authored micro-module. It closes no coverage gap — W4 covers every `FCmpOp`
/// already — and it is not A0-eligible: the body's `derived_mir` verdict is
/// `unsupported`.
pub const IR_FBQ_CORE: &str = include_str!("../spec/core_spec/generated/ir_fbq.core.txt");
/// The committed minted definition script of the `fcmp oeq` chain.
pub const IR_FBQ_DEFS: &str = include_str!("../spec/core_spec/generated/ir_fbq.defs.txt");
/// The committed mint record of the `fcmp oeq` chain.
pub const IR_FBQ_RECORD: &str = include_str!("../spec/core_spec/generated/ir_fbq.mint.json");
/// The committed tag table of the `fcmp oeq` chain. Its `functy` is 319 and NOT
/// `ir_fa`'s 381: the four `f64 -> f64` closures share one signature entry,
/// while this body returns `bool`, so `(ptr, f64, f64) -> bool` is its own.
pub const IR_FBQ_TAGS: &str = include_str!("../spec/core_spec/generated/ir_fbq.tags.json");

/// The committed core module of `env::native_reducers_float::reduce_float_neg::{closure#0}`
/// — the UNARY member of the float tranche: two parameters, one `unop`. The W2a
/// synthetic lane's header names `unop` among "the constructors no emitted body
/// exercises"; this body is the counterexample, and that is the whole of what it
/// adds. Not A0-eligible: its `derived_mir` verdict is `unsupported`.
pub const IR_FNG_CORE: &str = include_str!("../spec/core_spec/generated/ir_fng.core.txt");
/// The committed minted definition script of the `fneg` chain.
pub const IR_FNG_DEFS: &str = include_str!("../spec/core_spec/generated/ir_fng.defs.txt");
/// The committed mint record of the `fneg` chain.
pub const IR_FNG_RECORD: &str = include_str!("../spec/core_spec/generated/ir_fng.mint.json");
/// The committed tag table of the `fneg` chain. Its `functy` is 318 — its own
/// entry, neither `ir_fa`'s 381 nor `ir_fbq`'s 319, because the signature is
/// `(ptr, f64) -> f64` and the other two take three parameters.
pub const IR_FNG_TAGS: &str = include_str!("../spec/core_spec/generated/ir_fng.tags.json");
