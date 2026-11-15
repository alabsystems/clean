// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The pinned censuses the `EvalIR` acceptance gate checks against, and the one
//! helper that reads constructor names out of a built specification.
//!
//! Split out of `tests/eval_ir.rs` so that file stays inside the 500-line
//! paragon limit while gate clause 4 (`prelude_composition`) is added beside
//! it. Nothing here executes; every list is data the tests in the parent module
//! compare a built environment against.

use std::collections::BTreeSet;

use clean_kernel::Name;
use clean_verify::spec::Specification;

/// The shared representable `IRInst` alphabet. The original 30 constructor names
/// cover variants constructed by the executed bundle's two producers; the
/// appended sequential relaxed-u64 fetch-add is ByteV1-only. Legacy `ir_exec`
/// explicitly refuses that new constructor, so membership is not a claim of
/// successful legacy execution or measured three-executor agreement.
///
/// Twenty-eight come from the THIR lowerer (`crates/trust-thir-lower/src`);
/// `borrow` and `copy` come from the trust-ir bridge
/// (`crates/trust-ir-bridge/src/lower.rs`), the producer of the Phase-B callee
/// sidecar, which constructs `Inst::Borrow`/`Inst::BorrowMut` and `Inst::Copy`.
/// The modelled set is a SUBSET of the constructed set. B2C will publish that
/// difference by minting `data/irinst_producer_census.json`; until it exists,
/// the difference is stated nowhere checkable and no count of it should be
/// quoted from this list.
pub(crate) const EMITTED_INSTS: &[&str] = &[
    // arithmetic / comparison / cast
    "binop",
    "unop",
    "overflow",
    "icmp",
    "fcmp",
    "cast",
    // memory
    "load",
    "store",
    "alloca",
    "gep",
    "ptrdata",
    "ptrmetadata",
    "ptrfromparts",
    // control flow
    "br",
    "condbr",
    "switch",
    "call",
    "callindirect",
    "ret",
    // aggregates
    "extractfield",
    "insertfield",
    "extractelement",
    // constants
    "const_",
    "globaladdr",
    "undef",
    // proof
    "assert",
    "unreachable",
    // pseudo
    "select",
    // the trust-ir bridge's two (Phase B)
    "borrow",
    "copy",
    // Compiler-owned atomic bridge; sequential byte execution only.
    "atomic_fetch_add_relaxed_u64_seq",
    // Distinct target-indexed Usize lane. Source attachment is separate work.
    "atomic_fetch_add_relaxed_usize_seq",
    // Retained syntax only; all executors explicitly halt unmodelled.
    "release",
];

/// Variants with no syntactic image, pinned so that adding one to
/// `IRInst` without moving this list fails here.
///
/// The old comment said they were "referenced only in pattern position by the
/// lowerer" and that "if one of them starts being constructed, this test is
/// the place that notices". BOTH halves were false and are corrected here
/// rather than repeated. Measured 2026-09-10 at trust `0dd9d3e2d7` with
/// `grep -n 'InstrNode::new(Inst::<V> {'`: `Inst::InsertElement` is
/// CONSTRUCTED at 8 sites in `crates/trust-thir-lower/src/lib.rs` and
/// `Inst::Assume` at 14 in `crates/trust-ir-bridge/src/lower.rs` — nothing
/// noticed, because no gate ever compared this list against either producer.
/// That grep counts construction-SHAPED text rather than code (the project's
/// own scanner rule), so read the counts as evidence that "never constructed"
/// is false, not as the census; the parse-based scan is B2C's. `copy` left this
/// list in Phase B for the opposite reason: the bridge constructs it and the
/// machine now models it. The list is syntactically excluded, not
/// "unconstructed". B2C will make the constructed set checkable, by minting
/// `data/irinst_producer_census.json` from a parse-based two-producer scan
/// whose `unmodelled_constructed` field publishes the difference; that
/// artifact does not exist yet, so do not send a reader to it as if it did.
pub(crate) const NOT_EMITTED: &[&str] =
    &["assume", "heapalloc", "insertelement", "invoke", "nullptr"];

/// Every `EvalIR` inductive the firewall must clear. These are the relations and
/// data families the crystal's equality theorem will quantify over, so a
/// layer-2 predicate reachable from any of their constructor fields would make
/// that theorem vacuous.
pub(crate) const EVAL_IR_FAMILIES: &[&str] = &[
    "IRTy",
    "IRConst",
    "IRBinOp",
    "IRUnOp",
    "IRICmpOp",
    "IRFCmpOp",
    "IRCastOp",
    "IROverflowOp",
    "IRSwitchCase",
    "IRInst",
    "IREnc",
    "IRNode",
    "IRBlock",
    "IRFunc",
    "IRGlobal",
    "IRModule",
    "IRScalar",
    "IRBinding",
    "IRMemSlot",
    "IRFrame",
    "IRMachine",
    "IRFault",
    "IROutcome",
    "IRConfig",
    "IRStepResult",
];

/// The seven crystal executions plus exact wrapping-arithmetic and cast
/// executions registered by the stage.
pub(crate) const WITNESSES: &[&str] = &[
    "ir_is_zero_on_zero",
    "ir_is_zero_on_param",
    "ir_is_zero_on_succ",
    "ir_is_zero_on_max_zero_zero",
    "ir_is_zero_on_max_zero_param",
    "ir_is_zero_on_imax_param_zero",
    "ir_is_zero_dead_arc_panics",
    "ir_exact_add_wraps",
    "ir_exact_sub_wraps",
    "ir_exact_mul_wraps",
    "ir_exact_sdiv_negative",
    "ir_exact_srem_negative",
    "ir_sdiv_min_overflow",
    "ir_sdiv_zero_ub",
    "ir_exact_shl",
    "ir_exact_lshr",
    "ir_exact_ashr",
    "ir_shift_oversize_ub",
    "ir_exact_integer_and",
    "ir_exact_integer_not",
    "ir_exact_integer_ctpop",
    "ir_exact_slt_sign_boundary",
    "ir_exact_sgt_negative_pair",
    // The float-comparison lane (plan W4, 2026-08-25): the 12 fcmp predicates
    // over the classified binary64 substrate, each vector checked against
    // trust-ir a4e81b6's eval_fcmp_f64 and against host f64 by the stage
    // file's own Rust tests. The three ir_fcmp_* rows are the universally
    // quantified fragment/fault boundary (integer type, binary32, non-float
    // operand).
    "ir_exact_fcmp_oeq_equal",
    "ir_exact_fcmp_oeq_nan",
    "ir_exact_fcmp_ueq_nan",
    "ir_exact_fcmp_une_nan",
    "ir_exact_fcmp_olt_nan",
    "ir_exact_fcmp_ult_nan",
    "ir_exact_fcmp_oeq_zeros",
    "ir_exact_fcmp_olt_zeros",
    "ir_exact_fcmp_olt_neg",
    "ir_exact_fcmp_ogt_swap",
    "ir_exact_fcmp_oge_inf",
    "ir_exact_fcmp_olt_ninf",
    "ir_exact_fcmp_ole_asym",
    "ir_exact_fcmp_uge_nan",
    "ir_exact_fcmp_junk_oeq",
    "ir_exact_fcmp_junk_ueq",
    "ir_fcmp_int_ty_faults",
    "ir_fcmp_f32_unmodelled",
    "ir_fcmp_not_float_operand",
    // The overflow value domain (plan W3, 2026-08-25): the checked-arithmetic
    // value/flag vectors, width 4, each checked against trust-ir a4e81b6's
    // unsigned_overflow / signed_overflow / eval_int_binop.
    "ir_exact_ovf_add_wrap",
    "ir_exact_ovf_add_flag_u",
    "ir_exact_ovf_add_flag_u_boundary",
    "ir_exact_ovf_sub_borrow",
    "ir_exact_ovf_sub_flag_u",
    "ir_exact_ovf_sub_flag_u_eq",
    "ir_exact_ovf_mul_wrap",
    "ir_exact_ovf_mul_flag_u",
    "ir_exact_ovf_mul_flag_u_boundary",
    "ir_exact_ovf_s_add_min",
    "ir_exact_ovf_s_add_min_value",
    "ir_exact_ovf_s_add_mixed",
    "ir_exact_ovf_s_sub_min",
    "ir_exact_ovf_s_sub_min_neg",
    "ir_exact_ovf_s_mul_min",
    "ir_exact_ovf_s_mul_min_value",
    "ir_exact_ovf_s_mul_min_ok",
    // The adequacy grid's theorem band (plan W5, 2026-08-25): one
    // dropped-operand irrelevance theorem per field the ir_exec dispatch
    // binds and never reads — the three operand-audit-era precedents beside
    // the dispatch plus the sixteen in eval_ir_adequacy.rs. The grid
    // (data/evalir_adequacy_grid.json, scripts/evalir_adequacy_grid.py)
    // derives the row set mechanically; gating them here holds each to
    // registered + EMPTY transitive axiom closure on the big box.
    //
    // `ir_exec_load_ty_irrelevant` LEFT this list in Phase B and did not move
    // house: the load arm now READS the type through the module's derived
    // encodings table, so the theorem is false of the general module and is
    // replaced by the pair below — the conservativity half stated at an
    // `IRModule.mk`, and the negative witness that exhibits a module at which
    // the view is not the identity.
    "ir_exec_switch_exh_irrelevant",
    "ir_exec_callind_conv_irrelevant",
    "ir_exec_callind_sig_irrelevant",
    "ir_exec_load_vol_irrelevant",
    "ir_exec_store_ty_irrelevant",
    "ir_exec_store_vol_irrelevant",
    "ir_exec_alloca_ty_irrelevant",
    "ir_exec_gep_ty_irrelevant",
    "ir_exec_gep_inbounds_irrelevant",
    "ir_exec_ptrdata_ty_irrelevant",
    "ir_exec_ptrmeta_pt_irrelevant",
    "ir_exec_ptrparts_pt_irrelevant",
    "ir_exec_ptrparts_mt_irrelevant",
    "ir_exec_extractfield_ty_irrelevant",
    "ir_exec_insertfield_ty_irrelevant",
    "ir_exec_extractelement_ty_irrelevant",
    "ir_exec_undef_ty_irrelevant",
    "ir_exec_select_ty_irrelevant",
    // Phase B (link 3): the encoding-aware load view and the two arms the
    // trust-ir bridge's sidecar bodies carry. Each is an Eq.refl over the
    // registered semantics, so an empty axiom closure is the whole claim.
    "ir_exec_load_ty_irrelevant_mk",
    "ir_load_view_mkv_reads_ty",
    "ir_borrow_no_provenance_is_ub",
    "ir_copy_ty_slot_is_read",
    "ir_view_ptr0_is_none",
    "ir_view_agg_is_identity",
    // The float-residue band (2026-08-25, evalir_w4.PENDING.md delta 5's
    // wave): fneg/fabs, fmin/fmax, ffloor/fceil/ftrunc executed vectors —
    // each cross-checked against trust-ir a4e81b6's eval_float_unop /
    // eval_float_binop on host f64 by the stage file's own Rust tests — plus
    // the duplication pin (ir_f64_ltb_pre_agrees), the universally
    // quantified DATED refusals (frem/fsqrt/fdiv-finite, the binary32
    // boundary, and the eight fp casts).
    "ir_exact_fneg_one",
    "ir_exact_fneg_mzero",
    "ir_exact_fneg_nan",
    "ir_exact_fneg_junk_refused",
    "ir_exact_fabs_mone",
    "ir_exact_fabs_mzero",
    "ir_exact_fabs_nan_neg",
    "ir_exact_fmin_ordered",
    "ir_exact_fmax_ordered",
    "ir_exact_fmin_neg_pair",
    "ir_exact_fmin_nan_left",
    "ir_exact_fmax_nan_right",
    "ir_exact_fmin_ninf",
    "ir_exact_fmin_nan_both_refused",
    "ir_exact_fmin_zero_pair_refused",
    "ir_exact_fmax_zero_pair_refused",
    "ir_exact_ffloor_pos",
    "ir_exact_ffloor_neg",
    "ir_exact_fceil_neg",
    "ir_exact_ftrunc_neg",
    "ir_exact_ffloor_small_neg",
    "ir_exact_fceil_small_neg_keeps_mzero",
    "ir_exact_ftrunc_small_pos",
    "ir_exact_fceil_carry",
    "ir_exact_ffloor_already_int",
    "ir_exact_ffloor_mzero",
    "ir_exact_ffloor_inf",
    "ir_exact_ffloor_nan_refused",
    "ir_f64_ltb_pre_agrees",
    "ir_frem_unmodelled",
    "ir_fsqrt_unmodelled",
    "ir_fdiv_fin_fin_unmodelled",
    "ir_fneg_f32_unmodelled",
    "ir_fmin_f32_unmodelled",
    "ir_ffloor_f32_unmodelled",
    "ir_cast_fptrunc_unmodelled",
    "ir_cast_fpext_unmodelled",
    "ir_cast_fptoui_unmodelled",
    "ir_cast_fptosi_unmodelled",
    "ir_cast_uitofp_unmodelled",
    "ir_cast_sitofp_unmodelled",
    "ir_cast_fptosisat_unmodelled",
    "ir_cast_fptouisat_unmodelled",
    "ir_exact_trunc_low_bit",
    "ir_exact_zext_canonicalizes",
    "ir_exact_sext_negative",
    "ir_inttoptr_fails_closed",
    // The constant evaluator, after `IRConst` gained its aggregate form
    // (`aggv`/`vnil`/`vcons`) for `mode::CleanMode::from_source_system`. The
    // first nine pin every PRE-EXISTING arm's meaning across the rewrite of
    // `ir_const_value` from a `match` into an `IRConst.rec`; the rest execute
    // the new case and its fail-closed edges.
    "ir_const_value_int_unchanged",
    "ir_const_value_bool_unchanged",
    "ir_const_value_unit_unchanged",
    "ir_const_value_null_unchanged",
    "ir_const_value_undef_unchanged",
    "ir_const_value_float_unchanged",
    "ir_const_value_func_unchanged",
    "ir_const_eval_int_still_wraps",
    "ir_const_eval_int_rejects_agg_ty",
    "ir_const_value_agg_is_ir_var",
    "ir_const_eval_agg_at_enum",
    "ir_const_eval_agg_at_struct",
    "ir_const_eval_agg_at_scalar_fails_closed",
    "ir_const_eval_bare_spine_fails_closed",
    "ir_const_eval_bare_cons_fails_closed",
    "ir_const_agg_nonspine_has_no_fields",
    "ir_const_agg_empty",
    "ir_const_agg_two_elements",
    "ir_const_agg_nested",
];

/// Phase-B's return-slot stage, in registration order (`add_eval_ir_slot_lemmas`).
///
/// The alloca/store/load/ret pattern every derived-bundle callee body opens
/// with, closed at an ABSTRACT heap and an ABSTRACT allocation counter, plus
/// the five substrate facts it rests on. The stage file carries the same list
/// for its own structural tests; this copy is what the registration gate holds
/// against the built spec.
pub(crate) const SLOT_LEMMAS: &[&str] = &[
    // The store/load view family (2026-09-13), first because DECLS registers
    // it first. See `eval_ir_slot_lemmas.rs` for why the store arm may ignore
    // its type and exactly where that stops being true.
    "ir_exec_load_is_view",
    "ir_view_word_agg",
    "ir_view_opt_agg",
    "ir_view_ty_agg",
    "ir_load_view_opt_agg",
    "ir_load_view_agg",
    "ir_exec_load_agg",
    "ir_nat_sub_self",
    "ir_nat_eqb_walk_refl",
    "ir_nat_eqb_refl",
    "ir_mem_lookup_head",
    "ir_mem_update_head",
    "ir_mem_lookup_skip",
    "ir_slot_b0",
    "ir_slot_func",
    "ir_slot_module",
    "ir_slot_mach0",
    "ir_slot_smach",
    "ir_slot_lmach",
    "ir_slot_rmach",
    "ir_slot_after_store_lookup",
    "ir_slot_after_store_update",
    "ir_slot_after_load",
    "ir_slot_step_alloca",
    "ir_slot_step_store",
    "ir_slot_store_resolved",
    "ir_slot_step_load",
    "ir_slot_store_seg",
    "ir_slot_load_seg",
    "ir_slot_activation",
    "ir_slot_seg",
    "ir_slot_cost_is_4",
    "ir_slot_concrete",
    "ir_slot_resumes_caller",
];

/// The one `ir_slot_`-prefixed declaration that is NOT part of that stage:
/// `add_eval_ir`'s liveness projection, registered long before it. Named here
/// so the gate can assert the prefix EXACTLY rather than merely inclusively.
pub(crate) const SLOT_PREFIX_NOT_FROM_THE_STAGE: &[&str] = &["ir_slot_live"];

pub(crate) fn ctor_names(spec: &Specification, inductive: &str) -> BTreeSet<String> {
    spec.env()
        .get_inductive(&Name::from_string(inductive))
        .map(|ind| {
            ind.constructor_names
                .iter()
                .map(|n| {
                    n.to_string()
                        .rsplit_once('.')
                        .map_or_else(|| n.to_string(), |(_, last)| last.to_string())
                })
                .collect()
        })
        .unwrap_or_default()
}
