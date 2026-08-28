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

/// The 28 `Inst` variants the THIR lowerer constructs, as their `IRInst`
/// constructor names. Ordered as in `trust_ir::Inst` so the two lists can be
/// diffed by eye.
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
];

/// The six variants referenced only in pattern position by the lowerer, and so
/// deliberately absent from `IRInst`. Pinned so that if one of them starts being
/// constructed, this test is the place that notices.
pub(crate) const NOT_EMITTED: &[&str] = &[
    "assume",
    "copy",
    "heapalloc",
    "insertelement",
    "invoke",
    "nullptr",
];

/// The operator alphabets, with their exact Rust-side cardinalities.
pub(crate) const OPERATOR_ALPHABETS: &[(&str, usize)] = &[
    ("IRBinOp", 20),
    ("IRUnOp", 9),
    ("IRICmpOp", 10),
    ("IRFCmpOp", 12),
    ("IRCastOp", 17),
    ("IROverflowOp", 3),
];

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
    // the dispatch plus the seventeen in eval_ir_adequacy.rs. The grid
    // (data/evalir_adequacy_grid.json, scripts/evalir_adequacy_grid.py)
    // derives the 20-row set mechanically; gating them here holds each to
    // registered + EMPTY transitive axiom closure on the big box.
    "ir_exec_switch_exh_irrelevant",
    "ir_exec_callind_conv_irrelevant",
    "ir_exec_callind_sig_irrelevant",
    "ir_exec_load_ty_irrelevant",
    "ir_exec_load_vol_irrelevant",
    "ir_exec_store_ty_irrelevant",
    "ir_exec_store_vol_irrelevant",
    "ir_exec_alloca_ty_irrelevant",
    "ir_exec_gep_ty_irrelevant",
    "ir_exec_gep_inbounds_irrelevant",
    "ir_exec_ptrdata_ty_irrelevant",
    "ir_exec_ptrmeta_pt_irrelevant",
    "ir_exec_ptrmeta_mt_irrelevant",
    "ir_exec_ptrparts_pt_irrelevant",
    "ir_exec_ptrparts_mt_irrelevant",
    "ir_exec_extractfield_ty_irrelevant",
    "ir_exec_insertfield_ty_irrelevant",
    "ir_exec_extractelement_ty_irrelevant",
    "ir_exec_undef_ty_irrelevant",
    "ir_exec_select_ty_irrelevant",
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
