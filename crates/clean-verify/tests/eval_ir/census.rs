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
