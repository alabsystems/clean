// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` acceptance gate (crystal job **C3**).
//!
//! C3's gate has three clauses, and there is one test here per clause:
//!
//! 1. *Every emitted construct has a case.* — `ir_exec` dispatches on `IRInst`,
//!    so the claim reduces to `IRInst` having exactly one constructor per
//!    trust-ir `Inst` variant the THIR lowerer constructs.
//!    [`eval_ir_covers_exactly_the_emitted_inst_set`] pins that set by name
//!    against the measured census, so both a missing arm and an invented one
//!    fail closed.
//! 2. *The firewall (C2) passes over it.* —
//!    [`eval_ir_relations_pass_the_vacuity_firewall`] runs the C2 walker over
//!    every `EvalIR` inductive.
//! 3. *A hand-executed `is_zero` derivation returns the right Bool.* — the seven
//!    witnesses are registered as `Eq.refl` definitions inside the stage itself,
//!    so [`eval_ir_spec_builds`] passing IS that derivation succeeding: the
//!    kernel ran the machine. [`eval_ir_witnesses_are_registered_and_axiom_free`]
//!    then checks they are present and rest on nothing.
//!
//! The measured census the coverage list comes from (re-runnable in
//! the sibling trust checkout's `crates/trust-thir-lower/src`):
//!
//! ```text
//! grep -roh "Inst::[A-Za-z0-9_]*" . | sort | uniq -c | sort -rn
//! ```
//!
//! 34 variants are referenced; six of them — `Assume`, `Copy`, `HeapAlloc`,
//! `InsertElement`, `Invoke`, `NullPtr` — occur only in pattern position and are
//! never constructed, leaving **28 constructed**. That is the denominator, and
//! it is 28 of the 57 variants of the full `Inst` enum.

use std::collections::BTreeSet;

use clean_kernel::Name;
use clean_verify::spec::Specification;
use clean_verify::test_utils::build_eval_ir_spec_with_stack;
use clean_verify::vacuity_firewall::{audit_relation, env_knows};

/// The 28 `Inst` variants the THIR lowerer constructs, as their `IRInst`
/// constructor names. Ordered as in `trust_ir::Inst` so the two lists can be
/// diffed by eye.
const EMITTED_INSTS: &[&str] = &[
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
const NOT_EMITTED: &[&str] = &[
    "assume",
    "copy",
    "heapalloc",
    "insertelement",
    "invoke",
    "nullptr",
];

/// The operator alphabets, with their exact Rust-side cardinalities.
const OPERATOR_ALPHABETS: &[(&str, usize)] = &[
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
const EVAL_IR_FAMILIES: &[&str] = &[
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
const WITNESSES: &[&str] = &[
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
];

fn ctor_names(spec: &Specification, inductive: &str) -> BTreeSet<String> {
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

/// GATE CLAUSE 3, and the load-bearing test in this file.
///
/// The seven `is_zero` executions are `Eq.refl` definitions registered by the
/// stage, so the stage building at all means the kernel *ran the machine* on
/// each input and found the stated outcome. Nothing here is asserted by hand:
/// if any arm of the 28-way dispatch were wrong for those inputs, or the
/// recursion, or the null check, the definition would fail to typecheck and this
/// test would fail with the elaborator's message.
#[test]
fn eval_ir_spec_builds() {
    let spec = build_eval_ir_spec_with_stack();
    assert!(
        env_knows(spec.env(), "ir_eval"),
        "the EvalIR entry point must be registered; the stage built but ir_eval is absent"
    );
}

/// GATE CLAUSE 1: coverage, stated as a fraction and checked by name.
#[test]
fn eval_ir_covers_exactly_the_emitted_inst_set() {
    let spec = build_eval_ir_spec_with_stack();
    let found = ctor_names(&spec, "IRInst");

    let expected: BTreeSet<String> = EMITTED_INSTS.iter().map(|s| (*s).to_string()).collect();
    assert_eq!(
        expected.len(),
        EMITTED_INSTS.len(),
        "the EMITTED_INSTS list has a duplicate"
    );
    assert_eq!(
        found.len(),
        28,
        "IRInst must have exactly 28 constructors (the measured constructed-Inst census); found {}: {:?}",
        found.len(),
        found
    );

    let missing: Vec<&String> = expected.difference(&found).collect();
    let extra: Vec<&String> = found.difference(&expected).collect();
    assert!(
        missing.is_empty() && extra.is_empty(),
        "IRInst does not match the emitted census.\n  missing arms: {missing:?}\n  unexpected arms: {extra:?}"
    );

    // The six pattern-position-only variants stay out. If the lowerer starts
    // constructing one, the census above changes and this is where it shows.
    for name in NOT_EMITTED {
        assert!(
            !found.contains(*name),
            "{name} is referenced but never CONSTRUCTED by the lowerer, so it must not be in \
             IRInst. If that changed, re-run the census and update both lists together."
        );
    }
}

/// The operator alphabets are complete against their Rust enums — the sub-
/// dispatches inside the `binop` / `unop` / `icmp` / `fcmp` / `cast` arms.
#[test]
fn eval_ir_operator_alphabets_are_complete() {
    let spec = build_eval_ir_spec_with_stack();
    for (name, want) in OPERATOR_ALPHABETS {
        let found = ctor_names(&spec, name);
        assert_eq!(
            found.len(),
            *want,
            "{name} must have {want} constructors to cover its Rust counterpart; found {}: {:?}",
            found.len(),
            found
        );
    }
}

/// GATE CLAUSE 2: the C2 vacuity firewall clears every `EvalIR` family.
///
/// This is the check that stops `EvalIR` from becoming the thing it exists to
/// replace. An execution semantics whose constructor fields could reach
/// `Typing` / `has_type` would let the crystal's equality theorem be discharged
/// by assuming the typing judgment it is supposed to be independent of — the
/// exact defect `KernelInferAccepts`'s `const` and `lam` arms have.
///
/// Held to `is_pristine` — no layer-2 contact at ANY polarity — rather than to
/// the polarity-aware `is_clean`. C2b's premise-only class explains a finding on
/// a relation that already has one; the `EvalIR` families are expected to have
/// none at all, and the first one arriving should be a decision, not a shrug.
#[test]
fn eval_ir_relations_pass_the_vacuity_firewall() {
    let spec = build_eval_ir_spec_with_stack();

    let mut dirty = Vec::new();
    for family in EVAL_IR_FAMILIES {
        assert!(
            env_knows(spec.env(), family),
            "{family} must be registered — the firewall silently audits nothing if the name is \
             absent, so a rename has to fail here rather than pass"
        );
        let report = audit_relation(&spec, family);
        if !report.is_pristine() {
            dirty.push(report.render());
        }
    }

    assert!(
        dirty.is_empty(),
        "the vacuity firewall rejected {} EvalIR family/families:\n{}",
        dirty.len(),
        dirty.join("\n")
    );
}

/// The witnesses are present and rest on nothing.
///
/// Empty transitive axiom closure by kernel ground truth: these are `Eq.refl`
/// proofs over reducible definitions, so anything in the closure would mean a
/// definition somewhere in the semantics is an axiom rather than a computation.
#[test]
fn eval_ir_witnesses_are_registered_and_axiom_free() {
    let spec = build_eval_ir_spec_with_stack();

    for name in WITNESSES {
        assert!(
            env_knows(spec.env(), name),
            "{name} must be registered by the EvalIR stage"
        );
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().map(|n| n.to_string()).collect();
        deps.sort();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY transitive axiom closure — it is a computation, not an \
             assumption. Found: {deps:?}"
        );
    }
}

/// The module the witnesses run is the one the crystal will pin, and it is a
/// single function so the width-one doctrine is visible in the artifact rather
/// than only in the prose.
#[test]
fn eval_ir_crystal_module_is_width_one() {
    let spec = build_eval_ir_spec_with_stack();
    for name in ["ir_lz_module", "ir_lz_func", "ir_tLevel"] {
        assert!(
            env_knows(spec.env(), name),
            "{name} must be registered — it is part of the crystal's worked example"
        );
    }
}
