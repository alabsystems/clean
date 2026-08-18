// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` acceptance gate (crystal job **C3**).
//!
//! C3's gate has four clauses, and there is one test here per clause:
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
//!
//! Clause 4 lives in [`prelude_composition`]: the same stage must also build in
//! Clean's Lean-4 production prelude, which is a *different* environment with a
//! different `Eq` and none of the spec foundation's arithmetic lemmas. That
//! clause exists because the builder for it was broken for four commits behind
//! an honestly-green gate list that never constructed it — read the module doc
//! there before adding a declaration to the stage.

// The pinned censuses and the constructor-name reader, split out on
// 2026-08-16: adding gate clause 4 below took this file to 507 lines against a
// 500-line convention, and the census lists are the half that is data rather
// than the half that is a gate.
#[path = "eval_ir/census.rs"]
mod census;

// GATE CLAUSE 4 — the composition boundary. Read its module doc before adding a
// declaration to the EvalIR stage.
#[path = "eval_ir/prelude_composition.rs"]
mod prelude_composition;

use std::collections::BTreeSet;

use census::{
    ctor_names, EMITTED_INSTS, EVAL_IR_FAMILIES, NOT_EMITTED, OPERATOR_ALPHABETS, WITNESSES,
};
use clean_kernel::Name;
use clean_verify::test_utils::build_eval_ir_spec_with_stack;
use clean_verify::vacuity_firewall::{audit_relation, env_knows};

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

/// The `IRConst` census, pinned by name.
///
/// It was SEVEN until `mode::CleanMode::from_source_system` — whose every arm
/// emits `const enum.13 { k }`, i.e. `trust_ir::Constant::Aggregate` — was
/// chained. The aggregate form is carried as an inline element spine
/// (`aggv`/`vnil`/`vcons`) for the same measured reason `IRScalar`'s payload is:
/// a structural `IRList IRConst` field is a NESTED inductive and the elaborator
/// does not register one.
///
/// The count is asserted so that adding a constructor is a deliberate act with
/// a matching evaluation case, not a drift — `ir_const_value` is an
/// `IRConst.rec`, so a new constructor without a minor does not compile, but a
/// new constructor with a *stub* minor would, and this is where that shows.
#[test]
fn eval_ir_const_census_is_pinned() {
    let spec = build_eval_ir_spec_with_stack();
    let found = ctor_names(&spec, "IRConst");
    let expected: BTreeSet<String> = [
        "int_", "bool_", "unit_", "null_", "undef_", "float_", "func_", "aggv", "vnil", "vcons",
    ]
    .iter()
    .map(|s| (*s).to_string())
    .collect();
    assert_eq!(
        found, expected,
        "IRConst must be exactly the seven scalar constants plus the three inline-spine \
         constructors that model trust_ir::Constant::Aggregate; found {found:?}"
    );
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

/// **The folding lemmas, gated where they can regress.**
///
/// Two clauses, because each lemma has two halves and only one of them is a
/// proposition:
///
/// 1. The proved half — the three agreement theorems (`ir_nat_ltb_walk_eq`,
///    `ir_nat_eqb_walk_eq`, `ir_nat_leb_walk_eq`: the subtraction tests the
///    machine runs ARE the paired unary walks, at every pair of arguments),
///    plus the seven restatements that put the walk back into the statement of
///    what runs — `ir_div_go_guard` for the division loop and
///    `ir_icmp_{ult,ugt,ule,uge,eq,ne}_walk` for the six integer `icmp` arms.
///    Registered, and resting on nothing. If someone deletes a theorem and
///    keeps the fast comparison, the swap becomes an assertion and this fails.
/// 2. The half no theorem can state — that the kernel FOLDS a comparison of
///    literals instead of walking it. That is a reduction-cost fact, so it is
///    held by a clock, over the exact terms that used to be the wall:
///    `ir_wrap 32 (ir_wrap 32 4294967295)`, the `expr_bvar_in_range` sentinel
///    residue extrapolated at ~9.6 days and never once measured;
///    `ir_wrap 64 (ir_wrap 64 57343)`, `is_valid_char`'s left-constant `icmp`
///    residue, measured at 24.973 s before the wrap lemma and 0.010 s after;
///    and now the two COMPARISONS themselves — the u32 sentinel equality
///    (4.29e9 walk steps) and the `0xD800 < 0x110000` less-than that cost
///    19–210 s inside a concrete `ir_eval`.
///
/// The bound is 30 s for all six declarations TOGETHER — three orders of
/// magnitude above what they measure and still far below the single 24.973 s
/// the smallest of them used to cost, so it cannot go green on a regression and
/// cannot go red on a loaded box.
#[test]
fn eval_ir_wrap_folds_a_literal_residue_without_walking_it() {
    let mut spec = build_eval_ir_spec_with_stack();

    for name in [
        "ir_nat_pos",
        "ir_nat_iszero",
        "ir_nat_ltb_walk",
        "ir_nat_eqb_walk",
        "ir_nat_leb_walk",
        "ir_nat_ltb_walk_eq",
        "ir_nat_eqb_walk_eq",
        "ir_nat_leb_walk_eq",
        "ir_div_go_guard",
        "ir_icmp_ult_walk",
        "ir_icmp_ugt_walk",
        "ir_icmp_ule_walk",
        "ir_icmp_uge_walk",
        "ir_icmp_eq_walk",
        "ir_icmp_ne_walk",
    ] {
        assert!(
            env_knows(spec.env(), name),
            "{name} must be registered — without it the folded comparison is an assertion \
             rather than a theorem"
        );
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY transitive axiom closure; found {:?}",
            deps.iter().map(ToString::to_string).collect::<Vec<_>>()
        );
    }

    // Each of these is `Eq.refl`: the kernel has to produce the residue as a
    // literal, or decide the comparison, to accept it. The values are the
    // answers themselves, so a guard that folded to the WRONG one fails here
    // too, not just a slow one.
    let residues: &[(&str, &str)] = &[
        (
            "u32 sentinel, twice wrapped",
            "def l2_gate_u32_sentinel : Eq Nat (ir_wrap 32 (ir_wrap 32 4294967295)) 4294967295 := Eq.refl Nat 4294967295",
        ),
        (
            "is_valid_char's left-constant icmp residue",
            "def l2_gate_vc_c2 : Eq Nat (ir_wrap 64 (ir_wrap 64 57343)) 57343 := Eq.refl Nat 57343",
        ),
        (
            "the 0x110000 bound is_valid_char's bb4 materializes",
            "def l2_gate_vc_c3 : Eq Nat (ir_wrap 64 (ir_wrap 64 1114112)) 1114112 := Eq.refl Nat 1114112",
        ),
        (
            "a NON-zero quotient still reduces to the right residue",
            "def l2_gate_quotient : Eq Nat (ir_wrap 8 55296) Nat.zero := Eq.refl Nat Nat.zero",
        ),
        (
            "the u32 sentinel EQUALITY — 4.29e9 paired walk steps",
            "def l2_gate_eqb_sentinel : Eq Bool (ir_nat_eqb (ir_wrap 32 (ir_wrap 32 4294967295)) (ir_wrap 32 4294967295)) Bool.true := Eq.refl Bool Bool.true",
        ),
        (
            "is_valid_char's widest comparison — 0x110000 peels on the argument",
            "def l2_gate_ltb_vc_c3 : Eq Bool (ir_nat_ltb (ir_wrap 64 1114112) (ir_wrap 64 (ir_wrap 64 1114112))) Bool.false := Eq.refl Bool Bool.false",
        ),
    ];

    let started = std::time::Instant::now();
    for (what, source) in residues {
        spec.add_recursive_def(source, "eval_ir gate: the folding lemmas, clocked")
            .unwrap_or_else(|e| panic!("{what}: the term must fold to its literal: {e}"));
    }
    let elapsed = started.elapsed().as_secs_f64();
    assert!(
        elapsed < 30.0,
        "the six terms took {elapsed:.3}s. They fold through ir_nat_ltb / ir_nat_eqb, which \
         cost one native BigNat subtraction each; comparisons that walk their operands unary \
         again put the u32 ones at days, not seconds."
    );
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
