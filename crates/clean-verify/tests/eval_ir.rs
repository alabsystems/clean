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
//! **The census recipe this doc used to give was measurably wrong, and is
//! replaced rather than repeated.** It read: `grep -roh "Inst::[A-Za-z0-9_]*"`
//! over `crates/trust-thir-lower/src`, "34 variants are referenced; six of them
//! occur only in pattern position". Run it: the recipe yields **61** distinct
//! tokens, not 34; `Inst::InsertElement` is CONSTRUCTED at eight production
//! sites in that crate's `lib.rs` while `insertelement` sat in `NOT_EMITTED`
//! under a comment promising this test would notice; and it scanned only ONE of
//! the two producers of the executed bundle.
//!
//! The denominator is now DERIVED, from two in-tree sources that must agree —
//! the `IRInst` inductive in `eval_ir_syntax.rs` and `EMITTED_INSTS` in
//! `eval_ir/census.rs` (`scripts/evalir_coverage.py::derive_denominator`) — and
//! it is **33**: the former 30 plus ByteV1's distinct U64 and Usize sequential
//! atomic fetch-adds and retained Release. Release is explicitly unmodelled in
//! each execution layer; syntax growth is not measured agreement coverage.
//! Which names are genuinely constructed by the two production producers,
//! and which constructed names are NOT modelled, is what
//! B2C will publish, by minting `data/irinst_producer_census.json` from a
//! parse-based two-producer scan (`scripts/irinst_producer_census.py`). Neither
//! exists yet: until they are minted, quote no fraction of the full `Inst` enum
//! from here, and read the denominator as exactly what `derive_denominator`
//! derives — the modelled set — and not as a claim about the constructed set.
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

// Phase B's return-slot stage — registration and axiom-closure gate. Split out
// rather than inlined for the reason recorded above: this file sits at the
// 500-line convention and the slot lemmas are their own clause.
#[path = "eval_ir/slot_lemmas.rs"]
mod slot_lemmas;

// GATE CLAUSE 5 (plan W5, 2026-08-25) — the adequacy grid: every field of
// every IRInst constructor classified (read / proved-dropped / erased /
// declared-delta), re-derived from the registered syntax and dispatch and
// held against data/evalir_adequacy_grid.json. Spec-free by design.
#[path = "eval_ir/adequacy_grid.rs"]
mod adequacy_grid;

// The ir_lzc chain's declaration census (Phase A: both functions minted, the
// programme's first global). Split out for the same reason the census lists
// above were: with it inline this file stood at 513 lines against the 500-line
// convention. It asserts the ir_lzb census too, so the two sit in one test.
#[path = "eval_ir/lzc_census.rs"]
mod lzc_census;

// The ir_lzd chain's EvalIr-half census, split out for the same reason.
#[path = "eval_ir/lzd_census.rs"]
mod lzd_census;

// Every coverage claim the EvalIR syntax registers against a trust_ir enum,
// and every constructor count of the six operator alphabets, held against the
// enum through exhaustive matches; so is every variant count these sources
// restate in prose.
#[path = "eval_ir/trust_ir_parity.rs"]
mod trust_ir_parity;

// Crystal E5 (decision memo §23): the wide-pointer kinds, typed metadata, the vtable image and
// the refused wide `icmp`, held to trust-ir's reference interpreter on real m0off slices.
#[path = "eval_ir/e5_fat_images.rs"]
mod e5_fat_images;

use std::collections::BTreeSet;

use census::{ctor_names, EMITTED_INSTS, EVAL_IR_FAMILIES, NOT_EMITTED, WITNESSES};
use clean_kernel::Name;
use clean_verify::test_utils::build_eval_ir_spec_with_stack;
use clean_verify::vacuity_firewall::{audit_relation, env_knows};

/// GATE CLAUSE 3, and the load-bearing test in this file.
///
/// The seven `is_zero` executions are `Eq.refl` definitions registered by the
/// stage, so the stage building at all means the kernel *ran the machine* on
/// each input and found the stated outcome. Nothing here is asserted by hand:
/// if any arm of the `IRInst` dispatch were wrong for those inputs, or the
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

/// Exact representable syntax, not successful-execution coverage.
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
        EMITTED_INSTS.len(),
        "IRInst must have exactly one constructor per EMITTED_INSTS row (the derived \
         representable syntax census, {} names); found {}: {:?}",
        EMITTED_INSTS.len(),
        found.len(),
        found
    );

    let missing: Vec<&String> = expected.difference(&found).collect();
    let extra: Vec<&String> = found.difference(&expected).collect();
    assert!(
        missing.is_empty() && extra.is_empty(),
        "IRInst does not match the emitted census.\n  missing arms: {missing:?}\n  unexpected arms: {extra:?}"
    );

    // These variants have NO syntactic image in IRInst. This is a syntax
    // boundary, not a claim that nobody constructs them — two of them are
    // constructed in production today, which is why the honest account will be
    // data/irinst_producer_census.json's `unmodelled_constructed` list (B2C
    // mints it; it does not exist yet) rather than a comment here.
    for name in NOT_EMITTED {
        assert!(
            !found.contains(*name),
            "{name} has NO syntax image in this profile, so it must not be in IRInst. Adding a \
             constructor for it means moving it out of NOT_EMITTED, into EMITTED_INSTS, and re-deriving \
             every artifact that restates the census."
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
        "int_",
        "bool_",
        "unit_",
        "null_",
        "undef_",
        "float_",
        "func_",
        "aggv",
        "vnil",
        "vcons",
        // phantomdata (2026-09-16): trust_ir::Constant::PhantomData, the
        // zero-sized marker. Added because `tick_heartbeat` emits
        // `const () phantomdata` and reader A refuses a body it has no image
        // for; kept SEPARATE from `unit_` because the producer keeps it
        // separate and the emitted text prints it by its own name.
        "phantomdata",
    ]
    .iter()
    .map(|s| (*s).to_string())
    .collect();
    assert_eq!(
        found, expected,
        "IRConst must be exactly the seven scalar constants, the three inline-spine \
         constructors that model trust_ir::Constant::Aggregate, and the zero-sized \
         `phantomdata` marker; found {found:?}"
    );
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
        "ir_nat_sub_ltb",
        "ir_nat_sub_eqb",
        "ir_nat_sub_ltb_walk_eq",
        "ir_nat_sub_eqb_walk_eq",
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
        // `axiom_deps` deliberately FILTERS OUT the foundational axioms
        // (clean-kernel/src/env/axiom_audit.rs), so on its own it would let a
        // new dependency on Classical.choice through this assertion unnoticed.
        // The claim here is a literally EMPTY closure -- both halves.
        let deps = spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        let foundational = spec
            .env()
            .foundational_axiom_deps(&Name::from_string(name))
            .unwrap_or_default();
        assert!(
            foundational.is_empty(),
            "{name} must reach NO foundational axiom either; found {:?}",
            foundational
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
        );
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

/// Both `Level::is_zero` modules are registered and both are single functions,
/// so the width-one doctrine is visible in the artifact rather than only in
/// the prose: `ir_lzm_module` is the hand SEMANTIC MODEL the A4/A5 theorems
/// are about, `ir_lz_module` is the MINTED emitted body (2026-08-22) over
/// which A4 is refuted — see `eval_ir_level_minted.rs`.
#[test]
fn eval_ir_crystal_module_is_width_one() {
    let spec = build_eval_ir_spec_with_stack();
    for name in [
        "ir_lzm_module",
        "ir_lzm_func",
        "ir_tLevel",
        "ir_lz_module",
        "ir_lz_func",
        "ir_lz_tlevel",
        "ir_lz_on_max_stuck",
    ] {
        assert!(
            env_knows(spec.env(), name),
            "{name} must be registered — it is part of the crystal's worked example"
        );
    }
}

/// **The `ir_lzb` declaration count, MINTED rather than typed.**
///
/// `docs/CRYSTAL_STATUS.md` and the decision memo have said since 2026-08-26
/// that link 4 for the designated target closed over "59 declarations,
/// kernel-checked through the registered stages". The 2026-09-07 crystal audit
/// found that figure is prose-only and matches no static count of the three
/// `eval_ir_lzb*.rs` files — the standing rule it violates is *no claim-bearing
/// value is typed where a producer exists*.
///
/// This is the producer for the EvalIr-bundle half: the module, its witnesses,
/// the ten frame lemmas and the three segment lemmas. Every name registered by
/// those stages begins `ir_lzb`, so the count is exact and a lemma added or
/// deleted moves it. The Full-only half — `EncodesLevelArcF`,
/// `EncodesLiveLevelRefF`, `ir_lzb_cost` and A4/A5 — is not in this bundle and
/// is not counted here; the two are stated separately rather than added into
/// one number nobody can check.
///
/// The number is not a target. It is here so the docs can quote something a
/// command re-derives.
#[test]
fn eval_ir_lzb_declaration_census_is_pinned() {
    let spec = build_eval_ir_spec_with_stack();
    let names: BTreeSet<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_lzb"))
        .collect();
    assert_eq!(
        names.len(),
        30,
        "the EvalIr bundle's `ir_lzb` declarations moved. This count is what \
         docs/CRYSTAL_STATUS.md and designs/2026-08-22-is-zero-model-vs-minted-decision.md \
         quote for the module + steps + activation stages; update both with the new \
         number rather than the assertion. Registered: {names:?}"
    );
    for required in [
        "ir_lzb_module",
        "ir_lzb_deref",
        "ir_lzb_func0_is_minted",
        "ir_lzb_deref_activation",
        "ir_lzb_max_true_seg",
        "ir_lzb_max_false_seg",
        "ir_lzb_imax_seg",
        "ir_lzb_cost_halts_max",
        "ir_lzb_cost_halts_imax",
    ] {
        assert!(
            names.contains(required),
            "{required} must be registered by the EvalIr bundle"
        );
    }
}
