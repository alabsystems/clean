// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **M11 — the three operands the dispatch drops, PROVED inert.**
//!
//! A blind slot that stays an erasure owes a justification, and
//! `data/crystal_mint_blind_slots.json` sets the standard: a kernel-checked
//! theorem or a measured fact, never a comment. The standard-bearer is
//! `ir_ty_is_agg_enum_any`, which proves `ir_ty_is_agg (IRTy.enum_ n)` is
//! `Bool.true` at EVERY whole-crate id and is therefore why a type-table
//! renumbering cannot reach the value the machine computes.
//!
//! Three rows needed the same treatment and had a comment instead:
//!
//! * **`switch-exhaustive-flag`.** `eval_ir_machine`'s dispatch reads
//!   `IRInst.switch v dflt dargs cases exh => ir_switch_exec m s (ir_getd s v)
//!   dflt dargs cases` — the flag is not passed on. Every statement that "no
//!   theorem moved when the transcription's `Bool.true` was corrected to the
//!   measured `false`" rested on reading that line.
//! * **`cc-and-linkage`.** `eval_ir_syntax.rs` keeps `CallIndirect`'s
//!   convention explicitly so that "an adequacy theorem has something to
//!   quantify over". Nothing quantified over it.
//! * **`functy-index`.** The signature-table index the header carries is the
//!   same table `callindirect`'s `sig` operand indexes, and the dispatch drops
//!   that too.
//!
//! These are those theorems, and they are quantified over EVERY module, state,
//! selector, default, argument list and case list rather than over the values
//! that happened to be measured. Each is `Eq.refl`: the kernel iota-reduces the
//! match on the constructor, so the dropped operand never appears in the
//! answer.
//!
//! ## What this does and does not settle for the exhaustive flag
//!
//! It settles that the flag's value is a **lineage** fact — about which module
//! the compiler emitted — and provably not a fact about what that module
//! computes. It does NOT give the slot a second witness: trust-ir's `Display`
//! still never prints it, so reader B still writes `?`, and the artifact binary
//! is still the only thing in this repo that knows the value. Closing that
//! needs a producer change. The decision and its reasons are recorded on the
//! row itself, under `the_decision_2026_08_20`.

use clean_kernel::Name;
use clean_verify::spec::{AxiomCategory, Specification};
use clean_verify::test_utils::build_eval_ir_spec_with_stack;

const INERT: [&str; 3] = [
    "ir_exec_switch_exh_irrelevant",
    "ir_exec_callind_conv_irrelevant",
    "ir_exec_callind_sig_irrelevant",
];

/// The lemma these three are held to the standard of.
///
/// `ir_ty_is_agg_enum_any` is the registered precedent for "an erasure
/// justified by a kernel-checked theorem instead of a comment", so the three
/// new ones are asserted to carry EXACTLY its classification rather than a
/// status named here. Naming a status here would let the two drift: if the
/// EvalIR stage's promotion pipeline changes, the standard-bearer and the
/// three move together or this test fails.
const STANDARD_BEARER: &str = "ir_ty_is_agg_enum_any";

fn assert_kernel_checked_like_the_standard(spec: &Specification, name: &str) {
    let bearer = spec
        .definitions()
        .get(STANDARD_BEARER)
        .expect("the standard-bearing lemma must be registered");
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} must be registered in the EvalIR specification"));

    // KERNEL-CHECKED. Registration goes through `elaborate_decl_and_register`,
    // which type-checks the declaration against the environment — so a
    // `def … : Eq IRConfig lhs rhs := Eq.refl IRConfig …` whose two sides were
    // NOT definitionally equal would fail to elaborate and the whole EvalIR
    // specification would fail to build. That the constant is in the
    // environment at all is the check.
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_some(),
        "{name} is not a constant of the EvalIR specification environment"
    );
    assert!(!def.is_axiom, "{name} must not be an axiom");
    assert!(
        def.elaborated_value.is_some(),
        "{name} has no proof term — a `Declaration::Theorem` wrapping an axiom is a restatement, \
         not a proof"
    );
    assert_eq!(def.category, AxiomCategory::DerivedLemma, "{name} category");
    assert_eq!(
        def.proof_status, bearer.proof_status,
        "{name} is not classified as `{STANDARD_BEARER}` is. The blind-slot list holds an \
         erasure to that lemma's standard, so the two must not drift apart."
    );
    assert!(
        def.axiom_deps.is_empty(),
        "{name} must have ZERO axiom_deps, found {:?}. An inertness claim resting on a \
         domain-specific axiom would justify an erasure with an assumption.",
        def.axiom_deps
    );
}

#[test]
fn m11_the_dropped_operands_are_kernel_checked_inert() {
    let spec = build_eval_ir_spec_with_stack();
    for name in INERT {
        assert_kernel_checked_like_the_standard(&spec, name);
    }
    // NON-VACUITY: the standard-bearer itself is zero-axiom, so "the same as
    // the standard-bearer" is not "the same as something unchecked".
    let bearer = spec.definitions().get(STANDARD_BEARER).expect("registered");
    assert!(!bearer.is_axiom && bearer.axiom_deps.is_empty());
}

/// A statement the kernel could NOT have checked must fail to elaborate.
///
/// Without this the three theorems above are consistent with a registration
/// path that accepts any `Eq.refl` it is handed. Here the same shape is built
/// over two operands the dispatch DOES read — a `switch`'s two different
/// DEFAULT targets — and the specification stage must refuse it.
#[test]
fn m11_the_same_shape_over_an_operand_the_machine_reads_is_refused() {
    let bogus = concat!(
        "def ir_exec_switch_default_irrelevant_FALSE (m : IRModule) (v : Nat) (d1 : Nat) ",
        "(d2 : Nat) (dargs : IRList Nat) (cases : IRList IRSwitchCase) (rs : IRList Nat) ",
        "(s : IRMachine) : Eq IRConfig ",
        "(ir_exec m (IRInst.switch v d1 dargs cases Bool.false) rs s) ",
        "(ir_exec m (IRInst.switch v d2 dargs cases Bool.false) rs s) := ",
        "Eq.refl IRConfig (ir_switch_exec m s (ir_getd s v) d1 dargs cases)",
    );
    let mut spec = build_eval_ir_spec_with_stack();
    let e = spec
        .add_recursive_def(bogus, "a FALSE inertness claim, for falsification")
        .err();
    assert!(
        e.is_some(),
        "the specification accepted an inertness claim about the switch DEFAULT, which the \
         dispatch does pass on. If this is accepted, `m11`'s three theorems establish nothing."
    );
}

/// The theorems must be about `ir_exec` — the dispatch the machine actually
/// runs — and must differ in the operand they quantify over.
///
/// Without this a passing `m11` would be consistent with three vacuous
/// `Eq.refl`s about something else entirely.
#[test]
fn m11_the_statements_are_about_the_real_dispatch() {
    let src = std::fs::read_to_string(
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("src/spec/core_spec/eval_ir_machine.rs"),
    )
    .expect("the dispatch source must be readable");

    // The dispatch really does drop all three, so the theorems are about a
    // dispatch that ignores them rather than about a hypothetical one.
    assert!(
        src.contains(
            "| IRInst.switch v dflt dargs cases exh => ir_switch_exec m s (ir_getd s v) dflt \
             dargs cases"
        ),
        "the switch arm no longer drops `exh`; if it now dispatches on the flag, \
         `ir_exec_switch_exh_irrelevant` is FALSE and must have failed to elaborate — check why \
         it did not"
    );
    assert!(
        src.contains(
            "| IRInst.callindirect cid sig args cc => ir_callind_exec m s rs (ir_getd s cid) args"
        ),
        "the callindirect arm no longer drops `sig` and `cc`"
    );

    for (name, lhs, rhs) in [
        (
            "ir_exec_switch_exh_irrelevant",
            "IRInst.switch v dflt dargs cases Bool.true",
            "IRInst.switch v dflt dargs cases Bool.false",
        ),
        (
            "ir_exec_callind_conv_irrelevant",
            "IRInst.callindirect cid sig args cc1",
            "IRInst.callindirect cid sig args cc2",
        ),
        (
            "ir_exec_callind_sig_irrelevant",
            "IRInst.callindirect cid g1 args cc",
            "IRInst.callindirect cid g2 args cc",
        ),
    ] {
        assert!(
            src.contains(name),
            "{name} is not stated in eval_ir_machine.rs"
        );
        assert!(
            src.contains(lhs) && src.contains(rhs),
            "{name} must equate `ir_exec` at `{lhs}` with `ir_exec` at `{rhs}`; if the two sides \
             are not two DIFFERENT operand values the theorem is `x = x` and proves nothing"
        );
    }
}

/// **`functy-index`, the structural half.** The registered `IRFunc` carries no
/// type, so a signature index has no slot in the fragment to occupy.
///
/// Checked against the live inductive rather than asserted, because that is the
/// difference between a justification and a comment.
#[test]
fn m11_the_registered_irfunc_carries_no_type() {
    let src = std::fs::read_to_string(
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("src/spec/core_spec/eval_ir_syntax.rs"),
    )
    .expect("the syntax source must be readable");
    let decl = src
        .lines()
        .find(|l| {
            l.trim_start()
                .starts_with("| mk : Nat → IRList Nat → Nat → IRList IRBlock")
        })
        .expect(
            "the IRFunc constructor must still be `mk : Nat → IRList Nat → Nat → IRList IRBlock \
             → IRFunc`; if its shape changed, the `functy-index` row's structural justification \
             has to be re-derived",
        );
    assert!(
        !decl.contains("IRTy"),
        "IRFunc gained a type field: the `functy-index` erasure is no longer structural and the \
         row must be restated:\n{decl}"
    );
}
