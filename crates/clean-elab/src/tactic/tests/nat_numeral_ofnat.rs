// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for RC-H / brick T2: the tactic layer's Nat-numeral reader
//! must recognize `@OfNat.ofNat α k inst`, the form the elaborator actually
//! builds for a source numeral.
//!
//! Three private copies of the reader used to exist —
//! `finite_cases::extract_nat_literal`, `interval_cases::expr_to_int` and
//! `ring_literals::nat_const_value` — each handling only `Nat.zero`, a
//! `Nat.succ` chain and a raw `Lit(Nat)`. All three now delegate to the single
//! shared `nat_expr_eval::read_nat_numeral`.
//!
//! Observed symptoms, each with a passing `Nat.succ`-spelled control:
//! `fin_cases h` on `h : Fin 3` → `InvalidTarget { detail: "not a recognized
//! finite type" }`; `interval_cases n` under `2 ≤ n ≤ 3` → `"no bounds found in
//! context"`; and `ring` reporting `Unknown("… OfNat.ofNat …")` on both sides of
//! `0 + x = x`.

use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};
use clean_parser::parse_file;

use crate::tactic::finite_cases::extract_nat_literal;
use crate::tactic::interval_cases::expr_to_int;
use crate::tactic::nat_expr_eval::read_nat_numeral;
use crate::tactic::ring_literals::nonnegative_ring_const_value;
use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};

// ---------------------------------------------------------------------------
// Builders for the numeral spellings the elaborator produces
// ---------------------------------------------------------------------------

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `@OfNat.ofNat Nat k (instOfNatNat k)` — a plain Nat source numeral.
fn ofnat_nat(k: u64) -> Expr {
    Expr::apps(
        c("OfNat.ofNat"),
        [
            c("Nat"),
            Expr::nat_lit(k),
            Expr::app(c("instOfNatNat"), Expr::nat_lit(k)),
        ],
    )
}

/// `@OfNat.ofNat α k inst` for an arbitrary type and instance — the numeral must
/// be read from the index, not the instance, so the `Zero.toOfNat0` /
/// `One.toOfNat1` bridges the elaborator picks under real imports also work.
fn ofnat_via(ty: &str, k: u64, inst: Expr) -> Expr {
    Expr::apps(c("OfNat.ofNat"), [c(ty), Expr::nat_lit(k), inst])
}

// ---------------------------------------------------------------------------
// The shared reader
// ---------------------------------------------------------------------------

#[test]
fn test_read_nat_numeral_reads_the_ofnat_app_form() {
    for k in [0_u64, 1, 2, 3, 42] {
        assert_eq!(
            read_nat_numeral(&ofnat_nat(k)),
            Some(k),
            "@OfNat.ofNat Nat {k} (instOfNatNat {k}) must read as {k}"
        );
    }
}

#[test]
fn test_read_nat_numeral_is_independent_of_the_ofnat_instance() {
    // `(0 : α)` under real imports elaborates through `Zero.toOfNat0`, not
    // `instOfNatNat` — the index is still the numeral.
    assert_eq!(
        read_nat_numeral(&ofnat_via(
            "Int",
            0,
            Expr::app(c("Zero.toOfNat0"), c("instZeroInt"))
        )),
        Some(0)
    );
    assert_eq!(
        read_nat_numeral(&ofnat_via(
            "Int",
            1,
            Expr::app(c("One.toOfNat1"), c("instOneInt"))
        )),
        Some(1)
    );
    assert_eq!(
        read_nat_numeral(&ofnat_via("Nat", 7, c("someUnknownInstance"))),
        Some(7)
    );
}

#[test]
fn test_read_nat_numeral_reads_the_delta_reduced_projection_form() {
    // `OfNat.ofNat`'s value is `fun {α n} [inst] => inst.1`, so a partially
    // reduced numeral can surface as `Proj("OfNat", 0, inst)`.
    let proj_inst_of_nat_nat = Expr::proj(
        Name::from_string("OfNat"),
        0,
        Expr::app(c("instOfNatNat"), Expr::nat_lit(5)),
    );
    assert_eq!(read_nat_numeral(&proj_inst_of_nat_nat), Some(5));

    let proj_zero = Expr::proj(
        Name::from_string("OfNat"),
        0,
        Expr::app(c("Zero.toOfNat0"), c("instZeroInt")),
    );
    assert_eq!(read_nat_numeral(&proj_zero), Some(0));

    let proj_one = Expr::proj(
        Name::from_string("OfNat"),
        0,
        Expr::app(c("One.toOfNat1"), c("instOneInt")),
    );
    assert_eq!(read_nat_numeral(&proj_one), Some(1));
}

#[test]
fn test_read_nat_numeral_still_reads_the_legacy_spellings() {
    assert_eq!(read_nat_numeral(&c("Nat.zero")), Some(0));
    assert_eq!(read_nat_numeral(&c("Nat.one")), Some(1));
    assert_eq!(read_nat_numeral(&Expr::nat_lit(9)), Some(9));
    let succ_succ_zero = Expr::app(c("Nat.succ"), Expr::app(c("Nat.succ"), c("Nat.zero")));
    assert_eq!(read_nat_numeral(&succ_succ_zero), Some(2));
    // A `Nat.succ` over an OfNat numeral is the mixed spelling.
    assert_eq!(
        read_nat_numeral(&Expr::app(c("Nat.succ"), ofnat_nat(3))),
        Some(4)
    );
}

#[test]
fn test_read_nat_numeral_rejects_symbolic_and_malformed_input() {
    // Symbolic numeral index.
    assert_eq!(
        read_nat_numeral(&ofnat_via("Nat", 0, c("inst")).clone()),
        Some(0),
        "sanity: the well-formed case reads"
    );
    let symbolic_index = Expr::apps(
        c("OfNat.ofNat"),
        [c("Nat"), Expr::fvar(clean_kernel::FVarId::new(0)), c("i")],
    );
    assert_eq!(read_nat_numeral(&symbolic_index), None);
    // Not a numeral at all.
    assert_eq!(read_nat_numeral(&c("Foo.bar")), None);
    assert_eq!(read_nat_numeral(&Expr::bvar(0)), None);
    assert_eq!(read_nat_numeral(&Expr::prop()), None);
    // A projection of a different structure.
    assert_eq!(
        read_nat_numeral(&Expr::proj(Name::from_string("Prod"), 0, c("p"))),
        None
    );
    // A projection of an OfNat instance whose field-0 value is not fixed.
    assert_eq!(
        read_nat_numeral(&Expr::proj(
            Name::from_string("OfNat"),
            0,
            c("mysteryInstance")
        )),
        None
    );
}

// ---------------------------------------------------------------------------
// All three call sites see the same form
// ---------------------------------------------------------------------------

#[test]
fn test_fin_cases_reader_sees_the_ofnat_bound() {
    assert_eq!(extract_nat_literal(&ofnat_nat(3)), Some(3));
    // Control: the spelling that already worked.
    let succ3 = Expr::app(
        c("Nat.succ"),
        Expr::app(c("Nat.succ"), Expr::app(c("Nat.succ"), c("Nat.zero"))),
    );
    assert_eq!(extract_nat_literal(&succ3), Some(3));
}

#[test]
fn test_interval_cases_reader_sees_the_ofnat_bound() {
    assert_eq!(expr_to_int(&ofnat_nat(2)), Some(2));
    assert_eq!(expr_to_int(&ofnat_nat(3)), Some(3));
    // Control: the spelling that already worked.
    assert_eq!(
        expr_to_int(&Expr::app(c("Nat.succ"), c("Nat.zero"))),
        Some(1)
    );
}

#[test]
fn test_ring_literal_reader_sees_the_ofnat_numeral() {
    assert_eq!(nonnegative_ring_const_value(&ofnat_nat(0)), Some(0));
    assert_eq!(nonnegative_ring_const_value(&ofnat_nat(1)), Some(1));
    assert_eq!(nonnegative_ring_const_value(&ofnat_nat(12)), Some(12));
    // Int spellings are unchanged.
    assert_eq!(nonnegative_ring_const_value(&c("Int.zero")), Some(0));
    assert_eq!(
        nonnegative_ring_const_value(&Expr::app(c("Int.ofNat"), ofnat_nat(4))),
        Some(4)
    );
    // Non-constants stay symbolic.
    assert_eq!(nonnegative_ring_const_value(&c("Foo.bar")), None);
}

// ---------------------------------------------------------------------------
// End-to-end: the tactics the reader unblocks
// ---------------------------------------------------------------------------

/// Elaborate every declaration in `code` against one fresh prelude env, and
/// return the results. `Ok` means the kernel accepted the proof term.
fn elab_all(code: &str) -> Vec<Result<ElabResult, crate::ElabError>> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect()
}

#[track_caller]
fn assert_all_closed(code: &str, what: &str) {
    let results = elab_all(code);
    assert!(!results.is_empty(), "{what}: nothing parsed");
    for result in &results {
        assert!(
            matches!(result, Ok(ElabResult::Theorem { .. })),
            "{what}: expected a kernel-registered theorem, got {result:?}"
        );
    }
}

#[test]
fn test_fin_cases_splits_a_source_numeral_fin_bound() {
    assert_all_closed(
        "theorem fc (h : Fin 3) : True := by\n  fin_cases h\n  trivial\n  trivial\n  trivial\n",
        "fin_cases on `Fin 3`",
    );
}

#[test]
fn test_ring_folds_source_numeral_identities() {
    assert_all_closed(
        "theorem rz (x : Nat) : 0 + x = x := by ring\n",
        "ring on `0 + x = x`",
    );
    assert_all_closed(
        "theorem ro (x : Nat) : 1 * x = x := by ring\n",
        "ring on `1 * x = x`",
    );
    assert_all_closed(
        "theorem raz (x : Nat) : x + 0 = x := by ring\n",
        "ring on `x + 0 = x`",
    );
    assert_all_closed(
        "theorem rmo (x : Nat) : x * 1 = x := by ring\n",
        "ring on `x * 1 = x`",
    );
}

#[test]
fn test_ring_still_rejects_a_false_numeral_identity() {
    let results = elab_all("theorem bad (x : Nat) : 1 + x = x := by ring\n");
    assert!(
        !matches!(results.first(), Some(Ok(ElabResult::Theorem { .. }))),
        "`1 + x = x` must not be provable by ring: {results:?}"
    );
}
