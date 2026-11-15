// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Lean 4.8 tactic/term forms from trust-ir's `lean/trust_ir-semantics`
//! that Clean failed to parser recovery — end to end (parse → elaborate →
//! kernel re-check) through the same `elaborate_decl_and_register` entry
//! `clean check` drives.
//!
//! Every positive row is accepted by the pinned Lean 4.8.0 and asserted free
//! of domain-specific axioms (`common::assert_axiom_free`; a row Lean reports
//! as depending on no axiom at all asserts that too, `assert_no_axioms`), and
//! every twin is a source Lean 4.8.0 REJECTS (checked with the toolchain as
//! an oracle), refused at the twin's own declaration and, where Clean's
//! wording is fixed by its error type, for the reason Lean gives. A row named
//! PINNED GAP is one Lean accepts and Clean refuses by name; a row named
//! PINNED DIVERGENCE is one Clean accepts and Lean refuses. Both flip loudly
//! the day the behavior changes. So a fix that over-accepts — `cases h : e` binding the wrong
//! equation, a dotted case tag selecting the wrong goal, a keyword
//! constructor pattern read as a catch-all binder, a marked simp rule that
//! names nothing — fails here, and a twin cannot pass because its
//! scaffolding broke.
//!
//! The rows live in `tactic_alt_syntax_e2e/tactic_forms.rs`,
//! `tactic_alt_syntax_e2e/term_forms.rs`,
//! `tactic_alt_syntax_e2e/annotated_targets.rs` (`generalize … at`, binding
//! `match` arms, field-less cases, goals behind an elimination) and
//! `tactic_alt_syntax_e2e/shadowing.rs` (the annotated target's equation
//! shadowing an older local), over the harness in
//! `tactic_alt_syntax_e2e/common.rs`; this file binds them into one test
//! binary.

// An integration-test crate ROOT resolves `mod` against `tests/`, not against a
// same-named directory, so each child module names its path explicitly.
#[path = "tactic_alt_syntax_e2e/annotated_targets.rs"]
mod annotated_targets;
#[path = "tactic_alt_syntax_e2e/common.rs"]
mod common;
#[path = "tactic_alt_syntax_e2e/shadowing.rs"]
mod shadowing;
#[path = "tactic_alt_syntax_e2e/tactic_forms.rs"]
mod tactic_forms;
#[path = "tactic_alt_syntax_e2e/term_forms.rs"]
mod term_forms;
