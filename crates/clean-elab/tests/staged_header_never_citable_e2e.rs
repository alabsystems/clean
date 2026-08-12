// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! I1 — the BINDING INVARIANT: a staged header is never citable.
//!
//! Ruling of record: `docs/design/2026-08-05-i1-ruling-header-elaboration.md`
//! (Trust superproject). *"Provisional headers must live in a
//! non-authoritative staging environment, unreachable from citations,
//! `environment()`, PROOF authority and CALL."*
//!
//! A header is a name and a type with no value — to everything downstream,
//! indistinguishable from an axiom the user never wrote. If one could back a
//! kernel-certified proof, `theorem a : False := b` and `theorem b : False :=
//! a` would certify each other. So the tests here are about what is ABSENT and
//! what is REFUSED, not about what succeeds.
//!
//! Each positive has a control that must fail, because "nothing is citable" is
//! trivially satisfied by a checker that registers nothing:
//!
//!   1. `test_staged_header_is_absent_from_the_published_environment` — after
//!      the batch, no name is marked staged and every registered declaration
//!      has a VALUE. CONTROL: `test_the_same_batch_really_did_register` — the
//!      declarations are there, so absence is not vacuous.
//!   2. `test_a_proof_cycle_is_refused_and_registers_nothing` — the MUST-FAIL
//!      control for the whole scheme. Two theorems that cite each other must be
//!      REFUSED and neither may reach the environment. This is what a checker
//!      that let a header back a proof would accept, and it is the reason the
//!      staging environment exists at all.
//!   3. `test_an_honest_axiom_still_registers_and_is_disclosed` — proves (2) is
//!      about STAGING, not about axioms: an `axiom` the author actually wrote
//!      still registers, with a value-free `Axiom` kind that discloses it.

use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

struct Checked {
    env: Environment,
    committed: bool,
    rejections: String,
}

fn check(source: &str) -> Checked {
    let mut env = Environment::with_prelude();
    let mut file_ctx = clean_elab::FileContext::new();
    let decls = parse_file(source).expect("fixture must parse");
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let outcome = elaborate_module(&mut env, &mut file_ctx, &units, BatchOptions::islands());
    Checked {
        committed: outcome.committed,
        rejections: outcome.render_rejections(),
        env,
    }
}

/// A batch with a forward reference — `early` names `late`, which is declared
/// after it — so `late` really is staged as a header during checking.
const FORWARD_REFERENCE: &str = "\
set_option autoImplicit false
def early : Nat := late
def late : Nat := 7
";

/// Nothing that reaches the published environment is a provisional header, and
/// no declaration the batch registered is value-free.
#[test]
fn test_staged_header_is_absent_from_the_published_environment() {
    let checked = check(FORWARD_REFERENCE);
    assert!(
        checked.committed,
        "the fixture must commit for this test to say anything: {}",
        checked.rejections
    );
    assert!(
        !checked.env.has_staged_headers(),
        "the PUBLISHED environment reports staged headers {:?} — a provisional \
         signature escaped the staging environment, so a proof could rest on a \
         name-and-type the author never asserted",
        checked.env.staged_header_names()
    );
    for name in ["early", "late"] {
        let name = Name::from_string(name);
        let info = checked
            .env
            .get_const(&name)
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        assert!(
            info.value.is_some(),
            "`{name}` is in the environment with NO VALUE — that is a staged \
             header, not a definition. It is citable, and it asserts its type \
             without proving it."
        );
    }
}

/// CONTROL for (1): absence is not vacuous — the batch really did register both
/// declarations, and `early` really did resolve the forward reference.
#[test]
fn test_the_same_batch_really_did_register() {
    let checked = check(FORWARD_REFERENCE);
    assert!(
        checked.committed,
        "REJECTED a plain forward reference, which header-first checking exists \
         to accept: {}",
        checked.rejections
    );
    let early = checked
        .env
        .get_const(&Name::from_string("early"))
        .expect("`early` must be registered");
    let mut referenced = std::collections::HashSet::new();
    early
        .value
        .as_ref()
        .expect("`early` must have a value")
        .collect_constants_into(&mut referenced);
    assert!(
        referenced.contains(&Name::from_string("late")),
        "`early` does not mention `late` after elaboration — the forward \
         reference resolved to something else, so this fixture is not testing \
         what it claims to test. Referenced: {referenced:?}"
    );
}

/// THE MUST-FAIL CONTROL. Two theorems that cite each other prove nothing. If a
/// staged header could back a proof, this batch would be accepted, and `False`
/// would be certified.
#[test]
fn test_a_proof_cycle_is_refused_and_registers_nothing() {
    let checked = check(
        "\
set_option autoImplicit false
theorem a : False := b
theorem b : False := a
",
    );
    assert!(
        !checked.committed,
        "ACCEPTED a proof cycle. `a` is only as proved as `b`, and `b` only as \
         `a` — neither is proved. This is exactly what a staged header backing \
         a proof would allow, and it must be refused."
    );
    for name in ["a", "b"] {
        assert!(
            checked.env.get_const(&Name::from_string(name)).is_none(),
            "`{name}` reached the environment from a REFUSED batch"
        );
    }
    assert!(
        !checked.env.has_staged_headers(),
        "the refused batch left staged headers behind in the caller's \
         environment: {:?}",
        checked.env.staged_header_names()
    );
}

/// CONTROL for (3): the refusal above is about STAGING, not about axioms. An
/// `axiom` the author actually wrote still registers — value-free, kind
/// `Axiom`, and therefore disclosed by name in any certification closure that
/// reaches it.
#[test]
fn test_an_honest_axiom_still_registers_and_is_disclosed() {
    let checked = check(
        "\
set_option autoImplicit false
axiom chosen : Nat
def uses : Nat := chosen
",
    );
    assert!(
        checked.committed,
        "REJECTED an honest `axiom`. The staging refusal must be about \
         PROVISIONAL headers, not about assumptions the author wrote: {}",
        checked.rejections
    );
    let chosen = checked
        .env
        .get_const(&Name::from_string("chosen"))
        .expect("`chosen` must be registered");
    assert!(
        chosen.value.is_none(),
        "an `axiom` must stay value-free so it is visible as an assumption"
    );
    assert!(
        !checked.env.is_staged_header(&Name::from_string("chosen")),
        "an author-written `axiom` must NOT be marked as a staged header — \
         staging is a checker state, not a way of writing an assumption"
    );
}
