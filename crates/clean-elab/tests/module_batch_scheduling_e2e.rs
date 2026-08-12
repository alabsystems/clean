// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! I1 — scheduling: what header-first checking can now SEE, and what it must
//! still refuse.
//!
//! Ruling of record: `docs/design/2026-08-05-i1-ruling-header-elaboration.md`
//! (Trust superproject). Exposing the dependency structure is one of the things
//! header-first buys that retry cannot — retry sees "no progress" and cannot
//! tell "these need each other's headers" from "these are viciously circular".
//! But *"it does not automatically legalize it"*: the cycle fixtures must stay
//! rejected.
//!
//! Every refusal here is paired with a control that must go the other way, so
//! none of them can be passed by a checker that simply refuses more.
//!
//!   1. `test_declarations_that_need_each_other_are_refused_by_name` —
//!      MUST-FAIL control: two `def`s that call each other outside a `mutual`
//!      block. Refused, with a diagnostic that names both and offers the ways
//!      forward. CONTROL:
//!      `test_a_forward_reference_that_is_not_a_cycle_is_accepted` — a plain
//!      forward reference, which is the whole point of the feature, goes
//!      through.
//!   2. `test_two_declarations_cannot_claim_one_name` — MUST-FAIL control: a
//!      duplicate canonical name is DIAGNOSED, not silently skipped. CONTROL:
//!      `test_the_same_two_names_in_different_namespaces_are_accepted` — the
//!      collision must be about the CANONICAL name, not the short one.
//!   3. `test_a_def_with_no_written_type_can_still_be_forward_referenced` — a
//!      `def` with no signature is not a hole in the name index. Its type is
//!      read off a full elaboration performed inside the header fixed point, so
//!      it is staged like everything else.

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

/// MUST FAIL. `ping` and `pong` call each other and are not written as one
/// `mutual` block. Clean has no supported form for that, so the batch is
/// refused — and the diagnostic must say which declarations and what to do,
/// because the reader is a programmer who has to fix it.
#[test]
fn test_declarations_that_need_each_other_are_refused_by_name() {
    let checked = check(
        "\
set_option autoImplicit false
def ping (n : Nat) : Nat := pong n
def pong (n : Nat) : Nat := ping n
",
    );
    assert!(
        !checked.committed,
        "ACCEPTED a dependency cycle between `ping` and `pong`. Exposing the \
         cycle is what header-first checking buys; legalizing it is not."
    );
    for name in ["ping", "pong"] {
        assert!(
            checked.env.get_const(&Name::from_string(name)).is_none(),
            "`{name}` reached the environment from a REFUSED batch"
        );
    }
    let report = &checked.rejections;
    assert!(
        report.contains("ping") && report.contains("pong"),
        "the refusal does not name both members of the cycle, so the reader \
         cannot act on it:\n{report}"
    );
    assert!(
        report.contains("mutual"),
        "the refusal does not offer a way forward. A diagnostic that only says \
         'this is a cycle' leaves the fix to be guessed:\n{report}"
    );
}

/// CONTROL for (1) — "refuse anything that looks recursive" cannot pass this.
/// A plain forward reference is not a cycle, and accepting it is the entire
/// point of header-first checking.
#[test]
fn test_a_forward_reference_that_is_not_a_cycle_is_accepted() {
    let checked = check(
        "\
set_option autoImplicit false
def ping (n : Nat) : Nat := pong n
def pong (n : Nat) : Nat := n
",
    );
    assert!(
        checked.committed,
        "REJECTED a forward reference with no cycle in it. `ping` names `pong`, \
         which is declared later and depends on nothing — this is exactly what \
         a staged header index exists to resolve: {}",
        checked.rejections
    );
    for name in ["ping", "pong"] {
        let name = Name::from_string(name);
        assert!(
            checked
                .env
                .get_const(&name)
                .is_some_and(|info| info.value.is_some()),
            "`{name}` must be registered WITH a value"
        );
    }
}

/// MUST FAIL. Two declarations claiming one canonical name is diagnosed. The
/// failure mode this guards against is silence: skipping the second claimant
/// leaves two declarations disagreeing about what a name means, with no
/// message at all.
#[test]
fn test_two_declarations_cannot_claim_one_name() {
    let checked = check(
        "\
set_option autoImplicit false
def shared : Nat := 0
def shared : Nat := 1
",
    );
    assert!(
        !checked.committed,
        "ACCEPTED two declarations of `shared`. One name must mean one thing \
         across the batch, or the header index is not an index."
    );
    assert!(
        checked.rejections.contains("shared"),
        "the collision was not diagnosed by name:\n{}",
        checked.rejections
    );
}

/// CONTROL for (2) — the collision is about the CANONICAL name. Two `shared`s
/// in different namespaces are two different declarations and must both land.
#[test]
fn test_the_same_two_names_in_different_namespaces_are_accepted() {
    let checked = check(
        "\
set_option autoImplicit false
namespace A
def shared : Nat := 0
end A
namespace B
def shared : Nat := 1
end B
",
    );
    assert!(
        checked.committed,
        "REJECTED `A.shared` and `B.shared` as a collision. Collision detection \
         must compare qualified names, not short ones: {}",
        checked.rejections
    );
    for name in ["A.shared", "B.shared"] {
        assert!(
            checked.env.get_const(&Name::from_string(name)).is_some(),
            "`{name}` must be registered"
        );
    }
}

/// A `def` with NO written result type is still in the name index.
///
/// Its type cannot be read off its signature — there is no signature — so it is
/// read off a full elaboration, recomputed inside the header fixed point until
/// it stops changing. Leaving such a declaration out of the index would mean
/// every reference to it stayed order-dependent, which is the property this
/// whole facility removes.
#[test]
fn test_a_def_with_no_written_type_can_still_be_forward_referenced() {
    let checked = check(
        "\
set_option autoImplicit false
def user : Nat := inferred
def inferred := 41
",
    );
    assert!(
        checked.committed,
        "REJECTED a forward reference to `inferred`, whose type is inferred \
         from its body. A declaration with no written signature must still be \
         stageable — otherwise `def f := e` is a hole in the name index and \
         references to it keep source-order semantics: {}",
        checked.rejections
    );
    let user = checked
        .env
        .get_const(&Name::from_string("user"))
        .expect("`user` must be registered");
    let mut referenced = std::collections::HashSet::new();
    user.value
        .as_ref()
        .expect("`user` must have a value")
        .collect_constants_into(&mut referenced);
    assert!(
        referenced.contains(&Name::from_string("inferred")),
        "`user` does not mention `inferred` after elaboration, so the forward \
         reference resolved to something else: {referenced:?}"
    );
}
