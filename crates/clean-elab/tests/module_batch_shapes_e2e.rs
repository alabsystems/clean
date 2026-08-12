// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! I1 — the declaration shapes a batch has to keep working.
//!
//! Header-first checking is only worth having if ordinary programs still go
//! through it. These are the shapes whose handling changed: type-level
//! declarations are elaborated COMPLETELY in their own phase rather than staged
//! (a partial family — the type name resolvable without its constructors —
//! would be worse than no header at all), and instances are frozen into the
//! resolution table at header time rather than when their declaration lands.
//!
//! Every case is written so the FORWARD direction is the interesting one: the
//! user is declared before the thing it uses. Under source order each of these
//! is an unknown identifier.

use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

fn check(source: &str) -> (Environment, bool, String) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = clean_elab::FileContext::new();
    let decls = parse_file(source).expect("fixture must parse");
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let outcome = elaborate_module(&mut env, &mut file_ctx, &units, BatchOptions::islands());
    let committed = outcome.committed;
    let report = outcome.render_rejections();
    (env, committed, report)
}

fn assert_registered(env: &Environment, names: &[&str]) {
    for name in names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some()
                || env.get_inductive(&Name::from_string(name)).is_some()
                || env.get_constructor(&Name::from_string(name)).is_some(),
            "`{name}` is not in the published environment"
        );
    }
}

/// An `inductive` used by a declaration written BEFORE it.
///
/// Type-level declarations are elaborated first, in authored order, so the
/// whole family — type, constructors, recursors — exists before any body runs.
#[test]
fn test_an_inductive_can_be_used_before_it_is_declared() {
    let (env, committed, report) = check(
        "\
set_option autoImplicit false
def pick : Colour := Colour.red
inductive Colour where
  | red : Colour
  | blue : Colour
",
    );
    assert!(
        committed,
        "REJECTED a use of `Colour` written before the `inductive`. A type-level \
         declaration cannot depend on any body, so it must be schedulable ahead \
         of everything that uses it: {report}"
    );
    assert_registered(&env, &["Colour", "Colour.red", "Colour.blue", "pick"]);
}

/// A `structure` and one of its projections, used before the declaration.
#[test]
fn test_a_structure_projection_can_be_used_before_the_structure() {
    let (env, committed, report) = check(
        "\
set_option autoImplicit false
def first (p : Pair) : Nat := p.left
structure Pair where
  left : Nat
  right : Nat
",
    );
    assert!(
        committed,
        "REJECTED a projection of `Pair` used before the `structure`. Staging \
         only the type name and not its fields is exactly the partial family \
         this design refuses to produce — the whole declaration is elaborated \
         instead: {report}"
    );
    assert_registered(&env, &["Pair", "Pair.left", "Pair.right", "first"]);
}

/// A named `instance` resolved by a declaration written before it.
///
/// Instance metadata is frozen into the staging environment's resolution table
/// at header time. Without that, instance selection would depend on
/// registration order — the same defect as name resolution, one level down.
#[test]
fn test_a_named_instance_is_visible_before_it_is_declared() {
    let (env, committed, report) = check(
        "\
set_option autoImplicit false
class Tag (a : Type) where
  tag : a -> Nat

def use_tag (n : Nat) : Nat := Tag.tag n

instance tagNat : Tag Nat where
  tag := fun n => n
",
    );
    assert!(
        committed,
        "REJECTED an instance use written before the `instance`. A named \
         instance's canonical name is stable, so its class and priority can be \
         frozen at header time and resolution stops depending on registration \
         order: {report}"
    );
    assert_registered(&env, &["Tag", "tagNat", "use_tag"]);
}

/// A `theorem` whose proof reduces through a definition declared after it.
///
/// This is the shape that cannot be faked by name resolution alone: `rfl` has
/// to UNFOLD `answer`, so `answer` must be a real definition by the time the
/// proof is checked — not the staged signature that made the name resolve.
#[test]
fn test_a_proof_reduces_through_a_later_definition() {
    let (env, committed, report) = check(
        "\
set_option autoImplicit false
theorem answer_is_42 : answer = 42 := rfl
def answer : Nat := 42
",
    );
    assert!(
        committed,
        "REJECTED a proof that must unfold a later definition. Resolving the \
         NAME against a header is not enough — the body phase has to schedule \
         `answer` before the proof, so `rfl` reduces through a definition and \
         not through a value-free signature: {report}"
    );
    assert_registered(&env, &["answer", "answer_is_42"]);
}
