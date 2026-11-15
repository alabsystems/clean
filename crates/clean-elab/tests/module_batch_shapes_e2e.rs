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
//! The forward cases declare the user before the thing it uses. Under source
//! order each of these is an unknown identifier. The alias-prefix case instead
//! exercises a target published before planning the alias command.

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

#[test]
fn alias_keeps_declared_prefix_metadata_when_target_returns_a_function() {
    let mut env = Environment::with_prelude();
    let mut file_ctx = clean_elab::FileContext::new();
    // Alias commands elaborate during planning, before queued value bodies.
    // Publish the exact target first, then exercise alias registration and its
    // named-argument consumer together through the public batch interface.
    for source in [
        "def original (n : Nat) : Nat → Nat := fun m => n\n",
        "\
alias prefixBatchAlias := original
example : prefixBatchAlias (n := 2) 3 = 2 := rfl
",
    ] {
        let decls = parse_file(source).expect("prefix fixture must parse");
        let units = [SourceUnit {
            id: UnitId(0),
            decls: &decls,
        }];
        let outcome = elaborate_module(&mut env, &mut file_ctx, &units, BatchOptions::islands());
        assert!(
            outcome.committed,
            "prefix alias batch was refused: {}",
            outcome.render_rejections()
        );
    }
    let alias = Name::from_string("prefixBatchAlias");
    assert_eq!(
        env.get_typed_param_names(&alias),
        Some([Name::from_string("n")].as_slice()),
        "the returned function argument is outside the declared metadata prefix"
    );
    assert_eq!(
        env.get_const(&alias).expect("alias").type_,
        env.get_const(&Name::from_string("original"))
            .expect("target")
            .type_
    );
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

/// Consumers must receive the original anonymous judgment, not reconstruct a
/// potentially different elaboration from its source after the batch.
#[test]
fn test_anonymous_proof_judgments_survive_batch_reporting() {
    use clean_kernel::{Expr, Level, ReferenceKernel};
    let mut env = Environment::with_prelude();
    let mut ctx = clean_elab::FileContext::new();
    let decls = parse_file("def retained_n : Nat := 1\nexample : retained_n = 1 := rfl\n")
        .expect("fixture parses");
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let outcome = elaborate_module(&mut env, &mut ctx, &units, BatchOptions::islands());
    assert!(outcome.committed, "{}", outcome.render_rejections());
    let judgments: Vec<_> = outcome
        .decls
        .iter()
        .flat_map(|d| &d.checked_judgments)
        .collect();
    assert_eq!(judgments.len(), 1);
    let reference = ReferenceKernel::new(env).expect("base admitted");
    reference
        .check_closed_term(&judgments[0].type_, &judgments[0].value)
        .expect("original example rechecks");
    let wrong_goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_str("Nat"), Expr::nat_lit(1), Expr::nat_lit(2)],
    );
    assert!(
        reference
            .check_closed_term(&wrong_goal, &judgments[0].value)
            .is_err(),
        "the retained proof cannot be substituted for a different judgment"
    );
}

#[test]
fn test_a_refused_anonymous_proof_retains_no_successful_judgment() {
    let mut env = Environment::with_prelude();
    let mut ctx = clean_elab::FileContext::new();
    let decls = parse_file("example : (1 : Nat) = 2 := rfl\n").expect("fixture parses");
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let outcome = elaborate_module(&mut env, &mut ctx, &units, BatchOptions::islands());
    assert!(!outcome.committed);
    assert!(!outcome.is_clean());
    assert!(outcome.decls.iter().all(|d| d.checked_judgments.is_empty()));
}
