// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A `codata` / `codef` command returns the declarations it registered.
//!
//! These commands elaborate, kernel-check and register real declarations (the
//! carrier, its accessors, the corecursor, the `rfl` laws, the codef's own
//! definition) and used to answer `ElabResult::Skipped` — the result of a
//! command that declares nothing. Every consumer that counts or re-checks
//! declarations through `ElabResult::leaf_decls` therefore saw nothing, and a
//! `sorry` written in a codef clause reached no per-declaration trust gate:
//! `clean check` exited 0 with `status: pass` while its own trust summary
//! counted the sorry (reports/2026-09-24-project-check-vacuous.md).
//!
//! One test per generating lane (plain, indexed, variant and mutual codata;
//! plain, mk-guarded, indexed and mutual codef). Each asserts that the
//! command's result flattens to at least one leaf, that every leaf is a
//! declaration actually present in the environment, and that the user-named
//! declaration is among them.

use crate::elaborate_decl_and_register;
use crate::register::registration_warning_for_name;
use crate::{ElabResult, RegistrationWarningKind};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

const STREAM: &str = "codata Strm (A : Type) where\n  head : A\n  tail : Strm A\n";
const INDEXED: &str =
    "codata IS3 : (n : Nat) → Type where\n  val : Nat\n  next : IS3 (Nat.succ n)\n";
const MUTUAL: &str =
    "mutual\n  codata TreeQ (A : Type) where\n    label : A\n    kids : ForestQ A\n  \
codata ForestQ (A : Type) where\n    first : TreeQ A\n    rest : ForestQ A\nend\n";

/// Elaborate every declaration of `code`; return the environment and the
/// LAST declaration's result (the command under test).
fn elab_last(code: &str) -> (Environment, ElabResult) {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("fixture parses");
    let mut last = None;
    for (i, decl) in decls.iter().enumerate() {
        last = Some(
            elaborate_decl_and_register(&mut env, decl)
                .unwrap_or_else(|e| panic!("decl {i} must elaborate: {e:?}")),
        );
    }
    (env, last.expect("at least one declaration"))
}

/// The command's result names every declaration it registered, and at least
/// the ones in `expected`.
fn assert_declares(code: &str, expected: &[&str]) -> Environment {
    let (env, result) = elab_last(code);
    assert!(
        !matches!(result, ElabResult::Skipped),
        "a command that registered declarations must not answer Skipped"
    );
    let mut leaves = Vec::new();
    result.leaf_decls(&mut leaves);
    assert!(!leaves.is_empty(), "no declaration leaves for:\n{code}");
    let names: Vec<&Name> = leaves
        .iter()
        .map(|leaf| {
            leaf.declaration_name()
                .unwrap_or_else(|| panic!("leaf without a declaration name: {leaf:?}"))
        })
        .collect();
    for name in &names {
        assert!(
            env.get_const(name).is_some(),
            "leaf `{name}` is not a registered declaration"
        );
    }
    for want in expected {
        let want = Name::from_string(want);
        assert!(
            names.contains(&&want),
            "`{want}` missing from the command's declarations: {names:?}"
        );
    }
    env
}

#[test]
fn plain_codata_returns_its_generated_declarations() {
    assert_declares(STREAM, &["Strm", "Strm.head", "Strm.tail", "Strm.corec"]);
}

#[test]
fn indexed_codata_returns_its_generated_declarations() {
    assert_declares(INDEXED, &["IS3", "IS3.val", "IS3.next"]);
}

#[test]
fn variant_codata_returns_its_generated_declarations() {
    assert_declares(
        "codata VBox (A : Type) where\n  | wrap : A → VBox A → VBox A\n",
        &["VBox"],
    );
}

#[test]
fn mutual_codata_returns_its_generated_declarations() {
    assert_declares(MUTUAL, &["TreeQ", "ForestQ"]);
}

#[test]
fn plain_codef_returns_its_definition() {
    let code = format!(
        "{STREAM}codef natsFrom (n : Nat) : Strm Nat where\n  head := n\n  tail := natsFrom (Nat.succ n)\n"
    );
    assert_declares(&code, &["natsFrom"]);
}

#[test]
fn guarded_codef_returns_its_definition() {
    let code = format!(
        "{STREAM}codef alternate (s : Nat) : Strm Nat where\n  head := s\n  \
         tail := Strm.mk (Nat.add s 100) (alternate (Nat.succ s))\n"
    );
    assert_declares(&code, &["alternate"]);
}

#[test]
fn indexed_codef_returns_its_definition() {
    let code = format!(
        "{INDEXED}codef tracker (n : Nat) : IS3 n where\n  val := n\n  next := tracker (Nat.succ n)\n"
    );
    assert_declares(&code, &["tracker"]);
}

#[test]
fn mutual_codef_returns_every_member() {
    let code = format!(
        "{MUTUAL}mutual\n  codef tq (s : Nat) : TreeQ Nat where\n    label := s\n    kids := fq (Nat.succ s)\n  \
         codef fq (s : Nat) : ForestQ Nat where\n    first := tq s\n    rest := fq (Nat.succ s)\nend\n"
    );
    assert_declares(&code, &["tq", "fq"]);
}

/// The trust half: a `sorry` in a codef clause is a registration warning on
/// the codef's OWN declaration, and that declaration is now one of the
/// command's leaves — so a per-declaration gate can see it.
#[test]
fn a_sorry_in_a_codef_clause_is_visible_on_a_returned_declaration() {
    for (code, name) in [
        (
            format!("{STREAM}codef natsFrom (n : Nat) : Strm Nat where\n  head := sorry\n  tail := natsFrom (Nat.succ n)\n"),
            "natsFrom",
        ),
        (
            format!(
                "{STREAM}codef alternate (s : Nat) : Strm Nat where\n  head := s\n  \
                 tail := Strm.mk sorry (alternate (Nat.succ s))\n"
            ),
            "alternate",
        ),
        (
            format!("{INDEXED}codef tracker (n : Nat) : IS3 n where\n  val := sorry\n  next := tracker (Nat.succ n)\n"),
            "tracker",
        ),
    ] {
        let env = assert_declares(&code, &[name]);
        let warning = registration_warning_for_name(&env, &Name::from_string(name))
            .unwrap_or_else(|| panic!("`{name}` must carry its sorry as a registration warning"));
        assert!(
            matches!(
                warning.kind,
                RegistrationWarningKind::ExplicitSorry | RegistrationWarningKind::SyntheticSorry
            ),
            "`{name}`: expected a sorry warning, got {:?}",
            warning.kind
        );
    }
}
