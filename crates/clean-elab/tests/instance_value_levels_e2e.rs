// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! An instance whose BODY reaches a universe-polymorphic constant must not
//! leak that constant's levels into the declarations that USE the instance.
//!
//! Measured 2026-09-19 (Trust superproject,
//! `reports/2026-09-19-the-lean-typeclass-gap-is-in-the-island.md`, addenda
//! 6-7): `instance : Mag Nat where op := fun x y => x + y` elaborates with the
//! three `HAdd` universe metavariables in its stored value UNSOLVED while its
//! type is the concrete `Mag Nat`. Every resolution freshens them, a
//! monomorphic class constrains nothing, and decl-close generalizes them onto
//! the USING declaration: `def five : Nat := twice 5` registers as
//! `five.{u_3, u_4, u_5} : Nat`. `clean check` passes (nothing compares), the
//! Trust island's header-first batch refuses with HeaderTypeDivergence
//! (`staged {} Nat` vs `registered {u_3, u_4, u_5} Nat`).
//!
//! Two fixes were ruled out by measurement before this test existed: defaulting
//! value-only fresh levels to `Zero` at decl close (breaks monadic `do`:
//! `Bind.bind` stops reducing — `b07_term_position_do_block_rfl_certifies`),
//! and dropping the `?`-prefixed names from the candidate's level params (the
//! kernel rejects an undefined universe level parameter). The instance's stored
//! value must carry SOLVED levels — at `Mag Nat` the `HAdd` levels are `0`.
//!
//! These tests drive the same header-first batch the island uses, so they fail
//! exactly the way the island fails, and they pin the polymorphic use that
//! already works so the fix cannot be "refuse everything".
use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

struct Checked {
    env: Environment,
    committed: bool,
    rejections: String,
}

fn island(source: &str) -> Checked {
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

/// The batch commits with no rejection, and the named declarations are
/// registered with NO universe parameters — the leak is measured from outside
/// the batch too, so a bug in the header check itself is still caught.
fn must_commit_monomorphic(source: &str, monomorphic: &[&str]) {
    let checked = island(source);
    assert!(
        checked.committed && checked.rejections.is_empty(),
        "the island batch must commit with no rejection; got:\n{}\n--- source ---\n{source}",
        checked.rejections
    );
    for name in monomorphic {
        let decl = checked
            .env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("`{name}` must be registered when the batch commits"));
        assert!(
            decl.level_params.is_empty(),
            "`{name}` registered with universe parameters {:?} on a fully concrete \
             type — an instance body's levels leaked into its user",
            decl.level_params
        );
    }
    // The reservation invariant, measured from outside: no registered constant of
    // this batch carries a level parameter spelled in the metavariable namespace.
    for decl in checked.env.constants() {
        for level in &decl.level_params {
            assert!(
                !level.to_string().starts_with("?u_"),
                "`{}` registered with the reserved level name `{level}`",
                decl.name
            );
        }
    }
}

fn must_commit(source: &str) {
    must_commit_monomorphic(source, &[]);
}

const MAG: &str = "class Mag (a : Type) where\n  op : a -> a -> a\n\
                   instance : Mag Nat where\n  op := fun x y => x + y\n";

/// The measured shape: a polymorphic user of the instance at a concrete carrier.
#[test]
fn instance_body_levels_do_not_leak_through_a_polymorphic_user() {
    must_commit_monomorphic(
        &format!(
            "{MAG}def twice {{a : Type}} [Mag a] (x : a) : a := Mag.op x x\n\
             def five : Nat := twice 5\n"
        ),
        &["five"],
    );
}

/// The second face: a NAMED instance is itself staged by the island batch, so
/// the raw mint vector refused the instance declaration directly
/// (`staged {}` vs `registered {?u_0, ?u_1, ?u_2}` on `instMagNat`).
#[test]
fn a_named_instance_commits_and_registers_without_universe_parameters() {
    must_commit_monomorphic(
        "class Mag (a : Type) where\n  op : a -> a -> a\n\
         instance instMagNat : Mag Nat where\n  op := fun x y => x + y\n\
         def five : Nat := Mag.op 2 3\n",
        &["instMagNat", "five"],
    );
}

/// The monomorphic twin: a direct method call at the concrete carrier.
#[test]
fn instance_body_levels_do_not_leak_through_a_monomorphic_user() {
    must_commit_monomorphic(&format!("{MAG}def five : Nat := Mag.op 2 3\n"), &["five"]);
}

/// A VALUE-parameter class leaks the same way when its instance body reaches
/// `HAdd` (report addendum 2: `name := 3 + 4` leaks, `name := 7` does not).
#[test]
fn a_value_parameter_class_with_an_arithmetic_instance_body_does_not_leak() {
    must_commit_monomorphic(
        "class Tag (n : Nat) where\n  name : Nat\n\
         instance : Tag 0 where\n  name := 3 + 4\n\
         def seven : Nat := Tag.name 0\n",
        &["seven"],
    );
    must_commit_monomorphic(
        "class Tag (n : Nat) where\n  name : Nat\n\
         instance : Tag 0 where\n  name := 7\n\
         def seven : Nat := Tag.name 0\n",
        &["seven"],
    );
}

/// CONTROL — "refuse everything" cannot pass this: the polymorphic use of the
/// instance, with no concrete-carrier user, commits today and must keep
/// committing.
#[test]
fn a_polymorphic_use_without_a_concrete_user_commits() {
    must_commit(&format!(
        "{MAG}def twice {{a : Type}} [Mag a] (x : a) : a := Mag.op x x\n"
    ));
}

/// A universe-POLYMORPHIC instance (`instance : Wrap a`) whose body reaches
/// `List.cons.{u}` leaks the same way at a concrete carrier — measured: `one`
/// registers with universe parameters on `List Nat`. The class's own level is
/// declared and stays; the body's are the ones that must be solved.
#[test]
fn a_universe_polymorphic_instance_body_does_not_leak_at_a_concrete_carrier() {
    must_commit_monomorphic(
        "class Wrap (a : Type u) where\n  wrap : a -> List a\n\
         instance : Wrap a where\n  wrap := fun x => [x]\n\
         def one : List Nat := Wrap.wrap 1\n",
        &["one"],
    );
}
