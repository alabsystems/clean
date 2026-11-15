// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `@[implemented_by f]` is validated at elaboration the way Lean does it
//! (`src/Lean/Compiler/ImplementedByAttr.lean`, v4.30.0-rc2): `f` is resolved
//! as a global constant that already exists, its universe-parameter count must
//! equal the declaration's, and its type — instantiated at the declaration's
//! universe parameters — must be STRUCTURALLY equal to the declaration's type
//! (`Expr` `==`, which ignores binder names and binder annotations; not
//! definitional equality). Clean used to accept any name, so the compiler
//! could later run an implementation of a different type.
//!
//! Every expectation was measured with pinned Lean v4.30.0-rc2 on 2026-10-17
//! (`compiler-implemented-by-and-extern-fail-closed`,
//! docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md).

use clean_kernel::{Environment, Name};

use crate::test_support::file_verdicts::{run_file, run_modules_env_messages, verdict_of};

type Verdicts = Vec<(String, Result<(), String>)>;

/// One module, each refusal rendered as `clean check` prints it.
fn run_messages(src: &str) -> (Environment, Verdicts) {
    run_modules_env_messages(&[src])
}

/// The message `decl` is refused with (Lean's text is the `Display`).
fn refusal(src: &str, decl: &str) -> String {
    let (_, verdicts) = run_messages(src);
    match verdict_of(&verdicts, decl) {
        Ok(()) => panic!("`{decl}` was ACCEPTED; pinned Lean rejects it:\n{src}"),
        Err(err) => err.clone(),
    }
}

/// The first refusal of the LAST module (an `attribute` command has no
/// declaration name of its own).
fn first_refusal(verdicts: &Verdicts) -> String {
    verdicts
        .iter()
        .find_map(|(_, v)| v.as_ref().err().cloned())
        .unwrap_or_else(|| panic!("the file must have a refusal; got {verdicts:?}"))
}

fn implemented_by(env: &Environment, decl: &str) -> Option<String> {
    env.get_implemented_by(&Name::from_string(decl))
        .map(ToString::to_string)
}

/// Lean: "Invalid `implemented_by` argument `fastI`: `fastI` has type Int → Int
/// but `slowN` has type Nat → Nat".
#[test]
fn test_implemented_by_type_mismatch_refused() {
    let err = refusal(
        "def fastI (n : Int) : Int := n + 1\n\
         @[implemented_by fastI]\n\
         def slowN (n : Nat) : Nat := n + 2\n",
        "slowN",
    );
    assert!(
        err.contains("Invalid `implemented_by` argument `fastI`") && err.contains("has type"),
        "{err}"
    );
}

/// Lean: "Unknown constant `fastLater`" — the target must already exist.
#[test]
fn test_implemented_by_forward_reference_refused() {
    let err = refusal(
        "@[implemented_by fastLater]\n\
         def slowF (n : Nat) : Nat := n + 2\n\
         def fastLater (n : Nat) : Nat := n + 1\n",
        "slowF",
    );
    assert!(err.contains("Unknown constant `fastLater`"), "{err}");
}

/// Lean: "Invalid `implemented_by` argument `fastL`: `fastL` has 1 universe
/// level parameter(s), but `slowL` has 0".
#[test]
fn test_implemented_by_level_param_count_mismatch_refused() {
    let err = refusal(
        "universe u\n\
         def fastL (α : Sort u) (x : α) : α := x\n\
         @[implemented_by fastL]\n\
         def slowL (α : Type) (x : α) : α := x\n",
        "slowL",
    );
    assert!(
        err.contains("Invalid `implemented_by` argument `fastL`")
            && err.contains("universe level parameter"),
        "{err}"
    );
}

/// The rule is structural equality, not definitional: Lean rejects an
/// `abbrev` spelling of the same type.
#[test]
fn test_implemented_by_defeq_but_not_structurally_equal_refused() {
    let err = refusal(
        "abbrev MyNat := Nat\n\
         def fastA (n : MyNat) : MyNat := n + 1\n\
         @[implemented_by fastA]\n\
         def slowA (n : Nat) : Nat := n + 2\n",
        "slowA",
    );
    assert!(
        err.contains("Invalid `implemented_by` argument `fastA`"),
        "{err}"
    );
}

/// Lean: "Invalid `implemented_by` argument `selfy`: Definition cannot be
/// implemented by itself".
#[test]
fn test_implemented_by_self_refused() {
    let err = refusal(
        "@[implemented_by selfy]\ndef selfy (n : Nat) : Nat := n\n",
        "selfy",
    );
    assert!(err.contains("implemented by itself"), "{err}");
}

/// The negative control: what Lean ACCEPTS stays accepted — a different
/// binder annotation and binder name, renamed universe parameters, a target
/// reached through the current namespace or an `open`, and the attribute
/// command.
#[test]
fn test_implemented_by_accepts_what_lean_accepts() {
    let verdicts = run_file(
        "def fastB (α : Type) (x : α) : α := x\n\
         @[implemented_by fastB]\n\
         def slowB {α : Type} (y : α) : α := y\n\
         universe u v\n\
         def fastU (α : Sort u) (x : α) : α := x\n\
         @[implemented_by fastU]\n\
         def slowU (β : Sort v) (x : β) : β := x\n\
         namespace N\n\
         def fastN (n : Nat) : Nat := n + 1\n\
         @[implemented_by fastN]\n\
         def slowN (n : Nat) : Nat := n + 2\n\
         end N\n\
         open N in\n\
         @[implemented_by fastN]\n\
         def slowO (n : Nat) : Nat := n + 2\n\
         def fastC (n : Nat) : Nat := n + 1\n\
         def slowC (n : Nat) : Nat := n + 2\n\
         attribute [implemented_by fastC] slowC\n\
         def fastP (n : Nat) : Nat := n + 1\n\
         @[implemented_by fastP]\n\
         opaque slowP (n : Nat) : Nat\n",
    );
    for decl in ["slowB", "slowU", "slowN", "slowO", "slowC"] {
        assert!(
            verdict_of(&verdicts, decl).is_ok(),
            "`{decl}` must be accepted as Lean accepts it: {verdicts:?}"
        );
    }
    assert!(
        verdicts.iter().all(|(_, v)| v.is_ok()),
        "every declaration must be accepted: {verdicts:?}"
    );
}

/// Lean: "Cannot add attribute `[implemented_by]` to declaration `Nat.add`
/// because it is in an imported module" (measured, rc 1). Accepting it re-routed
/// every compiled `Nat.add` (`Nat.add 2 3` printed `6` at exit 0). The same for
/// a declaration of a source module this one imports.
#[test]
fn test_implemented_by_command_on_imported_decl_refused() {
    let (env, verdicts) = run_messages(
        "def myAdd (a b : Nat) : Nat := a * b\n\
         attribute [implemented_by myAdd] Nat.add\n",
    );
    assert_eq!(
        first_refusal(&verdicts),
        "Cannot add attribute `[implemented_by]` to declaration `Nat.add` because it is in an \
         imported module"
    );
    assert_eq!(implemented_by(&env, "Nat.add"), None);

    let (env, verdicts) = run_modules_env_messages(&[
        "def fast (n : Nat) : Nat := n + 1\ndef slow (n : Nat) : Nat := n + 2\n",
        "attribute [implemented_by fast] slow\n",
    ]);
    assert_eq!(
        first_refusal(&verdicts),
        "Cannot add attribute `[implemented_by]` to declaration `slow` because it is in an \
         imported module"
    );
    assert_eq!(implemented_by(&env, "slow"), None);
}

/// Lean refuses an ambiguous argument (measured: both shapes, rc 1) instead of
/// picking one. Clean fell back to the name as written: the first shape ran
/// the root `fast`, the second was refused with another message.
#[test]
fn test_implemented_by_ambiguous_target_refused() {
    for (source, message) in [
        (
            "def fast (n : Nat) : Nat := n + 1\n\
             namespace Foo\n\
             def fast (n : Nat) : Nat := n + 3\n\
             end Foo\n\
             open Foo\n\
             @[implemented_by fast]\n\
             def slow (n : Nat) : Nat := n + 2\n",
            "ambiguous identifier ``fast`, possible interpretations: [Foo.fast, fast]",
        ),
        (
            "namespace A\n\
             def f (n : Nat) : Nat := n + 1\n\
             end A\n\
             namespace B\n\
             def f (n : Nat) : Nat := n + 3\n\
             end B\n\
             open A B\n\
             @[implemented_by f]\n\
             def slow (n : Nat) : Nat := n + 2\n",
            "ambiguous identifier ``f`, possible interpretations: [A.f, B.f]",
        ),
    ] {
        let (env, verdicts) = run_messages(source);
        let err = match verdict_of(&verdicts, "slow") {
            Err(err) => err.clone(),
            Ok(()) => panic!("an ambiguous target must be refused: {source}"),
        };
        assert_eq!(err, message, "{source}");
        assert_eq!(implemented_by(&env, "slow"), None, "{source}");
    }
}

/// Lean resolves the argument before a LATER member of the same `mutual`
/// block exists: "Unknown constant `g`" (measured, plain and inside a
/// namespace). Clean resolved it after the whole block registered and
/// accepted it.
#[test]
fn test_implemented_by_later_mutual_sibling_refused() {
    for (source, decl) in [
        (
            "mutual\n\
             @[implemented_by g]\n\
             def f (n : Nat) : Nat := n + 2\n\
             def g (n : Nat) : Nat := n + 1\n\
             end\n",
            "f",
        ),
        (
            "namespace N\n\
             mutual\n\
             @[implemented_by g]\n\
             def f (n : Nat) : Nat := n + 2\n\
             def g (n : Nat) : Nat := n + 1\n\
             end\n\
             end N\n",
            "N.f",
        ),
    ] {
        let (env, verdicts) = run_messages(source);
        let refused = verdicts
            .iter()
            .filter_map(|(_, v)| v.as_ref().err())
            .any(|err| err == "Unknown constant `g`");
        assert!(refused, "{source}: {verdicts:?}");
        assert_eq!(implemented_by(&env, decl), None, "{source}");
    }
}

/// POSITIVE CONTROL for the sibling rule: an EARLIER member is accepted
/// (measured: `2`, `2` and `false`), resolved in the block's namespace.
#[test]
fn test_implemented_by_earlier_mutual_sibling_accepted() {
    for (source, decl, target) in [
        (
            "mutual\n\
             def fastM (n : Nat) : Nat := n + 1\n\
             @[implemented_by fastM]\n\
             def slowM (n : Nat) : Nat := n + 2\n\
             end\n",
            "slowM",
            "fastM",
        ),
        (
            "namespace N\n\
             mutual\n\
             def g (n : Nat) : Nat := n + 1\n\
             @[implemented_by g]\n\
             def f (n : Nat) : Nat := n + 2\n\
             end\n\
             end N\n",
            "N.f",
            "N.g",
        ),
        (
            "namespace N\n\
             mutual\n\
             def od : Nat → Bool\n  \
             | 0 => false\n  \
             | n+1 => ev n\n\
             @[implemented_by od]\n\
             def ev : Nat → Bool\n  \
             | 0 => true\n  \
             | n+1 => od n\n\
             end\n\
             end N\n",
            "N.ev",
            "N.od",
        ),
    ] {
        let (env, verdicts) = run_messages(source);
        assert!(
            verdicts.iter().all(|(_, v)| v.is_ok()),
            "{source}: {verdicts:?}"
        );
        assert_eq!(
            implemented_by(&env, decl).as_deref(),
            Some(target),
            "{source}"
        );
    }
}

/// `def N.slow` elaborates inside `namespace N` (Lean's
/// `expandDeclNamespace?`), so its argument `fast` is `N.fast` (measured:
/// `2`).
#[test]
fn test_implemented_by_decl_namespace_scope_resolves() {
    let (env, verdicts) = run_messages(
        "namespace N\n\
         def fast (n : Nat) : Nat := n + 1\n\
         end N\n\
         @[implemented_by fast]\n\
         def N.slow (n : Nat) : Nat := n + 2\n",
    );
    assert!(verdicts.iter().all(|(_, v)| v.is_ok()), "{verdicts:?}");
    assert_eq!(implemented_by(&env, "N.slow").as_deref(), Some("N.fast"));
}

/// The messages are pinned Lean's, as `clean check` prints them.
#[test]
fn test_implemented_by_messages_are_lean_text() {
    assert_eq!(
        refusal(
            "@[implemented_by fastLater]\n\
             def slowF (n : Nat) : Nat := n + 2\n\
             def fastLater (n : Nat) : Nat := n + 1\n",
            "slowF",
        ),
        "Unknown constant `fastLater`"
    );
    assert_eq!(
        refusal(
            "universe u\n\
             def fastL (α : Sort u) (x : α) : α := x\n\
             @[implemented_by fastL]\n\
             def slowL (α : Type) (x : α) : α := x\n",
            "slowL",
        ),
        "Invalid `implemented_by` argument `fastL`: `fastL` has 1 universe level parameter(s), \
         but `slowL` has 0"
    );
    assert_eq!(
        refusal(
            "@[implemented_by selfy]\ndef selfy (n : Nat) : Nat := n\n",
            "selfy"
        ),
        "Invalid `implemented_by` argument `selfy`: Definition cannot be implemented by itself"
    );
    let mismatch = refusal(
        "def fastI (n : Int) : Int := n + 1\n\
         @[implemented_by fastI]\n\
         def slowN (n : Nat) : Nat := n + 2\n",
        "slowN",
    );
    assert!(
        mismatch.starts_with("Invalid `implemented_by` argument `fastI`: `fastI` has type\n  ")
            && mismatch.contains("\nbut `slowN` has type\n  "),
        "{mismatch}"
    );
}

/// Lean v4.35.0 rejects this spelling; it must not register a compiler override.
#[test]
fn test_implemented_by_camel_case_is_unknown_attribute() {
    let (env, verdicts) = run_messages(
        "def fast (n : Nat) : Nat := n + 1\n\
         @[implementedBy fast]\n\
         def slow (n : Nat) : Nat := n + 2\n",
    );
    let error = verdict_of(&verdicts, "slow")
        .as_ref()
        .expect_err("Lean rejects implementedBy");
    assert_eq!(error, "Unknown attribute `[implementedBy]`");
    assert!(env.get_const(&Name::from_string("slow")).is_none());
    assert_eq!(implemented_by(&env, "slow"), None);
}

#[test]
fn test_unknown_attribute_does_not_leave_an_implemented_by_binding() {
    for attributes in [
        "implemented_by fast, notARealAttribute",
        "notARealAttribute, implemented_by fast",
    ] {
        let source = format!("def fast (n : Nat) : Nat := n + 1\n@[{attributes}] def slow (n : Nat) : Nat := n + 2\n");
        let (env, verdicts) = run_messages(&source);
        let error = verdict_of(&verdicts, "slow")
            .as_ref()
            .expect_err("unknown attributes fail before collection");
        assert!(error.contains("notARealAttribute"), "{error}");
        assert!(env.get_const(&Name::from_string("slow")).is_none());
        assert_eq!(implemented_by(&env, "slow"), None);
    }
}

/// KNOWN DIVERGENCE, pinned so it fails the day it closes. In Lean an
/// `optParam` default is part of the type it compares, so pinned Lean refuses:
/// "`fastD` has type optParam Nat 3 → Nat but `slowD` has type Nat → Nat".
/// Clean's type for a binder with a default carries no `optParam`, so the
/// structural check sees the same type twice and accepts. Both erase to the
/// same runtime signature.
#[test]
fn test_implemented_by_optparam_default_accepted_known_divergence() {
    let (env, verdicts) = run_messages(
        "def fastD (n : Nat := 3) : Nat := n + 1\n\
         @[implemented_by fastD]\n\
         def slowD (n : Nat) : Nat := n + 2\n",
    );
    assert!(verdict_of(&verdicts, "slowD").is_ok(), "{verdicts:?}");
    assert_eq!(implemented_by(&env, "slowD").as_deref(), Some("fastD"));
    let fast_d = env
        .get_const(&Name::from_string("fastD"))
        .expect("fastD is registered");
    assert!(
        !fast_d.type_.to_string().contains("optParam"),
        "`fastD`'s type now carries `optParam`: the divergence may have closed, and `slowD` \
         must then be refused as in Lean: {}",
        fast_d.type_
    );
}

/// The header-first batch driver (`module_batch`, Trust's island lane) applies
/// the attribute after the whole module's headers are staged. Lean refuses a
/// target declared later ("Unknown constant `later`"); so must the batch.
#[test]
fn test_implemented_by_batch_forward_reference_refused() {
    use crate::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    let decls = clean_parser::parse_file(
        "@[implemented_by later]\n\
         def slow3 (n : Nat) : Nat := n + 2\n\
         def later (n : Nat) : Nat := n + 1\n",
    )
    .expect("the fixture parses");
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let outcome = elaborate_module(&mut env, &mut file_ctx, &units, BatchOptions::islands());
    let report = outcome.render_rejections();
    assert_eq!(implemented_by(&env, "slow3"), None, "{report}");
    assert!(report.contains("Unknown constant `later`"), "{report}");
}

/// `@[implemented_by]` on an `instance` binds the instance constant (pinned
/// Lean runs `fastB`: `1`, battery row `attr_implemented_by_instance`). The
/// parser used to drop every attribute on an instance but its priority, so
/// nothing was bound and compiled code ran the instance's own value.
#[test]
fn test_implemented_by_on_instance_registered() {
    let (env, verdicts) = run_messages(
        "@[reducible] def fastB : Inhabited Nat := ⟨1⟩\n\
         @[implemented_by fastB]\n\
         instance slowB : Inhabited Nat := ⟨2⟩\n",
    );
    assert!(verdicts.iter().all(|(_, v)| v.is_ok()), "{verdicts:?}");
    assert_eq!(implemented_by(&env, "slowB").as_deref(), Some("fastB"));
}

/// The instance's argument is validated like a `def`'s, with Lean's text.
#[test]
fn test_implemented_by_on_instance_type_mismatch_refused() {
    let err = refusal(
        "@[reducible] def fastI : Inhabited Int := ⟨1⟩\n\
         @[implemented_by fastI]\n\
         instance slowI : Inhabited Nat := ⟨2⟩\n",
        "slowI",
    );
    assert!(
        err.starts_with("Invalid `implemented_by` argument `fastI`: `fastI` has type")
            && err.contains("but `slowI` has type"),
        "{err}"
    );
}
