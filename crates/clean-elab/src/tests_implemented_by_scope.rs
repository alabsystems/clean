// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Where an `@[implemented_by]` argument resolves, and which declarations the
//! `attribute [implemented_by]` command may name, in every context that
//! elaborates source.
//!
//! **Scope.** Pinned Lean v4.30.0-rc2 elaborates a declaration written
//! `pre.d` inside `namespace pre` (`expandDeclNamespace?`,
//! `Lean/Elab/Declaration.lean`), whatever its modifiers: `private def N.d`
//! opens `N`. A name written `_root_.pre.d` opens nothing. A `mutual` block
//! opens the common prefix of its members' namespaces, and nothing when a
//! member has none (`expandMutualNamespace`). Measured on 2026-10-18 with
//! `fast := n + 1`, `N.fast := n + 2`, `slow := n + 3` and `main` printing
//! the bound declaration applied to `1`: `private def N.slow` prints `3`
//! (`N.fast`), and is accepted with only `N.fast` declared; `def
//! _root_.N.slow` prints `2` (`fast`), and with only `N.fast` declared is
//! "Unknown constant `fast`"; `_root_.N.X.slow` written inside `namespace N`
//! prints `5` (`N.fast`, the current namespace's); `mutual` of `N.slow` and
//! `other` prints `2`; `mutual` of `N.A.slow` and `N.B.other` prints `3`
//! (`N.fast`, not `N.A.fast`).
//!
//! **Declared here.** Lean refuses the command form on a declaration of an
//! imported module (`ParametricAttribute.add`). A declaration the same
//! elaboration run added is never imported, whatever the driver: a file with
//! a `FileContext`, a driver with none (Trust's bridge,
//! `elaborate_decl_and_register_with_warning`), a `namespace` block elaborated
//! without one, or a header-first batch (`crate::module_batch`, Trust's island
//! lane).

use clean_kernel::{Environment, Name};

use crate::test_support::file_verdicts::{
    assert_all_accepted, run_modules_env_messages, verdict_of,
};
use crate::ElabResult;

const TARGETS: &str = "def fast (n : Nat) : Nat := n + 1\n\
                       def N.fast (n : Nat) : Nat := n + 2\n";

fn bound(env: &Environment, decl: &Name) -> Option<String> {
    env.get_implemented_by(decl).map(ToString::to_string)
}

fn bound_str(env: &Environment, decl: &str) -> Option<String> {
    bound(env, &Name::from_string(decl))
}

/// The private kernel name of `user` in module `M0`.
fn private_m0(user: &str) -> Name {
    crate::private_names::mk_private_name(&Name::from_string("M0"), &Name::from_string(user))
}

/// One module named `M0`, accepted as a whole, and its environment.
fn accepted(src: &str) -> Environment {
    let (env, verdicts) = run_modules_env_messages(&[src]);
    assert_all_accepted(&verdicts, src);
    env
}

/// `private def N.slow` is elaborated inside `namespace N`, as Lean does:
/// `fast` is `N.fast`. Clean derived the namespace from the kernel name
/// `_private.M0.0.N.slow`, so it bound the root `fast`, and with only
/// `N.fast` declared it refused a program Lean accepts.
#[test]
fn test_implemented_by_private_decl_opens_its_written_namespace() {
    let env = accepted(&format!(
        "{TARGETS}@[implemented_by fast]\nprivate def N.slow (n : Nat) : Nat := n + 3\n"
    ));
    assert_eq!(
        bound(&env, &private_m0("N.slow")).as_deref(),
        Some("N.fast")
    );

    let env = accepted(
        "def N.fast (n : Nat) : Nat := n + 2\n\
         @[implemented_by fast]\n\
         private def N.slow (n : Nat) : Nat := n + 3\n",
    );
    assert_eq!(
        bound(&env, &private_m0("N.slow")).as_deref(),
        Some("N.fast")
    );

    let env = accepted(
        "namespace M\n\
         def fast (n : Nat) : Nat := n + 1\n\
         def N.fast (n : Nat) : Nat := n + 2\n\
         @[implemented_by fast]\n\
         private def N.slow (n : Nat) : Nat := n + 3\n\
         end M\n",
    );
    assert_eq!(
        bound(&env, &private_m0("M.N.slow")).as_deref(),
        Some("M.N.fast")
    );
}

/// `def _root_.N.slow` opens no namespace: `fast` resolves where the
/// declaration is written. Clean entered `N` because the kernel name's parent
/// extended the (anonymous) current namespace.
#[test]
fn test_implemented_by_root_prefixed_decl_opens_no_namespace() {
    let env = accepted(&format!(
        "{TARGETS}@[implemented_by fast]\ndef _root_.N.slow (n : Nat) : Nat := n + 3\n"
    ));
    assert_eq!(bound_str(&env, "N.slow").as_deref(), Some("fast"));

    let env = accepted(
        "def fast (n : Nat) : Nat := n + 1\n\
         def N.X.fast (n : Nat) : Nat := n + 2\n\
         namespace N\n\
         def fast (n : Nat) : Nat := n + 4\n\
         @[implemented_by fast]\n\
         def _root_.N.X.slow (n : Nat) : Nat := n + 3\n\
         end N\n",
    );
    assert_eq!(bound_str(&env, "N.X.slow").as_deref(), Some("N.fast"));

    let src = "def N.fast (n : Nat) : Nat := n + 2\n\
               @[implemented_by fast]\n\
               def _root_.N.slow (n : Nat) : Nat := n + 3\n";
    let (env, verdicts) = run_modules_env_messages(&[src]);
    assert_eq!(
        verdict_of(&verdicts, "N.slow"),
        &Err("Unknown constant `fast`".to_string()),
        "{src}"
    );
    assert_eq!(bound_str(&env, "N.slow"), None);
}

/// A `mutual` block opens the common prefix of its members' namespaces, for
/// every member: nothing when one member has no namespace (`fast` is the root
/// one), `N` for `N.A.slow` beside `N.B.other` (`fast` is `N.fast`, never
/// `N.A.fast`). Clean entered each member's own namespace.
#[test]
fn test_implemented_by_mutual_block_opens_common_namespace() {
    let env = accepted(&format!(
        "{TARGETS}mutual\n\
         @[implemented_by fast]\n\
         def N.slow (n : Nat) : Nat := n + 3\n\
         def other (n : Nat) : Nat := n + 5\n\
         end\n"
    ));
    assert_eq!(bound_str(&env, "N.slow").as_deref(), Some("fast"));

    let env = accepted(&format!(
        "{TARGETS}def N.A.fast (n : Nat) : Nat := n + 4\n\
         mutual\n\
         @[implemented_by fast]\n\
         def N.A.slow (n : Nat) : Nat := n + 3\n\
         def N.B.other (n : Nat) : Nat := n + 5\n\
         end\n"
    ));
    assert_eq!(bound_str(&env, "N.A.slow").as_deref(), Some("N.fast"));
}

/// Each declaration's verdict when `src` is elaborated one declaration at a
/// time with NO `FileContext`, as Trust's bridge elaborates an island
/// (`elaborate_decl_and_register_with_warning`), each error as a user reads it.
fn run_without_file_context(env: &mut Environment, src: &str) -> Vec<Result<(), String>> {
    let decls = clean_parser::parse_file(src).expect("the fixture parses");
    decls
        .iter()
        .map(
            |decl| match crate::elaborate_decl_and_register_with_warning(env, decl) {
                Err(err) => Err(err.to_string()),
                Ok(registered) => {
                    let mut leaves = Vec::new();
                    registered.result.leaf_decls(&mut leaves);
                    match leaves.into_iter().find_map(|leaf| match leaf {
                        ElabResult::Failed { error, .. } => Some(error.to_string()),
                        _ => None,
                    }) {
                        Some(err) => Err(err),
                        None => Ok(()),
                    }
                }
            },
        )
        .collect()
}

const IMPORTED_NAT_ADD: &str = "Cannot add attribute `[implemented_by]` to declaration \
                                `Nat.add` because it is in an imported module";

/// Without a `FileContext` the command may name a declaration the same run
/// added: Lean refuses only a declaration of an imported module. Clean
/// refused every command form there. A prelude constant is still refused,
/// with Lean's text.
#[test]
fn test_implemented_by_command_without_file_context_names_own_decl() {
    let mut env = Environment::with_prelude();
    let verdicts = run_without_file_context(
        &mut env,
        "def fast (n : Nat) : Nat := n + 1\n\
         def slow (n : Nat) : Nat := n + 2\n\
         attribute [implemented_by fast] slow\n",
    );
    assert!(verdicts.iter().all(Result::is_ok), "{verdicts:?}");
    assert_eq!(bound_str(&env, "slow").as_deref(), Some("fast"));

    let verdicts = run_without_file_context(
        &mut env,
        "def myAdd (a b : Nat) : Nat := a * b\n\
         attribute [implemented_by myAdd] Nat.add\n",
    );
    assert_eq!(verdicts.last(), Some(&Err(IMPORTED_NAT_ADD.to_string())));
    assert_eq!(bound_str(&env, "Nat.add"), None);
}

/// A `namespace` block elaborated without a `FileContext` builds a temporary
/// one; a declaration added before the block is still the run's own. Clean
/// refused the command because the temporary context had recorded nothing.
#[test]
fn test_implemented_by_command_in_namespace_block_without_file_context() {
    let mut env = Environment::with_prelude();
    let verdicts = run_without_file_context(
        &mut env,
        "def fast (n : Nat) : Nat := n + 1\n\
         def slow (n : Nat) : Nat := n + 2\n\
         namespace N\n\
         attribute [implemented_by fast] slow\n\
         end N\n",
    );
    assert!(verdicts.iter().all(Result::is_ok), "{verdicts:?}");
    assert_eq!(bound_str(&env, "slow").as_deref(), Some("fast"));
}

/// Header-first batch elaboration (Trust's island lane,
/// `module_batch::elaborate_module`): a declaration of the batch is the
/// batch's own, so the command may name it. Clean refused it (each node's
/// lexical snapshot recorded nothing). A prelude constant is still refused.
#[test]
fn test_implemented_by_command_in_module_batch_names_batch_decl() {
    use crate::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
    let run = |env: &mut Environment, src: &str| {
        let mut file_ctx = crate::FileContext::new();
        let decls = clean_parser::parse_file(src).expect("the fixture parses");
        let units = [SourceUnit {
            id: UnitId(0),
            decls: &decls,
        }];
        elaborate_module(env, &mut file_ctx, &units, BatchOptions::islands()).render_rejections()
    };
    let mut env = Environment::with_prelude();
    let report = run(
        &mut env,
        "def fast (n : Nat) : Nat := n + 1\n\
         def slow (n : Nat) : Nat := n + 2\n\
         attribute [implemented_by fast] slow\n",
    );
    assert!(report.is_empty(), "{report}");
    assert_eq!(bound_str(&env, "slow").as_deref(), Some("fast"));

    let mut env = Environment::with_prelude();
    let report = run(
        &mut env,
        "def myAdd (a b : Nat) : Nat := a * b\n\
         attribute [implemented_by myAdd] Nat.add\n",
    );
    assert!(report.contains(IMPORTED_NAT_ADD), "{report}");
    assert_eq!(bound_str(&env, "Nat.add"), None);
}

/// `attribute [extern]` is a parametric attribute too
/// (`Lean/Compiler/ExternAttr.lean`), so Lean refuses it on a declaration of
/// an imported module (measured: `attribute [extern "clean_no_such_sym"]
/// Nat.add`, rc 1, this text). Clean registered it, binding a symbol to a
/// prelude constant. The run's own declaration may still be bound.
#[test]
fn test_extern_command_on_imported_decl_refused() {
    let (env, verdicts) =
        run_modules_env_messages(&["attribute [extern \"clean_no_such_sym\"] Nat.add\n"]);
    assert_eq!(
        verdicts.iter().find_map(|(_, v)| v.as_ref().err()),
        Some(
            &"Cannot add attribute `[extern]` to declaration `Nat.add` because it is in an \
              imported module"
                .to_string()
        ),
        "{verdicts:?}"
    );
    assert_eq!(env.get_extern(&Name::from_string("Nat.add")), None);

    let (env, verdicts) = run_modules_env_messages(&[
        "def bump (n : Nat) : Nat := n + 1\n",
        "attribute [extern \"clean_no_such_sym\"] bump\n",
    ]);
    assert!(
        verdicts.iter().any(|(_, v)| v
            .as_ref()
            .is_err_and(|e| e.contains("declaration `bump` because it is in an imported module"))),
        "{verdicts:?}"
    );
    assert_eq!(env.get_extern(&Name::from_string("bump")), None);

    let env = accepted(
        "def bump (n : Nat) : Nat := n + 1\n\
         attribute [extern \"clean_no_such_sym\"] bump\n",
    );
    assert_eq!(
        env.get_extern(&Name::from_string("bump"))
            .map(String::as_str),
        Some("clean_no_such_sym")
    );
}

/// The first error elaborating `src` (module `M0`) as the driver returns it:
/// the typed `ElabError`, never a rendering.
fn first_error(src: &str) -> crate::ElabError {
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    file_ctx.set_main_module(Name::from_string("M0"));
    for decl in &clean_parser::parse_file(src).expect("the fixture parses") {
        let processed = crate::preprocess_decl_with_context(decl, &mut file_ctx);
        match crate::elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Err(err) => return err,
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                if let Some(error) = leaves.into_iter().find_map(|leaf| match leaf {
                    ElabResult::Failed { error, .. } => Some(error.clone()),
                    _ => None,
                }) {
                    return *error;
                }
            }
        }
    }
    panic!("pinned Lean refuses this file; Clean accepted it:\n{src}");
}

/// A refusal from real elaboration carries the typed variant and defect a
/// caller can match on (`ElabError::InvalidImplementedBy`), not only Lean's
/// text.
#[test]
fn test_implemented_by_refusal_is_typed_from_elaboration() {
    use crate::{ElabError, ImplementedByDefect};
    match first_error(
        "def fast (n : Nat) : Nat := n + 1\n\
         namespace Foo\n\
         def fast (n : Nat) : Nat := n + 3\n\
         end Foo\n\
         open Foo\n\
         @[implemented_by fast]\n\
         def slow (n : Nat) : Nat := n + 2\n",
    ) {
        ElabError::InvalidImplementedBy {
            decl,
            target,
            defect: ImplementedByDefect::Ambiguous(candidates),
        } => {
            assert_eq!(decl, Name::from_string("slow"));
            assert_eq!(target, "fast");
            assert_eq!(
                candidates,
                vec![Name::from_string("Foo.fast"), Name::from_string("fast")]
            );
        }
        other => panic!("expected the typed ambiguity, got {other:?}"),
    }
    match first_error(
        "def myAdd (a b : Nat) : Nat := a * b\n\
         attribute [implemented_by myAdd] Nat.add\n",
    ) {
        ElabError::InvalidImplementedBy {
            decl,
            defect: ImplementedByDefect::ImportedDeclaration,
            ..
        } => assert_eq!(decl, Name::from_string("Nat.add")),
        other => panic!("expected the typed imported-declaration refusal, got {other:?}"),
    }
    match first_error("@[implemented_by later]\ndef slow (n : Nat) : Nat := n + 2\n") {
        ElabError::InvalidImplementedBy {
            target,
            defect: ImplementedByDefect::UnknownConstant,
            ..
        } => assert_eq!(target, "later"),
        other => panic!("expected the typed unknown constant, got {other:?}"),
    }
}

/// The ORDER record of a late `attribute [implemented_by]` command lands in
/// the environment whatever the driver, so every lane that compiles from it
/// sees the hazard: without a `FileContext` (Trust's bridge) and in a
/// header-first batch (Trust's island lane) as with one. It used to live in
/// the `FileContext`: absent without one, and in a batch left in a node's
/// lexical snapshot.
#[test]
fn test_implemented_by_order_record_lands_in_the_environment() {
    const LATE: &str = "def fast (n : Nat) : Nat := n + 1\n\
                        def slow (n : Nat) : Nat := n + 2\n\
                        def caller (n : Nat) : Nat := slow n\n\
                        attribute [implemented_by fast] slow\n";
    let recorded = |env: &Environment| -> Vec<(String, String)> {
        let mut found: Vec<(String, String)> = clean_compiler::implemented_by_order(env)
            .into_iter()
            .flatten()
            .map(|(referrer, why)| (referrer.to_string(), why.rebound.to_string()))
            .collect();
        found.sort();
        found
    };
    // `caller` reaches `slow`, and `slow`'s own code (not `@[noinline]`)
    // came before the command too (`own_code_before_binding`).
    let want = vec![
        ("caller".to_string(), "slow".to_string()),
        ("slow".to_string(), "slow".to_string()),
    ];

    let mut env = Environment::with_prelude();
    let verdicts = run_without_file_context(&mut env, LATE);
    assert!(verdicts.iter().all(Result::is_ok), "{verdicts:?}");
    assert_eq!(recorded(&env), want, "without a file context");

    use crate::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    let decls = clean_parser::parse_file(LATE).expect("the fixture parses");
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let report = elaborate_module(&mut env, &mut file_ctx, &units, BatchOptions::islands())
        .render_rejections();
    assert!(report.is_empty(), "{report}");
    assert_eq!(recorded(&env), want, "in a header-first batch");

    let env = accepted(LATE);
    assert_eq!(recorded(&env), want, "with a file context");
}
