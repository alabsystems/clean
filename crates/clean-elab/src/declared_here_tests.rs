// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A driver that elaborates a prelude once and hands every consumer a copy
//! of the context (Trust's temporal lanes keep the pair in a per-thread
//! cache, `fresh_temporal_prelude_context`) gives each copy its own run with
//! [`crate::FileContext::fork_run`]. The prelude's declarations are then
//! imported to the consumer, as a module's are in Lean, and the command form
//! on one is refused with Lean's text. A plain clone stays in the prelude's
//! run, as a lexical snapshot must (`module_batch`), so there the command
//! binds the prelude's declaration.

use clean_kernel::{Environment, Name};

use crate::{ElabResult, FileContext};

const PRELUDE: &str = "def preludeSlow (n : Nat) : Nat := n + 2\n";

/// `src` elaborated into `env` with `file_ctx`, each error as a user reads it.
fn run(env: &mut Environment, file_ctx: &mut FileContext, src: &str) -> Vec<Result<(), String>> {
    clean_parser::parse_file(src)
        .expect("the fixture parses")
        .iter()
        .map(|decl| {
            let processed = crate::preprocess_decl_with_context(decl, file_ctx);
            let result = crate::elaborate_decl_and_register_with_context(env, &processed, file_ctx)
                .map_err(|err| err.to_string())?;
            let mut leaves = Vec::new();
            result.leaf_decls(&mut leaves);
            match leaves.into_iter().find_map(|leaf| match leaf {
                ElabResult::Failed { error, .. } => Some(error.to_string()),
                _ => None,
            }) {
                Some(err) => Err(err),
                None => Ok(()),
            }
        })
        .collect()
}

/// The prelude elaborated once, as the cache holds it.
fn cached_prelude() -> (Environment, FileContext) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let verdicts = run(&mut env, &mut file_ctx, PRELUDE);
    assert!(verdicts.iter().all(Result::is_ok), "{verdicts:?}");
    (env, file_ctx)
}

#[test]
fn test_fork_run_makes_a_cached_prelude_imported() {
    let (prelude_env, prelude_ctx) = cached_prelude();
    for (attr, command) in [
        (
            "implemented_by",
            "attribute [implemented_by fast] preludeSlow\n",
        ),
        (
            "extern",
            "attribute [extern \"clean_no_such_sym\"] preludeSlow\n",
        ),
    ] {
        let src = format!("def fast (n : Nat) : Nat := n + 1\n{command}");

        let mut env = prelude_env.clone();
        let mut consumer = prelude_ctx.fork_run();
        let verdicts = run(&mut env, &mut consumer, &src);
        assert_eq!(
            verdicts.last(),
            Some(&Err(format!(
                "Cannot add attribute `[{attr}]` to declaration `preludeSlow` because it is \
                 in an imported module"
            ))),
            "{attr}: {verdicts:?}"
        );
        assert!(verdicts.first().is_some_and(Result::is_ok), "{verdicts:?}");
        let slow = Name::from_string("preludeSlow");
        assert_eq!(env.get_implemented_by(&slow), None, "{attr}");
        assert_eq!(env.get_extern(&slow), None, "{attr}");

        // The consumer's own declarations are its run's: `fast` may be bound.
        let verdicts = run(
            &mut env,
            &mut consumer,
            "def slower (n : Nat) : Nat := n + 3\nattribute [implemented_by fast] slower\n",
        );
        assert!(verdicts.iter().all(Result::is_ok), "{attr}: {verdicts:?}");

        let mut env = prelude_env.clone();
        let mut snapshot = prelude_ctx.clone();
        let verdicts = run(&mut env, &mut snapshot, &src);
        assert!(
            verdicts.iter().all(Result::is_ok),
            "{attr}, a clone is the same run: {verdicts:?}"
        );
    }
}

/// Two forks of one context are two runs: what one declares is imported to
/// the other.
#[test]
fn test_fork_run_gives_each_consumer_its_own_run() {
    let (prelude_env, prelude_ctx) = cached_prelude();
    let mut env = prelude_env.clone();
    let mut first = prelude_ctx.fork_run();
    let verdicts = run(&mut env, &mut first, "def mine (n : Nat) : Nat := n + 1\n");
    assert!(verdicts.iter().all(Result::is_ok), "{verdicts:?}");

    let mut second = prelude_ctx.fork_run();
    let verdicts = run(
        &mut env,
        &mut second,
        "def fast (n : Nat) : Nat := n + 1\nattribute [implemented_by fast] mine\n",
    );
    assert_eq!(
        verdicts.last(),
        Some(&Err(
            "Cannot add attribute `[implemented_by]` to declaration `mine` because it is in \
             an imported module"
                .to_string()
        )),
        "{verdicts:?}"
    );
}
