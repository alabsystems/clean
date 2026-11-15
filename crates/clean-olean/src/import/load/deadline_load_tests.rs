// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A load under its caller's deadline (`clean_kernel::tc::run_until`) stops
//! once the deadline has passed, and the module cache it fills holds only
//! modules decoded whole (`super::super::deadline`).

use super::*;
use crate::{ModuleCache, OleanExporter};
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::tc::run_until;
use clean_kernel::{Declaration, Expr};
use std::path::Path;
use std::time::Instant;

/// A chain of `modules` modules in `dir`, `Chain<i>` importing `Chain<i-1>`,
/// each declaring `axioms` axioms `Chain<i>.ax<k> : Prop`. Returns the root's
/// name.
fn chain(dir: &Path, modules: usize, axioms: usize) -> String {
    for i in 0..modules {
        let mut env = Environment::default();
        for k in 0..axioms {
            env.add_decl_unchecked(Declaration::Axiom {
                name: Name::from_string(&format!("Chain{i}.ax{k}")),
                level_params: vec![],
                type_: Expr::prop(),
            });
        }
        let previous = format!("Chain{}", i.saturating_sub(1));
        let imports: Vec<(&str, bool)> = if i == 0 {
            vec![]
        } else {
            vec![(previous.as_str(), false)]
        };
        let bytes = OleanExporter::export_with_env(
            &env,
            &imports,
            &[],
            "0000000000000000000000000000000000000000",
        )
        .expect("export a chain module");
        std::fs::write(dir.join(format!("Chain{i}.olean")), bytes).expect("write a chain module");
    }
    format!("Chain{}", modules - 1)
}

/// What a load of the chain registered: each chain constant and its type.
fn chain_constants(env: &Environment) -> Vec<(String, String)> {
    let mut constants: Vec<(String, String)> = env
        .constants()
        .map(|c| (c.name.to_string(), format!("{:?}", c.type_)))
        .filter(|(name, _)| name.starts_with("Chain"))
        .collect();
    constants.sort();
    constants
}

/// A load whose deadline had passed read every module, decoded each into the
/// cache and registered every declaration, and only its caller's `run_until`
/// dropped the result. It stops before reading the first module now, and the
/// cache stays empty. Without a deadline nothing changes.
#[test]
fn a_load_past_its_deadline_reads_nothing_and_caches_nothing() {
    let dir = tempfile::tempdir().expect("a scratch directory");
    let root = chain(dir.path(), 3, 2);
    let search = [dir.path().to_path_buf()];
    let cache = ModuleCache::new();

    let mut env = Environment::default();
    let mut stopped = None;
    let finished = run_until(Some(Instant::now()), || {
        stopped = Some(matches!(
            load_module_with_deps_cached(&mut env, &root, &search, &cache),
            Err(ImportError::Interrupted)
        ));
    });
    assert_eq!(finished, None, "the load ran past its deadline unnoticed");
    assert_eq!(stopped, Some(true), "the load did not stop at its deadline");
    assert!(
        cache.is_empty(),
        "a load past its deadline filled the cache"
    );
    assert!(chain_constants(&env).is_empty());

    let mut env = Environment::default();
    load_module_with_deps_cached(&mut env, &root, &search, &cache)
        .expect("a load with no deadline");
    assert_eq!(cache.len(), 3);
    assert_eq!(chain_constants(&env).len(), 6);
}

/// The recursive loader stops before each module as well.
#[test]
fn the_recursive_loader_stops_at_its_deadline() {
    let dir = tempfile::tempdir().expect("a scratch directory");
    let root = chain(dir.path(), 3, 2);
    let search = [dir.path().to_path_buf()];
    let mut env = Environment::default();
    let mut stopped = None;
    let finished = run_until(Some(Instant::now()), || {
        stopped = Some(matches!(
            load_module_with_deps(&mut env, &root, &search),
            Err(ImportError::Interrupted)
        ));
    });
    assert_eq!(finished, None);
    assert_eq!(stopped, Some(true));
    assert!(chain_constants(&env).is_empty());
}

/// A load cut anywhere leaves the cache consistent: whatever it put there was
/// decoded whole, so a load from that cache registers exactly what a load
/// from an empty one does. The cut is swept from the start of the load to past
/// its end, in steps of a sixteenth of the time a whole load takes.
#[test]
fn a_load_cut_anywhere_leaves_the_cache_holding_whole_modules() {
    let dir = tempfile::tempdir().expect("a scratch directory");
    let root = chain(dir.path(), 24, 150);
    let search = [dir.path().to_path_buf()];

    let mut reference = Environment::default();
    let began = Instant::now();
    load_module_with_deps_cached(&mut reference, &root, &search, &ModuleCache::new())
        .expect("a load with no deadline");
    let whole = began.elapsed();
    let reference = chain_constants(&reference);
    assert_eq!(reference.len(), 24 * 150);

    let mut cut = 0;
    for step in 0..=24u32 {
        let cache = ModuleCache::new();
        let mut env = Environment::default();
        let offset = whole.mul_f64(f64::from(step) / 16.0);
        let deadline = Instant::now().checked_add(offset);
        let finished = run_until(deadline, || {
            load_module_with_deps_cached(&mut env, &root, &search, &cache)
        });
        if !matches!(finished, Some(Ok(_))) {
            cut += 1;
        }
        let mut again = Environment::default();
        load_module_with_deps_cached(&mut again, &root, &search, &cache)
            .unwrap_or_else(|e| panic!("step {step}: a load from what the cut left: {e}"));
        assert_eq!(
            chain_constants(&again),
            reference,
            "step {step}: the cache the cut left made a different load"
        );
        assert!(cache.len() <= 24);
    }
    assert!(cut >= 1, "no load was cut: the sweep tested nothing");
}
