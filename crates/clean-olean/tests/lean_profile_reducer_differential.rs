// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The differential battery behind rule 0 of the Lean kernel-theory profile
//! (`clean_kernel::env::kernel_theory`): a native reducer fires in
//! `KernelTheory::Lean` only when it is in `LEAN_PROFILE_DIFFERENTIAL_REDUCERS`,
//! and a name is on that list only while this battery shows, over the pinned
//! toolchain's own `Init` `.olean`s, that the reducer fired on its inputs and
//! every result it produced is definitionally equal — in
//! `KernelTheory::LeanReference`, Lean's kernel exactly — to the head applied
//! to the same inputs, at the same type (`clean_olean::test_support::reducer_differential`).
//!
//! Measured 2026-09-24 with the round-1 profile, which admitted any reducer
//! whose head Lean's kernel COULD compute: every `.olean` re-check lane proved
//! `String.drop "abc" 1 = String.drop "xbc" 1` (Lean 4.30's `drop` returns a
//! `String.Slice` that remembers its string, Clean's reducer a `String`
//! literal), and `"\u{3000}x".trimLeft = "x"`, `"Ä".toLower = "ä"` and
//! `"ß".toUpper = "SS"` (Lean's are ASCII-only). This battery refuses all of
//! them, and `BitVec.ofNat` (whose reducer returns a `Nat`).

use std::sync::OnceLock;

use clean_kernel::env::{Environment, LeanTheoryExclusion, LEAN_PROFILE_DIFFERENTIAL_REDUCERS};
use clean_kernel::name::Name;
use clean_olean::test_support::reducer_differential::differential;
use clean_olean::{default_search_paths, load_module_with_deps};

/// The `Init` modules that define every allowlisted head and the refused
/// `String` heads (`Lean.Environment.getModuleIdxFor?` on pinned v4.30.0-rc2).
const MODULES: [&str; 7] = [
    "Init.Data.BitVec.Basic",
    "Init.Data.Bool",
    "Init.Data.Char.Basic",
    "Init.Data.Int.Basic",
    "Init.Data.Nat.Basic",
    "Init.Data.String.TakeDrop",
    "Init.Data.String.Modify",
];

/// The heads Lean 4.30 defines differently from Clean's reducer.
const DISAGREEING: [&str; 7] = [
    "String.drop",
    "String.take",
    "String.trimLeft",
    "String.trimRight",
    "String.toLower",
    "String.toUpper",
    "BitVec.ofNat",
];

fn env() -> &'static Environment {
    static ENV: OnceLock<Environment> = OnceLock::new();
    ENV.get_or_init(|| {
        let mut env = Environment::for_lean_replay();
        let search = default_search_paths();
        for module in MODULES {
            load_module_with_deps(&mut env, module, &search)
                .unwrap_or_else(|e| panic!("load {module}: {e}"));
        }
        env
    })
}

#[test]
fn test_lean_profile_every_admitted_reducer_agrees_with_delta_iota() {
    let env = env();
    for head in LEAN_PROFILE_DIFFERENTIAL_REDUCERS {
        let name = Name::from_string(head);
        assert!(
            env.get_native_reducer(&name).is_some(),
            "`{head}` is on the list but no reducer is registered for it"
        );
        assert_eq!(
            env.lean_theory_exclusion(&name),
            None,
            "`{head}`: rules 1-3 must hold over the pinned `Init`"
        );
        let report = differential(env, &name);
        assert!(
            report.covered(),
            "`{head}` is on the list but the battery does not cover it: {report:?}"
        );
    }
}

#[test]
fn test_lean_profile_battery_refuses_reducers_lean_disagrees_with() {
    let env = env();
    for head in DISAGREEING {
        let name = Name::from_string(head);
        let report = differential(env, &name);
        assert!(
            report.fired > 0 && !report.disagreements.is_empty(),
            "`{head}`: the battery must fire it and find the disagreement: {report:?}"
        );
        assert_eq!(
            env.lean_theory_exclusion(&name),
            Some(LeanTheoryExclusion::NotDifferentiallyChecked),
            "`{head}` must stay off in Lean's theory"
        );
    }
}

/// No non-`Nat` reducer is admitted without being on the list: rule 0 is the
/// only door, whatever the environment holds.
#[test]
fn test_lean_profile_admits_no_unlisted_non_nat_reducer() {
    let env = env();
    let mut admitted = 0usize;
    for name in env.registered_native_reducer_names() {
        if env.lean_theory_exclusion(name).is_some() {
            continue;
        }
        admitted += 1;
        let spelled = name.to_string();
        assert!(
            Environment::is_lean_kernel_nat_extension(name)
                || LEAN_PROFILE_DIFFERENTIAL_REDUCERS.contains(&spelled.as_str()),
            "`{spelled}` is admitted in Lean's theory without a differential battery"
        );
    }
    assert!(admitted >= LEAN_PROFILE_DIFFERENTIAL_REDUCERS.len());
}
