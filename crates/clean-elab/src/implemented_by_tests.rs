// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The order record of `attribute [implemented_by]` ([`compiled_before_binding`])
//! and the typed refusal.

use std::collections::{HashMap, HashSet};

use clean_kernel::expr::UsedConstants;
use clean_kernel::{ConstantKind, Environment, Name};

use super::*;
use crate::test_support::file_verdicts::run_file_env_context;

/// The ORDER record the file left in its environment
/// (`clean_compiler::implemented_by_order`), empty when there is none.
fn order_record(env: &Environment) -> HashMap<Name, CompiledBefore> {
    env.compiled_before_record().cloned().unwrap_or_default()
}

/// `compiled_before_binding` over `rebound`, as (referrer, rebound
/// declaration, the constant it reaches it through) strings.
fn recorded_before(env: &Environment, rebound: &str) -> Vec<(String, String, String)> {
    let rebound = HashSet::from([Name::from_string(rebound)]);
    compiled_before_binding(env, &rebound)
        .into_iter()
        .map(|(referrer, why)| {
            (
                referrer.to_string(),
                why.rebound.to_string(),
                why.via.to_string(),
            )
        })
        .collect()
}

fn all_accepted(verdicts: &[(String, Result<(), String>)]) {
    assert!(verdicts.iter().all(|(_, v)| v.is_ok()), "{verdicts:?}");
}

/// What a command binding `slow` would come too late for: every constant
/// already added whose value reaches `slow`, by a reference or through a
/// chain, a `where` helper included. Never a theorem (a proof never runs),
/// never `slow`, and never a constant bound into it (neither runs its value
/// once the command binds).
#[test]
fn test_compiled_before_binding_names_earlier_code_only() {
    let (env, _, verdicts) = run_file_env_context(
        "def fast (n : Nat) : Nat := n + 1\n\
         def slow (n : Nat) : Nat := n + 2\n\
         @[implemented_by slow] def viaChain (n : Nat) : Nat := n + 3\n\
         def caller (n : Nat) : Nat := slow n\n\
         def chainCaller (n : Nat) : Nat := viaChain n\n\
         def outer (n : Nat) : Nat := go n\n  \
         where go (k : Nat) : Nat := slow k\n\
         theorem slow_one : slow 1 = 3 := rfl\n\
         def unrelated (n : Nat) : Nat := fast n\n",
    );
    all_accepted(&verdicts);
    let found = recorded_before(&env, "slow");
    for (referrer, via) in [
        ("caller", "slow"),
        ("chainCaller", "viaChain"),
        ("outer.go", "slow"),
        ("outer", "outer.go"),
    ] {
        assert!(
            found.contains(&(referrer.to_string(), "slow".to_string(), via.to_string())),
            "`{referrer}` reaches `slow` through `{via}` and was added first: {found:?}"
        );
    }
    for absent in ["slow", "viaChain", "slow_one", "unrelated", "fast"] {
        assert!(
            found.iter().all(|(referrer, _, _)| referrer != absent),
            "`{absent}` must not be recorded: {found:?}"
        );
    }
}

/// The record is TRANSITIVE: code that reaches a rebound declaration only
/// through other earlier code (a caller's caller, a user of an instance whose
/// field is the rebound declaration) is recorded too. The native path
/// rewrites a value before its walk (`clean_native`'s monad-instance
/// inlining), so a record of direct references alone would miss `useBind`.
#[test]
fn test_compiled_before_binding_is_transitive() {
    let (env, _, verdicts) = run_file_env_context(
        "def fast (n : Nat) : Nat := n + 1\n\
         def slow (n : Nat) : Nat := n + 2\n\
         def caller (n : Nat) : Nat := slow n\n\
         def callerCaller (n : Nat) : Nat := caller n\n\
         structure Box (α : Type) where\n  \
         val : α\n  \
         tag : Nat\n\
         def slowBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 2⟩\n\
         def fastBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 1⟩\n\
         instance instBindBox : Bind Box := ⟨slowBind⟩\n\
         def useBind (n : Nat) : Nat := (Box.mk n 0 >>= fun k => Box.mk k 0).tag\n\
         def useUse (n : Nat) : Nat := useBind n\n",
    );
    all_accepted(&verdicts);
    let found = recorded_before(&env, "slow");
    assert!(
        found.contains(&(
            "callerCaller".to_string(),
            "slow".to_string(),
            "caller".to_string()
        )),
        "{found:?}"
    );
    for absent in ["useBind", "instBindBox", "fast"] {
        assert!(
            found.iter().all(|(referrer, _, _)| referrer != absent),
            "`{absent}` must not be recorded for `slow`: {found:?}"
        );
    }
    let found = recorded_before(&env, "slowBind");
    for (referrer, via) in [
        ("instBindBox", "slowBind"),
        ("useBind", "instBindBox"),
        ("useUse", "useBind"),
    ] {
        assert!(
            found.contains(&(
                referrer.to_string(),
                "slowBind".to_string(),
                via.to_string()
            )),
            "`{referrer}` reaches `slowBind` through `{via}`: {found:?}"
        );
    }
    for absent in ["slowBind", "fastBind", "caller", "Box.mk"] {
        assert!(
            found.iter().all(|(referrer, _, _)| referrer != absent),
            "`{absent}` must not be recorded for `slowBind`: {found:?}"
        );
    }
}

/// `attr_implemented_by_order_chain`: the command rebinds `middle`, a link
/// of `slow`'s chain. `caller` is recorded through `slow`; `slow` itself is
/// not (its own chain runs `middle`, never its value). `middle`'s own code
/// is recorded for itself: it is not `@[noinline]`, so Lean may have copied
/// its pre-binding body into later callers (`own_code_before_binding`).
#[test]
fn test_compiled_before_binding_skips_rebound_chain() {
    let (env, _, verdicts) = run_file_env_context(
        "def fastest (n : Nat) : Nat := n + 1\n\
         def middle (n : Nat) : Nat := n + 2\n\
         @[implemented_by middle] def slow (n : Nat) : Nat := n + 3\n\
         @[noinline] def caller (n : Nat) : Nat := slow n\n\
         attribute [implemented_by fastest] middle\n\
         def after (n : Nat) : Nat := caller n\n",
    );
    all_accepted(&verdicts);
    let record = order_record(&env);
    let caller = record
        .get(&Name::from_string("caller"))
        .unwrap_or_else(|| panic!("`caller` must be recorded: {record:?}"));
    assert_eq!(caller.rebound, Name::from_string("middle"));
    assert_eq!(caller.via, Name::from_string("slow"));
    let middle = record
        .get(&Name::from_string("middle"))
        .unwrap_or_else(|| panic!("`middle`'s own code must be recorded: {record:?}"));
    assert_eq!(
        (&middle.rebound, &middle.via),
        (&Name::from_string("middle"), &Name::from_string("middle"))
    );
    assert_eq!(record.len(), 2, "{record:?}");
    for absent in ["slow", "fastest", "after"] {
        assert!(
            !record.contains_key(&Name::from_string(absent)),
            "`{absent}` must not be recorded: {record:?}"
        );
    }
}

/// The environment's record holds only what was added BEFORE the command:
/// `after`, added after it, is not recorded, and a binding written on the
/// declaration records nothing. The rebound declaration's own code was
/// added before the command too, and is recorded for itself unless it is
/// `@[noinline]` (`own_code_before_binding`: Lean's inliner copies it into
/// later callers).
#[test]
fn test_file_record_holds_only_code_added_before_the_command() {
    let (env, _, verdicts) = run_file_env_context(
        "def fast (n : Nat) : Nat := n + 1\n\
         def slow (n : Nat) : Nat := n + 2\n\
         def caller (n : Nat) : Nat := slow n\n\
         attribute [implemented_by fast] slow\n\
         def after (n : Nat) : Nat := caller n\n",
    );
    all_accepted(&verdicts);
    assert_eq!(
        env.get_implemented_by(&Name::from_string("slow")),
        Some(&Name::from_string("fast"))
    );
    let record = order_record(&env);
    assert_eq!(record.len(), 2, "{record:?}");
    let caller = &record[&Name::from_string("caller")];
    assert_eq!(caller.rebound, Name::from_string("slow"));
    assert_eq!(caller.via, Name::from_string("slow"));
    let slow = &record[&Name::from_string("slow")];
    assert_eq!(
        (&slow.rebound, &slow.via),
        (&Name::from_string("slow"), &Name::from_string("slow"))
    );

    let (env, _, verdicts) = run_file_env_context(
        "def fast (n : Nat) : Nat := n + 1\n\
         @[implemented_by fast] def slow (n : Nat) : Nat := n + 2\n\
         def caller (n : Nat) : Nat := slow n\n\
         @[noinline] def slow2 (n : Nat) : Nat := n + 2\n\
         attribute [implemented_by fast] slow2\n\
         def after (n : Nat) : Nat := caller n + slow2 n\n",
    );
    all_accepted(&verdicts);
    assert!(
        env.compiled_before_record().is_none(),
        "nothing added before a command reaches what it binds: {:?}",
        order_record(&env)
    );

    // The same without `@[noinline]`: `slow2`'s own code is recorded.
    let (env, _, verdicts) = run_file_env_context(
        "def fast (n : Nat) : Nat := n + 1\n\
         def slow2 (n : Nat) : Nat := n + 2\n\
         attribute [implemented_by fast] slow2\n\
         def after (n : Nat) : Nat := slow2 n\n",
    );
    all_accepted(&verdicts);
    let record = order_record(&env);
    assert_eq!(
        record.keys().map(ToString::to_string).collect::<Vec<_>>(),
        ["slow2"],
        "{record:?}"
    );
}

/// A `@[macro_inline]` declaration's binding is validated and not
/// registered, on the declaration or by the command, so every reference
/// compiles the body Lean expands (`binding_applies`), and nothing is
/// recorded. A target Lean refuses is still refused.
#[test]
fn test_macro_inline_binding_is_validated_and_not_registered() {
    let (env, _, verdicts) = run_file_env_context(
        "def fast (n : Nat) : Nat := n + 1\n\
         @[macro_inline, implemented_by fast] def slow (n : Nat) : Nat := n + 2\n\
         @[macro_inline] def slow2 (n : Nat) : Nat := n + 2\n\
         def caller (n : Nat) : Nat := slow2 n\n\
         attribute [implemented_by fast] slow2\n",
    );
    all_accepted(&verdicts);
    for decl in ["slow", "slow2"] {
        assert!(
            !env.has_implemented_by(&Name::from_string(decl)),
            "`{decl}` is `@[macro_inline]`"
        );
    }
    assert!(
        env.compiled_before_record().is_none(),
        "{:?}",
        order_record(&env)
    );

    let (_, _, verdicts) = run_file_env_context(
        "@[macro_inline, implemented_by noSuchTarget] def slow (n : Nat) : Nat := n + 2\n",
    );
    assert!(
        verdicts.iter().any(|(_, v)| v
            .as_ref()
            .is_err_and(|e| e.contains("Unknown constant `noSuchTarget`"))),
        "{verdicts:?}"
    );
}

/// The refusal is typed (`ElabError::InvalidImplementedBy`) and displays
/// Lean's text, with no `Unknown identifier:` lead of the string-typed error
/// it replaced.
#[test]
fn test_implemented_by_error_is_typed_and_displays_lean_text() {
    let (_, _, verdicts) = run_file_env_context(
        "def fast (n : Nat) : Nat := n + 1\n\
         @[implemented_by fast] def slow (n : Nat) : Nat := n + 2\n",
    );
    all_accepted(&verdicts);
    let err = ElabError::InvalidImplementedBy {
        decl: Name::from_string("slow"),
        target: "fast".to_string(),
        defect: ImplementedByDefect::Ambiguous(vec![
            Name::from_string("Foo.fast"),
            Name::from_string("fast"),
        ]),
    };
    assert_eq!(
        err.to_string(),
        "ambiguous identifier ``fast`, possible interpretations: [Foo.fast, fast]"
    );
    let unknown = ElabError::InvalidImplementedBy {
        decl: Name::from_string("slow"),
        target: "later".to_string(),
        defect: ImplementedByDefect::UnknownConstant,
    };
    assert_eq!(unknown.to_string(), "Unknown constant `later`");
    let mismatch = ElabError::InvalidImplementedBy {
        decl: Name::from_string("slow"),
        target: "fast".to_string(),
        defect: ImplementedByDefect::TypeMismatch {
            target_type: "Int → Int".to_string(),
            decl_type: "Nat → Nat".to_string(),
        },
    };
    assert_eq!(
        mismatch.to_string(),
        "Invalid `implemented_by` argument `fast`: `fast` has type\n  Int → Int\nbut `slow` has type\n  Nat → Nat"
    );
}

/// The first rebound declaration `name`'s `@[implemented_by]` chain reaches
/// (it, its target, …), or a recorded constant's: the reference walk the
/// kernel's scan uses, restated for the rescan below.
fn chain_reaches(
    env: &Environment,
    rebound: &HashSet<Name>,
    recorded: &HashMap<Name, CompiledBefore>,
    name: &Name,
) -> Option<Name> {
    let mut visited: HashSet<&Name> = HashSet::new();
    let mut current = name;
    loop {
        if rebound.contains(current) {
            return Some(current.clone());
        }
        if let Some(why) = recorded.get(current) {
            return Some(why.rebound.clone());
        }
        if !visited.insert(current) {
            return None;
        }
        current = env.get_implemented_by(current)?;
    }
}

/// The record as a rescan of EVERY constant per round computes it: the
/// definition `Environment::compiled_before_binding` documents, kept here as
/// the reference its one-scan worklist is held to.
fn compiled_before_binding_by_rescan(
    env: &Environment,
    rebound: &HashSet<Name>,
) -> Vec<(Name, CompiledBefore)> {
    let unrecorded = HashMap::new();
    let mut recorded: HashMap<Name, CompiledBefore> = HashMap::new();
    loop {
        let mut round = Vec::new();
        for info in env.constants() {
            if info.kind == ConstantKind::Theorem || recorded.contains_key(&info.name) {
                continue;
            }
            let Some(value) = &info.value else {
                continue;
            };
            if chain_reaches(env, rebound, &unrecorded, &info.name).is_some() {
                continue;
            }
            let mut used = HashSet::new();
            value.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
            let reached = used
                .iter()
                .filter_map(|name| {
                    chain_reaches(env, rebound, &recorded, name).map(|rebound| CompiledBefore {
                        rebound,
                        via: name.clone(),
                    })
                })
                .min_by_key(|why| (why.rebound.to_string(), why.via.to_string()));
            if let Some(why) = reached {
                round.push((info.name.clone(), why));
            }
        }
        if round.is_empty() {
            break;
        }
        recorded.extend(round);
    }
    let mut found: Vec<(Name, CompiledBefore)> = recorded.into_iter().collect();
    found.sort_by_key(|(referrer, _)| referrer.to_string());
    found
}

/// The one-scan worklist records exactly what the per-round rescan records,
/// `why` included, over chains through RECORDED constants (`viaRecorded`
/// runs `a`, recorded one round earlier), a deep caller chain, a cycle of
/// bindings, a `where` helper, an instance field and several declarations
/// rebound at once. Every case records something (no vacuous agreement).
#[test]
fn test_compiled_before_binding_matches_the_per_round_rescan() {
    let deep: String = (1..12)
        .map(|k| format!("def d{k} (n : Nat) : Nat := d{} n + 1\n", k - 1))
        .collect();
    let cases: [(String, &[&[&str]]); 4] = [
        (
            "def fast (n : Nat) : Nat := n + 1\n\
             def slow (n : Nat) : Nat := n + 2\n\
             def a (n : Nat) : Nat := slow n\n\
             @[implemented_by a] def viaRecorded (n : Nat) : Nat := n + 5\n\
             def x (n : Nat) : Nat := viaRecorded n\n\
             def y (n : Nat) : Nat := x n + a n\n\
             def other (n : Nat) : Nat := fast n\n\
             def outer (n : Nat) : Nat := go n\n  \
             where go (k : Nat) : Nat := y k\n\
             theorem y_zero : y 0 = y 0 := rfl\n"
                .to_string(),
            &[&["slow"], &["a"], &["viaRecorded"], &["slow", "fast"]],
        ),
        (
            format!(
                "def d0 (n : Nat) : Nat := n\n{deep}\
                 def b (n : Nat) : Nat := n + 7\n\
                 @[implemented_by b] def c (n : Nat) : Nat := d5 n\n\
                 def user (n : Nat) : Nat := c n + d11 n\n"
            ),
            &[&["d0"], &["d5"], &["b"], &["d3", "b"]],
        ),
        (
            "structure Box (α : Type) where\n  \
             val : α\n  \
             tag : Nat\n\
             def slowBind {α β : Type} (x : Box α) (f : α → Box β) : Box β := ⟨(f x.val).val, x.tag + 2⟩\n\
             instance instBindBox : Bind Box := ⟨slowBind⟩\n\
             def useBind (n : Nat) : Nat := (Box.mk n 0 >>= fun k => Box.mk k 0).tag\n\
             def useUse (n : Nat) : Nat := useBind n\n"
                .to_string(),
            &[&["slowBind"], &["useBind"]],
        ),
        (
            // The command closes a cycle of bindings: `a` runs `b`, `b` runs
            // `a`; a walk along either chain stops where it started.
            "def b (n : Nat) : Nat := n + 1\n\
             @[implemented_by b] def a (n : Nat) : Nat := n + 2\n\
             def u (n : Nat) : Nat := a n\n\
             attribute [implemented_by a] b\n\
             def v (n : Nat) : Nat := u n + b n\n"
                .to_string(),
            &[&["a"], &["u"], &["b", "u"]],
        ),
    ];
    for (source, rebound_sets) in &cases {
        let (env, _, verdicts) = run_file_env_context(source);
        all_accepted(&verdicts);
        for names in *rebound_sets {
            let rebound: HashSet<Name> = names.iter().map(|n| Name::from_string(n)).collect();
            let worklist = compiled_before_binding(&env, &rebound);
            let rescan = compiled_before_binding_by_rescan(&env, &rebound);
            assert!(!rescan.is_empty(), "{names:?} records nothing:\n{source}");
            assert_eq!(worklist, rescan, "{names:?} over:\n{source}");
        }
    }
}
