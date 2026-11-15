// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A catch-all arm's right-hand side is elaborated ONCE per `match` (gap G76,
//! ledger class (146), `infer/elab_match/shared_alt.rs`), through the
//! elaborator's production entry (`elaborate_decl_and_register`: elaborate,
//! then the full kernel check).
//!
//! The constructor-ordered `casesOn` builder used to elaborate a trailing
//! `| _ => rhs` / `| x => rhs` once for every constructor it covers, so `k`
//! nested catch-all matches over a `c`-constructor type cost `(c - 2)^k`
//! elaborations: trust-ir `Pred.impliesFuel` (`TrustIr/Pred.lean:532`) ran past
//! 1800 s, and the depth-5 `nest` below took 104 s on the integ/r5 `cf329c127`
//! release binary (depth 4: 1.8 s; depth 6: killed after 564 s). Pinned Lean
//! 4.8.0 checks every file here in under 0.4 s.
//!
//! The field-leak control and the `Pred` shape are in
//! `match_catch_all_sharing_pred.rs`.
//!
//! Every value below is the pinned Lean 4.8.0 binary's (checked 2026-10-16:
//! it accepts each `rfl` / `decide` / `simp` and refuses each FALSE claim).
//! `walk` was checked as a `noncomputable def`: Lean 4.8.0's ELABORATOR is
//! linear on it (0.06 s at depth 10), but its old code generator inlines the
//! matchers and is itself exponential there (41 s at depth 6), which says
//! nothing about elaboration; `clean check` generates no code.

use super::*;
use std::sync::mpsc;
use std::time::Duration;

pub(super) fn register(env: &mut Environment, src: &str) -> Result<(), ElabError> {
    let decl = parse_decl_for_elab(src)?;
    crate::elaborate_decl_and_register(env, &decl).map(|_| ())
}

pub(super) fn register_ok(env: &mut Environment, src: &str) {
    if let Err(err) = register(env, src) {
        panic!("should elaborate and kernel-check:\n{src}\n{err:?}");
    }
}

/// Refused, and not registered.
pub(super) fn refused(env: &mut Environment, name: &str, src: &str) {
    assert!(register(env, src).is_err(), "must be refused:\n{src}");
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "the refused `{name}` must not be registered"
    );
}

const K: &str = "inductive K where\n  | a | b | c | d | e | f | g | h";

const STEP: &str = "def step : K → K\n  | .a => .b | .b => .c | .c => .d | .d => .e\n  | .e => .f | .f => .g | .g => .h | .h => .a";

/// `depth` nested matches alternating on `x` and `y`, each with two
/// constructor arms and a wildcard catch-all over the other six constructors.
fn nest_source(depth: usize) -> String {
    let mut out = String::from("def nest (x y : K) : Nat :=\n");
    for level in 0..depth {
        let pad = "  ".repeat(1 + 2 * level);
        let var = if level % 2 == 0 { "x" } else { "y" };
        out.push_str(&format!("{pad}match {var} with\n"));
        out.push_str(&format!("{pad}| .a => {}\n", level * 10 + 1));
        out.push_str(&format!("{pad}| .b => {}\n", level * 10 + 2));
        out.push_str(&format!("{pad}| _ =>\n"));
    }
    out.push_str(&format!("{}1000\n", "  ".repeat(1 + 2 * depth)));
    out
}

/// `depth` nested matches, each on `step` of the previous NAMED catch-all's
/// binder: `walk x` is the number of `step`s from `x` to `.a`.
fn walk_source(depth: usize) -> String {
    let mut out = String::from("def walk (x : K) : Nat :=\n");
    let mut var = String::from("x");
    for level in 0..depth {
        let pad = "  ".repeat(1 + 2 * level);
        let scrutinee = if level == 0 {
            var.clone()
        } else {
            format!("step {var}")
        };
        let next = format!("k{}", level + 1);
        out.push_str(&format!("{pad}match {scrutinee} with\n"));
        out.push_str(&format!("{pad}| .a => {level}\n"));
        out.push_str(&format!("{pad}| {next} =>\n"));
        var = next;
    }
    out.push_str(&format!("{}100\n", "  ".repeat(1 + 2 * depth)));
    out
}

/// The size of `expr` read as a TREE, counted up to `cap`: what every
/// consumer that walks terms without sharing pays.
fn tree_nodes_capped(expr: &Expr, cap: usize) -> usize {
    let mut count = 0usize;
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        count += 1;
        if count >= cap {
            return cap;
        }
        match e.kind() {
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => stack.push(inner),
            _ => {}
        }
    }
    count
}

/// The number of DISTINCT nodes of `expr` (by address): a right-hand side
/// shared by several minor premises counts once.
fn distinct_nodes(expr: &Expr) -> usize {
    let mut seen: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(e) as usize) {
            continue;
        }
        match e.kind() {
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => stack.push(inner),
            _ => {}
        }
    }
    seen.len()
}

/// The registered value of a measured definition: its distinct nodes, and its
/// tree size (capped at [`TREE_CAP`]).
pub(super) struct ValueSize {
    pub(super) distinct: usize,
    pub(super) tree: usize,
}

const TREE_CAP: usize = 1_000_000;

/// Elaborate `decls` in order into a fresh prelude environment on a worker
/// thread; `Ok` only when every one registers within `bound`, with the size of
/// `measured`'s registered value. The per-split re-elaboration this guards
/// against takes hours at the depths used here (it took 104 s at `nest` depth
/// 5 on a release build, ×6 per level), so a generous bound cannot make the
/// test flaky.
pub(super) fn registers_within(
    decls: Vec<String>,
    measured: &'static str,
    bound: Duration,
) -> Result<ValueSize, String> {
    let (sender, receiver) = mpsc::channel();
    std::thread::Builder::new()
        .name("g76-catch-all-sharing".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut env = Environment::with_prelude();
            let mut outcome = Ok(());
            for src in &decls {
                if let Err(err) = register(&mut env, src) {
                    outcome = Err(format!("{src}\n{err:?}"));
                    break;
                }
            }
            let outcome = outcome.and_then(|()| {
                env.get_const(&Name::from_string(measured))
                    .and_then(|info| info.value.as_ref())
                    .map(|value| ValueSize {
                        distinct: distinct_nodes(value),
                        tree: tree_nodes_capped(value, TREE_CAP),
                    })
                    .ok_or_else(|| format!("`{measured}` has no registered value"))
            });
            let _ = sender.send(outcome);
        })
        .map_err(|err| format!("cannot spawn the worker: {err}"))?;
    match receiver.recv_timeout(bound) {
        Ok(outcome) => outcome,
        Err(_) => Err(format!(
            "did not elaborate within {bound:?}: a catch-all is elaborated per constructor again"
        )),
    }
}

#[test]
fn test_match_nested_wildcard_catch_alls_elaborate_once() {
    // Seven levels: the old builder needed 6^7 ≈ 2.8e5 elaborations of the
    // innermost right-hand side; one per level now.
    let mut decls = vec![K.to_string(), nest_source(7)];
    for (name, args, value) in [
        ("n_cc", ".c .c", "1000"),
        ("n_ac", ".a .c", "1"),
        ("n_bh", ".b .h", "2"),
        ("n_ca", ".c .a", "11"),
        ("n_db", ".d .b", "12"),
        ("n_hh", ".h .h", "1000"),
    ] {
        decls.push(format!("theorem {name} : nest {args} = {value} := rfl"));
    }
    decls.push("theorem n_dec : nest .e .f = 1000 := by decide".to_string());
    let size = match registers_within(decls, "nest", Duration::from_secs(300)) {
        Ok(size) => size,
        Err(err) => panic!("{err}"),
    };
    // One copy of each level's right-hand side, bound once by a `let`: the
    // value is linear in the source as a DAG AND as a tree. Elaborated per
    // constructor it had a distinct copy per path (over 6^7); shared but
    // copied into each minor it was a small DAG with that same tree.
    assert!(
        size.distinct < 4_000,
        "`nest` has {} distinct nodes",
        size.distinct
    );
    assert!(
        size.tree < 8_000,
        "`nest` has a tree of {} nodes",
        size.tree
    );
}

#[test]
fn test_match_nested_wildcard_catch_alls_false_values_refused() {
    let mut env = Environment::with_prelude();
    register_ok(&mut env, K);
    register_ok(&mut env, &nest_source(4));
    refused(
        &mut env,
        "n_false_rfl",
        "theorem n_false_rfl : nest .c .a = 1000 := rfl",
    );
    refused(
        &mut env,
        "n_false_dec",
        "theorem n_false_dec : nest .c .c = 11 := by decide",
    );
}

#[test]
fn test_match_nested_named_catch_alls_compute_lean_values() {
    // Seven levels of `| kᵢ => match step kᵢ with …`: the binder of each
    // catch-all is the next scrutinee's argument (7^7 ≈ 8.2e5 elaborations
    // of the innermost right-hand side before).
    let mut decls = vec![K.to_string(), STEP.to_string(), walk_source(7)];
    for (name, arg, value) in [
        ("w_a", ".a", "0"),
        ("w_h", ".h", "1"),
        ("w_g", ".g", "2"),
        ("w_f", ".f", "3"),
        ("w_e", ".e", "4"),
        ("w_d", ".d", "5"),
        ("w_c", ".c", "6"),
        ("w_b", ".b", "100"),
    ] {
        decls.push(format!("theorem {name} : walk {arg} = {value} := rfl"));
    }
    decls.push("theorem w_dec : walk .d = 5 := by decide".to_string());
    let size = match registers_within(decls, "walk", Duration::from_secs(300)) {
        Ok(size) => size,
        Err(err) => panic!("{err}"),
    };
    assert!(
        size.distinct < 4_000,
        "`walk` has {} distinct nodes",
        size.distinct
    );
    assert!(
        size.tree < 8_000,
        "`walk` has a tree of {} nodes",
        size.tree
    );
}

/// `simp [walk, step]` closes `walk .h = 1` two and three levels deep and
/// refuses `walk .h = 2` at both, as pinned Lean 4.8.0 does (2026-10-25:
/// exit 0 on the true claim at depth 3, "unsolved goals" on each false one).
/// Three levels deep used to trip simp's size budget ("grew the term past"),
/// on integ/r5 `cf329c127` and on integ/r6 through `ae0eaf93d` (simp unfolded
/// `walk` to its whole `casesOn` tree). It closed with the merge of main's
/// RM1 elaborator fixes (R146) into integ/r6, the only change to clean-elab's
/// match or simp code between that run and the next: a catch-all arm is now
/// elaborated once as a join point (`elab_match/join_point.rs`), which runs
/// before this file's shared-`let` lowering, and simp's equation synthesis
/// keeps the join's `let`.
#[test]
fn test_match_named_catch_all_simp_unfolding_matches_base() {
    for depth in [2, 3] {
        let mut env = Environment::with_prelude();
        register_ok(&mut env, K);
        register_ok(&mut env, STEP);
        register_ok(&mut env, &walk_source(depth));
        register_ok(
            &mut env,
            "theorem w_simp : walk .h = 1 := by simp [walk, step]",
        );
        refused(
            &mut env,
            "w_simp_false",
            "theorem w_simp_false : walk .h = 2 := by simp [walk, step]",
        );
    }
}

#[test]
fn test_match_nested_named_catch_alls_false_values_refused() {
    let mut env = Environment::with_prelude();
    register_ok(&mut env, K);
    register_ok(&mut env, STEP);
    register_ok(&mut env, &walk_source(4));
    refused(
        &mut env,
        "w_false_rfl",
        "theorem w_false_rfl : walk .b = 6 := rfl",
    );
    refused(
        &mut env,
        "w_false_dec",
        "theorem w_false_dec : walk .c = 7 := by decide",
    );
}

/// `depth` nested two-discriminant matches whose catch-all row `_, _`
/// overlaps the concrete row diagonally: the column split puts the row's
/// right-hand side under the concrete constructor's group AND the default.
fn diag_source(depth: usize) -> String {
    const CTORS: [&str; 8] = ["a", "b", "c", "d", "e", "f", "g", "h"];
    let mut out = String::from("def diag (x y : K) : Nat :=\n");
    for level in 0..depth {
        let pad = "  ".repeat(1 + 2 * level);
        let (first, second) = (CTORS[level % 8], CTORS[(level + 1) % 8]);
        out.push_str(&format!("{pad}match x, y with\n"));
        out.push_str(&format!("{pad}| .{first}, .{second} => {level}\n"));
        out.push_str(&format!("{pad}| _, _ =>\n"));
    }
    out.push_str(&format!("{}100\n", "  ".repeat(1 + 2 * depth)));
    out
}

#[test]
fn test_match_diagonal_catch_all_rows_elaborate_once() {
    // integ/r5 `cf329c127`: depth 3 took 4.0 s, depth 4 over 120 s. The
    // column split still puts the `_, _` right-hand side at two leaves per
    // level, elaborated apiece (ledger class (146), open), so this pins the
    // values and the per-constructor half only.
    let mut decls = vec![K.to_string(), diag_source(5)];
    for (name, args, value) in [
        ("d_ab", ".a .b", "0"),
        ("d_bc", ".b .c", "1"),
        ("d_cd", ".c .d", "2"),
        ("d_aa", ".a .a", "100"),
        ("d_ef", ".e .f", "4"),
        ("d_cc", ".c .c", "100"),
    ] {
        decls.push(format!("theorem {name} : diag {args} = {value} := rfl"));
    }
    if let Err(err) = registers_within(decls, "diag", Duration::from_secs(300)) {
        panic!("{err}");
    }
    let mut env = Environment::with_prelude();
    register_ok(&mut env, K);
    register_ok(&mut env, &diag_source(3));
    refused(
        &mut env,
        "d_false",
        "theorem d_false : diag .a .b = 100 := rfl",
    );
}
