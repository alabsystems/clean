// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R176: strict positivity in one pass, each container slot once per block.
//! The rules as they stood (`1d6aa1926`) are kept verbatim in
//! `tests/reference.rs`. The properties compare the two on generated
//! containers and constructor types; the cost tests measure both, through
//! `crate::term::KIND_READS` and the constructor lists an env hands out, so
//! each one also shows the cost it rules out; `tests/pins.rs` keeps the
//! oracle's reading of a container's parameter.

use std::cell::Cell;

use super::Positivity;
use crate::level::Level;
use crate::minimal_env::MinimalEnv;
use crate::name::Name;
use crate::rawexpr::BinderInfo;
use crate::term::{ConstRef, Term, TermKind, KIND_READS};
use crate::validate::Env;

mod differential;
mod pins;
mod reference;

/// One constructor, a fresh check.
fn check(env: &dyn Env, block: &[Name], ctor: &Term) -> Result<(), ()> {
    Positivity::new(env, block).check_ctor(ctor)
}

/// One constructor, the rules as they stood.
fn check_before(env: &dyn Env, block: &[Name], ctor: &Term) -> Result<(), ()> {
    reference::check_positivity_ctor_block(env, block, ctor)
}

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

fn konst(s: &str) -> Term {
    Term::const_ref(ConstRef::mk_unchecked_levels(n(s), vec![]))
}

fn app(f: Term, a: Term) -> Term {
    Term::app(f, a)
}

fn pi(d: Term, b: Term) -> Term {
    Term::pi(BinderInfo::Default, d, b)
}

fn lam(d: Term, b: Term) -> Term {
    Term::lam(BinderInfo::Default, d, b)
}

fn prop() -> Term {
    Term::sort(Level::zero())
}

fn ty() -> Term {
    Term::sort(Level::succ(Level::zero()))
}

/// `doms[0] → … → ret`.
fn telescope(doms: Vec<Term>, ret: Term) -> Term {
    doms.into_iter().rev().fold(ret, |b, d| pi(d, b))
}

/// Nodes of `t` as a tree, read through the `kind` field rather than
/// `Term::kind`, so counting them reads nothing the cost tests measure.
fn nodes(t: &Term) -> u64 {
    let mut count: u64 = 0;
    let mut stack = vec![t.clone()];
    while let Some(cur) = stack.pop() {
        count = count.saturating_add(1);
        match &*cur.kind {
            TermKind::App(a, b) | TermKind::Lam(_, a, b) | TermKind::Pi(_, a, b) => {
                stack.push(a.clone());
                stack.push(b.clone());
            }
            TermKind::Let(a, b, c) => {
                stack.push(a.clone());
                stack.push(b.clone());
                stack.push(c.clone());
            }
            TermKind::Proj(_, _, a) => stack.push(a.clone()),
            TermKind::BVar(_)
            | TermKind::Sort(_)
            | TermKind::Const(_)
            | TermKind::Elim(_)
            | TermKind::Lit(_) => {}
        }
    }
    count
}

/// `env` with the container `name` of `np` parameters and constructors
/// `ctors` (its type is not read by positivity).
fn with_container(env: MinimalEnv, name: &str, np: u32, ctors: Vec<Term>) -> MinimalEnv {
    let named = ctors
        .into_iter()
        .enumerate()
        .map(|(i, t)| (n(&format!("{name}.c{i}")), t))
        .collect();
    env.with_container_inductive(n(name), 0, np, ty(), false, named)
}

/// `C (α : Type)` with `C.c0 : (α : Type) → α → C α`.
fn c_env() -> MinimalEnv {
    let c0 = telescope(vec![ty(), Term::bvar(0)], app(konst("C"), Term::bvar(1)));
    with_container(MinimalEnv::new(), "C", 1, vec![c0])
}

/// `P.c0 : (α β : Type) → α → β → P α β`, 13 nodes.
fn p_ctor() -> Term {
    telescope(
        vec![ty(), ty(), Term::bvar(1), Term::bvar(1)],
        app(app(konst("P"), Term::bvar(3)), Term::bvar(2)),
    )
}

/// `P (α β : Type)`, covariant in both.
fn p_env() -> MinimalEnv {
    with_container(MinimalEnv::new(), "P", 2, vec![p_ctor()])
}

/// `E.c0 : (α : Type) → nest(d, bottom) → E α`, `bottom` under one binder,
/// where `α` is `BVar(0)`.
fn e_ctor(d: u32, bottom: Term) -> Term {
    telescope(vec![ty(), nest(d, bottom)], app(konst("E"), Term::bvar(1)))
}

/// `P` and `E (α : Type)` with the one constructor `e0`.
fn e_env(e0: Term) -> MinimalEnv {
    with_container(p_env(), "E", 1, vec![e0])
}

/// `K0 (A : Type)` with `K0.c0 : (A : Type) → A → K0 A`, and for `0 < j <= k`
/// `Kj (A : Type)` with `Kj.c0 : (A : Type) → K(j-1) A → … → Kj A`, `uses`
/// fields of `K(j-1) A`.
fn ladder(k: u32, uses: u32) -> MinimalEnv {
    let k0 = telescope(vec![ty(), Term::bvar(0)], app(konst("K0"), Term::bvar(1)));
    let mut env = with_container(MinimalEnv::new(), "K0", 1, vec![k0]);
    for j in 1..=k {
        let below = konst(&format!("K{}", j.saturating_sub(1)));
        let fields = (0..uses).map(|f| app(below.clone(), Term::bvar(f)));
        let ret = app(konst(&format!("K{j}")), Term::bvar(uses));
        let ctor = telescope(std::iter::once(ty()).chain(fields).collect(), ret);
        env = with_container(env, &format!("K{j}"), 1, vec![ctor]);
    }
    env
}

/// `G` joined to height `h` over leaves `Type`: `2^(h + 2) - 3` nodes. `G` is
/// no inductive, and nothing in the tree mentions a block type.
fn g_tree(h: u32) -> Term {
    match h.checked_sub(1) {
        None => ty(),
        Some(below) => app(app(konst("G"), g_tree(below)), g_tree(below)),
    }
}

/// `C (C (… (C D)))`, `d` applications of `C`, `D = g_tree(h)`.
fn chain(d: u32, h: u32) -> Term {
    (0..d).fold(g_tree(h), |t, _| app(konst("C"), t))
}

/// `x (x (… (x D)))`, `d` applications of `BVar(0)`, `D = g_tree(h)`.
fn var_chain(d: u32, h: u32) -> Term {
    (0..d).fold(g_tree(h), |t, _| app(Term::bvar(0), t))
}

/// `P (P (… (P bottom Big) Big) …) Big`, `d` applications of `P`, `Big` a
/// `g_tree(6)` of 253 nodes.
fn nest(d: u32, bottom: Term) -> Term {
    (0..d).fold(bottom, |t, _| app(app(konst("P"), t), g_tree(6)))
}

/// A `MinimalEnv` that counts the constructor lists read from it.
struct CountingEnv<'a> {
    inner: &'a MinimalEnv,
    lists: Cell<u64>,
}

impl<'a> CountingEnv<'a> {
    fn new(inner: &'a MinimalEnv) -> Self {
        CountingEnv {
            inner,
            lists: Cell::new(0),
        }
    }
}

impl Env for CountingEnv<'_> {
    fn num_level_params(&self, name: &Name) -> Option<u32> {
        self.inner.num_level_params(name)
    }
    fn inductive_large_elim(&self, name: &Name) -> Option<bool> {
        self.inner.inductive_large_elim(name)
    }
    fn inductive_num_params(&self, name: &Name) -> Option<u32> {
        self.inner.inductive_num_params(name)
    }
    fn inductive_constructors(&self, name: &Name) -> Option<Vec<(Name, Term)>> {
        self.lists.set(self.lists.get().saturating_add(1));
        self.inner.inductive_constructors(name)
    }
}

/// Which rules a cost is measured on.
#[derive(Clone, Copy)]
enum Rules {
    /// The one pass.
    Now,
    /// The rules before R176 (`reference.rs`).
    Before,
}

/// One check's verdict, its `Term::kind` reads on this thread, and the
/// constructor lists it read.
#[derive(Debug)]
struct Cost {
    verdict: Result<(), ()>,
    reads: u64,
    lists: u64,
}

fn cost(env: &MinimalEnv, block: &[Name], ctor: &Term, rules: Rules) -> Cost {
    let counting = CountingEnv::new(env);
    let start = KIND_READS.with(Cell::get);
    let verdict = match rules {
        Rules::Now => check(&counting, block, ctor),
        Rules::Before => check_before(&counting, block, ctor),
    };
    Cost {
        verdict,
        reads: KIND_READS.with(Cell::get).saturating_sub(start),
        lists: counting.lists.get(),
    }
}

/// What a check reads of `node_count` nodes (the constructor's and each
/// scanned container constructor's), `heads` of them heads that are not
/// constants: each node once, by the pass or by the walk that asks whether it
/// mentions the target, and such a head twice (an application's inner spine
/// nodes not at all).
fn bound(node_count: u64, heads: u64) -> u64 {
    node_count.saturating_add(heads)
}

// ---------------------------------------------------------------------------
// Cost: each figure in a doc comment is what a model of both versions gave.
// ---------------------------------------------------------------------------

/// `C (C (… (C D))) → T`, `d = 1000`, `D` 4,093 nodes: 6,095 nodes, no block
/// type in the chain. Each level walked its argument to ask whether it
/// mentions `T`, then walked it again: 5,135,940 reads, at least `d × |D|`
/// (4,093,000). One pass: 5,072 (6,096 when a leaf's walk read it again).
#[test]
fn test_positivity_container_chain_without_occurrence_reads_each_node_at_most_once() {
    let env = c_env();
    let block = [n("T")];
    let ctor = pi(chain(1000, 10), konst("T"));
    let size = nodes(&ctor);
    assert_eq!(size, 6_095);
    let now = cost(&env, &block, &ctor, Rules::Now);
    let before = cost(&env, &block, &ctor, Rules::Before);
    assert_eq!((now.verdict, before.verdict), (Ok(()), Ok(())));
    assert!(now.reads <= bound(size, 0), "{now:?} for {size} nodes");
    assert!(before.reads >= 4_093_000, "{before:?}");
}

/// `(x : Type → Type) → x (x (… (x D))) → T`, `d = 1000`: 6,099 nodes, the
/// general-application rule at every level. Each level walked every argument
/// to refuse a block type in one, then walked it again: 5,135,944 reads. One
/// pass: 6,076, each variable head read twice (8,101 when a leaf's walk read
/// it again).
#[test]
fn test_positivity_general_application_chain_reads_only_a_variable_head_twice() {
    let env = MinimalEnv::new();
    let block = [n("T")];
    let ctor = telescope(vec![pi(ty(), ty()), var_chain(1000, 10)], konst("T"));
    let size = nodes(&ctor);
    assert_eq!(size, 6_099);
    let now = cost(&env, &block, &ctor, Rules::Now);
    let before = cost(&env, &block, &ctor, Rules::Before);
    assert_eq!((now.verdict, before.verdict), (Ok(()), Ok(())));
    assert!(now.reads <= bound(size, 1_000), "{now:?} for {size} nodes");
    assert!(before.reads >= 4_093_000, "{before:?}");
}

/// `P (P (… (P T Big) Big) …) Big → T`, `d = 200`: 51,203 nodes, `T` at the
/// bottom. Each level's walk to find `T` went through every `Big` below it
/// (at least `253 × 199 × 200 / 2`, 5,034,700), and each level asked the
/// oracle about `P`'s slot 0: 5,422,703 reads, 200 lists. One pass: 38,412
/// reads, slot 0 of `P` scanned once (1 list). With `T → Prop` at the bottom
/// both refuse: 5,422,903 reads and 200 lists before, 403 reads now.
#[test]
fn test_positivity_block_type_deep_in_a_container_chain_reads_each_node_at_most_once() {
    let env = p_env();
    let block = [n("T")];
    let scanned = nodes(&p_ctor());
    assert_eq!(scanned, 13);

    let ctor = pi(nest(200, konst("T")), konst("T"));
    let size = nodes(&ctor);
    assert_eq!(size, 51_203);
    let now = cost(&env, &block, &ctor, Rules::Now);
    let before = cost(&env, &block, &ctor, Rules::Before);
    assert_eq!((now.verdict, before.verdict), (Ok(()), Ok(())));
    assert!(
        now.reads <= bound(size.saturating_add(scanned), 0),
        "{now:?}"
    );
    assert_eq!((now.lists, before.lists), (1, 200));
    assert!(before.reads >= 5_034_700, "{before:?}");

    let ctor = pi(nest(200, pi(konst("T"), prop())), konst("T"));
    let now = cost(&env, &block, &ctor, Rules::Now);
    let before = cost(&env, &block, &ctor, Rules::Before);
    assert_eq!((now.verdict, before.verdict), (Err(()), Err(())));
    assert!(now.reads <= bound(nodes(&ctor), 0), "{now:?}");
    assert!(before.reads >= 5_034_700, "{before:?}");
}

/// `E.c0 : (α : Type) → P (P (… (P α Big) Big) …) Big → E α`, `d = 200`
/// (51,207 nodes), and `E T → T`: the chain is in the container's own
/// constructor. The oracle's scan of `E` walked each argument with
/// `bvar_mentions` to find `α` and then scanned it: 5,397,113 reads, 201
/// lists. One pass: 38,419 reads, `E` and `P` scanned once each (2 lists).
/// With `α → Prop` at the bottom both refuse: 5,077,310 reads and 201 lists
/// before, 410 reads and 1 list now.
#[test]
fn test_positivity_container_scan_of_a_chain_reads_each_node_at_most_once() {
    let block = [n("T")];
    let ctor = pi(app(konst("E"), konst("T")), konst("T"));

    let e0 = e_ctor(200, Term::bvar(0));
    let scanned = nodes(&e0).saturating_add(nodes(&p_ctor()));
    assert_eq!(nodes(&e0), 51_207);
    let env = e_env(e0);
    let now = cost(&env, &block, &ctor, Rules::Now);
    let before = cost(&env, &block, &ctor, Rules::Before);
    assert_eq!((now.verdict, before.verdict), (Ok(()), Ok(())));
    assert!(
        now.reads <= bound(nodes(&ctor).saturating_add(scanned), 0),
        "{now:?}"
    );
    assert_eq!((now.lists, before.lists), (2, 201));
    assert!(before.reads >= 5_034_700, "{before:?}");

    let env = e_env(e_ctor(200, pi(Term::bvar(0), prop())));
    let now = cost(&env, &block, &ctor, Rules::Now);
    let before = cost(&env, &block, &ctor, Rules::Before);
    assert_eq!((now.verdict, before.verdict), (Err(()), Err(())));
    assert_eq!((now.lists, before.lists), (1, 201));
    assert!(now.reads <= 1_000, "{now:?}");
    assert!(before.reads >= 5_034_700, "{before:?}");
}

/// `K16 T → T` over `ladder(16, 2)`: a 5-node constructor. The oracle checked
/// `K(j-1)`'s slot again at each of its two uses and forgot it: 131,071
/// constructor lists (`2^17 - 1`) and 1,179,643 reads. Each slot once: 17
/// lists, 186 reads.
#[test]
fn test_positivity_each_container_slot_is_checked_once_per_check() {
    let env = ladder(16, 2);
    let block = [n("T")];
    let ctor = pi(app(konst("K16"), konst("T")), konst("T"));
    let now = cost(&env, &block, &ctor, Rules::Now);
    let before = cost(&env, &block, &ctor, Rules::Before);
    assert_eq!((now.verdict, before.verdict), (Ok(()), Ok(())));
    assert_eq!((now.lists, before.lists), (17, 131_071));
    assert!(now.reads <= 1_000, "{now:?}");
}

/// `W (α_0 … α_99 : Type)` with `W.c0 : (α_0 … α_99 : Type) → α_0 → … →
/// α_99 → W α_0 … α_99` (601 nodes), and `W T … T → T`: each of the 100 slots
/// is required and scans `W.c0`, once here as in the rules (100 lists). A
/// leaf's walk reading it again made that 55,254 reads to the rules' 40,306;
/// one pass: 40,204. Both are `slots × |W.c0|`, a slot being checked alone.
#[test]
fn test_positivity_wide_container_reads_no_more_than_the_rules() {
    let np: u32 = 100;
    // Field `k` sits under the `np` parameters and `k` fields, so `α_k` is
    // `BVar(np - 1)`; under every binder, `α_k` is `BVar(2 np - 1 - k)`.
    let fields = (0..np).map(|_| Term::bvar(np.saturating_sub(1)));
    let top = np.saturating_mul(2).saturating_sub(1);
    let ret = (0..np).fold(konst("W"), |f, k| app(f, Term::bvar(top.saturating_sub(k))));
    let w0 = telescope((0..np).map(|_| ty()).chain(fields).collect(), ret);
    assert_eq!(nodes(&w0), 601);
    let env = with_container(MinimalEnv::new(), "W", np, vec![w0]);
    let block = [n("T")];
    let ctor = pi(
        (0..np).fold(konst("W"), |f, _| app(f, konst("T"))),
        konst("T"),
    );
    let now = cost(&env, &block, &ctor, Rules::Now);
    let before = cost(&env, &block, &ctor, Rules::Before);
    assert_eq!((now.verdict, before.verdict), (Ok(()), Ok(())));
    assert_eq!((now.lists, before.lists), (100, 100));
    assert!(now.reads <= before.reads, "{now:?} against {before:?}");
}

/// Sixteen constructors `E T → T`, `E.c0` nesting `α` in 8 levels of `P`:
/// one check for the block scans `E` and `P` once (2 lists); a fresh check per
/// constructor, twice each (32); the rules, 9 each (144).
#[test]
fn test_positivity_a_block_checks_each_container_slot_once() {
    let env = e_env(e_ctor(8, Term::bvar(0)));
    let block = [n("T")];
    let ctor = pi(app(konst("E"), konst("T")), konst("T"));

    let counting = CountingEnv::new(&env);
    let mut positivity = Positivity::new(&counting, &block);
    for _ in 0..16 {
        assert_eq!(positivity.check_ctor(&ctor), Ok(()));
    }
    assert_eq!(counting.lists.get(), 2);

    let fresh = CountingEnv::new(&env);
    let before = CountingEnv::new(&env);
    for _ in 0..16 {
        assert_eq!(check(&fresh, &block, &ctor), Ok(()));
        assert_eq!(check_before(&before, &block, &ctor), Ok(()));
    }
    assert_eq!((fresh.lists.get(), before.lists.get()), (32, 144));
}

/// `K20000 T → T` over `ladder(20_000, 1)`, on a thread of 512 KiB: the
/// oracle recursed natively through every container on the path (some four
/// frames each), which overflows it and aborts the process (run red on its
/// own, `--exact`). The obligations are a worklist: 20,001 lists. The env is
/// built on that thread, so nothing needs to be `Send`.
#[test]
fn test_positivity_long_chain_of_containers_needs_no_native_stack() {
    let (verdict, lists) = std::thread::Builder::new()
        // 512 KiB.
        .stack_size(524_288)
        .spawn(|| {
            let env = ladder(20_000, 1);
            let counting = CountingEnv::new(&env);
            let ctor = pi(app(konst("K20000"), konst("T")), konst("T"));
            let verdict = check(&counting, &[n("T")], &ctor);
            (verdict, counting.lists.get())
        })
        .expect("thread spawns")
        .join()
        .expect("the check returns rather than unwinding");
    assert_eq!((verdict, lists), (Ok(()), 20_001));
}
