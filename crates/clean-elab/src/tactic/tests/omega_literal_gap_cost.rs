// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression lock: `omega`'s Nat proof must not grow with the GAP between two
//! literal bounds.
//!
//! ## The defect (measured 2026-09-30, `clean check`, 4 GB resident cap)
//!
//! | goal                                           | before            |
//! |------------------------------------------------|-------------------|
//! | `(h : v < 10) ⊢ v < 1000`                      | OK, 0.3 GB        |
//! | `(h : v < 10) ⊢ v < 100000`                    | over 4 GB, 26 s   |
//! | `(h : v < 10) ⊢ v < 1000000`                   | over 4 GB, 0.6 s  |
//! | `(h : v < 1114112) ⊢ v < 4294967296`           | over 4 GB         |
//! | `(h : v < 1114112) ⊢ v < 1114113`              | OK, 0.06 GB       |
//!
//! The direct reconstruction (`arith_linarith_nat_direct`) weakened the bound
//! with one `Nat.le.step` per unit of the gap. Each term is now one literal
//! comparison decided by the kernel's `Nat.ble` fold
//! (`tactic::nat_le_bridge`).
//!
//! ORDER MATTERS. Every test that runs a large gap first checks, on gaps small
//! enough to be cheap even with the defect back, that the term size does not
//! move with the gap. A regression fails on that canary instead of building a
//! four-billion-node term on a shared machine.

use super::*;
use crate::tactic::arith_linarith_nat_direct::try_prove_nat_inequality_direct_with_hyps;
use crate::tactic::nat_le_bridge::{nat_false_of_lits_le, nat_le_between, nat_le_lits, tree_size};
use crate::tactic::tc_app::{nat_le_tc, nat_lt_tc};
use clean_kernel::level::Level;
use clean_kernel::Expr;
use serial_test::serial;
use std::time::{Duration, Instant};

/// Largest tree size any literal-gap term may have. The whole term is a
/// handful of constants and literals; the old unary chain for the smallest gap
/// below (990) was tens of thousands of nodes.
const MAX_TERM_NODES: usize = 64;

/// Generous wall-clock bound for one `omega` call in a debug build on a loaded
/// machine. The old term for the 2^32 gap never finished being built.
const MAX_OMEGA_TIME: Duration = Duration::from_secs(10);

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `@OfNat.ofNat.{0} Nat k (instOfNatNat k)` — the elaborated source numeral.
fn ofnat_nat(k: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [
            c("Nat"),
            Expr::nat_lit(k),
            Expr::app(c("instOfNatNat"), Expr::nat_lit(k)),
        ],
    )
}

fn nat_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(c("Nat.add"), [lhs, rhs])
}

fn local(id: u64, name: &str, ty: Expr) -> LocalDecl {
    LocalDecl {
        binder_info: Default::default(),
        fvar: FVarId::new(id),
        name: clean_parser::SurfaceName::component(name, false),
        ty,
        value: None,
    }
}

/// `v : Nat` (fvar 0), `h : v < lo` (fvar 1) ⊢ `v < hi`.
fn bound_goal(lo: u64, hi: u64) -> (Expr, Vec<LocalDecl>) {
    let v = Expr::fvar(FVarId::new(0));
    let ctx = vec![
        local(0, "v", c("Nat")),
        local(1, "h", nat_lt_tc(v.clone(), ofnat_nat(lo))),
    ];
    (nat_lt_tc(v, ofnat_nat(hi)), ctx)
}

fn hyps_of(ctx: &[LocalDecl]) -> Vec<(Expr, Expr)> {
    ctx.iter()
        .map(|d| (Expr::fvar(d.fvar), d.ty.clone()))
        .collect()
}

/// Tree size of the direct reconstruction's term for `h : v < lo ⊢ v < hi`.
fn direct_term_size(lo: u64, hi: u64) -> usize {
    let (goal, ctx) = bound_goal(lo, hi);
    let term = try_prove_nat_inequality_direct_with_hyps(&goal, &hyps_of(&ctx))
        .unwrap_or_else(|| panic!("direct prover must propose a term for v < {lo} ⊢ v < {hi}"));
    tree_size(&term)
}

/// The canary: on gaps small enough to be cheap with the defect back, the term
/// size must not move with the gap.
fn assert_gap_independent_on_small_gaps() {
    let small = direct_term_size(10, 1000);
    let double = direct_term_size(10, 2000);
    assert_eq!(
        small, double,
        "the omega term grew with the literal gap (990 → {small} nodes, 1990 → {double} \
         nodes): the unary weakening is back"
    );
    assert!(
        small <= MAX_TERM_NODES,
        "the omega term for v < 10 ⊢ v < 1000 has {small} nodes (bound {MAX_TERM_NODES})"
    );
}

/// Run `omega` on `h : v < lo ⊢ v < hi`, assert it closes with a real,
/// constant-size proof within the time bound.
fn assert_omega_closes_cheaply(lo: u64, hi: u64) {
    let label = format!("(h : v < {lo}) ⊢ v < {hi}");
    let (goal, ctx) = bound_goal(lo, hi);
    let mut state = ProofState::with_context(Environment::with_prelude(), goal, ctx);
    reset_all_counters();
    let axiom_before = axiom_snapshot();
    let start = Instant::now();
    let result = omega(&mut state);
    let elapsed = start.elapsed();
    assert!(result.is_ok(), "omega must prove `{label}`, got {result:?}");
    assert!(state.is_complete(), "`{label}` must be closed");
    assert!(
        elapsed < MAX_OMEGA_TIME,
        "`{label}` took {elapsed:?} (bound {MAX_OMEGA_TIME:?})"
    );
    assert_no_trusted_axiom_usage("omega", &label, axiom_before);
    let ledger = state.trust_ledger();
    assert_eq!(ledger.sorry_count, 0, "`{label}` must not close with sorry");
    let proof = state
        .instantiated_proof()
        .unwrap_or_else(|| panic!("`{label}` must have a proof term"));
    let nodes = tree_size(&proof);
    assert!(
        nodes <= MAX_TERM_NODES,
        "`{label}`: proof has {nodes} nodes (bound {MAX_TERM_NODES})"
    );
    eprintln!("omega {label}: {elapsed:?}, {nodes} nodes");
}

#[test]
#[serial]
fn test_omega_literal_gap_repros_close_with_constant_size_terms() {
    assert_gap_independent_on_small_gaps();
    for (lo, hi) in [
        (10, 1_000),
        (10, 100_000),
        (10, 1_000_000),
        (1_114_112, 4_294_967_296),
        (1_114_112, 1_114_113),
        (4_294_967_296, 4_294_967_297),
    ] {
        assert_omega_closes_cheaply(lo, hi);
    }
}

#[test]
#[serial]
fn test_omega_literal_gap_negative_controls_are_refused() {
    assert_gap_independent_on_small_gaps();
    // FALSE: v = 100000 satisfies h and violates the goal.
    for (lo, hi) in [(100_001, 100_000), (4_294_967_297, 4_294_967_296)] {
        let (goal, ctx) = bound_goal(lo, hi);
        assert!(
            try_prove_nat_inequality_direct_with_hyps(&goal, &hyps_of(&ctx)).is_none(),
            "the direct prover must propose nothing for the FALSE v < {lo} ⊢ v < {hi}"
        );
        let mut state = ProofState::with_context(Environment::with_prelude(), goal, ctx);
        reset_all_counters();
        let result = omega(&mut state);
        assert!(
            result.is_err() && !state.is_complete(),
            "omega must REFUSE the FALSE (h : v < {lo}) ⊢ v < {hi}, got {result:?}"
        );
    }
}

/// Symbolic upper bounds share the fix: `(h : v ≤ w + 3) ⊢ v ≤ w + 1000003`.
#[test]
#[serial]
fn test_omega_symbolic_core_gap_closes_with_constant_size_term() {
    let v = Expr::fvar(FVarId::new(0));
    let w = Expr::fvar(FVarId::new(1));
    let mk = |off: u64| {
        let ctx = vec![
            local(0, "v", c("Nat")),
            local(1, "w", c("Nat")),
            local(
                2,
                "h",
                nat_le_tc(v.clone(), nat_add(w.clone(), ofnat_nat(3))),
            ),
        ];
        (
            nat_le_tc(v.clone(), nat_add(w.clone(), ofnat_nat(off))),
            ctx,
        )
    };
    let size = |off: u64| {
        let (goal, ctx) = mk(off);
        tree_size(
            &try_prove_nat_inequality_direct_with_hyps(&goal, &hyps_of(&ctx))
                .expect("direct prover must propose a term"),
        )
    };
    assert_eq!(
        size(1_003),
        size(2_003),
        "symbolic-core term grew with the gap"
    );

    let (goal, ctx) = mk(1_000_003);
    let mut state = ProofState::with_context(Environment::with_prelude(), goal, ctx);
    reset_all_counters();
    omega(&mut state).expect("omega must prove (h : v ≤ w + 3) ⊢ v ≤ w + 1000003");
    assert!(state.is_complete());
    let nodes = tree_size(&state.instantiated_proof().expect("proof term"));
    assert!(nodes <= MAX_TERM_NODES, "proof has {nodes} nodes");

    // FALSE twin: v = w + 3 violates `v ≤ w + 2`.
    let (goal, ctx) = mk(2);
    let mut state = ProofState::with_context(Environment::with_prelude(), goal, ctx);
    reset_all_counters();
    assert!(
        omega(&mut state).is_err() && !state.is_complete(),
        "omega must refuse (h : v ≤ w + 3) ⊢ v ≤ w + 2"
    );
}

/// `(h : v < bound) ⊢ v ≠ k` for `k ≥ bound`, closed by omega; returns the
/// proof's tree size.
fn omega_ne_beyond_bound(bound: u64, k: u64) -> usize {
    let v = Expr::fvar(FVarId::new(0));
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
        [c("Nat"), v.clone(), ofnat_nat(k)],
    );
    let ctx = vec![
        local(0, "v", c("Nat")),
        local(1, "h", nat_lt_tc(v, ofnat_nat(bound))),
    ];
    let mut state = ProofState::with_context(Environment::with_prelude(), goal, ctx);
    reset_all_counters();
    let start = Instant::now();
    omega(&mut state)
        .unwrap_or_else(|e| panic!("omega must prove (h : v < {bound}) ⊢ v ≠ {k}: {e:?}"));
    assert!(state.is_complete());
    assert!(
        start.elapsed() < MAX_OMEGA_TIME,
        "took {:?}",
        start.elapsed()
    );
    tree_size(&state.instantiated_proof().expect("proof term"))
}

/// `(h : v < 1114112) ⊢ v ≠ 4294967296`: the bound-hypothesis refuter substitutes
/// `v := 4294967296` and refutes `4294967297 ≤ 1114112`. That refutation used to
/// peel `Nat.le_of_succ_le_succ` once per unit of the smaller literal.
#[test]
#[serial]
fn test_omega_ne_beyond_bound_refutes_with_constant_size_term() {
    // Canary first: cheap even with a unary refuter back.
    let small = omega_ne_beyond_bound(1_000, 2_000);
    let double = omega_ne_beyond_bound(2_000, 3_000);
    assert_eq!(small, double, "the ≠ refutation grew with the literals");
    let nodes = omega_ne_beyond_bound(1_114_112, 4_294_967_296);
    assert_eq!(nodes, small, "the ≠ refutation grew with the literals");
}

/// The bridge builders, kernel-checked directly.
#[test]
fn test_nat_le_bridge_terms_kernel_check_and_refuse_false_comparisons() {
    let mut env = Environment::with_prelude();
    for (name, ty) in [
        ("n", c("Nat")),
        // An inconsistent axiom, only to have a term of a FALSE literal `Nat.le`
        // to refute.
        (
            "h_false",
            Expr::apps(
                c("Nat.le"),
                [Expr::nat_lit(4_294_967_297), Expr::nat_lit(1_114_112)],
            ),
        ),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
        .expect("test axiom should add");
    }
    let tc = TypeChecker::with_mode(&env, env.mode());
    let le = |a: Expr, b: Expr| Expr::apps(c("Nat.le"), [a, b]);
    let n = c("n");

    // Literal comparison across a 2^32-scale gap.
    let lits = nat_le_lits(1_114_112, 4_294_967_296);
    tc.check_type(
        &lits,
        &le(Expr::nat_lit(1_114_112), Expr::nat_lit(4_294_967_296)),
    )
    .expect("1114112 ≤ 4294967296 must check");
    assert!(tree_size(&lits) <= MAX_TERM_NODES);

    // NEGATIVE: the same term shape at a FALSE comparison is refused by the
    // kernel's `Nat.ble` fold — the bridge cannot make a false bound true.
    assert!(
        tc.check_type(
            &nat_le_lits(100_001, 100_000),
            &le(Expr::nat_lit(100_001), Expr::nat_lit(100_000))
        )
        .is_err(),
        "the kernel must refuse 100001 ≤ 100000"
    );

    // Common symbolic base: `n + 3 ≤ n + 1000003`, `n ≤ n + 1000000`, and the
    // contradiction closer's `succ R ≤ R + k` where `R` itself starts with a
    // LEFT literal (`5 + n`), which must be kept whole as the base, never
    // reordered to `n + 5`.
    let n3 = nat_add(n.clone(), Expr::nat_lit(3));
    let n1000003 = nat_add(n.clone(), Expr::nat_lit(1_000_003));
    let shifted = nat_le_between(&n3, &n1000003).expect("n + 3 ≤ n + 1000003");
    tc.check_type(&shifted, &le(n3.clone(), n1000003.clone()))
        .expect("n + 3 ≤ n + 1000003 must check");
    assert!(tree_size(&shifted) <= MAX_TERM_NODES);
    let n1000000 = nat_add(n.clone(), Expr::nat_lit(1_000_000));
    let from_zero = nat_le_between(&n, &n1000000).expect("n ≤ n + 1000000");
    tc.check_type(&from_zero, &le(n.clone(), n1000000))
        .expect("n ≤ n + 1000000 must check");
    let r = nat_add(Expr::nat_lit(5), n.clone());
    let succ_r = Expr::app(c("Nat.succ"), r.clone());
    let r_plus_k = nat_add(r.clone(), Expr::nat_lit(700));
    let farkas_step = nat_le_between(&succ_r, &r_plus_k).expect("succ R ≤ R + 700");
    tc.check_type(&farkas_step, &le(succ_r, r_plus_k))
        .expect("succ (5 + n) ≤ (5 + n) + 700 must check");
    // NEGATIVE: no proof for a false offset order or a mere reordering.
    assert!(
        nat_le_between(&n1000003, &n3).is_none(),
        "n + 1000003 ≤ n + 3 is false"
    );
    assert!(
        nat_le_between(&nat_add(Expr::nat_lit(8), n.clone()), &n3).is_none(),
        "8 + n vs n + 3: no common right-offset base"
    );

    // Refutation of a false literal bound, constant-size.
    let refute =
        nat_false_of_lits_le(c("h_false"), 4_294_967_297, 1_114_112).expect("4294967297 > 1114112");
    tc.check_type(&refute, &c("False"))
        .expect("the refutation must check at False");
    assert!(tree_size(&refute) <= MAX_TERM_NODES);
    assert!(nat_false_of_lits_le(c("h_false"), 3, 5).is_none());
}
