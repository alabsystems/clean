// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! linarith's builders read every hypothesis as the `≤` it proves by
//! definition: `a ≥ b` as `b ≤ a`, `a > b` as `b < a` (Lean 4.8.0
//! `Init/Prelude.lean:1115-1117`), and a strict `a < b` as `Nat.succ a ≤ b`
//! (`Init/Prelude.lean:1643`) or, over Int, `a + 1 ≤ b`
//! (`Init/Data/Int/Basic.lean:180`). Each case that must close has a
//! satisfiable twin that must be refused.

use super::*;

fn make_nat_lt_tc(lhs: Expr, rhs: Expr) -> Expr {
    tc_app::nat_lt_tc(lhs, rhs)
}

fn make_nat_ge_tc(lhs: Expr, rhs: Expr) -> Expr {
    mk_rel("GE.ge", "Nat", "instLENat", lhs, rhs)
}

fn make_nat_gt_tc(lhs: Expr, rhs: Expr) -> Expr {
    mk_rel("GT.gt", "Nat", "instLTNat", lhs, rhs)
}

fn make_int_lt_tc(lhs: Expr, rhs: Expr) -> Expr {
    mk_rel("LT.lt", "Int", "instLTInt", lhs, rhs)
}

fn int_lit(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Nat.add"), vec![]), [a, b])
}

fn nat_mul(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Nat.mul"), vec![]), [a, b])
}

/// The `i`-th variable of the context [`replay_closes`] builds.
fn var(i: u64) -> Expr {
    Expr::fvar(FVarId::new(i))
}

/// [`replay_closes_in`] over the plain prelude.
fn replay_closes(vars: &[&str], hyps: Vec<Expr>, coefficients: Vec<i128>) -> bool {
    replay_closes_in(Environment::with_prelude(), vars, hyps, coefficients)
}

/// Run `build_linarith_proof` in `env` over a `False` goal whose context is
/// the variables `vars` (named `x0, x1, …`, typed by the given sort name)
/// followed by `hyps`, the `i`-th hypothesis weighted `coefficients[i]`, and
/// hand the result to `close_goal`. `true` means the goal closed.
fn replay_closes_in(
    env: Environment,
    vars: &[&str],
    hyps: Vec<Expr>,
    coefficients: Vec<i128>,
) -> bool {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let mut ctx: Vec<LocalDecl> = vars
        .iter()
        .enumerate()
        .map(|(i, sort)| LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(i as u64),
            name: clean_parser::SurfaceName::generated_path(&format!("x{i}")),
            ty: Expr::const_(Name::from_string(sort), vec![]),
            value: None,
        })
        .collect();
    let mut hyp_ids = Vec::new();
    for (i, ty) in hyps.into_iter().enumerate() {
        let id = FVarId::new((vars.len() + i) as u64);
        hyp_ids.push(id);
        ctx.push(LocalDecl {
            binder_info: Default::default(),
            fvar: id,
            name: clean_parser::SurfaceName::generated_path(&format!("h{i}")),
            ty,
            value: None,
        });
    }
    assert_eq!(
        coefficients.len(),
        hyp_ids.len(),
        "one coefficient per hypothesis"
    );
    let mut state =
        ProofState::with_context(env, Expr::const_(Name::from_string("False"), vec![]), ctx);
    let goal = state.current_goal().expect("should have a goal").clone();
    let certificate = LinarithCertificate {
        coefficients,
        result_constant: 0,
    };
    let Some(proof) = build_linarith_proof(&state, &goal, &certificate, &hyp_ids) else {
        return false;
    };
    state.close_goal(&goal, proof).is_ok() && state.is_complete()
}

/// [`replay_closes`] over one `x0 : Nat` with every hypothesis weighted 1.
fn nat_replay_closes(hyps: Vec<Expr>) -> bool {
    let n = hyps.len();
    replay_closes(&["Nat"], hyps, vec![1; n])
}

/// A lone `h : 0x110000 < 0x110000` is refuted: it is
/// `Nat.le (Nat.succ 0x110000) 0x110000` by definition. Read as `0x110000 ≤
/// 0x110000` it was consistent and `h` itself came back as the proof of
/// `False` (`TrustIr/Basic.lean`'s `not_validChar_above_max`).
#[test]
fn test_build_linarith_proof_strict_lone_nat_self_lt_closes() {
    assert!(nat_replay_closes(vec![make_nat_lt_tc(
        Expr::nat_lit(0x110000),
        Expr::nat_lit(0x110000),
    )]));
}

/// Negative control: `h : 0x10FFFF < 0x110000` is true, so nothing refutes it.
#[test]
fn test_build_linarith_proof_strict_lone_nat_true_lt_refused() {
    assert!(!nat_replay_closes(vec![make_nat_lt_tc(
        Expr::nat_lit(0x10FFFF),
        Expr::nat_lit(0x110000),
    )]));
}

/// The chain `0xD800 ≤ x`, `x < 256` proves `0xD800 < 256`, i.e.
/// `Nat.le (Nat.succ 0xD800) 256`; the `False` term used to apply it where
/// `Nat.le 0xD800 256` was due, which the kernel refused
/// (`validChar_of_lt_256`).
#[test]
fn test_build_linarith_proof_strict_nat_chain_closes() {
    assert!(nat_replay_closes(vec![
        make_nat_le_tc(Expr::nat_lit(0xD800), var(0)),
        make_nat_lt_tc(var(0), Expr::nat_lit(256)),
    ]));
}

/// Negative control: `x = 0xD800` satisfies `0xD800 ≤ x`, `x < 0xD801`.
#[test]
fn test_build_linarith_proof_strict_nat_chain_satisfiable_refused() {
    assert!(!nat_replay_closes(vec![
        make_nat_le_tc(Expr::nat_lit(0xD800), var(0)),
        make_nat_lt_tc(var(0), Expr::nat_lit(0xD801)),
    ]));
}

/// `h : 3 ≥ 5` is `5 ≤ 3`. Read with its operands in surface order it was the
/// consistent `3 ≤ 5`, and `h` came back as the proof of `False` (`expected
/// False, got Nat.le 5 3`).
#[test]
fn test_build_linarith_proof_lone_nat_ge_reads_reversed_closes() {
    assert!(nat_replay_closes(vec![make_nat_ge_tc(
        Expr::nat_lit(3),
        Expr::nat_lit(5),
    )]));
}

/// Negative control: `5 ≥ 3` is `3 ≤ 5`, true.
#[test]
fn test_build_linarith_proof_lone_nat_true_ge_refused() {
    assert!(!nat_replay_closes(vec![make_nat_ge_tc(
        Expr::nat_lit(5),
        Expr::nat_lit(3),
    )]));
}

/// `256 > x`, `x ≥ 0xD800` is the chain `0xD800 ≤ x < 256`. In surface order
/// the two did not chain at all (`expected 256 < x, got 256 > x`).
#[test]
fn test_build_linarith_proof_gt_ge_chain_reads_reversed_closes() {
    assert!(nat_replay_closes(vec![
        make_nat_gt_tc(Expr::nat_lit(256), var(0)),
        make_nat_ge_tc(var(0), Expr::nat_lit(0xD800)),
    ]));
}

/// Negative control: `x = 0xD800` satisfies `0xD801 > x`, `x ≥ 0xD800`.
#[test]
fn test_build_linarith_proof_gt_ge_chain_satisfiable_refused() {
    assert!(!nat_replay_closes(vec![
        make_nat_gt_tc(Expr::nat_lit(0xD801), var(0)),
        make_nat_ge_tc(var(0), Expr::nat_lit(0xD800)),
    ]));
}

/// `a + b < 3`, `5 ≤ a` neither chains nor cancels to a shared core; summed
/// as `Nat.succ (a + b) + 5 ≤ 3 + a` it is refuted with `0 ≤ b`. The strict
/// hypothesis used to enter the sum as `a + b ≤ 3`, which it does not prove
/// (`expected Nat.le (a + b) 3, got a + b < 3`).
#[test]
fn test_build_linarith_proof_strict_nat_sum_closes() {
    assert!(replay_closes(
        &["Nat", "Nat"],
        vec![
            make_nat_lt_tc(nat_add(var(0), var(1)), Expr::nat_lit(3)),
            make_nat_le_tc(Expr::nat_lit(5), var(0)),
        ],
        vec![1, 1],
    ));
}

/// Negative control: `a = 5, b = 0` satisfies `a + b < 6`, `5 ≤ a`.
#[test]
fn test_build_linarith_proof_strict_nat_sum_satisfiable_refused() {
    assert!(!replay_closes(
        &["Nat", "Nat"],
        vec![
            make_nat_lt_tc(nat_add(var(0), var(1)), Expr::nat_lit(6)),
            make_nat_le_tc(Expr::nat_lit(5), var(0)),
        ],
        vec![1, 1],
    ));
}

/// The scaled path reads a strict hypothesis strictly too: `2 · (3 < x)` is
/// `2 · 4 ≤ 2 · x`, which `2 * x ≤ 7` refutes. Read as `2 · (3 ≤ x)` the sum
/// `6 + 2x ≤ 2x + 7` is consistent.
#[test]
fn test_build_linarith_proof_strict_nat_scaled_closes() {
    assert!(replay_closes(
        &["Nat"],
        vec![
            make_nat_lt_tc(Expr::nat_lit(3), var(0)),
            make_nat_le_tc(nat_mul(Expr::nat_lit(2), var(0)), Expr::nat_lit(7)),
        ],
        vec![2, 1],
    ));
}

/// Negative control: `x = 4` satisfies `3 < x`, `2 * x ≤ 8`.
#[test]
fn test_build_linarith_proof_strict_nat_scaled_satisfiable_refused() {
    assert!(!replay_closes(
        &["Nat"],
        vec![
            make_nat_lt_tc(Expr::nat_lit(3), var(0)),
            make_nat_le_tc(nat_mul(Expr::nat_lit(2), var(0)), Expr::nat_lit(8)),
        ],
        vec![2, 1],
    ));
}

/// A lone strict Int `5 < 3` is `5 + 1 ≤ 3`, refuted by the concrete Int
/// closer (no strict Int closer was wired).
#[test]
fn test_build_linarith_proof_strict_lone_int_closes() {
    assert!(replay_closes(
        &[],
        vec![make_int_lt_tc(int_lit(5), int_lit(3))],
        vec![1],
    ));
}

/// Negative control: `2 < 3` over Int is true.
#[test]
fn test_build_linarith_proof_strict_lone_int_true_lt_refused() {
    assert!(!replay_closes(
        &[],
        vec![make_int_lt_tc(int_lit(2), int_lit(3))],
        vec![1],
    ));
}

/// `5 ≤ v`, `v < 3` over Int chains to `5 < 3`, i.e. `5 + 1 ≤ 3`.
#[test]
fn test_build_linarith_proof_strict_int_chain_closes() {
    assert!(replay_closes(
        &["Int"],
        vec![
            make_int_lt_tc(var(0), int_lit(3)),
            make_int_le_tc(int_lit(5), var(0)),
        ],
        vec![1, 1],
    ));
}

/// Negative control: `v = 5` satisfies `v < 6`, `5 ≤ v`.
#[test]
fn test_build_linarith_proof_strict_int_chain_satisfiable_refused() {
    assert!(!replay_closes(
        &["Int"],
        vec![
            make_int_lt_tc(var(0), int_lit(6)),
            make_int_le_tc(int_lit(5), var(0)),
        ],
        vec![1, 1],
    ));
}

fn real_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn rat_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Rat.ofInt"), vec![]),
        int_lit(n),
    )
}

/// The Real order and its Int downcast (`Real.ofInt_le_to_Int`).
fn real_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas()
        .expect("Int ordering lemmas should initialize");
    env.init_real_linear_order()
        .expect("Real linear order should initialize");
    env
}

/// The Rat order and its Int downcast (`Int.cast_le_prop`).
fn rat_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_rat_ord()
        .expect("Rat ordering lemmas should initialize");
    env.init_cast_simp_lemmas()
        .expect("Rat.ofInt cast lemmas should initialize");
    env
}

/// KNOWN GAP, pinned as a refusal: a strict Real / Rat hypothesis.
///
/// `(5 : ℝ) < 3 ⊢ False` and its Rat twin are true, and Mathlib's `linarith`
/// proves them, but Real's and Rat's `<` is not a `≤` by definition (`Real.lt`
/// and `Rat.lt` are their own constants), so `strict_as_le_lhs` and
/// `definitional_le_endpoints` (`arith_linarith_chain.rs`) return `None` and
/// the builders give up. Before the strict reading those terms were ill-typed
/// and the kernel refused them, so this is completeness debt, not a
/// regression. The non-strict `5 ≤ 3` closes in the same environment with
/// the same literals, so the refusal is the strict reading's, not the
/// fixture's. The day this closes, flip the strict assertions and add the
/// true `2 < 3` as the negative control.
#[test]
fn test_build_linarith_proof_strict_real_rat_lone_is_a_pinned_gap() {
    type Lit = fn(u64) -> Expr;
    let cases: [(&str, fn() -> Environment, Lit, &str, &str); 2] = [
        ("Real", real_env, real_of_nat, "instLEReal", "instLTReal"),
        ("Rat", rat_env, rat_of_nat, "instLERat", "instLTRat"),
    ];
    for (sort, env, lit, le_inst, lt_inst) in cases {
        assert!(
            replay_closes_in(
                env(),
                &[],
                vec![mk_rel("LE.le", sort, le_inst, lit(5), lit(3))],
                vec![1],
            ),
            "control: the {sort} `5 ≤ 3` must close"
        );
        assert!(
            !replay_closes_in(
                env(),
                &[],
                vec![mk_rel("LT.lt", sort, lt_inst, lit(5), lit(3))],
                vec![1],
            ),
            "the strict {sort} gap closed: `5 < 3` now refutes — flip this pin to a positive \
             row with the true `2 < 3` as its negative control"
        );
    }
}
