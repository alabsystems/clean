// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Built-in simp lemma definitions for Nat, Bool, and Prop.
//!
//! Extracted from `lemmas.rs` to keep file and function sizes within limits.
//! Each function collects lemmas for a category, guarded by environment
//! constant presence and config exclusions.

use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

use super::types::{SimpConfig, SimpIndexMode, SimpLemma};
use crate::tactic::core::ProofState;

/// Collect built-in Nat arithmetic simp lemmas.
///
/// ENSURES: Each returned lemma has a valid LHS/RHS pattern for a Nat identity.
pub(crate) fn collect_nat_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    // The everyday identity lemmas below are `Unindexed` (B102, extended to
    // the remaining WHNF-rotted siblings in B103): their literal-operand
    // patterns WHNF-rot under the discrimination-tree key path
    // (`Nat.add ?n 0` ι-collapses to `?n` — a bare star; `Nat.mul ?n 1`
    // δ/ι-collapses to its stuck `Nat.rec` body — a bogus-specific key; the
    // `Nat.mul`/`Nat.sub` zero/self/one siblings rot the same two ways), so
    // Normal indexing either shadows them behind wrong-but-specific tree hits
    // or never offers them at the goal's own (equally rotted) query key. As
    // star-keyed lemmas they are offered everywhere and still guarded by the
    // unifier + `lhs_inst ≡ expr` def-eq check + kernel re-verification.

    // Nat.add_zero: n + 0 = n
    push_if_present(state, config, &mut lemmas, "Nat.add_zero", || SimpLemma {
        name: Name::from_string("Nat.add_zero"),
        lhs: make_nat_add_pattern("n", "Nat.zero"),
        rhs: Expr::bvar(0),
        eq_type: Some(nat_ty.clone()),
        proof_expr: None,
        index_mode: SimpIndexMode::Unindexed,
        priority: 100,
    });

    // Nat.zero_add: 0 + n = n
    push_if_present(state, config, &mut lemmas, "Nat.zero_add", || SimpLemma {
        name: Name::from_string("Nat.zero_add"),
        lhs: make_nat_add_pattern("Nat.zero", "n"),
        rhs: Expr::bvar(0),
        eq_type: Some(nat_ty.clone()),
        proof_expr: None,
        index_mode: SimpIndexMode::Unindexed,
        priority: 100,
    });

    // Nat.mul_one: n * 1 = n
    //
    // The `1` leaf is the RAW literal, not `Const(Nat.one)`: the surface goal
    // spells `1` as `Lit(Nat 1)` (after the `OfNat` wrapper collapses), and
    // the unifier's two-literal fast path decides `Lit 1 ≡ Lit 1` by value,
    // while a `Nat.one` const leaf δ-rots under WHNF and never bridges (B102).
    push_if_present(state, config, &mut lemmas, "Nat.mul_one", || SimpLemma {
        name: Name::from_string("Nat.mul_one"),
        lhs: make_nat_mul_lit_pattern(NatMulLitSide::LitRight),
        rhs: Expr::bvar(0),
        eq_type: Some(nat_ty.clone()),
        proof_expr: None,
        index_mode: SimpIndexMode::Unindexed,
        priority: 100,
    });

    // Nat.one_mul: 1 * n = n
    push_if_present(state, config, &mut lemmas, "Nat.one_mul", || SimpLemma {
        name: Name::from_string("Nat.one_mul"),
        lhs: make_nat_mul_lit_pattern(NatMulLitSide::LitLeft),
        rhs: Expr::bvar(0),
        eq_type: Some(nat_ty.clone()),
        proof_expr: None,
        index_mode: SimpIndexMode::Unindexed,
        priority: 100,
    });

    // Nat.mul_zero: n * 0 = 0
    push_if_present(state, config, &mut lemmas, "Nat.mul_zero", || SimpLemma {
        name: Name::from_string("Nat.mul_zero"),
        lhs: make_nat_mul_pattern("n", "Nat.zero"),
        rhs: Expr::const_(Name::from_string("Nat.zero"), vec![]),
        eq_type: Some(nat_ty.clone()),
        proof_expr: None,
        index_mode: SimpIndexMode::Unindexed,
        priority: 100,
    });

    // Nat.zero_mul: 0 * n = 0
    push_if_present(state, config, &mut lemmas, "Nat.zero_mul", || SimpLemma {
        name: Name::from_string("Nat.zero_mul"),
        lhs: make_nat_mul_pattern("Nat.zero", "n"),
        rhs: Expr::const_(Name::from_string("Nat.zero"), vec![]),
        eq_type: Some(nat_ty.clone()),
        proof_expr: None,
        index_mode: SimpIndexMode::Unindexed,
        priority: 100,
    });

    // Nat.sub_zero: n - 0 = n
    //
    // B103: explicitly `Unindexed`. Under Normal indexing its key ι-collapsed
    // to the bare star `?n` and only `insert_if_specific`'s too-generic
    // rejection happened to star it — make the star-tier discipline explicit
    // rather than an accident of the key rot.
    push_if_present(state, config, &mut lemmas, "Nat.sub_zero", || SimpLemma {
        name: Name::from_string("Nat.sub_zero"),
        lhs: make_nat_sub_pattern("n", "Nat.zero"),
        rhs: Expr::bvar(0),
        eq_type: Some(nat_ty.clone()),
        proof_expr: None,
        index_mode: SimpIndexMode::Unindexed,
        priority: 100,
    });

    // Nat.sub_self: n - n = 0
    push_if_present(state, config, &mut lemmas, "Nat.sub_self", || SimpLemma {
        name: Name::from_string("Nat.sub_self"),
        lhs: make_nat_sub_pattern("n", "n"),
        rhs: Expr::const_(Name::from_string("Nat.zero"), vec![]),
        eq_type: Some(nat_ty.clone()),
        proof_expr: None,
        index_mode: SimpIndexMode::Unindexed,
        priority: 100,
    });

    // Nat.zero_sub: 0 - n = 0
    push_if_present(state, config, &mut lemmas, "Nat.zero_sub", || SimpLemma {
        name: Name::from_string("Nat.zero_sub"),
        lhs: make_nat_sub_pattern("Nat.zero", "n"),
        rhs: Expr::const_(Name::from_string("Nat.zero"), vec![]),
        eq_type: Some(nat_ty.clone()),
        proof_expr: None,
        index_mode: SimpIndexMode::Unindexed,
        priority: 100,
    });

    // Nat.sub_one: n - 1 = Nat.pred n
    //
    // The `1` leaf is the RAW literal (B102's `Nat.mul_one` lesson): the
    // surface goal spells `1` as `Lit(Nat 1)` after the `OfNat` wrapper
    // collapses, and the unifier's two-literal fast path decides
    // `Lit 1 ≡ Lit 1` by value, while a `Nat.succ Nat.zero` leaf rots under
    // the key path's WHNF. `unify_core` still bridges a kernel-spelled
    // `Nat.succ Nat.zero` operand by reduction on disagreement.
    push_if_present(state, config, &mut lemmas, "Nat.sub_one", || SimpLemma {
        name: Name::from_string("Nat.sub_one"),
        lhs: Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.sub"), vec![]),
                Expr::bvar(0),
            ),
            Expr::nat_lit(1),
        ),
        rhs: Expr::app(
            Expr::const_(Name::from_string("Nat.pred"), vec![]),
            Expr::bvar(0),
        ),
        eq_type: Some(nat_ty.clone()),
        proof_expr: None,
        index_mode: SimpIndexMode::Unindexed,
        priority: 100,
    });

    // Nat.add_sub_cancel: a + b - b = a  (two binders: bvar1 = a, bvar0 = b)
    push_if_present(state, config, &mut lemmas, "Nat.add_sub_cancel", || {
        SimpLemma {
            name: Name::from_string("Nat.add_sub_cancel"),
            lhs: Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Nat.sub"), vec![]),
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Nat.add"), vec![]),
                            Expr::bvar(1),
                        ),
                        Expr::bvar(0),
                    ),
                ),
                Expr::bvar(0),
            ),
            rhs: Expr::bvar(1),
            eq_type: Some(nat_ty.clone()),
            proof_expr: None,
            index_mode: SimpIndexMode::Normal,
            priority: 100,
        }
    });

    lemmas
}

/// Collect built-in Bool simp lemmas.
pub(crate) fn collect_bool_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();
    let bool_ty = || Expr::const_(Name::from_string("Bool"), vec![]);

    // Bool.not_not: !!b = b
    push_if_present(state, config, &mut lemmas, "Bool.not_not", || SimpLemma {
        name: Name::from_string("Bool.not_not"),
        lhs: Expr::app(
            Expr::const_(Name::from_string("Bool.not"), vec![]),
            Expr::app(
                Expr::const_(Name::from_string("Bool.not"), vec![]),
                Expr::bvar(0),
            ),
        ),
        rhs: Expr::bvar(0),
        eq_type: Some(bool_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });

    // Single-variable Bool && / || identities. The LHS binds one `b` (bvar 0);
    // ground literals (true/false) are constants. Each kernel theorem is
    // registered in the prelude (`data_types_bool_simp.rs`), so `push_if_present`
    // picks them up once present.
    let btrue = || Expr::const_(Name::from_string("Bool.true"), vec![]);
    let bfalse = || Expr::const_(Name::from_string("Bool.false"), vec![]);

    // Bool.and_true: (b && true) = b
    push_if_present(state, config, &mut lemmas, "Bool.and_true", || SimpLemma {
        name: Name::from_string("Bool.and_true"),
        lhs: make_bool_and_pattern(Expr::bvar(0), btrue()),
        rhs: Expr::bvar(0),
        eq_type: Some(bool_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    // Bool.and_false: (b && false) = false
    push_if_present(state, config, &mut lemmas, "Bool.and_false", || SimpLemma {
        name: Name::from_string("Bool.and_false"),
        lhs: make_bool_and_pattern(Expr::bvar(0), bfalse()),
        rhs: bfalse(),
        eq_type: Some(bool_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    // Bool.true_and: (true && b) = b
    push_if_present(state, config, &mut lemmas, "Bool.true_and", || SimpLemma {
        name: Name::from_string("Bool.true_and"),
        lhs: make_bool_and_pattern(btrue(), Expr::bvar(0)),
        rhs: Expr::bvar(0),
        eq_type: Some(bool_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    // Bool.false_and: (false && b) = false
    push_if_present(state, config, &mut lemmas, "Bool.false_and", || SimpLemma {
        name: Name::from_string("Bool.false_and"),
        lhs: make_bool_and_pattern(bfalse(), Expr::bvar(0)),
        rhs: bfalse(),
        eq_type: Some(bool_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    // Bool.or_false: (b || false) = b
    push_if_present(state, config, &mut lemmas, "Bool.or_false", || SimpLemma {
        name: Name::from_string("Bool.or_false"),
        lhs: make_bool_or_pattern(Expr::bvar(0), bfalse()),
        rhs: Expr::bvar(0),
        eq_type: Some(bool_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    // Bool.or_true: (b || true) = true
    push_if_present(state, config, &mut lemmas, "Bool.or_true", || SimpLemma {
        name: Name::from_string("Bool.or_true"),
        lhs: make_bool_or_pattern(Expr::bvar(0), btrue()),
        rhs: btrue(),
        eq_type: Some(bool_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    // Bool.false_or: (false || b) = b
    push_if_present(state, config, &mut lemmas, "Bool.false_or", || SimpLemma {
        name: Name::from_string("Bool.false_or"),
        lhs: make_bool_or_pattern(bfalse(), Expr::bvar(0)),
        rhs: Expr::bvar(0),
        eq_type: Some(bool_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    // Bool.true_or: (true || b) = true
    push_if_present(state, config, &mut lemmas, "Bool.true_or", || SimpLemma {
        name: Name::from_string("Bool.true_or"),
        lhs: make_bool_or_pattern(btrue(), Expr::bvar(0)),
        rhs: btrue(),
        eq_type: Some(bool_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    // Bool.and_self: (b && b) = b
    push_if_present(state, config, &mut lemmas, "Bool.and_self", || SimpLemma {
        name: Name::from_string("Bool.and_self"),
        lhs: make_bool_and_pattern(Expr::bvar(0), Expr::bvar(0)),
        rhs: Expr::bvar(0),
        eq_type: Some(bool_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    // Bool.or_self: (b || b) = b
    push_if_present(state, config, &mut lemmas, "Bool.or_self", || SimpLemma {
        name: Name::from_string("Bool.or_self"),
        lhs: make_bool_or_pattern(Expr::bvar(0), Expr::bvar(0)),
        rhs: Expr::bvar(0),
        eq_type: Some(bool_ty()),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });

    lemmas
}

/// Helper to create a `Bool.and lhs rhs` pattern.
fn make_bool_and_pattern(left: Expr, right: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Bool.and"), vec![]), left),
        right,
    )
}

/// Helper to create a `Bool.or lhs rhs` pattern.
fn make_bool_or_pattern(left: Expr, right: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Bool.or"), vec![]), left),
        right,
    )
}

/// Collect built-in Prop simplification lemmas (And/Or/Not with True/False).
pub(crate) fn collect_prop_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();
    lemmas.extend(collect_prop_and_lemmas(state, config));
    lemmas.extend(collect_prop_or_lemmas(state, config));
    lemmas.extend(collect_prop_not_lemmas(state, config));
    lemmas.extend(collect_eq_ite_lemmas(state, config));
    lemmas
}

/// Reflexive-equality and canonical-`ite` simp lemmas: `eq_self`, `ite_true`,
/// `ite_false`. Each is a real kernel-checked theorem registered in the prelude
/// (`clean-kernel` `logic_simp_ite_eq.rs`), so `push_if_present` only emits the
/// rule once the proof constant exists in the env — keeping every rewrite
/// backed by a genuine `Eq` proof.
///
/// Bvar layout mirrors each theorem's binder order (outermost binder = highest
/// index), so the builtin `proof_expr: None` path reconstructs the proof as
/// `name <α> [<a> <b>]` matching the decl signature.
fn collect_eq_ite_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();
    // The `Eq`/`ite` constants are universe-polymorphic. A pattern hardcoding a
    // concrete level (e.g. `Eq.{0}`) fails to unify against a goal subterm whose
    // level is `Succ(Zero)` (e.g. `@Eq.{1} Nat n n`, since `Nat : Sort 1`). A
    // `Level::Param` head acts as a level metavariable in the simp unifier
    // (`unify_levels`), so it solves against whatever the goal's level is.
    let lvl = || Level::param(Name::from_string("u_simp"));
    let eq_ = || Expr::const_(Name::from_string("Eq"), vec![lvl()]);
    let ite_ = || Expr::const_(Name::from_string("ite"), vec![lvl()]);

    // eq_self : {α} (a) → @Eq Prop (@Eq α a a) True.
    // Binders: α = bvar1, a = bvar0. LHS pattern `@Eq α a a`, RHS `True`.
    push_if_present(state, config, &mut lemmas, "eq_self", || SimpLemma {
        name: Name::from_string("eq_self"),
        lhs: Expr::app(
            Expr::app(Expr::app(eq_(), Expr::bvar(1)), Expr::bvar(0)),
            Expr::bvar(0),
        ),
        rhs: mk_true(),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });

    // ite_true : {α} (a b) → @Eq α (@ite α True instDecidableTrue a b) a.
    // Binders: α = bvar2, a = bvar1, b = bvar0. LHS `@ite α True inst a b`,
    // RHS `a`.
    let inst_true = || Expr::const_(Name::from_string("instDecidableTrue"), vec![]);
    let inst_false = || Expr::const_(Name::from_string("instDecidableFalse"), vec![]);
    push_if_present(state, config, &mut lemmas, "ite_true", || SimpLemma {
        name: Name::from_string("ite_true"),
        lhs: mk_ite_pattern(ite_(), Expr::bvar(2), mk_true(), inst_true()),
        rhs: Expr::bvar(1),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });

    // ite_false : {α} (a b) → @Eq α (@ite α False instDecidableFalse a b) b.
    push_if_present(state, config, &mut lemmas, "ite_false", || SimpLemma {
        name: Name::from_string("ite_false"),
        lhs: mk_ite_pattern(ite_(), Expr::bvar(2), mk_false(), inst_false()),
        rhs: Expr::bvar(0),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });

    lemmas
}

/// `@ite α cond inst (bvar 1) (bvar 0)` — the LHS pattern for `ite_true`/
/// `ite_false`. `a` = bvar1, `b` = bvar0 (the two value binders).
fn mk_ite_pattern(ite: Expr, alpha: Expr, cond: Expr, inst: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::app(ite, alpha), cond), inst),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    )
}

fn mk_true() -> Expr {
    Expr::const_(Name::from_string("True"), vec![])
}
fn mk_false() -> Expr {
    Expr::const_(Name::from_string("False"), vec![])
}

/// Prop And lemmas: and_true, true_and, and_false, false_and.
fn collect_prop_and_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();
    let and_ = || Expr::const_(Name::from_string("And"), vec![]);

    push_if_present(state, config, &mut lemmas, "and_true", || SimpLemma {
        name: Name::from_string("and_true"),
        lhs: Expr::app(Expr::app(and_(), Expr::bvar(0)), mk_true()),
        rhs: Expr::bvar(0),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    push_if_present(state, config, &mut lemmas, "true_and", || SimpLemma {
        name: Name::from_string("true_and"),
        lhs: Expr::app(Expr::app(and_(), mk_true()), Expr::bvar(0)),
        rhs: Expr::bvar(0),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    push_if_present(state, config, &mut lemmas, "and_false", || SimpLemma {
        name: Name::from_string("and_false"),
        lhs: Expr::app(Expr::app(and_(), Expr::bvar(0)), mk_false()),
        rhs: mk_false(),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    push_if_present(state, config, &mut lemmas, "false_and", || SimpLemma {
        name: Name::from_string("false_and"),
        lhs: Expr::app(Expr::app(and_(), mk_false()), Expr::bvar(0)),
        rhs: mk_false(),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    push_if_present(state, config, &mut lemmas, "and_self", || SimpLemma {
        name: Name::from_string("and_self"),
        lhs: Expr::app(Expr::app(and_(), Expr::bvar(0)), Expr::bvar(0)),
        rhs: Expr::bvar(0),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    lemmas
}

/// Prop Or lemmas: or_true, true_or, or_false, false_or.
fn collect_prop_or_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();
    let or_ = || Expr::const_(Name::from_string("Or"), vec![]);

    push_if_present(state, config, &mut lemmas, "or_true", || SimpLemma {
        name: Name::from_string("or_true"),
        lhs: Expr::app(Expr::app(or_(), Expr::bvar(0)), mk_true()),
        rhs: mk_true(),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    push_if_present(state, config, &mut lemmas, "true_or", || SimpLemma {
        name: Name::from_string("true_or"),
        lhs: Expr::app(Expr::app(or_(), mk_true()), Expr::bvar(0)),
        rhs: mk_true(),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    push_if_present(state, config, &mut lemmas, "or_false", || SimpLemma {
        name: Name::from_string("or_false"),
        lhs: Expr::app(Expr::app(or_(), Expr::bvar(0)), mk_false()),
        rhs: Expr::bvar(0),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    push_if_present(state, config, &mut lemmas, "false_or", || SimpLemma {
        name: Name::from_string("false_or"),
        lhs: Expr::app(Expr::app(or_(), mk_false()), Expr::bvar(0)),
        rhs: Expr::bvar(0),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    push_if_present(state, config, &mut lemmas, "or_self", || SimpLemma {
        name: Name::from_string("or_self"),
        lhs: Expr::app(Expr::app(or_(), Expr::bvar(0)), Expr::bvar(0)),
        rhs: Expr::bvar(0),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    lemmas
}

/// Prop Not lemmas: not_true, not_false.
fn collect_prop_not_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();
    let not_ = || Expr::const_(Name::from_string("Not"), vec![]);

    push_if_present(state, config, &mut lemmas, "not_true", || SimpLemma {
        name: Name::from_string("not_true"),
        lhs: Expr::app(not_(), mk_true()),
        rhs: mk_false(),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    push_if_present(state, config, &mut lemmas, "not_false", || SimpLemma {
        name: Name::from_string("not_false"),
        lhs: Expr::app(not_(), mk_false()),
        rhs: mk_true(),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
    lemmas
}

/// Collect built-in List simp lemmas.
///
/// Currently registers `List.append_nil : xs ++ [] = xs`. The reducing
/// direction `[] ++ xs = xs` closes by ι-reduction (rfl) without a lemma, but
/// the symbolic-tail direction is stuck on the recursion target and needs the
/// kernel-proved `List.append_nil` theorem (registered, axiom-free, by
/// `init_list_ops`).
///
/// The pattern is the BARE-op `@List.append.{u_simp} ?α ?xs (@List.nil.{u_simp}
/// ?α)`. simp's `reduce_op_projection_head` peels the `HAppend.hAppend`
/// typeclass projection off the goal `xs ++ []` to expose bare `List.append`
/// before unifying — the exact mechanism by which the bare-`Nat.add` Nat lemmas
/// match `HAdd`-headed goals. The `u_simp` level param is solved by the unifier
/// and re-applied to the reconstructed `@List.append_nil.{u_simp} α xs` proof
/// (the universe-polymorphic path already handled for `Eq.{u_simp}`/`ite`).
///
/// SOUNDNESS: the pattern's 2nd append arg is literally `@List.nil ?α` (sharing
/// the SAME `?α` as the list) and the RHS is the 1st arg `?xs`, so it only
/// fires on `xs ++ []` and rewrites to `xs`. It cannot match `xs ++ ys` (ys not
/// nil ⇒ unify fails) nor synthesize `[]` from `[] ++ xs`. The reconstructed
/// proof is the kernel-checked `List.append_nil`; `close_goal`/`add_decl`
/// re-verify, so any mis-assembly fails closed.
pub(crate) fn collect_list_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();

    // List.append_nil: xs ++ [] = xs
    //
    // BVar(1) ↦ ?α (implicit, applied FIRST — matches `{α}`),
    // BVar(0) ↦ ?xs (explicit, applied LAST — matches `(xs)`).
    // The reverse-order proof reconstruction in `simp/expr.rs` applies
    // BVar(1) then BVar(0), assembling `@List.append_nil α xs`.
    push_if_present(state, config, &mut lemmas, "List.append_nil", || {
        SimpLemma {
            name: Name::from_string("List.append_nil"),
            lhs: make_list_append_nil_pattern(),
            rhs: Expr::bvar(0),
            // `List α : Type u_simp` — left as None; simp infers the carrier and
            // the kernel re-check governs soundness (mirrors Bool/Prop lemmas).
            eq_type: None,
            proof_expr: None,
            // B103: nil-operand identity — same WHNF-rotted-key disease as the
            // Nat literal-operand identities (`List.append ?xs nil` δ-unfolds
            // to its stuck `List.rec` body under the key path), so star-keyed.
            index_mode: SimpIndexMode::Unindexed,
            priority: 100,
        }
    });

    // List.length_nil: (@List.nil α).length = 0
    //
    // BVar(0) ↦ ?α (the only metavar). The proof reconstructs
    // `@List.length_nil.{u_simp} α`.
    push_if_present(state, config, &mut lemmas, "List.length_nil", || {
        SimpLemma {
            name: Name::from_string("List.length_nil"),
            lhs: make_list_length_nil_pattern(),
            rhs: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            eq_type: Some(Expr::const_(Name::from_string("Nat"), vec![])),
            proof_expr: None,
            // B103: nil-operand identity — its pattern ι-collapses fully to
            // `Nat.zero` under the key path (a bogus-specific key), so
            // star-keyed like the Nat literal-operand identities.
            index_mode: SimpIndexMode::Unindexed,
            priority: 100,
        }
    });

    // List.length_cons: (@List.cons α x xs).length = Nat.succ xs.length
    //
    // BVar(2) ↦ ?α, BVar(1) ↦ ?x, BVar(0) ↦ ?xs (reverse-applied as α x xs).
    // The proof reconstructs `@List.length_cons.{u_simp} α x xs`.
    push_if_present(state, config, &mut lemmas, "List.length_cons", || {
        SimpLemma {
            name: Name::from_string("List.length_cons"),
            lhs: make_list_length_cons_pattern(),
            rhs: Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                make_list_length_app(Expr::bvar(2), Expr::bvar(0)),
            ),
            eq_type: Some(Expr::const_(Name::from_string("Nat"), vec![])),
            proof_expr: None,
            index_mode: SimpIndexMode::Normal,
            priority: 100,
        }
    });

    // List.length_append: (xs ++ ys).length = xs.length + ys.length
    //
    // BVar(2) ↦ ?α, BVar(1) ↦ ?xs, BVar(0) ↦ ?ys (reverse-applied as α xs ys).
    // The proof reconstructs `@List.length_append.{u_simp} α xs ys`.
    //
    // The goal's `++`/`+` are HAppend/HAdd-projection-headed; simp's
    // `reduce_op_projection_head` peels the typeclass projections off the goal
    // to expose bare `List.append`/`Nat.add` before unifying — the same path
    // the bare-`Nat.add` lemmas and `List.append_nil` already rely on. The
    // bare-`Nat.add` RHS is def-eq to the goal's `HAdd`-headed RHS, so after the
    // rewrite the goal becomes `a = a`, closed by the existing `eq_self` lemma.
    push_if_present(state, config, &mut lemmas, "List.length_append", || {
        SimpLemma {
            name: Name::from_string("List.length_append"),
            lhs: make_list_length_append_pattern(),
            rhs: Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Nat.add"), vec![]),
                    make_list_length_app(Expr::bvar(2), Expr::bvar(1)),
                ),
                make_list_length_app(Expr::bvar(2), Expr::bvar(0)),
            ),
            eq_type: Some(Expr::const_(Name::from_string("Nat"), vec![])),
            proof_expr: None,
            index_mode: SimpIndexMode::Normal,
            priority: 100,
        }
    });

    lemmas
}

/// Build `@List.length.{u_simp} α l` for the given `α` / `l` sub-patterns.
fn make_list_length_app(alpha: Expr, l: Expr) -> Expr {
    let u_simp = Level::param(Name::from_string("u_simp"));
    let list_length = Expr::const_(Name::from_string("List.length"), vec![u_simp]);
    Expr::app(Expr::app(list_length, alpha), l)
}

/// Build `@List.length.{u_simp} ?α (@List.nil.{u_simp} ?α)` (`?α` = BVar(0)).
fn make_list_length_nil_pattern() -> Expr {
    let u_simp = Level::param(Name::from_string("u_simp"));
    let alpha = Expr::bvar(0);
    let list_nil = Expr::const_(Name::from_string("List.nil"), vec![u_simp]);
    let nil = Expr::app(list_nil, alpha.clone());
    make_list_length_app(alpha, nil)
}

/// Build `@List.length.{u_simp} ?α (@List.cons.{u_simp} ?α ?x ?xs)`.
///
/// `?α` = BVar(2), `?x` = BVar(1), `?xs` = BVar(0).
fn make_list_length_cons_pattern() -> Expr {
    let u_simp = Level::param(Name::from_string("u_simp"));
    let alpha = Expr::bvar(2);
    let x = Expr::bvar(1);
    let xs = Expr::bvar(0);
    let list_cons = Expr::const_(Name::from_string("List.cons"), vec![u_simp]);
    let cons = Expr::app(Expr::app(Expr::app(list_cons, alpha.clone()), x), xs);
    make_list_length_app(alpha, cons)
}

/// Build `@List.length.{u_simp} ?α (@List.append.{u_simp} ?α ?xs ?ys)`.
///
/// `?α` = BVar(2), `?xs` = BVar(1), `?ys` = BVar(0).
fn make_list_length_append_pattern() -> Expr {
    let u_simp = Level::param(Name::from_string("u_simp"));
    let alpha = Expr::bvar(2);
    let xs = Expr::bvar(1);
    let ys = Expr::bvar(0);
    let list_append = Expr::const_(Name::from_string("List.append"), vec![u_simp]);
    let append = Expr::app(Expr::app(Expr::app(list_append, alpha.clone()), xs), ys);
    make_list_length_app(alpha, append)
}

/// Build the bare-op pattern `@List.append.{u_simp} ?α ?xs (@List.nil.{u_simp}
/// ?α)` for `List.append_nil`.
///
/// `?α` is `BVar(1)` (shared between the `List.append` type arg and the
/// `List.nil` type arg), `?xs` is `BVar(0)`. The consts carry a `u_simp` level
/// param so the unifier solves the universe and the proof-reconstruction path
/// re-applies it (same as `Eq.{u_simp}`/`ite.{u_simp}`).
fn make_list_append_nil_pattern() -> Expr {
    let u_simp = Level::param(Name::from_string("u_simp"));
    let alpha = Expr::bvar(1);
    let xs = Expr::bvar(0);
    let list_append = Expr::const_(Name::from_string("List.append"), vec![u_simp.clone()]);
    let list_nil = Expr::const_(Name::from_string("List.nil"), vec![u_simp]);
    // @List.nil.{u_simp} ?α
    let nil = Expr::app(list_nil, alpha.clone());
    // @List.append.{u_simp} ?α ?xs (@List.nil ?α)
    Expr::app(Expr::app(Expr::app(list_append, alpha), xs), nil)
}

/// Push a lemma if the constant is present in the environment and not excluded.
fn push_if_present(
    state: &ProofState,
    config: &SimpConfig,
    lemmas: &mut Vec<SimpLemma>,
    name: &str,
    make_lemma: impl FnOnce() -> SimpLemma,
) {
    let n = Name::from_string(name);
    if state.env.get_const(&n).is_some() && !config.exclude.contains(name) {
        lemmas.push(make_lemma());
    }
}

/// Helper to create a Nat.add pattern.
fn make_nat_add_pattern(left: &str, right: &str) -> Expr {
    let left_expr = if left == "n" {
        Expr::bvar(0)
    } else {
        Expr::const_(Name::from_string(left), vec![])
    };
    let right_expr = if right == "n" {
        Expr::bvar(0)
    } else {
        Expr::const_(Name::from_string(right), vec![])
    };

    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            left_expr,
        ),
        right_expr,
    )
}

/// Helper to create a Nat.sub pattern.
fn make_nat_sub_pattern(left: &str, right: &str) -> Expr {
    let left_expr = if left == "n" {
        Expr::bvar(0)
    } else {
        Expr::const_(Name::from_string(left), vec![])
    };
    let right_expr = if right == "n" {
        Expr::bvar(0)
    } else {
        Expr::const_(Name::from_string(right), vec![])
    };

    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.sub"), vec![]),
            left_expr,
        ),
        right_expr,
    )
}

/// Which operand of a `Nat.mul` pattern carries the literal `1`.
enum NatMulLitSide {
    /// `1 * ?n` (`Nat.one_mul`)
    LitLeft,
    /// `?n * 1` (`Nat.mul_one`)
    LitRight,
}

/// Build `Nat.mul ?n (Lit 1)` / `Nat.mul (Lit 1) ?n` for the `mul_one` /
/// `one_mul` identity patterns. Uses the raw `Lit(Nat 1)` leaf so the
/// unifier's literal fast path matches the goal's own literal spelling; see
/// the `Nat.mul_one` registration comment (B102).
fn make_nat_mul_lit_pattern(side: NatMulLitSide) -> Expr {
    let one = Expr::nat_lit(1);
    let n = Expr::bvar(0);
    let (left_expr, right_expr) = match side {
        NatMulLitSide::LitLeft => (one, n),
        NatMulLitSide::LitRight => (n, one),
    };
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            left_expr,
        ),
        right_expr,
    )
}

/// Helper to create a Nat.mul pattern.
fn make_nat_mul_pattern(left: &str, right: &str) -> Expr {
    let left_expr = if left == "n" {
        Expr::bvar(0)
    } else {
        Expr::const_(Name::from_string(left), vec![])
    };
    let right_expr = if right == "n" {
        Expr::bvar(0)
    } else {
        Expr::const_(Name::from_string(right), vec![])
    };

    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            left_expr,
        ),
        right_expr,
    )
}
