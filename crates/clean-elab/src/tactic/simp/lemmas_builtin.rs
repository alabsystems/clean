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
    lemmas.extend(collect_logic_iff_lemmas(state, config));
    lemmas
}

/// Lean 4.8 core's `@[simp]` logic lemmas that Clean's prelude carries as
/// kernel-checked theorems (`clean-kernel` `logic_simp_iff.rs`), G39 (ledger
/// (109)). Each is read off its DECLARED type, as a registry lemma is — an
/// equation as `lhs = rhs`, an `Iff` through `lemmas::mk_iff_simp_lemma` — so
/// the rule is the theorem's own statement, and under `import Init` the same
/// names are Lean's constants read the same way. A name the environment lacks
/// contributes nothing.
///
/// `imp_false` is NOT read as a rule: its `?a → False` pattern met Clean's
/// reducible `Not`; it is its own step (`simp/imp_false.rs`).
///
/// `ne_eq` turns `a ≠ b` into `¬(a = b)`, so the constructor step and the
/// `Not` lemmas reach a disequality as they do in Lean. Until the 4.30 world
/// switched the legacy constructor-disequality closer off (decision
/// "Bind constructor simplification to the selected source world",
/// 2026-11-11) that closer alone closed `some v ≠ none`; without this rule
/// plain `simp` made no progress on it (G64).
const LOGIC_IFF_SIMP_LEMMAS: [&str; 8] = [
    "ite_eq_left_iff",
    "ite_eq_right_iff",
    "Decidable.not_not",
    "not_false_eq_true",
    "not_true_eq_false",
    "implies_true",
    "false_implies",
    "ne_eq",
];

fn collect_logic_iff_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    LOGIC_IFF_SIMP_LEMMAS
        .iter()
        .filter_map(|text| {
            let name = Name::from_string(text);
            if config
                .exclude
                .contains(&clean_parser::SurfaceName::from_name(name.clone()))
            {
                return None;
            }
            let decl = state.env.get_const(&name)?;
            if let Some((eq_type, lhs, rhs)) = super::expr::extract_equality_full(&decl.type_) {
                return Some(SimpLemma {
                    name,
                    lhs,
                    rhs,
                    eq_type: Some(eq_type),
                    proof_expr: None,
                    index_mode: SimpIndexMode::Normal,
                    priority: 100,
                });
            }
            super::lemmas::mk_iff_simp_lemma(&name, &decl.type_, 100, &decl.level_params)
        })
        .collect()
}

/// Lean 4.8's `simpOnlyBuiltins` (`[eq_self, iff_self]`), which every `simp
/// only` starts from; Clean's prelude has no `iff_self`, so `eq_self` alone.
pub(crate) fn collect_simp_only_builtins(
    state: &ProofState,
    config: &SimpConfig,
) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();
    push_eq_self(state, config, &mut lemmas);
    lemmas
}

/// `eq_self : {α} (a) → @Eq Prop (@Eq α a a) True` (α = bvar1, a = bvar0);
/// the `Eq` level is a `Level::Param` the simp unifier solves.
fn push_eq_self(state: &ProofState, config: &SimpConfig, lemmas: &mut Vec<SimpLemma>) {
    let level = Level::param(Name::from_string("u_simp"));
    let eq_ = Expr::const_(Name::from_string("Eq"), vec![level]);
    push_if_present(state, config, lemmas, "eq_self", || SimpLemma {
        name: Name::from_string("eq_self"),
        lhs: Expr::apps(eq_, [Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)]),
        rhs: mk_true(),
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });
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
    let ite_ = || Expr::const_(Name::from_string("ite"), vec![lvl()]);

    push_eq_self(state, config, &mut lemmas);

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

/// Push a lemma if the constant is present in the environment and not excluded.
pub(super) fn push_if_present(
    state: &ProofState,
    config: &SimpConfig,
    lemmas: &mut Vec<SimpLemma>,
    name: &str,
    make_lemma: impl FnOnce() -> SimpLemma,
) {
    let n = Name::from_string(name);
    if state.env.get_const(&n).is_some()
        && !config
            .exclude
            .contains(&clean_parser::SurfaceName::from_name(n.clone()))
    {
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
