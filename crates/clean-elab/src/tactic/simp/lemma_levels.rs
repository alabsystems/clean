// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fresh universe levels for every USE of a simp lemma.
//!
//! # Lean's rule
//!
//! `SimpTheorem.getValue` (`Lean/Meta/Tactic/Simp/SimpTheorems.lean:403-412`)
//! instantiates a universe-polymorphic theorem's level parameters with FRESH
//! level metavariables (`mkFreshLevelMVar`) every time the rewriter tries it
//! (`Rewrite.lean:179`, `let val ← thm.getValue`), and matching then solves
//! them. `Eq` and `Iff` theorems are treated alike: `preprocess` turns
//! `a ↔ b` into `propext h : a = b` before any of this happens.
//!
//! # What Clean did instead, and what it cost
//!
//! Clean matched the lemma's stored pattern as it was lifted out of the
//! declaration's type, so its levels are spelled by the DECLARATION's own
//! parameter names (`u`, `u_1`, …), and the matcher's `MetaState` keys level
//! parameters BY NAME. Two defects followed.
//!
//! * The `Iff` template (`mk_iff_rewrite_proof_template`, built at
//!   registration) never had those names replaced at all, so every
//!   universe-polymorphic `↔` lemma was refused wholesale as
//!   `REJECT template-level` — `eq_comm`, `forall_eq`, `forall_eq'`,
//!   `Classical.not_forall`, `exists_comm`, `beq_iff_eq`, `Pi.le_def`,
//!   `Prod.lt_iff`, `Function.update_eq_iff`, … Measured 2026-09-12 on the
//!   pinned source-elaboration slice: 27 `Mathlib/Logic/Basic`,
//!   `Logic/Function/Basic`, `Logic/Unique` and `Order/Basic` rows.
//! * Even the `Eq` path could not tell a lemma parameter that matching never
//!   touched from one legitimately unified with the goal's SAME-NAMED
//!   parameter (Mathlib's ubiquitous `u_1`): both read back as `u_1`.
//!
//! [`LemmaLevels`] renames the lemma's declared parameters to names in the
//! reserved `?` space no surface identifier can reach (see
//! [`crate::level_mint::MINT_PREFIX`]) and never repeats, so after matching a
//! fresh name that is still present is exactly an unsolved level — the test
//! Lean's `hasAssignableMVar proof` makes before accepting a rewrite.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::LazyLock;

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level, LocalContext};

use super::args::SIMP_ARG_RULE_PREFIX;
use super::expr::collect_binder_types_in_conclusion;
use super::pattern::substitute_bvars_with_metas;
use super::types::SimpLemma;
use crate::tactic::core::{Goal, ProofState};
use crate::unify::{MetaState, Unifier, UnifyResult};

/// Stem of every fresh simp level name. `?` cannot start a surface
/// identifier, and `ElabCtx::elab_level` refuses any WRITTEN universe name in
/// that space, so no goal can mention one.
static FRESH_STEM: LazyLock<Name> = LazyLock::new(|| Name::from_string("?simp_u"));

/// Monotone source of fresh-name suffixes. Process-wide, so two uses — the
/// outer rewrite and a discharger's nested `simp` — can never share a name.
static FRESH_COUNTER: AtomicU64 = AtomicU64::new(0);

/// A simp lemma's universe parameters, renamed for one match attempt.
pub(super) struct LemmaLevels {
    /// The declaration's own parameter names, as its stored pattern spells them.
    declared: Vec<Name>,
    /// The fresh name standing in for each of `declared`, position by position.
    fresh_names: Vec<Name>,
    /// `fresh_names` as levels, for `instantiate_level_params_direct`.
    fresh: Vec<Level>,
}

impl LemmaLevels {
    /// The renaming for one attempt to rewrite with `lemma`.
    ///
    /// Environment rules carry their declaration's universe parameters.
    /// Term arguments carry the residual universe metavariables from their
    /// elaborated proof. Local hypotheses carry the goal's rigid parameters.
    pub(super) fn for_lemma(state: &ProofState, lemma: &SimpLemma) -> Self {
        let declared = if crate::namespace::name_has_prefix(&lemma.name, &SIMP_ARG_RULE_PREFIX) {
            let mut declared = Vec::new();
            if let Some(proof) = &lemma.proof_expr {
                collect_level_params(proof, &mut declared);
                declared
                    .retain(|name| crate::level_mint::is_reserved_level_name(&name.to_string()));
            }
            declared
        } else if is_local_rule(lemma) {
            Vec::new()
        } else {
            state
                .env
                .get_const(&lemma.name)
                .map_or_else(Vec::new, |info| info.level_params.clone())
        };
        let fresh_names: Vec<Name> = declared
            .iter()
            .map(|_| {
                FRESH_STEM
                    .clone()
                    .num(FRESH_COUNTER.fetch_add(1, Ordering::Relaxed))
            })
            .collect();
        let fresh = fresh_names.iter().cloned().map(Level::param).collect();
        Self {
            declared,
            fresh_names,
            fresh,
        }
    }

    /// Whether there is nothing to rename.
    pub(super) fn is_empty(&self) -> bool {
        self.declared.is_empty()
    }

    /// `e` with the declared parameters replaced by their fresh names.
    pub(super) fn rename(&self, e: &Expr) -> Expr {
        e.instantiate_level_params_direct(&self.declared, &self.fresh)
    }

    /// Each fresh level as the match resolved it (still the fresh name when
    /// unsolved), in declaration order.
    pub(super) fn resolved(&self, metas: &MetaState) -> Vec<Level> {
        self.fresh
            .iter()
            .map(|lvl| metas.instantiate_level(lvl))
            .collect()
    }

    /// Whether `lvl` still mentions a fresh name, i.e. an unsolved level.
    pub(super) fn level_is_unsolved(&self, lvl: &Level) -> bool {
        !self.is_empty() && level_mentions(lvl, &self.fresh_names)
    }

    /// Whether any fresh level is still unsolved in `metas` — false in the
    /// common case, where every level the lemma has occurs in its pattern.
    pub(super) fn has_unsolved(&self, metas: &MetaState) -> bool {
        self.fresh
            .iter()
            .any(|lvl| self.level_is_unsolved(&metas.instantiate_level(lvl)))
    }

    /// Whether `e` still mentions a fresh name anywhere, i.e. carries an
    /// unsolved level. Always `false` for an empty renaming.
    pub(super) fn mentions_unsolved(&self, e: &Expr) -> bool {
        !self.is_empty() && expr_mentions_levels(e, &self.fresh_names)
    }

    /// Solve the fresh levels the LHS match left open from the TYPES of the
    /// arguments it bound, then refuse nothing: an unsolved level is refused
    /// later, where the proof is assembled.
    ///
    /// Lean's `isDefEq` assigns a pattern metavariable only after checking
    /// its type (`checkTypesAndAssign`), and that check is where `?u` in
    /// `?α : Sort ?u` meets `Nat : Type`. Clean's pattern metavariables carry
    /// a placeholder type, so a level only a BINDER TYPE mentions —
    /// `implies_true.{u} (α : Sort u) : (α → True) = True`, whose pattern is
    /// just `?α → True` — is never touched by matching. This walks the
    /// declaration's telescope (renamed) outermost-first and unifies each
    /// bound argument's inferred type with its binder's instantiated domain,
    /// inside a scope that is rolled back when they do not unify.
    ///
    /// The goal's own level parameters are declared rigid for the attempt,
    /// so solving can assign only this lemma's fresh levels: a goal's `u`
    /// is a parameter, never something a rewrite may re-spell.
    ///
    /// REQUIRES: the declaration's type re-derives the lemma's stored
    ///   pattern (the caller checks `statement_yields_pattern`), so its
    ///   telescope describes `bvar_to_meta`'s keys.
    pub(super) fn solve_from_bound_argument_types(
        &self,
        state: &ProofState,
        goal: &Goal,
        declared_type: &Expr,
        metas: &mut MetaState,
        bvar_to_meta: &hashbrown::HashMap<u32, Expr>,
    ) {
        if self.is_empty() {
            return;
        }
        let telescope = collect_binder_types_in_conclusion(&self.rename(declared_type));
        for index in (0..telescope.len()).rev() {
            let Some(meta_expr) = bvar_to_meta.get(&(index as u32)) else {
                continue;
            };
            let domain = substitute_bvars_with_metas(&telescope[index], bvar_to_meta);
            let domain = metas.instantiate_levels(&metas.instantiate(&domain));
            if !self.mentions_unsolved(&domain)
                || domain.has_loose_bvars()
                || super::expr::contains_unassigned_meta(&domain)
            {
                continue;
            }
            let arg = metas.instantiate_levels(&metas.instantiate(meta_expr));
            if arg.has_loose_bvars() || super::expr::contains_unassigned_meta(&arg) {
                continue;
            }
            let Ok(arg_ty) = state.infer_type(goal, &arg) else {
                continue;
            };
            for name in goal_level_params(&arg_ty) {
                metas.add_rigid_level_param(name);
            }
            metas.push_scope();
            let unified = {
                let mut unifier = Unifier::with_env(metas, &state.env, LocalContext::new());
                matches!(unifier.unify(&domain, &arg_ty), UnifyResult::Success)
            };
            if unified {
                metas.commit();
            } else {
                metas.pop_scope();
            }
        }
    }
}

/// Whether `lemma` is a rule minted from a LOCAL hypothesis (`simp [h]`,
/// `simp [*]`, `simp_rw [h]`) rather than from an environment declaration.
///
/// Every local rule's proof template is built on the hypothesis's free
/// variable (`lemmas::collect_local_extra_lemma`, `local_prop_hyp_lemma`,
/// `collect_hypothesis_lemmas`, `rw::collect_local_rw_simp_lemmas`), and no
/// environment rule's template can mention one: it is the declaration's
/// constant applied to the lemma's own binders, wrapped by closed constants
/// (`propext`, `Iff.intro`, `And.left`, …), or there is no template at all (an
/// `=` lemma is assembled from its name).
///
/// The rule's NAME does not decide it, which is what this test used to read.
/// A `@[simp]` lemma stays in the simp set when a hypothesis happens to share
/// its name — Lean's registry is not shadowed by the local context — and
/// reading it as a local rule skipped its level renaming, so a
/// universe-polymorphic `↔` lemma so shadowed was refused as
/// `template-level` (measured 2026-09-20: `(reg_lem : n = n) ⊢ RR n` under
/// `@[simp] reg_lem : RR x ↔ True` made no progress; pinned Lean closes it).
pub(super) fn is_local_rule(lemma: &SimpLemma) -> bool {
    lemma.proof_expr.as_ref().is_some_and(Expr::has_fvar_quick)
}

/// The non-reserved universe parameters `e` mentions: the level parameters
/// of the goal a rewrite is stated over, which a match may never assign.
///
/// Names in the reserved `?` space are left out — they are the elaborator's
/// own universe METAVARIABLES (`?u_N`), which matching could always solve.
pub(super) fn goal_level_params(e: &Expr) -> Vec<Name> {
    let mut out: Vec<Name> = Vec::new();
    collect_level_params(e, &mut out);
    out.retain(|name| !crate::level_mint::is_reserved_level_name(&name.to_string()));
    out
}

fn collect_level_params(e: &Expr, out: &mut Vec<Name>) {
    crate::stack_safe(|| {
        if !e.has_level_param_quick() {
            return;
        }
        match e.kind() {
            ExprKind::Sort(level) => push_params(level, out),
            ExprKind::Const(_, levels) => {
                for level in levels.iter() {
                    push_params(level, out);
                }
            }
            ExprKind::App(f, a) => {
                collect_level_params(f, out);
                collect_level_params(a, out);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                collect_level_params(ty, out);
                collect_level_params(body, out);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                collect_level_params(ty, out);
                collect_level_params(val, out);
                collect_level_params(body, out);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                collect_level_params(inner, out);
            }
            _ => {}
        }
    });
}

fn push_params(level: &Level, out: &mut Vec<Name>) {
    let mut params = Vec::new();
    level.collect_params(&mut params);
    for p in params {
        if !out.contains(&p) {
            out.push(p);
        }
    }
}

/// Whether any `Sort` or `Const` level in `e` mentions one of `names`.
fn expr_mentions_levels(e: &Expr, names: &[Name]) -> bool {
    crate::stack_safe(|| {
        if !e.has_level_param_quick() {
            return false;
        }
        match e.kind() {
            ExprKind::Sort(level) => level_mentions(level, names),
            ExprKind::Const(_, levels) => levels.iter().any(|lvl| level_mentions(lvl, names)),
            ExprKind::App(f, a) => expr_mentions_levels(f, names) || expr_mentions_levels(a, names),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                expr_mentions_levels(ty, names) || expr_mentions_levels(body, names)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                expr_mentions_levels(ty, names)
                    || expr_mentions_levels(val, names)
                    || expr_mentions_levels(body, names)
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                expr_mentions_levels(inner, names)
            }
            _ => false,
        }
    })
}

/// Whether a universe level mentions any of `names`, at any depth.
fn level_mentions(level: &Level, names: &[Name]) -> bool {
    match level {
        Level::Param(p) => names.iter().any(|n| n == p),
        Level::Succ(inner) => level_mentions(inner, names),
        Level::Max(a, b) | Level::IMax(a, b) => {
            level_mentions(a, names) || level_mentions(b, names)
        }
        Level::Zero => false,
    }
}
