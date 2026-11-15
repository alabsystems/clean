// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Simp lemma collection from the environment.
//!
//! Gathers built-in arithmetic/boolean rules, @[simp]-registered lemmas from
//! the environment registry, user-specified extra lemmas, and aesop simp lemmas
//! into a priority-ordered `SimpLemmaSet`.

use std::collections::HashMap;

use clean_kernel::env::ConstantKind;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

use super::expr::{extract_equality_full, extract_iff_with_binders, mk_iff_rewrite_proof_template};
use super::lemmas_local::local_prop_hyp_lemma;
pub(super) use super::lemmas_local::{
    local_rule_binder_types, prop_false_proof, prop_simp_lemmas_from_proof, prop_true_proof,
    type_is_prop,
};
use super::prop_lemmas::mk_prop_simp_lemmas;
use super::types::{SimpConfig, SimpIndexMode, SimpLemma, SimpLemmaSet, UnfoldDef};
use super::{lemmas_builtin, lemmas_builtin_list};
use crate::name_resolution::resolve_identifier;
use crate::tactic::core::ProofState;
use crate::tactic::core::TacticError;
use crate::tactic::match_equality;

/// Collect simp lemmas from the environment.
///
/// # Contract
///
/// REQUIRES: `state` has a valid environment with loaded constants
/// REQUIRES: `config.exclude` lists lemma names to skip
/// ENSURES: Returned lemmas are well-typed equality rewrite rules (`lhs = rhs`)
/// ENSURES: Excluded lemmas from `config.exclude` are not present in result
/// ENSURES: Lemmas are sorted by priority (most specific first, fallback last)
/// ENSURES: Each lemma has valid `lhs` and `rhs` extracted from its type
pub(crate) fn collect_simp_lemmas(state: &ProofState, config: &SimpConfig) -> SimpLemmaSet {
    collect_simp_lemmas_with_memo(state, config, None)
}

/// [`collect_simp_lemmas`], taking the key paths of closed lemma patterns from
/// `memo` (`index_path_memo.rs`); the cached-set rebuild is the one caller
/// that passes one.
pub(crate) fn collect_simp_lemmas_with_memo(
    state: &ProofState,
    config: &SimpConfig,
    memo: Option<&mut super::index_path_memo::PathMemo>,
) -> SimpLemmaSet {
    let mut lemmas = Vec::new();

    // In `simp only` mode, skip built-in and @[simp] registry lemmas.
    // Only `extra_lemmas`, `aesop_simp_lemmas`, and hypothesis-derived lemmas
    // are used. Beta/eta reduction still applies (controlled by config flags).
    if !config.only {
        lemmas.extend(lemmas_builtin::collect_nat_lemmas(state, config));
        lemmas.extend(lemmas_builtin::collect_bool_lemmas(state, config));
        lemmas.extend(lemmas_builtin::collect_prop_lemmas(state, config));
        lemmas.extend(lemmas_builtin_list::collect_list_lemmas(state, config));

        // Add registered @[simp] lemmas from the environment registry (#1670)
        lemmas.extend(collect_registry_lemmas(state, config));
    } else if config.simprocs.runs_simp_only_builtins() {
        // Lean's `simp only` starts from `simpOnlyBuiltins`; see
        // `SimprocScope::runs_simp_only_builtins` for why only this scope.
        lemmas.extend(lemmas_builtin::collect_simp_only_builtins(state, config));
    }

    // Add user-specified extra lemmas (by name)
    lemmas.extend(collect_extra_lemmas(state, config));

    // `simp [*]` semantics: add all equality hypotheses from the local context
    // as rewrite lemmas. This lets `simp [*]` use h : a = b from the context.
    if config.use_hypotheses {
        lemmas.extend(collect_hypothesis_lemmas(state, config));
    }

    // Add aesop simp lemmas (already constructed, from @[aesop norm simp] rules)
    lemmas.extend(config.aesop_simp_lemmas.iter().cloned());

    // Sort by priority (higher first)
    lemmas.sort_by_key(|b| std::cmp::Reverse(b.priority));

    SimpLemmaSet::from_state_memo(state, lemmas, memo)
}

/// Collect user-specified extra lemmas (by name).
pub(super) fn collect_extra_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();
    for lemma_name in &config.extra_lemmas {
        // Lean's `simpGoal` removes the hypothesis being simplified from its
        // own set; a name that IS that hypothesis yields no rule.
        if config
            .exclude_hypothesis
            .as_ref()
            .is_some_and(|name| name == lemma_name)
        {
            continue;
        }
        let local_rules = collect_local_extra_lemma(state, lemma_name);
        if !local_rules.is_empty() {
            lemmas.extend(local_rules);
            continue;
        }

        let name = resolve_extra_lemma_name(state, lemma_name);
        if let Some(decl) = state.env.get_const(&name) {
            if let Some((eq_type, lhs, rhs)) = extract_equality_full(&decl.type_) {
                lemmas.push(SimpLemma {
                    name,
                    lhs,
                    rhs,
                    eq_type: Some(eq_type),
                    proof_expr: None,
                    index_mode: SimpIndexMode::Normal,
                    priority: 50,
                });
            } else if let Some(lemma) =
                mk_iff_simp_lemma(&name, &decl.type_, 50, &decl.level_params)
            {
                lemmas.push(lemma);
            } else if let Some(eqs) = config
                .prepared_rec_equations
                .get(&name)
                .cloned()
                .or_else(|| super::rec_equations::synthesize_rec_def_equations(&state.env, &name))
            {
                // A definition compiled to a `T.rec` value gets Lean-style
                // per-constructor equational lemmas instead of a delta-unfold
                // (which would rewrite the goal into a stuck recursor form no
                // IH can match — the rec-iota simp class, B7).
                // `resolve_unfold_defs` skips exactly these names.
                lemmas.extend(eqs.into_iter().filter(|equation| {
                    !config
                        .exclude
                        .contains(&clean_parser::SurfaceName::from_name(equation.name.clone()))
                }));
            } else {
                // A constant whose TYPE is any other proposition — a
                // theorem, an axiom, a constructor of an inductive
                // proposition, a proposition-valued field — is Lean's
                // `preprocess` form: `p = True`, `p = False`,
                // `(a = b) = False`, the halves of a conjunction
                // (`prop_lemmas`). A definition of any other type yields
                // nothing here.
                lemmas.extend(mk_prop_simp_lemmas(state, &name, 50));
            }
            // Otherwise, if the constant is a Definition whose type is not an
            // equality (e.g. `StateT.bind`, `Except.bind`, monadic helper
            // definitions), it is captured by `resolve_unfold_defs` and
            // delta-unfolded by `simp_expr`, not here as an equality rewrite
            // lemma. See #3518.
        } else {
            // A named simp lemma that resolves to NOTHING used to vanish here
            // with no diagnostic (`if let Some(decl) = …` with no `else`), so
            // `simp [<a name this environment lacks>]` degenerated to plain
            // `simp` and the row reported "no progress" instead of naming the
            // missing lemma — the cascade-masking class.
            //
            // Lean's `elabSimpArgs` THROWS on such an argument. Clean does not
            // yet, deliberately: under `--imports-prefer-olean` a derived name
            // the decoder does not mint (a `to_dual` twin, say) would turn
            // every row that currently degrades gracefully into a hard
            // failure, and that blast radius has not been measured. The
            // diagnostic is the part that costs nothing.
            //
            // A name that IS a local yields no rule here whenever the local is
            // not a proposition (`n : Nat`, `f : α → β`), and `simp_all` pushes
            // hypothesis names into `extra_lemmas` on every call — so saying
            // "names nothing in this environment" about one would be both
            // false and, inside an aesop search, said thousands of times.
            let names_a_local = state.current_goal().is_some_and(|goal| {
                goal.local_ctx.iter().any(|decl| {
                    crate::tactic::pattern::names::hypothesis_named(&decl.name, lemma_name)
                })
            });
            if !names_a_local {
                tracing::warn!(
                    "simp: lemma `{}` names nothing in this environment and was \
                     skipped; the rewrite set is the one you would get without it",
                    lemma_name
                );
            }
        }
    }
    lemmas
}

/// Resolve an extra-lemma name to a fully-qualified environment constant,
/// consulting the opened-namespace context when one is available.
///
/// `simp [extra_lemma]` historically looked the name up only as the literal
/// string the user wrote (`Name::from_string` + `env.get_const`). That fails
/// for unqualified names brought into scope by `open`: after `open Nat`,
/// `simp [add_zero]` could not reach `Nat.add_zero`. Term references do not
/// have this problem because the elaborator resolves them through
/// [`resolve_identifier`], which tries the current namespace outward, then
/// each opened namespace, then the literal (root) name — Lean's
/// `resolveGlobalName` order (B03). This helper applies the same order
/// to simp's name-based lemma path.
///
/// SOUNDNESS: resolution only succeeds when the candidate names a constant
/// that actually exists in the environment (`resolve_identifier` checks
/// `env.get_const`). When no opened-namespace match is found — or when no
/// namespace context was threaded — it falls back to the literal name, so
/// behavior is unchanged for already-qualified names and the caller's
/// existing `get_const` lookup still governs whether the lemma is used.
fn resolve_extra_lemma_name(state: &ProofState, lemma_name: &clean_parser::SurfaceName) -> Name {
    let literal = lemma_name
        .qualify_under(&clean_parser::SurfaceName::default())
        .into_name();
    match state.namespace_state() {
        Some(ns_state) => resolve_identifier(lemma_name, ns_state, &state.env).unwrap_or(literal),
        None => literal,
    }
}

/// Resolve `extra_lemmas` names that refer to `Declaration::Definition`
/// bodies into a delta-unfold map.
///
/// Used by top-level simp entrypoints (`simp`, `simp_only`, `simp_at_*`,
/// `simp_all`) to enable `simp [foo]` to unfold `foo` when `foo` is a
/// definition rather than an equality lemma. Matches Lean 4's `simp`
/// delta-unfolding semantics (`Lean/Meta/Tactic/Simp/Rewrite.lean`).
///
/// # Contract
///
/// REQUIRES: `state.env` is populated.
/// ENSURES: Each entry `(name -> value)` in the result corresponds to a
///   `Declaration::Definition` in the environment whose `type_` does NOT
///   already match an equality pattern. Equality-typed theorems/definitions
///   remain in the lemma set and are not also unfolded.
/// ENSURES: Names that do not resolve to a constant, or resolve to an axiom,
///   inductive, constructor, or equality-typed declaration are skipped.
/// ENSURES: Names shadowed by a local hypothesis are skipped (locals already
///   take priority via `collect_local_extra_lemma`).
/// ENSURES: Part of #3518.
pub(crate) fn resolve_unfold_defs(
    state: &ProofState,
    extra_lemmas: &[clean_parser::SurfaceName],
    prepared: &mut HashMap<Name, Vec<SimpLemma>>,
) -> HashMap<Name, UnfoldDef> {
    let mut out = HashMap::new();
    let goal = state.current_goal();
    for lemma_name in extra_lemmas {
        // Local hypotheses shadow environment constants.
        if let Some(g) = goal {
            if g.local_ctx
                .iter()
                .any(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, lemma_name))
            {
                continue;
            }
        }
        let name = resolve_extra_lemma_name(state, lemma_name);
        let Some(decl) = state.env.get_const(&name) else {
            continue;
        };
        // Equality- and iff-typed declarations are rewrite lemmas, not unfold
        // targets (an `Iff` conclusion becomes an `Eq` rewrite via propext —
        // see `mk_iff_simp_lemma`).
        if extract_equality_full(&decl.type_).is_some()
            || extract_iff_with_binders(&decl.type_).is_some()
        {
            continue;
        }
        // Only `Definition`-kind constants expose a reducible body we may
        // substitute in. Axioms, constructors, inductives, recursors, and
        // opaques either have no body or must not be delta-unfolded.
        // Theorems are also skipped: proof terms are not intended as
        // rewrite-unfold targets for `simp`.
        if matches!(decl.kind, ConstantKind::Definition) {
            // A rec-compiled definition is served as per-constructor
            // equational lemmas by `collect_extra_lemmas` (rec-iota simp
            // class, B7); delta-unfolding it here would rewrite the goal into
            // a stuck recursor form those equations (and the local IHs) can
            // no longer match. The same synthesis call keeps the two sites
            // agreeing exactly: any def it refuses stays on this unfold path.
            if let Some(equations) =
                super::rec_equations::synthesize_rec_def_equations(&state.env, &name)
            {
                prepared.insert(name, equations);
                continue;
            }
            if let Some(value) = &decl.value {
                out.insert(
                    name,
                    UnfoldDef {
                        level_params: decl.level_params.clone(),
                        value: value.clone(),
                    },
                );
            }
        }
    }
    out
}

/// Seed `config.unfold_defs` with the bodies of globally `@[simp]`-tagged
/// *definitions* (B15).
///
/// In Lean 4, `@[simp] def f` registers `f`'s equation lemmas in the default
/// simp set, so a bare `simp` unfolds `f`. Clean models a non-recursive
/// `@[simp] def` as a delta-unfold of its body (the equation lemma of a
/// non-pattern-matching def is exactly `f x = <body>`). This makes the `@[simp]`
/// tag on a *definition* OBSERVABLE: without the tag, `simp` no longer unfolds
/// `f` (matching Lean's "simp made no progress" once the reflexivity closer runs
/// at reducible transparency); with the tag, `f` unfolds.
///
/// Only applies to the default simp set — skipped in `simp only` mode (which
/// excludes the global `@[simp]` set). Skips: equality/iff-typed decls (those
/// are rewrite lemmas, handled by `collect_registry_lemmas`), non-`Definition`
/// constants (theorems/axioms/ctors expose no delta body), excluded names, and
/// self-referential (recursive) bodies (a naive delta-unfold would re-introduce
/// the constant and loop up to `max_steps`; Lean uses per-branch equation lemmas
/// that clean does not model here).
///
/// SOUNDNESS: each inserted `(name, body)` comes from a
/// `Declaration::Definition` in the environment, so substituting `name → body`
/// is definitional; `simp_expr` records it with `proof: None` and the kernel
/// re-check at `close_goal` is the backstop.
pub(crate) fn seed_unfold_defs_from_simp_defs(state: &ProofState, config: &mut SimpConfig) {
    if config.only {
        return;
    }
    for info in state.env.get_simp_lemmas() {
        let name = &info.name;
        if config
            .exclude
            .contains(&clean_parser::SurfaceName::from_name(name.clone()))
        {
            continue;
        }
        let Some(decl) = state.env.get_const(name) else {
            continue;
        };
        if !matches!(decl.kind, ConstantKind::Definition) {
            continue;
        }
        // Equality/iff conclusions are rewrite lemmas, not unfold targets.
        if extract_equality_full(&decl.type_).is_some()
            || extract_iff_with_binders(&decl.type_).is_some()
        {
            continue;
        }
        if super::rec_equations::synthesize_rec_def_equations(&state.env, name).is_some() {
            continue;
        }
        let Some(value) = &decl.value else {
            continue;
        };
        if value_references_const(value, name) {
            continue;
        }
        config
            .unfold_defs
            .entry(name.clone())
            .or_insert_with(|| UnfoldDef {
                level_params: decl.level_params.clone(),
                value: value.clone(),
            });
    }
}

/// Whether `e` syntactically references the constant `name` (used to skip
/// recursive `@[simp] def`s in [`seed_unfold_defs_from_simp_defs`]).
fn value_references_const(e: &Expr, name: &Name) -> bool {
    match e.kind() {
        ExprKind::Const(n, _) => n == name,
        ExprKind::App(f, a) => value_references_const(f, name) || value_references_const(a, name),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            value_references_const(t, name) || value_references_const(b, name)
        }
        ExprKind::Let(_, t, v, b, _) => {
            value_references_const(t, name)
                || value_references_const(v, name)
                || value_references_const(b, name)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            value_references_const(inner, name)
        }
        _ => false,
    }
}

/// Resolve an extra lemma name from the current goal's local context.
///
/// Local hypotheses should shadow environment constants for `simp_all`,
/// `simp_only`, and similar name-based entrypoints.
///
/// Empty when no local has that name or the local yields no rule (it is not
/// a proposition); the caller then resolves the name globally. One local can
/// yield several rules: a conjunction is split (`local_prop_hyp_lemma`).
fn collect_local_extra_lemma(
    state: &ProofState,
    lemma_name: &clean_parser::SurfaceName,
) -> Vec<SimpLemma> {
    let Some(goal) = state.current_goal() else {
        return Vec::new();
    };
    // The MOST RECENT local of that name, as Lean resolves a shadowed name.
    let Some(hyp_decl) = goal
        .local_ctx
        .iter()
        .rev()
        .find(|decl| crate::tactic::pattern::names::hypothesis_named(&decl.name, lemma_name))
    else {
        return Vec::new();
    };
    collect_local_extra_lemma_for_decl(state, goal, hyp_decl)
}

/// Automatic context walks keep the selected local identity instead of
/// resolving its spelling again after a newer local shadows it.
pub(in crate::tactic) fn collect_local_extra_lemma_for_decl(
    state: &ProofState,
    goal: &crate::tactic::Goal,
    hyp_decl: &crate::tactic::LocalDecl,
) -> Vec<SimpLemma> {
    let hyp_ty = state.whnf(goal, &hyp_decl.ty);
    let Some((binder_count, eq_type, lhs, rhs, _levels)) = extract_local_equality_template(&hyp_ty)
    else {
        return local_prop_hyp_lemma(state, goal, hyp_decl, 50);
    };
    let proof_template = mk_local_proof_template(Expr::fvar(hyp_decl.fvar), binder_count);

    vec![SimpLemma {
        name: hyp_decl.name.name().clone(),
        lhs: state.metas.instantiate(&lhs),
        rhs: state.metas.instantiate(&rhs),
        eq_type: Some(state.metas.instantiate(&eq_type)),
        proof_expr: Some(state.metas.instantiate(&proof_template)),
        index_mode: SimpIndexMode::NoIndexAtArgs,
        priority: 50,
    }]
}

pub(crate) fn extract_local_equality_template(
    ty: &Expr,
) -> Option<(u32, Expr, Expr, Expr, Vec<Level>)> {
    let mut binder_count = 0;
    let mut current = ty;
    while let ExprKind::Pi(_, _, body) = current.kind() {
        binder_count += 1;
        current = body;
    }

    let (eq_type, lhs, rhs, levels) = match_equality(current).ok()?;
    Some((binder_count, eq_type, lhs, rhs, levels))
}

pub(crate) fn mk_local_proof_template(mut proof: Expr, binder_count: u32) -> Expr {
    for idx in (0..binder_count).rev() {
        proof = Expr::app(proof, Expr::bvar(idx));
    }
    proof
}

/// Collect equality hypotheses from the current goal's local context as simp lemmas.
///
/// This implements `simp [*]` semantics: all hypotheses of the form `h : a = b`
/// (possibly under forall binders) become rewrite lemmas for the goal.
///
/// REQUIRES: `state` has at least one goal with a local context.
/// ENSURES: Each returned lemma has `proof_expr` set to the hypothesis fvar
///   applied to its binder arguments, so the rewrite carries a real proof term.
/// ENSURES: EVERY Prop hypothesis yields a rule — an equation as itself, and
///   anything else through `local_prop_hyp_lemma`, Lean's `preprocess`.
/// ENSURES: `config.exclude_hypothesis` never yields a rule.
/// ENSURES: a hypothesis named in `config.exclude` (`simp [*, -h]`) never
///   yields a rule — Lean's `applyStarArg` skips an erased `.fvar` origin.
///
/// Lean's `[*]` is `applyStarArg` (`Lean/Elab/Tactic/Simp.lean`): it loops
/// over `getPropHyps` — EVERY Prop hypothesis — and calls
/// `simpTheorems.addTheorem (.fvar h)`, the same `preprocess` a named lemma
/// takes, so `hab : a ≤ b` becomes `(a ≤ b) = True` and `ha : a ≤ b → p a`
/// becomes the conditional `∀ (_ : a ≤ b), p a = True`. Clean used to keep
/// only `h : a = b`-shaped locals here and drop the rest with no diagnostic,
/// which is why `simp only [ha, hab]` proved goals `simp [*]` could not — the
/// named path has always had the fall-through (`collect_local_extra_lemma`).
pub(super) fn collect_hypothesis_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    let excluded = state.current_goal().and_then(|goal| {
        config.exclude_hypothesis.as_ref().and_then(|name| {
            goal.local_ctx
                .iter()
                .rev()
                .find(|decl| crate::tactic::pattern::names::hypothesis_named(&decl.name, name))
                .map(|decl| decl.fvar)
        })
    });
    collect_hypothesis_lemmas_excluding(state, config, excluded)
}

pub(super) fn collect_hypothesis_lemmas_excluding(
    state: &ProofState,
    config: &SimpConfig,
    excluded: Option<clean_kernel::FVarId>,
) -> Vec<SimpLemma> {
    let Some(goal) = state.current_goal() else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for decl in &goal.local_ctx {
        // Lean removes the hypothesis being simplified from its own set
        // (`simpGoal`); without this a `simp [*] at h` would rewrite `h : P`
        // to `True` by `h` itself.
        if excluded == Some(decl.fvar) {
            continue;
        }
        // `simp [*, -h]`: Lean's `applyStarArg` guards its `getPropHyps` loop
        // with `unless simpTheorems.isErased (.fvar h)`, so an erased LOCAL
        // never joins the star set either. Pinned v4.30.0-rc2 refuses
        // `example (h : P) : P := by simp [*, -h]` ("`simp` made no
        // progress") while accepting it without the `-h`. `-` only gained a
        // writer (`SimpConfig::exclude`) with the `simpArg` port, so before
        // that the two channels could not disagree.
        if config.exclude.iter().any(|name| {
            goal.local_ctx
                .iter()
                .rev()
                .find(|candidate| {
                    crate::tactic::pattern::names::hypothesis_named(&candidate.name, name)
                })
                .is_some_and(|candidate| candidate.fvar == decl.fvar)
        }) {
            continue;
        }
        let hyp_ty = state.whnf(goal, &decl.ty);
        let Some((binder_count, eq_type, lhs, rhs, _levels)) =
            extract_local_equality_template(&hyp_ty)
        else {
            // Every other PROPOSITION is Lean's `preprocess` form. Priority 75
            // keeps the `[*]` slot (between the registry's 100 and a named
            // extra lemma's 50); a non-Prop local yields nothing, which is
            // `local_prop_hyp_lemma`'s own `Sort 0` check.
            out.extend(local_prop_hyp_lemma(state, goal, decl, 75));
            continue;
        };
        let proof_template = mk_local_proof_template(Expr::fvar(decl.fvar), binder_count);
        out.push(SimpLemma {
            name: decl.name.name().clone(),
            lhs: state.metas.instantiate(&lhs),
            rhs: state.metas.instantiate(&rhs),
            eq_type: Some(state.metas.instantiate(&eq_type)),
            proof_expr: Some(state.metas.instantiate(&proof_template)),
            index_mode: SimpIndexMode::NoIndexAtArgs,
            priority: 75, // Between registry (100) and user extra (50)
        });
    }
    out
}

/// Build a `SimpLemma` from a constant whose conclusion is `Iff lhs rhs`.
///
/// In Lean 4 an `@[simp]` lemma of the form `h : a ↔ b` (optionally under
/// leading binders) rewrites `a` to `b` (`Lean/Meta/Tactic/Simp/SimpTheorems.lean`
/// turns the biconditional into an `Eq` rewrite through `propext`). Clean's simp
/// engine consumes only `Eq` proofs, so we register the pattern `lhs → rhs` and
/// store a `proof_expr` template that wraps the lemma application with `propext`
/// to yield a genuine `lhs = rhs` proof.
///
/// Returns `None` when the type does not conclude in `Iff` (callers fall through
/// to the equality path / unfold handling). Soundness: the rewrite direction is
/// `lhs → rhs`, matching the iff's left-to-right reading; no reverse direction is
/// invented for non-symmetric (`→`) lemmas because only `Iff` conclusions reach
/// here. The `propext`-wrapped witness introduces no axiom beyond the
/// foundational `propext`.
pub(super) fn mk_iff_simp_lemma(
    name: &Name,
    ty: &Expr,
    priority: u32,
    level_params: &[Name],
) -> Option<SimpLemma> {
    let (binder_count, lhs, rhs) = extract_iff_with_binders(ty)?;
    let proof_expr = mk_iff_rewrite_proof_template(name, binder_count, &lhs, &rhs, level_params);
    Some(SimpLemma {
        name: name.clone(),
        lhs,
        rhs,
        // The rewrite is a `Prop` equality (`a = b` with `a b : Prop`).
        eq_type: Some(Expr::prop()),
        proof_expr: Some(proof_expr),
        index_mode: SimpIndexMode::Normal,
        priority,
    })
}

/// Collect simp lemmas from the environment's @[simp] registry (#1670).
///
/// Skips hardcoded builtin names (already added inline) and excluded lemmas.
/// Extracts LHS/RHS from each lemma's declared equality type.
fn collect_registry_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    const HARDCODED: &[&str] = &[
        "Nat.add_zero",
        "Nat.zero_add",
        "Nat.mul_one",
        "Nat.one_mul",
        "Nat.mul_zero",
        "Nat.zero_mul",
        "Bool.not_not",
        "and_true",
        "true_and",
        "and_false",
        "false_and",
        "or_true",
        "true_or",
        "or_false",
        "false_or",
        "not_true",
        "not_false",
        // G39: collected by `lemmas_builtin::collect_logic_iff_lemmas`.
        "ite_eq_left_iff",
        "ite_eq_right_iff",
        "imp_false",
        "Decidable.not_not",
        "not_false_eq_true",
        "not_true_eq_false",
        "implies_true",
        "false_implies",
        "ne_eq",
    ];
    let mut out = Vec::new();
    for info in state.env.get_simp_lemmas() {
        let name_str = clean_parser::SurfaceName::from_name(info.name.clone());
        if HARDCODED
            .iter()
            .any(|text| info.name == Name::from_string(text))
            || config.exclude.contains(&name_str)
        {
            continue;
        }
        out.extend(
            attr_simp_lemmas(state, &info.name, info.priority.value())
                .into_iter()
                .filter(|equation| {
                    !config
                        .exclude
                        .contains(&clean_parser::SurfaceName::from_name(equation.name.clone()))
                }),
        );
    }

    // `get_simp_lemmas()` iterates a HashMap; stabilize equal-priority registry
    // lemmas so simp rewrite selection is deterministic across runs.
    out.sort_by(|a, b| a.name.cmp(&b.name));
    out
}

/// The rewrite rules a `@[simp]` attribute on constant `name` contributes, as
/// Lean's `mkSimpTheoremsFromConst` makes them: an `=` conclusion as it is, an
/// `↔` through `propext`, any other proposition through `preprocess`
/// (`Nat.zero_le : 0 ≤ n` becomes `(0 ≤ n) = True`). Empty when `name` names
/// nothing.
fn attr_simp_lemmas(state: &ProofState, name: &Name, priority: u32) -> Vec<SimpLemma> {
    let Some(decl) = state.env.get_const(name) else {
        return Vec::new();
    };
    if let Some((eq_type, lhs, rhs)) = extract_equality_full(&decl.type_) {
        vec![SimpLemma {
            name: name.clone(),
            lhs,
            rhs,
            eq_type: Some(eq_type),
            proof_expr: None,
            index_mode: SimpIndexMode::Normal,
            priority,
        }]
    } else if let Some(lemma) = mk_iff_simp_lemma(name, &decl.type_, priority, &decl.level_params) {
        vec![lemma]
    } else if let Some(mut equations) =
        super::rec_equations::synthesize_rec_def_equations(&state.env, name)
    {
        for equation in &mut equations {
            equation.priority = priority;
        }
        equations
    } else {
        mk_prop_simp_lemmas(state, name, priority)
    }
}

/// Collect simp lemmas by name from the environment.
///
/// Strict version of the extra-lemma path in `collect_simp_lemmas` for
/// tactic-owned lemma bundles (cast proof-carry, etc.) where every named
/// constant must exist and must be an equality rewrite rule.
///
/// REQUIRES: Each name in `names` is present in `state.env`.
/// REQUIRES: Each constant's type extracts as `@Eq α lhs rhs` (possibly under binders).
/// ENSURES: Returns one `SimpLemma` per name with `proof_expr: None` (proof
///   reconstructed from the constant name + instantiated binder arguments).
/// ENSURES: Returns `EnvironmentMissing` if any name is absent.
/// ENSURES: Returns `InvalidTarget` if any constant is not an equality.
pub(crate) fn collect_named_eq_lemmas(
    state: &ProofState,
    names: &[&str],
    priority: u32,
) -> Result<Vec<SimpLemma>, TacticError> {
    let mut lemmas = Vec::with_capacity(names.len());
    for &name_str in names {
        let name = Name::from_string(name_str);
        let decl = state
            .env
            .get_const(&name)
            .ok_or_else(|| TacticError::EnvironmentMissing {
                constant: name_str.to_string(),
            })?;
        let (eq_type, lhs, rhs) =
            extract_equality_full(&decl.type_).ok_or_else(|| TacticError::InvalidTarget {
                tactic: "collect_named_eq_lemmas".to_string(),
                detail: format!("{name_str} is not an equality"),
            })?;
        lemmas.push(SimpLemma {
            name,
            lhs,
            rhs,
            eq_type: Some(eq_type),
            proof_expr: None,
            index_mode: SimpIndexMode::Normal,
            priority,
        });
    }
    Ok(lemmas)
}

#[cfg(test)]
mod namespace_resolution_tests {
    use super::*;
    use crate::namespace::NamespaceState;
    use clean_kernel::env::Declaration;
    use clean_kernel::{Environment, Level};

    fn nat_ty() -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }

    fn mk_eq(ty: &Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    ty.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Register `Nat.add_zero : a = a` (shape is all the lemma path inspects).
    fn add_nat_add_zero(env: &mut Environment) {
        let nat = nat_ty();
        let a = Expr::const_(Name::from_string("a"), vec![]);
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("a"),
            level_params: vec![],
            type_: nat.clone(),
        })
        .expect("register a");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.add_zero"),
            level_params: vec![],
            type_: mk_eq(&nat, a.clone(), a),
        })
        .expect("register Nat.add_zero");
    }

    fn test_env() -> Environment {
        let mut env = Environment::new();
        env.init_nat().expect("init nat");
        env.init_eq().expect("init eq");
        add_nat_add_zero(&mut env);
        env
    }

    /// Build a `simp only` config naming a single extra lemma.
    fn only_config(lemma: &'static str) -> SimpConfig {
        SimpConfig {
            only: true,
            extra_lemmas: vec![clean_parser::SurfaceName::generated_path(lemma)],
            ..SimpConfig::new()
        }
    }

    #[test]
    fn prepared_equations_are_rebuilt_for_each_invocation() {
        let mut env = Environment::with_prelude();
        let declaration = clean_parser::parse_decl(
            "def cachedRec : Nat → Nat | Nat.zero => Nat.zero | Nat.succ n => Nat.succ (cachedRec n)",
        ).expect("recursive declaration");
        crate::elaborate_decl_and_register(&mut env, &declaration).expect("register definition");
        let state = ProofState::new(env, nat_ty());
        let mut config = only_config("cachedRec");
        super::super::seed_unfold_defs_from_extras(&state, &mut config);
        let name = Name::from_string("cachedRec");
        let prepared = config
            .prepared_rec_equations
            .get(&name)
            .expect("prepared equations");
        assert_eq!(prepared.len(), 2);
        assert!(!config.unfold_defs.contains_key(&name));
        let collected = collect_extra_lemmas(&state, &config);
        assert_eq!(collected.len(), prepared.len());
        assert!(collected
            .iter()
            .zip(prepared)
            .all(|(a, b)| a.lhs == b.lhs && a.rhs == b.rhs));

        // Reusing the config against another environment must not carry the
        // former invocation's family, even when the requested name is unchanged.
        let other = ProofState::new(Environment::with_prelude(), nat_ty());
        super::super::seed_unfold_defs_from_extras(&other, &mut config);
        assert!(config.prepared_rec_equations.is_empty());
        assert!(collect_extra_lemmas(&other, &config).is_empty());
    }

    fn state_with_open(env: Environment, opened: &[&str]) -> ProofState {
        let target = mk_eq(&nat_ty(), nat_ty(), nat_ty());
        let mut state = ProofState::new(env, target);
        let mut ns = NamespaceState::new();
        for ns_name in opened {
            ns.open_namespace(Name::from_string(ns_name));
        }
        state.set_namespace_state(ns);
        state
    }

    // The gap: without namespace resolution the unqualified `add_zero` would
    // be looked up literally and missed. With `open Nat` threaded into the
    // proof state it must resolve to `Nat.add_zero`.
    #[test]
    fn test_collect_extra_lemmas_opened_namespace_resolves_unqualified() {
        let state = state_with_open(test_env(), &["Nat"]);
        let config = only_config("add_zero");
        let lemmas = collect_extra_lemmas(&state, &config);
        assert_eq!(
            lemmas.len(),
            1,
            "open Nat should let `add_zero` resolve to Nat.add_zero"
        );
        assert_eq!(lemmas[0].name, Name::from_string("Nat.add_zero"));
    }

    // Regression: a bare qualified name still resolves directly even with an
    // open in scope (resolve_identifier tries the literal name first).
    #[test]
    fn test_collect_extra_lemmas_qualified_name_still_resolves() {
        let state = state_with_open(test_env(), &["Nat"]);
        let config = only_config("Nat.add_zero");
        let lemmas = collect_extra_lemmas(&state, &config);
        assert_eq!(lemmas.len(), 1);
        assert_eq!(lemmas[0].name, Name::from_string("Nat.add_zero"));
    }

    // An unqualified name with no namespace context set falls back to the
    // literal lookup, which misses — no panic, no spurious lemma.
    #[test]
    fn test_collect_extra_lemmas_no_namespace_state_unqualified_misses() {
        let target = mk_eq(&nat_ty(), nat_ty(), nat_ty());
        let state = ProofState::new(test_env(), target);
        assert!(state.namespace_state().is_none());
        let config = only_config("add_zero");
        let lemmas = collect_extra_lemmas(&state, &config);
        assert!(
            lemmas.is_empty(),
            "without an open, the bare `add_zero` should not resolve"
        );
    }

    // An unknown lemma falls back to the literal name and is simply not
    // collected (clean miss, not a panic or mis-resolution).
    #[test]
    fn test_collect_extra_lemmas_unknown_lemma_falls_back_cleanly() {
        let state = state_with_open(test_env(), &["Nat"]);
        let config = only_config("no_such_lemma");
        let lemmas = collect_extra_lemmas(&state, &config);
        assert!(lemmas.is_empty());
    }

    // The opened namespace must actually contain the constant: opening an
    // unrelated namespace must not mis-resolve `add_zero`.
    #[test]
    fn test_collect_extra_lemmas_wrong_namespace_does_not_resolve() {
        let state = state_with_open(test_env(), &["List"]);
        let config = only_config("add_zero");
        let lemmas = collect_extra_lemmas(&state, &config);
        assert!(
            lemmas.is_empty(),
            "opening List must not resolve add_zero to Nat.add_zero"
        );
    }

    // `resolve_extra_lemma_name` resolves through the open and falls back to
    // the literal name when nothing matches.
    #[test]
    fn test_resolve_extra_lemma_name_through_open_and_fallback() {
        let state = state_with_open(test_env(), &["Nat"]);
        assert_eq!(
            resolve_extra_lemma_name(
                &state,
                &clean_parser::SurfaceName::generated_path("add_zero")
            ),
            Name::from_string("Nat.add_zero")
        );
        // Unknown name falls back to the literal (so the caller's get_const
        // miss governs behavior, not a panic).
        assert_eq!(
            resolve_extra_lemma_name(&state, &clean_parser::SurfaceName::generated_path("ghost")),
            Name::from_string("ghost")
        );
    }
}
