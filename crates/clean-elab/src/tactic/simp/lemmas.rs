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
use super::lemmas_builtin;
use super::types::{SimpConfig, SimpIndexMode, SimpLemma, SimpLemmaSet};
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
    let mut lemmas = Vec::new();

    // In `simp only` mode, skip built-in and @[simp] registry lemmas.
    // Only `extra_lemmas`, `aesop_simp_lemmas`, and hypothesis-derived lemmas
    // are used. Beta/eta reduction still applies (controlled by config flags).
    if !config.only {
        lemmas.extend(lemmas_builtin::collect_nat_lemmas(state, config));
        lemmas.extend(lemmas_builtin::collect_bool_lemmas(state, config));
        lemmas.extend(lemmas_builtin::collect_prop_lemmas(state, config));
        lemmas.extend(lemmas_builtin::collect_list_lemmas(state, config));

        // Add registered @[simp] lemmas from the environment registry (#1670)
        lemmas.extend(collect_registry_lemmas(state, config));
    }

    // Add user-specified extra lemmas (by name)
    lemmas.extend(collect_extra_lemmas(state, config));

    // `simp [*]` semantics: add all equality hypotheses from the local context
    // as rewrite lemmas. This lets `simp [*]` use h : a = b from the context.
    if config.use_hypotheses {
        lemmas.extend(collect_hypothesis_lemmas(state));
    }

    // Add aesop simp lemmas (already constructed, from @[aesop norm simp] rules)
    lemmas.extend(config.aesop_simp_lemmas.iter().cloned());

    // Sort by priority (higher first)
    lemmas.sort_by_key(|b| std::cmp::Reverse(b.priority));

    SimpLemmaSet::from_state(state, lemmas)
}

/// Collect user-specified extra lemmas (by name).
fn collect_extra_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();
    for lemma_name in &config.extra_lemmas {
        if let Some(local_lemma) = collect_local_extra_lemma(state, lemma_name) {
            lemmas.push(local_lemma);
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
            } else if let Some(lemma) = mk_iff_simp_lemma(&name, &decl.type_, 50) {
                lemmas.push(lemma);
            }
            // If the constant is a Definition whose type is not an equality
            // (e.g. `StateT.bind`, `Except.bind`, monadic helper definitions),
            // it is captured by `resolve_unfold_defs` and delta-unfolded by
            // `simp_expr`, not here as an equality rewrite lemma. See #3518.
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
fn resolve_extra_lemma_name(state: &ProofState, lemma_name: &str) -> Name {
    let literal = Name::from_string(lemma_name);
    match state.namespace_state() {
        Some(ns_state) => resolve_identifier(&literal, ns_state, &state.env).unwrap_or(literal),
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
    extra_lemmas: &[String],
) -> HashMap<Name, Expr> {
    let mut out = HashMap::new();
    let goal = state.current_goal();
    for lemma_name in extra_lemmas {
        // Local hypotheses shadow environment constants.
        if let Some(g) = goal {
            if g.local_ctx.iter().any(|d| d.name == *lemma_name) {
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
            if let Some(value) = &decl.value {
                out.insert(name, value.clone());
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
        if config.exclude.contains(&name.to_string()) {
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
        let Some(value) = &decl.value else {
            continue;
        };
        if value_references_const(value, name) {
            continue;
        }
        config
            .unfold_defs
            .entry(name.clone())
            .or_insert_with(|| value.clone());
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
fn collect_local_extra_lemma(state: &ProofState, lemma_name: &str) -> Option<SimpLemma> {
    let goal = state.current_goal()?;
    let hyp_decl = goal.local_ctx.iter().find(|decl| decl.name == lemma_name)?;
    let hyp_ty = state.whnf(goal, &hyp_decl.ty);
    let (binder_count, eq_type, lhs, rhs, _levels) = extract_local_equality_template(&hyp_ty)?;
    let proof_template = mk_local_proof_template(Expr::fvar(hyp_decl.fvar), binder_count);

    Some(SimpLemma {
        name: Name::from_string(lemma_name),
        lhs: state.metas.instantiate(&lhs),
        rhs: state.metas.instantiate(&rhs),
        eq_type: Some(state.metas.instantiate(&eq_type)),
        proof_expr: Some(state.metas.instantiate(&proof_template)),
        index_mode: SimpIndexMode::NoIndexAtArgs,
        priority: 50,
    })
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
/// ENSURES: Only equality-shaped hypotheses are included; non-equality hypotheses
///   are silently skipped.
fn collect_hypothesis_lemmas(state: &ProofState) -> Vec<SimpLemma> {
    let Some(goal) = state.current_goal() else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for decl in &goal.local_ctx {
        let hyp_ty = state.whnf(goal, &decl.ty);
        let Some((binder_count, eq_type, lhs, rhs, _levels)) =
            extract_local_equality_template(&hyp_ty)
        else {
            continue;
        };
        let proof_template = mk_local_proof_template(Expr::fvar(decl.fvar), binder_count);
        out.push(SimpLemma {
            name: Name::from_string(&decl.name),
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
fn mk_iff_simp_lemma(name: &Name, ty: &Expr, priority: u32) -> Option<SimpLemma> {
    let (binder_count, lhs, rhs) = extract_iff_with_binders(ty)?;
    let proof_expr = mk_iff_rewrite_proof_template(name, binder_count, &lhs, &rhs);
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
    ];
    let mut out = Vec::new();
    for info in state.env.get_simp_lemmas() {
        let name_str = info.name.to_string();
        if HARDCODED.contains(&name_str.as_str()) || config.exclude.contains(&name_str) {
            continue;
        }
        if let Some(decl) = state.env.get_const(&info.name) {
            if let Some((eq_type, lhs, rhs)) = extract_equality_full(&decl.type_) {
                out.push(SimpLemma {
                    name: info.name.clone(),
                    lhs,
                    rhs,
                    eq_type: Some(eq_type),
                    proof_expr: None,
                    index_mode: SimpIndexMode::Normal,
                    priority: info.priority.value(),
                });
            } else if let Some(lemma) =
                mk_iff_simp_lemma(&info.name, &decl.type_, info.priority.value())
            {
                out.push(lemma);
            }
        }
    }

    // `get_simp_lemmas()` iterates a HashMap; stabilize equal-priority registry
    // lemmas so simp rewrite selection is deterministic across runs.
    out.sort_by(|a, b| a.name.cmp(&b.name));
    out
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
    fn only_config(lemma: &str) -> SimpConfig {
        SimpConfig {
            only: true,
            extra_lemmas: vec![lemma.to_string()],
            ..SimpConfig::new()
        }
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
            resolve_extra_lemma_name(&state, "add_zero"),
            Name::from_string("Nat.add_zero")
        );
        // Unknown name falls back to the literal (so the caller's get_const
        // miss governs behavior, not a panic).
        assert_eq!(
            resolve_extra_lemma_name(&state, "ghost"),
            Name::from_string("ghost")
        );
    }
}
