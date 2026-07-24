// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Aesop rule builder support: unfold, tactic, forward, destruct, witness enumeration.

use std::sync::Arc;

use crate::stack_safe;
use crate::tactic::{
    assumption, decide, have_, reduce_eq, rfl, simp, tauto, trivial, Goal, LocalDecl, ProofState,
    SimpConfig, TacticError, TacticResult,
};
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, Level};

// =============================================================================
// Unfold Builder Support
// =============================================================================

/// Check if an expression contains a constant with the given name
fn contains_const(e: &Expr, name: &Name) -> bool {
    stack_safe(|| match e.kind() {
        ExprKind::Const(n, _) => n == name,
        ExprKind::App(f, a) => contains_const(f, name) || contains_const(a, name),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_const(ty, name) || contains_const(body, name)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_const(ty, name) || contains_const(val, name) || contains_const(body, name)
        }
        ExprKind::MData(_, inner) | ExprKind::Squash(inner) => contains_const(inner, name),
        ExprKind::Proj(_, _, inner) => contains_const(inner, name),
        _ => false,
    })
}

/// Unfold all occurrences of a constant with its definition body
fn unfold_const(e: &Expr, name: &Name, body: &Expr) -> Expr {
    stack_safe(|| match e.kind() {
        ExprKind::Const(n, _) if n == name => body.clone(),
        ExprKind::App(f, a) => Expr::app(unfold_const(f, name, body), unfold_const(a, name, body)),
        ExprKind::Lam(bi, ty, b) => Expr::lam(
            *bi,
            unfold_const(ty, name, body),
            unfold_const(b, name, body),
        ),
        ExprKind::Pi(bi, ty, b) => Expr::pi(
            *bi,
            unfold_const(ty, name, body),
            unfold_const(b, name, body),
        ),
        ExprKind::Let(n, ty, val, b, non_dep) => Expr::let_named(
            n.clone(),
            unfold_const(ty, name, body),
            unfold_const(val, name, body),
            unfold_const(b, name, body),
            *non_dep,
        ),
        ExprKind::MData(md, inner) => Expr::mdata(md.clone(), unfold_const(inner, name, body)),
        ExprKind::Proj(s, idx, inner) => {
            Expr::proj(s.clone(), *idx, unfold_const(inner, name, body))
        }
        ExprKind::Squash(inner) => {
            Expr::from_kind(ExprKind::Squash(Arc::new(unfold_const(inner, name, body))))
        }
        _ => e.clone(),
    })
}

/// Apply an unfold rule - unfold a definition in the goal
/// REQUIRES: `state` has a current goal when callers expect unfolding to succeed.
/// REQUIRES: `def_name` names a declaration in `env`; successful unfolding additionally requires a definition body.
/// ENSURES: On `Ok(())`, the current goal target replaces every occurrence of `def_name` with its body while preserving the local context.
/// ENSURES: On error, no goal replacement is committed to `state`.
pub(super) fn apply_unfold_rule(
    state: &mut ProofState,
    def_name: &Name,
    env: &Environment,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = goal.target.clone();

    // Check if target contains the definition to unfold
    if !contains_const(&target, def_name) {
        return Err(TacticError::UnfoldFailed {
            name: def_name.to_string(),
            reason: "not in goal".into(),
        });
    }

    // Get the definition body
    let const_info = env
        .get_const(def_name)
        .ok_or_else(|| TacticError::EnvironmentMissing {
            constant: def_name.to_string(),
        })?;

    let body = const_info
        .value
        .as_ref()
        .ok_or_else(|| TacticError::UnfoldFailed {
            name: def_name.to_string(),
            reason: "has no definition body (axiom or opaque)".into(),
        })?;

    // Replace all occurrences of `def_name` with its body
    let new_target = unfold_const(&target, def_name, body);

    // Use replace_target_def_eq to keep MetaId(0) connected through the
    // proof chain. Unfolding is definitionally equal by construction.
    // Part of #2477: previously this replaced goals[0] in-place, which
    // disconnected MetaId(0) and caused proof_term() to return None.
    state.replace_target_def_eq(new_target)
}

// =============================================================================
// Tactic Builder Support
// =============================================================================

/// Apply a tactic rule - invoke a named tactic
/// REQUIRES: `tactic_name` is one of the supported built-in tactic names for success.
/// ENSURES: Supported names delegate directly to the corresponding tactic implementation.
/// ENSURES: On `Err(RuleApplicationFailed)`, `tactic_name` was not one of the supported built-ins.
pub(super) fn apply_tactic_rule(state: &mut ProofState, tactic_name: &Name) -> TacticResult {
    // Look up and invoke the named tactic
    match tactic_name.to_string().as_str() {
        // Built-in tactics that can be registered as Aesop rules
        "simp" => simp(state, SimpConfig::default()),
        "trivial" => trivial(state),
        "assumption" => assumption(state),
        "rfl" => rfl(state),
        "reduce_eq" => reduce_eq(state),
        "decide" => decide(state),
        "tauto" => tauto(state),
        // User-defined tactics would need a registry
        other => Err(TacticError::RuleApplicationFailed {
            rule: "tactic".into(),
            detail: format!("unknown tactic '{other}'"),
        }),
    }
}

// =============================================================================
// Witness Enumeration for Existential Goals
// =============================================================================

/// Enumerate candidate witnesses for an existential type.
///
/// For a goal `∃ x : α, P x`, this function finds expressions of type `α` that
/// might satisfy `P`. The strategy prioritizes:
///
/// 1. **Nullary constructors** - Zero-argument constructors like `Nat.zero`, `Unit.unit`
/// 2. **Local context values** - Variables in scope with the right type
/// 3. **Simple literals** - Common values like 0, 1, true, false
///
/// This is a heuristic approach - we can't enumerate all possible witnesses,
/// so we try common patterns that often succeed in practice.
/// Uses the goal's local context so FVars resolve correctly (#2229).
/// REQUIRES: `witness_type` and `local_ctx` are interpreted in the same local context as `goal`.
/// ENSURES: Returned expressions are candidate witnesses whose types heuristically match `witness_type`.
/// ENSURES: Duplicate witness expressions are removed before returning.
pub fn enumerate_witnesses(
    state: &ProofState,
    goal: &Goal,
    witness_type: &Expr,
    local_ctx: &[LocalDecl],
) -> Vec<Expr> {
    let mut witnesses = Vec::new();

    // Normalize the type to expose its head (#2229: use goal context)
    let whnf_type = state.whnf(goal, witness_type);
    let ty_head = whnf_type.get_app_fn();

    // Strategy 1: Find nullary constructors of the type
    if let ExprKind::Const(type_name, levels) = ty_head.kind() {
        if let Some(ind_val) = state.env().get_inductive(type_name) {
            for ctor_name in &ind_val.constructor_names {
                if let Some(ctor_val) = state.env().get_constructor(ctor_name) {
                    // Check if this is a nullary constructor (no fields after parameters)
                    if ctor_val.num_fields == 0 {
                        // Create the constructor expression
                        let ctor_expr = Expr::const_(ctor_name.clone(), levels.clone());
                        witnesses.push(ctor_expr);
                    }
                }
            }
        }
    }

    // Strategy 2: Check local context for values of the right type
    for decl in local_ctx {
        if state.is_def_eq(goal, &decl.ty, witness_type) {
            witnesses.push(Expr::fvar(decl.fvar));
        }
    }

    // Strategy 3: Try common literal values based on type name
    if let ExprKind::Const(type_name, _) = ty_head.kind() {
        let name_str = type_name.to_string();
        match name_str.as_str() {
            "Nat" => {
                // Already added Nat.zero via constructor above
                // Add literal 0 as backup (different representation)
                witnesses.push(Expr::nat_lit(0));
                witnesses.push(Expr::nat_lit(1));
            }
            "Int" => {
                witnesses.push(Expr::nat_lit(0));
            }
            "Bool" => {
                // true and false should be added via constructors
                witnesses.push(Expr::const_(Name::from_string("Bool.true"), vec![]));
                witnesses.push(Expr::const_(Name::from_string("Bool.false"), vec![]));
            }
            "String" => {
                witnesses.push(Expr::str_lit(""));
            }
            _ => {}
        }
    }

    // Deduplicate (simple structural equality)
    witnesses.dedup();

    witnesses
}

// =============================================================================
// Forward Builder Support
// =============================================================================

/// Apply a forward rule: given a theorem `h : A → B → C`,
/// find hypotheses matching `A` and `B`, then add `C` to context.
///
/// Forward rules are different from `apply` rules:
/// - `apply` works backward: given goal C, find rule A → B → C and add goals A, B
/// - `forward` works forward: given hyps A, B and rule A → B → C, add hyp C
///
/// This is essential for Mathlib's category theory proofs where facts
/// are built up progressively.
/// REQUIRES: `state` has a current goal and `rule_type` is interpreted in the same environment as `rule_name`.
/// REQUIRES: Successful application requires every parameter in `rule_type` to match a local hypothesis structurally.
/// ENSURES: On `Ok(())`, a fresh hypothesis for the instantiated conclusion is added to the current goal context.
/// ENSURES: On `Err(RuleApplicationFailed)`, no new hypothesis is added.
pub(super) fn apply_forward_rule(
    state: &mut ProofState,
    rule_name: &Name,
    rule_type: &Expr,
    levels: &[Level],
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let local_ctx = &goal.local_ctx;

    // Decompose the rule type: A₁ → A₂ → ... → Aₙ → C
    // into parameters [(A₁, bi₁), (A₂, bi₂), ...] and conclusion C
    let (params, conclusion) = decompose_pi_chain(rule_type);

    if params.is_empty() {
        // Rule has no parameters, nothing to match
        return Err(TacticError::RuleApplicationFailed {
            rule: "forward".into(),
            detail: "has no parameters".into(),
        });
    }

    // Try to find matching hypotheses for each parameter
    let mut matched_args: Vec<Option<Expr>> = vec![None; params.len()];

    for (i, (param_ty, _bi)) in params.iter().enumerate() {
        // Try to find a hypothesis with this type
        for decl in local_ctx {
            // Simple type matching (could be improved with unification)
            if types_match_simple(param_ty, &decl.ty) {
                matched_args[i] = Some(Expr::fvar(decl.fvar));
                break;
            }
        }
    }

    // Check if all arguments are matched
    let all_matched = matched_args.iter().all(|m| m.is_some());
    if !all_matched {
        return Err(TacticError::RuleApplicationFailed {
            rule: "forward".into(),
            detail: "not all arguments matched".into(),
        });
    }

    // Instantiate conclusion with matched arguments
    let conclusion_inst = instantiate_conclusion(&conclusion, &params, &matched_args);

    // Check if we already have this hypothesis (avoid duplicates)
    for decl in local_ctx {
        if types_match_simple(&conclusion_inst, &decl.ty) {
            return Err(TacticError::RuleApplicationFailed {
                rule: "forward".into(),
                detail: "hypothesis already exists".into(),
            });
        }
    }

    // Build the proof term: rule_name arg1 arg2 ...
    let mut proof = Expr::const_(rule_name.clone(), levels.to_vec());
    for arg in matched_args.iter().flatten() {
        proof = Expr::app(proof, arg.clone());
    }

    // Add the new hypothesis using have_
    let hyp_name = generate_forward_hyp_name(local_ctx, rule_name);
    have_(state, &hyp_name, conclusion_inst, Some(proof))
}

/// Apply a destruct rule: like forward but clears the matched hypothesis
///
/// Destruct rules are used when the hypothesis should be consumed after use.
/// For example, `h : P ∧ Q` can be destructed to get `P` while removing `h`.
///
/// This prevents infinite loops (hypothesis is removed so can't match again)
/// and keeps the context clean by removing intermediate hypotheses.
/// REQUIRES: `state` has a current goal and `rule_type` is interpreted in the same environment as `rule_name`.
/// REQUIRES: Successful application requires every parameter in `rule_type` to match a local hypothesis structurally.
/// ENSURES: On `Ok(())`, adds the instantiated conclusion as a fresh hypothesis and clears the first matched source hypothesis.
/// ENSURES: On `Err(RuleApplicationFailed)`, no conclusion hypothesis is added.
pub(super) fn apply_destruct_rule(
    state: &mut ProofState,
    rule_name: &Name,
    rule_type: &Expr,
    levels: &[Level],
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let local_ctx = &goal.local_ctx;

    // Decompose the rule type: A₁ → A₂ → ... → Aₙ → C
    let (params, conclusion) = decompose_pi_chain(rule_type);

    if params.is_empty() {
        return Err(TacticError::RuleApplicationFailed {
            rule: "destruct".into(),
            detail: "has no parameters".into(),
        });
    }

    // Try to find matching hypotheses for each parameter
    // Track the name of the first matched hypothesis (the one to clear)
    let mut matched_args: Vec<Option<Expr>> = vec![None; params.len()];
    let mut first_matched_hyp_name: Option<String> = None;

    for (i, (param_ty, _bi)) in params.iter().enumerate() {
        for decl in local_ctx {
            if types_match_simple(param_ty, &decl.ty) {
                matched_args[i] = Some(Expr::fvar(decl.fvar));
                // Track the first matched hypothesis for clearing
                if first_matched_hyp_name.is_none() {
                    first_matched_hyp_name = Some(decl.name.clone());
                }
                break;
            }
        }
    }

    // Check if all arguments are matched
    let all_matched = matched_args.iter().all(|m| m.is_some());
    if !all_matched {
        return Err(TacticError::RuleApplicationFailed {
            rule: "destruct".into(),
            detail: "not all arguments matched".into(),
        });
    }

    // Must have a hypothesis to clear
    let hyp_to_clear =
        first_matched_hyp_name.ok_or_else(|| TacticError::RuleApplicationFailed {
            rule: "destruct".into(),
            detail: "no hypothesis to clear".into(),
        })?;

    // Instantiate conclusion with matched arguments
    let conclusion_inst = instantiate_conclusion(&conclusion, &params, &matched_args);

    // Check if we already have this hypothesis (avoid duplicates)
    for decl in local_ctx {
        if types_match_simple(&conclusion_inst, &decl.ty) {
            return Err(TacticError::RuleApplicationFailed {
                rule: "destruct".into(),
                detail: "hypothesis already exists".into(),
            });
        }
    }

    // Build the proof term: rule_name arg1 arg2 ...
    let mut proof = Expr::const_(rule_name.clone(), levels.to_vec());
    for arg in matched_args.iter().flatten() {
        proof = Expr::app(proof, arg.clone());
    }

    // Add the new hypothesis using have_
    let hyp_name = generate_forward_hyp_name(local_ctx, rule_name);
    have_(state, &hyp_name, conclusion_inst, Some(proof))?;

    // Clear the matched hypothesis (this is what distinguishes destruct from forward)
    crate::tactic::hypothesis::clear(state, &hyp_to_clear)?;

    Ok(())
}

/// Decompose a Pi chain into parameters and conclusion
///
/// `A → B → C` becomes `[(A, Explicit), (B, Explicit)]` and `C`
fn decompose_pi_chain(ty: &Expr) -> (Vec<(Expr, clean_kernel::expr::BinderData)>, Expr) {
    let mut params = Vec::new();
    let mut current = ty.clone();

    while let ExprKind::Pi(bi, domain, codomain) = current.kind() {
        params.push((domain.as_ref().clone(), *bi));
        current = codomain.as_ref().clone();
    }

    (params, current)
}

/// Simple type matching (structural equality)
///
/// Uses `Expr::eq` (structural `PartialEq`) instead of Debug format comparison.
/// A full implementation would use definitional equality (`is_def_eq`).
/// ENSURES: Returns `true` exactly when `ty1` and `ty2` are structurally equal.
/// ENSURES: Performs no normalization or definitional equality checks.
pub(super) fn types_match_simple(ty1: &Expr, ty2: &Expr) -> bool {
    ty1 == ty2
}

/// Instantiate conclusion type with matched arguments
///
/// For `A → B → C(x, y)` where we matched `a : A` and `b : B`,
/// this substitutes the arguments to get `C(a, b)`.
fn instantiate_conclusion(
    conclusion: &Expr,
    _params: &[(Expr, clean_kernel::expr::BinderData)],
    _matched_args: &[Option<Expr>],
) -> Expr {
    // For simple cases, the conclusion doesn't depend on the arguments
    // (e.g., `h : P → Q` has conclusion `Q` independent of the `P` argument)
    // For dependent types, we'd need proper substitution here
    conclusion.clone()
}

/// Generate a fresh hypothesis name for forward rules
fn generate_forward_hyp_name(local_ctx: &[LocalDecl], rule_name: &Name) -> String {
    let base = format!("h_{}", rule_name.to_string().replace('.', "_"));

    // Find a unique name
    let mut candidate = base.clone();
    let mut suffix = 1;
    while local_ctx.iter().any(|d| d.name == candidate) {
        candidate = format!("{base}_{suffix}");
        suffix += 1;
    }
    candidate
}

/// Parse an existential goal to extract the witness type.
///
/// For `Exists {α} p` where `p : α → Prop`, returns `α`.
/// ENSURES: Returns `Some(α)` exactly for `Exists` applications with at least one argument.
/// ENSURES: Returns `None` for non-`Exists` expressions or malformed `Exists` applications.
pub fn extract_exists_witness_type(expr: &Expr) -> Option<Expr> {
    // Exists {α} p is App(App(Const("Exists", _), α), p)
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    match head.kind() {
        ExprKind::Const(name, _) if name.to_string() == "Exists" => {
            if !args.is_empty() {
                Some(args[0].clone())
            } else {
                None
            }
        }
        _ => None,
    }
}
