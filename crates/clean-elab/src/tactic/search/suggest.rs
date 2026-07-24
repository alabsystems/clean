// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Suggestion and hint tactics: suggest, hint, exact?!, apply?!

use crate::tactic::equality::rewrite;
use crate::tactic::{apply, exact, ProofState, TacticError, TacticResult};
use clean_kernel::ExprKind;

use super::simple::{apply_search, can_apply_to_produce, exact_search, rewrite_search};

/// A tactic suggestion with confidence score
#[derive(Debug, Clone)]
pub struct TacticSuggestion {
    /// The suggested tactic command
    pub tactic: String,
    /// Confidence score (0.0 to 1.0)
    pub confidence: f64,
    /// Explanation of why this tactic might work
    pub reason: String,
}

/// `suggest` - suggest tactics that might make progress on the goal
///
/// Analyzes the goal structure and suggests appropriate tactics.
///
/// # Example
/// ```text
/// -- goal: P ∧ Q
/// suggest
/// -- suggests: constructor, split, And.intro
/// ```
/// REQUIRES: `state` has a current goal when callers expect non-error suggestions.
/// ENSURES: Returned suggestions are sorted by non-increasing confidence and truncated to `max_suggestions`.
/// ENSURES: Returns `Err(NoGoals)` iff there is no current goal to analyze.
pub fn suggest(
    state: &mut ProofState,
    max_suggestions: usize,
) -> Result<Vec<TacticSuggestion>, TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = goal.target.clone();
    let local_ctx = goal.local_ctx.clone();

    let mut suggestions = Vec::new();

    // Analyze goal structure
    let target_head = target.get_app_fn();
    let _target_args = target.get_app_args();

    // Get the head name if it's a constant
    let head_name = if let ExprKind::Const(name, _) = target_head.kind() {
        Some(name.to_string())
    } else {
        None
    };

    // Check for specific goal shapes

    // 1. Equality goals
    if head_name.as_deref() == Some("Eq") {
        suggestions.push(TacticSuggestion {
            tactic: "rfl".to_string(),
            confidence: 0.9,
            reason: "Goal is an equality - try reflexivity".to_string(),
        });
        suggestions.push(TacticSuggestion {
            tactic: "simp".to_string(),
            confidence: 0.7,
            reason: "Simplification often solves equalities".to_string(),
        });
        suggestions.push(TacticSuggestion {
            tactic: "cert_simp".to_string(),
            confidence: 0.65,
            reason: "Certificate/list simplifier can expose arithmetic equalities".to_string(),
        });
        suggestions.push(TacticSuggestion {
            tactic: "ring".to_string(),
            confidence: 0.6,
            reason: "Ring solver for algebraic equalities".to_string(),
        });
        suggestions.push(TacticSuggestion {
            tactic: "omega".to_string(),
            confidence: 0.5,
            reason: "omega for integer arithmetic".to_string(),
        });
        suggestions.push(TacticSuggestion {
            tactic: "cert_mathverse".to_string(),
            confidence: 0.55,
            reason: "Certificate-aware omega wrapper for normalized arithmetic".to_string(),
        });
    }

    // 2. Conjunction goals (And)
    if head_name.as_deref() == Some("And") {
        suggestions.push(TacticSuggestion {
            tactic: "constructor".to_string(),
            confidence: 0.95,
            reason: "Goal is a conjunction - split into two goals".to_string(),
        });
        suggestions.push(TacticSuggestion {
            tactic: "split".to_string(),
            confidence: 0.95,
            reason: "Split conjunction into components".to_string(),
        });
    }

    // 3. Disjunction goals (Or)
    if head_name.as_deref() == Some("Or") {
        suggestions.push(TacticSuggestion {
            tactic: "left".to_string(),
            confidence: 0.5,
            reason: "Prove left disjunct".to_string(),
        });
        suggestions.push(TacticSuggestion {
            tactic: "right".to_string(),
            confidence: 0.5,
            reason: "Prove right disjunct".to_string(),
        });
    }

    // 4. Existential goals (Exists)
    if head_name.as_deref() == Some("Exists") {
        suggestions.push(TacticSuggestion {
            tactic: "use _".to_string(),
            confidence: 0.8,
            reason: "Provide a witness for the existential".to_string(),
        });
    }

    // 5. Universal goals (Pi/forall)
    if let ExprKind::Pi(_, _, _) = target.kind() {
        suggestions.push(TacticSuggestion {
            tactic: "intro".to_string(),
            confidence: 0.95,
            reason: "Goal is a forall/implication - introduce hypothesis".to_string(),
        });
        suggestions.push(TacticSuggestion {
            tactic: "intros".to_string(),
            confidence: 0.9,
            reason: "Introduce all hypotheses at once".to_string(),
        });
    }

    // 6. False goal
    if head_name.as_deref() == Some("False") {
        suggestions.push(TacticSuggestion {
            tactic: "contradiction".to_string(),
            confidence: 0.8,
            reason: "Goal is False - look for contradiction in hypotheses".to_string(),
        });
        suggestions.push(TacticSuggestion {
            tactic: "tauto".to_string(),
            confidence: 0.6,
            reason: "Propositional tautology solver".to_string(),
        });
    }

    // 7. Negation goals (Not)
    if head_name.as_deref() == Some("Not") {
        suggestions.push(TacticSuggestion {
            tactic: "intro h".to_string(),
            confidence: 0.9,
            reason: "Goal is a negation - assume and derive contradiction".to_string(),
        });
        suggestions.push(TacticSuggestion {
            tactic: "push_neg".to_string(),
            confidence: 0.7,
            reason: "Push negations inward".to_string(),
        });
    }

    // 8. Check for applicable hypotheses
    for decl in &local_ctx {
        // If hypothesis type matches goal exactly
        // (#2229: use goal's local context so FVars resolve)
        if state.is_def_eq(goal, &decl.ty, &target) {
            suggestions.push(TacticSuggestion {
                tactic: format!("exact {}", decl.name),
                confidence: 1.0,
                reason: format!("Hypothesis {} has exactly the goal type", decl.name),
            });
        }

        // If hypothesis can be applied
        if let Some(args) = can_apply_to_produce(state, goal, &decl.ty, &target, 5) {
            if !args.is_empty() {
                suggestions.push(TacticSuggestion {
                    tactic: format!("apply {}", decl.name),
                    confidence: 0.85,
                    reason: format!(
                        "Hypothesis {} can be applied ({} args needed)",
                        decl.name,
                        args.len()
                    ),
                });
            }
        }
    }

    // 9. Generic tactics that often help
    suggestions.push(TacticSuggestion {
        tactic: "simp".to_string(),
        confidence: 0.4,
        reason: "Simplification is often useful".to_string(),
    });
    suggestions.push(TacticSuggestion {
        tactic: "trivial".to_string(),
        confidence: 0.3,
        reason: "Try simple tactics".to_string(),
    });
    suggestions.push(TacticSuggestion {
        tactic: "aesop".to_string(),
        confidence: 0.5,
        reason: "General automated proof search".to_string(),
    });

    // Sort by confidence and limit results
    suggestions.sort_by(|a, b| {
        b.confidence
            .partial_cmp(&a.confidence)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    suggestions.truncate(max_suggestions);

    Ok(suggestions)
}

/// `exact?!` - search and apply the first matching proof
/// REQUIRES: `state` has a current goal when callers expect search to run.
/// ENSURES: On `Ok(())`, the first result from `exact_search(state, 1)` has been applied with `exact`.
/// ENSURES: On `Err(SearchExhausted { tactic: "exact?", .. })`, no matching proof was found.
pub fn exact_search_and_apply(state: &mut ProofState) -> TacticResult {
    let results = exact_search(state, 1)?;

    if let Some(result) = results.first() {
        exact(state, result.expr.clone())
    } else {
        Err(TacticError::SearchExhausted {
            tactic: "exact?".into(),
            detail: "no matching proof found".into(),
        })
    }
}

/// `apply?!` - search and apply the first matching lemma
/// REQUIRES: `state` has a current goal when callers expect search to run.
/// ENSURES: On `Ok(())`, the first result from `apply_search(state, 1)` has been applied with `apply`.
/// ENSURES: On `Err(SearchExhausted { tactic: "apply?", .. })`, no applicable lemma was found.
pub fn apply_search_and_apply(state: &mut ProofState) -> TacticResult {
    let results = apply_search(state, 1)?;

    if let Some(result) = results.first() {
        apply(state, result.expr.clone())
    } else {
        Err(TacticError::SearchExhausted {
            tactic: "apply?".into(),
            detail: "no applicable lemma found".into(),
        })
    }
}

/// `rw?` - search for and apply the first applicable rewrite lemma.
///
/// Mirrors [`exact_search_and_apply`] / [`apply_search_and_apply`]: it runs
/// [`rewrite_search`] for the single best candidate, then applies it through the
/// real [`rewrite`] tactic — so the resulting proof state is identical to an
/// explicit `rw [name]`, justified by the same kernel-checked `Eq.subst` proof
/// term (no new trust surface). The interactive `rw?` semantics are *suggest the
/// applicable rewrites*; like `exact?`/`apply?`, this entry point also applies
/// the top hit. Use [`rewrite_search`] directly to enumerate suggestions without
/// mutating the proof state.
///
/// Only `Eq`-shaped candidates are auto-applied. `rewrite_search` may also
/// surface `Iff`-shaped lemmas (marked `-- iff:`) as suggestions; those are
/// skipped here because [`rewrite`] builds `Eq.subst` proofs and cannot apply an
/// `Iff` without a `propext` bridge it does not construct.
///
/// REQUIRES: `state` has a current goal when callers expect search to run.
/// ENSURES: On `Ok(())`, the first `Eq`-rewritable result from
///   `rewrite_search(state, ..)` has been applied with `rewrite`.
/// ENSURES: On `Err(SearchExhausted { tactic: "rw?", .. })`, no applicable
///   equality rewrite was found.
///
/// NOTE: The exclude-list form `rw? [-lemma]` is deferred — it requires parser
/// support for the bracketed exclude syntax, which is out of scope here.
pub fn rewrite_search_and_apply(state: &mut ProofState) -> TacticResult {
    // Collect a few candidates so we can skip suggestion-only `Iff` hits and
    // apply the first genuinely `Eq`-rewritable one (its `rw [...]` suggestion).
    let results = rewrite_search(state, 8)?;

    match results.iter().find(|r| r.suggestion.starts_with("rw [")) {
        Some(result) => rewrite(state, &result.name.to_string(), false),
        None => Err(TacticError::SearchExhausted {
            tactic: "rw?".into(),
            detail: "no applicable rewrite found".into(),
        }),
    }
}

/// `hint` - provide hints about the goal without modifying state
/// REQUIRES: `state` has a current goal when callers expect hints.
/// ENSURES: Returned list is non-empty on `Ok`.
/// ENSURES: Returns `Err(NoGoals)` iff there is no current goal to inspect.
pub fn hint(state: &ProofState) -> Result<Vec<String>, TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = goal.target.clone();

    let mut hints = Vec::new();

    let target_head = target.get_app_fn();

    if let ExprKind::Const(name, _) = target_head.kind() {
        let name_str = name.to_string();

        match name_str.as_str() {
            "Eq" => {
                hints.push(
                    "This is an equality goal. Try: rfl, simp, cert_simp, ring, cert_mathverse, mathverse, or rewrite"
                        .to_string(),
                );
            }
            "And" => {
                hints.push(
                    "This is a conjunction. Use `constructor` or `split` to prove each part"
                        .to_string(),
                );
            }
            "Or" => {
                hints.push(
                    "This is a disjunction. Use `left` or `right` to choose which side to prove"
                        .to_string(),
                );
            }
            "Exists" => {
                hints.push(
                    "This is an existential. Use `use <witness>` to provide a witness".to_string(),
                );
            }
            "Not" | "False" => {
                hints.push("This is a negation/falsity goal. Try `intro` to assume the hypothesis, then derive a contradiction".to_string());
            }
            "True" => {
                hints.push("This is trivially true. Use `trivial` or `constructor`".to_string());
            }
            "Iff" => {
                hints
                    .push("This is an iff. Use `constructor` to prove both directions".to_string());
            }
            _ => {
                hints.push(format!(
                    "Goal head is `{name_str}`. Check if there's a relevant lemma or constructor"
                ));
            }
        }
    }

    if let ExprKind::Pi(_, _, _) = target.kind() {
        hints.push(
            "This is a forall/implication. Use `intro` to introduce the hypothesis".to_string(),
        );
    }

    // Check local context for useful hypotheses
    let local_ctx = goal.local_ctx.clone();
    for decl in &local_ctx {
        // (#2229: use goal's local context so FVars resolve)
        if state.is_def_eq(goal, &decl.ty, &target) {
            hints.push(format!(
                "Hypothesis `{}` has exactly the goal type - use `exact {}`",
                decl.name, decl.name
            ));
        }
    }

    if hints.is_empty() {
        hints.push(
            "No specific hints available. Try `simp`, `trivial`, or search with `exact?`"
                .to_string(),
        );
    }

    Ok(hints)
}
