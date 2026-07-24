// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 3C Wave 3 tactic registrations (#2430).
//!
//! Migrates 13 hardcoded `SurfaceTactic` variants to registry dispatch:
//! - 3C.3: 4 ident-list (intro, ext, funext, by_contra)
//! - 3C.4: 4 nonempty-ident (subst, revert, clear, rename_i)
//! - 3C.7: 3 compound-arg (by_cases, specialize, generalize)
//! - 3C.8: 2 search (exact?, apply?)
//!
//! Split from `builtins.rs` per the 500-line file limit.

use std::sync::Arc;

use clean_kernel::Expr;

use super::registry::{TacticArgPattern, TacticEntry, TacticRegistry};
use super::{ProofState, TacticError, TacticResult};

use super::builtins::expr_to_hyp_name;

/// Register Phase 3C Wave 3 tactics into the registry.
/// ENSURES: `registry` contains the phase-3C wave-3 handlers for ident-list, nonempty-ident,
/// compound-arg, and search tactics.
/// ENSURES: Existing simple entries with those names are replaced.
pub(crate) fn register_phase3c_wave3(registry: &mut TacticRegistry) {
    register_ident_list_tactics(registry);
    register_nonempty_ident_tactics(registry);
    register_compound_arg_tactics(registry);
    register_search_tactics(registry);
}

/// 3C.3: ident-list tactics (zero or more identifier names).
fn register_ident_list_tactics(registry: &mut TacticRegistry) {
    registry.register(TacticEntry {
        name: "intro".to_string(),
        pattern: TacticArgPattern::IdentList,
        handler: Arc::new(|ps, args| {
            if args.is_empty() {
                super::intro(ps, "h")
            } else {
                let names = args_to_names(ps, args)?;
                for name in &names {
                    super::intro(ps, name)?;
                }
                Ok(())
            }
        }),
    });
    registry.register(TacticEntry {
        name: "ext".to_string(),
        pattern: TacticArgPattern::IdentList,
        handler: Arc::new(|ps, args| {
            let names = args_to_names(ps, args)?;
            if names.is_empty() {
                super::ext(ps, "x")?;
            } else {
                for name in &names {
                    super::ext(ps, name)?;
                }
            }
            Ok(())
        }),
    });
    registry.register(TacticEntry {
        name: "funext".to_string(),
        pattern: TacticArgPattern::IdentList,
        handler: Arc::new(|ps, args| {
            let names = args_to_names(ps, args)?;
            if names.is_empty() {
                super::funext(ps, "x")?;
            } else {
                for name in &names {
                    super::funext(ps, name)?;
                }
            }
            Ok(())
        }),
    });
    registry.register(TacticEntry {
        name: "by_contra".to_string(),
        pattern: TacticArgPattern::IdentList,
        handler: Arc::new(|ps, args| {
            let name = if let Some(arg) = args.first() {
                expr_to_hyp_name(ps, arg)?
            } else {
                "h".to_string()
            };
            super::by_contra(ps, &name)
        }),
    });
}

/// 3C.4: nonempty-ident-list tactics.
fn register_nonempty_ident_tactics(registry: &mut TacticRegistry) {
    registry.register(TacticEntry {
        name: "subst".to_string(),
        pattern: TacticArgPattern::NonemptyIdentList,
        handler: Arc::new(|ps, args| {
            let names = args_to_names(ps, args)?;
            if names.is_empty() {
                super::subst_vars(ps)
            } else {
                for name in &names {
                    super::subst(ps, name)?;
                }
                Ok(())
            }
        }),
    });
    registry.register(TacticEntry {
        name: "revert".to_string(),
        pattern: TacticArgPattern::NonemptyIdentList,
        handler: Arc::new(|ps, args| {
            let names = args_to_names(ps, args)?;
            for name in &names {
                super::revert(ps, name)?;
            }
            Ok(())
        }),
    });
    registry.register(TacticEntry {
        name: "clear".to_string(),
        pattern: TacticArgPattern::NonemptyIdentList,
        handler: Arc::new(|ps, args| {
            let names = args_to_names(ps, args)?;
            for name in &names {
                super::clear(ps, name)?;
            }
            Ok(())
        }),
    });
    registry.register(TacticEntry {
        name: "rename_i".to_string(),
        pattern: TacticArgPattern::NonemptyIdentList,
        handler: Arc::new(rename_i_handler),
    });
}

fn rename_i_handler(ps: &mut ProofState, args: &[Expr]) -> TacticResult {
    let new_names = args_to_names(ps, args)?;
    if let Some(goal) = ps.current_goal_mut() {
        let inacc_indices: Vec<usize> = goal
            .local_ctx
            .iter()
            .enumerate()
            .rev()
            .filter(|(_, d)| {
                d.name.starts_with('_') || d.name.chars().next().is_some_and(|c| c.is_ascii_digit())
            })
            .map(|(i, _)| i)
            .collect();
        for (new_name, &idx) in new_names.iter().zip(inacc_indices.iter()) {
            if new_name != "_" {
                goal.local_ctx[idx].name = new_name.clone();
            }
        }
    }
    Ok(())
}

/// 3C.7: compound-arg tactics (ident + expr combinations).
fn register_compound_arg_tactics(registry: &mut TacticRegistry) {
    // by_cases: args = [Const(hyp_name), elaborated_prop]
    registry.register(TacticEntry {
        name: "by_cases".to_string(),
        pattern: TacticArgPattern::ExprList,
        handler: Arc::new(|ps, args| {
            if args.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "by_cases".into(),
                    expected: "2 arguments: <name> <proposition>".into(),
                });
            }
            let hyp_name = expr_to_hyp_name(ps, &args[0])?;
            super::by_cases(ps, &hyp_name, args[1].clone())
        }),
    });
    // specialize: args = [Const(hyp_name), elaborated_arg₁, … elaborated_argₙ].
    // Applies every argument in order (multi-arg). Each application is
    // re-bound to the SAME hypothesis name, so `specialize h a b` is
    // `h := h a b` shadowing the original. A non-∀/non-function `h` or
    // surplus arguments error gracefully (no panic) via `specialize_multi`.
    registry.register(TacticEntry {
        name: "specialize".to_string(),
        pattern: TacticArgPattern::ExprList,
        handler: Arc::new(|ps, args| {
            if args.len() < 2 {
                return Err(TacticError::MissingArgument {
                    tactic: "specialize".into(),
                    expected: "at least 2 arguments: <hyp> <arg> …".into(),
                });
            }
            let hyp_name = expr_to_hyp_name(ps, &args[0])?;
            super::specialize_generalize::specialize_multi(ps, &hyp_name, &args[1..])
        }),
    });
    // generalize: args = [elaborated_term, Const(var_name)] for the bare
    // `generalize e = x` form, or [elaborated_term, Const(var_name),
    // Const(hyp_name)] for the `generalize h : e = x` form (the hypothesis
    // name `h` records `h : e = x`). The 3-arg form routes through
    // `generalize_eq`, which abstracts `e` AND introduces the equality
    // hypothesis; the 2-arg form omits the hypothesis. A surplus (>3) or
    // deficient (<2) argument count errors gracefully (no panic).
    registry.register(TacticEntry {
        name: "generalize".to_string(),
        pattern: TacticArgPattern::ExprList,
        handler: Arc::new(|ps, args| match args {
            [term, var, hyp] => {
                let var_name = expr_to_hyp_name(ps, var)?;
                let hyp_name = expr_to_hyp_name(ps, hyp)?;
                super::generalize_eq(ps, term.clone(), &var_name, &hyp_name)
            }
            [term, var] => {
                let var_name = expr_to_hyp_name(ps, var)?;
                super::generalize(ps, term.clone(), &var_name)
            }
            _ => Err(TacticError::MissingArgument {
                tactic: "generalize".into(),
                expected: "2 arguments (<term> = <var>) or 3 (<hyp> : <term> = <var>)".into(),
            }),
        }),
    });
}

/// 3C.8: search tactics (exact?, apply?, rw?).
fn register_search_tactics(registry: &mut TacticRegistry) {
    registry.register(TacticEntry {
        name: "exact?".to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(|ps, _args| super::exact_search_and_apply(ps)),
    });
    registry.register(TacticEntry {
        name: "apply?".to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(|ps, _args| super::apply_search_and_apply(ps)),
    });
    // `rw?` mirrors exact?/apply?: search for an applicable rewrite and apply the
    // top hit via the same kernel-checked `Eq.subst` path as `rw`. The
    // exclude-list form `rw? [-lemma]` is deferred (needs parser support).
    registry.register(TacticEntry {
        name: "rw?".to_string(),
        pattern: TacticArgPattern::Nullary,
        handler: Arc::new(|ps, _args| super::rewrite_search_and_apply(ps)),
    });
}

/// Convert elaborated args to string names (for ident-list tactics).
fn args_to_names(ps: &ProofState, args: &[Expr]) -> Result<Vec<String>, TacticError> {
    args.iter().map(|e| expr_to_hyp_name(ps, e)).collect()
}
