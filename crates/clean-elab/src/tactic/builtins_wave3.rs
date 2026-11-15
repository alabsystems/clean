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

use clean_parser::SurfaceName;

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
                super::intro(ps, &SurfaceName::generated_path("h"))
            } else {
                let names = args_to_names(ps, args)?;
                for name in &names {
                    if name.is_unescaped_component("_") {
                        super::intro(ps, name)?;
                    } else {
                        super::target_equation::intro_shadowing(ps, name)?;
                    }
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
                super::ext(ps, &SurfaceName::generated_path("x"))?;
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
                super::funext(ps, &SurfaceName::generated_path("x"))?;
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
                SurfaceName::generated_path("h")
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
            // Lean's evalRevert resolves all names first; MVarId.revert then
            // includes forward dependencies and sorts in declaration order.
            // Reuse the batch proof construction used by cases/induction.
            let mut roots = Vec::with_capacity(names.len());
            for name in &names {
                super::pattern::names::require_binding_name(name, "revert")?;
                roots.push(super::hypothesis::hypothesis_fvar(ps, name)?);
            }
            let goal = ps.current_goal().ok_or(TacticError::NoGoals)?;
            let mut reverted: std::collections::HashSet<_> = roots.into_iter().collect();
            // Query instantiated dependencies without rewriting any locals.
            // A well-formed context lists each dependency before its users.
            for decl in &goal.local_ctx {
                if reverted.contains(&decl.fvar) {
                    continue;
                }
                if super::major_dependents::generalizing_depends_on(ps, decl, &reverted) {
                    reverted.insert(decl.fvar);
                }
            }
            let reverted: Vec<_> = reverted.into_iter().collect();
            super::major_dependents::revert_fvars(ps, &reverted).map(|_| ())
        }),
    });
    registry.register(TacticEntry {
        name: "clear".to_string(),
        pattern: TacticArgPattern::NonemptyIdentList,
        handler: Arc::new(|ps, args| {
            let names = args_to_names(ps, args)?;
            // Lean's `evalClear`: resolve every name, sort the locals by
            // declaration order, and clear the LAST first, so `clear h hp`
            // succeeds when `hp` depends on `h` (each clear still refuses a
            // remaining dependent, `hypothesis::clear_fvar`).
            let mut fvars = Vec::with_capacity(names.len());
            for name in &names {
                super::pattern::names::require_binding_name(name, "clear")?;
                fvars.push(super::hypothesis::hypothesis_fvar(ps, name)?);
            }
            let goal = ps.current_goal().ok_or(TacticError::NoGoals)?;
            let position = |fvar: &clean_kernel::FVarId| {
                goal.local_ctx.iter().position(|decl| decl.fvar == *fvar)
            };
            fvars.sort_by_key(|fvar| std::cmp::Reverse(position(fvar)));
            fvars.dedup();
            for fvar in fvars {
                super::hypothesis::clear_fvar(ps, fvar)?;
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
    rename_inaccessible_binders(ps, &new_names)
}

/// Name the last inaccessible locals in context order, as both `rename_i`
/// and `case` do. This includes inaccessible locals from earlier eliminations.
pub(super) fn rename_inaccessible_binders(
    ps: &mut ProofState,
    new_names: &[SurfaceName],
) -> TacticResult {
    if let Some(goal) = ps.current_goal_mut() {
        // Lean 4.8's `rename_i x₁ … xₙ` (`evalRenameInaccessibles`) names the
        // LAST n inaccessible locals, in context order (`x₁` the earliest of
        // them), and refuses more names than there are (gap G67). Every
        // local whose name Clean generated is inaccessible — an unnamed
        // constructor field from an earlier `cases` as much as the latest
        // case's — except `this`, which Lean's `have` makes accessible.
        // An older duplicate is inaccessible only while a newer matching local
        // is present. Keep the introduction predicate's direction: an older
        // ACTUAL local matches the newer REQUESTED name. Template-origin
        // restrictions apply to that requested name and are asymmetric.
        let inaccessible: Vec<usize> =
            goal.local_ctx
                .iter()
                .enumerate()
                .filter(|(index, d)| {
                    is_generated_inaccessible_name(&d.name)
                        || (is_generated_name(&d.name) && !d.name.is_unescaped_component("this"))
                        || goal.local_ctx.iter().skip(*index + 1).any(|newer| {
                            super::pattern::names::hypothesis_named(&d.name, &newer.name)
                        })
                })
                .map(|(i, _)| i)
                .collect();
        if new_names.len() > inaccessible.len() {
            return Err(TacticError::GoalMismatch(
                "too many variable names provided".to_string(),
            ));
        }
        let renamed = &inaccessible[inaccessible.len() - new_names.len()..];
        for (new_name, &idx) in new_names.iter().zip(renamed) {
            if !new_name.is_unescaped_component("_") {
                goal.local_ctx[idx].name = new_name.clone();
            }
        }
    }
    Ok(())
}

/// Every component of `name` was generated, none written in source.
fn is_generated_name(name: &SurfaceName) -> bool {
    !name.is_anonymous()
        && name
            .component_syntax()
            .iter()
            .all(|origin| *origin == clean_parser::NameComponentSyntax::Generated)
}

pub(super) fn is_generated_inaccessible_name(name: &SurfaceName) -> bool {
    if name.is_relative_constructor()
        || name.is_anonymous()
        || !name
            .component_syntax()
            .iter()
            .all(|origin| *origin == clean_parser::NameComponentSyntax::Generated)
    {
        return false;
    }
    let Some((first, _)) = name.split_first() else {
        return false;
    };
    match first.name().inner() {
        clean_kernel::name::NameInner::Num(_, _) => true,
        clean_kernel::name::NameInner::Str(_, text) => {
            text.starts_with('_') || text.chars().next().is_some_and(|c| c.is_ascii_digit())
        }
        clean_kernel::name::NameInner::Anon => false,
    }
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
            let hyp_name = super::builtins::term_hyp_name(ps, &args[0])?;
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
            // `generalize (h :)? e = x at loc` — the parser puts a location
            // naming hypotheses after a fixed equation slot (`_` without `h`).
            [term, var, hyp, locations @ ..] if !locations.is_empty() => {
                let var_name = expr_to_hyp_name(ps, var)?;
                let hyp_name = expr_to_hyp_name(ps, hyp)?;
                let hyp_name = (!hyp_name.is_unescaped_component("_")).then_some(hyp_name);
                let mut listed = Vec::with_capacity(locations.len());
                let mut wildcard = false;
                for location in locations {
                    let name = expr_to_hyp_name(ps, location)?;
                    if name.is_unescaped_component("*") {
                        wildcard = true;
                    } else if !name.is_unescaped_component("⊢") {
                        listed.push(name);
                    }
                }
                let hyps = if wildcard {
                    super::generalize::GeneralizeHyps::All
                } else {
                    super::generalize::GeneralizeHyps::Listed(listed)
                };
                super::generalize::generalize_at(
                    ps,
                    term.clone(),
                    &var_name,
                    hyp_name.as_ref(),
                    &hyps,
                )
            }
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
pub(super) fn args_to_names(
    ps: &ProofState,
    args: &[Expr],
) -> Result<Vec<SurfaceName>, TacticError> {
    args.iter().map(|e| expr_to_hyp_name(ps, e)).collect()
}
