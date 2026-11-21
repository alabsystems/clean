//! Hypothesis locations for checked conditional and recursor case splits.

use clean_kernel::{Expr, ExprKind, RecursorArgOrder};
use clean_parser::SurfaceName;

use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};

/// Generalize the selected local and its dependents, split its conditional or
/// match discriminant, then restore their complete telescope in every branch. Every continuation
/// is built by the existing checked revert/split/intro operations. Unsupported
/// conditions and failed proof extraction restore the original proof state.
pub(super) fn split_at(state: &mut ProofState, name: &SurfaceName) -> TacticResult {
    let before = state.clone();
    let result = split_at_inner(state, name);
    if result.is_err() {
        *state = before;
    }
    result
}

fn split_at_inner(state: &mut ProofState, name: &SurfaceName) -> TacticResult {
    let original = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let selected = original
        .local_ctx
        .iter()
        .rev()
        .find(|local| super::pattern::names::hypothesis_named(&local.name, name))
        .ok_or_else(|| TacticError::HypothesisNotFound(name.to_string()))?;
    let ty = state.metas.instantiate(&selected.ty);
    // Checking this location BEFORE generalization prevents an unrelated
    // conditional in the conclusion from satisfying `split at h`.
    let conditional = super::connective::contains_splittable_ite(&ty);
    let found = if conditional {
        None
    } else {
        find_match_major(state, &original, &ty)
    };
    if !conditional && found.is_none() {
        return Err(TacticError::GoalMismatch(format!(
            "split at {name}: no splittable if-then-else or match discriminant in this hypothesis"
        )));
    }

    let site = found
        .as_ref()
        .filter(|found| has_nested_pattern(&found.original))
        .and_then(|found| application_path(&ty, &found.original));
    let trailing = state.goals.len() - 1;
    split_decision(state, name, &ty, found)?;
    if let Some(path) = site {
        expand_nested_patterns(state, name, &path, trailing)?;
    }
    Ok(())
}

fn split_decision(
    state: &mut ProofState,
    name: &SurfaceName,
    ty: &Expr,
    found: Option<MatchDecision>,
) -> TacticResult {
    let conditional = found.is_none();
    if let Some(found) = &found {
        if found.original != found.reduced
            && !super::equality::contains_expr(&found.original, &found.major)
        {
            // WHNF can expose the next decision as a projection of a record.
            // Generalizing that projection in the unreduced hypothesis would
            // leave the match on its old record. Change the hypothesis through
            // definitional equality before abstracting the major premise.
            let exposed = super::equality::replace_expr(ty, &found.original, &found.reduced);
            super::term_close::change_at(state, name, exposed)?;
        }
    }
    let original = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    super::congr_obtain::revert(state, name)?;
    let generalized = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let removed: Vec<_> = original
        .local_ctx
        .iter()
        .filter(|local| {
            !generalized
                .local_ctx
                .iter()
                .any(|kept| kept.fvar == local.fvar)
        })
        .collect();
    let trailing = state.goals.len() - 1;
    if let Some(found) = found {
        let temporary = super::pattern::util::generate_fresh_hyp_name(
            &original.local_ctx,
            &SurfaceName::generated_path("split_discriminant"),
        );
        // Abstract the discriminant through the reverted hypothesis AND the
        // conclusion. Merely calling cases_expr would leave occurrences in the
        // hypothesis unchanged. Generalization and cases each build a checked
        // continuation; an indexed or dependent case they cannot justify refuses.
        if let ExprKind::Proj(owner, index, receiver) = found.major.kind() {
            // Match compilation exposes a primitive projection, while a written
            // field in the reverted telescope can use its registered accessor.
            // Put those occurrences into the same form before abstracting them.
            let ty = state.infer_type(&generalized, receiver)?;
            let receiver_type = state.whnf(&generalized, &ty);
            if let Some(accessor) = crate::structure_cmd::field_accessor_application(
                state.env(),
                owner,
                &receiver_type,
                *index,
                receiver,
            ) {
                if super::equality::contains_expr(&generalized.target, &accessor) {
                    let target =
                        super::equality::replace_expr(&generalized.target, &accessor, &found.major);
                    super::term_close::change(state, target)?;
                }
            }
        }
        super::generalize::generalize(state, found.major, &temporary)?;
        super::proof_manipulation::cases(state, &temporary)?;
    } else {
        super::connective::split_ite(state, &generalized, Some(&original.local_ctx))?;
    }
    // Only the freshly split goals are visited. Trailing unrelated goals
    // retain their original order, contexts and unresolved obligations.
    let branches = state.goals.len() - trailing;
    for branch in 0..branches {
        state.goals.swap(0, branch);
        if !conditional {
            reserve_restored_names(state, &original, &generalized, &removed)?;
        }
        for local in &removed {
            super::intro(state, &local.name)?;
        }
        state.goals.swap(0, branch);
    }
    Ok(())
}

// Locate the selected expression within its hypothesis. Revisit only that
// occurrence after each branch refinement, never adjacent arguments or the
// body of a binder in the enclosing proposition.
fn application_path(ty: &Expr, selected: &Expr) -> Option<Vec<bool>> {
    crate::stack_safe(|| {
        if ty == selected {
            return Some(Vec::new());
        }
        let ExprKind::App(f, a) = ty.kind() else {
            return None;
        };
        for (is_arg, e) in [(false, f), (true, a)] {
            if let Some(mut path) = application_path(e, selected) {
                path.push(is_arg);
                return Some(path);
            }
        }
        None
    })
}

fn nested_motive(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::MData(markers, _) if markers.iter().any(|(key, value)|
        key.to_string() == crate::infer::NESTED_PATTERN_MOTIVE && matches!(value, clean_kernel::MDataValue::Bool(true))))
}

fn has_nested_pattern(e: &Expr) -> bool {
    let mut pending = vec![e];
    let mut seen = std::collections::HashSet::new();
    while let Some(e) = pending.pop() {
        if !seen.insert(e) {
            continue;
        }
        if nested_motive(e) {
            return true;
        }
        match e.kind() {
            ExprKind::App(f, a) => pending.extend([f.as_ref(), a.as_ref()]),
            ExprKind::Lam(_, _, body) | ExprKind::MData(_, body) => pending.push(body),
            ExprKind::Let(_, _, value, body, _) => {
                pending.push(value);
                pending.push(body);
            }
            _ => {}
        }
    }
    false
}

fn expand_nested_patterns(
    state: &mut ProofState,
    name: &SurfaceName,
    path: &[bool],
    trailing: usize,
) -> TacticResult {
    let rest = state.goals.split_off(state.goals.len() - trailing);
    let mut pending: Vec<_> = state.goals.drain(..).rev().map(|goal| (goal, 0)).collect();
    let mut leaves = std::collections::VecDeque::new();
    let limit = state.options().max_depth() as usize;
    while let Some((goal, depth)) = pending.pop() {
        let local = goal
            .local_ctx
            .iter()
            .rev()
            .find(|local| super::pattern::names::hypothesis_named(&local.name, name))
            .ok_or_else(|| TacticError::HypothesisNotFound(name.to_string()))?;
        let ty = state.metas.instantiate(&local.ty);
        let site = path.iter().rev().try_fold(&ty, |e, is_arg| match e.kind() {
            ExprKind::App(f, a) => Some(if *is_arg { a.as_ref() } else { f.as_ref() }),
            _ => None,
        });
        let decision = site.and_then(|e| {
            if e.has_loose_bvars() {
                return None;
            }
            let exposed = state.whnf(&goal, e);
            match_decision(state, e, &exposed).filter(|found| found.nested)
        });
        if let Some(decision) = decision {
            if depth >= limit {
                return Err(TacticError::DepthExceeded {
                    tactic: "split at".into(),
                    max_depth: limit,
                });
            }
            state.goals.push_front(goal);
            split_decision(state, name, &ty, Some(decision))?;
            pending.extend(state.goals.drain(..).rev().map(|goal| (goal, depth + 1)));
        } else {
            leaves.push_back(goal);
        }
    }
    state.goals = leaves;
    state.goals.extend(rest);
    Ok(())
}

/// Constructor fields are new locals. Keep their generated names from taking
/// a reverted source hypothesis's name, since intro otherwise freshens that
/// requested source name and a following `exact h` can select the wrong local.
/// As with rename, only display/resolution names change; every FVar and type
/// and every checked case continuation is retained.
fn reserve_restored_names(
    state: &mut ProofState,
    original: &Goal,
    generalized: &Goal,
    removed: &[&LocalDecl],
) -> TacticResult {
    let branch = state.current_goal_mut().ok_or(TacticError::NoGoals)?;
    let mut reserved = original.local_ctx.clone();
    reserved.extend(branch.local_ctx.clone());
    for local in &mut branch.local_ctx {
        if !generalized
            .local_ctx
            .iter()
            .any(|kept| kept.fvar == local.fvar)
            && removed
                .iter()
                .any(|old| super::pattern::names::local_name_matches(&local.name, &old.name))
        {
            local.name = super::pattern::util::generate_fresh_hyp_name(&reserved, &local.name);
            reserved.push(local.clone());
        }
    }
    Ok(())
}

/// Read the major slot from registered recursor metadata, never from an assumed
/// argument order. A casesOn suffix is only an unfolding/search hint: a wrapper
/// must expose a registered recursor before any major is selected. WHNF exposes imported wrappers and
/// eliminates already-known constructor matches. A major beneath a binder may
/// be used only when it has no loose bound variables at this location.
struct MatchDecision {
    original: Expr,
    reduced: Expr,
    major: Expr,
    nested: bool,
}

fn match_decision(state: &ProofState, original: &Expr, reduced: &Expr) -> Option<MatchDecision> {
    let ExprKind::Const(name, _) = reduced.get_app_fn().kind() else {
        return None;
    };
    let recursor = state.env.get_recursor(name)?;
    let args = reduced.get_app_args();
    let params = recursor.num_params as usize;
    let motives = recursor.num_motives as usize;
    let before_major = params
        + motives
        + recursor.num_indices as usize
        + match recursor.arg_order {
            RecursorArgOrder::MajorAfterMinors => recursor.num_minors as usize,
            RecursorArgOrder::MajorAfterMotive => 0,
        };
    let major = *args.get(before_major)?;
    if major.has_loose_bvars() {
        return None;
    }
    let nested = args[params..params + motives]
        .iter()
        .any(|m| nested_motive(m));
    Some(MatchDecision {
        original: original.clone(),
        reduced: reduced.clone(),
        major: major.clone(),
        nested,
    })
}

fn find_match_major(state: &ProofState, goal: &Goal, expression: &Expr) -> Option<MatchDecision> {
    crate::stack_safe(|| {
        // A body visited below a Pi/lambda is not itself well formed in the
        // outer goal's local context. Inspect its syntactic recursor spine;
        // only closed subterms may enter that context's type checker.
        // Do not unfold arbitrary functions while scanning (e.g. arithmetic
        // hidden in other arguments). Source `unfold` exposes the match first.
        let candidate_head = match expression.get_app_fn().kind() {
            ExprKind::Const(name, _) => {
                state.env.get_recursor(name).is_some() || name.to_string().ends_with(".casesOn")
            }
            _ => false,
        };
        let reduced = if expression.has_loose_bvars() || !candidate_head {
            expression.clone()
        } else {
            state.whnf(goal, expression)
        };
        if let Some(decision) = match_decision(state, expression, &reduced) {
            return Some(decision);
        }
        match reduced.kind() {
            ExprKind::App(function, argument) => find_match_major(state, goal, function)
                .or_else(|| find_match_major(state, goal, argument)),
            ExprKind::Lam(_, _, body) => find_match_major(state, goal, body),
            ExprKind::Pi(_, domain, body) => find_match_major(state, goal, domain)
                .or_else(|| find_match_major(state, goal, body)),
            ExprKind::Let(_, ty, value, body, _) => find_match_major(state, goal, ty)
                .or_else(|| find_match_major(state, goal, value))
                .or_else(|| find_match_major(state, goal, body)),
            ExprKind::Proj(_, _, value) | ExprKind::MData(_, value) => {
                find_match_major(state, goal, value)
            }
            _ => None,
        }
    })
}
