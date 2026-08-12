// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `induction … using <eliminator>` for eliminators that are **not** kernel
//! recursors — Lean's `@[elab_as_elim]` declarations.
//!
//! # Why a second path exists
//!
//! [`super::induction::induction_using`] assembles the proof term in the fixed
//! recursor order (`params → motive → minors → major`) and drives the case
//! split from `InductiveVal::constructor_names` + `RecursorVal::rules`. Neither
//! can express `Nat.strongRecOn`:
//!
//! ```text
//! Nat.strongRecOn.{u} {motive : Nat → Sort u} (n : Nat)
//!     (ind : ∀ n, (∀ m, m < n → motive m) → motive n) : motive n
//! ```
//!
//! — the motive *precedes* the target, there is exactly one alternative (not
//! one per `Nat` constructor), and that alternative's telescope is nested. This
//! module is therefore telescope-driven: [`super::elim_info::get_elim_info`]
//! reads the shape off the eliminator's own type and the proof term is built
//! binder by binder in the eliminator's declared order.
//!
//! # Dispatch
//!
//! Reached **only** when `Environment::get_recursor` returns `None` for the
//! `using` name, so the recursor fast path is untouched: an eliminator that is
//! a real recursor still takes the original route, bit for bit.
//!
//! # Bounded scope (deliberate)
//!
//! Serves **single-target, non-indexed eliminators with explicit
//! alternatives**. Everything outside that fails closed with a diagnostic that
//! names the construct — never a silent sorry:
//!
//! - more than one target, or a motive applied to a computed argument
//!   (`num_complex_motive_args > 0`) — needs index unification (RC-S);
//! - implicit targets that must be *discovered* rather than named — Lean's
//!   `addImplicitTargets`;
//! - any non-motive, non-target, non-alternative binder that first-order
//!   matching cannot solve, in particular instance-implicit parameters.
//!
//! # Alternative tags and the missing binder name
//!
//! Lean tags each case goal with the alternative's binder name
//! (`ElimAltInfo.name = xDecl.userName`). Clean's kernel [`ExprKind::Pi`] does
//! **not store binder names** — `crates/clean-olean/src/import/convert_expr.rs`
//! parses `forallE`'s name and drops it — so that tag is not recoverable from
//! the environment for any imported eliminator.
//!
//! Tags are therefore taken **positionally** from the user's `with` block: the
//! *i*-th `| name … =>` alternative names the *i*-th alternative of the
//! eliminator. `induction n using Nat.strongRecOn with | ind n ih => …` tags
//! the single case `ind`, which is what Lean produces. Writing the
//! alternatives out of the eliminator's declared order (which Lean accepts,
//! since it matches by name) mis-assigns the tags here; the mismatched case
//! body then fails to prove its goal and the proof is rejected. That is a
//! usability limitation, never an unsoundness: every assembled term is
//! re-checked by the kernel.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};

use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::elim_info::{get_elim_info, match_pattern, telescope, ElimInfo, ElimSolution};
use super::simp::beta_reduce;

/// A case goal produced by a custom eliminator's alternative.
struct ElimCase {
    /// Metavariable standing for this alternative's proof.
    case_meta: crate::unify::MetaId,
    /// Local context of the case goal.
    new_ctx: Vec<LocalDecl>,
    /// Target of the case goal.
    new_target: Expr,
    /// Goal tag (see the module docs on positional tagging).
    tag: String,
    /// `fun fields… => ?case_meta`, the argument passed to the eliminator.
    case_proof: Expr,
}

fn unsupported(detail: String) -> TacticError {
    TacticError::InvalidTarget {
        tactic: "induction … using".into(),
        detail,
    }
}

/// `induction <hyp> using <elim>` for a non-recursor eliminator.
///
/// `alt_names` are the `with`-block alternative names in source order; entry
/// *i* tags case *i* (see the module docs). An absent or `_` entry falls back
/// to `alt<binder position>`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `elim_name` is NOT a registered kernel recursor (the caller
///   dispatches on that)
/// ENSURES: On Ok, the current goal is closed with
///   `@elim levels… args…` and one goal per alternative is pushed, tagged
/// ENSURES: On Ok, the assembled term's type is def-eq to the original target
///   (checked by `close_goal_assembled`) and is re-checked strictly by
///   `verify_tactic_proof` once the case metas are solved
/// ENSURES: On Err, `state` is unchanged and no goal has been closed
pub(crate) fn induction_using_eliminator(
    state: &mut ProofState,
    hyp_name: &str,
    elim_name: &Name,
    alt_names: &[String],
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let elim_const = state
        .env
        .get_const(elim_name)
        .ok_or_else(|| TacticError::EnvironmentMissing {
            constant: elim_name.to_string(),
        })?
        .clone();

    let info = get_elim_info(&elim_const.type_)
        .map_err(|e| unsupported(format!("`{elim_name}` is not an eliminator: {e}")))?;

    // ---- bounded-shape gate -------------------------------------------------
    if info.targets_pos.len() != 1 {
        return Err(unsupported(format!(
            "`{elim_name}` has {} targets; this implementation serves single-target eliminators \
             (multi-target needs index unification)",
            info.targets_pos.len()
        )));
    }
    if info.num_complex_motive_args != 0 {
        return Err(unsupported(format!(
            "`{elim_name}` applies its motive to {} computed argument(s); indexed eliminators are \
             not yet supported",
            info.num_complex_motive_args
        )));
    }
    if !info.alts_info.is_empty() && !info.alts_info.iter().any(|alt| alt.proves_motive) {
        return Err(unsupported(format!(
            "`{elim_name}` has {} explicit alternative(s) but none of them concludes with the \
             motive, so it does not eliminate into the goal",
            info.alts_info.len()
        )));
    }
    let target_pos = info.targets_pos[0];

    // ---- the major premise --------------------------------------------------
    let (hyp_idx, hyp_decl) = goal
        .local_ctx
        .iter()
        .enumerate()
        .find(|(_, d)| d.name == hyp_name)
        .ok_or_else(|| TacticError::UnknownIdent(hyp_name.to_string()))?;
    let hyp_fvar = hyp_decl.fvar;
    let hyp_ty = state.metas.instantiate(&hyp_decl.ty);

    // ---- solve universe levels and the remaining parameters -----------------
    let solution = solve_elim(state, &goal, &info, &elim_const, target_pos, &hyp_ty)?;
    let levels = collect_levels(&solution, &elim_const.level_params, elim_name)?;

    // ---- walk the telescope, building one argument per binder ---------------
    let elim_type = elim_const
        .type_
        .instantiate_level_params_direct(&elim_const.level_params, &levels);
    let goal_target = state.metas.instantiate(&goal.target);

    let mut args: Vec<Expr> = Vec::with_capacity(info.num_binders);
    let mut cases: Vec<ElimCase> = Vec::new();
    let mut alt_index = 0usize;
    let mut remaining = elim_type;

    // Every alternative's field FVars must be numbered from the SAME base, the
    // way `cases_core` numbers its branches (`proof_manipulation.rs`). The
    // assignment scope validator accepts a tactic FVar inside the assembled
    // term only when `id - binder_base < binder_depth` at its occurrence
    // (`close_fvars::assignment_scope_violation`), and each alternative's
    // lambda re-starts that depth at zero. Letting the global counter run on
    // across alternatives makes the SECOND alternative's first field
    // `binder_base + 1` at depth 1 and the proof is rejected — which is exactly
    // what a two-alternative eliminator whose first alternative binds a field
    // did before this reset. Field FVars never cross alternatives (each appears
    // only in its own `new_ctx` and its own lambda), so resetting is safe.
    let branch_fvar_base = state.goal_binder_base(&goal);
    let mut branch_fvar_max = branch_fvar_base;

    for pos in 0..info.num_binders {
        let ExprKind::Pi(binder, domain, codomain) = remaining.strip_mdata().kind() else {
            return Err(unsupported(format!(
                "`{elim_name}`: telescope binder {pos} disappeared under level instantiation"
            )));
        };
        let binder_info = binder.info;
        let domain = domain.as_ref().clone();
        let codomain = codomain.as_ref().clone();

        let arg = if pos == info.motive_pos {
            build_motive(&domain, &goal_target, hyp_fvar, elim_name)?
        } else if pos == target_pos {
            Expr::fvar(hyp_fvar)
        } else if let Some(alt) = info.alts_info.iter().find(|a| a.binder_pos == pos) {
            let tag = alt_tag(alt_names, alt_index, alt.binder_pos);
            alt_index += 1;
            state.next_fvar = branch_fvar_base;
            let case = build_case(state, &goal, hyp_idx, &domain, alt.num_fields, tag)?;
            branch_fvar_max = branch_fvar_max.max(state.next_fvar);
            let proof = case.case_proof.clone();
            cases.push(case);
            proof
        } else {
            solution.binder(pos).cloned().ok_or_else(|| {
                unsupported(format!(
                    "`{elim_name}`: could not determine parameter {pos} ({}) from the goal; \
                     eliminators with unsolvable implicit or instance parameters are not yet \
                     supported",
                    describe_binder(binder_info)
                ))
            })?
        };

        remaining = codomain.instantiate(&arg);
        args.push(arg);
    }

    // Leave the counter past every alternative's fields so tactics later run on
    // the case goals cannot collide with them (mirrors `cases_core`).
    state.next_fvar = branch_fvar_max;

    // ---- assemble and close -------------------------------------------------
    let proof = Expr::apps(Expr::const_(elim_name.clone(), levels), args);

    // The alternative arguments wrap still-open case metas whose stored targets
    // reference this tactic's field binders, exactly as in the recursor path:
    // use the assembly-time close (lenient spine inference + def-eq target
    // match). `verify_tactic_proof` re-checks strictly once the metas are
    // solved, so a wrong eliminator is rejected there, never accepted silently.
    state.close_goal_assembled(&goal, proof)?;

    for case in cases {
        state.goals.push_back(Goal {
            meta_id: case.case_meta,
            target: case.new_target,
            local_ctx: case.new_ctx,
            tag: Some(case.tag),
        });
    }
    Ok(())
}

/// Human-readable binder kind, for the fail-closed diagnostic.
fn describe_binder(info: BinderInfo) -> &'static str {
    match info {
        BinderInfo::Implicit => "implicit",
        BinderInfo::InstImplicit => "instance-implicit",
        BinderInfo::StrictImplicit => "strict-implicit",
        _ => "explicit",
    }
}

/// Tag for the `i`-th alternative: the user's `with`-block name when there is
/// one, else a positional fallback.
fn alt_tag(alt_names: &[String], index: usize, binder_pos: usize) -> String {
    match alt_names.get(index) {
        Some(name) if name != "_" && !name.is_empty() => name.clone(),
        _ => format!("alt{binder_pos}"),
    }
}

/// Recover the eliminator's universe levels and implicit parameters by
/// first-order matching against the goal.
///
/// Two independent matches feed the same solution:
/// 1. the **target binder's declared type** against the major premise's actual
///    type — this solves type parameters (`{α : Type u}` in `List` eliminators)
///    and their levels;
/// 2. the **motive's result sort** against the goal target's sort — this solves
///    the motive universe (`Sort u ↦ Prop` for a propositional goal);
/// 3. each **already-solved parameter's declared type** against the inferred
///    type of its solution. A level can appear nowhere but a parameter's own
///    type: `WellFounded.induction {α : Sort u} {r : α → α → Prop} (hwf) …` pins
///    `α := Nat` from step 1, and only `Sort u ≟ Sort 1` (the type of `Nat`)
///    then determines `u`.
///
/// Clean's [`Level`] has no metavariable constructor, so this matching *is* the
/// level solver; there is no unifier to defer to.
fn solve_elim(
    state: &ProofState,
    goal: &Goal,
    info: &ElimInfo,
    elim_const: &clean_kernel::ConstantInfo,
    target_pos: usize,
    hyp_ty: &Expr,
) -> Result<ElimSolution, TacticError> {
    let params = &elim_const.level_params;
    let (binders, _) = telescope(&elim_const.type_);
    let mut sol = ElimSolution::default();

    // (1) target binder type ≟ actual hypothesis type
    if let Some((_, target_ty)) = binders.get(target_pos) {
        match_pattern(target_ty, hyp_ty, target_pos, params, &mut sol);
    }

    // (2) motive telescope: parameter type ≟ hypothesis type, result sort ≟ goal sort
    if let Some((_, motive_ty)) = binders.get(info.motive_pos) {
        let (motive_params, motive_result) = telescope(motive_ty);
        if let Some((_, motive_dom)) = motive_params.first() {
            match_pattern(motive_dom, hyp_ty, info.motive_pos, params, &mut sol);
        }
        if let ExprKind::Sort(level_pattern) = motive_result.strip_mdata().kind() {
            let goal_sort = goal_sort_level(state, goal)?;
            match_pattern(
                &Expr::sort(level_pattern.clone()),
                &Expr::sort(goal_sort),
                info.motive_pos,
                params,
                &mut sol,
            );
        }
    }

    // (3) solved parameter's declared type ≟ inferred type of its solution.
    // Assignments are first-write-wins, so the direct matches above always win;
    // this only fills levels nothing else determines.
    let solved: Vec<(usize, Expr)> = sol.binder_values.clone();
    for (pos, value) in solved {
        let Some((_, declared)) = binders.get(pos) else {
            continue;
        };
        let Ok(value_ty) = state.infer_type(goal, &value) else {
            continue;
        };
        let value_ty = state.whnf(goal, &value_ty);
        match_pattern(declared, &value_ty, pos, params, &mut sol);
    }

    Ok(sol)
}

/// The universe level of the goal target, i.e. `l` in `target : Sort l`.
fn goal_sort_level(state: &ProofState, goal: &Goal) -> Result<Level, TacticError> {
    let target = state.metas.instantiate(&goal.target);
    let target_ty = state.infer_type(goal, &target)?;
    match state.whnf(goal, &target_ty).strip_mdata().kind() {
        ExprKind::Sort(level) => Ok(level.clone()),
        other => Err(unsupported(format!(
            "the goal target does not live in a sort (inferred {other:?})"
        ))),
    }
}

/// Order the solved levels to match the eliminator's declared level parameters.
///
/// An unsolved parameter fails closed: guessing `0` would build a term the
/// kernel rejects with a far less legible error, and could silently pick the
/// wrong universe for an eliminator whose levels do not appear in the goal.
fn collect_levels(
    sol: &ElimSolution,
    level_params: &[Name],
    elim_name: &Name,
) -> Result<Vec<Level>, TacticError> {
    level_params
        .iter()
        .map(|param| {
            sol.levels
                .iter()
                .find(|(p, _)| p == param)
                .map(|(_, l)| l.clone())
                .ok_or_else(|| {
                    unsupported(format!(
                        "`{elim_name}`: universe parameter `{param}` is not determined by the goal"
                    ))
                })
        })
        .collect()
}

/// `fun (x : D) => target[hyp := x]`, with `D` the eliminator's own motive
/// domain so the application type-checks against the declared motive type.
fn build_motive(
    motive_ty: &Expr,
    goal_target: &Expr,
    hyp_fvar: FVarId,
    elim_name: &Name,
) -> Result<Expr, TacticError> {
    let ExprKind::Pi(binder, domain, _) = motive_ty.strip_mdata().kind() else {
        return Err(unsupported(format!(
            "`{elim_name}`: motive is not a function type"
        )));
    };
    Ok(Expr::lam(
        binder.info,
        domain.as_ref().clone(),
        goal_target.abstract_fvar(hyp_fvar),
    ))
}

/// Turn one alternative's declared type into a case goal plus the
/// `fun fields… => ?case` argument the eliminator receives.
///
/// Every field type and the case target are beta-reduced: once the motive is
/// substituted, each `motive e` in the alternative is a redex
/// `(fun x => target x) e`, and leaving those unreduced would show the user an
/// induction hypothesis of the shape `∀ m, m < n → (fun x => …) m`.
///
/// A `let` in the alternative's telescope (which `altArity` counts, so it is
/// part of `num_fields`) binds nothing the user can name: it is zeta-reduced
/// and consumes its slot without producing a field.
fn build_case(
    state: &mut ProofState,
    goal: &Goal,
    hyp_idx: usize,
    alt_ty: &Expr,
    num_fields: usize,
    tag: String,
) -> Result<ElimCase, TacticError> {
    let mut new_ctx = goal.local_ctx.clone();
    // The major premise is consumed by the eliminator, exactly as in the
    // recursor path (`build_induction_cases`). Hypotheses that *depend* on it
    // are not auto-reverted here either — that is the shared `cases`/`induction`
    // gap (RC-G / brick T12), not specific to this path.
    if hyp_idx < new_ctx.len() {
        new_ctx.remove(hyp_idx);
    }

    let mut current = alt_ty.clone();
    let mut fields: Vec<(FVarId, BinderInfo, Expr)> = Vec::with_capacity(num_fields);
    for slot in 0..num_fields {
        match current.strip_mdata().kind() {
            ExprKind::Pi(binder, domain, codomain) => {
                let binder_info = binder.info;
                let field_ty = beta_reduce(domain);
                let codomain = codomain.as_ref().clone();
                let fvar = state.fresh_fvar();
                new_ctx.push(LocalDecl {
                    fvar,
                    name: format!("{tag}_{}", fields.len()),
                    ty: field_ty.clone(),
                    value: None,
                });
                fields.push((fvar, binder_info, field_ty));
                current = codomain.instantiate(&Expr::fvar(fvar));
            }
            ExprKind::Let(_, _, value, body, _) => {
                let value = value.as_ref().clone();
                current = body.instantiate(&value);
            }
            _ => {
                return Err(unsupported(format!(
                    "alternative `{tag}`: expected {num_fields} binder(s), telescope ended at {slot}"
                )));
            }
        }
    }

    let new_target = beta_reduce(&current);
    let case_meta = state.fresh_meta_in_context(new_target.clone(), &new_ctx);

    let mut case_proof =
        Expr::from_kind(ExprKind::FVar(crate::unify::MetaState::to_fvar(case_meta)));
    for (fvar, binder_info, field_ty) in fields.iter().rev() {
        case_proof = Expr::lam(
            *binder_info,
            field_ty.clone(),
            case_proof.abstract_fvar(*fvar),
        );
    }

    Ok(ElimCase {
        case_meta,
        new_ctx,
        new_target,
        tag,
        case_proof,
    })
}
