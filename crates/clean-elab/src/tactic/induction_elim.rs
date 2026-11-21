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
//! Serves eliminators with **exactly one explicit target** (the one the user
//! names) and any number of implicit targets, which are solved the way Lean's
//! `addImplicitTargets` solves them: by unifying the explicit target's
//! declared type with the major premise's type. As in Lean, a target binder
//! that is not explicit is implicit whatever else it is, so an eliminator
//! whose only target is `{t : T}` has "too many targets" for `induction t`.
//! Everything outside that fails closed with a diagnostic that names the
//! construct — never a silent sorry:
//!
//! - no explicit target, or more than one (Lean: `Too many targets` /
//!   `Insufficient number of targets`);
//! - a motive applied to a computed argument (`num_complex_motive_args > 0`)
//!   — needs index unification (RC-S) — or to its targets out of telescope
//!   order;
//! - an implicit target that matching cannot solve, that is not a local, that
//!   repeats another target (Lean's `checkInductionTargets`), that is
//!   let-bound, or that some other hypothesis depends on (Lean reverts those
//!   in `generalizeVars`);
//! - any non-motive, non-target, non-alternative binder that first-order
//!   matching cannot solve, in particular instance-implicit parameters.
//!
//! After the split every target is cleared from each case, in target order,
//! when nothing left in that case mentions it (Lean's `toClear` with
//! `tryClear`), so a case whose goal still mentions an implicit target keeps
//! it.
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
use clean_parser::SurfaceName;

use super::builtins_replace::mentions_fvar;
use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::elim_info::{get_elim_info, match_pattern, telescope, ElimInfo, ElimSolution};
use super::elim_targets::{explicit_target, resolve_targets};
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
    tag: SurfaceName,
    /// `fun fields… => ?case_meta`, the argument passed to the eliminator.
    case_proof: Expr,
    case_binders: Vec<FVarId>,
}

/// How the alternatives' case goals are tagged.
#[derive(Clone, Copy, Debug)]
pub(crate) enum AltTags<'a> {
    /// `induction … using e with | a … => …`: the *i*-th `with` alternative
    /// names the *i*-th alternative (see the module docs).
    WithBlock(&'a [SurfaceName]),
    /// An `@[induction_eliminator]` chosen by the registry. Lean tags these
    /// with the alternatives' binder names, which Clean's kernel `Pi` does not
    /// store, so each case gets a tag no `case` or `with` alternative can
    /// spell: a later reference by Lean's name fails instead of matching a
    /// guessed one.
    Inaccessible,
}

fn unsupported(detail: String) -> TacticError {
    TacticError::InvalidTarget {
        tactic: "induction … using".into(),
        detail,
    }
}

/// `induction <hyp> using <elim>` for a non-recursor eliminator.
///
/// With [`AltTags::WithBlock`], entry *i* of the `with`-block names tags case
/// *i* (see the module docs); an absent or `_` entry falls back to
/// `alt<binder position>`.
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
    hyp_name: &SurfaceName,
    elim_name: &Name,
    tags: AltTags<'_>,
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
    if info.targets_pos.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(unsupported(format!(
            "`{elim_name}` applies its motive to its targets out of their parameter order; \
             that motive layout is not supported"
        )));
    }
    let explicit_pos = explicit_target(&elim_const.type_, &info, elim_name)?;
    let explicit_motive_param = info
        .targets_pos
        .iter()
        .position(|&pos| pos == explicit_pos)
        .ok_or_else(|| unsupported(format!("`{elim_name}`: explicit target is not a target")))?;

    // ---- the major premise --------------------------------------------------
    let hyp_decl = goal
        .local_ctx
        .iter()
        .rev()
        .find(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, hyp_name))
        .ok_or_else(|| TacticError::UnknownIdent(hyp_name.to_string()))?;
    let hyp_fvar = hyp_decl.fvar;
    let hyp_ty = state.metas.instantiate(&hyp_decl.ty);

    // ---- solve universe levels and the remaining parameters -----------------
    let solution = solve_elim(
        state,
        &goal,
        &info,
        &elim_const,
        explicit_pos,
        explicit_motive_param,
        &hyp_ty,
    )?;
    let levels = collect_levels(&solution, &elim_const.level_params, elim_name)?;
    let target_fvars = resolve_targets(
        state,
        &goal,
        &info,
        &solution,
        explicit_pos,
        hyp_fvar,
        elim_name,
    )?;

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
            build_motive(&domain, &goal_target, &target_fvars, elim_name)?
        } else if let Some(k) = info.targets_pos.iter().position(|&t| t == pos) {
            Expr::fvar(target_fvars[k])
        } else if let Some(alt) = info.alts_info.iter().find(|a| a.binder_pos == pos) {
            let tag = alt_tag(tags, alt_index, alt.binder_pos);
            alt_index += 1;
            state.next_fvar = branch_fvar_base;
            let case = build_case(state, &goal, &target_fvars, &domain, alt.num_fields, tag)?;
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
            case_binders: case.case_binders,
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
fn alt_tag(tags: AltTags<'_>, index: usize, binder_pos: usize) -> SurfaceName {
    match tags {
        AltTags::WithBlock(alt_names) => match alt_names.get(index) {
            Some(name) if !name.is_unescaped_component("_") && !name.is_anonymous() => name.clone(),
            _ => SurfaceName::from_name(Name::anon().str(format!("alt{binder_pos}"))),
        },
        AltTags::Inaccessible => SurfaceName::from_name(
            Name::anon()
                .num(0x5441_4354)
                .str("custom_eliminator_alt")
                .num(binder_pos as u64),
        ),
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
    motive_param: usize,
    hyp_ty: &Expr,
) -> Result<ElimSolution, TacticError> {
    let params = &elim_const.level_params;
    let (binders, _) = telescope(&elim_const.type_);
    let mut sol = ElimSolution::default();

    // Matching application arguments before exposing an abbreviation can bind
    // the wrong telescope slot. Compare reducible heads first when the two
    // named carriers differ, and keep the original representation on a miss.
    let mut match_major = |pattern: &Expr, depth| {
        if let (ExprKind::Const(want, _), ExprKind::Const(have, _)) =
            (pattern.get_app_fn().kind(), hyp_ty.get_app_fn().kind())
        {
            if want != have
                && (crate::instance_alias::is_reducible_definition(&state.env, have)
                    || crate::instance_alias::is_reducible_definition(&state.env, want))
            {
                let declared = state.whnf_indexing(goal, pattern);
                let actual = state.whnf_indexing(goal, hyp_ty);
                if matches!((declared.get_app_fn().kind(), actual.get_app_fn().kind()),
                    (ExprKind::Const(left, _), ExprKind::Const(right, _)) if left == right)
                {
                    match_pattern(&declared, &actual, depth, params, &mut sol);
                    return;
                }
            }
        }
        match_pattern(pattern, hyp_ty, depth, params, &mut sol);
    };

    // (1) target binder type ≟ actual hypothesis type
    if let Some((_, target_ty)) = binders.get(target_pos) {
        match_major(target_ty, target_pos);
    }

    // (2) motive telescope: parameter type ≟ hypothesis type, result sort ≟ goal sort.
    // The parameter is matched only when the explicit target is the motive's
    // FIRST parameter: a later one's type is in the scope of the earlier
    // motive parameters, which `match_pattern` would misread as eliminator
    // binders.
    if let Some((_, motive_ty)) = binders.get(info.motive_pos) {
        let (motive_params, motive_result) = telescope(motive_ty);
        if motive_param == 0 {
            if let Some((_, motive_dom)) = motive_params.first() {
                match_major(motive_dom, info.motive_pos);
            }
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

/// `fun (x₁ : D₁) … (xₙ : Dₙ) => target[t₁ := x₁, …, tₙ := xₙ]` over the
/// targets in order (Lean's `setMotiveArg`, `mkLambdaFVars targets goal`),
/// with each `Dᵢ` the eliminator's own motive domain so the application
/// type-checks against the declared motive type.
fn build_motive(
    motive_ty: &Expr,
    goal_target: &Expr,
    target_fvars: &[FVarId],
    elim_name: &Name,
) -> Result<Expr, TacticError> {
    let mut domains = Vec::with_capacity(target_fvars.len());
    let mut current = motive_ty.clone();
    for _ in target_fvars {
        let ExprKind::Pi(binder, domain, codomain) = current.strip_mdata().kind() else {
            return Err(unsupported(format!(
                "`{elim_name}`: motive does not take one parameter per target"
            )));
        };
        domains.push((binder.info, domain.as_ref().clone()));
        current = codomain.as_ref().clone();
    }
    // Abstracting `t₁` first and `tₙ` last leaves `tₙ` at `BVar 0` and `t₁`
    // at `BVar (n-1)`: `abstract_fvar` shifts the loose variables it meets.
    let mut body = goal_target.clone();
    for &fvar in target_fvars {
        body = body.abstract_fvar(fvar);
    }
    for (info, domain) in domains.into_iter().rev() {
        body = Expr::lam(info, domain, body);
    }
    Ok(body)
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
    targets: &[FVarId],
    alt_ty: &Expr,
    num_fields: usize,
    tag: SurfaceName,
) -> Result<ElimCase, TacticError> {
    let mut new_ctx = goal.local_ctx.clone();

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
                    binder_info: *binder,
                    fvar,
                    name: super::pattern::util::generate_fresh_hyp_name(
                        &new_ctx,
                        &super::case_field_names::generated_case_field_name(
                            &tag,
                            fields.len() as u64,
                            super::case_field_names::CaseFieldKind::Field,
                        ),
                    ),
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
    // Lean's `toClear`: each target, in target order, is cleared when nothing
    // left in the case mentions it (`tryClear`). The major premise's
    // dependents were reverted before the split, so it is normally cleared;
    // an implicit target the case still mentions (`motive a a refl` keeps
    // `a`) stays, as does one a later target still depends on when it is
    // tried.
    for &target in targets {
        let Some(idx) = new_ctx.iter().position(|d| d.fvar == target) else {
            continue;
        };
        let mentioned = mentions_fvar(&new_target, target)
            || new_ctx.iter().skip(idx + 1).any(|d| {
                mentions_fvar(&state.metas.instantiate(&d.ty), target)
                    || d.value
                        .as_ref()
                        .is_some_and(|v| mentions_fvar(&state.metas.instantiate(v), target))
            });
        if !mentioned {
            new_ctx.remove(idx);
        }
    }
    // Scope keeps the eliminated major, as for `cases` (`fresh_case_meta`).
    let case_meta = state.fresh_case_meta(new_target.clone(), goal, &new_ctx);

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
        case_binders: fields.iter().map(|(id, _, _)| *id).collect(),
    })
}
