// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic for case analysis on inductive types (`cases`).
//!
//! The `induction` tactic has been split to `induction.rs` (#307).

use super::pattern::names::local_name_matches;
use clean_parser::{SurfaceInductionAlt, SurfaceName};

use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::indexed_family::{applied_index_args, beta_apply, build_family_motive, FamilyMotive};
use super::pattern::util::generate_fresh_hyp_name as fresh_hyp_name;

/// Compute universe levels for a recursor/casesOn constant.
///
/// Recursors may have one extra level parameter for the motive's return universe
/// (prepended before the inductive's own levels). For Prop-only eliminators,
/// the recursor has the same levels as the inductive.
///
/// `ind_levels`: universe levels from the inductive type's head expression.
/// `rec_level_count`: number of level params on the recursor (from env).
/// REQUIRES: `ind_levels` contains the universe levels from the inductive's head expression
/// REQUIRES: `rec_level_count` is the number of level params on the recursor
/// ENSURES: returned vec has length `rec_level_count`
/// ENSURES: if recursor has a motive level, it is prepended before `ind_levels`
pub(crate) fn recursor_levels(
    state: &ProofState,
    goal: &Goal,
    ind_levels: &[Level],
    rec_level_count: usize,
) -> Vec<Level> {
    if rec_level_count > ind_levels.len() {
        // Recursor has motive level — infer from target's sort.
        let motive_level = state
            .infer_type(goal, &goal.target)
            .ok()
            .and_then(|ty| match ty.kind() {
                ExprKind::Sort(level) => Some(level.clone()),
                _ => None,
            })
            .unwrap_or_else(Level::zero);
        let mut levels = vec![motive_level];
        levels.extend(ind_levels.iter().cloned());
        levels
    } else {
        ind_levels.to_vec()
    }
}

/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` refers to a hypothesis whose type is an inductive type
/// ENSURES: On Ok, the current goal is replaced by one goal per constructor
/// ENSURES: On Ok, each new goal has constructor arguments added to the local context
/// ENSURES: On Err(UnknownIdent), `hyp_name` is not in the local context
pub fn cases(state: &mut ProofState, hyp_name: &SurfaceName) -> TacticResult {
    cases_with_alternatives(state, hyp_name, &[]).map(|_| ())
}

/// Returns whether the index-equation path already named the constructor
/// fields. It must consume source names before those equations eliminate fields.
pub(super) fn cases_with_alternatives(
    state: &mut ProofState,
    hyp_name: &SurfaceName,
    alts: &[SurfaceInductionAlt],
) -> Result<bool, TacticError> {
    super::pattern::names::require_binding_name(hyp_name, "cases")?;
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let hyp_decl = goal
        .local_ctx
        .iter()
        .rev()
        .find(|d| local_name_matches(&d.name, hyp_name))
        .ok_or_else(|| TacticError::UnknownIdent(hyp_name.to_string()))?;
    let hyp_fvar = hyp_decl.fvar;
    cases_fvar_with_alternatives(state, hyp_fvar, alts)
}

/// `cases` on the local bound to `hyp_fvar`, selected by identity rather than
/// by name.
///
/// [`cases`] resolves a NAME to the innermost local carrying it, so a
/// hypothesis whose name is shadowed or inaccessible (`h✝`, a generated case
/// field) cannot be reached through it. Internal callers that already hold the
/// exact local — omega's hypothesis splitter — use this instead; the
/// elimination first retains compound-index equations, then uses `cases_core`,
/// including its `Eq` → `unifyEqs?`
/// routing and its removal of the eliminated local from every branch.
///
/// ENSURES: On Err(HypothesisNotFound), no local of the current goal is bound
///   to `hyp_fvar`; otherwise exactly what [`cases`] ensures.
pub(crate) fn cases_fvar(state: &mut ProofState, hyp_fvar: clean_kernel::FVarId) -> TacticResult {
    cases_fvar_with_alternatives(state, hyp_fvar, &[]).map(|_| ())
}

fn cases_fvar_with_alternatives(
    state: &mut ProofState,
    hyp_fvar: clean_kernel::FVarId,
    alts: &[SurfaceInductionAlt],
) -> Result<bool, TacticError> {
    if let Some(result) = super::cases_index_constraints::try_cases(state, hyp_fvar, alts) {
        return result.map(|_| true);
    }
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let (hyp_idx, hyp_decl) = goal
        .local_ctx
        .iter()
        .enumerate()
        .find(|(_, d)| d.fvar == hyp_fvar)
        .ok_or_else(|| TacticError::HypothesisNotFound(format!("{hyp_fvar:?}")))?;
    let hyp_ty = state.metas.instantiate(&hyp_decl.ty);
    cases_core(
        state,
        goal,
        Some(hyp_idx),
        Some(hyp_fvar),
        Expr::fvar(hyp_fvar),
        hyp_ty,
    )?;
    Ok(false)
}

/// Case split on an arbitrary scrutinee expression.
///
/// This supports Lean syntax like `cases (Nat.decEq m n) with ...`, where the
/// scrutinee is not already bound as a local hypothesis. The target does not
/// depend on a named scrutinee local, so branch targets are preserved while
/// constructor fields (for example `h : m = n`) are added to each branch.
/// Equality expressions first become checked local proofs so equation
/// elimination rewrites dependent hypotheses as well as the target.
pub(super) fn cases_expr(
    state: &mut ProofState,
    scrutinee: Expr,
    alts: &[SurfaceInductionAlt],
) -> Result<bool, TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let hyp_ty = state.infer_type(&goal, &scrutinee)?;
    let hyp_ty_whnf = state.whnf(&goal, &hyp_ty);
    if let Some(result) =
        super::cases_index_constraints::try_cases_expr(state, &goal, &scrutinee, &hyp_ty_whnf, alts)
    {
        return result.map(|_| true);
    }
    if matches!(hyp_ty_whnf.get_app_fn().kind(), ExprKind::Const(name, _) if name == &Name::from_string("Eq"))
    {
        let name = fresh_hyp_name(&goal.local_ctx, &SurfaceName::generated_path("cases_eq"));
        super::forward::have_(state, &name, hyp_ty, Some(scrutinee))?;
        let local = state
            .current_goal()
            .and_then(|g| g.local_ctx.last())
            .map(|d| d.fvar)
            .ok_or(TacticError::NoGoals)?;
        return super::cases_unify_eqs::cases_eq(state, local).map(|_| false);
    }
    cases_core(state, goal, None, None, scrutinee, hyp_ty)?;
    Ok(false)
}

fn cases_core(
    state: &mut ProofState,
    goal: Goal,
    hyp_idx: Option<usize>,
    hyp_fvar: Option<clean_kernel::FVarId>,
    scrutinee: Expr,
    hyp_ty: Expr,
) -> TacticResult {
    let mut goal = goal;
    let mut hyp_idx = hyp_idx;
    let hyp_ty_whnf = state.whnf(&goal, &hyp_ty);

    let head = hyp_ty_whnf.get_app_fn().clone();
    let args: Vec<Expr> = hyp_ty_whnf.get_app_args().into_iter().cloned().collect();

    let ind_name = match head.kind() {
        ExprKind::Const(name, _) => name.clone(),
        _ => {
            return Err(TacticError::GoalMismatch(format!(
                "cases: scrutinee has type '{}' which is not an inductive type",
                crate::error_render::term(&hyp_ty_whnf)
            )));
        }
    };

    // `cases h` on an equality hypothesis runs Lean's equation unification
    // (`unifyEqs?`): substitute a local side, clear a definitionally trivial
    // equation, split two constructor applications by `noConfusion` and
    // recurse on the field equations (G82). It rewrites the whole context, not
    // only the target, so it is not the generic eliminator path below. This
    // only applies when `cases` was given a genuine local hypothesis (`cases
    // h`), not the `cases_expr` scrutinee form. An equation it cannot solve is
    // refused with Lean's "dependent elimination failed" (or by name, for the
    // steps not implemented) — fail-closed, never a silent over-accept.
    if ind_name == Name::from_string("Eq") {
        if let (Some(hyp_idx), Some(hyp_fvar)) = (hyp_idx, hyp_fvar) {
            if goal
                .local_ctx
                .get(hyp_idx)
                .is_some_and(|d| d.fvar == hyp_fvar)
            {
                return super::cases_unify_eqs::cases_eq(state, hyp_fvar);
            }
        }
    }

    // HEq mirrors the `Eq` route above (and for the same reason): its casesOn
    // is an INDEXED eliminator whose motive has arity num_indices+1. The
    // generic path below can build that motive since RC-S (`indexed_family`),
    // but this shortcut keeps `subst`'s capabilities — a context-wide
    // rewrite and a non-fvar left side — and is kept for them. Route
    // `cases h` on `h : HEq x y` through `HEq.ndrec` directly, exactly as
    // `subst` uses `Eq.ndrec`:
    //
    //   HEq.ndrec.{v,u} {α} {a} {motive : {β : Sort u} → β → Sort v}
    //                   (minor : motive a) {β} {b} (h : HEq a b) : motive b
    //
    // with `motive := fun {β} (z : β) => target[y := z]` and the surviving
    // goal `target[y := x]` (the `HEq.refl` branch). Requires the RIGHT side
    // to be an eliminable local fvar; otherwise fall through to the generic
    // (index-aware) path. The assembled term is kernel-rechecked at
    // `close_goal`, so a mis-built motive cannot over-accept.
    // heqToEq (Lean's `heqToEq`): when a heterogeneous equality's two TYPES
    // are definitionally equal, `HEq a b` IS `a = b` — convert with
    // `eq_of_heq` and unify that equation exactly as the `Eq` arm above does
    // (substitution, or `noConfusion` on two constructor applications).
    // Strictly more capable than the `HEq.ndrec` route below for that shape:
    // `subst` rewrites the hypothesis through the whole context, so dependent
    // hypotheses need no generalization, and it also handles a NON-fvar type
    // index (`HEq f g` with `f g : α → γ`) that the ndrec route cannot.
    if ind_name == Name::from_string("HEq") && args.len() == 4 {
        let (alpha, a_val, beta, b_val) = (
            args[0].clone(),
            args[1].clone(),
            args[2].clone(),
            args[3].clone(),
        );
        if let Some(hyp_fvar) = hyp_fvar {
            if state.is_def_eq(&goal, &alpha, &beta) {
                let u_level = match head.kind() {
                    ExprKind::Const(_, lvls) if !lvls.is_empty() => lvls[0].clone(),
                    _ => Level::zero(),
                };
                let mut eq_proof =
                    Expr::const_(Name::from_string("eq_of_heq"), vec![u_level.clone()]);
                eq_proof = Expr::app(eq_proof, alpha.clone());
                eq_proof = Expr::app(eq_proof, a_val.clone());
                eq_proof = Expr::app(eq_proof, b_val.clone());
                eq_proof = Expr::app(eq_proof, Expr::fvar(hyp_fvar));

                let mut eq_ty = Expr::const_(Name::from_string("Eq"), vec![u_level]);
                eq_ty = Expr::app(eq_ty, alpha);
                eq_ty = Expr::app(eq_ty, a_val);
                eq_ty = Expr::app(eq_ty, b_val);

                let base = goal
                    .local_ctx
                    .iter()
                    .find(|d| d.fvar == hyp_fvar)
                    .map_or_else(|| SurfaceName::generated_path("heq"), |d| d.name.clone());
                let eq_hyp_name = super::pattern::names::generated_suffix(&base, "_eq");
                super::forward::have_(state, &eq_hyp_name, eq_ty, Some(eq_proof))?;
                let eq_fvar = state
                    .current_goal()
                    .and_then(|g| g.local_ctx.last())
                    .map(|d| d.fvar)
                    .ok_or(TacticError::NoGoals)?;
                return super::cases_unify_eqs::cases_eq(state, eq_fvar);
            }
        }
    }

    if ind_name == Name::from_string("HEq") {
        if let (Some(hyp_fvar), Some(heq_args)) = (hyp_fvar, Some(&args)) {
            if heq_args.len() == 4 {
                let (alpha, a_val, beta, b_val) = (
                    heq_args[0].clone(),
                    heq_args[1].clone(),
                    heq_args[2].clone(),
                    heq_args[3].clone(),
                );
                if let (ExprKind::FVar(b_fvar), ExprKind::FVar(beta_fvar)) =
                    (b_val.kind(), beta.kind())
                {
                    // generalizeIndices, the `revert` half. A hypothesis whose
                    // type mentions an eliminated INDEX cannot survive the
                    // elimination in place — the eliminator abstracts that
                    // index in its motive — so it must be a Pi binder of the
                    // TARGET when the eliminator is applied, and be
                    // re-introduced per branch.
                    //
                    // Do it by reverting through the shipped machinery rather
                    // than folding a private "reverted target": four earlier
                    // attempts built the telescope only for the motive while
                    // `goal.target` stayed bare, so `close_goal_assembled`'s
                    // def-eq compared `Pi` against `App` at the ROOT and
                    // failed every time. `revert` replaces the goal, so after
                    // it the assembly below is correct with no changes at all
                    // — motive, branch target, branch context and the def-eq
                    // check then all derive from the same target. This is the
                    // revert/eliminate/re-intro pair `induction … generalizing`
                    // already ships (builtins_phase3d_intro.rs).
                    let dep_fvars: Vec<_> = goal
                        .local_ctx
                        .iter()
                        .filter(|d| d.fvar != hyp_fvar && d.fvar != *b_fvar && d.fvar != *beta_fvar)
                        .filter(|d| {
                            let fvars = crate::tactic::hypothesis::collect_fvars(&d.ty);
                            fvars.contains(b_fvar) || fvars.contains(beta_fvar)
                        })
                        .map(|d| d.fvar)
                        .collect();
                    let mut reverted = Vec::new();
                    for fvar in &dep_fvars {
                        // Already pulled in as a transitive dependent of an
                        // earlier revert.
                        if reverted.iter().any(|(old, _)| old == fvar) {
                            continue;
                        }
                        reverted.extend(
                            crate::tactic::specialize_generalize::revert_fvar_with_deps(
                                state, *fvar,
                            )?,
                        );
                    }
                    let reverted: Vec<_> = reverted.into_iter().map(|(_, name)| name).collect();
                    // Re-read: `revert` replaced the goal.
                    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                    // `HEq.{u}` carries α's universe on its own head; the
                    // motive's universe is the goal's, which for every case in
                    // this class is `Prop` (the goal is a proposition). Level
                    // mismatches fail closed at the kernel re-check.
                    let u_level = match head.kind() {
                        ExprKind::Const(_, lvls) if !lvls.is_empty() => lvls[0].clone(),
                        _ => Level::zero(),
                    };
                    let v_level = Level::zero();

                    // A hypothesis whose type mentions the eliminated index
                    // (`h₁ : HEq f g` with `g : β → γ` in Mathlib's congr_heq)
                    // must be generalized into the goal and re-introduced per
                    // branch — Lean's `generalizeIndices`. Not implemented:
                    // fail CLOSED with the reason rather than assemble a term
                    // the kernel will reject with an opaque mismatch.
                    let has_dependents = goal.local_ctx.iter().any(|d| {
                        d.fvar != hyp_fvar && d.fvar != *b_fvar && d.fvar != *beta_fvar && {
                            let fvars = crate::tactic::hypothesis::collect_fvars(&d.ty);
                            fvars.contains(b_fvar) || fvars.contains(beta_fvar)
                        }
                    });
                    if has_dependents {
                        return Err(TacticError::GoalMismatch(
                            "cases on `HEq`: a hypothesis depends on the eliminated index; \
                             generalizing such hypotheses (Lean's generalizeIndices) is not \
                             implemented — revert them manually first"
                                .to_string(),
                        ));
                    }

                    // motive := fun {β : Sort u} (z : β) => target[b := z][β := β]
                    let target_abs = goal.target.clone().abstract_fvar(*b_fvar);
                    let inner = Expr::lam(BinderInfo::Default, beta.clone(), target_abs);
                    let motive = Expr::lam(
                        BinderInfo::Implicit,
                        Expr::sort(u_level.clone()),
                        inner.abstract_fvar(*beta_fvar),
                    );

                    // Surviving goal: reverted target with (β, b) specialized
                    // to (α, a); the reverted dependents come back as its
                    // leading Pi binders, so they leave the context too.
                    // Surviving goal: target with (β, b) specialized to (α, a).
                    let branch_target = goal
                        .target
                        .subst_fvar(*b_fvar, &a_val)
                        .subst_fvar(*beta_fvar, &alpha);
                    let branch_ctx: Vec<_> = goal
                        .local_ctx
                        .iter()
                        .filter(|d| d.fvar != hyp_fvar && d.fvar != *b_fvar && d.fvar != *beta_fvar)
                        .cloned()
                        .collect();
                    let branch_meta =
                        state.fresh_meta_in_context(branch_target.clone(), &branch_ctx);
                    let minor = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(branch_meta)));

                    let mut proof =
                        Expr::const_(Name::from_string("HEq.ndrec"), vec![v_level, u_level]);
                    proof = Expr::app(proof, alpha);
                    proof = Expr::app(proof, a_val);
                    proof = Expr::app(proof, motive);
                    proof = Expr::app(proof, minor);
                    proof = Expr::app(proof, beta);
                    proof = Expr::app(proof, b_val);
                    proof = Expr::app(proof, Expr::fvar(hyp_fvar));

                    state.close_goal_assembled(&goal, proof)?;
                    state.goals.push_back(Goal {
                        case_binders: vec![],
                        meta_id: branch_meta,
                        target: branch_target,
                        local_ctx: branch_ctx,
                        tag: Some(SurfaceName::generated_path("refl")),
                    });
                    // …and the `intro` half: re-introduce in reverse revert
                    // order, which is the Pi-binder order of the reverted
                    // target. `intro` mints FRESH tactic FVars from the goal's
                    // binder base — reusing the original elaborator ids is what
                    // sank an earlier attempt (they sit below `fvar_base`, so
                    // `close_fvars` leaves the binders vacuous and
                    // `build_local_ctx` discards the branch decls).
                    for name in reverted.iter().rev() {
                        super::target_equation::intro_shadowing(state, name)?;
                    }
                    return Ok(());
                }
            }
        }
    }

    let ind_info = state
        .env
        .get_inductive(&ind_name)
        .ok_or_else(|| {
            TacticError::GoalMismatch(format!("cases: '{ind_name}' is not an inductive type"))
        })?
        .clone();

    let levels = match head.kind() {
        ExprKind::Const(_, lvls) => lvls.to_vec(),
        _ => vec![],
    };

    // Class (80): a hypothesis that mentions the major premise is reverted
    // before the elimination and re-introduced after each case's fields, as
    // Lean's `cases` does (`super::major_dependents`).
    let reverted = match hyp_fvar {
        Some(major) => {
            let dependents = super::major_dependents::dependents_of(state, &goal, &[major]);
            let reverted = super::major_dependents::revert_fvars(state, &dependents)?;
            if !reverted.is_empty() {
                goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
                hyp_idx = goal.local_ctx.iter().position(|d| d.fvar == major);
            }
            reverted
        }
        None => Vec::new(),
    };

    // Part of #2232: use casesOn instead of rec. The cases tactic only wraps
    // constructor field lambdas (no IH), which matches casesOn's arity. Using
    // T.rec caused arity mismatch for recursive constructors (e.g., Nat.succ
    // expects 2 args in rec but cases only produced 1-arg lambda).
    //
    // Eliminator lookup is two-tier, mirroring `elab_match` (helpers.rs
    // `eliminator_levels`, nested_ctor.rs): a NATIVE Clean inductive registers
    // `T.casesOn` in the kernel recursor registry (`build_cases_on`), but Lean 4
    // itself ships `T.casesOn` as an auxiliary *definition*
    // (Lean/Meta/Constructions/CasesOn.lean) — only `T.rec` is a Recursor kernel
    // object — so an `.olean`-imported inductive arrives with `get_recursor`
    // missing while `get_const` finds the definitional constant. The tactic only
    // needs the eliminator's universe arity from the lookup: the application
    // layout it assembles below (params → motive → major → minors) is the same
    // `MajorAfterMotive` convention in both worlds, and the constant's declared
    // `level_params` is authoritative for the arity either way. The assembled
    // proof is still kernel-rechecked (`close_goal` / `verify_tactic_proof` →
    // `add_decl`), so a mis-assembled application fails closed downstream —
    // this fallback cannot over-accept.
    let rec_name = ind_name.clone().str("casesOn");
    let rec_level_count = match state.env.get_recursor(&rec_name) {
        Some(rec_info) => rec_info.level_params.len(),
        None => state
            .env
            .get_const(&rec_name)
            .ok_or_else(|| TacticError::EnvironmentMissing {
                constant: rec_name.to_string(),
            })?
            .level_params
            .len(),
    };

    let num_ctors = ind_info.constructor_names.len();
    if num_ctors == 0 {
        // An empty family can still be indexed (`Fin 0`-shaped absurdities), so
        // the motive and the eliminator spine go through the same index-aware
        // path as the general case below. With a bare-term scrutinee there is no
        // hypothesis fvar to abstract and the motive is simply constant in its
        // last binder — exactly what this branch built before.
        let FamilyMotive { motive, index_args } = build_family_motive(
            state,
            &head,
            &ind_info,
            &args,
            &hyp_ty,
            hyp_fvar,
            &goal.target,
        )?;
        let rec_levels = recursor_levels(state, &goal, &levels, rec_level_count);
        let params = &args[..args.len().min(ind_info.num_params as usize)];
        // `casesOn` layout: indices, then the major premise, then the minors
        // (here only those of the other members of a mutual or nested block).
        let proof = super::cases_on_spine::assemble_cases_on(
            state,
            &ind_info,
            super::cases_on_spine::CasesOnArgs {
                rec_name: &rec_name,
                rec_levels,
                params,
                motive,
                index_args: &index_args,
                major: scrutinee,
                minors: Vec::new(),
            },
        )?;

        // Part of #2154 Tier 2 Wave 1: 0-ctor case, no metas — migrated to checked close_goal.
        state.close_goal(&goal, proof)?;
        return Ok(());
    }

    // #close_fvars (`cases <term> with`, non-fvar scrutinee): the `motive_fvar`
    // below is a TEMPORARY sentinel — it is abstracted straight into the motive
    // lambda and never appears as a binder in the assembled proof term. If we let
    // it permanently consume an FVar id, the per-branch field FVars start one id
    // too high relative to the minor-premise binder depth they occupy: for `Or`
    // (constructors with one field each), the field lands at binder depth 1 but
    // gets id `base + 1`, so `close_fvars`' `(n - base) < depth` check fails
    // (`1 < 1` is false) → the field FVar is left unconverted (an ID-to-binder
    // gap → the close_fvars panic on a valid `cases Classical.em p with …`).
    // `branch_fvar_base` below numbers the field FVars from the goal's own
    // context (`goal_fvar_base`), which is independent of the global counter the
    // sentinel borrows, so the sentinel's id no longer needs snapshotting.
    let motive_fvar = if hyp_fvar.is_none() {
        Some(state.fresh_fvar())
    } else {
        None
    };
    let motive_body = if let Some(motive_fvar) = motive_fvar {
        replace_cases_scrutinee_occurrences(
            state,
            &goal,
            &goal.target,
            &scrutinee,
            &hyp_ty,
            &Expr::fvar(motive_fvar),
        )
    } else {
        goal.target.clone()
    };
    // The free variable that stands for the major premise inside the motive
    // body: the real hypothesis for `cases h`, the sentinel above for
    // `cases <term>`. One of the two is always present — `motive_fvar` is
    // allocated exactly when `hyp_fvar` is `None`.
    let major_fvar = match (hyp_fvar, motive_fvar) {
        (Some(f), _) | (None, Some(f)) => f,
        (None, None) => {
            return Err(TacticError::GoalMismatch(
                "cases: no free variable available to abstract the major premise".to_string(),
            ))
        }
    };
    let FamilyMotive { motive, index_args } = build_family_motive(
        state,
        &head,
        &ind_info,
        &args,
        &hyp_ty,
        Some(major_fvar),
        &motive_body,
    )?;

    let mut case_metas = Vec::with_capacity(num_ctors);

    // #3528: Save next_fvar before the branches loop and reset before each
    // branch so each branch's field FVars start from the same base. This is
    // safe because each branch gets its own goal (with its own local_ctx)
    // and its own proof lambda — FVar IDs never need to be globally unique
    // across sibling branches, only within a single goal/lambda chain.
    //
    // Without this reset, branch N+1's first field FVar has ID
    // `fvar_before_branches + (sum of field counts in branches 0..N)`, but
    // it lands at the same binder depth (1) inside branch N+1's lambda.
    // close_fvars would then fail its (n - base) < depth check, leading to
    // a panic in debug and "Declaration contains free variables" in release.
    //
    // Note: `eval_induction_alts` (the caller) additionally resets next_fvar
    // to `max_fvar_in_goal_ctx + 1` before running each branch's tactic
    // sequence, so nested cases work correctly at deeper binder depths.
    //
    // Number the branch field FVars from the GOAL's own context
    // (`goal_fvar_base` = one past the highest tactic FVar bound in this goal,
    // floored at `fvar_base`), NOT the monotonic global `next_fvar`. This is the
    // exact depth-correct base `close_fvars` needs — a field at minor-premise
    // binder depth `d` must get id `base + (d-1)` — and it is a pure function of
    // this goal's context, so SIBLING branch goals (e.g. the two `Iff.intro`
    // subgoals from a `constructor`/`split`, each proved with its own
    // `intro; cases` chain) get the SAME field ids at the SAME depths. Using the
    // global counter instead let an earlier sibling's advanced `next_fvar` leak
    // in, so the second sibling's field FVars started too high and `close_fvars`'
    // `(n - base) < depth` check failed → a residual FVar → `closed_proof`
    // returns None → `ProofNotProduced` (e.g. `by tauto` on `(a∧b) ↔ (a∧b)`,
    // whose Iff branch proves each side via `intro h; cases h`). This is the same
    // fix `intro` carries (#2533); the two now share `goal_fvar_base`.
    // `goal_binder_base`: identical to `goal_fvar_base` unless the goal's
    // context was narrowed by `clear`, in which case the context alone would
    // hand back an id still bound by a live `lambda` (capture).
    let branch_fvar_base = state.goal_binder_base(&goal);
    let mut branch_fvar_max = branch_fvar_base;

    for ctor_name in &ind_info.constructor_names {
        // Reset next_fvar so this branch allocates from the same base as
        // branch 0. Safe because field FVars only appear in this branch's
        // own new_ctx and its own proof lambda; they never cross branches.
        state.next_fvar = branch_fvar_base;

        let ctor_info = state
            .env
            .get_constructor(ctor_name)
            .ok_or_else(|| TacticError::EnvironmentMissing {
                constant: ctor_name.to_string(),
            })?
            .clone();

        let mut new_ctx = goal.local_ctx.clone();
        if let Some(hyp_idx) = hyp_idx {
            new_ctx.remove(hyp_idx);
        }

        // The constructor's stored type carries the inductive's OWN universe
        // parameters (e.g. `List.cons : {α : Type u} → α → List α → List α` keeps
        // `List.{u}` in its recursive tail field). Substituting `α := Nat` alone
        // leaves that `List.{u}` behind, so the assembled `casesOn` minor-premise
        // lambda would bind `List.{u} Nat` while the kernel expects `List.{0} Nat`
        // — the leaked-universe rejection. Instantiate the constructor's level
        // params with the major premise's ACTUAL levels first (the same
        // `instantiate_level_params_direct` the kernel uses when it applies a
        // constructor), so field types are universe-correct before we walk them.
        // Length-guarded: on any params/levels mismatch we leave the type as-is
        // and let the kernel re-check fail closed rather than mis-substitute.
        let ctor_ty_src = if ctor_info.level_params.len() == levels.len() {
            ctor_info
                .type_
                .instantiate_level_params_direct(&ctor_info.level_params, &levels)
        } else {
            ctor_info.type_.clone()
        };
        let mut ctor_ty = ctor_ty_src;
        let mut field_fvars = Vec::new();
        let mut param_idx = 0;

        for _ in 0..ctor_info.num_params {
            if let ExprKind::Pi(_, _, codomain) = ctor_ty.kind() {
                if param_idx < args.len() {
                    ctor_ty = codomain.instantiate(&args[param_idx]);
                } else {
                    ctor_ty = codomain.instantiate(&Expr::from_kind(ExprKind::Sort(Level::zero())));
                }
                param_idx += 1;
            }
        }

        let mut field_idx = 0;
        while let ExprKind::Pi(bi, domain, codomain) = ctor_ty.clone().kind() {
            let ctor_short = SurfaceName::from_name(ctor_name.clone()).last_component();
            let field_base = super::case_field_names::generated_case_field_name(
                &ctor_short,
                field_idx as u64,
                super::case_field_names::CaseFieldKind::Field,
            );
            let field_name = fresh_hyp_name(&new_ctx, &field_base);
            let field_fvar = state.fresh_fvar();

            let field_decl = LocalDecl {
                binder_info: *bi,
                fvar: field_fvar,
                name: field_name,
                ty: domain.as_ref().clone(),
                value: None,
            };
            new_ctx.push(field_decl);
            field_fvars.push(field_fvar);

            ctor_ty = codomain.instantiate(&Expr::fvar(field_fvar));
            field_idx += 1;

            if field_idx >= ctor_info.num_fields as usize {
                break;
            }
        }

        // Track the max next_fvar across branches so post-loop state reflects
        // the largest FVar ID reserved by any branch (prevents collisions with
        // any subsequent FVar allocations in this ProofState).
        branch_fvar_max = branch_fvar_max.max(state.next_fvar);

        let mut ctor_app = Expr::const_(ctor_name.clone(), levels.clone());
        for arg in args.iter().take(ind_info.num_params as usize) {
            ctor_app = Expr::app(ctor_app, arg.clone());
        }
        for fvar in &field_fvars {
            ctor_app = Expr::app(ctor_app, Expr::fvar(*fvar));
        }

        let new_target = if index_args.is_empty() {
            // Non-indexed family: unchanged from before indices were handled.
            if let Some(hyp_fvar) = hyp_fvar {
                goal.target.subst_fvar(hyp_fvar, &ctor_app)
            } else {
                replace_cases_scrutinee_occurrences(
                    state,
                    &goal,
                    &goal.target,
                    &scrutinee,
                    &hyp_ty,
                    &ctor_app,
                )
            }
        } else {
            // Indexed family: this branch's goal is the eliminator's own minor
            // premise, `motive ctor_indices… (C params… fields…)`. Computing it
            // by beta-applying the SAME motive that goes into the proof term is
            // what makes `Nat.le.refl` specialise the goal at `m := n` and
            // `Nat.le.step` at `m := m' + 1` — substituting into the goal
            // directly would leave the old index in place.
            let ctor_indices = applied_index_args(&ind_info, &ctor_ty).ok_or_else(|| {
                TacticError::GoalMismatch(format!(
                    "cases: constructor '{ctor_name}' of indexed family '{ind_name}' does not \
                     conclude in an applied '{ind_name}' after its fields"
                ))
            })?;
            let mut applied = ctor_indices;
            applied.push(ctor_app);
            beta_apply(&motive, &applied)
        };
        let new_target = state.metas.instantiate(&new_target);

        // Lean names each case goal `tag ++ ctorName` after the goal it splits
        // (`Lean/Meta/Tactic/Induction.lean`, `mkFreshExprSyntheticOpaqueMVar d
        // (tag ++ n)`), so `cases a <;> cases b` yields `some.cons`, which
        // `case some.cons =>` selects. A goal with no tag contributes nothing.
        let ctor_short = SurfaceName::from_name(ctor_name.clone()).last_component();
        let ctor_short_tag = match &goal.tag {
            Some(parent) if !parent.is_anonymous() => parent.append(&ctor_short),
            _ => ctor_short,
        };
        // The case's scope keeps the eliminated major (`fresh_case_meta`): its
        // proof is still under that binder.
        let case_meta = state.fresh_case_meta(new_target.clone(), &goal, &new_ctx);
        case_metas.push((case_meta, new_ctx, new_target, field_fvars, ctor_short_tag));
    }

    // Restore next_fvar to the max used across all branches so future
    // allocations (e.g., tactics run on the per-branch goals later) start
    // from a fresh ID that doesn't collide with any branch's field FVars.
    state.next_fvar = branch_fvar_max;

    let rec_levels = recursor_levels(state, &goal, &levels, rec_level_count);

    // Lean-faithful casesOn order: the family's INDICES come first, then the
    // major premise (scrutinee), then the minor premises. Omitting the indices
    // — as this did before RC-S — slid the major premise into the first index
    // slot and every later argument one position left.
    let mut minors = Vec::with_capacity(case_metas.len());
    for (case_meta, new_ctx, _target, field_fvars, _) in &case_metas {
        let case_body = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(*case_meta)));

        let mut case_proof = case_body;
        for fvar in field_fvars.iter().rev() {
            let fvar_ty = new_ctx.iter().find(|d| d.fvar == *fvar).map_or_else(
                || Expr::from_kind(ExprKind::Sort(Level::zero())),
                |d| d.ty.clone(),
            );
            case_proof = Expr::lam(
                BinderInfo::Default,
                fvar_ty,
                case_proof.abstract_fvar(*fvar),
            );
        }

        minors.push(case_proof);
    }
    let params = &args[..args.len().min(ind_info.num_params as usize)];
    // A mutual or nested family's kernel `casesOn` also takes the other
    // members' motives and minors (`super::cases_on_spine`, class (92) B5).
    let proof = super::cases_on_spine::assemble_cases_on(
        state,
        &ind_info,
        super::cases_on_spine::CasesOnArgs {
            rec_name: &rec_name,
            rec_levels,
            params,
            motive,
            index_args: &index_args,
            major: scrutinee,
            minors,
        },
    )?;

    // The minor-premise arguments are open subgoal metavariables whose stored
    // targets are the *constructor-specialized* goals (e.g. `Eq (succ k) (succ k)`),
    // i.e. `motive` already beta-reduced and `subst_fvar`-applied at the
    // constructor. casesOn's strict App-arg check, by contrast, expects each
    // minor to inhabit the *unreduced* dependent application `motive (ctor …)`
    // (a beta-redex `(fun x => …) (ctor …)`). When the motive is dependent
    // (the goal mentions the scrutinee, e.g. `n = n`), the strict
    // `infer_type_strict` path used by `close_goal` rejects this genuinely-valid
    // term because it does not reduce the motive redex on the expected side.
    //
    // `close_goal_assembled` is the variant designed for exactly this shape
    // (recursor/eliminator spine with open-meta minor premises): it infers the
    // recursor application *leniently* (App-args not re-checked) but still
    // verifies the result type is def-eq to the goal target, and defers the
    // strict per-argument check to `verify_tactic_proof` — the single
    // enforcement point — once every minor-premise meta has been solved by its
    // branch tactics and the fully-instantiated term can be kernel-rechecked.
    // This mirrors `induction`, which already uses `close_goal_assembled`
    // (induction.rs) for its recursor proof. Soundness is unchanged: the final
    // assembled proof is strictly re-checked (and `add_decl`-rechecked), so a
    // wrong/weaker motive or mis-typed branch fails downstream, never silently.
    //
    // Part of #2154 Tier 2 Wave 2: structural match with meta case branches.
    state.close_goal_assembled(&goal, proof)?;

    let case_meta_ids: Vec<_> = case_metas.iter().map(|case| case.0).collect();
    for (case_meta, new_ctx, new_target, field_fvars, ctor_tag) in case_metas {
        let new_goal = Goal {
            case_binders: field_fvars,
            meta_id: case_meta,
            target: new_target,
            local_ctx: new_ctx,
            tag: Some(ctor_tag),
        };
        state.goals.push_back(new_goal);
    }

    super::major_dependents::reintroduce(state, &case_meta_ids, &reverted)
}

fn replace_cases_scrutinee_occurrences(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    scrutinee: &Expr,
    scrutinee_ty: &Expr,
    replacement: &Expr,
) -> Expr {
    if expr == scrutinee || matches_decidable_scrutinee_type(state, goal, expr, scrutinee_ty) {
        return replacement.clone();
    }

    match expr.kind() {
        ExprKind::App(f, a) => Expr::app(
            replace_cases_scrutinee_occurrences(
                state,
                goal,
                f,
                scrutinee,
                scrutinee_ty,
                replacement,
            ),
            replace_cases_scrutinee_occurrences(
                state,
                goal,
                a,
                scrutinee,
                scrutinee_ty,
                replacement,
            ),
        ),
        ExprKind::Lam(bi, ty, body) => Expr::lam(
            *bi,
            replace_cases_scrutinee_occurrences(
                state,
                goal,
                ty,
                scrutinee,
                scrutinee_ty,
                replacement,
            ),
            replace_cases_scrutinee_occurrences(
                state,
                goal,
                body,
                scrutinee,
                scrutinee_ty,
                replacement,
            ),
        ),
        ExprKind::Pi(bi, ty, body) => Expr::pi(
            *bi,
            replace_cases_scrutinee_occurrences(
                state,
                goal,
                ty,
                scrutinee,
                scrutinee_ty,
                replacement,
            ),
            replace_cases_scrutinee_occurrences(
                state,
                goal,
                body,
                scrutinee,
                scrutinee_ty,
                replacement,
            ),
        ),
        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            replace_cases_scrutinee_occurrences(
                state,
                goal,
                ty,
                scrutinee,
                scrutinee_ty,
                replacement,
            ),
            replace_cases_scrutinee_occurrences(
                state,
                goal,
                val,
                scrutinee,
                scrutinee_ty,
                replacement,
            ),
            replace_cases_scrutinee_occurrences(
                state,
                goal,
                body,
                scrutinee,
                scrutinee_ty,
                replacement,
            ),
            *non_dep,
        ),
        ExprKind::Proj(name, idx, inner) => Expr::proj(
            name.clone(),
            *idx,
            replace_cases_scrutinee_occurrences(
                state,
                goal,
                inner,
                scrutinee,
                scrutinee_ty,
                replacement,
            ),
        ),
        ExprKind::MData(mdata, inner) => Expr::mdata(
            mdata.clone(),
            replace_cases_scrutinee_occurrences(
                state,
                goal,
                inner,
                scrutinee,
                scrutinee_ty,
                replacement,
            ),
        ),
        ExprKind::Squash(inner) => Expr::from_kind(ExprKind::Squash(std::sync::Arc::new(
            replace_cases_scrutinee_occurrences(
                state,
                goal,
                inner,
                scrutinee,
                scrutinee_ty,
                replacement,
            ),
        ))),
        _ => expr.clone(),
    }
}

fn matches_decidable_scrutinee_type(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    scrutinee_ty: &Expr,
) -> bool {
    if !is_decidable_type(scrutinee_ty) {
        return false;
    }
    state
        .infer_type(goal, expr)
        .ok()
        .is_some_and(|expr_ty| state.is_def_eq(goal, &expr_ty, scrutinee_ty))
}

fn is_decidable_type(expr: &Expr) -> bool {
    matches!(
        expr.get_app_fn().kind(),
        ExprKind::Const(name, _) if *name == Name::from_string("Decidable")
    )
}
