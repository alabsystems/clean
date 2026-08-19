// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic for case analysis on inductive types (`cases`).
//!
//! The `induction` tactic has been split to `induction.rs` (#307).

use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::tauto::fresh_hyp_name;

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
pub fn cases(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let (hyp_idx, hyp_decl) = goal
        .local_ctx
        .iter()
        .enumerate()
        .find(|(_, d)| d.name == hyp_name)
        .ok_or_else(|| TacticError::UnknownIdent(hyp_name.to_string()))?;
    let hyp_fvar = hyp_decl.fvar;
    let hyp_ty = state.metas.instantiate(&hyp_decl.ty);

    cases_core(
        state,
        goal,
        Some(hyp_idx),
        Some(hyp_fvar),
        Expr::fvar(hyp_fvar),
        hyp_ty,
    )
}

/// Case split on an arbitrary scrutinee expression.
///
/// This supports Lean syntax like `cases (Nat.decEq m n) with ...`, where the
/// scrutinee is not already bound as a local hypothesis. The target does not
/// depend on a named scrutinee local, so branch targets are preserved while
/// constructor fields (for example `h : m = n`) are added to each branch.
pub fn cases_expr(state: &mut ProofState, scrutinee: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let hyp_ty = state.infer_type(&goal, &scrutinee)?;
    cases_core(state, goal, None, None, scrutinee, hyp_ty)
}

fn cases_core(
    state: &mut ProofState,
    goal: Goal,
    hyp_idx: Option<usize>,
    hyp_fvar: Option<clean_kernel::FVarId>,
    scrutinee: Expr,
    hyp_ty: Expr,
) -> TacticResult {
    let hyp_ty_whnf = state.whnf(&goal, &hyp_ty);

    let head = hyp_ty_whnf.get_app_fn().clone();
    let args: Vec<Expr> = hyp_ty_whnf.get_app_args().into_iter().cloned().collect();

    let ind_name = match head.kind() {
        ExprKind::Const(name, _) => name.clone(),
        _ => {
            return Err(TacticError::GoalMismatch(format!(
                "cases: scrutinee has type '{hyp_ty_whnf:?}' which is not an inductive type"
            )));
        }
    };

    // `cases h` on an equality hypothesis IS `subst` in Lean 4: `Eq` is a
    // special inductive whose single constructor `Eq.refl` moves an index, so
    // the generic N-constructor `casesOn`-motive construction below builds a
    // wrong motive/eliminator application (it leaks an unbound sentinel FVar
    // and leaves an unapplied Pi where a proof of the goal is required). Route
    // to the kernel-checked `subst` tactic instead — the exact machinery the
    // `subst` tactic and the `rcases … with rfl` pattern already use. This only
    // applies when `cases` was given a genuine local hypothesis (`cases h`),
    // not the `cases_expr` scrutinee form, and only when one side of the
    // equation is a local variable `subst` can eliminate. If it is not (e.g.
    // `h : 5 = 3`), `subst`'s error is surfaced verbatim — fail-closed, never a
    // panic and never a silent over-accept.
    if ind_name == Name::from_string("Eq") {
        if let (Some(hyp_idx), Some(hyp_fvar)) = (hyp_idx, hyp_fvar) {
            if let Some(hyp_name) = goal
                .local_ctx
                .get(hyp_idx)
                .filter(|d| d.fvar == hyp_fvar)
                .map(|d| d.name.clone())
            {
                return super::equality::subst(state, &hyp_name);
            }
        }
    }

    // HEq mirrors the `Eq` route above (and for the same reason): its casesOn
    // is an INDEXED eliminator whose motive has arity num_indices+1, a shape
    // the generic assembly below cannot build — and since `Eq` shortcuts to
    // `subst`, that generic path has never had a working indexed example.
    // Route `cases h` on `h : HEq x y` through `HEq.ndrec` directly, exactly
    // as `subst` uses `Eq.ndrec`:
    //
    //   HEq.ndrec.{v,u} {α} {a} {motive : {β : Sort u} → β → Sort v}
    //                   (minor : motive a) {β} {b} (h : HEq a b) : motive b
    //
    // with `motive := fun {β} (z : β) => target[y := z]` and the surviving
    // goal `target[y := x]` (the `HEq.refl` branch). Requires the RIGHT side
    // to be an eliminable local fvar; otherwise fall through to the generic
    // path, which fails closed. The assembled term is kernel-rechecked at
    // `close_goal`, so a mis-built motive cannot over-accept.
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
                        meta_id: branch_meta,
                        target: branch_target,
                        local_ctx: branch_ctx,
                        tag: Some("refl".to_string()),
                    });
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
    let rec_name = Name::from_string(&format!("{ind_name}.casesOn"));
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

    let motive_body = goal.target.clone();
    let motive = Expr::lam(
        BinderInfo::Default,
        hyp_ty.clone(),
        if let Some(hyp_fvar) = hyp_fvar {
            motive_body.abstract_fvar(hyp_fvar)
        } else {
            motive_body
        },
    );

    let num_ctors = ind_info.constructor_names.len();
    if num_ctors == 0 {
        let rec_levels = recursor_levels(state, &goal, &levels, rec_level_count);
        let rec = Expr::const_(rec_name.clone(), rec_levels);

        let mut proof = rec;
        for arg in args.iter().take(ind_info.num_params as usize) {
            proof = Expr::app(proof, arg.clone());
        }
        proof = Expr::app(proof, motive.clone());
        proof = Expr::app(proof, scrutinee);

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
    let motive = Expr::lam(
        BinderInfo::Default,
        hyp_ty.clone(),
        if let Some(hyp_fvar) = hyp_fvar {
            motive_body.abstract_fvar(hyp_fvar)
        } else if let Some(motive_fvar) = motive_fvar {
            motive_body.abstract_fvar(motive_fvar)
        } else {
            motive_body
        },
    );

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
            let ctor_short_name = ctor_name.to_string();
            let ctor_short = ctor_short_name
                .rsplit('.')
                .next()
                .unwrap_or(&ctor_short_name);
            let field_name = fresh_hyp_name(&new_ctx, &format!("{ctor_short}_{field_idx}"));
            let field_fvar = state.fresh_fvar();

            let field_decl = LocalDecl {
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

            if !matches!(
                bi.info,
                BinderInfo::Default | BinderInfo::Implicit | BinderInfo::InstImplicit
            ) {
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

        let new_target = if let Some(hyp_fvar) = hyp_fvar {
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
        };
        let new_target = state.metas.instantiate(&new_target);

        let ctor_short_tag = ctor_name
            .to_string()
            .rsplit('.')
            .next()
            .unwrap_or(&ctor_name.to_string())
            .to_string();
        let case_meta = state.fresh_meta_in_context(new_target.clone(), &new_ctx);
        case_metas.push((case_meta, new_ctx, new_target, field_fvars, ctor_short_tag));
    }

    // Restore next_fvar to the max used across all branches so future
    // allocations (e.g., tactics run on the per-branch goals later) start
    // from a fresh ID that doesn't collide with any branch's field FVars.
    state.next_fvar = branch_fvar_max;

    let rec_levels = recursor_levels(state, &goal, &levels, rec_level_count);
    let rec = Expr::const_(rec_name, rec_levels);

    let mut proof = rec;
    for arg in args.iter().take(ind_info.num_params as usize) {
        proof = Expr::app(proof, arg.clone());
    }
    proof = Expr::app(proof, motive);
    // Lean-faithful casesOn order: the major premise (scrutinee) comes right
    // after the motive, before the minor premises.
    proof = Expr::app(proof, scrutinee);

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

        proof = Expr::app(proof, case_proof);
    }

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

    for (case_meta, new_ctx, new_target, _, ctor_tag) in case_metas {
        let new_goal = Goal {
            meta_id: case_meta,
            target: new_target,
            local_ctx: new_ctx,
            tag: Some(ctor_tag),
        };
        state.goals.push_back(new_goal);
    }

    Ok(())
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
