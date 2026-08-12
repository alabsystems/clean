// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Induction tactic for structural recursion over inductive types.
//!
//! Split from `proof_manipulation.rs` (#307). The `cases` tactic remains there.

use crate::unify::{MetaId, MetaState};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, ConstructorVal, Expr, ExprKind, FVarId, InductiveVal, Level, RecursorVal,
};

use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::proof_manipulation::recursor_levels;

/// Data for one induction case (one constructor branch).
///
/// Tracks the metavariable, local context, target, field free variables,
/// induction hypothesis free variables, and constructor tag for each branch
/// of a structural induction proof.
#[derive(Debug, Clone)]
pub(crate) struct InductionCase {
    /// Metavariable for this case branch.
    pub(crate) case_meta: MetaId,
    /// Local context for the case goal.
    pub(crate) new_ctx: Vec<LocalDecl>,
    /// Target type for this case.
    pub(crate) new_target: Expr,
    /// Free variables for constructor fields.
    pub(crate) field_fvars: Vec<FVarId>,
    /// Induction hypothesis free variables (None for non-recursive fields).
    pub(crate) ih_fvars: Vec<Option<FVarId>>,
    /// Short constructor name (e.g., "zero", "succ").
    pub(crate) ctor_tag: String,
}

/// Shared context for building an induction proof.
struct InductionCtx<'a> {
    goal: &'a Goal,
    ind_info: &'a InductiveVal,
    rec_info: &'a RecursorVal,
    rec_name: &'a Name,
    args: &'a [Expr],
    levels: &'a [Level],
    motive: &'a Expr,
    hyp_fvar: FVarId,
    hyp_idx: usize,
}

/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` refers to a hypothesis whose type is an inductive type
/// ENSURES: On Ok, the current goal is replaced by one goal per constructor (with induction hypotheses)
/// ENSURES: On Ok, recursive constructor goals include an induction hypothesis for each recursive argument
/// ENSURES: On Err(UnknownIdent), `hyp_name` is not in the local context
pub fn induction(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    induction_using(state, hyp_name, None)
}

/// Structural induction on `hyp_name`, optionally with a named recursor override.
///
/// `rec_override` is the fully-qualified eliminator name requested by an
/// `induction … using <elim>` clause. When `None`, the type's default
/// `<Ind>.rec` is used.
///
/// A `using` name that IS a registered kernel recursor takes this function's
/// recursor path. A name that is a constant but not a recursor — Lean's
/// `@[elab_as_elim]` eliminators, such as `Nat.strongRecOn` — is handed to
/// [`super::induction_elim::induction_using_eliminator`], which reads the
/// motive/target/alternative layout off the eliminator's own type. A name that
/// is neither still fails closed with [`TacticError::EnvironmentMissing`].
/// Either way the assembled proof term is re-checked by the kernel, so an
/// eliminator that does not fit the goal is rejected there rather than
/// silently accepted.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` refers to a hypothesis whose type is an inductive type
/// ENSURES: On Ok, the current goal is replaced by one goal per constructor
/// ENSURES: On Err(UnknownIdent), `hyp_name` is not in the local context
/// ENSURES: On Err(EnvironmentMissing), `rec_override` is not a registered recursor
pub fn induction_using(
    state: &mut ProofState,
    hyp_name: &str,
    rec_override: Option<&Name>,
) -> TacticResult {
    induction_using_alts(state, hyp_name, rec_override, &[])
}

/// [`induction_using`] plus the `with`-block alternative names, in source
/// order.
///
/// The names matter only on the custom-eliminator path: Clean's kernel `Pi`
/// stores no binder name, so an `@[elab_as_elim]` eliminator's alternative tags
/// cannot be read back from the environment and are taken positionally from the
/// `with` block instead. See [`super::induction_elim`]. The recursor path
/// ignores them — it tags cases with constructor names, as before.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: identical behaviour to [`induction_using`] whenever `rec_override`
///   names a registered kernel recursor (or is `None`)
pub fn induction_using_alts(
    state: &mut ProofState,
    hyp_name: &str,
    rec_override: Option<&Name>,
    alt_names: &[String],
) -> TacticResult {
    // Custom eliminator (`@[elab_as_elim]`): a `using` name that is a real
    // constant but NOT a kernel recursor. Dispatching here — and only here —
    // leaves the recursor path below byte-for-byte unchanged.
    if let Some(elim) = rec_override {
        if state.env.get_recursor(elim).is_none() && state.env.get_const(elim).is_some() {
            return super::induction_elim::induction_using_eliminator(
                state, hyp_name, elim, alt_names,
            );
        }
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let (hyp_idx, hyp_decl) = goal
        .local_ctx
        .iter()
        .enumerate()
        .find(|(_, d)| d.name == hyp_name)
        .ok_or_else(|| TacticError::UnknownIdent(hyp_name.to_string()))?;
    let hyp_fvar = hyp_decl.fvar;
    let hyp_ty = state.metas.instantiate(&hyp_decl.ty);

    let hyp_ty_whnf = state.whnf(&goal, &hyp_ty);
    let head = hyp_ty_whnf.get_app_fn().clone();
    let args: Vec<Expr> = hyp_ty_whnf.get_app_args().into_iter().cloned().collect();

    let ind_name = match head.kind() {
        ExprKind::Const(name, _) => name.clone(),
        _ => {
            return Err(TacticError::GoalMismatch(format!(
                "induction: hypothesis '{hyp_name}' has type '{hyp_ty_whnf:?}' which is not an inductive type"
            )));
        }
    };

    let ind_info = state
        .env
        .get_inductive(&ind_name)
        .ok_or_else(|| {
            TacticError::GoalMismatch(format!("induction: '{ind_name}' is not an inductive type"))
        })?
        .clone();
    let levels = match head.kind() {
        ExprKind::Const(_, lvls) => lvls.to_vec(),
        _ => vec![],
    };
    // `induction … using r` overrides the default `<Ind>.rec`. The override is
    // looked up like the default recursor and fails closed if it is not a
    // registered recursor; the kernel re-checks the assembled proof term so a
    // recursor with the wrong motive/arity is rejected rather than over-accepted.
    let default_rec_name = Name::from_string(&format!("{ind_name}.rec"));
    let rec_name = rec_override.cloned().unwrap_or(default_rec_name);
    let rec_info = state
        .env
        .get_recursor(&rec_name)
        .ok_or_else(|| TacticError::EnvironmentMissing {
            constant: rec_name.to_string(),
        })?
        .clone();
    let motive = Expr::lam(
        BinderInfo::Default,
        hyp_ty.clone(),
        goal.target.abstract_fvar(hyp_fvar),
    );

    // 0-ctor inductive: close directly with the recursor applied to the major premise.
    if ind_info.constructor_names.is_empty() {
        let rec_levels = recursor_levels(state, &goal, &levels, rec_info.level_params.len());
        let mut proof = Expr::const_(rec_name.clone(), rec_levels);
        for arg in args.iter().take(ind_info.num_params as usize) {
            proof = Expr::app(proof, arg.clone());
        }
        proof = Expr::app(proof, motive.clone());
        proof = Expr::app(proof, Expr::fvar(hyp_fvar));
        // Part of #2154 Tier 2 Wave 1: 0-ctor induction, no metas.
        state.close_goal(&goal, proof)?;
        return Ok(());
    }

    let ctx = InductionCtx {
        goal: &goal,
        ind_info: &ind_info,
        rec_info: &rec_info,
        rec_name: &rec_name,
        args: &args,
        levels: &levels,
        motive: &motive,
        hyp_fvar,
        hyp_idx,
    };
    let cases = build_induction_cases(state, &ctx)?;
    assemble_induction_proof(state, &ctx, cases)
}

/// Build one `InductionCase` per constructor, including field fvars and induction hypotheses.
///
/// REQUIRES: `ctx.ind_info.constructor_names` is non-empty
/// ENSURES: returned vec has one entry per constructor
fn build_induction_cases(
    state: &mut ProofState,
    ctx: &InductionCtx<'_>,
) -> Result<Vec<InductionCase>, TacticError> {
    let mut cases = Vec::with_capacity(ctx.ind_info.constructor_names.len());

    // Every constructor branch's field / IH FVars must be numbered from the SAME
    // base, exactly as `cases_core` numbers its branches (`proof_manipulation.rs`
    // — see the long note there). `close_fvars` accepts a tactic FVar inside the
    // assembled recursor term only when `id - binder_base < binder_depth` at its
    // occurrence (`close_fvars::assignment_scope_violation`), and each minor
    // premise's lambda chain re-starts that depth at zero. Letting the global
    // counter run on across constructors makes the SECOND field-binding branch's
    // first field `base + <fields bound so far>` at depth 1, so the proof is
    // rejected with "assignment violates its creation scope". That is why
    // `induction` failed on every inductive with two or more field-binding
    // constructors (`Or`, `Sum`, …) while `Nat` / `List` / `Option` — whose only
    // field-binding constructor is the last one — kept working. Branch FVars
    // never cross branches (each appears only in its own `new_ctx` and its own
    // minor-premise lambda), so resetting per branch is safe.
    //
    // The base is derived from THIS goal — one past its highest tactic FVar,
    // floored at `fvar_base` — not from the monotonic global `next_fvar`, so
    // sibling goals reaching `induction` with different counter values still get
    // depth-correct ids. `goal_binder_base` is `goal_fvar_base` widened to the
    // goal meta's creation scope: identical unless the context was narrowed by
    // `clear`, in which case the context alone would hand back an id still bound
    // by a live `lambda` (capture). `cases_core` uses the same base.
    let branch_fvar_base = state.goal_binder_base(ctx.goal);
    let mut branch_fvar_max = branch_fvar_base;

    for (ctor_idx, ctor_name) in ctx.ind_info.constructor_names.iter().enumerate() {
        // Reset so this branch allocates from the same base as branch 0.
        state.next_fvar = branch_fvar_base;

        let ctor_info = state
            .env
            .get_constructor(ctor_name)
            .ok_or_else(|| TacticError::EnvironmentMissing {
                constant: ctor_name.to_string(),
            })?
            .clone();
        let recursive_fields = if ctor_idx < ctx.rec_info.rules.len() {
            ctx.rec_info.rules[ctor_idx].recursive_fields.clone()
        } else {
            vec![false; ctor_info.num_fields as usize]
        };
        let mut new_ctx = ctx.goal.local_ctx.clone();
        new_ctx.remove(ctx.hyp_idx);
        let field_fvars = extract_ctor_fields(
            state,
            &ctor_info,
            &mut new_ctx,
            ctor_name,
            ctx.args,
            ctx.levels,
        );
        let ih_fvars = build_induction_hypotheses(
            state,
            ctx.goal,
            &mut new_ctx,
            ctor_name,
            &field_fvars,
            &recursive_fields,
            ctx.hyp_fvar,
        );
        // Track the largest id any branch reserved so the post-loop counter sits
        // past every branch's fields and IHs (mirrors `cases_core`).
        branch_fvar_max = branch_fvar_max.max(state.next_fvar);

        let mut ctor_app = Expr::const_(ctor_name.clone(), ctx.levels.to_vec());
        for arg in ctx.args.iter().take(ctx.ind_info.num_params as usize) {
            ctor_app = Expr::app(ctor_app, arg.clone());
        }
        for fvar in &field_fvars {
            ctor_app = Expr::app(ctor_app, Expr::fvar(*fvar));
        }
        let new_target = state
            .metas
            .instantiate(&ctx.goal.target.subst_fvar(ctx.hyp_fvar, &ctor_app));
        let ctor_short_tag = ctor_name
            .to_string()
            .rsplit('.')
            .next()
            .unwrap_or(&ctor_name.to_string())
            .to_string();
        let case_meta = state.fresh_meta_in_context(new_target.clone(), &new_ctx);
        cases.push(InductionCase {
            case_meta,
            new_ctx,
            new_target,
            field_fvars,
            ih_fvars,
            ctor_tag: ctor_short_tag,
        });
    }

    // Leave the counter past every branch's fields so tactics later run on the
    // case goals cannot collide with them (mirrors `cases_core`).
    state.next_fvar = branch_fvar_max;

    Ok(cases)
}

/// Extract constructor field fvars by walking the constructor type past parameters.
///
/// `ind_levels` are the ACTUAL universe levels of the major premise's inductive
/// head (e.g. `[0]` for `List Nat`). They are substituted for the constructor's
/// own level params before the type is walked, so a recursive field such as
/// `List α`'s tail keeps `List.{0}` rather than the leaked-in `List.{u}` — the
/// universe leak that made the assembled `List.rec` proof term fail the kernel
/// re-check. See the matching note in `cases_core` (`proof_manipulation.rs`).
///
/// REQUIRES: `ctor_info.type_` is a well-formed constructor type
/// ENSURES: returned fvars are added to `new_ctx`
/// ENSURES: returned vec length equals number of fields extracted
fn extract_ctor_fields(
    state: &mut ProofState,
    ctor_info: &ConstructorVal,
    new_ctx: &mut Vec<LocalDecl>,
    ctor_name: &Name,
    args: &[Expr],
    ind_levels: &[Level],
) -> Vec<FVarId> {
    // Length-guarded universe instantiation: on any params/levels mismatch keep
    // the stored type and let the kernel re-check fail closed, never
    // mis-substitute.
    let mut ctor_ty = if ctor_info.level_params.len() == ind_levels.len() {
        ctor_info
            .type_
            .instantiate_level_params_direct(&ctor_info.level_params, ind_levels)
    } else {
        ctor_info.type_.clone()
    };
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
    let mut field_fvars = Vec::new();
    let mut field_idx = 0;
    while let ExprKind::Pi(bi, domain, codomain) = ctor_ty.clone().kind() {
        let ctor_short_name = ctor_name.to_string();
        let ctor_short = ctor_short_name
            .rsplit('.')
            .next()
            .unwrap_or(&ctor_short_name);
        let field_name = format!("{ctor_short}_{field_idx}");
        let field_fvar = state.fresh_fvar();
        let field_ty = domain.as_ref().clone();
        new_ctx.push(LocalDecl {
            fvar: field_fvar,
            name: field_name,
            ty: field_ty,
            value: None,
        });
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
    field_fvars
}

/// Build induction hypotheses for recursive fields of a constructor.
///
/// REQUIRES: `field_fvars` and `recursive_fields` correspond to the same constructor
/// ENSURES: IH decls are added to `new_ctx` for each recursive field
/// ENSURES: returned vec has same length as `field_fvars`
fn build_induction_hypotheses(
    state: &mut ProofState,
    goal: &Goal,
    new_ctx: &mut Vec<LocalDecl>,
    ctor_name: &Name,
    field_fvars: &[FVarId],
    recursive_fields: &[bool],
    hyp_fvar: FVarId,
) -> Vec<Option<FVarId>> {
    let mut ih_fvars = Vec::new();
    for (i, fvar) in field_fvars.iter().enumerate() {
        if i < recursive_fields.len() && recursive_fields[i] {
            let ctor_short_name = ctor_name.to_string();
            let ctor_short = ctor_short_name
                .rsplit('.')
                .next()
                .unwrap_or(&ctor_short_name);
            let ih_name = format!("ih_{ctor_short}_{i}");
            let ih_fvar = state.fresh_fvar();
            let ih_ty = state
                .metas
                .instantiate(&goal.target.subst_fvar(hyp_fvar, &Expr::fvar(*fvar)));
            new_ctx.push(LocalDecl {
                fvar: ih_fvar,
                name: ih_name,
                ty: ih_ty,
                value: None,
            });
            ih_fvars.push(Some(ih_fvar));
        } else {
            ih_fvars.push(None);
        }
    }
    ih_fvars
}

/// Assemble the recursor proof term from case metas, close the goal, and push new goals.
///
/// REQUIRES: `cases` has one entry per constructor
/// ENSURES: On Ok, the original goal is closed with a recursor proof term
/// ENSURES: On Ok, one new goal per constructor is pushed onto `state.goals`
fn assemble_induction_proof(
    state: &mut ProofState,
    ctx: &InductionCtx<'_>,
    cases: Vec<InductionCase>,
) -> TacticResult {
    let rec_levels = recursor_levels(state, ctx.goal, ctx.levels, ctx.rec_info.level_params.len());
    let mut proof = Expr::const_(ctx.rec_name.clone(), rec_levels);
    for arg in ctx.args.iter().take(ctx.ind_info.num_params as usize) {
        proof = Expr::app(proof, arg.clone());
    }
    proof = Expr::app(proof, ctx.motive.clone());
    for case in &cases {
        let mut case_proof = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(case.case_meta)));
        for ih_fvar in case.ih_fvars.iter().rev().flatten() {
            let ih_ty = case
                .new_ctx
                .iter()
                .find(|d| d.fvar == *ih_fvar)
                .map_or_else(
                    || Expr::from_kind(ExprKind::Sort(Level::zero())),
                    |d| d.ty.clone(),
                );
            case_proof = Expr::lam(
                BinderInfo::Default,
                ih_ty,
                case_proof.abstract_fvar(*ih_fvar),
            );
        }
        for fvar in case.field_fvars.iter().rev() {
            let fvar_ty = case.new_ctx.iter().find(|d| d.fvar == *fvar).map_or_else(
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
    proof = Expr::app(proof, Expr::fvar(ctx.hyp_fvar));

    // Part of #2154 Tier 2 Wave 2: structural recursor with meta case branches.
    // The minor-premise lambdas wrap still-open subgoal metas whose stored
    // target types reference the constructor field / IH binder FVars. Use the
    // assembly-time close (lenient recursor-spine inference, def-eq target
    // match) — strict App-arg validation happens in verify_tactic_proof once
    // the case metas are solved. See #38.
    state.close_goal_assembled(ctx.goal, proof)?;

    for case in cases {
        state.goals.push_back(Goal {
            meta_id: case.case_meta,
            target: case.new_target,
            local_ctx: case.new_ctx,
            tag: Some(case.ctor_tag),
        });
    }
    Ok(())
}
